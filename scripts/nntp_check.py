#!/usr/bin/env python3
# SPDX-License-Identifier: AGPL-3.0-or-later
"""The NNTP server: the session's program (`DN.Server.Session`) with its socket host
(`native/nntp_host.c`), run on loopback and checked from outside.

Every byte a client reads has to be what `session_ref` computes from the bytes it sent. Every run
but `nntplib`'s, which runs the server as it is run in use, has the host report each turn — the
events it gave the program, the actions it carried out and what the kernel took of each send — and
the report is held three times: `session_ref.judge` holds the program to the session's contract on
real sockets; the model, `dn-compiler session-model`, replays it and has to act and ask to be woken
as the program did; and it is held against the clients' sockets and the host's side of the
contract: what a client sent reaches its connection's input in order, what it read is what the
kernel took of the program's sends; input comes only from a connection the program asked to read
from whose last send was taken whole, at most once a batch, and `writable` only after a send taken
in part; an index is never given out again with a generation it had, and no turn is taken with
nothing to do. Whether the server still holds a connection's socket is read off the kernel's
tables.

The standard library's `nntplib` is greeted, reads the capabilities and the help, and quits. A
pipeline of lines of many kinds gets its replies in order. Three recorded transcripts
(`tests/golden/nntp-transcripts.json`), whose replies `session_ref` has to compute too, are sent cut
at every position into two parts, the second once the host has given out the first, and one is
sent a byte at a time; each reads what it records: a line past the limit is refused and not
answered as its command, and nothing after QUIT is answered. A client that shuts down its sending
side gets the replies to its whole lines and then the end of the stream; a reset mid-line is
reported as a close. A client that reads nothing until its receive queue stops growing gets every
byte once it reads; a line sent once an answer that asks to read waits for room waits in the
kernel; a client reset while a send waits for room is reported closed, and never ready to write.
On a clock the check moves, the deadlines of the first command, of a line and of inactivity close
their connections at once at the time the program asked to be woken at and not a millisecond
before; after QUIT the server shuts down sending and holds the socket, dropping what still comes,
until the client closes its side, 5 s of silence or 30 s in all, and not a millisecond before; out
of descriptors, it leaves the listening socket alone for 100 ms and then serves the client that
waited. On the real clock, the first command's deadline closes at ten seconds and a silent
lingering socket at five, with the server idle meanwhile, and the client that waited out a pause
is served once it is over. A hundred resets leave the server the descriptors it had, and of
seventy lingering sockets it keeps the last sixty-four. Sixty-four clients that connect while the
server is stopped are taken sixteen a batch, a sixty-fifth waits until one closes, and one reset
while it waits is closed as soon as it is taken. Where nothing happens, the server spends no
processor time. Every run ends on SIGTERM.

Each planted defect, in the host or in the program, has to be caught by the check named for it and
for the reason named.
"""
from __future__ import annotations

import argparse
from collections.abc import Buffer, Callable, Iterator
from contextlib import contextmanager
from dataclasses import dataclass
import fcntl
import json
import os
from pathlib import Path
import queue
import resource
import selectors
import signal
import socket
import struct
import subprocess
import sys
import termios
import threading
import time
from typing import IO, Any
import warnings

sys.path.insert(0, str(Path(__file__).resolve().parent))
import lanes  # the path above is what makes these importable
from lanes import NATIVE, ROOT, LaneError, Report
import session_check as sessions
import session_native
import session_ref as ref

OUT = ROOT / "build/nntp"
HOST = NATIVE / "nntp_host.c"
HOSTS = [HOST, NATIVE / "session_calls.h", NATIVE / "cake_header.c", NATIVE / "accept_policy.h", *lanes.RUNTIME]
REVISION, SOURCE = b"0123abc", b"https://example.org/dragons-net"
TEXTS = ref.texts(REVISION, SOURCE)
GREETING = TEXTS["greeting"]
# The host's own limits: how long a graceful close lingers, and how long accepting pauses.
LINGER_QUIET, LINGER_TOTAL, ACCEPT_PAUSE, LINGERING = 5_000, 30_000, 100, 64
# How long a check waits for the server; shorter while planted defects are run.
TIMEOUT = 10.0
Conn = tuple[int, int]


def expected(stream: bytes) -> bytes:
    """What a client that sent `stream` reads: the greeting, then the reply to each whole line."""
    return GREETING + b"".join(TEXTS[a] for a in ref.answers(stream))


def lines(*texts: str) -> bytes:
    return b"".join(t.encode() + b"\r\n" for t in texts)


GOLDEN = ROOT / "tests/golden/nntp-transcripts.json"


def transcripts() -> dict[str, tuple[bytes, bytes]]:
    """The recorded transcripts, what a client sends and what it has to read, byte for byte, from a
    server started with this lane's identity; `session_ref` has to compute each reading too."""
    recorded = json.loads(GOLDEN.read_text())
    if (recorded["revision"], recorded["source"]) != (REVISION.decode(), SOURCE.decode()):
        raise LaneError(f"{GOLDEN.name} was recorded with another identity")
    found = {}
    for name, transcript in recorded["transcripts"].items():
        sent, read = transcript["sent"].encode("latin-1"), transcript["read"].encode("latin-1")
        if expected(sent) != read:
            raise LaneError(f"session_ref answers the transcript {name!r} otherwise than it records")
        found[name] = (sent, read)
    return found


@dataclass
class Turn:
    """One turn as the host reports it; a send carries whether to read and what the kernel took."""
    now: int
    events: list[tuple[Any, ...]]
    actions: list[tuple[Any, ...]]
    wake: int

    def judged(self) -> ref.Turn:
        sends = [a for a in self.actions if a[0] == "send"]
        return ref.Turn(self.now, self.events, [a[:5] for a in self.actions], [a[5] for a in sends], self.wake)

    @property
    def partial(self) -> bool:
        return any(a[0] == "send" and a[5] < len(a[3]) for a in self.actions)


# How many words follow the index and the generation of each kind.
EVENTS = {"open": 1, "recv": 1, "end": 0, "writable": 0, "closed": 0}
ACTIONS = {"send": 3, "graceful": 0, "close": 0}


def hexed(word: str) -> bytes:
    return b"" if word == "-" else bytes.fromhex(word)


def items(words: list[str], kinds: dict[str, int]) -> list[tuple[Any, ...]]:
    found: list[tuple[Any, ...]] = []
    k = 0
    while k < len(words):
        kind = words[k]
        if kind not in kinds:
            raise LaneError(f"the host reported {kind!r}")
        idx, gen, rest = int(words[k + 1]), int(words[k + 2]), words[k + 3:k + 3 + kinds[kind]]
        k += 3 + kinds[kind]
        if kind == "open":
            found.append((kind, idx, gen, int(rest[0])))
        elif kind == "recv":
            found.append((kind, idx, gen, hexed(rest[0])))
        elif kind == "send":
            found.append((kind, idx, gen, hexed(rest[2]), rest[0] == "1", int(rest[1])))
        else:
            found.append((kind, idx, gen))
    return found


def parse(line: str) -> Turn:
    """`turn NOW <events> | <actions> | wake WAKE`, or `| stopped CODE` in the turn the program
    stopped the run, which ends the check with the events that turn gave the program."""
    parts = [part.split() for part in line.split(" |")]
    if len(parts) != 3 or parts[0][:1] != ["turn"] or len(parts[2]) != 2 or parts[2][0] not in ("wake", "stopped"):
        raise LaneError(f"the host reported {line[:160]!r}")
    head, acts, tail = parts
    try:
        turn = Turn(int(head[1]), items(head[2:], EVENTS), items(acts, ACTIONS), int(tail[1]))
    except (ValueError, IndexError):
        raise LaneError(f"the host reported {line[:160]!r}") from None
    if tail[0] == "stopped":
        raise LaneError(f"at {turn.now} the program stopped the run with code {turn.wake}, given {turn.events!r:.300}")
    return turn


class Client(socket.socket):
    """A client on loopback that keeps what it sent and what it read. It sends each piece at once,
    since a check times its pieces against the clock it moves."""

    def __init__(self, port: int, receive_buffer: int = 0) -> None:
        super().__init__(socket.AF_INET, socket.SOCK_STREAM)
        self.sent = bytearray()
        self.got = bytearray()
        self.eof = False
        # the connection the host reported for this client, once it has
        self.conn: Conn | None = None
        if receive_buffer:
            self.setsockopt(socket.SOL_SOCKET, socket.SO_RCVBUF, receive_buffer)
        self.setsockopt(socket.IPPROTO_TCP, socket.TCP_NODELAY, 1)
        self.settimeout(TIMEOUT)
        self.connect(("127.0.0.1", port))
        self.port: int = self.getsockname()[1]

    def sendall(self, data: Buffer, flags: int = 0, /) -> None:
        self.sent += data
        super().sendall(data, flags)

    def recv(self, size: int, flags: int = 0, /) -> bytes:
        data = super().recv(size, flags)
        self.got += data
        self.eof |= not data
        return data


class Server:
    """The server on a free loopback port. With `virtual`, on a clock the check moves; otherwise on
    the real clock. With `traced`, its report is read as it comes, and when the run ends it is
    judged and held against the clients' sockets."""

    def __init__(self, binary: Path, virtual: bool, traced: bool, options: tuple[str, ...]) -> None:
        self.clock_write = -1
        self.lines: queue.Queue[str | None] = queue.Queue()
        self.trace: list[Turn] = []
        # the clients of each port, in the order they connected
        self.clients: dict[int, list[Client]] = {}
        self.delivered: dict[Conn, bytearray] = {}
        self.gone: dict[Conn, int] = {}
        self.last = Turn(0, [], [], 0)
        self.batch = session_native.layout(OUT)["BATCH"]
        self.idle_allowed = 0
        self.traced = traced
        self.err: str | None = None
        extra: list[str] = []
        ours: list[int] = []
        theirs: list[int] = []
        if traced:
            report_read, report_write = os.pipe()
            extra += ["--report-fd", str(report_write)]
            ours.append(report_read)
            theirs.append(report_write)
        if virtual:
            clock_read, self.clock_write = os.pipe()
            extra += ["--clock-fd", str(clock_read)]
            theirs.append(clock_read)
        try:
            self.proc = subprocess.Popen(
                [str(binary), "--port", "0", "--revision", REVISION.decode(), "--source", SOURCE.decode(), *extra,
                 *options], stdout=subprocess.PIPE, stderr=subprocess.PIPE, pass_fds=theirs, text=True)
        except OSError:
            for fd in [*ours, *theirs, self.clock_write]:
                if fd >= 0:
                    os.close(fd)
            raise
        for fd in theirs:
            os.close(fd)
        if traced:
            threading.Thread(target=self.read_reports, args=(ours[0],), daemon=True).start()
        try:
            self.port = self.read_port()
        except BaseException:
            self.close()
            raise

    def read_reports(self, fd: int) -> None:
        with open(fd, encoding="ascii") as stream:
            for line in stream:
                self.lines.put(line)
        self.lines.put(None)

    def read_port(self) -> int:
        out = self.pipe(self.proc.stdout)
        with selectors.DefaultSelector() as ready:
            ready.register(out.fileno(), selectors.EVENT_READ)
            if not ready.select(TIMEOUT):
                raise LaneError(f"the server gave no port in {TIMEOUT} s{self.why()}")
        line = out.readline()
        if not line:
            raise LaneError(f"the server gave no port{self.why()}")
        return int(json.loads(line)["port"])

    @staticmethod
    def pipe(stream: IO[str] | None) -> IO[str]:
        if stream is None:
            raise LaneError("the server has no pipe")
        return stream

    def said(self) -> str:
        """What the server wrote to stderr, once it has ended."""
        if self.err is None:
            self.err = self.pipe(self.proc.stderr).read()
        return self.err

    def why(self) -> str:
        if self.proc.poll() is None:
            return ""
        return f" and ended with status {self.proc.returncode}: {self.said()[-300:]!r}"

    def died(self) -> str:
        """How the server ended, if it did: a client can see its sockets close a moment before."""
        try:
            self.proc.wait(timeout=0.1)
        except subprocess.TimeoutExpired:
            return ""
        return f"; the server had ended with status {self.proc.returncode}: {self.said()[-300:]!r}"

    def client(self, receive_buffer: int = 0) -> Client:
        c = Client(self.port, receive_buffer)
        self.clients.setdefault(c.port, []).append(c)
        return c

    def turn(self) -> Turn:
        """The next turn the host reports."""
        try:
            line = self.lines.get(timeout=TIMEOUT)
        except queue.Empty:
            raise LaneError(f"the server gave no turn in {TIMEOUT} s{self.why()}") from None
        if line is None:
            self.lines.put(None)
            raise LaneError(f"the server stopped reporting{self.why()}")
        return self.take(parse(line))

    def take(self, t: Turn) -> Turn:
        woken = self.last.wake and t.now >= self.last.wake
        if not t.events and len(self.last.events) < self.batch and not woken:
            if not self.idle_allowed:
                raise LaneError(f"the server took a turn with nothing to do at {t.now}")
            self.idle_allowed -= 1
        for e in t.events:
            if e[0] == "open":
                waiting = [c for c in self.clients.get(e[3], []) if c.conn is None]
                if waiting:
                    waiting[0].conn = (e[1], e[2])
            elif e[0] == "recv":
                self.delivered.setdefault((e[1], e[2]), bytearray()).extend(e[3])
            elif e[0] == "closed":
                self.gone[e[1], e[2]] = t.now
        for a in t.actions:
            if a[0] != "send":
                self.gone[a[1], a[2]] = t.now
        self.trace.append(t)
        self.last = t
        return t

    def until(self, done: Callable[[], bool], what: str) -> None:
        try:
            while not done():
                self.turn()
        except LaneError as error:
            raise LaneError(f"waiting for {what}: {error}") from None

    def idle(self, seconds: float) -> None:
        """Take every turn the server reports within `seconds`."""
        end = time.monotonic() + seconds
        while (left := end - time.monotonic()) > 0:
            try:
                line = self.lines.get(timeout=left)
            except queue.Empty:
                return
            if line is None:
                self.lines.put(None)
                return
            self.take(parse(line))

    def conn_of(self, c: Client) -> Conn:
        self.until(lambda: c.conn is not None, f"the connection from port {c.port}")
        if c.conn is None:
            raise LaneError(f"no connection from port {c.port}")
        return c.conn

    def received(self, c: Client) -> bytes:
        """What the host has given the program of what `c` sent."""
        return bytes(self.delivered.get(c.conn, b"")) if c.conn else b""

    def closed(self, c: Client) -> bool:
        return c.conn in self.gone

    def await_close(self, c: Client, what: str) -> None:
        self.until(lambda: self.closed(c), what)

    def quiet(self, seconds: float, what: str) -> None:
        """Take the turns of `seconds` with nothing to do; the server has to spend almost no
        processor time in them."""
        before = cpu_seconds(self.proc.pid)
        self.idle(seconds)
        used = cpu_seconds(self.proc.pid) - before
        if used > seconds / 4:
            raise LaneError(f"{what}: the server used {used:.2f} s of CPU in {seconds} s with nothing to do")

    def await_input(self, c: Client, n: int) -> None:
        """Take turns until the host has given the program `n` bytes of `c`, or its connection is gone."""
        self.until(lambda: len(self.received(c)) >= n or self.closed(c), f"{n} bytes from port {c.port}")

    def kinds(self, c: Client) -> list[str]:
        """The kinds of the events and actions of `c`'s connection, in order."""
        return [x[0] for t in self.trace for x in [*t.events, *t.actions] if (x[1], x[2]) == c.conn]

    def advance(self, now: int) -> None:
        os.write(self.clock_write, f"{now}\n".encode())

    def stop(self) -> None:
        if self.proc.poll() is None:
            self.proc.send_signal(signal.SIGTERM)
        try:
            _, err = self.proc.communicate(timeout=TIMEOUT)
        except subprocess.TimeoutExpired:
            self.proc.kill()
            self.proc.communicate()
            raise LaneError("the server did not end on SIGTERM") from None
        self.err = err
        if self.proc.returncode != 0 or "stopped: a signal" not in err:
            raise LaneError(f"on SIGTERM the server ended with status {self.proc.returncode}: {err[-300:]!r}")
        if not self.traced:
            return
        try:
            while (line := self.lines.get(timeout=TIMEOUT)) is not None:
                self.take(parse(line))
        except queue.Empty:
            raise LaneError("the report did not end with the server") from None
        # The host first: what the program did is judged on events the host has to have given it.
        held_to_sockets(self.trace, self.clients, self.batch)
        try:
            ref.judge(REVISION, SOURCE, [t.judged() for t in self.trace])
        except ref.Violation as error:
            raise LaneError(f"on sockets the program broke the session's contract: {error}") from None
        replayed(self.trace)

    def close(self) -> None:
        if self.proc.poll() is None:
            self.proc.kill()
        self.proc.wait()
        for stream in (self.proc.stdout, self.proc.stderr):
            if stream:
                stream.close()
        if self.clock_write >= 0:
            os.close(self.clock_write)
            self.clock_write = -1
        for same_port in self.clients.values():
            for c in same_port:
                c.close()


def replayed(trace: list[Turn]) -> None:
    """The report replayed through the model: given each turn's events, time and what the kernel
    took, the model has to act and ask to be woken as the program did."""
    with sessions.Speaker(sessions.model_command(), (REVISION, SOURCE)) as model:
        for k, t in enumerate(trace):
            answer = model.turn(t.now, [e[:3] if e[0] == "open" else e for e in t.events])
            if answer != [a[:5] for a in t.actions]:
                raise LaneError(f"turn {k} at {t.now}: the program did {t.actions}, the model {answer}")
            wake = model.settle([a[5] for a in t.actions if a[0] == "send"])
            if wake != t.wake:
                raise LaneError(f"turn {k} at {t.now}: the program asked to be woken at {t.wake}, the model {wake}")


def held_to_sockets(trace: list[Turn], clients: dict[int, list[Client]], batch: int) -> None:
    """The report against the sockets and the host's side of the contract: every connection comes
    from a client of the check; what the host gave the program of it is what the client sent, all of
    it once the input ended; what the client read is what the kernel took of the program's sends,
    all of it once the stream ended; input comes only when the last send asked to read and was taken
    whole, at most once a batch, and `writable` only after a send taken in part; no event comes for
    a connection after its close; a batch holds at most `batch` events; an index is given out only
    when free, and never with a generation it had; a client never taken reads nothing, not even the
    end of its stream."""
    waiting = {port: list(same_port) for port, same_port in clients.items()}
    client_of: dict[Conn, Client] = {}
    given: dict[Conn, bytearray] = {}
    delivered: dict[Conn, bytearray] = {}
    reading: dict[Conn, bool] = {}
    unsent: dict[Conn, bool] = {}
    ended: set[Conn] = set()
    gone: set[Conn] = set()
    generation: dict[int, int] = {}
    for t in trace:
        if len(t.events) > batch:
            raise LaneError(f"at {t.now} a batch of {len(t.events)} events")
        inputs: set[Conn] = set()
        for e in t.events:
            conn = (e[1], e[2])
            if e[0] == "open":
                if e[2] <= generation.get(e[1], 0):
                    raise LaneError(f"index {e[1]} was given out again with generation {e[2]}")
                if (e[1], generation.get(e[1], 0)) in client_of and (e[1], generation[e[1]]) not in gone:
                    raise LaneError(f"at {t.now} index {e[1]} was given out while its connection was open")
                if not waiting.get(e[3]):
                    raise LaneError(f"{conn} opened from port {e[3]}, which is no client of the check")
                generation[e[1]] = e[2]
                client_of[conn], given[conn], delivered[conn] = waiting[e[3]].pop(0), bytearray(), bytearray()
                reading[conn] = unsent[conn] = False
                continue
            if conn not in client_of or conn in gone:
                raise LaneError(f"at {t.now} an event {e[0]} for {conn}, which is not open")
            if e[0] in ("recv", "end"):
                if not reading[conn] or conn in inputs or conn in ended:
                    raise LaneError(f"at {t.now} input from {conn}, which the host was not to read")
                inputs.add(conn)
            if e[0] == "recv":
                delivered[conn] += e[3]
            elif e[0] == "end":
                ended.add(conn)
            elif e[0] == "writable":
                if not unsent[conn]:
                    raise LaneError(f"at {t.now} {conn} reported ready to write with nothing untaken")
                unsent[conn] = False
            elif e[0] == "closed":
                gone.add(conn)
        for a in t.actions:
            conn = (a[1], a[2])
            if a[0] == "send" and conn in given and conn not in gone:
                given[conn] += a[3][:a[5]]
                reading[conn] = a[4] and a[5] == len(a[3])
                unsent[conn] = a[5] < len(a[3])
            elif a[0] != "send":
                gone.add(conn)
    for conn, c in client_of.items():
        if not c.sent.startswith(delivered[conn]):
            raise LaneError(f"{conn} was given {bytes(delivered[conn][-60:])!r}, not what its client sent")
        if conn in ended and delivered[conn] != c.sent:
            raise LaneError(f"{conn}: the input ended after {len(delivered[conn])} of {len(c.sent)} bytes sent")
        if not given[conn].startswith(c.got):
            raise LaneError(f"{conn}: its client read {bytes(c.got[-60:])!r}, which the kernel was not given")
        if c.eof and c.got != given[conn]:
            raise LaneError(f"{conn}: its client read {len(c.got)} bytes to the end, of {len(given[conn])} taken")
    for same_port in waiting.values():
        for c in same_port:
            if c.got or c.eof:
                raise LaneError(f"the client on port {c.port} read from a connection never reported open")


@contextmanager
def serving(binary: Path, virtual: bool = False, *options: str, traced: bool = True) -> Iterator[Server]:
    server = Server(binary, virtual, traced, options)
    try:
        try:
            yield server
        except (LaneError, OSError) as error:
            said = str(error) if isinstance(error, LaneError) else repr(error)
            raise LaneError(said if "ended with status" in said else said + server.died()) from None
        server.stop()
    finally:
        server.close()


def read_exactly(s: socket.socket, n: int) -> bytes:
    got = b""
    while len(got) < n:
        chunk = s.recv(n - len(got))
        if not chunk:
            raise LaneError(f"the stream ended after {len(got)} of {n} bytes: {got[-80:]!r}")
        got += chunk
    return got


def read_expected(s: socket.socket, want: bytes, what: str) -> None:
    got = read_exactly(s, len(want))
    if got != want:
        raise LaneError(f"{what}: read {got[-120:]!r}, not {want[-120:]!r}")


def read_to_end(s: socket.socket) -> bytes:
    got = b""
    try:
        while chunk := s.recv(65536):
            got += chunk
    except TimeoutError:
        raise LaneError(f"the stream did not end; read {got[-120:]!r}") from None
    return got


def ended(s: socket.socket) -> bool:
    """Whether the server closed the connection: the stream ends or is reset."""
    try:
        return s.recv(1) == b""
    except ConnectionResetError:
        return True


def still_open(s: socket.socket) -> bool:
    """Whether nothing has arrived and the connection is not closed, without waiting."""
    s.setblocking(False)
    try:
        s.recv(1)
    except BlockingIOError:
        return True
    finally:
        s.settimeout(TIMEOUT)
    return False


def held(pid: int, c: Client) -> bool:
    """Whether the server still holds a socket connected to `c`, as the kernel lists them. Once `c`
    has closed its side too the kernel lists the connection no more, so this is asked only of a
    client that keeps its side open."""
    ours = set()
    for fd in Path(f"/proc/{pid}/fd").iterdir():
        try:
            ours.add(str(fd.readlink()))
        except FileNotFoundError:
            continue
    for row in Path(f"/proc/{pid}/net/tcp").read_text().splitlines()[1:]:
        fields = row.split()
        if int(fields[2].split(":")[1], 16) == c.port and f"socket:[{fields[9]}]" in ours:
            return True
    return False


def queued(s: socket.socket) -> int:
    """The bytes waiting in the socket's receive queue."""
    count = struct.pack("i", 0)
    return int(struct.unpack("i", fcntl.ioctl(s.fileno(), termios.FIONREAD, count))[0])


def reset(s: socket.socket) -> None:
    s.setsockopt(socket.SOL_SOCKET, socket.SO_LINGER, struct.pack("ii", 1, 0))
    s.close()


def cpu_seconds(pid: int) -> float:
    fields = Path(f"/proc/{pid}/stat").read_text().rsplit(")", 1)[1].split()
    return (int(fields[11]) + int(fields[12])) / os.sysconf("SC_CLK_TCK")


def with_nntplib(binary: Path) -> str:
    try:
        with warnings.catch_warnings():
            warnings.simplefilter("ignore", DeprecationWarning)
            import nntplib  # noqa: PLC0415  (deprecated, and gone after Python 3.12)
    except ImportError:
        raise LaneError("this check needs the nntplib of Python 3.12") from None
    with serving(binary, traced=False) as server:
        news = nntplib.NNTP("127.0.0.1", server.port, timeout=TIMEOUT)
        welcome = news.getwelcome()
        capabilities = news.getcapabilities()
        _, help_lines = news.help()
        bye = news.quit()
    if welcome + "\r\n" != GREETING.decode():
        raise LaneError(f"nntplib was greeted with {welcome!r}")
    if capabilities != {"VERSION": ["2"], "IMPLEMENTATION": ["dragons-net", REVISION.decode()]}:
        raise LaneError(f"nntplib read the capabilities {capabilities}")
    if help_lines != TEXTS["help"].decode().split("\r\n")[1:-2]:
        raise LaneError(f"nntplib read the help {help_lines}")
    if bye + "\r\n" != TEXTS["quit"].decode():
        raise LaneError(f"nntplib quit with {bye!r}")
    return f"{len(help_lines)} lines of help"


def pipeline(binary: Path) -> str:
    recorded = transcripts()
    stream = recorded["commands"][0].removesuffix(b"QUIT\r\n") + recorded["long lines"][0] + lines("HELP")
    with serving(binary) as server:
        s = server.client()
        s.sendall(stream)
        got = read_to_end(s)
    if got != expected(stream):
        raise LaneError(f"a pipeline got {got[-160:]!r}")
    return f"{len(ref.answers(stream))} replies"


def in_parts(server: Server, stream: bytes, read: bytes, parts: list[bytes]) -> None:
    """Send each part once the host has given the program the parts before it; `read` is what the
    client has to read."""
    c = server.client()
    sent = 0
    for part in parts:
        c.sendall(part)
        sent += len(part)
        server.await_input(c, sent)
    got = read_to_end(c)
    c.close()
    if got != read:
        raise LaneError(f"{stream[:30]!r} in parts of {[len(p) for p in parts][:4]} bytes: read {got[-120:]!r}")


def every_cut(binary: Path) -> str:
    recorded = transcripts()
    cuts = 0
    with serving(binary, True) as server:
        for sent, read in recorded.values():
            for at in range(1, len(sent)):
                in_parts(server, sent, read, [sent[:at], sent[at:]])
                cuts += 1
        sent, read = recorded["commands"]
        in_parts(server, sent, read, [sent[k:k + 1] for k in range(len(sent))])
    return f"{cuts} cuts of {len(recorded)} transcripts, and one sent a byte at a time"


def half_close(binary: Path) -> str:
    stream = b"HELP\r\nSTAT 1\r\nCAPAB"
    with serving(binary) as server:
        s = server.client()
        s.sendall(stream)
        s.shutdown(socket.SHUT_WR)
        got = read_to_end(s)
        server.until(lambda: server.closed(s), "the close")
        kinds = server.kinds(s)
    if got != expected(stream):
        raise LaneError(f"after the end of input the client got {got[-160:]!r}")
    if "end" not in kinds or "closed" in kinds or kinds[-1] != "graceful":
        raise LaneError(f"the end of input was reported as {kinds}")
    return "the replies to the whole lines, then the end"


def reset_mid_line(binary: Path) -> str:
    with serving(binary) as server:
        s = server.client()
        read_expected(s, GREETING, "the greeting")
        s.sendall(b"HEL")
        server.await_input(s, 3)
        reset(s)
        server.until(lambda: server.closed(s), "the reset")
        kinds = server.kinds(s)
        after = server.client()
        after.sendall(b"QUIT\r\n")
        got = read_to_end(after)
    if kinds[-1] != "closed" or "end" in kinds:
        raise LaneError(f"a reset was reported as {kinds}")
    if got != expected(b"QUIT\r\n"):
        raise LaneError(f"after a reset the next client got {got!r}")
    return "reported as a close; the next client served"


def slow_reader(binary: Path) -> str:
    # Far more than the kernel buffers on both ends hold, so that the server has to wait for room.
    stream = b"HELP\r\n" * 100 + b"QUIT\r\n"
    with serving(binary, True, "--send-buffer", "4096") as server:
        s = server.client(receive_buffer=1024)
        s.sendall(stream)
        # The client reads nothing until the server reports a send taken only in part and its own
        # receive queue has stopped growing: the kernel took all it had room for.
        server.until(lambda: server.last.partial, "a send taken in part")
        held = -1
        while held != queued(s):
            held = queued(s)
            server.idle(0.1)
        got = read_to_end(s)
    want = expected(stream)
    if got != want:
        raise LaneError(f"a slow reader got {len(got)} bytes, not {len(want)}: {got[-120:]!r}")
    return f"{len(got)} bytes, {held} of them held in the client's queue before it read"


def reading_waits(binary: Path) -> str:
    """Lines sent one at a time to a client that reads nothing: once an answer that asks to read
    again is taken only in part, the next line waits in the kernel until the rest is taken."""
    with serving(binary, True, "--send-buffer", "4096") as server:
        c = server.client(receive_buffer=1024)
        conn = server.conn_of(c)

        def answers() -> list[tuple[Any, ...]]:
            return [a for t in server.trace for a in t.actions if a[0] == "send" and (a[1], a[2]) == conn]

        def answered(n: int) -> Callable[[], bool]:
            return lambda: len(answers()) == n

        sent = 0
        while not answers()[-1][5] < len(answers()[-1][3]):
            if sent == 1000:
                raise LaneError("no answer was taken in part")
            c.sendall(b"HELP\r\n")
            sent += 1
            server.until(answered(sent + 1), f"the answer to line {sent}")
        before = len(server.received(c))
        c.sendall(b"HELP\r\n")
        server.idle(0.05)
        if len(server.received(c)) != before:
            raise LaneError("a line was read while the answer before it waited for room")
        c.sendall(b"QUIT\r\n")
        got = read_to_end(c)
    if got != expected(b"HELP\r\n" * (sent + 1) + b"QUIT\r\n"):
        raise LaneError(f"the client read {got[-120:]!r}")
    return f"the next line waited once the answer to line {sent} was taken in part"


def reset_while_sending(binary: Path) -> str:
    """A client that reads nothing and is reset while a send waits for room: the report shows its
    close and no room ever came, and the next client is served."""
    with serving(binary, True, "--send-buffer", "4096") as server:
        s = server.client(receive_buffer=1024)
        s.sendall(b"HELP\r\n" * 100)
        server.until(lambda: server.last.partial, "a send taken in part")
        reset(s)
        server.await_close(s, "the reset")
        kinds = server.kinds(s)
        again = server.client()
        conn = server.conn_of(again)
        read_expected(again, GREETING, "the next greeting")
    if kinds[-1] != "closed" or "writable" in kinds:
        raise LaneError(f"a reset while sending was reported as {kinds}")
    return f"closed; the next client served at {conn[0]}/{conn[1]}"


def deadline(binary: Path, name: str, sends: list[tuple[int, bytes]], after: int) -> str:
    """Send each part at its time; the connection has to close at once `after` milliseconds past the
    last turn, where the program has to ask to be woken, and not a millisecond before."""
    with serving(binary, True) as server:
        s = server.client()
        server.conn_of(s)
        last = server.last
        read_expected(s, GREETING, "the greeting")
        sent = b""
        for at, part in sends:
            server.advance(at)
            s.sendall(part)
            before = expected(sent)
            sent += part
            server.await_input(s, len(sent))
            last = server.last
            read_expected(s, expected(sent)[len(before):], f"{name}: after {part!r}")
        due = last.now + after
        if last.wake != due:
            raise LaneError(f"{name}: the program asked to be woken at {last.wake}, not {due}")
        server.advance(due - 1)
        # A turn of another connection, so that the host has read the clock before the look.
        other = server.client()
        server.conn_of(other)
        read_expected(other, GREETING, "the other connection's greeting")
        if not still_open(s) or server.closed(s):
            raise LaneError(f"{name}: the connection closed before {due}")
        server.advance(due)
        server.await_close(s, f"the close at {due}")
        closing = server.last
        if closing.now != due or ("close", *server.conn_of(s)) not in closing.actions or not ended(s):
            raise LaneError(f"{name}: the connection was not closed at {due}: {closing}")
        if held(server.proc.pid, s):
            raise LaneError(f"{name}: the connection was closed gracefully, not at once")
    return f"closed at {due}"


def real_deadline(binary: Path) -> str:
    """On the real clock: the first command's deadline closes at ten seconds and not before; a
    client that quits and stays silent has its socket held for 5 s and then closed; and the server
    waits for both without using the processor."""
    with serving(binary) as server:
        pid = server.proc.pid
        began = time.monotonic()
        s = server.client()
        read_expected(s, GREETING, "the greeting")
        quitter = server.client()
        quitter.sendall(b"QUIT\r\n")
        read_to_end(quitter)
        quit_at, cpu = time.monotonic(), cpu_seconds(pid)
        time.sleep(max(0.0, quit_at + LINGER_QUIET / 1000 - 0.5 - time.monotonic()))
        if not held(pid, quitter):
            raise LaneError(f"on the real clock a lingering socket closed before {LINGER_QUIET} ms of silence")
        time.sleep(max(0.0, quit_at + LINGER_QUIET / 1000 + 1 - time.monotonic()))
        if held(pid, quitter):
            raise LaneError(f"on the real clock a lingering socket was held {LINGER_QUIET + 1000} ms after the close")
        s.settimeout(max(0.1, began + ref.FIRST_COMMAND / 1000 + 1.5 - time.monotonic()))
        closed = ended(s)
        took, used = time.monotonic() - began, cpu_seconds(pid) - cpu
    if not closed or not ref.FIRST_COMMAND / 1000 - 0.01 <= took <= ref.FIRST_COMMAND / 1000 + 1:
        raise LaneError(f"on the real clock the first command's deadline closed after {took:.2f} s")
    if used > 0.2:
        raise LaneError(f"waiting for the deadlines, the server used {used:.2f} s of CPU")
    return f"closed after {took:.2f} s, the lingering socket after {LINGER_QUIET} ms, {used:.2f} s of CPU"


def lingering(binary: Path) -> str:
    """Three clients send QUIT and a line after it: each reads the reply to QUIT and the end. One stays
    silent, one keeps sending every 4 s, and one closes its side, after which the server closes its
    socket and does nothing more; after each step a turn of a fourth client, the ticker, shows the
    host has read the clock and drained what came."""
    with serving(binary, True) as server:
        pid = server.proc.pid
        ticker = server.client()
        read_expected(ticker, GREETING, "the ticker's greeting")

        def tick() -> None:
            n = len(server.received(ticker)) + 6
            ticker.sendall(b"HELP\r\n")
            server.await_input(ticker, n)
            read_expected(ticker, TEXTS["help"], "the ticker's help")

        def step(now: int, sending: bool = False) -> None:
            server.advance(start + now)
            if sending:
                busy.sendall(b"x")
            tick()

        def expect(c: Client, want: bool, what: str) -> None:
            if held(pid, c) != want:
                raise LaneError(what)

        silent, busy, closer = clients = [server.client() for _ in range(3)]
        for c in clients:
            c.sendall(b"QUIT\r\nHELP\r\n")
            got = read_to_end(c)
            if got != expected(b"QUIT\r\n"):
                raise LaneError(f"after QUIT a client read {got[-80:]!r}")
        server.until(lambda: all(server.closed(c) for c in clients), "the graceful closes")
        begun = {server.gone[server.conn_of(c)] for c in clients}
        if len(begun) != 1:
            raise LaneError(f"three clients quit on a still clock at {begun}")
        start = begun.pop()
        for c in clients:
            expect(c, True, "a graceful close closed at once instead of lingering")
        before = descriptors(pid)
        closer.close()
        tick()
        server.quiet(0.1, "after a lingering client closed its side")
        if descriptors(pid) != before - 1:
            raise LaneError("a lingering socket was not closed when its client closed its side")
        step(4000, sending=True)
        step(LINGER_QUIET - 1)
        expect(silent, True, f"closed before {LINGER_QUIET} ms of silence")
        step(LINGER_QUIET)
        expect(silent, False, f"still open after {LINGER_QUIET} ms of silence")
        expect(busy, True, f"closed after {LINGER_QUIET} ms though its client kept sending")
        for when in range(8000, LINGER_TOTAL, 4000):
            step(when, sending=True)
        step(LINGER_TOTAL - 1)
        expect(busy, True, f"closed before {LINGER_TOTAL} ms in all")
        step(LINGER_TOTAL)
        expect(busy, False, f"still open after {LINGER_TOTAL} ms in all")
    return f"held until the client's close, {LINGER_QUIET} ms of silence or {LINGER_TOTAL} ms in all"


def descriptors(pid: int) -> int:
    return sum(1 for _ in Path(f"/proc/{pid}/fd").iterdir())


def descriptors_kept(binary: Path) -> str:
    """A hundred clients reset one after another leave the server the descriptors it had. Seventy
    that quit and keep their side open leave it sixty-four more, those of the last sixty-four: a
    full list of lingering sockets gives up the one that has lingered longest."""
    with serving(binary, True) as server:
        pid = server.proc.pid
        base = descriptors(pid)
        for _ in range(100):
            c = server.client()
            read_expected(c, GREETING, "a greeting")
            reset(c)
            server.await_close(c, "a reset")
        if descriptors(pid) != base:
            raise LaneError(f"after 100 resets the server holds {descriptors(pid)} descriptors, not {base}")
        quitters = []
        for _ in range(LINGERING + 6):
            c = server.client()
            c.sendall(b"QUIT\r\n")
            read_to_end(c)
            quitters.append(c)
        server.until(lambda: all(server.closed(c) for c in quitters), "the graceful closes")
        kept = [held(pid, c) for c in quitters]
        if kept != [False] * 6 + [True] * LINGERING:
            raise LaneError(f"the lingering sockets kept are not the last {LINGERING}: {kept}")
        if descriptors(pid) != base + LINGERING:
            raise LaneError(f"with {LINGERING} lingering the server holds {descriptors(pid)} descriptors, not "
                            f"{base + LINGERING}")
    return f"{base} descriptors after 100 resets, {base + LINGERING} with the last {LINGERING} lingering"


def lowest_free(pid: int) -> int:
    taken = {int(p.name) for p in Path(f"/proc/{pid}/fd").iterdir()}
    return next(k for k in range(len(taken) + 1) if k not in taken)


def refuse_accepts(server: Server) -> tuple[int, Client]:
    """Lower the server's limit on descriptors to those it holds and connect a client: the server
    takes one turn on the refused accept. Gives the old soft limit and the client."""
    pid = server.proc.pid
    soft, hard = resource.prlimit(pid, resource.RLIMIT_NOFILE)
    resource.prlimit(pid, resource.RLIMIT_NOFILE, (lowest_free(pid), hard))
    server.idle_allowed = 1
    late = server.client()
    server.until(lambda: not server.idle_allowed, "the refused accept")
    return soft, late


def out_of_descriptors(binary: Path) -> str:
    """Out of descriptors, the server takes one turn on the refused accept and none more while it
    pauses; it serves the client once the pause is over."""
    with serving(binary, True) as server:
        soft, late = refuse_accepts(server)
        refused = server.last.now
        server.advance(refused + ACCEPT_PAUSE - 1)
        server.quiet(0.1, "while accepting paused")
        if not still_open(late) or late.conn is not None:
            raise LaneError(f"served before the pause of {ACCEPT_PAUSE} ms was over")
        pid = server.proc.pid
        resource.prlimit(pid, resource.RLIMIT_NOFILE, (soft, resource.prlimit(pid, resource.RLIMIT_NOFILE)[1]))
        server.advance(refused + ACCEPT_PAUSE)
        server.conn_of(late)
        read_expected(late, GREETING, "the greeting after the pause")
    pauses = server.said().count("pausing")
    if pauses != 1:
        raise LaneError(f"the pause was logged {pauses} times")
    return f"served after {ACCEPT_PAUSE} ms"


def real_pause(binary: Path) -> str:
    """The same on the real clock: with nothing else to wake it, the server serves the client that
    waited once the pause is over."""
    with serving(binary) as server:
        soft, late = refuse_accepts(server)
        refused = time.monotonic()
        pid = server.proc.pid
        resource.prlimit(pid, resource.RLIMIT_NOFILE, (soft, resource.prlimit(pid, resource.RLIMIT_NOFILE)[1]))
        server.conn_of(late)
        waited = time.monotonic() - refused
        read_expected(late, GREETING, "the greeting after the pause")
    if not ACCEPT_PAUSE / 2000 <= waited <= 1:
        raise LaneError(f"on the real clock the client that waited was served {waited:.3f} s after the refusal")
    return f"served {waited:.3f} s after the refusal"


def crowd(binary: Path) -> str:
    """Sixty-four clients connect while the server is stopped, so that it takes them in full
    batches; a sixty-fifth waits until one of them closes, and a sixty-sixth, reset while it waits,
    is closed as soon as the server takes it."""
    with serving(binary, True) as server:
        server.proc.send_signal(signal.SIGSTOP)
        try:
            clients = [server.client() for _ in range(ref.CONNS)]
        finally:
            server.proc.send_signal(signal.SIGCONT)
        for s in clients:
            read_expected(s, GREETING, "a greeting")
        server.until(lambda: all(s.conn is not None for s in clients), "the openings")
        if max(len(t.events) for t in server.trace) != server.batch:
            raise LaneError(f"sixty-four clients waiting were not taken {server.batch} a batch")
        extra = server.client()
        dropped = server.client()
        reset(dropped)
        clients[1].sendall(b"HELP\r\n")
        read_expected(clients[1], TEXTS["help"], "the help")
        # A host that listens with its table full takes turns for nothing here.
        server.quiet(0.1, "with the table full")
        if not still_open(extra):
            raise LaneError("a connection past the table was served while the table was full")
        clients[0].sendall(b"QUIT\r\n")
        read_expected(clients[0], TEXTS["quit"], "the reply to QUIT")
        read_expected(extra, GREETING, "the greeting past the table")
        clients[2].sendall(b"QUIT\r\n")
        read_expected(clients[2], TEXTS["quit"], "the reply to QUIT")
        server.await_close(dropped, "the close of a client reset while it waited")
    return f"{ref.CONNS} served {server.batch} a batch, the next once one closed"


CHECKS: dict[str, Callable[[Path], str]] = {
    "nntplib": with_nntplib,
    "pipeline": pipeline,
    "lines cut between reads": every_cut,
    "half close": half_close,
    "reset mid-line": reset_mid_line,
    "slow reader": slow_reader,
    "reading waits": reading_waits,
    "reset while sending": reset_while_sending,
    "first command": lambda b: deadline(b, "the first command", [], ref.FIRST_COMMAND),
    "a line": lambda b: deadline(b, "a line", [(5, b"HELP\r\nHEL")], ref.LINE_TIME),
    "inactivity": lambda b: deadline(b, "inactivity", [(5, b"HELP\r\n")], ref.INACTIVITY),
    "the real clock": real_deadline,
    "lingering close": lingering,
    "descriptors": descriptors_kept,
    "out of descriptors": out_of_descriptors,
    "out of descriptors on the real clock": real_pause,
    "sixty-five clients": crowd,
}


@dataclass
class Defect:
    """A defect planted in the host (exact text) or in the program (a pattern), with how many times
    the text occurs, the check that has to catch it and a part of what that check has to say."""
    name: str
    edits: list[tuple[str, str, int]]
    check: str
    sign: str
    program: bool = False


# Not planted, since nothing outside could tell: a batch that does not rotate where it starts, an
# action carried out for a stale generation, and a failed send not marked lost. The host gives out
# all one poll reported before it polls again, so a connection one batch does not reach the next one
# does; the program never acts for a generation it was told is closed; and a socket whose send
# failed hangs up at the next poll.
DEFECTS = [
    Defect("input no longer read after a read", [(
        "            event(a, DN_SESSION_RECEIVED, i, c->gen, (uint64_t)n);",
        "            c->reading = 0;\n            event(a, DN_SESSION_RECEIVED, i, c->gen, (uint64_t)n);", 1)],
        "lines cut between reads", "gave no turn"),
    Defect("the end of input reported as a close", [(
        "            event(a, DN_SESSION_INPUT_ENDED, i, c->gen, 0);",
        "            event(a, DN_SESSION_CLOSED, i, c->gen, 0);\n            free_index(c);", 1)],
        "half close", "the end of input was reported"),
    Defect("input read when the program did not ask", [
        ("(c->reading ? POLLIN : 0)", "POLLIN", 1), ("if ((r & POLLIN) && c->reading)", "if (r & POLLIN)", 1)],
        "slow reader", "stopped the run: code 4"),
    Defect("the wake ignored", [("if (news || (wake && now_ms() >= wake)) return;", "if (news) return;", 1)],
           "first command", "gave no turn"),
    Defect("woken a millisecond late", [("(wake && now_ms() >= wake)", "(wake && now_ms() > wake)", 1)],
           "first command", "gave no turn"),
    Defect("a new connection put at index 0", [("        while (conns[i].fd >= 0 || conns[i].lost) ++i;\n", "", 1)],
           "sixty-five clients", "stopped the run: code 6"),
    Defect("an index given out again with its generation", [(".gen = conns[i].gen + 1,", ".gen = 1,", 1)],
           "lines cut between reads", "given out again with generation"),
    Defect("a lingering socket never closed", [(
        "if (now >= l->until || now >= l->quiet_until) {", "if (now == UINT64_MAX) {", 1)],
        "lingering close", "still open after"),
    Defect("silence counted from the close only", [(
        "            l->quiet_until = now_ms() + LINGER_QUIET_MS;", "            continue;", 1)],
        "lingering close", "though its client kept sending"),
    Defect("a graceful close made at once", [(
        "static void linger(int fd) {\n", "static void linger(int fd) {\n    close(fd);\n    return;\n", 1)],
        "lingering close", "closed at once instead of lingering"),
    Defect("a graceful close that does not shut down sending", [(
        "    if (shutdown(fd, SHUT_WR) && errno != ENOTCONN) {\n        close(fd);\n        return;\n    }\n", "", 1)],
        "lingering close", "the stream did not end"),
    Defect("a close now that lingers", [("            else close(fd);", "            else linger(fd);", 1)],
           "first command", "closed gracefully, not at once"),
    Defect("no poll for writing", [("(c->unsent ? POLLOUT : 0)", "0", 1)], "slow reader", "the stream did not end"),
    Defect("a send said taken whole", [(
        "uint64_t taken = n > 0 ? (uint64_t)n : 0;", "uint64_t taken = n >= 0 ? len : 0;", 1)],
        "slow reader", "the kernel was not given"),
    Defect("reading while a send waits for room", [(
        "cn->reading = !cn->lost && read && taken == len;", "cn->reading = !cn->lost && read;", 1)],
        "reading waits", "stopped the run: code 4"),
    Defect("listening with the table full", [(
        "int listening = free_indexes() > 0 && !paused;", "int listening = !paused;", 1)],
        "sixty-five clients", "a turn with nothing to do"),
    Defect("no poll timeout on the real clock", [(
        "else left = at - now > INT_MAX ? INT_MAX : (int)(at - now);", "else return timeout;", 1)],
        "the real clock", "was held"),
    Defect("a poll timeout in seconds", [("(int)(at - now);", "(int)((at - now) / 1000);", 1)],
           "the real clock", "s of CPU"),
    Defect("a failed read ignored", [(
        ("        } else if (errno != EAGAIN && errno != EWOULDBLOCK && errno != EINTR) {\n"
         "            event(a, DN_SESSION_CLOSED, i, c->gen, 0);\n            free_index(c);\n        }"),
        "        }", 1)],
        "reset mid-line", "a turn with nothing to do"),
    Defect("a hang-up ignored", [(
        ("    if (r & (POLLERR | POLLHUP | POLLNVAL)) {\n        event(a, DN_SESSION_CLOSED, i, c->gen, 0);\n"
         "        free_index(c);\n        return;\n    }\n"), "", 1)],
        "reset while sending", "was reported as"),
    Defect("writable reported with nothing untaken", [
        ("(c->unsent ? POLLOUT : 0)", "POLLOUT", 1), ("if ((r & POLLOUT) && c->unsent) {", "if (r & POLLOUT) {", 1)],
        "pipeline", "with nothing untaken"),
    Defect("a close reported and the index kept", [(
        "        event(a, DN_SESSION_CLOSED, i, c->gen, 0);\n        free_index(c);\n        return;\n    }\n    if",
        "        event(a, DN_SESSION_CLOSED, i, c->gen, 0);\n        return;\n    }\n    if", 1)],
        "reset while sending", "which is not open"),
    Defect("a batch one event too large", [(
        "while (accept_ready && turn_events < DN_SESSION_BATCH && free_indexes() > 0) {",
        "while (accept_ready && turn_events <= DN_SESSION_BATCH && free_indexes() > 0) {", 1)],
        "sixty-five clients", "stopped the run: code 1"),
    Defect("a lost connection reported late", [(
        "                cn->lost = 1;\n                carrying = 1;\n", "                cn->lost = 1;\n", 1)],
        "sixty-five clients", "the close of a client reset while it waited"),
    Defect("a closed connection's descriptor kept", [("    if (c->fd >= 0) close(c->fd);\n    c->fd = -1;",
                                                       "    c->fd = -1;", 1)],
           "descriptors", "after 100 resets"),
    Defect("a lingering socket given up and not closed", [(
        "    if (lingering[at].fd >= 0) close(lingering[at].fd);\n", "", 1)],
        "descriptors", "the lingering sockets kept are not the last"),
    Defect("the newest lingering socket given up", [(
        "if (lingering[i].since < lingering[at].since) at = i;",
        "if (lingering[i].since > lingering[at].since) at = i;", 1)],
        "descriptors", "the lingering sockets kept are not the last"),
    Defect("a lingering socket kept when its client closes", [(
        "        if (n == 0 || (n < 0 && errno != EAGAIN", "        if ((n < 0 && errno != EAGAIN", 1)],
        "lingering close", "with nothing to do"),
    Defect("no poll timeout for a lingering socket", [(
        "            timeout = until(end, timeout);\n", "            (void)end;\n", 1)],
           "the real clock", "was held"),
    Defect("no poll timeout for the pause of accepting", [(
        "        if (paused) timeout = until(accept_paused_until, timeout);\n", "", 1)],
        "out of descriptors on the real clock", "waiting for the connection"),
    Defect("SIGTERM ignored", [('if (fds[0].revents) stop_serving("a signal");', "", 1)],
           "pipeline", "did not end on SIGTERM"),
    Defect("accepting paused for good", [(
        "accept_paused_until = now_ms() + ACCEPT_PAUSE_MS;", "accept_paused_until = UINT64_MAX;", 1)],
        "out of descriptors", "waiting for the connection"),
    Defect("accepting not paused when out of descriptors", [(
        ("                accept_ready = 0;\n                accept_paused_until = now_ms() + ACCEPT_PAUSE_MS;\n"
         "                return;"), "                return;", 1)],
        "out of descriptors", "a turn with nothing to do"),
    Defect("the first command's deadline a millisecond early", [(r"now \+ 10000;", "now + 9999;", 1)],
           "first command", "asked to be woken at 10000", program=True),
    Defect("a line's deadline a millisecond early", [(r"now \+ 180000;", "now + 179999;", 2)],
           "a line", "asked to be woken", program=True),
    Defect("the inactivity deadline a millisecond early", [(r"now \+ 1800000;", "now + 1799999;", 3)],
           "inactivity", "asked to be woken", program=True),
    Defect("HELP answered as CAPABILITIES", [(r"r = 2;", "r = 1;", 1)], "pipeline",
           "broke the session's contract", program=True),
    Defect("a line past the limit answered as its command", [(r"if \(kind == 1\) == 0 \{", "if 0 {", 1)],
           "pipeline", "broke the session's contract", program=True),
    Defect("the session kept after QUIT", [(r"if r == 3 \{\s+st cb \+ 16, 1;", "if r == 3 {", 1)],
           "pipeline", "the stream did not end", program=True),
]


def spelled(n: int) -> str:
    """`n`, below a hundred, in words, as the documents write counts."""
    ones = ["zero", "one", "two", "three", "four", "five", "six", "seven", "eight", "nine", "ten", "eleven", "twelve",
            "thirteen", "fourteen", "fifteen", "sixteen", "seventeen", "eighteen", "nineteen"]
    tens = ["", "", "twenty", "thirty", "forty", "fifty", "sixty", "seventy", "eighty", "ninety"]
    if n < 20:
        return ones[n]
    return tens[n // 10] + (f"-{ones[n % 10]}" if n % 10 else "")


def planted(cake: str, source: str, assembly: Path, index: int, defect: Defect) -> Path:
    if defect.program:
        text = source
        for pattern, becomes, times in defect.edits:
            text = session_native.plant(text, pattern, becomes, times)
        return session_native.build(cake, f"defect-{index}", text, OUT, HOST)
    text = HOST.read_text()
    for old, new, times in defect.edits:
        if text.count(old) != times:
            raise LaneError(f"the host holds {old[:60]!r} {text.count(old)} times, not {times}, for {defect.name}")
        text = text.replace(old, new)
    host = OUT / f"defect-{index}.c"
    host.write_text(text)
    return lanes.link(OUT / f"defect-{index}", [host, NATIVE / "cake_header.c", NATIVE / "cake_runtime.c", assembly],
                      includes=[OUT], check=False)


def caught(cake: str, source: str, assembly: Path) -> dict[str, str]:
    global TIMEOUT  # noqa: PLW0603  (a defect caught by a wait needs no ten seconds of it)
    found = {}
    TIMEOUT = 1.5
    try:
        for index, defect in enumerate(DEFECTS):
            binary = planted(cake, source, assembly, index, defect)
            try:
                CHECKS[defect.check](binary)
            except (LaneError, OSError) as error:
                if defect.sign not in str(error):
                    raise LaneError(f"{defect.name} was caught, but not as {defect.sign!r}: {error!r}") from None
                found[defect.name] = f"{defect.check}: {str(error)[:300]}"
                continue
            raise LaneError(f"{defect.name} passed the check {defect.check!r}")
    finally:
        TIMEOUT = 10.0
    return found


def check(cake: str) -> Report:
    OUT.mkdir(parents=True, exist_ok=True)
    (OUT / "dn_session_layout.h").write_text(lanes.emit("emit-session-layout"))
    source = lanes.emit("emit-session")
    binary = session_native.build(cake, "nntp", source, OUT, HOST)
    results = {}
    for name, run in CHECKS.items():
        try:
            results[name] = run(binary)
        except OSError as error:
            raise LaneError(f"{name}: {error!r}") from None
        except LaneError as error:
            raise LaneError(f"{name}: {error}") from None
    found = caught(cake, source, OUT / "nntp.S")
    cuts = sum(len(sent) - 1 for sent, _ in transcripts().values())
    program = sum(d.program for d in DEFECTS)
    lanes.require_quoted({
        "docs/baseline.md": [
            f"{len(DEFECTS)} planted defects", f"{cuts:,} cuts", f"{spelled(len(DEFECTS))} NNTP servers",
            f"{spelled(len(DEFECTS) - program)} planted in its host and {spelled(program)} in its program"],
        "docs/assurance.md": [f"{len(DEFECTS)} planted defects", f"{cuts:,} cuts"]})
    return Report("checked", cake, HOSTS, {"executable_sha256": lanes.digest(binary), "checks": results,
                                           "planted_defects_caught": found})


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--cake", default=os.environ.get("CAKE"))
    args = parser.parse_args()
    lanes.require_platform(parser)
    cake = lanes.given_cake(parser, args.cake)
    lanes.lane_main("NNTP", OUT, lambda: check(cake))


if __name__ == "__main__":
    main()
