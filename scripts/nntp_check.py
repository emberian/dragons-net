#!/usr/bin/env python3
# SPDX-License-Identifier: AGPL-3.0-or-later
"""The NNTP server: the session's program (`DN.Server.Session`) with its socket host
(`native/nntp_host.c`), run on loopback and checked from outside (docs/baseline.md, "NNTP server").

Every byte a client reads has to be what `session_ref` computes from the bytes it sent. Every run but
`nntplib`'s reports its turns, and each report is held against the clients' sockets and the host's
side of the contract, judged by `session_ref.judge`, and replayed through the model. The checks are
`CHECKS`; each defect of `DEFECTS`, planted in the host or in the program, has to be caught by the
check named for it and for the reason named.
"""
from __future__ import annotations

import argparse
from collections.abc import Buffer, Callable, Iterator
from concurrent.futures import ThreadPoolExecutor
from contextlib import contextmanager
from dataclasses import dataclass
import datetime
import fcntl
import json
import os
from pathlib import Path
import queue
import random
import resource
import selectors
import signal
import socket
import struct
import subprocess
import sys
import tempfile
import termios
import time
from types import ModuleType
from typing import IO, Any, NamedTuple
import warnings

sys.path.insert(0, str(Path(__file__).resolve().parent))
import abnf_check  # the path above is what makes these importable
import lanes
from lanes import NATIVE, ROOT, LaneError, Report
import session_check as sessions
import session_native
import session_ref as ref
import store_check
import store_ref

OUT = ROOT / "build/nntp"
HOST = NATIVE / "nntp_host.c"
# The host's side of the store, linked with every build of the host.
STORE = [NATIVE / "store.c", NATIVE / "jobs.c"]
HOSTS = [HOST, *STORE, NATIVE / "store.h", NATIVE / "jobs.h", NATIVE / "session_calls.h",
         NATIVE / "call_checks.h", NATIVE / "cake_header.c", NATIVE / "accept_policy.h", *lanes.RUNTIME]
REVISION, SOURCE = sessions.IDENTITY
TEXTS = ref.texts(REVISION, SOURCE)
GREETING = TEXTS["greeting"]
GOLDEN = ROOT / "tests/golden/nntp-transcripts.json"
# The host's own limits: how long a graceful close lingers, how long accepting pauses, and how many
# sockets linger at once.
LINGER_QUIET, LINGER_TOTAL, ACCEPT_PAUSE, LINGERING = 5_000, 30_000, 100, 64
# How long a check waits for the server, and for a server with a planted defect.
TIMEOUT, DEFECT_TIMEOUT = 10.0, 1.5
# The program acts for the generation before its connection's, to see the host refuse it.
STALE = ("st slot + 16, lds 1 (cb + 8);", "st slot + 16, lds 1 (cb + 8) - 1;", 6)
Conn = tuple[int, int]


@dataclass
class Build:
    """The server to check, the same server built with a program that acts for the generation before
    its connection's, and how long to wait for either."""
    path: Path
    stale: Path
    timeout: float = TIMEOUT


def expected(stream: bytes) -> bytes:
    """What a client that sent `stream` reads: the greeting, then the reply to each whole line."""
    return GREETING + b"".join(TEXTS[a] for a in ref.answers(stream))


def lines(*texts: str) -> bytes:
    return b"".join(t.encode() + b"\r\n" for t in texts)


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


class Event(NamedTuple):
    """An event as the host reports it: `data` for input, `port` of the client for an opening."""
    kind: str
    idx: int
    gen: int
    data: bytes = b""
    port: int = 0

    @property
    def conn(self) -> Conn:
        return (self.idx, self.gen)

    def plain(self) -> ref.Event:
        """As the judge and the model take it."""
        return ref.Event(self.kind, self.idx, self.gen, self.data)


class Action(NamedTuple):
    """An action as the host reports it: for a send, its bytes, whether to read once they are taken,
    and how many the kernel took."""
    kind: str
    idx: int
    gen: int
    data: bytes = b""
    read: bool = False
    taken: int = 0

    @property
    def conn(self) -> Conn:
        return (self.idx, self.gen)

    def plain(self) -> ref.Action:
        return ref.Action(self.kind, self.idx, self.gen, self.data, self.read)


@dataclass
class Turn:
    """One turn as the host reports it."""
    now: int
    events: list[Event]
    actions: list[Action]
    wake: int

    def judged(self) -> ref.Turn:
        sends = [a for a in self.actions if a.kind == "send"]
        return ref.Turn(self.now, [e.plain() for e in self.events], [a.plain() for a in self.actions],
                        [a.taken for a in sends], self.wake)

    @property
    def partial(self) -> bool:
        return any(a.kind == "send" and a.taken < len(a.data) for a in self.actions)


def hexed(word: str) -> bytes:
    return b"" if word == "-" else bytes.fromhex(word)


def events(words: list[str]) -> list[Event]:
    """`open idx gen port`, `recv idx gen hex`, and `end`, `writable`, `closed` with idx and gen."""
    found = []
    k = 0
    while k < len(words):
        kind, idx, gen = words[k], int(words[k + 1]), int(words[k + 2])
        if kind == "open":
            found.append(Event(kind, idx, gen, port=int(words[k + 3])))
            k += 4
        elif kind == "recv":
            found.append(Event(kind, idx, gen, hexed(words[k + 3])))
            k += 4
        elif kind in ("end", "writable", "closed"):
            found.append(Event(kind, idx, gen))
            k += 3
        else:
            raise LaneError(f"the host reported an event {kind!r}")
    return found


def actions(words: list[str]) -> list[Action]:
    """`send idx gen read taken hex`, and `graceful`, `close` with idx and gen."""
    found = []
    k = 0
    while k < len(words):
        kind, idx, gen = words[k], int(words[k + 1]), int(words[k + 2])
        if kind == "send":
            found.append(Action(kind, idx, gen, hexed(words[k + 5]), words[k + 3] == "1", int(words[k + 4])))
            k += 6
        elif kind in ("graceful", "close"):
            found.append(Action(kind, idx, gen))
            k += 3
        else:
            raise LaneError(f"the host reported an action {kind!r}")
    return found


def parse(line: str) -> Turn:
    """`turn NOW <events> | <actions> | wake WAKE`, or `| stopped CODE` in the turn the program
    stopped the run, which ends the check with the events that turn gave the program."""
    parts = [part.split() for part in line.split(" |")]
    if len(parts) != 3 or parts[0][:1] != ["turn"] or len(parts[2]) != 2 or parts[2][0] not in ("wake", "stopped"):
        raise LaneError(f"the host reported {line[:160]!r}")
    head, acts, tail = parts
    try:
        turn = Turn(int(head[1]), events(head[2:]), actions(acts), int(tail[1]))
    except (ValueError, IndexError):
        raise LaneError(f"the host reported {line[:160]!r}") from None
    if tail[0] == "stopped":
        raise LaneError(f"at {turn.now} the program stopped the run with code {turn.wake}, given {turn.events!r:.300}")
    return turn


class Client(socket.socket):
    """A client on loopback that keeps what it sent and what it read. It sends each piece at once,
    since a check times its pieces against the clock it moves."""

    def __init__(self, port: int, timeout: float, receive_buffer: int = 0, family: int = socket.AF_INET) -> None:
        super().__init__(family, socket.SOCK_STREAM)
        self.sent = bytearray()
        self.got = bytearray()
        self.eof = False
        # the connection the host reported for this client, once it has
        self.conn: Conn | None = None
        try:
            if receive_buffer:
                self.setsockopt(socket.SOL_SOCKET, socket.SO_RCVBUF, receive_buffer)
            self.setsockopt(socket.IPPROTO_TCP, socket.TCP_NODELAY, 1)
            self.settimeout(timeout)
            self.connect(("::1" if family == socket.AF_INET6 else "127.0.0.1", port))
            self.port: int = self.getsockname()[1]
        except BaseException:
            self.close()
            raise

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
    the real clock. With `traced`, its report is read as it comes, and when the run ends it is held
    against the clients' sockets and the host's side of the contract, and, with `judged`, judged and
    replayed through the model."""

    def __init__(self, binary: Path, timeout: float, virtual: bool, traced: bool, judged: bool,
                 options: tuple[str, ...]) -> None:
        self.timeout = timeout
        self.clock_write = -1
        self.lines = lanes.Lines()
        self.trace: list[Turn] = []
        # the clients of each port, in the order they connected
        self.clients: dict[int, list[Client]] = {}
        self.delivered: dict[Conn, bytearray] = {}
        self.gone: dict[Conn, int] = {}
        self.last = Turn(0, [], [], 0)
        # The layout the server was built with lies beside it (lanes.whole_program).
        self.batch = session_native.layout(binary.parent)["BATCH"]
        self.idle_allowed = 0
        self.traced, self.judged = traced, judged
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
            self.lines = lanes.Lines(os.fdopen(ours[0], encoding="ascii"))
        try:
            self.port = self.read_port()
        except BaseException:
            self.close()
            raise

    def read_port(self) -> int:
        out = self.pipe(self.proc.stdout)
        with selectors.DefaultSelector() as ready:
            ready.register(out.fileno(), selectors.EVENT_READ)
            if not ready.select(self.timeout):
                raise LaneError(f"the server gave no port in {self.timeout} s{self.why()}")
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

    def client(self, receive_buffer: int = 0, family: int = socket.AF_INET) -> Client:
        c = Client(self.port, self.timeout, receive_buffer, family)
        self.clients.setdefault(c.port, []).append(c)
        return c

    def turn(self) -> Turn:
        """The next turn the host reports."""
        try:
            line = self.lines.get(self.timeout)
        except queue.Empty:
            raise LaneError(f"the server gave no turn in {self.timeout} s{self.why()}") from None
        if line is None:
            raise LaneError(f"the server stopped reporting{self.why()}")
        return self.take(parse(line))

    def take(self, t: Turn) -> Turn:
        woken = self.last.wake and t.now >= self.last.wake
        if not t.events and self.trace and len(self.last.events) < self.batch and not woken:
            if not self.idle_allowed:
                raise LaneError(f"the server took a turn with nothing to do at {t.now}")
            self.idle_allowed -= 1
        for e in t.events:
            if e.kind == "open":
                waiting = [c for c in self.clients.get(e.port, []) if c.conn is None]
                if waiting:
                    waiting[0].conn = e.conn
            elif e.kind == "recv":
                self.delivered.setdefault(e.conn, bytearray()).extend(e.data)
            elif e.kind == "closed":
                self.gone[e.conn] = t.now
        for a in t.actions:
            if a.kind != "send":
                self.gone[a.conn] = t.now
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
                line = self.lines.get(left)
            except queue.Empty:
                return
            if line is None:
                return
            self.take(parse(line))

    def quiet(self, seconds: float, what: str) -> None:
        """Take the turns of `seconds` with nothing to do; the server has to spend less than a
        quarter of that time on the processor."""
        before = cpu_seconds(self.proc.pid)
        self.idle(seconds)
        used = cpu_seconds(self.proc.pid) - before
        if used > seconds / 4:
            raise LaneError(f"{what}: the server used {used:.2f} s of CPU in {seconds} s with nothing to do")

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

    def await_input(self, c: Client, n: int) -> None:
        """Take turns until the host has given the program `n` bytes of `c`, or its connection is gone."""
        self.until(lambda: len(self.received(c)) >= n or self.closed(c), f"{n} bytes from port {c.port}")

    def kinds(self, c: Client) -> list[str]:
        """The kinds of the events and actions of `c`'s connection, in order."""
        found: list[str] = []
        for t in self.trace:
            found += [e.kind for e in t.events if e.conn == c.conn]
            found += [a.kind for a in t.actions if a.conn == c.conn]
        return found

    def advance(self, now: int) -> None:
        os.write(self.clock_write, f"{now}\n".encode())

    def stop(self) -> None:
        if self.proc.poll() is None:
            self.proc.send_signal(signal.SIGTERM)
        try:
            _, err = self.proc.communicate(timeout=self.timeout)
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
            while (line := self.lines.get(self.timeout)) is not None:
                self.take(parse(line))
        except queue.Empty:
            raise LaneError("the report did not end with the server") from None
        # The host first: what the program did is judged on events the host has to have given it.
        held_to_sockets(self.trace, self.clients, self.batch)
        if not self.judged:
            return
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
            judged = t.judged()
            answer = model.turn(t.now, judged.events)
            if answer != judged.actions:
                raise LaneError(f"turn {k} at {t.now}: the program did {judged.actions}, the model {answer}")
            wake = model.settle(judged.took)
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
            if e.kind == "open":
                if e.gen <= generation.get(e.idx, 0):
                    raise LaneError(f"index {e.idx} was given out again with generation {e.gen}")
                if (e.idx, generation.get(e.idx, 0)) in client_of and (e.idx, generation[e.idx]) not in gone:
                    raise LaneError(f"at {t.now} index {e.idx} was given out while its connection was open")
                if not waiting.get(e.port):
                    raise LaneError(f"{e.conn} opened from port {e.port}, which is no client of the check")
                generation[e.idx] = e.gen
                client_of[e.conn], given[e.conn], delivered[e.conn] = waiting[e.port].pop(0), bytearray(), bytearray()
                reading[e.conn] = unsent[e.conn] = False
                continue
            if e.conn not in client_of or e.conn in gone:
                raise LaneError(f"at {t.now} an event {e.kind} for {e.conn}, which is not open")
            if e.kind in ("recv", "end"):
                if not reading[e.conn] or e.conn in inputs or e.conn in ended:
                    raise LaneError(f"at {t.now} input from {e.conn}, which the host was not to read")
                inputs.add(e.conn)
            if e.kind == "recv":
                delivered[e.conn] += e.data
            elif e.kind == "end":
                ended.add(e.conn)
            elif e.kind == "writable":
                if not unsent[e.conn]:
                    raise LaneError(f"at {t.now} {e.conn} reported ready to write with nothing untaken")
                unsent[e.conn] = False
            elif e.kind == "closed":
                gone.add(e.conn)
        for a in t.actions:
            if a.kind == "send" and a.conn in given and a.conn not in gone:
                given[a.conn] += a.data[:a.taken]
                reading[a.conn] = a.read and a.taken == len(a.data)
                unsent[a.conn] = a.taken < len(a.data)
            elif a.kind != "send":
                gone.add(a.conn)
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
def serving(build: Build, virtual: bool = False, *options: str, traced: bool = True,
            stale: bool = False) -> Iterator[Server]:
    """The server of `build`, or with `stale` its program that acts for the generation before, which
    is not judged since it is wrong on purpose."""
    server = Server(build.stale if stale else build.path, build.timeout, virtual, traced, not stale, options)
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
    timeout = s.gettimeout()
    s.setblocking(False)
    try:
        s.recv(1)
    except BlockingIOError:
        return True
    finally:
        s.settimeout(timeout)
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
    for table in ("tcp", "tcp6"):
        for row in Path(f"/proc/{pid}/net/{table}").read_text().splitlines()[1:]:
            fields = row.split()
            if int(fields[2].split(":")[1], 16) == c.port and f"socket:[{fields[9]}]" in ours:
                return True
    return False


def descriptors(pid: int) -> int:
    return sum(1 for _ in Path(f"/proc/{pid}/fd").iterdir())


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


def import_nntplib() -> ModuleType:
    try:
        with warnings.catch_warnings():
            warnings.simplefilter("ignore", DeprecationWarning)
            import nntplib  # noqa: PLC0415 -- deprecated, and gone after Python 3.12
    except ImportError:
        raise LaneError("this check needs the nntplib of Python 3.12") from None
    return nntplib


def with_nntplib(b: Build) -> str:
    nntplib = import_nntplib()
    with serving(b, traced=False) as server:
        news = nntplib.NNTP("127.0.0.1", server.port, timeout=b.timeout)
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


def pipeline(b: Build) -> str:
    recorded = transcripts()
    stream = recorded["commands"][0].removesuffix(b"QUIT\r\n") + recorded["long lines"][0] + lines("HELP")
    with serving(b) as server:
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


def every_cut(b: Build) -> str:
    recorded = transcripts()
    cuts = 0
    with serving(b, True) as server:
        for sent, read in recorded.values():
            for at in range(1, len(sent)):
                in_parts(server, sent, read, [sent[:at], sent[at:]])
                cuts += 1
        sent, read = recorded["commands"]
        in_parts(server, sent, read, [sent[k:k + 1] for k in range(len(sent))])
    return f"{cuts} cuts of {len(recorded)} transcripts, and one sent a byte at a time"


def half_close(b: Build) -> str:
    stream = b"HELP\r\nSTAT 1\r\nCAPAB"
    with serving(b) as server:
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


def reset_mid_line(b: Build) -> str:
    with serving(b) as server:
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


def slow_reader(b: Build) -> str:
    # Far more than the kernel buffers on both ends hold, so that the server has to wait for room.
    stream = b"HELP\r\n" * 100 + b"QUIT\r\n"
    with serving(b, True, "--send-buffer", "4096") as server:
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


def reading_waits(b: Build) -> str:
    """Lines sent one at a time to a client that reads nothing: once an answer that asks to read
    again is taken only in part, the next line waits in the kernel until the rest is taken."""
    with serving(b, True, "--send-buffer", "4096") as server:
        c = server.client(receive_buffer=1024)
        conn = server.conn_of(c)

        def answers() -> list[Action]:
            return [a for t in server.trace for a in t.actions if a.kind == "send" and a.conn == conn]

        def answered(n: int) -> Callable[[], bool]:
            return lambda: len(answers()) == n

        sent = 0
        while not answers()[-1].taken < len(answers()[-1].data):
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


def reset_while_sending(b: Build) -> str:
    """A client that reads nothing and is reset while a send waits for room: the report shows its
    close and no room ever came, and the next client is served."""
    with serving(b, True, "--send-buffer", "4096") as server:
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


def deadline(b: Build, name: str, sends: list[tuple[int, bytes]], after: int) -> str:
    """Send each part at its time; the connection has to close at once `after` milliseconds past the
    last turn, where the program has to ask to be woken, and not a millisecond before."""
    with serving(b, True) as server:
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
        if closing.now != due or Action("close", *server.conn_of(s)) not in closing.actions or not ended(s):
            raise LaneError(f"{name}: the connection was not closed at {due}: {closing}")
        if held(server.proc.pid, s):
            raise LaneError(f"{name}: the connection was closed gracefully, not at once")
    return f"closed at {due}"


def real_deadline(b: Build) -> str:
    """On the real clock: the first command's deadline closes at ten seconds and not before; a
    client that quits and stays silent has its socket held for 5 s and then closed; and the server
    waits for both using less than 0.2 s of processor time."""
    with serving(b) as server:
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


def lingering(b: Build) -> str:
    """Three clients send QUIT and a line after it: each reads the reply to QUIT and the end. One stays
    silent, one keeps sending every 4 s, and one closes its side, after which the server closes its
    socket and does nothing more; after each step a turn of a fourth client, the ticker, shows the
    host has read the clock and drained what came."""
    with serving(b, True) as server:
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


def descriptors_kept(b: Build) -> str:
    """A hundred clients reset one after another leave the server the descriptors it had. Seventy
    that quit and keep their side open leave it sixty-four more, those of the last sixty-four: a
    full list of lingering sockets gives up the one that has lingered longest."""
    with serving(b, True) as server:
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


def out_of_descriptors(b: Build) -> str:
    """Out of descriptors, the server takes one turn on the refused accept and none more while it
    pauses; it serves the client once the pause is over."""
    with serving(b, True) as server:
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


def real_pause(b: Build) -> str:
    """The same on the real clock: with nothing else to wake it, the server serves the client that
    waited once the pause is over, as its own clock, which the report gives, measures it from the
    turn that refused the connection."""
    with serving(b) as server:
        soft, late = refuse_accepts(server)
        refused = server.last.now
        pid = server.proc.pid
        resource.prlimit(pid, resource.RLIMIT_NOFILE, (soft, resource.prlimit(pid, resource.RLIMIT_NOFILE)[1]))
        server.conn_of(late)
        waited = server.last.now - refused
        read_expected(late, GREETING, "the greeting after the pause")
    if not ACCEPT_PAUSE <= waited <= 1000:
        raise LaneError(f"on the real clock the client that waited was served {waited} ms after the refusal")
    return f"served {waited} ms after the refusal"


def stale_generation(b: Build) -> str:
    """A program that acts for the generation before its connection's: the host carries out none of
    its actions and tells it that nothing of its sends was taken, and the client reads nothing."""
    with serving(b, True, stale=True) as server:
        c = server.client()
        conn = server.conn_of(c)
        server.quiet(0.1, "with every action for another generation")
        if not still_open(c):
            raise LaneError("an action for another generation reached the client")
        sends = [a for t in server.trace for a in t.actions if a.kind == "send"]
    if not sends or any(a.conn == conn or a.taken for a in sends):
        raise LaneError(f"the host took the sends {sends} for the generation before {conn}")
    return f"{len(sends)} sends for the generation before, none taken"


def over_ipv6(b: Build) -> str:
    """The server listening on the IPv6 loopback address greets a client and answers its QUIT."""
    with serving(b, False, "--address", "::1") as server:
        s = server.client(family=socket.AF_INET6)
        s.sendall(b"QUIT\r\n")
        got = read_to_end(s)
    if got != expected(b"QUIT\r\n"):
        raise LaneError(f"over IPv6 the client read {got[-80:]!r}")
    return "greeted and answered on ::1"


def crowd(b: Build) -> str:
    """Sixty-four clients connect while the server is stopped, so that it takes them in full
    batches; a sixty-fifth waits until one of them closes, and a sixty-sixth, reset while it waits,
    is closed as soon as the server takes it."""
    with serving(b, True) as server:
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


def store_start(b: Build) -> str:
    """Recovery at start on a spool: an empty one gets a journal of its format and a start record, a
    start after it appends another, the server listening each time and greeting a client of loopback,
    which may post, with 200; and a spool holding a name no store gives, or a journal of two commits
    of one Message-ID, ends the start with status 4, the reason named."""
    with tempfile.TemporaryDirectory() as temp:
        spool, run = Path(temp, "spool"), Path(temp, "run")
        spool.mkdir()
        run.mkdir()
        options = ("--spool", str(spool), "--run-dir", str(run), "--path-identity", "dn.example",
                   "--group", "local.test")
        for _ in range(2):
            with serving(b, False, *options, traced=False) as server:
                read_expected(server.client(), TEXTS["greeting-post"], "the greeting after recovery")
        data = (spool / "journal").read_bytes()
        at = store_ref.HEADER + len(store_ref.MAGIC)
        key = data[at:at + store_ref.KEY]
        first = store_ref.FIRST_FRAME
        start = store_ref.HEADER + 1
        want = (store_ref.frame(key, 0, store_ref.FORMAT, store_ref.MAGIC + key)
                + store_ref.frame(key, first, store_ref.START, b"")
                + store_ref.frame(key, first + start, store_ref.START, b""))
        left = sorted(f.name for f in spool.iterdir())
        if data != want or left != ["journal"]:
            raise LaneError(f"two starts on an empty spool left {left}, a journal of "
                            f"{data.hex()}, not {want.hex()}")
        mid, twice = b"<twice@x>", data
        for seq in (1, 2):
            body = store_ref.payload((seq, mid, [(b"local.test", seq)], 0, 1, 0))
            twice += store_ref.frame(key, len(twice), store_ref.COMMIT, body)
        cases = (("junk", b"", "bad-name 6a756e6b"), ("journal", twice, f"id-twice {mid.hex()}"))
        for name, octets, said in cases:
            (spool / name).write_bytes(octets)
            done = subprocess.run([str(b.path), "--port", "0", "--revision", REVISION.decode(), "--source",
                                   SOURCE.decode(), *options], capture_output=True, text=True,
                                  timeout=b.timeout, check=False)
            if done.returncode != 4 or f"the store is refused: corrupt {said}" not in done.stderr:
                raise LaneError(f"a spool refused for {said}: status {done.returncode}, {done.stderr[-300:]!r}")
            (spool / "junk").unlink(missing_ok=True)
    return f"a journal of {len(want)} octets; refused: {'; '.join(said for _, _, said in cases)}"


def read_back(news: Any, nntplib: ModuleType, spool: Path, ids: list[str]) -> None:
    """Each article read back by `nntplib` as its file holds it: ARTICLE the header fields, Xref with
    its number in `local.test`, the empty line and the body; HEAD up to Xref, BODY after the empty line,
    STAT the number 0 and the Message-ID; an article the store lacks 430."""
    for k, mid in enumerate(ids, 1):
        octets = (spool / f"a{k:016x}").read_bytes()
        header, body = octets.split(b"\r\n\r\n", 1)
        unstuffed = [line[1:] if line.startswith(b".") else line for line in (header + b"\r\n").split(b"\r\n")]
        head = [*unstuffed[:-1], f"Xref: dn.example local.test:{k}".encode()]
        lines = [line[1:] if line.startswith(b".") else line for line in body.split(b"\r\n")[:-1]]
        got = {"article": news.article(mid), "head": news.head(mid), "body": news.body(mid)}
        wanted = {"article": (220, [*head, b"", *lines]), "head": (221, head), "body": (222, lines)}
        for what, (resp, info) in got.items():
            code, lines_wanted = wanted[what]
            if resp != f"{code} 0 {mid}" or info.lines != lines_wanted:
                raise LaneError(f"{what.upper()} {mid} answered {resp!r}, {info.lines[:6]}, not {lines_wanted[:6]}")
        if news.stat(mid)[0] != f"223 0 {mid}":
            raise LaneError(f"STAT {mid} answered otherwise than 223 0 {mid}")
    try:
        news.article("<none@x.example>")
    except nntplib.NNTPTemporaryError as error:
        if not str(error).startswith("430"):
            raise LaneError(f"an article the store lacks answered {error}") from None
    else:
        raise LaneError("an article the store lacks found")


def past_end(move: Any, nntplib: ModuleType, code: str) -> None:
    """NEXT or LAST past an end of the group: `code`, 421 or 422."""
    try:
        found = move()
    except nntplib.NNTPTemporaryError as error:
        if not str(error).startswith(code):
            raise LaneError(f"{move.__name__.upper()} past an end answered {error}") from None
    else:
        raise LaneError(f"{move.__name__.upper()} found {found} past an end")


def walk(news: Any, nntplib: ModuleType, ids: list[str]) -> None:
    """`local.test` selected by `nntplib`, its count and its numbers; each of its articles reached by
    STAT and NEXT, and back by LAST, 421 and 422 at the ends; ARTICLE by number makes it current."""
    _, count, first, last, name = news.group("local.test")
    if (count, first, last, name) != (len(ids), 1, len(ids), "local.test"):
        raise LaneError(f"GROUP local.test answered {count} {first} {last} {name}")
    steps = [news.stat(), *(news.next() for _ in ids[1:])]
    if [(num, mid) for _, num, mid in steps] != list(enumerate(ids, 1)):
        raise LaneError(f"STAT and NEXT over local.test gave {steps}")
    past_end(news.next, nntplib, "421")
    back = [news.last() for _ in ids[1:]]
    if [(num, mid) for _, num, mid in back] != list(enumerate(ids, 1))[-2::-1]:
        raise LaneError(f"LAST over local.test gave {back}")
    past_end(news.last, nntplib, "422")
    _, info = news.article(2)
    if (info.number, info.message_id) != (2, ids[1]) or news.stat()[1:] != (2, ids[1]):
        raise LaneError(f"ARTICLE 2 gave {info.number} {info.message_id}, then STAT {news.stat()}")


def listings(news: Any, server: Server, ids: list[str]) -> None:
    """`local.test` listed by `nntplib`: LIST ACTIVE with its highest and lowest numbers and `y`, as a
    wildmat takes it or not; LIST NEWSGROUPS and NEWGROUPS empty; DATE the wall clock in UTC. Its
    numbers from 2 by LISTGROUP over a socket of its own."""
    whole = [("local.test", str(len(ids)), "1", "y")]
    for pattern, want in ((None, whole), ("local.t*", whole), ("*,!local.*", [])):
        got = [tuple(g) for g in news.list(pattern)[1]]
        if got != want:
            raise LaneError(f"LIST ACTIVE {pattern} gave {got}")
    if news.descriptions("local.*")[1] != {} or news.newgroups(datetime.date(2026, 1, 1))[1] != []:
        raise LaneError("LIST NEWSGROUPS or NEWGROUPS gave groups")
    when = news.date()[1]
    now = datetime.datetime.now(datetime.UTC).replace(tzinfo=None)
    if abs((now - when).total_seconds()) > 60:
        raise LaneError(f"DATE gave {when}, at {now}")
    c = server.client()
    read_expected(c, TEXTS["greeting-post"], "the greeting")
    c.sendall(b"LISTGROUP local.test 2-\r\n")
    numbers = "".join(f"{k}\r\n" for k in range(2, len(ids) + 1))
    read_expected(c, f"211 {len(ids)} 1 {len(ids)} local.test\r\n{numbers}.\r\n".encode(), "LISTGROUP")


def post_over_sockets(b: Build) -> str:
    """POST on an empty spool from loopback: 340, the article, 240; after a restart its Message-ID is
    refused, 441, and two other articles taken, 240, the last by `nntplib` with a line of a dot and past
    16,384 octets, each in a file of its own. The host's log names the address and port of each article's poster by its
    `logging-data`. After another restart `nntplib` reads each back (`read_back`), and once an octet
    of a file is changed on the disk, its ARTICLE is answered 403; walks the group (`walk`) and lists it
    (`listings`)."""
    first = sessions.article(*sessions.BASIC, "Message-ID: <one@x.example>")
    second = sessions.article(*sessions.BASIC, "Message-ID: <two@x.example>")
    third = "\r\n".join((*sessions.BASIC, "Message-ID: <three@x.example>", "", ".",
                         *(f"line {k} " + "y" * 70 for k in range(500)))).encode()
    nntplib = import_nntplib()
    posters: list[int] = []
    logs: list[str] = []

    def post(server: Server, article: bytes, reply: str) -> None:
        c = server.client()
        read_expected(c, TEXTS["greeting-post"], "the greeting")
        c.sendall(b"POST\r\n")
        read_expected(c, TEXTS["post"], "the reply to POST")
        c.sendall(article)
        read_expected(c, TEXTS[reply], "the reply to the article")
        if reply == "posted":
            posters.append(c.port)

    with tempfile.TemporaryDirectory() as temp:
        spool, run = Path(temp, "spool"), Path(temp, "run")
        spool.mkdir()
        run.mkdir()
        options = ("--spool", str(spool), "--run-dir", str(run), "--path-identity", "dn.example",
                   "--group", "local.test")
        with serving(b, False, *options, traced=False) as server:
            post(server, first, "posted")
        logs.append(server.said())
        with serving(b, False, *options, traced=False) as server:
            post(server, first, "failed")
            post(server, second, "posted")
            try:
                with nntplib.NNTP("127.0.0.1", server.port, timeout=b.timeout) as news:
                    posters.append(news.sock.getsockname()[1])
                    welcome, posted, bye = news.getwelcome(), news.post(third), news.quit()
            except nntplib.NNTPError as error:
                raise LaneError(f"nntplib could not post: {error}") from None
        logs.append(server.said())
        left = sorted(f.name for f in spool.iterdir())
        data = [f.read_bytes().split(b"logging-data=", 1)[-1].split(b"\r\n", 1)[0].decode()
                for f in sorted(spool.glob("a*"))]
        ids = ["<one@x.example>", "<two@x.example>", "<three@x.example>"]
        try:
            with serving(b, False, *options, traced=False) as server, \
                    nntplib.NNTP("127.0.0.1", server.port, timeout=b.timeout) as news:
                read_back(news, nntplib, spool, ids)
                walk(news, nntplib, ids)
                listings(news, server, ids)
            first_file = spool / "a0000000000000001"
            changed = bytearray(first_file.read_bytes())
            changed[-3] ^= 1
            first_file.write_bytes(changed)
            with serving(b, False, *options, traced=False) as server, \
                    nntplib.NNTP("127.0.0.1", server.port, timeout=b.timeout) as news:
                try:
                    news.article(ids[0])
                except nntplib.NNTPTemporaryError as error:
                    refused = str(error)
                else:
                    refused = "found"
        except nntplib.NNTPError as error:
            raise LaneError(f"nntplib could not read: {error}") from None
    if refused != TEXTS["unreadable"].decode().rstrip("\r\n"):
        raise LaneError(f"an article whose file changed on the disk answered {refused!r}")
    if left != ["a0000000000000001", "a0000000000000002", "a0000000000000003", "journal"]:
        raise LaneError(f"three articles posted left {left}")
    said = [welcome, posted, bye]
    if [line + "\r\n" for line in said] != [TEXTS[t].decode() for t in ("greeting-post", "posted", "quit")]:
        raise LaneError(f"nntplib was greeted, its article answered and its QUIT with {said}")
    logged = [line for log in logs for line in log.splitlines() if line.startswith("connection ")]
    for value, port in zip(data, posters, strict=True):
        if f"connection {value} from 127.0.0.1 port {port}" not in logged:
            raise LaneError(f"logging-data {value[:40]!r} of the poster at port {port} is not in the log {logged}")
    return ("posted, the Message-ID refused after a restart, two others posted, their posters logged, each read "
            "back and listed, a changed file refused")


def files_of(image: str) -> list[tuple[bytes, bytes]]:
    """The files an image of the store lane names, in order."""
    if image == "-":
        return []
    return [(bytes.fromhex(n.replace("-", "")), bytes.fromhex(d.replace("-", "")))
            for n, d in (f.split("=") for f in image.split(";"))]


def image_of(spool: Path) -> tuple[str, dict[bytes, bytes]]:
    """A spool as the store lane writes an image, in the order the directory lists its names, and its
    files."""
    names = [os.fsencode(f.name) for f in spool.iterdir()]
    files = {n: (spool / os.fsdecode(n)).read_bytes() for n in names}
    return store_check.image([(n, files[n]) for n in names]), files


def started(b: Build, spool: Path, run: Path, groups: list[bytes]) -> tuple[int | None, str]:
    """The server started on `spool`: None once it listens, then stopped by SIGTERM; else the status it
    ended with. What it wrote to stderr."""
    command = [str(b.path), "--port", "0", "--revision", REVISION.decode(), "--source", SOURCE.decode(),
               "--spool", str(spool), "--run-dir", str(run), "--path-identity", "dn.example",
               *(a for g in groups for a in ("--group", g.decode()))]
    with subprocess.Popen(command, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True) as proc:
        out = Server.pipe(proc.stdout)
        with selectors.DefaultSelector() as ready:
            ready.register(out.fileno(), selectors.EVENT_READ)
            if not ready.select(b.timeout):
                proc.kill()
                proc.communicate()
                raise LaneError(f"the server on {spool} neither listened nor ended in {b.timeout} s")
        listened = bool(out.readline())
        if listened:
            proc.send_signal(signal.SIGTERM)
        try:
            _, err = proc.communicate(timeout=b.timeout)
        except subprocess.TimeoutExpired:
            proc.kill()
            proc.communicate()
            raise LaneError(f"the server on {spool} did not end in {b.timeout} s") from None
        if listened and (proc.returncode != 0 or "stopped: a signal" not in err):
            raise LaneError(f"on SIGTERM the server on {spool} ended with status {proc.returncode}: {err[-300:]!r}")
        return (None if listened else proc.returncode), err


def store_directories(b: Build) -> str:
    """The store lane's directories, each written to a spool and the server started on it twice: where
    `dn-compiler recovery-model` recovers the directory, the server listens, and leaves the files the
    model's actions leave, a start record appended to the journal, then one more; where it refuses, the
    start ends with status 4 and the model's reason."""
    model = [str(lanes.DN_COMPILER), "recovery-model"]
    rng = random.Random(store_check.SEED)  # noqa: S311 -- the store lane's own draw
    cases = []
    for case in (*store_check.table(), *store_check.drawn(rng)):
        _, key_hex, groups_hex, listed = case.line.split(" ")
        files = files_of(listed)
        if len(key_hex) == 32 and all(n and b"/" not in n and 0 not in n and n not in (b".", b"..") for n, _ in files):
            groups = [bytes.fromhex(g) for g in groups_hex.split(",")] if groups_hex != "-" else []
            cases.append((bytes.fromhex(key_hex), groups, files))
    def one(k: int, key: bytes, groups: list[bytes], files: list[tuple[bytes, bytes]]) -> bool:
        """Whether the model recovers the directory, the server having done as it does."""
        with tempfile.TemporaryDirectory() as temp:
            spool, run = Path(temp, f"spool-{k}"), Path(temp, f"run-{k}")
            spool.mkdir()
            run.mkdir()
            for name, data in files:
                (spool / os.fsdecode(name)).write_bytes(data)
            image, _ = image_of(spool)
            line = f"recover {key.hex()} {','.join(g.hex() for g in groups) or '-'} {image}"
            said = abnf_check.answer_lines(model, [line])[0]
            status, err = started(b, spool, run, groups)
            if said.startswith("corrupt "):
                if status != 4 or f"the store is refused: {said}\n" not in err:
                    raise LaneError(f"{line[:200]}: the model answers {said[:200]}, the server status {status}: "
                                    f"{err[-300:]!r}")
                return False
            if status is not None:
                raise LaneError(f"{line[:200]}: the model recovers it, the server ended with status {status}: "
                                f"{err[-300:]!r}")
            _, nxt, end, _, _, actions = said.split(" ")[1:]
            _, after = image_of(spool)
            journal = after.get(b"journal", b"")
            at = store_ref.HEADER + len(store_ref.MAGIC)
            jkey = journal[at:at + store_ref.KEY]
            actions = ";".join(f"create:{jkey.hex()}" if a.startswith("create:") else a for a in actions.split(";"))
            applied = abnf_check.answer_lines(model, [f"apply {line.split(' ')[3]} {actions}"])[0]
            want = dict(files_of(applied))
            want[b"journal"] = want.get(b"journal", b"") + store_ref.frame(jkey, int(end), store_ref.START, b"")
            if after != want:
                held = store_check.image(sorted(after.items()))
                raise LaneError(f"{line[:200]}: after a start the spool holds {held[:300]}, "
                                f"not {store_check.image(sorted(want.items()))[:300]} (next {nxt})")
            status, err = started(b, spool, run, groups)
            _, again = image_of(spool)
            want[b"journal"] += store_ref.frame(jkey, len(want[b"journal"]), store_ref.START, b"")
            if status is not None or again != want:
                raise LaneError(f"{line[:200]}: a second start: status {status}, the spool "
                                f"{store_check.image(sorted(again.items()))[:300]}: {err[-300:]!r}")
            return True

    with ThreadPoolExecutor(lanes.WORKERS) as pool:
        results = list(pool.map(lambda kc: one(kc[0], *kc[1]), enumerate(cases)))
    recovered = sum(results)
    refused = len(results) - recovered
    return f"{recovered} spools recovered and started again, {refused} refused as the model refuses them"


CHECKS: dict[str, Callable[[Build], str]] = {
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
    "actions for another generation": stale_generation,
    "over IPv6": over_ipv6,
    "sixty-five clients": crowd,
    "a store recovered at start": store_start,
    "a post over sockets": post_over_sockets,
    "the store lane's directories": store_directories,
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


# Not planted, since nothing outside could tell: a batch that does not rotate where it starts, and a
# failed send not marked lost. The host gives out all one poll reported before it polls again, so a
# connection one batch does not reach the next one does; and a socket whose send failed hangs up at
# the next poll. Nor TCP_NODELAY left off: it only delays a reply until the one before is
# acknowledged, which on loopback no check can time reliably, and no portable call reads another
# process's socket option.
DEFECTS = [
    Defect("a connection not logged", [("        dn_store_log_opened(&peer);\n", "", 1)], "a post over sockets",
           "is not in the log"),
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
        "int taking = listening && free_indexes() > 0 && !paused;", "int taking = listening && !paused;", 1)],
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
    Defect("an action carried out for a stale generation", [(
        "if (cn->fd < 0 || cn->gen != gen) {", "(void)gen;\n        if (cn->fd < 0) {", 1)],
        "actions for another generation", "reached the client"),
    Defect("SIGTERM ignored", [('if (fds[0].revents) stop_serving("a signal");', "", 1)],
           "pipeline", "did not end on SIGTERM"),
    Defect("accepting paused for good", [(
        "accept_paused_until = now + ACCEPT_PAUSE_MS;", "accept_paused_until = UINT64_MAX + 0 * now;", 1)],
        "out of descriptors", "waiting for the connection"),
    Defect("accepting not paused when out of descriptors", [(
        ("                accept_ready = 0;\n                accept_paused_until = now + ACCEPT_PAUSE_MS;\n"
         "                return;"), "                (void)now;\n                return;", 1)],
        "out of descriptors", "a turn with nothing to do"),
    Defect("a store refused at start taken for a broken contract",
           [("    if (stop == DN_SESSION_STORE_REFUSED || stop == DN_SESSION_RECOVERY_FAILED)\n", "    if (0)\n", 1)],
           "a store recovered at start", "status 3"),
    Defect("the start record written as a commit", [(r"(st8 @base \+ \d+ \+ 12), 3;", r"\1, 2;", 1)],
           "a store recovered at start", "a journal of", program=True),
    Defect("a final file set aside removed instead",
           [(r"(st @base \+ \d+, 1;\n\s*st @base \+ \d+, )8;", r"\g<1>9;", 1)],
           "the store lane's directories", "after a start the spool holds", program=True),
    Defect("the second pass not begun at the first name", [(r"if lds 1 \(rsc \+ 32\) \{", "if 0 {", 1)],
           "the store lane's directories", "the spool holds", program=True),
    Defect("the first command's deadline a millisecond early", [(r"now \+ 10000;", "now + 9999;", 1)],
           "first command", "asked to be woken at 10000", program=True),
    Defect("a line's deadline a millisecond early", [(r"now \+ 180000;", "now + 179999;", 2)],
           "a line", "asked to be woken", program=True),
    Defect("the inactivity deadline a millisecond early",
           [(r"st cb \+ 48, now \+ 1800000;", "st cb + 48, now + 1799999;", 8)],
           "inactivity", "asked to be woken", program=True),
    Defect("HELP answered as CAPABILITIES", [(r"r = 2;", "r = 1;", 1)], "pipeline",
           "broke the session's contract", program=True),
    Defect("a line past the limit answered as its command", [(r"if \(kind == 1\) == 0 \{", "if 0 {", 1)],
           "pipeline", "broke the session's contract", program=True),
    Defect("the session kept after QUIT", [(r"(if 0 < \(\(r == 3\) \+ \(r == 37\)\) \{)\s+st cb \+ 16, 1;", r"\1", 1)],
           "pipeline", "the stream did not end", program=True),
    Defect("a file's CRC-32C not compared",
           [(r"if \(\(acc \^ 4294967295\) == \(lds 1 \(rs \+ 160\)\)\) == 0 \{", "if 0 {", 1)],
           "a post over sockets", "changed on the disk answered", program=True),
    Defect("NEXT taken at the current article", [(r"\(mode == 2\) & \(x < num\)", "(mode == 2) & (x <= num)", 1)],
           "a post over sockets", "STAT and NEXT over local.test gave", program=True),
    Defect("LAST taken at the current article", [(r"\(mode == 3\) & \(num < x\)", "(mode == 3) & (num <= x)", 1)],
           "a post over sockets", "LAST over local.test gave", program=True),
]


def spelled(n: int) -> str:
    """`n`, below a hundred, in words, as the documents write counts."""
    ones = ["zero", "one", "two", "three", "four", "five", "six", "seven", "eight", "nine", "ten", "eleven", "twelve",
            "thirteen", "fourteen", "fifteen", "sixteen", "seventeen", "eighteen", "nineteen"]
    tens = ["", "", "twenty", "thirty", "forty", "fifty", "sixty", "seventy", "eighty", "ninety"]
    if n < 20:
        return ones[n]
    return tens[n // 10] + (f"-{ones[n % 10]}" if n % 10 else "")


def planted(source: str, defect: Defect) -> str:
    """The program's text, or the host's, with `defect` planted."""
    text = source if defect.program else HOST.read_text()
    for pattern, becomes, times in defect.edits:
        what = f"the {'program' if defect.program else 'host'}, for {defect.name},"
        text = lanes.plant(text, pattern, becomes, times, what, exact=not defect.program)
    return text


def hosted(index: int, defect: Defect, text: str, build: Build) -> Build:
    """The server with `defect` planted in its host, linked with the programs of `build`, waited for no
    longer than a defect needs."""
    name = f"defect-{index}"
    host = OUT / f"{name}.c"
    host.write_text(text)
    runtime = [NATIVE / "cake_header.c", NATIVE / "cake_runtime.c"]

    def linked(binary: str, program: str) -> Path:
        return lanes.link(OUT / binary, [host, *STORE, *runtime, OUT / program], includes=[OUT], check=False)

    # Only the check of actions for another generation runs the program that acts for the one before.
    stale = linked(f"{name}-stale", "stale.S") if CHECKS[defect.check] is stale_generation else build.stale
    return Build(linked(name, "nntp.S"), stale, DEFECT_TIMEOUT)


def caught(builds: list[Build]) -> dict[str, str]:
    found = {}
    for defect, built in zip(DEFECTS, builds, strict=True):
        try:
            CHECKS[defect.check](built)
        except (LaneError, OSError) as error:
            if defect.sign not in str(error):
                raise LaneError(f"{defect.name} was caught, but not as {defect.sign!r}: {error!r}") from None
            found[defect.name] = f"{defect.check}: {str(error)[:300]}"
            continue
        raise LaneError(f"{defect.name} passed the check {defect.check!r}")
    return found


def check(cake: str) -> Report:
    if sys.version_info[:2] != (3, 12):
        raise LaneError(f"this lane needs the nntplib of Python 3.12, not Python {sys.version.split()[0]}")
    OUT.mkdir(parents=True, exist_ok=True)
    (OUT / "dn_session_layout.h").write_text(lanes.emit("emit-session-layout"))
    source = lanes.emit("emit-session")
    stale = lanes.plant(source, *STALE, "the program, for acting for the generation before,", exact=True)
    texts = [planted(source, d) for d in DEFECTS]
    # Every program is compiled before any check runs, so that none of them shares the machine with
    # a compiler, the checks of real time least of all.
    with ThreadPoolExecutor(lanes.WORKERS) as pool:
        base, old = (pool.submit(lanes.whole_program, cake, name, text, OUT, HOST, STORE)
                     for name, text in (("nntp", source), ("stale", stale)))
        made = {k: pool.submit(lanes.whole_program, cake, f"defect-{k}", texts[k], OUT, HOST, STORE)
                for k, d in enumerate(DEFECTS) if d.program}
        build = Build(base.result(), old.result())
        linked = {k: pool.submit(hosted, k, d, texts[k], build) for k, d in enumerate(DEFECTS) if not d.program}
        builds = [Build(made[k].result(), build.stale, DEFECT_TIMEOUT) if k in made else linked[k].result()
                  for k in range(len(DEFECTS))]
    results = {}
    for name, run in CHECKS.items():
        try:
            results[name] = run(build)
        except OSError as error:
            raise LaneError(f"{name}: {error!r}") from None
        except LaneError as error:
            raise LaneError(f"{name}: {error}") from None
    found = caught(builds)
    cuts = sum(len(sent) - 1 for sent, _ in transcripts().values())
    program = sum(d.program for d in DEFECTS)
    lanes.require_quoted({
        "docs/baseline.md": [
            f"{len(DEFECTS)} planted defects", f"{cuts:,} cuts", f"{spelled(len(DEFECTS))} NNTP servers",
            f"{spelled(len(DEFECTS) - program)} planted in its host and {spelled(program)} in its program"],
        "docs/assurance.md": [f"{len(DEFECTS)} planted defects", f"{cuts:,} cuts"]})
    return Report("checked", cake, HOSTS, {"executable_sha256": lanes.digest(build.path), "checks": results,
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
