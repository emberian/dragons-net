#!/usr/bin/env python3
# SPDX-License-Identifier: AGPL-3.0-or-later
"""The NNTP server: the session's program (`DN.Server.Session`) with its socket host
(`native/nntp_host.c`), run on loopback and checked from outside.

Every byte a client reads has to be what `session_ref` computes from the bytes it sent. The standard
library's `nntplib` is greeted, reads the capabilities and the help, and quits. A pipeline of lines
of many kinds — lines of 512 and 513 octets among them — gets its replies in order, and the
connection closes after QUIT. A line cut between two reads, and an empty line on its own, are
answered once their rest arrives. A client that shuts down its sending side gets the replies to
its whole lines and then the end of the stream; a reset mid-line leaves the server serving. A
client that reads nothing until its receive queue is full gets every byte once it reads. On a clock
the check moves, the deadlines of the first command, of a line and of inactivity close their
connections at the time the program asked to be woken at and not a millisecond before; on the real
clock, the first command's closes at ten seconds. Sixty-four connections are served, a sixty-fifth
waits until one closes. The server takes no turn with nothing to do, and every run ends on
SIGTERM.
"""
from __future__ import annotations

import argparse
from collections.abc import Callable, Iterator
from contextlib import contextmanager
import fcntl
import json
import os
from pathlib import Path
import selectors
import signal
import socket
import struct
import subprocess
import sys
import termios
import time
from typing import IO
import warnings

sys.path.insert(0, str(Path(__file__).resolve().parent))
import lanes  # the path above is what makes these importable
from lanes import NATIVE, ROOT, LaneError, Report
import session_native
import session_ref as ref

OUT = ROOT / "build/nntp"
HOST = NATIVE / "nntp_host.c"
HOSTS = [HOST, NATIVE / "session_calls.h", NATIVE / "cake_header.c", NATIVE / "accept_policy.h", *lanes.RUNTIME]
REVISION, SOURCE = b"0123abc", b"https://example.org/dragons-net"
TEXTS = ref.texts(REVISION, SOURCE)
GREETING = TEXTS["greeting"]
TIMEOUT = 10


def expected(stream: bytes) -> bytes:
    """What a client that sent `stream` reads: the greeting, then the reply to each whole line."""
    return GREETING + b"".join(TEXTS[a] for a in ref.answers(stream))


class Server:
    """The server on a free loopback port. With `virtual`, on a clock the check moves, and reporting
    each turn; otherwise on the real clock, reporting nothing. A turn has to have events, unless
    the one before it filled its batch or the time it asked to be woken at has come."""

    def __init__(self, binary: Path, virtual: bool, *options: str) -> None:
        self.report_read = self.clock_write = -1
        extra: list[str] = []
        keep: list[int] = []
        if virtual:
            self.report_read, report_write = os.pipe()
            clock_read, self.clock_write = os.pipe()
            extra = ["--report-fd", str(report_write), "--clock-fd", str(clock_read)]
            keep = [report_write, clock_read]
        self.proc = subprocess.Popen(
            [str(binary), "--port", "0", "--revision", REVISION.decode(), "--source", SOURCE.decode(), *extra,
             *options], stdout=subprocess.PIPE, stderr=subprocess.PIPE, pass_fds=keep, text=True)
        for fd in keep:
            os.close(fd)
        self.reports = b""
        self.batch = session_native.layout(OUT)["BATCH"]
        self.last = {"events": 0, "wake": 0}
        try:
            self.port = self.read_port()
        except BaseException:
            self.close()
            raise

    def read_port(self) -> int:
        out = self.pipe(self.proc.stdout)
        self.wait_for(out.fileno(), "port")
        line = out.readline()
        if not line:
            raise LaneError(f"the server gave no port{self.why()}")
        return int(json.loads(line)["port"])

    @staticmethod
    def pipe(stream: IO[str] | None) -> IO[str]:
        if stream is None:
            raise LaneError("the server has no pipe")
        return stream

    def wait_for(self, fd: int, what: str) -> None:
        with selectors.DefaultSelector() as ready:
            ready.register(fd, selectors.EVENT_READ)
            if not ready.select(TIMEOUT):
                raise LaneError(f"the server gave no {what} in {TIMEOUT} s{self.why()}")

    def why(self) -> str:
        if self.proc.poll() is None:
            return ""
        return f" and ended with status {self.proc.returncode}: {self.pipe(self.proc.stderr).read()[-300:]!r}"

    def turn(self) -> dict[str, int]:
        """The next turn the host reports."""
        while b"\n" not in self.reports:
            self.wait_for(self.report_read, "turn")
            chunk = os.read(self.report_read, 4096)
            if not chunk:
                raise LaneError(f"the server stopped reporting{self.why()}")
            self.reports += chunk
        line, self.reports = self.reports.split(b"\n", 1)
        return self.checked(line)

    def checked(self, line: bytes) -> dict[str, int]:
        words = line.decode().split()
        turn = {words[k]: int(words[k + 1]) for k in range(0, len(words), 2)}
        woken = self.last["wake"] and turn["turn"] >= self.last["wake"]
        if not turn["events"] and self.last["events"] < self.batch and not woken:
            raise LaneError(f"the server took a turn with nothing to do: {line.decode()!r}")
        self.last = turn
        return turn

    def idle(self, seconds: float) -> None:
        """Check every turn the server reports within `seconds`."""
        end = time.monotonic() + seconds
        with selectors.DefaultSelector() as ready:
            ready.register(self.report_read, selectors.EVENT_READ)
            while (left := end - time.monotonic()) > 0:
                if ready.select(left):
                    self.reports += os.read(self.report_read, 65536)
                    *done, self.reports = self.reports.split(b"\n")
                    for line in done:
                        self.checked(line)

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
        if self.proc.returncode != 0 or "stopped: a signal" not in err:
            raise LaneError(f"on SIGTERM the server ended with status {self.proc.returncode}: {err[-300:]!r}")
        if self.report_read >= 0:
            while chunk := os.read(self.report_read, 65536):
                self.reports += chunk
            for line in self.reports.splitlines():
                self.checked(line)

    def close(self) -> None:
        if self.proc.poll() is None:
            self.proc.kill()
            self.proc.communicate()
        for fd in (self.report_read, self.clock_write):
            if fd >= 0:
                os.close(fd)
        self.report_read = self.clock_write = -1


@contextmanager
def serving(binary: Path, virtual: bool = False, *options: str) -> Iterator[Server]:
    server = Server(binary, virtual, *options)
    try:
        yield server
        server.stop()
    finally:
        server.close()


def client(port: int, receive_buffer: int = 0) -> socket.socket:
    s = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
    if receive_buffer:
        s.setsockopt(socket.SOL_SOCKET, socket.SO_RCVBUF, receive_buffer)
    s.settimeout(TIMEOUT)
    s.connect(("127.0.0.1", port))
    return s


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
    while chunk := s.recv(65536):
        got += chunk
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


def queued(s: socket.socket) -> int:
    """The bytes waiting in the socket's receive queue."""
    count = struct.pack("i", 0)
    return int(struct.unpack("i", fcntl.ioctl(s.fileno(), termios.FIONREAD, count))[0])


def reset(s: socket.socket) -> None:
    s.setsockopt(socket.SOL_SOCKET, socket.SO_LINGER, struct.pack("ii", 1, 0))
    s.close()


def lines(*texts: str) -> bytes:
    return b"".join(t.encode() + b"\r\n" for t in texts)


def with_nntplib(binary: Path) -> str:
    try:
        with warnings.catch_warnings():
            warnings.simplefilter("ignore", DeprecationWarning)
            import nntplib  # noqa: PLC0415  (deprecated, and gone after Python 3.12)
    except ImportError:
        raise LaneError("this check needs the nntplib of Python 3.12") from None
    with serving(binary) as server:
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
    stream = lines("CAPABILITIES", "capabilities foo", "help", "", "\tHEAD\t", "HEAD 7", "STAT <a@b>",
                   "STAT 12abc", "LIST", "HELP" + " " * 506, "HELP" + " " * 507) + b"HE\rLP\r\n" + \
        b"HELP\0\r\n" + b"HELP\n" + lines("QUIT", "HELP")
    with serving(binary) as server:
        s = client(server.port)
        s.sendall(stream)
        got = read_to_end(s)
        s.close()
    if got != expected(stream):
        raise LaneError(f"a pipeline got {got[-160:]!r}")
    return f"{len(ref.answers(stream))} replies"


def cut_lines(binary: Path) -> str:
    """Each part is sent once the host has taken the one before in a turn of its own."""
    parts = [b"HEL", b"P\r\n", b"\r\n", b"CAPAB", b"ILITIES\r\n", b"QUIT\r\n"]
    with serving(binary, True) as server:
        s = client(server.port)
        server.turn()
        read_expected(s, GREETING, "the greeting")
        sent = b""
        for part in parts:
            s.sendall(part)
            server.turn()
            before = expected(sent)
            sent += part
            read_expected(s, expected(sent)[len(before):], f"after {part!r}")
        if not ended(s):
            raise LaneError("after QUIT the connection stayed open")
        s.close()
    return f"{len(parts)} parts, each answered when its line was whole"


def half_close(binary: Path) -> str:
    stream = b"HELP\r\nSTAT 1\r\nCAPAB"
    with serving(binary) as server:
        s = client(server.port)
        s.sendall(stream)
        s.shutdown(socket.SHUT_WR)
        got = read_to_end(s)
        s.close()
    if got != expected(stream):
        raise LaneError(f"after the end of input the client got {got[-160:]!r}")
    return "the replies to the whole lines, then the end"


def reset_mid_line(binary: Path) -> str:
    with serving(binary) as server:
        s = client(server.port)
        read_expected(s, GREETING, "the greeting")
        s.sendall(b"HEL")
        reset(s)
        s = client(server.port)
        s.sendall(b"QUIT\r\n")
        got = read_to_end(s)
        s.close()
    if got != expected(b"QUIT\r\n"):
        raise LaneError(f"after a reset the next client got {got!r}")
    return "the next client served"


def slow_reader(binary: Path) -> str:
    # Far more than the kernel buffers on both ends hold, so that the server has to wait for room.
    stream = b"HELP\r\n" * 100 + b"QUIT\r\n"
    with serving(binary, True, "--send-buffer", "4096") as server:
        s = client(server.port, receive_buffer=1024)
        server.turn()
        s.sendall(stream)
        # The client reads nothing until the server reports a send taken only in part and its own
        # receive queue has stopped growing: the kernel took all it had room for.
        while not server.turn()["partial"]:
            pass
        held = -1
        while held != queued(s):
            held = queued(s)
            server.idle(0.1)
        got = read_to_end(s)
        s.close()
    want = expected(stream)
    if got != want:
        raise LaneError(f"a slow reader got {len(got)} bytes, not {len(want)}: {got[-120:]!r}")
    return f"{len(got)} bytes, {held} of them held in the client's queue before it read"


def deadline(binary: Path, name: str, sends: list[tuple[int, bytes]], after: int) -> str:
    """Send each part at its time; the connection has to close `after` milliseconds past the last
    turn, where the program has to ask to be woken, and not a millisecond before."""
    with serving(binary, True) as server:
        s = client(server.port)
        last = server.turn()
        read_expected(s, GREETING, "the greeting")
        sent = b""
        for at, part in sends:
            server.advance(at)
            s.sendall(part)
            last = server.turn()
            before = expected(sent)
            sent += part
            read_expected(s, expected(sent)[len(before):], f"{name}: after {part!r}")
        due = last["turn"] + after
        if last["wake"] != due:
            raise LaneError(f"{name}: the program asked to be woken at {last['wake']}, not {due}")
        server.advance(due - 1)
        # A turn of another connection, so that the host has read the clock before the look.
        other = client(server.port)
        server.turn()
        read_expected(other, GREETING, "the other connection's greeting")
        if not still_open(s):
            raise LaneError(f"{name}: the connection closed before {due}")
        server.advance(due)
        closing = server.turn()
        if closing["turn"] != due or not ended(s):
            raise LaneError(f"{name}: the connection was not closed at {due}: {closing}")
        s.close()
        other.close()
    return f"closed at {due}"


def real_deadline(binary: Path) -> str:
    """The first command's deadline on the real clock: ten seconds, and not before."""
    with serving(binary) as server:
        s = client(server.port)
        read_expected(s, GREETING, "the greeting")
        began = time.monotonic()
        s.settimeout(ref.FIRST_COMMAND / 1000 + 5)
        closed = ended(s)
        took = time.monotonic() - began
        s.close()
    if not closed or not ref.FIRST_COMMAND / 1000 - 0.1 <= took <= ref.FIRST_COMMAND / 1000 + 1:
        raise LaneError(f"on the real clock the first command's deadline closed after {took:.2f} s")
    return f"closed after {took:.2f} s"


def crowd(binary: Path) -> str:
    with serving(binary, True) as server:
        clients = [client(server.port) for _ in range(ref.CONNS)]
        for s in clients:
            read_expected(s, GREETING, "a greeting")
        extra = client(server.port)
        clients[1].sendall(b"HELP\r\n")
        read_expected(clients[1], TEXTS["help"], "the help")
        # A host that listens with its table full takes turns for nothing here.
        server.idle(0.05)
        if not still_open(extra):
            raise LaneError("a connection past the table was served while the table was full")
        clients[0].sendall(b"QUIT\r\n")
        read_expected(clients[0], TEXTS["quit"], "the reply to QUIT")
        read_expected(extra, GREETING, "the greeting past the table")
        for s in [*clients, extra]:
            s.close()
    return f"{ref.CONNS} served, the next once one closed"


def check(cake: str) -> Report:
    OUT.mkdir(parents=True, exist_ok=True)
    (OUT / "dn_session_layout.h").write_text(lanes.emit("emit-session-layout"))
    binary = session_native.build(cake, "nntp", lanes.emit("emit-session"), OUT, HOST)
    checks: dict[str, Callable[[], str]] = {
        "nntplib": lambda: with_nntplib(binary),
        "pipeline": lambda: pipeline(binary),
        "lines cut between reads": lambda: cut_lines(binary),
        "half close": lambda: half_close(binary),
        "reset mid-line": lambda: reset_mid_line(binary),
        "slow reader": lambda: slow_reader(binary),
        "first command": lambda: deadline(binary, "the first command", [], ref.FIRST_COMMAND),
        "a line": lambda: deadline(binary, "a line", [(5, b"HELP\r\nHEL")], ref.LINE_TIME),
        "inactivity": lambda: deadline(binary, "inactivity", [(5, b"HELP\r\n")], ref.INACTIVITY),
        "first command on the real clock": lambda: real_deadline(binary),
        "sixty-five clients": lambda: crowd(binary),
    }
    results = {}
    for name, run in checks.items():
        try:
            results[name] = run()
        except OSError as error:
            raise LaneError(f"{name}: {error!r}") from None
        except LaneError as error:
            raise LaneError(f"{name}: {error}") from None
    return Report("checked", cake, HOSTS, {"executable_sha256": lanes.digest(binary), "checks": results})


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--cake", default=os.environ.get("CAKE"))
    args = parser.parse_args()
    lanes.require_platform(parser)
    cake = lanes.given_cake(parser, args.cake)
    lanes.lane_main("NNTP", OUT, lambda: check(cake))


if __name__ == "__main__":
    main()
