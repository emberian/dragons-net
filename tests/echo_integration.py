"""Real TCP tests for an externally built native echo host; stdlib only."""
from __future__ import annotations

from collections.abc import Iterator
from concurrent.futures import ThreadPoolExecutor
from contextlib import contextmanager
import json
from pathlib import Path
import resource
import selectors
import socket
import struct
import subprocess
import sys
import time
from typing import Any


@contextmanager
def server(binary: Path, *options: str,
           descriptors: int | None = None) -> Iterator[tuple[int, dict[str, Any]]]:
    limit = None if descriptors is None else (lambda: resource.setrlimit(
        resource.RLIMIT_NOFILE, (descriptors, descriptors)))
    # The descriptor limit is what one of the cases below exercises. The call runs before
    # any thread is started here, which is what makes preexec_fn safe in this file.
    process = subprocess.Popen(
        [str(binary), *options], stdout=subprocess.PIPE, stderr=subprocess.PIPE,
        text=True, preexec_fn=limit)  # noqa: PLW1509
    stats: dict[str, Any] = {}
    try:
        if process.stdout is None:
            raise RuntimeError("echo server has no output pipe")
        with selectors.DefaultSelector() as ready:
            ready.register(process.stdout, selectors.EVENT_READ)
            if not ready.select(10):
                raise RuntimeError("echo server startup timed out")
        info = json.loads(process.stdout.readline())
        yield info["port"], stats
    finally:
        process.terminate()
        try:
            _, error = process.communicate(timeout=5)
        except subprocess.TimeoutExpired:
            process.kill()
            process.communicate()
            raise RuntimeError("echo server did not terminate") from None
        if process.returncode:
            raise RuntimeError(f"echo server failed: {process.returncode}: {error}")
        stats.update(json.loads(error))


SLOTS = 32


def small_reader(port: int, buffer_bytes: int = 2048) -> socket.socket:
    """A client whose receive window is small, set before connecting so it takes effect."""
    sock = socket.socket()
    sock.setsockopt(socket.SOL_SOCKET, socket.SO_RCVBUF, buffer_bytes)
    sock.settimeout(10)
    sock.connect(("127.0.0.1", port))
    return sock


def exchange(port: int, payload: bytes, chunk: int = 4096, slow: bool = False) -> int:
    with socket.create_connection(("127.0.0.1", port), timeout=10) as sock:
        def send() -> None:
            for offset in range(0, len(payload), chunk):
                sock.sendall(payload[offset:offset+chunk])
            sock.shutdown(socket.SHUT_WR)
        # Full-duplex operation avoids a test-client deadlock on large streams.
        with ThreadPoolExecutor(max_workers=1) as executor:
            sender = executor.submit(send)
            result = bytearray()
            while True:
                data = sock.recv(997)
                if not data:
                    break
                result.extend(data)
                if len(result) > len(payload):
                    raise AssertionError("echo duplicated data")
                if slow:
                    time.sleep(0.0002)
            sender.result(timeout=10)
        if result != payload:
            raise AssertionError(f"echo differs: sent={len(payload)} received={len(result)}")
    return len(payload)


def main() -> None:
    binary = Path(sys.argv[1]).resolve()
    total, cases = 0, 0
    with server(binary, "--write-chunk", "7") as (port, stats):
        payloads = [b"", b"\x00", bytes(range(256)), b"x" * 4095,
                    b"y" * 4096, b"z" * 4097, bytes(range(256)) * 2048]
        for data in payloads:
            total += exchange(port, data, chunk=13, slow=len(data) > 10000)
            cases += 1
        with ThreadPoolExecutor(max_workers=8) as pool:
            jobs = [pool.submit(exchange, port, bytes([i])*20000, 29) for i in range(8)]
            total += sum(job.result(timeout=30) for job in jobs)
            cases += len(jobs)
        # Abrupt reset during pending output, followed by repeated slot reuse.
        for i in range(40):
            with socket.create_connection(("127.0.0.1", port), timeout=5) as sock:
                sock.sendall(b"abandoned" * 128)
                sock.setsockopt(socket.SOL_SOCKET, socket.SO_LINGER, struct.pack("ii", 1, 0))
            total += exchange(port, bytes([i]) * 113, chunk=1)
            cases += 1
        # Fill every admitted slot, proving acceptance by exchanging a byte on
        # each. The next connection may sit in the OS backlog, but must not be
        # serviced until an admitted slot is released.
        held = []
        try:
            for _ in range(32):
                sock = socket.create_connection(("127.0.0.1", port), timeout=5)
                held.append(sock)
                sock.sendall(b"s")
                if sock.recv(1) != b"s":
                    raise AssertionError("slot admission failed")
                total += 1
            with socket.create_connection(("127.0.0.1", port), timeout=5) as waiting:
                waiting.sendall(b"q")
                waiting.settimeout(0.2)
                try:
                    waiting.recv(1)
                except TimeoutError:
                    pass
                else:
                    raise AssertionError("more than 32 connections serviced")
                held.pop().close()
                waiting.settimeout(5)
                if waiting.recv(1) != b"q":
                    raise AssertionError("released slot not reusable")
                total += 1
            cases += 33
        finally:
            for sock in held:
                sock.close()
    if stats["kernel_bytes"] < total or stats["kernel_calls"] == 0 or stats["partial_progress"] == 0:
        raise AssertionError(f"native/partial-write path not exercised: {stats}")
    with server(binary, "--idle-ms", "250") as (port, idle):
        with socket.create_connection(("127.0.0.1", port), timeout=5) as sock:
            if sock.recv(1) != b"":
                raise AssertionError("idle connection not closed")
        # Clients that write and never read leave the server holding replies it cannot
        # hand over. If such slots did not expire, they would take the whole table with
        # them: after the timeout a fresh client must still be served.
        stuck = []
        try:
            for _ in range(SLOTS):
                sock = small_reader(port)
                sock.setblocking(False)
                stuck.append(sock)
                try:
                    for _ in range(500):
                        sock.send(b"x" * 4096)
                except (BlockingIOError, OSError):
                    pass
            time.sleep(1.5)
            total += exchange(port, b"the table came back")
            cases += 1
        finally:
            for sock in stuck:
                sock.close()
        total += exchange(port, b"slot reusable after timeout")
        cases += 3
    if idle["idle_expired"] < 1:
        raise AssertionError("idle cleanup path not exercised")
    if idle["recv_renewals"] < 1:
        raise AssertionError("receiving did not renew the idle timer")
    # A flood of connections under a descriptor limit must not cost the ones already being
    # served. The startup check keeps enough descriptors for every slot, so this exercises
    # the listener going quiet when the table is full rather than a real EMFILE.
    with server(binary, descriptors=44) as (port, starved):
        held = [socket.create_connection(("127.0.0.1", port), timeout=5) for _ in range(8)]
        try:
            for sock in held:
                sock.sendall(b"still here")
                if sock.recv(64) != b"still here":
                    raise AssertionError("a served connection was lost")
            extra = []
            try:
                for _ in range(40):
                    extra.append(socket.create_connection(("127.0.0.1", port), timeout=5))
            except OSError:
                pass
            for sock in extra:
                sock.close()
            for sock in held:
                sock.sendall(b"survived")
                if sock.recv(64) != b"survived":
                    raise AssertionError("a served connection was lost after the flood")
                total += 8
            cases += 1
        finally:
            for sock in held:
                sock.close()

    if starved["accepted"] < 8:
        raise AssertionError(f"the flood never reached the listener: {starved}")
    # A slow but live reader must not be dropped. The server's send buffer is small, so the
    # reply is handed over in many rounds across more than the idle timeout: the connection
    # survives only because progress on the send side renews the deadline.
    with server(binary, "--idle-ms", "400", "--write-chunk", "64",
                "--send-buffer", "2048") as (port, slow), \
            small_reader(port, 1024) as sock:
        sock.settimeout(5)
        payload = b"y" * 4096
        sock.sendall(payload)
        received = 0
        while received < len(payload):
            chunk = sock.recv(256)
            if chunk == b"":
                raise AssertionError("a reader making progress was dropped")
            received += len(chunk)
            time.sleep(0.05)
        total += received
        cases += 1
    if slow["partial_progress"] < 8:
        raise AssertionError(f"the handover was not slow enough to exercise renewal: {slow}")
    print(json.dumps({"cases": cases, "verified_bytes": total, "host": stats,
                      "idle_host": idle, "starved_host": starved,
                      "slow_reader_host": slow}))


if __name__ == "__main__":
    main()
