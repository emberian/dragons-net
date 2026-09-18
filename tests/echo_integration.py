"""Real TCP tests for an externally built native echo host; stdlib only."""
from concurrent.futures import ThreadPoolExecutor
from contextlib import contextmanager
import json
from pathlib import Path
import selectors
import socket
import struct
import subprocess
import sys
import time


@contextmanager
def server(binary, *options):
    process = subprocess.Popen([str(binary), *options], stdout=subprocess.PIPE,
                               stderr=subprocess.PIPE, text=True)
    stats = {}
    try:
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
            raise RuntimeError("echo server did not terminate")
        if process.returncode:
            raise RuntimeError(f"echo server failed: {process.returncode}: {error}")
        stats.update(json.loads(error))


def exchange(port, payload, chunk=4096, slow=False):
    with socket.create_connection(("127.0.0.1", port), timeout=10) as sock:
        def send():
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


def main():
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
                except socket.timeout:
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
        total += exchange(port, b"slot reusable after timeout")
        cases += 2
    if idle["idle_expired"] < 1:
        raise AssertionError("idle cleanup path not exercised")
    print(json.dumps({"cases": cases, "verified_bytes": total, "host": stats, "idle_host": idle}))


if __name__ == "__main__":
    main()
