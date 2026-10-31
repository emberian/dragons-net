#!/usr/bin/env python3
# SPDX-License-Identifier: AGPL-3.0-or-later
"""The io_uring lane: the ring layer (native/uring.c) on the running kernel, and the echo host on it
(native/echo_uring.c), built from the same generated kernel as the poll host:

- the layer's own check (native/uring_check.c): what a ring refuses, registration included, a kernel
  that refuses io_uring through a seccomp filter, more submissions and completions than the queues
  hold, cancellation by token and by descriptor, a message between two threads' rings, waits that
  end, a ring closed with an operation live;
- the generated code and its runtime assembled once a copy, every global symbol prefixed with the
  copy's number and no other left;
- the poll host's echo corpus (tests/echo_integration.py) against the host as built, with one
  thread and with a thread a core, and against its build with AddressSanitizer and
  UndefinedBehaviorSanitizer;
- a stop by SIGTERM or SIGINT with receives and sends in flight ends with status 0, each of them
  cancelled and reaped;
- each idle connection expires once, those holding a reply counted apart;
- run on two cores, a thread a core, each pinned to its own;
- the send buffer asked for is the one the connection's socket has;
- with exactly the descriptors the host counts every slot serves at once, and one fewer is refused;
- four slow readers at once, each taking more than an idle time, are all kept;
- in the test build, with libfiu's points: a receive's completion made stale ends the host with
  status 1; an interrupted or refused wait, a full completion queue and submissions taken one at a
  time leave a run as without them; a hand-over that fails, and a socket that cannot be shaped, cost
  only their connection; a connection handed over after the stop is closed at once; a stop a thread
  cannot be told of ends the host with status 2; and io_uring refused, missing or too old, a feature
  missing and a thread that cannot start or be created are refused at the start by name, the started
  threads stopped; so are too few descriptors, and a start record that cannot be written;
- each defect planted in echo_uring.c and uring.c is caught by the check it is planted for, saying
  what that check says of it.

The report records the kernel, its io_uring features and kernel.io_uring_disabled.
"""
from __future__ import annotations

import argparse
from collections.abc import Callable
from concurrent.futures import Future
from dataclasses import dataclass
import json
import os
from pathlib import Path
import platform
import re
import selectors
import signal
import socket
import subprocess
import sys
import time
from typing import Any, Self

sys.path.insert(0, str(Path(__file__).resolve().parent))
import lanes  # the path above is what makes it importable
from lanes import LaneError, Report

OUT = lanes.ROOT / "build/uring"
NATIVE = lanes.NATIVE
ECHO = NATIVE / "echo_uring.c"
LAYER = NATIVE / "uring.c"
CHECK = NATIVE / "uring_check.c"
CORPUS = lanes.ROOT / "tests/echo_integration.py"
HOSTS = [ECHO, LAYER, CHECK, NATIVE / "uring.h", NATIVE / "accept_policy.h", NATIVE / "faults.h", *lanes.RUNTIME]
COPIES = int(re.findall(r"COPIES = (\d+)", ECHO.read_text())[0])
SANITIZED = ["-fsanitize=address,undefined", "-fno-sanitize-recover=all", "-fno-omit-frame-pointer"]
# LeakSanitizer cannot run under ptrace, which records what a check reads (scripts/once.py).
SANITIZER_ENV = {**os.environ, "ASAN_OPTIONS": "detect_leaks=0"}
WAIT = 20


def globals_of(obj: Path, *, defined: bool) -> set[str]:
    flag = "--defined-only" if defined else "--undefined-only"
    listing = lanes.loud(["nm", flag, "--extern-only", str(obj)], timeout=60, what=f"reading {obj.name}")
    return {line.split()[-1] for line in listing.splitlines() if line.strip()}


def copies(cake: str, out: Path = OUT) -> list[Path]:
    """The generated echo and its runtime, once a copy, every global symbol either defines prefixed
    with `copyK_`; a copy that still defines or needs a name of another is refused. Built in `out`."""
    (out / "echo.pnk").write_text(lanes.emit("emit-echo", timeout=60))
    assembly = lanes.assemble(cake, out / "echo.pnk")
    runtime = lanes.compile_object(NATIVE / "cake_runtime.c", out / "cake_runtime.o")
    names = globals_of(assembly.with_suffix(".o"), defined=True) | globals_of(runtime, defined=True)
    if not {"cml_main", "cml_heap", "dn_echo", "dn_runtime_setup"} <= names:
        raise LaneError(f"the image lacks a name a copy renames: {sorted(names)}")
    objects = []
    for k in range(COPIES):
        renames = [f"-D{name}=copy{k}_{name}" for name in sorted(names)]
        for source, obj in ((assembly, out / f"copy{k}-echo.o"),
                            (NATIVE / "cake_runtime.c", out / f"copy{k}-runtime.o")):
            lanes.loud([lanes.cc(), *lanes.HARDENING, "-g", f"-I{NATIVE}", *renames, "-c", str(source),
                        "-o", str(obj)], timeout=120, what=f"compiling copy {k} of {source.name}")
            defined, needed = globals_of(obj, defined=True), globals_of(obj, defined=False)
            if not defined or any(not name.startswith(f"copy{k}_") for name in defined) or needed & names:
                raise LaneError(f"copy {k} of {source.name} defines {sorted(defined)} "
                                f"and needs {sorted(needed & names)}")
            objects.append(obj)
    return objects


@dataclass
class Builds:
    """The host as it is built, with the sanitizers, and as its test build, with libfiu's points."""

    plain: Path
    sanitized: Path
    fiu: Path


def build(name: str, objects: list[Path], echo: Path = ECHO, layer: Path = LAYER, *,
          all_three: bool = True) -> Builds:
    sources = [echo, layer, *objects]
    plain = lanes.link(OUT / name, sources, flags=["-lpthread"], check=(echo, layer) == (ECHO, LAYER))
    fiu = lanes.pinned_tool("libfiu")
    with_points = lanes.link(OUT / f"{name}-fiu", sources, includes=[fiu], check=False,
                             flags=["-DFIU_ENABLE=1", f"-L{fiu}", "-lfiu", f"-Wl,-rpath,{fiu}", "-lpthread"])
    if not all_three:
        return Builds(plain, plain, with_points)
    return Builds(plain, lanes.link(OUT / f"{name}-sanitized", sources, flags=[*SANITIZED, "-lpthread"],
                                    check=False), with_points)


def corpus(binary: Path, *options: str, env: dict[str, str] | None = None) -> dict[str, Any]:
    """The poll host's corpus, `options` given to every server it starts."""
    run = binary
    if options:
        run = OUT / f"{binary.name}-{'-'.join(o.strip('-') for o in options)}"
        run.write_text(f'#!/bin/sh\nexec {binary} {" ".join(options)} "$@"\n')
        run.chmod(0o755)
    # A session of its own, so that a corpus out of time is killed with the hosts it started.
    with subprocess.Popen([sys.executable, str(CORPUS), str(run)], stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                          text=True, env=env, start_new_session=True) as done:
        try:
            out, err = done.communicate(timeout=300)
        except subprocess.TimeoutExpired:
            os.killpg(done.pid, signal.SIGKILL)
            done.communicate()
            raise LaneError(f"the echo corpus on {run.name} took more than 300 s") from None
    if done.returncode:
        raise LaneError(f"the echo corpus failed on {run.name}:\n{out[-2000:]}{err[-4000:]}")
    measured: dict[str, Any] = json.loads(out)
    return measured


def limited(command: list[str], limit: int | None) -> list[str]:
    """`command` run with at most `limit` descriptors: set by a shell before it starts, since the lane's
    threads make a hook between fork and exec unsafe."""
    return command if limit is None else ["sh", "-c", 'ulimit -n "$0" && exec "$@"', str(limit), *command]


class Host:
    """The host started with `options`, read its record once it listens, and stopped by `end`, which
    a host that does not stop in time does not outlive; as a context, killed on leaving it if not
    ended by then, so that no check leaves a host behind, which the trace of a check would wait for."""

    def __init__(self, binary: Path, *options: str, env: dict[str, str] | None = None,
                 limit: int | None = None) -> None:
        self.process = subprocess.Popen(limited([str(binary), *options], limit), stdout=subprocess.PIPE,
                                        stderr=subprocess.PIPE, text=True, env=env)
        self.err = ""
        self.ended: tuple[int, str] | None = None
        out = self.process.stdout
        if out is None:
            raise LaneError("the host has no output pipe")
        with selectors.DefaultSelector() as ready:
            ready.register(out, selectors.EVENT_READ)
            line = out.readline() if ready.select(WAIT) else ""
        try:
            self.info: dict[str, Any] = json.loads(line)
            self.port: int = self.info["port"]
        except (ValueError, KeyError):
            self.end(signal.SIGKILL)
            raise LaneError(f"{binary.name} {' '.join(options)} did not start: {line!r} {self.err[-2000:]}") from None

    def __enter__(self) -> Self:
        return self

    def __exit__(self, *raised: object) -> None:
        if self.ended is None:
            try:
                self.end(signal.SIGKILL)
            except LaneError:
                pass

    def end(self, signum: int = signal.SIGTERM) -> tuple[int, str]:
        """Its status and what it wrote to standard error, once `signum` has ended it; ended already,
        as it was then."""
        if self.ended:
            return self.ended
        if self.process.poll() is None:
            self.process.send_signal(signum)
        try:
            _, self.err = self.process.communicate(timeout=WAIT)
        except subprocess.TimeoutExpired:
            self.process.kill()
            _, self.err = self.process.communicate()
            self.ended = (self.process.returncode, self.err)
            raise LaneError(f"the host did not end within {WAIT} s of signal {signum}") from None
        self.ended = (self.process.returncode, self.err)
        return self.ended

    def counters(self, signum: int = signal.SIGTERM) -> dict[str, Any]:
        """The counters it writes as it stops, which it has to do with status 0."""
        status, err = self.end(signum)
        if status or not err.strip():
            raise LaneError(f"the host ended with status {status}:\n{err[-3000:]}")
        counted: dict[str, Any] = json.loads(err.strip().splitlines()[-1])
        return counted


def exchange(port: int, data: bytes = b"a byte") -> None:
    with socket.create_connection(("127.0.0.1", port), timeout=5) as sock:
        sock.sendall(data)
        got = b""
        while len(got) < len(data):
            chunk = sock.recv(len(data) - len(got))
            if not chunk:
                raise LaneError(f"the host closed a connection that exchanged {got!r} of {data!r}")
            got += chunk
        if got != data:
            raise LaneError(f"the host echoed {got!r} for {data!r}")


def stuck(port: int) -> socket.socket:
    """A client that writes much and reads nothing, leaving the host with a reply it cannot hand over."""
    sock = socket.socket()
    sock.setsockopt(socket.SOL_SOCKET, socket.SO_RCVBUF, 2048)
    sock.connect(("127.0.0.1", port))
    sock.setblocking(False)
    try:
        for _ in range(200):
            sock.send(b"x" * 4096)
    except BlockingIOError:
        pass
    return sock


def stop_in_flight(binary: Path, env: dict[str, str] | None = None, signum: int = signal.SIGTERM) -> dict[str, Any]:
    """Eight connections waiting to be read from, each seen to have been served, and eight whose replies
    the kernel cannot take, each seen to hold some, then `signum`: the host ends with status 0 within its
    time, every operation cancelled."""
    held: list[socket.socket] = []
    with Host(binary, "--write-chunk", "4096", "--send-buffer", "4096", env=env) as host:
        try:
            for _ in range(8):
                held.append(socket.create_connection(("127.0.0.1", host.port), timeout=5))
                held[-1].sendall(b"x")
                if held[-1].recv(1) != b"x":
                    raise LaneError("a connection was not served before the stop")
            held += [stuck(host.port) for _ in range(8)]
            deadline = time.monotonic() + WAIT
            while any(send_queue(host.port, sock.getsockname()[1]) == 0 for sock in held[8:]):
                if time.monotonic() > deadline:
                    raise LaneError("a reply the client does not take never reached the host's send queue")
                time.sleep(0.05)
            stats = host.counters(signum)
        finally:
            for sock in held:
                sock.close()
    if stats["accepted"] != 16 or stats["cancelled"] < 16:
        raise LaneError(f"the stop cancelled {stats['cancelled']} operations of 16 connections: {stats}")
    return stats


def closed_by_host(sock: socket.socket, within: float) -> bool:
    """Whether the host ends the connection within `within` seconds; what it still sends is read off."""
    sock.setblocking(True)
    sock.settimeout(within)
    try:
        while sock.recv(65536):
            pass
    except TimeoutError:
        return False
    except OSError:
        pass
    return True


def idle(binary: Path) -> dict[str, Any]:
    """Four idle connections and four holding replies they never take: each expires once, within its
    time and a margin, and the four holding replies are counted apart."""
    held: list[socket.socket] = []
    with Host(binary, "--idle-ms", "300", "--send-buffer", "2048") as host:
        try:
            held = [socket.create_connection(("127.0.0.1", host.port), timeout=5) for _ in range(4)]
            held += [stuck(host.port) for _ in range(4)]
            # Nothing is read before they expire, which would renew the deadlines.
            time.sleep(1.5)
            if not all(closed_by_host(sock, 2) for sock in held):
                raise LaneError("an idle connection was not closed")
            stats = host.counters()
        finally:
            for sock in held:
                sock.close()
    if (stats["idle_expired"], stats["expired_pending"]) != (8, 4):
        raise LaneError(f"eight idle connections, four holding replies, expired as {stats}")
    return stats


def send_queue(port: int, client: int) -> int:
    """How many octets the host's socket of the connection from `client` holds to send (/proc/net/tcp)."""
    for line in Path("/proc/net/tcp").read_text().splitlines()[1:]:
        fields = line.split()
        local, remote = int(fields[1].split(":")[1], 16), int(fields[2].split(":")[1], 16)
        if (local, remote) == (port, client):
            return int(fields[4].split(":")[0], 16)
    raise LaneError(f"no socket of the host from port {client}")


def send_buffer(binary: Path) -> dict[str, int]:
    """The send buffer asked for is the socket's: a reply a client never takes fills the host's send
    queue to a few kilobytes with `--send-buffer 2048`, and to far more without."""
    queued = {}
    for name, options in (("asked", ["--send-buffer", "2048"]), ("default", [])):
        with Host(binary, *options) as host, stuck(host.port) as sock:
            time.sleep(0.5)
            queued[name] = send_queue(host.port, sock.getsockname()[1])
    if queued["asked"] > 8192 or queued["default"] < 65536:
        raise LaneError(f"the send buffer asked for is not the socket's: {queued} octets queued")
    return queued


def full_table(binary: Path) -> int:
    """With two threads and exactly the descriptors the host counts, the standard three, the listener,
    the signals, three rings and the 32 slots, every slot serves at once; one descriptor fewer is
    refused at the start."""
    limit = 6 + 2 + 32
    held: list[socket.socket] = []
    with Host(binary, "--threads", "2", limit=limit) as host:
        try:
            for i in range(32):
                sock = socket.create_connection(("127.0.0.1", host.port), timeout=5)
                held.append(sock)
                sock.sendall(bytes([i]))
                if sock.recv(1) != bytes([i]):
                    raise LaneError(f"slot {i} of 32 was not served within the descriptors counted")
        except OSError as error:
            raise LaneError(f"the full table within the descriptors counted failed: {error}") from None
        finally:
            for sock in held:
                sock.close()
        stats = host.counters()
    if stats["accept_errors"]:
        raise LaneError(f"the full table within the descriptors counted paused accepting: {stats}")
    refused(binary, ["--threads", "2"], 1, "too few file descriptors for the slot table and the threads",
            limit=limit - 1)
    return limit


def slow_reader(port: int) -> None:
    """A reader that takes a reply about twice what the small buffers on the way hold in bursts a fifth
    of an idle time apart, and has to get all of it."""
    payload = b"y" * 16384
    with socket.socket() as sock:
        sock.setsockopt(socket.SOL_SOCKET, socket.SO_RCVBUF, 1024)
        sock.settimeout(5)
        sock.connect(("127.0.0.1", port))
        sock.sendall(payload)
        received = 0
        while received < len(payload):
            time.sleep(0.2)
            sock.setblocking(False)
            try:
                while received < len(payload):
                    chunk = sock.recv(len(payload) - received)
                    if chunk == b"":
                        raise LaneError(f"a slow reader was dropped after {received} octets")
                    received += len(chunk)
            except BlockingIOError:
                pass
            sock.settimeout(5)


def slow_readers(binary: Path) -> int:
    """Four slow readers at once, each kept: a host that drops a reader making progress fails. That a
    send's progress alone renews a deadline is not separated, here or by the corpus on this host: its
    next send is submitted as the last completes, so a reply reaches the kernel within the time its
    receive renewed, and a host whose sends renew nothing keeps the readers too. Nor is a receive's
    renewal, which a send follows at once."""
    with Host(binary, "--idle-ms", "1000", "--write-chunk", "64", "--send-buffer", "2048") as host:
        try:
            with lanes.pool(4) as readers:
                for reader in [readers.submit(slow_reader, host.port) for _ in range(4)]:
                    reader.result()
        except OSError as error:
            raise LaneError(f"a slow reader failed: {error}") from None
        host.end()
    return 4


def pinned(binary: Path) -> dict[str, list[str]]:
    """Run on two cores, the host starts a thread a core, each pinned to its own; asked for three, it
    pins them to the two in turn."""
    seen = {}
    for threads, want in (("", ["0", "1"]), ("3", ["0", "0", "1"])):
        options = ["--threads", threads] if threads else []
        with Host(Path("/usr/bin/taskset"), "-c", "0,1", str(binary), *options) as host:
            tasks = sorted(Path(f"/proc/{host.process.pid}/task").iterdir())
            cpus = [re.findall(r"^Cpus_allowed_list:\s*(\S+)$", (task / "status").read_text(), re.MULTILINE)[0]
                    for task in tasks]
            host.counters()
        # The main thread keeps the two; each other is a worker's.
        workers = sorted(c for c in cpus if c != "0-1")
        if host.info["threads"] != len(want) or workers != want or cpus.count("0-1") != 1:
            raise LaneError(f"on cores 0 and 1 with {options or 'no option'} the threads ran on {cpus}: {host.info}")
        seen[threads or "default"] = cpus
    return seen


def fiu_env(enable: str) -> dict[str, str]:
    fiu = lanes.pinned_tool("libfiu")
    env = {k: v for k, v in os.environ.items() if not k.startswith("FIU_")}
    return {**env, "LD_PRELOAD": str(fiu / "fiu_run_preload.so"), "LD_LIBRARY_PATH": str(fiu), "FIU_ENABLE": enable}


def stale(builds: Builds) -> int:
    """A receive's completion made to look as if the connection before had submitted it (`dn/stale`)
    ends the host with status 1, naming the generations, before it is taken for this one's."""
    with Host(builds.fiu, env=fiu_env("enable name=dn/stale,failinfo=1,onetime")) as host:
        with socket.create_connection(("127.0.0.1", host.port), timeout=5) as sock:
            sock.sendall(b"x")
            closed_by_host(sock, 5)
        status, err = host.end()
    if status != 1 or "a completion for generation 0 of slot" not in err:
        raise LaneError(f"a stale completion ended the host with {status}:\n{err[-2000:]}")
    return 1


def transients(builds: Builds) -> int:
    """An interrupted wait, a full completion queue and a shortage of memory, once each, and every
    submission taken one at a time: sixteen connections are served and stopped as without them."""
    cases = ["dn/uring-enter,failinfo=4,onetime", "dn/uring-enter,failinfo=16,onetime",
             "dn/uring-enter,failinfo=11,onetime", "dn/uring-short,failinfo=1"]
    for case in cases:
        try:
            with Host(builds.fiu, "--threads", "2", env=fiu_env(f"enable name={case}")) as host:
                try:
                    for k in range(16):
                        exchange(host.port, bytes([k]) * 100)
                except (LaneError, OSError) as error:
                    raise LaneError(f"{error}; the host said {host.end(signal.SIGKILL)[1][-1000:]}") from None
                status, err = host.end()
        except LaneError as error:
            raise LaneError(f"with {case}: {error}") from None
        if status:
            raise LaneError(f"with {case} the host ended with status {status}:\n{err[-2000:]}")
    held = stop_in_flight(builds.fiu, fiu_env("enable name=dn/uring-short,failinfo=1"))
    if held["cancelled"] < 16:
        raise LaneError(f"a stop with every submission taken alone cancelled {held['cancelled']}")
    return len(cases) + 1


def costs_one(builds: Builds, point: str) -> None:
    """With `point` failing the first connection's hand-over, that connection alone is closed, and every
    slot serves afterwards: its place was given back."""
    held: list[socket.socket] = []
    with Host(builds.fiu, "--threads", "2", "--send-buffer", "4096",
              env=fiu_env(f"enable name={point},failinfo=1,onetime")) as host:
        try:
            with socket.create_connection(("127.0.0.1", host.port), timeout=5) as first:
                if not closed_by_host(first, 5):
                    raise LaneError(f"with {point} the first connection was kept")
            for i in range(32):
                sock = socket.create_connection(("127.0.0.1", host.port), timeout=5)
                held.append(sock)
                sock.sendall(bytes([i]))
                if sock.recv(1) != bytes([i]):
                    raise LaneError(f"with {point} slot {i} of 32 was not served afterwards")
        except OSError as error:
            raise LaneError(f"with {point}: {error}") from None
        finally:
            for sock in held:
                sock.close()
        stats = host.counters()
    if stats["accepted"] != 32 + (point == "dn/echo-handover"):
        raise LaneError(f"with {point} the host counted {stats['accepted']} connections accepted")


def late(builds: Builds) -> int:
    """A connection handed over after the stop (`dn/echo-late`: once the thread has given a place back, and
    held for it), its peer open, is closed at once: the host ends with status 0 well before the
    connection's idle time."""
    with Host(builds.fiu, "--threads", "1", env=fiu_env("enable name=dn/echo-late,failinfo=1")) as host, \
            socket.create_connection(("127.0.0.1", host.port), timeout=5):
        time.sleep(0.2)
        began = time.monotonic()
        try:
            stats = host.counters()
        except LaneError as error:
            raise LaneError(f"a stop with a connection handed over after it: {error}") from None
    took = time.monotonic() - began
    if took > 5 or stats["accepted"] != 2:
        raise LaneError(f"a stop with a connection handed over after it took {took:.1f} s: {stats}")
    return 1


def stop_lost(builds: Builds) -> int:
    """A stop a thread could not be told of (`dn/echo-stop-lost`) ends the host with status 2 and the
    reason, rather than leave it waiting for the thread for good."""
    with Host(builds.fiu, "--threads", "1", env=fiu_env("enable name=dn/echo-stop-lost,failinfo=1")) as host:
        try:
            status, err = host.end()
        except LaneError as error:
            raise LaneError(f"a stop lost: {error}") from None
    if status != 2 or "could not tell thread 0 to stop" not in err:
        raise LaneError(f"a stop lost ended the host with {status}:\n{err[-1000:]}")
    return 1


def faults(builds: Builds) -> int:
    costs_one(builds, "dn/echo-handover")
    costs_one(builds, "dn/echo-sndbuf")
    return 2 + late(builds) + stop_lost(builds)


def refused(binary: Path, args: list[str], status: int, message: str, *, env: dict[str, str] | None = None,
            limit: int | None = None) -> None:
    """Started with `args`, the host ends with `status` and `message`; refused at the start, having
    printed nothing."""
    try:
        done = subprocess.run(limited([str(binary), *args], limit), capture_output=True, text=True, timeout=WAIT,
                              check=False, env=env)
    except subprocess.TimeoutExpired:
        raise LaneError(f"{binary.name} {' '.join(args)} did not end when refused ({message})") from None
    if done.returncode != status or message not in done.stderr or (status == 1 and done.stdout):
        raise LaneError(f"{binary.name} {' '.join(args)} ended {done.returncode}, not {status} with {message!r}:\n"
                        f"{done.stdout}{done.stderr}")


def refusals(builds: Builds) -> int:
    """The refusals at the start: those of the kernel injected at the setup's call (`dn/uring-setup`),
    as the layer's check also sees a seccomp filter give them."""
    setup = "enable name=dn/uring-setup,failinfo="
    cases: list[tuple[list[str], int, str, dict[str, str] | None, int | None]] = [
        ([], 1, "io_uring: refused here (a seccomp filter or kernel.io_uring_disabled)", fiu_env(setup + "1"), None),
        ([], 1, "io_uring: not in this kernel", fiu_env(setup + "38"), None),
        ([], 1, "io_uring: the kernel lacks a setup flag (it is older than 6.6)", fiu_env(setup + "22"), None),
        ([], 1, "io_uring: the kernel lacks the feature of waits with a timeout",
         fiu_env("enable name=dn/uring-features,failinfo=256"), None),
        (["--threads", "4"], 1, "thread 2 could not start: a fault was planted; stopping the others",
         fiu_env("enable name=dn/echo-thread,failinfo=3"), None),
        (["--threads", "4"], 1, "thread 1 could not start: pthread_create: Resource temporarily unavailable",
         fiu_env("enable name=dn/echo-create,failinfo=2"), None),
        # A failure of the call that submits and waits ends the host, from whichever thread meets it.
        ([], 2, "io_uring_enter: Input/output error", fiu_env("enable name=dn/uring-enter,failinfo=5"), None),
        ([], 1, "too few file descriptors for the slot table and the threads", None, 30),
        (["--threads", "8"], 1, "too few file descriptors for the slot table and the threads", None, 44),
    ]
    for args, status, message, env, limit in cases:
        refused(builds.fiu if env else builds.plain, args, status, message, env=env, limit=limit)
    # A record of the start that cannot be written stops the threads that run, with status 1.
    with subprocess.Popen([str(builds.plain), "--threads", "2"], stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                          text=True) as host:
        if host.stdout:
            host.stdout.close()
        try:
            _, err = host.communicate(timeout=WAIT)
        except subprocess.TimeoutExpired:
            host.kill()
            host.communicate()
            raise LaneError("a host whose start record could not be written did not end") from None
    if host.returncode != 1 or "fflush: Broken pipe" not in err:
        raise LaneError(f"a host whose start record could not be written ended {host.returncode}:\n{err[-1000:]}")
    return len(cases) + 1


@dataclass(frozen=True)
class Defect:
    """A defect planted in `file`, the check that has to catch it, and a part of what that check has
    to say of it."""

    what: str
    pattern: str
    becomes: str
    caught_by: str
    sign: str
    file: Path = ECHO
    times: int = 1


# Not planted, since nothing outside could tell: an expiry counted again while its cancellation is in
# flight, which completes within the same wait; and a submission cut short not followed at once by the
# rest, which the caller's next wait submits.
DEFECTS = [
    Defect("a connection closed with its receive in flight", "    if (!s->ops) {\n        finish(w, i);",
           "    if (1) {\n        finish(w, i);", "idle", "an idle connection was not closed"),
    Defect("a place given back never counted", "        --admitted;\n        /* The test", "        /* The test",
           "corpus", "bytes([i]) * 113"),
    Defect("a connection admitted past the slots", "!accepting && admitted < SLOTS", "!accepting && admitted <= SLOTS",
           "corpus", "more than 32 connections serviced"),
    Defect("a partial send taken as whole", "    s->sent += n;\n", "    s->sent = s->length;\n", "corpus",
           "echo differs"),
    Defect("the rest of a reply dropped for a read", "    if (s->sent < s->length) {\n        arm_send(w, i);",
           "    if (s->sent < s->length) {\n        arm_recv(w, i);", "corpus", "echo differs"),
    Defect("an idle deadline not kept", "if (now - s->active >= idle_ms) {", "if (0) {", "idle",
           "an idle connection was not closed"),
    Defect("a reply held at expiry not counted apart", "            if (s->length) ++w->n.expired_pending;\n", "",
           "idle", "eight idle connections, four holding replies, expired as"),
    Defect("a thread ends with operations live",
           "if (w->stopping && !w->held && !w->ring.live && !w->awaiting_late) break;",
           "if (w->stopping) break;", "stop", "the host ended with status -6"),
    Defect("SIGINT left to its default", "    sigaddset(&mask, SIGINT);\n", "", "sigint",
           "the host ended with status -2"),
    Defect("the send buffer never set", "    if (send_buffer) {\n        int size", "    if (0) {\n        int size",
           "sndbuf", "the send buffer asked for is not the socket's"),
    Defect("a thread that cannot start leaves the others serving", "    if (stopping) tell_stop();",
           "    (void)0;", "refusals", "did not end when refused (thread 2 could not start"),
    Defect("a thread left where the scheduler puts it",
           "    int pinned = pthread_setaffinity_np(pthread_self(), sizeof one, &one);",
           "    int pinned = 0 * pthread_setaffinity_np(pthread_self(), 0, &one);", "pinned",
           "on cores 0 and 1 with"),
    Defect("a stop lost ignored", "        } else if (c->res < 0) {\n            dn_harness_now(",
           "        } else if (0) {\n            dn_harness_now(", "faults", "a stop lost: the host did not end"),
    Defect("a completion of another generation taken", "    if (s->fd < 0 || DN_TOKEN_GEN(t) != s->gen || !s->ops)",
           "    if (s->fd < 0 || !s->ops)", "stale", "a stale completion ended the host with 0"),
    Defect("a failed hand-over keeping its place",
           "            close((int)DN_TOKEN_SLOT(t));\n            --admitted;\n",
           "            close((int)DN_TOKEN_SLOT(t));\n", "faults", "with dn/echo-handover: timed out"),
    Defect("a connection handed over after the stop served",
           "    if (w->stopping) end(w, i);\n    else arm_recv(w, i);",
           "    arm_recv(w, i);", "faults", "a stop with a connection handed over after it: the host did not end"),
    Defect("an interrupted wait taken for an error", "            if (code == EINTR) continue;\n", "", "transients",
           "Interrupted system call", LAYER),
    Defect("a full completion queue taken for an error", "if (code == EBUSY || code == EAGAIN) return 0;",
           "if (code == EAGAIN) return 0;", "transients", "Device or resource busy", LAYER),
    Defect("a completion reaped without its count", "        --r->live;\n", "", "layer",
           "refused submissions left 0 others and", LAYER),
    Defect("the ring left unrestricted",
           "    if (registered(fd, IORING_REGISTER_RESTRICTIONS, rules, (unsigned)n + 1))", "    if (0)",
           "layer", "not -EACCES", LAYER),
    Defect("registration left open", "    rules[n].register_op = IORING_REGISTER_ENABLE_RINGS;",
           "    rules[n].register_op = IORING_REGISTER_FILES;", "layer",
           "registering a file on an enabled ring was not refused", LAYER),
]


def caught(defect: Defect, objects: list[Path]) -> None:
    """The check `defect` is planted for fails on the host built with it, saying its sign."""
    name = re.sub(r"[^a-z]+", "-", defect.what)
    planted = OUT / f"defect-{name}-{defect.file.name}"
    planted.write_text(lanes.plant(defect.file.read_text(), defect.pattern, defect.becomes, defect.times,
                                   f"{defect.file.name} for {defect.what!r}", exact=True))
    echo, layer = (planted, LAYER) if defect.file == ECHO else (ECHO, planted)
    if defect.caught_by == "layer":
        binary = lanes.link(OUT / f"check-{name}", [CHECK, layer], flags=["-lpthread"], check=False)
        try:
            done = subprocess.run([str(binary)], capture_output=True, text=True, timeout=120, check=False)
            said = f"status {done.returncode}: {done.stderr}"
        except subprocess.TimeoutExpired:
            said = "timed out"
        if "status 0:" in said or defect.sign not in said:
            raise LaneError(f"the layer check did not catch {defect.what!r} as {defect.sign!r}: {said[-500:]}")
        return
    builds = build(f"echo-{name}", objects, echo, layer, all_three=False)
    check: Callable[[], Any] = {
        "corpus": lambda: corpus(builds.plain), "idle": lambda: idle(builds.plain),
        "stop": lambda: stop_in_flight(builds.plain),
        "sigint": lambda: stop_in_flight(builds.plain, None, signal.SIGINT),
        "sndbuf": lambda: send_buffer(builds.plain), "refusals": lambda: refusals(builds),
        "stale": lambda: stale(builds), "faults": lambda: faults(builds),
        "transients": lambda: transients(builds), "pinned": lambda: pinned(builds.plain)}[defect.caught_by]
    try:
        check()
    except (LaneError, OSError, subprocess.TimeoutExpired) as error:
        said = f"{type(error).__name__}: {error}"
        if defect.sign not in said:
            raise LaneError(f"{defect.what!r} was caught by {defect.caught_by}, but not as {defect.sign!r}: "
                            f"{said[-800:]}") from None
        return
    raise LaneError(f"the {defect.caught_by} check did not catch {defect.what!r}")


def io_uring_disabled() -> str:
    path = Path("/proc/sys/kernel/io_uring_disabled")
    return path.read_text().strip() if path.is_file() else "absent"


def check(cake: str) -> Report:
    layer = lanes.link(OUT / "uring-check", [CHECK, LAYER], flags=["-lpthread"])
    layer_cases = json.loads(lanes.loud([str(layer)], timeout=120, what="the io_uring layer check"))["uring_cases"]
    objects = copies(cake)
    builds = build("dn-echo-uring", objects)
    with Host(builds.plain) as host:
        host.end()
    measured = {"layer_cases": layer_cases, "kernel": platform.release(), "io_uring_disabled": io_uring_disabled(),
                "io_uring_features": host.info["io_uring_features"], "copies": COPIES, "threads": host.info["threads"]}
    with lanes.pool() as pool:
        runs: dict[str, Future[Any]] = {
            "corpus": pool.submit(corpus, builds.plain),
            "corpus_one_thread": pool.submit(corpus, builds.plain, "--threads", "1"),
            "corpus_sanitized": pool.submit(corpus, builds.sanitized, env=SANITIZER_ENV),
            "stop": pool.submit(stop_in_flight, builds.plain),
            "stop_by_sigint": pool.submit(stop_in_flight, builds.plain, None, signal.SIGINT),
            "stop_sanitized": pool.submit(stop_in_flight, builds.sanitized, SANITIZER_ENV),
            "idle": pool.submit(idle, builds.plain),
            "send_buffer": pool.submit(send_buffer, builds.plain),
            "full_table_descriptors": pool.submit(full_table, builds.plain),
            "stale_completions": pool.submit(stale, builds),
            "transients": pool.submit(transients, builds),
            "faults": pool.submit(faults, builds),
            "pinned": pool.submit(pinned, builds.plain),
            "refusals": pool.submit(refusals, builds)}
        defects = [pool.submit(caught, defect, objects) for defect in DEFECTS]
        measured |= {name: run.result() for name, run in runs.items()}
        for defect in defects:
            defect.result()
    # Timed against an idle time, so run alone, after the rest.
    measured["slow_readers"] = slow_readers(builds.plain)
    measured["defects_caught"] = len(DEFECTS)
    return Report("native-tested", cake, HOSTS, {"assurance": "the echo corpus, stops, refusals and planted defects "
                                                             "on the running kernel, not a proof of the adapter",
                                                 "measurements": measured})


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--cake", default=os.environ.get("CAKE"))
    args = parser.parse_args()
    lanes.require_platform(parser)
    cake = lanes.given_cake(parser, args.cake)
    lanes.lane_main("URING", OUT, lambda: check(cake))


if __name__ == "__main__":
    main()
