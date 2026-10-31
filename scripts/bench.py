#!/usr/bin/env python3
# SPDX-License-Identifier: AGPL-3.0-or-later
"""Measure the hosts against one another (docs/bench.md): the echo on poll and on io_uring, the
NNTP server waiting with poll and with io_uring, and INN's reader where it is installed, as it is
and with TCP_NODELAY, under one open-loop load (native/load.c).

`check`, the bench lane, judges no number. It builds every host, the load and the allocation
counter; holds the load to faulty servers of its own, which it must catch; and puts a second of
load with slow readers on each host, every reply right and none owed. The NNTP replies the load
expects are read from each host, and the server's two hosts must give the same.

`measure` writes build/bench/measured.json, whose rows `table` prints for docs/bench.md: the
machine, and for each host a sweep of rates to the highest it keeps; then, in rounds, steady load
at half the lowest rate any host of its kind keeps and overload at one and a half times its own;
each NNTP command alone; allocations a reply from a run of their own, system calls a reply from one
under strace. The server's time, switches and allocations are counted over the load's window
alone. `profile` runs the NNTP server under callgrind with the mix or one command of it.
"""
from __future__ import annotations

import argparse
from collections.abc import Callable, Iterator
from contextlib import ExitStack, contextmanager, suppress
from dataclasses import dataclass, field
import grp
import json
import os
from pathlib import Path
import platform
import pwd
import random
import re
import shutil
import signal
import socket
import struct
import subprocess
import sys
import tempfile
import threading
import time
from typing import Any, BinaryIO, Self

sys.path.insert(0, str(Path(__file__).resolve().parent))
# The path above is what makes these importable.
import lanes
from lanes import NATIVE, ROOT, LaneError, Report
import uring_check

OUT = ROOT / "build/bench"
LOAD = NATIVE / "load.c"
COUNTER = NATIVE / "alloc_count.c"
NODELAY = NATIVE / "nodelay.c"
NNTP_HOST = NATIVE / "nntp_host.c"
NNTP_EXTRA = [NATIVE / "store.c", NATIVE / "jobs.c", NATIVE / "tls.c", NATIVE / "accounts.c", NATIVE / "uring.c"]
HOSTS = [LOAD, COUNTER, NODELAY, NATIVE / "echo_server.c", NATIVE / "echo_uring.c", NNTP_HOST, *NNTP_EXTRA,
         *lanes.RUNTIME]
GROUP = "bench.test"
ARTICLES = 200
# The replies RFC 3977 gives as a block that ends with a line holding a dot.
BLOCKS = {100, 101, 215, 220, 221, 222, 224, 225, 230, 231}
# Echo payloads, a size and how many of every ten requests have it.
ECHO_SIZES = [(64, 6), (512, 3), (4096, 1)]
SLOW_MS = 10
SLOW_READERS = 2
LOAD_BOUND = 0.7
# A rate kept: replies within 3% of it, none owed, the 99th percentile under 20 ms.
KEPT_SHARE, KEPT_P99_NS = 0.97, 20_000_000
NNRPD = Path("/usr/lib/news/bin/nnrpd")
# INN's settings this measurement sets; the rest are the package's.
INN_PATHS = ("etc", "db", "run", "log", "tmp", "spool", "articles", "overview", "incoming", "outgoing", "archive",
             "http")


@dataclass
class Host:
    """A server as started: its command, the connections the load opens (a host serves no more
    at once), whether it speaks NNTP, and what it is built from. One of ours prints a record with its
    port and takes a store; INN's reader listens on `port` and reads the store `env` names."""

    name: str
    command: list[str]
    conns: int
    nntp: bool
    binary: Path
    limits: dict[str, Any] = field(default_factory=dict)
    port: int = 0
    env: dict[str, str] = field(default_factory=dict)

    @property
    def ours(self) -> bool:
        return not self.port

    @property
    def kind(self) -> str:
        return "nntp" if self.nntp else "echo"


def exchange(send: bytes, expect: bytes) -> bytes:
    return struct.pack("<I", len(send)) + send + struct.pack("<I", len(expect)) + expect


def exchanges(blob: bytes) -> list[tuple[bytes, bytes]]:
    """The exchanges `exchange` wrote into `blob`."""
    found, at = [], 0
    while at < len(blob):
        parts = []
        for _ in range(2):
            (n,) = struct.unpack_from("<I", blob, at)
            parts.append(blob[at + 4:at + 4 + n])
            at += 4 + n
        found.append((parts[0], parts[1]))
    return found


def echo_requests() -> bytes:
    rng = random.Random(7)  # noqa: S311 -- a fixed seed, so that every run sends the same payloads
    sizes = [size for size, share in ECHO_SIZES for _ in range(share)]
    payloads = [bytes(rng.randrange(256) for _ in range(size)) for size in sizes]
    # The slow readers send the first request: the largest.
    payloads.sort(key=len, reverse=True)
    return exchange(b"", b"") + b"".join(exchange(p, p) for p in payloads)


def article(k: int) -> bytes:
    body = "".join(f"line {i} of article {k}, written to be read back whole\r\n" for i in range(40 + k % 60))
    return (f"From: bench@x.example\r\nNewsgroups: {GROUP}\r\nSubject: article {k}\r\n"
            f"Message-ID: <b{k}@x.example>\r\n" + (f"References: <b{k - 1}@x.example>\r\n" if k % 3 else "")
            + "\r\n" + body + ".\r\n").encode()


def five() -> list[int]:
    """The articles the load reads, the first the largest, which the slow readers ask for."""
    rng = random.Random(11)  # noqa: S311 -- a fixed seed, so that every run reads the same articles
    largest = max(range(1, ARTICLES + 1), key=lambda n: (n - 1) % 60)
    return [largest, *rng.sample([n for n in range(1, ARTICLES + 1) if n != largest], 4)]


def nntp_commands() -> list[bytes]:
    """A reader's mix over the five articles: each read whole by number, two of them by
    Message-ID too, and two by their headers; STAT, OVER of twenty articles and GROUP."""
    numbers = five()
    first = 1 + sum(numbers) % (ARTICLES - 20)
    # Article n holds Message-ID <b(n-1)@x.example>: the server numbers from 1 what was posted from 0.
    mix = ([f"ARTICLE {n}" for n in numbers] + [f"ARTICLE <b{n - 1}@x.example>" for n in numbers[:2]]
           + [f"HEAD {n}" for n in numbers[:2]] + [f"STAT {numbers[2]}", f"OVER {first}-{first + 19}",
                                                  f"GROUP {GROUP}"])
    return [line.encode() + b"\r\n" for line in mix]


def reply_of(f: BinaryIO) -> bytes:
    """A reply as the server sends it, its block whole, read off `f`."""
    line = f.readline()
    if len(line) < 5 or not line.endswith(b"\r\n"):
        raise LaneError(f"a reply line {line!r}")
    got = line
    if int(line[:3]) in BLOCKS:
        while (line := f.readline()) != b".\r\n":
            if not line.endswith(b"\r\n"):
                raise LaneError(f"a block ended in {line!r}")
            got += line
        got += line
    return got


def nntp_requests(port: int, commands: list[bytes] | None = None) -> bytes:
    """The opening and the requests, the mix's or `commands`, with the replies this server gives
    them, read one at a time."""
    with socket.create_connection(("127.0.0.1", port), timeout=30) as c, c.makefile("rb") as f:
        greeting = reply_of(f)
        setup = f"GROUP {GROUP}\r\n".encode()
        c.sendall(setup)
        opened = greeting + reply_of(f)
        out = exchange(setup, opened)
        for command in commands or nntp_commands():
            c.sendall(command)
            reply = reply_of(f)
            if reply[:1] != b"2":
                raise LaneError(f"{command!r} answered {reply[:80]!r}")
            out += exchange(command, reply)
    return out


def post_articles(port: int) -> None:
    with socket.create_connection(("127.0.0.1", port), timeout=30) as c, c.makefile("rb") as f:
        reply_of(f)
        for k in range(ARTICLES):
            c.sendall(b"POST\r\n")
            if not (said := reply_of(f)).startswith(b"340"):
                raise LaneError(f"POST answered {said!r}")
            c.sendall(article(k))
            if not (said := reply_of(f)).startswith(b"240"):
                raise LaneError(f"article {k} answered {said!r}")


def pinned(cpus: str | None) -> list[str]:
    return ["taskset", "-c", cpus] if cpus else []


class Server:
    """A host started on `cpus`, under `wrap` if given, its record read once it listens; `pid` is
    the host's own. Killed on leaving."""

    def __init__(self, host: Host, cpus: str | None, extra: list[str], env: dict[str, str] | None = None,
                 wrap: list[str] | None = None) -> None:
        given = {**(env or os.environ), **host.env}
        # Both the host's shims and those asked here.
        preload = [p for p in (host.env.get("LD_PRELOAD"), (env or {}).get("LD_PRELOAD")) if p]
        if preload:
            given["LD_PRELOAD"] = ":".join(preload)
        self.process = subprocess.Popen([*(wrap or []), *pinned(cpus), *host.command, *extra],
                                        stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True, env=given)
        self.pid = self.process.pid
        self.port = host.port or self.record(host)
        if not host.ours:
            self.listening(host)
        # taskset and the host exec in turn: a wrapper that traces has the host as its one child.
        if wrap and (children := Path(f"/proc/{self.pid}/task/{self.pid}/children").read_text().split()):
            self.pid = int(children[0])

    def record(self, host: Host) -> int:
        line = self.process.stdout.readline() if self.process.stdout else ""
        if not line:
            raise LaneError(f"{host.name} did not start: {self.process.communicate(timeout=30)[1][-500:]}")
        return int(json.loads(line)["port"])

    def listening(self, host: Host) -> None:
        for _ in range(100):
            with suppress(OSError), socket.create_connection(("127.0.0.1", self.port), timeout=1):
                return
            time.sleep(0.1)
        raise LaneError(f"{host.name} did not listen: {self.process.communicate(timeout=30)[1][-500:]}")

    def stop(self) -> str:
        os.kill(self.pid, signal.SIGTERM)
        try:
            _, err = self.process.communicate(timeout=30)
        except subprocess.TimeoutExpired:
            self.process.kill()
            _, err = self.process.communicate()
            raise LaneError(f"a host did not stop: {err[-300:]}") from None
        return err

    def __enter__(self) -> Self:
        return self

    def __exit__(self, *_: object) -> None:
        # The host under a wrapper only while it is still the wrapper's child: a pid reaped is reused.
        if self.process.poll() is None:
            if self.pid != self.process.pid and str(self.pid) in children(self.process.pid):
                os.kill(self.pid, signal.SIGKILL)
            self.process.kill()
        self.process.communicate()


def stat_of(pid: int | str) -> list[str]:
    return Path(f"/proc/{pid}/stat").read_text().rsplit(")", 1)[1].split()


def children(pid: int) -> list[str]:
    found = []
    for proc in Path("/proc").iterdir():
        with suppress(OSError, IndexError):
            if proc.name.isdigit() and int(stat_of(proc.name)[1]) == pid:
                found.append(proc.name)
    return found


def run_ns(pid: int | str) -> int:
    """The time the process's threads have run, in nanoseconds: /proc's ticks would round each of a
    forking server's processes, that runs a millisecond a second, down to nothing."""
    total = 0
    for task in Path(f"/proc/{pid}/task").iterdir():
        with suppress(OSError):
            total += int((task / "schedstat").read_text().split()[0])
    return total


def usage(pid: int) -> dict[str, int]:
    """The process's CPU time with its children's, those running to the nanosecond and those reaped
    to the tick; its share in the kernel, to the tick; its threads' context switches; its memory high
    water."""
    tick = os.sysconf("SC_CLK_TCK")
    fields = stat_of(pid)
    user, system = int(fields[11]) + int(fields[13]), int(fields[12]) + int(fields[14])
    if not Path(f"/proc/{pid}/schedstat").is_file():
        raise LaneError("/proc gives no schedstat: the kernel keeps no time a thread ran")
    spent = run_ns(pid) + (int(fields[13]) + int(fields[14])) * 1_000_000_000 // tick
    for name in children(pid):
        with suppress(OSError, IndexError):
            child = stat_of(name)
            user, system = user + int(child[11]), system + int(child[12])
            spent += run_ns(name)
    found = {"cpu_ns": spent, "cpu_user_ms": user * 1000 // tick, "cpu_system_ms": system * 1000 // tick,
             "voluntary_switches": 0, "involuntary_switches": 0}
    for task in Path(f"/proc/{pid}/task").iterdir():
        # A thread may end between the listing and the reading.
        with suppress(OSError):
            status = (task / "status").read_text()
            for kind, name in (("voluntary", "voluntary"), ("involuntary", "nonvoluntary")):
                found[f"{kind}_switches"] += int(re.findall(rf"^{name}_ctxt_switches:\s+(\d+)", status,
                                                            re.MULTILINE)[0])
    status = Path(f"/proc/{pid}/status").read_text()
    found["high_water_kb"] = int(re.findall(r"^VmHWM:\s+(\d+)", status, re.MULTILINE)[0])
    return found


def load(binary: Path, port: int, requests: Path, cpus: str | None, *, conns: int, rate: int, seconds: int,
         warmup: int, slow: int, threads: int, slow_ms: int = SLOW_MS,
         marks: tuple[Callable[[], None], Callable[[], None]] | None = None) -> dict[str, Any]:
    """The load's record of a run; `marks` are called as its window opens and closes."""
    command = [*pinned(cpus), str(binary), "--port", str(port), "--requests", str(requests), "--conns", str(conns),
               "--rate", str(rate), "--seconds", str(seconds), "--warmup", str(warmup), "--slow", str(slow),
               "--slow-ms", str(slow_ms), "--threads", str(threads)]
    with subprocess.Popen(command, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True) as run:
        watch = threading.Timer(seconds + warmup + 60, run.kill)
        watch.start()
        try:
            said = []
            for line in iter(run.stderr.readline if run.stderr else str, ""):
                if line == "window\n" and marks:
                    marks[0]()
                elif line == "end\n":
                    if marks:
                        marks[1]()
                    break
                else:
                    said.append(line)
            out, rest = run.communicate()
        finally:
            watch.cancel()
    if run.returncode not in (0, 1) or not out:
        raise LaneError(f"the load failed with status {run.returncode}: {''.join(said)[-300:]}{rest[-300:]}")
    result: dict[str, Any] = json.loads(out)
    result["status"] = run.returncode
    return result


def counts_of(path: Path | None) -> int:
    if path is None:
        return 0
    held = path.read_bytes()
    if len(held) < 24:
        raise LaneError("the allocation counter was not loaded")
    return int(struct.unpack("<3Q", held[:24])[0])


def run_load(server: Server, binary: Path, requests: Path, cpus: str | None, counts: Path | None = None,
             faulty: bool = False, **given: Any) -> dict[str, Any]:
    """A run of the load on `server`, its time, switches and allocations (from the file `counts`, if
    the counter is loaded) taken over the load's window alone. A wrong reply or a lost connection
    stops the measurement, but from a server `faulty` on purpose."""
    taken: list[tuple[dict[str, int], int]] = []

    def snap() -> None:
        taken.append((usage(server.pid), counts_of(counts)))

    # A process a connection: those of the run before gone and reaped, or their ends would fall in
    # this run's window.
    for _ in range(200):
        if not children(server.pid):
            break
        time.sleep(0.05)

    result = load(binary, server.port, requests, cpus, marks=(snap, snap), **given)
    if len(taken) != 2:
        raise LaneError("the load did not mark its window")
    (before, held), (after, now) = taken
    result["server"] = {k: after[k] - before[k] for k in after if k != "high_water_kb"}
    result["server"]["high_water_kb"] = after["high_water_kb"]
    result["server"]["allocations"] = now - held
    result["server"]["allocations_before"] = held
    if not faulty and (result["wrong"] or result["lost"]):
        raise LaneError(f"{result['wrong']} wrong replies, {result['lost']} connections lost: {result['why']}")
    return result


def server_cpus(cpus: str) -> set[int]:
    found: set[int] = set()
    for part in cpus.split(","):
        low, _, high = part.partition("-")
        found |= set(range(int(low), int(high or low) + 1))
    return found


def cores() -> dict[int, tuple[str, str]]:
    """Each CPU this process may run on, by its package and core: hardware threads of one core share
    its units."""
    topology = Path("/sys/devices/system/cpu")
    found = {}
    for cpu in sorted(os.sched_getaffinity(0)):
        at = topology / f"cpu{cpu}/topology"
        found[cpu] = ((at / "physical_package_id").read_text().strip(), (at / "core_id").read_text().strip())
    return found


def load_cpus(server: set[int], topology: dict[int, tuple[str, str]], wanted: int) -> list[int]:
    """`wanted` CPUs on cores the server's CPUs do not share, the first core left to the system when
    there are cores enough."""
    taken = {topology[c] for c in server if c in topology}

    def rank(c: int) -> tuple[int, int]:
        """The first hardware thread of each free core before the second."""
        return sorted(d for d in topology if topology[d] == topology[c]).index(c), c

    free = sorted((c for c in topology if topology[c] not in taken), key=rank)
    rest = [c for c in free if topology[c] != topology[min(topology)]]
    chosen = (rest if len(rest) >= wanted else free)[:wanted]
    if len(chosen) < wanted:
        raise LaneError(f"no {wanted} CPUs off the server's cores: {free}")
    return chosen


def built(cake: str) -> tuple[Path, Path, Path, list[Host]]:
    OUT.mkdir(parents=True, exist_ok=True)
    binary = lanes.link(OUT / "dn-load", [LOAD], flags=["-lpthread"])
    shims = []
    for source in (COUNTER, NODELAY):
        shims.append(OUT / f"{source.stem}.so")
        lanes.loud([lanes.cc(), "-O2", "-Wall", "-Wextra", "-Werror", "-fPIC", "-shared", str(source), "-ldl",
                    "-o", str(shims[-1])], timeout=120, what=f"linking {source.name}")
    (OUT / "echo.pnk").write_text(lanes.emit("emit-echo", timeout=60))
    echo = lanes.assemble(cake, OUT / "echo.pnk")
    poll = lanes.link(OUT / "dn-echo", [NATIVE / "echo_server.c", NATIVE / "cake_runtime.c", echo])
    objects = uring_check.copies(cake, OUT)
    ring = lanes.link(OUT / "dn-echo-uring", [uring_check.ECHO, uring_check.LAYER, *objects], flags=["-lpthread"])
    (OUT / "dn_session_layout.h").write_text(lanes.emit("emit-session-layout"))
    nntp = lanes.whole_program(cake, "dragons-nntpd", lanes.emit("emit-session"), OUT, NNTP_HOST, NNTP_EXTRA)
    layout = (OUT / "dn_session_layout.h").read_text()

    def number(text: str, name: str) -> int:
        return int(re.findall(rf"\b{name}\s*=?\s*(\d+)", text)[0])

    conns = number(layout, "DN_SESSION_CONNS")
    echo_limits = {"slots": number(NATIVE.joinpath("echo_server.c").read_text(), "SLOTS"),
                   "buffer_octets": number(NATIVE.joinpath("echo_server.c").read_text(), "CAPACITY"),
                   "ring_entries": number(uring_check.ECHO.read_text(), "ENTRIES"), "listen_backlog": "the slots"}
    host = NNTP_HOST.read_text()
    jobs = NATIVE.joinpath("jobs.c").read_text()
    nntp_limits = {"connections": conns, "input_octets": number(layout, "DN_SESSION_DATA"),
                   "action_octets": number(layout, "DN_SESSION_DATA"), "batch": number(layout, "DN_SESSION_BATCH"),
                   "lingering": number(host, "LINGERING"), "ring_entries": number(host, "RING_ENTRIES"),
                   "file_jobs": number(layout, "DN_SESSION_JOBS"), "job_octets": number(layout, "DN_SESSION_JOB_DATA"),
                   "job_workers": number(jobs, "WORKERS"), "listen_backlog": "the connections"}
    revision = ["--revision", "0123abc", "--source", "https://example.org/dn"]
    hosts = [Host("echo-poll", [str(poll)], 32, False, poll, echo_limits),
             Host("echo-uring-1", [str(ring), "--threads", "1"], 32, False, ring, echo_limits),
             Host("nntp-poll", [str(nntp), "--io", "poll", *revision], conns, True, nntp, nntp_limits),
             Host("nntp-uring", [str(nntp), *revision], conns, True, nntp, nntp_limits)]
    return binary, shims[0], shims[1], hosts


def store_options(temp: str) -> list[str]:
    return ["--spool", f"{temp}/spool", "--run-dir", f"{temp}/run", "--path-identity", "bench.example",
            "--group", GROUP]


@contextmanager
def filled(host: Host) -> Iterator[Path]:
    """A spool `host` filled with the articles, then stopped: every NNTP host serves a copy, so that
    they serve the same articles, dates and all."""
    with tempfile.TemporaryDirectory() as temp:
        for d in ("spool", "run"):
            Path(temp, d).mkdir()
        with Server(host, None, store_options(temp)) as server:
            post_articles(server.port)
            server.stop()
        yield Path(temp, "spool")


@contextmanager
def started(host: Host, cpus: str | None, spool: Path | None, env: dict[str, str] | None = None,
            wrap: list[str] | None = None) -> Iterator[tuple[Server, Path]]:
    """The host, and the requests the load sends it with the replies they must have: for NNTP, read
    from it, serving a copy of `spool`."""
    with tempfile.TemporaryDirectory() as temp:
        extra: list[str] = []
        if host.nntp and host.ours:
            if spool is None:
                raise LaneError(f"{host.name} needs a spool")
            shutil.copytree(spool, f"{temp}/spool")
            Path(temp, "run").mkdir()
            extra = store_options(temp)
        requests = Path(temp, "requests")
        with Server(host, cpus, extra, env, wrap) as server:
            requests.write_bytes(nntp_requests(server.port) if host.nntp else echo_requests())
            yield server, requests


def inn_version() -> str:
    done = subprocess.run(["dpkg-query", "-W", "-f", "${Version}", "inn2"], capture_output=True, text=True,
                          check=False, timeout=30)
    return done.stdout or "unknown"


@contextmanager
def inn(ours: Host, spool: Path, nodelay: Path) -> Iterator[list[Host]]:
    """INN's reader on a spool of its own holding the articles `ours` serves from `spool`, as files
    with the history and overview makehistory builds; nnrpd serves them without innd, which runs only
    as the user news. It forks a process a connection, all on the cores it is given. As it is, and
    with the shim that sets TCP_NODELAY, each on a port of its own."""
    with tempfile.TemporaryDirectory() as temp:
        root = Path(temp)
        paths = {name: root / ("spool/" + name if name in ("articles", "overview", "incoming", "outgoing",
                                                           "archive") else name) for name in INN_PATHS}
        for d in paths.values():
            d.mkdir(parents=True, exist_ok=True)
        for given in Path("/etc/news").iterdir():
            if given.is_file() and os.access(given, os.R_OK):
                shutil.copy(given, paths["etc"])
        kept = [line for line in Path("/etc/news/inn.conf").read_text().splitlines()
                if not re.match(rf"(path({'|'.join(INN_PATHS)}|host)|runasuser|runasgroup|nnrpdloadlimit):", line)]
        own = [f"path{name}: {d}" for name, d in paths.items()] + [
            "pathhost: bench.example", "nnrpdloadlimit: 0", f"runasuser: {pwd.getpwuid(os.getuid()).pw_name}",
            f"runasgroup: {grp.getgrgid(os.getgid()).gr_name}"]
        (paths["etc"] / "inn.conf").write_text("\n".join([*kept, *own]) + "\n")
        (paths["etc"] / "incoming.conf").write_text("")
        (paths["etc"] / "inn-secrets.conf").write_text("")
        group = paths["articles"] / GROUP.replace(".", "/")
        group.mkdir(parents=True)
        with started(ours, None, spool) as (server, _), \
                socket.create_connection(("127.0.0.1", server.port), timeout=30) as c, c.makefile("rb") as f:
            reply_of(f)
            c.sendall(f"GROUP {GROUP}\r\n".encode())
            reply_of(f)
            for k in range(1, ARTICLES + 1):
                c.sendall(f"ARTICLE {k}\r\n".encode())
                if not (got := reply_of(f)).startswith(b"220 "):
                    raise LaneError(f"article {k} for INN: {got[:80]!r}")
                lines = got.split(b"\r\n")[1:-2]
                (group / str(k)).write_bytes(b"".join((line[1:] if line.startswith(b"..") else line) + b"\n"
                                                     for line in lines))
            server.stop()
        (paths["db"] / "active").write_text(f"junk 0000000000 0000000001 n\n{GROUP} {ARTICLES:010d} 0000000001 y\n")
        for name in ("active.times", "newsgroups"):
            (paths["db"] / name).write_text("")
        env = {"INNCONF": str(paths["etc"] / "inn.conf")}
        for tool, *options in (("makehistory", "-O"), ("makedbz", "-i", "-o")):
            done = subprocess.run([str(NNRPD.parent / tool), *options, "-s", str(2 * ARTICLES)], capture_output=True,
                                  text=True, timeout=120, check=False, env={**os.environ, **env}, cwd=paths["db"])
            if done.returncode:
                raise LaneError(f"INN's {tool} failed with status {done.returncode}: {done.stderr[-500:]}")
        found = []
        for name, more in (("inn", {}), ("inn-nodelay", {"LD_PRELOAD": str(nodelay)})):
            # nnrpd binds the port it is given through innbind; the sandbox's image lets its user run it.
            with socket.socket() as probe:
                probe.bind(("127.0.0.1", 0))
                port = probe.getsockname()[1]
            found.append(Host(name, [str(NNRPD), "-D", "-f", "-p", str(port)], ours.conns, True, NNRPD,
                              {"processes": "one a connection", "loadlimit": "none", "version": inn_version(),
                               "tcp_nodelay": bool(more)}, port, {**env, **more}))
        yield found


FAULTY = r"""
import json, os, socket, sys, threading, time
fault = sys.argv[1]
listener = socket.create_server(("127.0.0.1", 0))
print(json.dumps({"port": listener.getsockname()[1]}), flush=True)

def serve(c, n):
    count = 0
    with c:
        try:
            while data := c.recv(65536):
                count += 1
                if fault == "flip" and n == 1 and count == 50:
                    data = bytes([data[0] ^ 1]) + data[1:]
                if fault == "flipslow" and n == 2 and count == 1:
                    data = bytes([data[0] ^ 1]) + data[1:]
                if fault == "close" and n == 1 and count == 10:
                    return
                if fault == "stall" and count == 300:
                    time.sleep(1)
                if fault == "late" and n == 1:
                    time.sleep(0.45)
                if fault == "silent" and n == 1 and count >= 10:
                    continue
                if fault == "extra" and n == 1 and count == 30:
                    data += b"!"
                if fault == "fork":
                    spin = time.process_time() + 0.001
                    while time.process_time() < spin:
                        pass
                c.sendall(data)
        except OSError:
            pass

n = 0
while True:
    c, _ = listener.accept()
    n += 1
    if fault != "fork":
        threading.Thread(target=serve, args=(c, n), daemon=True).start()
    elif os.fork():
        c.close()
    else:
        serve(c, n)
        os._exit(0)
"""


def faulty(fault: str) -> Host:
    """An echo of its own that misbehaves on its first connection, or on the second, the slow
    reader's, as asked: `flip` an octet of the fiftieth reply, `flipslow` one of the slow reader's
    first, `close` after ten replies, fall `silent` after ten, add an `extra` octet to the thirtieth,
    answer each request `late` by 0.45 s; on every connection, `stall` a second before the
    three-hundredth reply, or `fork` a process that spends a millisecond on each reply. Each
    connection has a thread of its own, but `fork`'s a process."""
    return Host(f"faulty-{fault}", [sys.executable, "-c", FAULTY, fault], 1, False, Path(sys.executable))


def quantile_of(cells: list[list[int]], q: float) -> int:
    """The histogram's quantile, from its cells: the top of the cell holding the rank, at most the
    greatest value."""
    total = sum(count for _, count in cells)
    rank = int(q * total)
    rank, seen = max(1, rank + (rank < q * total)), 0
    for top, count in cells:
        seen += count
        if seen >= rank:
            return top
    return cells[-1][0]


def held_to_faults(binary: Path) -> dict[str, Any]:
    """The load against servers of its own, a connection at 200 requests a second for a second's
    warm-up and a window of two, and a slow reader. A right one passes with every request due sent
    and served once, the slow reader paced, then given its megabytes. A wrong octet, the slow
    reader's too, and an octet too many are wrong replies, a closed connection a lost one. A
    connection silent from the warm-up owes every request of the window; one answering late is
    served by arrival, few in the window and none of its requests. A second's stall shows in the
    latencies as the schedule saw it, at the quantiles the cells give, and in how late requests
    went. A server's time is its window's, the processes it forks counted."""
    with tempfile.TemporaryDirectory() as temp:
        requests = Path(temp, "requests")
        requests.write_bytes(exchange(b"", b"") + exchange(b"x" * 100, b"x" * 100))
        found: dict[str, Any] = {}
        rate, warmup, seconds, slow_ms = 200, 1, 2, 1
        due = rate * seconds
        # A slow reader takes 16 octets a millisecond until the window closes.
        paced = 16 * (warmup + seconds) * 1000 // slow_ms
        expected = {"none": (0, 0, 0), "flip": (1, 1, 0), "flipslow": (1, 1, 0), "extra": (1, 1, 0),
                    "close": (1, 0, 1), "stall": (0, 0, 0), "silent": (0, 0, 0), "late": (0, 0, 0),
                    "fork": (0, 0, 0)}
        for fault, (status, wrong, lost) in expected.items():
            with Server(faulty(fault), None, []) as server:
                got = run_load(server, binary, requests, None, faulty=True, conns=1, rate=rate, seconds=seconds,
                               warmup=warmup, slow=1, threads=1, slow_ms=slow_ms)
            said = {k: got[k] for k in ("served", "completed", "sent", "owed", "wrong", "lost", "slow_octets",
                                        "slow_paced")}
            found[fault] = said
            if (got["status"], got["wrong"], got["lost"]) != (status, wrong, lost):
                raise LaneError(f"the load against a server that does {fault}: status {got['status']}, {said}, "
                                f"{got['why']!r}")
            whole = (got["sent"], got["completed"], got["owed"]) == (rate * (warmup + seconds), due, 0)
            if fault in ("none", "stall", "fork") and not (whole and due - 1 <= got["served"] <= due + 1):
                raise LaneError(f"against a server that answers {fault}, not {due} sent and served once: {said}")
            if fault == "none" and not (paced // 2 <= got["slow_paced"] <= paced + 16
                                        and got["slow_octets"] >= 1 << 20):
                raise LaneError(f"a slow reader took {got['slow_paced']} octets at its pace, not some {paced}, "
                                f"and {got['slow_octets']} in all")
            if fault == "silent" and got["owed"] != due:
                raise LaneError(f"a connection silent from the warm-up left {got['owed']} requests owed, not {due}")
            # Answers 0.45 s apart arrive at 1.35, 1.8, 2.25 and 2.7 s in the window; each request
            # went out after the one before was answered, so none fell due in the window.
            if fault == "late" and (got["served"], got["completed"], got["owed"]) != (4, 0, due):
                raise LaneError(f"against a server that answers 0.45 s late, not 4 served by arrival: {said}")
            if fault == "stall":
                # A second's stall delays some two hundred requests by a falling amount, from a second
                # down: some hundred by half a second or more.
                cells = got["latency_ns"]["cells"]
                late = sum(count for top, count in cells if top >= 500_000_000)
                if late < 60:
                    raise LaneError(f"a second's stall left {late} requests half a second late, not some 100")
                for name, q in (("p50", 0.5), ("p90", 0.9), ("p99", 0.99), ("p999", 0.999), ("p9999", 0.9999)):
                    if got["latency_ns"][name] != min(quantile_of(cells, q), got["latency_ns"]["max"]):
                        raise LaneError(f"the load's {name} is {got['latency_ns'][name]}, its cells say "
                                        f"{quantile_of(cells, q)}")
                # One request in flight: those behind the stalled one went late too.
                if got["send_late_ns"]["p99"] < 500_000_000:
                    raise LaneError(f"behind a second's stall requests went {got['send_late_ns']['p99']} ns late")
                found[fault]["half_a_second_late"] = late
            if fault == "fork":
                # A millisecond a reply, and a little more: the window's, not the warm-up's too.
                spent = got["server"]["cpu_ns"] / 1e6
                if not 0.9 * got["served"] <= spent <= 1.4 * got["served"]:
                    raise LaneError(f"a millisecond a reply in forked processes counted as {spent:.0f} ms "
                                    f"for {got['served']} replies")
                found[fault]["server_ms"] = round(spent)
    return found


def cells_checked(binary: Path) -> int:
    """The load's histogram has the cells its scheme says: exact below 128, then 64 a power of two."""
    tops = list(range(128))
    for shift in range(1, 58):
        tops += [((m + 1) << shift) - 1 for m in range(64, 128)]
    printed = [int(line) for line in lanes.loud([str(binary), "--cells"], timeout=60, what="dn-load --cells").split()]
    if printed != tops:
        wrong = next(i for i, (a, b) in enumerate(zip(printed, tops, strict=False)) if a != b)
        raise LaneError(f"the load's cell {wrong} tops at {printed[wrong]}, not {tops[wrong]}")
    return len(tops)


def check(cake: str) -> Report:
    binary, counter, nodelay, hosts = built(cake)
    measured: dict[str, Any] = {"faulty_servers": held_to_faults(binary), "histogram_cells": cells_checked(binary)}
    replies: dict[str, bytes] = {}
    with filled(hosts[2]) as spool, ExitStack() as stack:
        # INN's reader where the machine has it, as the sandbox does; CI's runners do not.
        reference = stack.enter_context(inn(hosts[2], spool, nodelay)) if NNRPD.exists() else []
        measured["inn_reference"] = "served" if reference else "absent"
        for host in [*hosts, *reference]:
            with tempfile.NamedTemporaryFile() as counts, \
                    started(host, None, spool, {**os.environ, "LD_PRELOAD": str(counter),
                                                "DN_ALLOC_FILE": counts.name}) as (server, requests):
                if host.nntp:
                    replies[host.name] = requests.read_bytes()
                # A rate any machine keeps, and slow readers taking megabytes of replies.
                got = run_load(server, binary, requests, None, Path(counts.name), conns=min(host.conns, 8),
                               rate=400, seconds=1, warmup=1, slow=SLOW_READERS, threads=2, slow_ms=1)
                server.stop()
            said = {k: got[k] for k in ("served", "completed", "owed", "slow_octets")}
            # Ours keep the rate beside the slow readers, and give them their megabytes once the window
            # closes; of INN as it runs, a reference, right replies are asked; the counter counts.
            if host.name != "inn" and (got["owed"] or got["completed"] != 400 or got["served"] < 390
                                       or got["slow_octets"] < 4 << 20):
                raise LaneError(f"{host.name} under load: {said}")
            if not got["server"]["allocations_before"]:
                raise LaneError(f"{host.name}: the allocation counter counted nothing")
            measured[host.name] = said
    if replies["nntp-poll"] != replies["nntp-uring"]:
        raise LaneError("the NNTP server gives other replies waiting with io_uring than with poll")
    return Report("native-tested", cake, HOSTS, {"assurance": "the load and its hosts run, every reply right; "
                                                              "no number judged", "measurements": measured})


def machine(cpus: dict[str, str], cake: str, binary: Path) -> dict[str, Any]:
    def read(path: str) -> str:
        p = Path(path)
        return p.read_text().strip() if p.is_file() else "unreadable"

    info = Path("/proc/cpuinfo").read_text()
    vulnerable = Path("/sys/devices/system/cpu/vulnerabilities")
    siblings = sorted({read(f"/sys/devices/system/cpu/cpu{c}/topology/thread_siblings_list") for c in cores()})
    return {"cpu": re.findall(r"^model name\s*:\s*(.+)$", info, re.MULTILINE)[0], "cpus": os.cpu_count(),
            "threads_of_a_core": siblings, "kernel": platform.release(),
            "governor": read("/sys/devices/system/cpu/cpu0/cpufreq/scaling_governor"),
            "boost": read("/sys/devices/system/cpu/cpufreq/boost"),
            "mitigations": {p.name: p.read_text().strip() for p in sorted(vulnerable.iterdir())}
            if vulnerable.is_dir() else {},
            "somaxconn": read("/proc/sys/net/core/somaxconn"), "tcp_rmem": read("/proc/sys/net/ipv4/tcp_rmem"),
            "tcp_wmem": read("/proc/sys/net/ipv4/tcp_wmem"), "affinity": cpus,
            "cc": lanes.loud([lanes.cc(), "--version"], timeout=30, what="the C compiler").splitlines()[0],
            "cc_flags": lanes.HARDENING, "cake": Path(cake).parent.name, "cake_sha256": lanes.digest(cake),
            "dn_compiler_sha256": lanes.digest(lanes.DN_COMPILER), "load_sha256": lanes.digest(binary)}


def per_reply(run: dict[str, Any], value: float) -> float:
    return value / max(int(run["served"]), 1)


def summary(run: dict[str, Any], *, raw: bool = False) -> dict[str, Any]:
    """A run in short, the server's time, switches and allocations a reply of the window; with
    `raw`, the load's whole record beside it."""
    lat, server = run["latency_ns"], run["server"]
    ticks = server["cpu_user_ms"] + server["cpu_system_ms"]
    found = {"rate": run["rate"], "kept": not saturated(run), "achieved": run["achieved"], "owed": run["owed"],
             "wrong": run["wrong"], "lost": run["lost"], "p50_us": lat["p50"] / 1000, "p99_us": lat["p99"] / 1000,
             "p999_us": lat["p999"] / 1000, "max_us": lat["max"] / 1000,
             "late_p99_us": run["send_late_ns"]["p99"] / 1000,
             "server_cpu_us_a_reply": round(per_reply(run, server["cpu_ns"] / 1000), 2),
             "server_system_share": round(server["cpu_system_ms"] / max(ticks, 1), 2),
             "switches_a_reply": round(per_reply(run, server["voluntary_switches"]
                                                 + server["involuntary_switches"]), 3),
             "allocations_a_reply": round(per_reply(run, server["allocations"]), 3),
             "high_water_kb": server["high_water_kb"],
             "load_cpu_share": round((run["cpu_user_us"] + run["cpu_system_us"])
                                     / (1e6 * run["seconds"] * run["threads"]), 2)}
    if raw:
        # The latencies' cells whole; of how late requests went, the quantiles.
        found["load"] = {**run, "send_late_ns": {k: v for k, v in run["send_late_ns"].items() if k != "cells"}}
    return found


def saturated(run: dict[str, Any]) -> bool:
    return bool(run["wrong"] or run["lost"] or run["owed"] or run["achieved"] < KEPT_SHARE * run["rate"]
                or run["latency_ns"]["p99"] > KEPT_P99_NS)


def given_for(host: Host, cpus: dict[str, str]) -> dict[str, Any]:
    return {"conns": host.conns - SLOW_READERS, "slow": SLOW_READERS, "threads": int(cpus["load_threads"])}


def sweep(lost: Callable[[int], bool]) -> tuple[int, list[int]]:
    """From 2,000 a second, the rate doubled while `lost` says the host keeps it, or halved until it
    does; then from the highest kept toward twice it, a quarter of the way at a time. The highest
    rate kept, and the rates tried."""
    kept_at = lost_at = 0
    tried = []
    rate = 2000
    while 250 <= rate <= 4_000_000 and not (kept_at and lost_at):
        tried.append(rate)
        if lost(rate):
            lost_at, rate = rate, rate // 2
        else:
            kept_at, rate = rate, rate * 2
    highest = kept_at
    for step in (1.25, 1.5, 1.75):
        if not (kept_at and lost_at):
            break
        tried.append(int(kept_at * step))
        if lost(tried[-1]):
            break
        highest = tried[-1]
    return highest, tried


def alone() -> dict[str, list[bytes]]:
    """Each command of the mix, of the same five articles where it names one."""
    numbers, mix = five(), nntp_commands()
    return {"ARTICLE": [f"ARTICLE {n}\r\n".encode() for n in numbers],
            "ARTICLE <id>": [f"ARTICLE <b{n - 1}@x.example>\r\n".encode() for n in numbers],
            "HEAD": [f"HEAD {n}\r\n".encode() for n in numbers], "STAT": [f"STAT {n}\r\n".encode() for n in numbers],
            "OVER": [c for c in mix if c.startswith(b"OVER")], "GROUP": [c for c in mix if c.startswith(b"GROUP")]}


def by_command(running: tuple[Server, Path], binary: Path, cpus: dict[str, str],
               given: dict[str, Any]) -> dict[str, Any]:
    """Each command alone, at 1,000 a second: the server's CPU time a reply, the median latency, and
    the reply's size."""
    server, _ = running
    found: dict[str, Any] = {}
    for name, commands in alone().items():
        blob = nntp_requests(server.port, commands)
        with tempfile.NamedTemporaryFile() as only:
            Path(only.name).write_bytes(blob)
            run = run_load(server, binary, Path(only.name), cpus["load"], rate=1000, seconds=5, warmup=2,
                           **{**given, "slow": 0})
        replies = [e for _, e in exchanges(blob)[1:]]
        found[name] = {"cpu_us_a_reply": round(per_reply(run, run["server"]["cpu_ns"] / 1000), 1),
                       "p50_us": run["latency_ns"]["p50"] / 1000, "octets": sum(map(len, replies)) // len(replies),
                       "kept": not saturated(run)}
    return found


def counted(host: Host, binary: Path, counter: Path, cpus: dict[str, str], spool: Path, rate: int) -> float:
    """Allocations a reply at `rate`, over the window of a run with the counter."""
    with tempfile.NamedTemporaryFile() as counts, \
            started(host, cpus["server"], spool, {**os.environ, "LD_PRELOAD": str(counter),
                                                  "DN_ALLOC_FILE": counts.name}) as (server, requests):
        run = run_load(server, binary, requests, cpus["load"], Path(counts.name), rate=rate, seconds=5, warmup=2,
                       **given_for(host, cpus))
        server.stop()
    return round(per_reply(run, run["server"]["allocations"]), 3)


def system_calls(host: Host, binary: Path, cpus: dict[str, str], spool: Path) -> dict[str, Any]:
    """The host's system calls a reply, at 2,000 a second under strace, which slows it too much to
    time; its start's calls are among them, some hundreds. Strace counts to the end, so no slow reader
    takes its 16 MiB after the window."""
    with tempfile.TemporaryDirectory() as temp:
        trace = Path(temp, "calls")
        with started(host, cpus["server"], spool, wrap=["strace", "-f", "-c", "-o", str(trace)]) \
                as (server, requests):
            run = run_load(server, binary, requests, cpus["load"], rate=2000, seconds=5, warmup=0,
                           **{**given_for(host, cpus), "slow": 0})
            server.stop()
        done = max(run["answered"], 1)
        calls: dict[str, float] = {}
        for line in trace.read_text().splitlines():
            parts = line.split()
            if len(parts) >= 5 and parts[0].replace(".", "").isdigit() and parts[-1] != "total":
                calls[parts[-1]] = round(int(parts[3]) / done, 3)
    return {"rate": 2000, "replies": done, "a_reply": dict(sorted(calls.items(), key=lambda kv: -kv[1])[:12]),
            "total_a_reply": round(sum(calls.values()), 2)}


def measure(cake: str, seconds: int, warmup: int, repeat: int, server: str, threads: int) -> None:
    """Every host started at once, each on its cores, swept in turn, its highest rate kept run again
    as long as a round's run, and each NNTP command alone. Then rounds of steady and overloaded runs,
    every host started anew, each round taking the hosts in another order, so that a drift of the
    machine falls on all of them; then a run of each with the counter, and one under strace."""
    binary, counter, nodelay, hosts = built(cake)
    spread = len(server_cpus(server))
    hosts.insert(2, Host(f"echo-uring-{spread}", [str(hosts[1].binary), "--threads", str(spread)], 32, False,
                         hosts[1].binary, hosts[1].limits))
    first = str(min(server_cpus(server)))
    load_on = ",".join(map(str, load_cpus(server_cpus(server), cores(), threads)))
    cpus = {"server": server, "load": load_on, "load_threads": str(threads)}
    nntp = next(h for h in hosts if h.nntp)
    with filled(nntp) as spool, ExitStack() as reference:
        if NNRPD.exists():
            hosts += reference.enter_context(inn(nntp, spool, nodelay))
        on = {h.name: {**cpus, "server": server if h.name == f"echo-uring-{spread}" else first} for h in hosts}
        found: dict[str, dict[str, Any]] = {
            h.name: {"command": h.command, "env": h.env, "binary_sha256": lanes.digest(h.binary),
                     "cpus": on[h.name]["server"], "limits": h.limits, "connections": h.conns - SLOW_READERS,
                     "slow_readers": SLOW_READERS, "sweep": [], "steady": [], "overload": []} for h in hosts}
        with ExitStack() as stack:
            running = {h.name: stack.enter_context(started(h, on[h.name]["server"], spool)) for h in hosts}
            for h in hosts:
                server_of, requests = running[h.name]

                def lost(rate: int, h: Host = h, server_of: Server = server_of, requests: Path = requests) -> bool:
                    run = run_load(server_of, binary, requests, on[h.name]["load"], rate=rate, seconds=3, warmup=2,
                                   **given_for(h, on[h.name]))
                    found[h.name]["sweep"].append(summary(run))
                    return saturated(run)

                sweep(lost)
                # The highest rate kept, kept again for as long as a round's run, or the next below.
                for rate in sorted((s["rate"] for s in found[h.name]["sweep"] if s["kept"]), reverse=True)[:3]:
                    run = run_load(server_of, binary, requests, on[h.name]["load"], rate=rate, seconds=seconds,
                                   warmup=warmup, **given_for(h, on[h.name]))
                    found[h.name]["kept"], found[h.name]["at_kept"] = rate, summary(run)
                    if not saturated(run):
                        break
                else:
                    found[h.name]["kept"] = 0
                if h.nntp:
                    found[h.name]["commands"] = by_command(running[h.name], binary, on[h.name],
                                                           given_for(h, on[h.name]))
        # Steady load at one rate for every host of a kind, so that their costs a reply compare.
        steady = {kind: max(250, min(found[h.name]["kept"] for h in hosts if h.kind == kind) // 2)
                  for kind in ("echo", "nntp")}
        # Each round starts every host anew, so that its start's chance falls on the rounds too.
        for round_ in range(repeat):
            with ExitStack() as stack:
                running = {h.name: stack.enter_context(started(h, on[h.name]["server"], spool)) for h in hosts}
                for h in hosts[round_ % len(hosts):] + hosts[:round_ % len(hosts)]:
                    server_of, requests = running[h.name]
                    for phase, rate in (("steady", steady[h.kind]), ("overload", int(found[h.name]["kept"] * 1.5))):
                        run = run_load(server_of, binary, requests, on[h.name]["load"], rate=max(rate, 250),
                                       seconds=seconds, warmup=warmup, **given_for(h, on[h.name]))
                        found[h.name][phase].append(summary(run, raw=True))
                for h in hosts:
                    said = running[h.name][0].stop()
                    if not h.nntp:
                        # The echo's own count of sends the kernel took in part: the slow readers' doing.
                        found[h.name]["partial_sends"] = found[h.name].get("partial_sends", 0) + json.loads(
                            said.strip().splitlines()[-1])["partial_progress"]
        for h in hosts:
            found[h.name]["allocations_a_reply"] = counted(h, binary, counter, on[h.name], spool, steady[h.kind])
            found[h.name]["system_calls"] = system_calls(h, binary, on[h.name], spool)
    report = {"machine": machine(cpus, cake, binary), "steady_rates": steady, "seconds": seconds,
              "warmup": warmup, "rounds": repeat, "echo_payloads": ECHO_SIZES,
              "nntp_mix": [c.decode().strip() for c in nntp_commands()],
              "slow_read": {"octets": 16, "every_ms": SLOW_MS, "receive_buffer": 4096, "asked_octets": 16 << 20},
              "hosts": found}
    # A histogram's cells a line each, not a number a line.
    text = re.sub(r"\[\s+(\d+),\s+(\d+)\s+\]", r"[\1, \2]", json.dumps(report, indent=1))
    (OUT / "measured.json").write_text(text + "\n")
    print(OUT / "measured.json")


def instructions(out: Path) -> dict[str, int]:
    """Each function's own instructions in a callgrind file."""
    said = lanes.loud(["callgrind_annotate", "--inclusive=no", "--auto=no", "--threshold=100", str(out)],
                      timeout=120, what="callgrind_annotate")
    found: dict[str, int] = {}
    for line in said.splitlines():
        if (m := re.match(r"\s*([\d,]+) \(\s*[\d.]+%\)\s+(\S+)", line)) and "PROGRAM TOTALS" not in line:
            found[m[2]] = found.get(m[2], 0) + int(m[1].replace(",", ""))
    return found


def profile(cake: str, command: str | None) -> None:
    """The NNTP server under callgrind, waiting with poll (Valgrind cannot follow io_uring), serving
    the mix, or `command` alone, at 200 a second for five seconds: where its instructions go, by
    function, less those of a run that starts, answers the mix once as its replies are read, and
    stops."""
    binary, _, _, hosts = built(cake)
    nntp = next(h for h in hosts if h.name == "nntp-poll")
    with filled(nntp) as spool:
        with started(nntp, None, spool) as (server, requests):
            opening, *mix = exchanges(requests.read_bytes())
            server.stop()
        chosen = [x for x in mix if command is None or x[0].split()[0] == command.encode()]
        if not chosen:
            raise SystemExit(f"bench.py: no {command} in the mix")
        only = OUT / "profiled-requests"
        only.write_bytes(b"".join(exchange(*x) for x in [opening, *chosen]))
        counted: list[dict[str, int]] = []
        run: dict[str, Any] = {}
        for loaded in (False, True):
            out = OUT / f"callgrind-{'loaded' if loaded else 'idle'}.out"
            with started(nntp, None, spool, wrap=["valgrind", "--tool=callgrind", f"--callgrind-out-file={out}"]) \
                    as (server, _):
                if loaded:
                    run = load(binary, server.port, only, None, conns=8, rate=200, seconds=5, warmup=0, slow=0,
                               threads=1)
                server.stop()
            counted.append(instructions(out))
    idle, busy = counted
    spent = {name: busy[name] - idle.get(name, 0) for name in busy}
    total = sum(n for n in spent.values() if n > 0)
    print(f"{run['served']} replies, {run['wrong']} wrong; {total:,} instructions beyond the start's")
    for name, n in sorted(spent.items(), key=lambda kv: -kv[1])[:15]:
        print(f"{n:>15,} {n / total:6.1%}  {name}")


def median(values: list[float]) -> float:
    ordered = sorted(values)
    return float(ordered[len(ordered) // 2])


def spread_of(runs: list[dict[str, Any]], key: str, digits: int = 0) -> str:
    """The median of the rounds, and their least and greatest."""
    values = [float(r[key]) for r in runs]
    return f"{median(values):,.{digits}f} ({min(values):,.{digits}f} to {max(values):,.{digits}f})"


def table(measured: dict[str, Any]) -> str:
    """The rows docs/bench.md shows: of the rounds, medians, with the least and greatest where shown."""
    rows = [("| Host | Kept, replies/s | CPU µs a reply there | Steady p50, µs | Steady p99, µs | Sent late p99, µs | "
             "CPU µs a reply | In the kernel | Switches a reply | Allocations a reply | VmHWM, MiB | "
             "Overload, replies/s | Calls a reply at 2,000/s |"),
            "|---|---|---|---|---|---|---|---|---|---|---|---|---|"]
    for name, h in measured["hosts"].items():
        steady, over = h["steady"], h["overload"]

        def bound(runs: list[dict[str, Any]]) -> str:
            """Where the load's own threads were busy most of the time, the load may be what saturated."""
            return " (load-bound)" if max(r["load_cpu_share"] for r in runs) > LOAD_BOUND else ""

        # A process a connection: switches and high water are its listener's alone.
        forks = bool(h["limits"].get("processes"))
        switches = "n/a" if forks else f"{median([r['switches_a_reply'] for r in steady]):.2f}"
        memory = "n/a" if forks else f"{max(r['high_water_kb'] for r in steady) / 1024:.1f}"
        rows.append(f"| `{name}` | {h['kept']:,}{bound(h['sweep'])} | {h['at_kept']['server_cpu_us_a_reply']:.1f} | "
                    f"{spread_of(steady, 'p50_us')} | {spread_of(steady, 'p99_us')} | "
                    f"{median([r['late_p99_us'] for r in steady]):,.0f} | "
                    f"{spread_of(steady, 'server_cpu_us_a_reply', 1)} | "
                    f"{median([r['server_system_share'] for r in steady]):.0%} | {switches} | "
                    f"{h['allocations_a_reply']:.2f} | {memory} | {median([r['achieved'] for r in over]):,.0f}"
                    f"{bound(over)} | "
                    f"{h['system_calls']['total_a_reply']:.1f} |")
    by_host = {name: h["commands"] for name, h in measured["hosts"].items() if "commands" in h}
    rows += ["", "| Command alone, 1,000/s | Octets | "
             + " | ".join(f"`{name}` CPU µs, p50 µs" for name in by_host) + " |",
             "|---|---|" + "---|" * len(by_host)]
    for command, first in next(iter(by_host.values())).items():
        cells = [f"{c[command]['cpu_us_a_reply']:,.0f}, {c[command]['p50_us']:,.0f}" if c[command]["kept"]
                 else f"{c[command]['cpu_us_a_reply']:,.0f}, not kept" for c in by_host.values()]
        rows.append(f"| {command} | {first['octets']:,} | " + " | ".join(cells) + " |")
    return "\n".join(rows)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("action", choices=["check", "measure", "table", "profile"], nargs="?", default="check")
    parser.add_argument("--command", help="profile: the one command of the mix to profile, as ARTICLE")
    parser.add_argument("--cake", default=os.environ.get("CAKE"))
    parser.add_argument("--seconds", type=int, default=10, help="each steady or overloaded run")
    parser.add_argument("--warmup", type=int, default=10, help="before each steady or overloaded run")
    parser.add_argument("--repeat", type=int, default=5, help="rounds")
    parser.add_argument("--server-cpus", default="2,3,4,5", help="the first alone for a host of one thread")
    parser.add_argument("--load-threads", type=int, default=4, help="on cores the server's do not share")
    args = parser.parse_args()
    if args.action == "table":
        print(table(json.loads((OUT / "measured.json").read_text())))
        return
    lanes.require_platform(parser)
    cake = lanes.given_cake(parser, args.cake)
    if args.action == "check":
        lanes.lane_main("BENCH", OUT, lambda: check(cake))
        return
    if args.action == "profile":
        profile(cake, args.command)
        return
    if shutil.which("taskset") is None:
        parser.error("taskset is needed")
    measure(cake, args.seconds, args.warmup, args.repeat, args.server_cpus, args.load_threads)


if __name__ == "__main__":
    main()
