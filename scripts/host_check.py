#!/usr/bin/env python3
# SPDX-License-Identifier: AGPL-3.0-or-later
"""The host lane: the host's side of the store (native/store.c), run with a stand-in for the
program (native/host_driver.c) that prints what the host hands it:

- the host listens, and prints its port, only once the program says to, and a word to listen
  that is neither 0 nor 1, or 0 after 1, ends it with status 1;
- without a spool there is no store: no identity, no group, no random octets, and no client may
  post;
- with one, the program gets the wall clock, 40 random octets drawn anew for each run, the path
  identity and the groups; a client may post from loopback by default, and else from the networks
  `--post-from` names, to the bit, over IPv4 and IPv6;
- a second host on a held spool, and a mark of a failed sync of this boot in the spool or the run
  directory, refuse the start with status 4; a mark of another boot is removed;
- options that cannot be refuse the start with status 2;
- file jobs (native/jobs.c): a file created, written, sized, synced, renamed, read past its end and
  closed; truncated; the directory listed a page at a time; eight jobs at once; each error's class,
  a job stopping at its first failure; each way a job breaks the contract ends the host with
  status 1;
- each defect planted in nntp_host.c, store.c and jobs.c is caught.
"""
from __future__ import annotations

from collections.abc import Callable
from dataclasses import dataclass
import errno
import json
import os
from pathlib import Path
import queue
import re
import signal
import socket
import subprocess
import sys
import tempfile
import time
from typing import Self

sys.path.insert(0, str(Path(__file__).resolve().parent))
import lanes  # the path above is what makes it importable
from lanes import LaneError, Report

OUT = lanes.ROOT / "build/host"
DRIVER = lanes.NATIVE / "host_driver.c"
HOST = lanes.NATIVE / "nntp_host.c"
STORE = lanes.NATIVE / "store.c"
JOBS = lanes.NATIVE / "jobs.c"
RUNTIME = [lanes.NATIVE / "cake_header.c", lanes.NATIVE / "cake_runtime.c"]
WAIT = 10
IDENTITY = "news.example.org"
GROUPS = ["local.test", "comp.lang.lean"]
MARK = "sync-failed"
OTHER_BOOT = "00000000-0000-0000-0000-000000000000"
NAMED = ["--revision", "0123abc", "--source", "https://example.org/dn"]


@dataclass
class Builds:
    """The host with the stand-in, as the server is built and as its test build, with libfiu's points."""

    plain: Path
    fiu: Path


def build(name: str, host: Path = HOST, store: Path = STORE, jobs: Path = JOBS) -> Builds:
    fiu = lanes.pinned_tool("libfiu")
    sources = [DRIVER, host, store, jobs, *RUNTIME]
    clean = (host, store, jobs) == (HOST, STORE, JOBS)
    return Builds(lanes.link(OUT / name, sources, includes=[OUT], check=clean),
                  lanes.link(OUT / f"{name}-fiu", sources, includes=[OUT, fiu], check=clean,
                             flags=["-DFIU_ENABLE=1", f"-L{fiu}", "-lfiu", f"-Wl,-rpath,{fiu}"]))


def fiu_environment(enable: str) -> dict[str, str]:
    """libfiu's preload, enabling the points `enable` names as the host starts."""
    fiu = lanes.pinned_tool("libfiu")
    env = {k: v for k, v in os.environ.items() if not k.startswith("FIU_")}
    return {**env, "LD_PRELOAD": str(fiu / "fiu_run_preload.so"), "LD_LIBRARY_PATH": str(fiu), "FIU_ENABLE": enable}


def layout() -> dict[str, int]:
    found = re.findall(r"#define DN_SESSION_(\w+) (\d+)", (OUT / "dn_session_layout.h").read_text())
    return {name: int(value) for name, value in found}


def launch(binary: Path, options: list[str], address: str, env: dict[str, str] | None = None,
           wrap: tuple[str, ...] = ()) -> tuple[subprocess.Popen[str], lanes.Lines]:
    """The host run under `wrap` with `env`, and its standard output."""
    proc = subprocess.Popen([*wrap, str(binary), *NAMED, "--address", address, *options], stdin=subprocess.PIPE,
                            stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True, env=env)
    return proc, lanes.Lines(proc.stdout)


def start(binary: Path, options: list[str], address: str) -> tuple[subprocess.Popen[str], lanes.Lines, int]:
    """The host, listening once the first batch is fetched and handed over; its standard output, and its port."""
    proc, lines = launch(binary, options, address)
    if proc.stdin is None:
        raise LaneError("the host has no input")
    try:
        proc.stdin.write("next\nemit\n")
        proc.stdin.flush()
    except BrokenPipeError:
        pass
    try:
        while (first := lines.get(WAIT)) and not first.startswith("{"):
            pass
    except queue.Empty:
        proc.kill()
        raise LaneError(f"the host said nothing in {WAIT} s with {options}") from None
    if not first:
        proc.kill()
        said = proc.communicate(timeout=WAIT)[1].strip()
        raise LaneError(f"the host did not start with {options}: status {proc.returncode}, saying {said!r}")
    return proc, lines, int(json.loads(first)["port"])


def stopped(proc: subprocess.Popen[str], lines: lanes.Lines, wait: float = WAIT) -> list[str]:
    """Stop the run; what the driver printed before, once the host ended as a stopped run does."""
    if proc.stdin is None:
        raise LaneError("the host has no input")
    proc.stdin.write("stop 7\n")
    proc.stdin.close()
    out = []
    while (line := lines.get(wait)) is not None:
        out.append(line.strip())
    status = proc.wait(timeout=wait)
    if status != 3:
        raise LaneError(f"the stopped run ended with status {status}")
    return out


def serve(binary: Path, options: list[str], address: str = "127.0.0.1") -> tuple[list[str], list[str]]:
    """Batches with a client connected, until it is opened: the start data and the connection opened, as
    words."""
    proc, lines, port = start(binary, options, address)
    out: list[str] = []
    try:
        with socket.create_connection((address, port), timeout=WAIT):
            if proc.stdin is None:
                raise LaneError("the host has no input")
            for _ in range(3):
                proc.stdin.write("next\n")
                proc.stdin.flush()
                while (line := lines.get(WAIT)) not in {".\n", None}:
                    out.append((line or "").strip())
                if any(line.startswith("opened ") for line in out):
                    break
                proc.stdin.write("emit\n")
            proc.stdin.write("emit\n")
            proc.stdin.flush()
            stopped(proc, lines)
    finally:
        if proc.poll() is None:
            proc.kill()
            proc.wait()
    begin = [line.split() for line in out if line.startswith("start ")]
    opened = [line.split() for line in out if line.startswith("opened ")]
    if not begin or len(opened) != 1 or any(b[2:] != begin[0][2:] for b in begin):
        raise LaneError(f"batches with one connection printed {out}")
    return begin[0], opened[0]


def refused(binary: Path, options: list[str], status: int, said: str) -> None:
    done = subprocess.run([str(binary), *NAMED, *options], stdin=subprocess.DEVNULL, capture_output=True, text=True,
                          timeout=WAIT, check=False)
    if done.returncode != status or said not in done.stderr or done.stdout:
        raise LaneError(f"{options}: status {done.returncode}, saying {done.stderr.strip()!r}, not status {status} "
                        f"saying {said!r}")


class Store:
    """A spool and a run directory of their own."""

    def __init__(self, temp: str) -> None:
        self.spool, self.run = Path(temp) / "spool", Path(temp) / "run"
        self.spool.mkdir()
        self.run.mkdir()

    def options(self, *more: str) -> list[str]:
        named = ["--spool", str(self.spool), "--run-dir", str(self.run), "--path-identity", IDENTITY]
        return [*named, *(o for g in GROUPS for o in ("--group", g)), *more]


def boot_id() -> str:
    return Path("/proc/sys/kernel/random/boot_id").read_text().strip()


def on_free_port(binary: Path) -> tuple[Jobs, int]:
    """A host on a port free a moment before, started again if another process took the port in between."""
    for _ in range(4):
        with socket.socket() as probe:
            probe.bind(("127.0.0.1", 0))
            port = probe.getsockname()[1]
        try:
            return Jobs(binary, ["--port", str(port)]), port
        except LaneError as error:
            if "Address already in use" not in str(error):
                raise
    raise LaneError("no free port in four attempts")


def listening(binary: Path) -> dict[str, str]:
    """No client connects before the program says to listen; once it has, the host prints its port and a client
    connects; a word to listen of 0 after 1, or of 2, ends the host with status 1."""
    first, port = on_free_port(binary)
    seen = {}
    with first as h:
        try:
            socket.create_connection(("127.0.0.1", port), timeout=WAIT).close()
        except ConnectionRefusedError:
            seen["before"] = "refused"
        else:
            raise LaneError("a client connected before the program said to listen")
        h.send("listen 1", "emit")
        said = json.loads(h.line() or "{}")
        if said.get("port") != port:
            raise LaneError(f"told to listen, the host printed {said}, not port {port}")
        with socket.create_connection(("127.0.0.1", port), timeout=WAIT):
            h.fetch()
            seen["after"] = "connected"
            h.send("listen 0", "emit")
            h.exited("listening 0, having listened 1", 1, "a word to listen of 0 after 1")
    with Jobs(binary, []) as h:
        h.send("listen 2", "emit")
        h.exited("listening 2, having listened 0", 1, "a word to listen of 2")
    seen["0 after 1"] = seen["2"] = "ended"
    return seen


def no_store(binary: Path) -> dict[str, object]:
    begin, opened = serve(binary, [])
    random = 2 * layout()["RANDOM_LEN"]
    if begin[2:] != ["0" * random, "-"] or opened[3] != "0":
        raise LaneError(f"without a spool the program got {begin[2:]}, a client posting {opened[3]}")
    return {"start": begin[2:], "post": opened[3]}


def handed(binary: Path) -> dict[str, object]:
    with tempfile.TemporaryDirectory() as temp:
        store = Store(temp)
        first, opened = serve(binary, store.options())
        second, _ = serve(binary, store.options())
    wall = int(first[1])
    if abs(wall - time.time() * 1000) > 60_000:
        raise LaneError(f"a wall clock of {wall} ms")
    wanted = [IDENTITY.encode().hex(), *(g.encode().hex() for g in GROUPS)]
    if first[3:] != wanted or second[3:] != wanted:
        raise LaneError(f"the program got {first[3:]}, not the identity and the groups {wanted}")
    random = 2 * layout()["RANDOM_LEN"]
    if len(first[2]) != random or first[2] == "0" * random or first[2] == second[2]:
        raise LaneError(f"random octets {first[2]} and then {second[2]}")
    if opened[3] != "1":
        raise LaneError("a client on loopback may not post by default")
    return {"wall": wall, "random": [first[2], second[2]], "post": opened[3]}


def posting(binary: Path) -> dict[str, str]:
    """Who may post: the networks named, to the bit; loopback is no longer one once any is named."""
    cases = {"10.0.0.0/8": "0", "127.0.0.1/32": "1", "127.0.0.0/31": "1", "127.0.0.2/31": "0",
             "::1/128": "0"}
    seen = {}
    with tempfile.TemporaryDirectory() as temp:
        store = Store(temp)
        for net in cases:
            seen[net] = serve(binary, store.options("--post-from", net))[1][3]
        seen["::1, by default"] = serve(binary, store.options(), "::1")[1][3]
        seen["::/127 from ::1"] = serve(binary, store.options("--post-from", "::/127"), "::1")[1][3]
    wanted_all = {**cases, "::1, by default": "1", "::/127 from ::1": "1"}
    if seen != wanted_all:
        raise LaneError(f"who may post: {seen}, not {wanted_all}")
    return seen


def held(binary: Path) -> str:
    with tempfile.TemporaryDirectory() as temp:
        store = Store(temp)
        proc, lines, _ = start(binary, store.options(), "127.0.0.1")
        try:
            refused(binary, store.options(), 4, "another process holds the spool")
            stopped(proc, lines)
        finally:
            if proc.poll() is None:
                proc.kill()
                proc.wait()
    return "refused"


def marks_at_start(binary: Path) -> dict[str, str]:
    seen = {}
    for where in ("spool", "run"):
        with tempfile.TemporaryDirectory() as temp:
            store = Store(temp)
            mark = getattr(store, where) / MARK
            for text, said in ((boot_id()[:10], "cannot be read whole"), ("", "cannot be read whole"),
                               (boot_id() + "\n", "a sync failed since the machine started")):
                mark.write_text(text)
                refused(binary, store.options(), 4, said)
                if not mark.exists():
                    raise LaneError(f"a refused start removed the mark in the {where} directory")
            mark.write_text(OTHER_BOOT + "\n")
            serve(binary, store.options())
            if mark.exists():
                raise LaneError(f"a mark of another boot is left in the {where} directory")
            seen[where] = "this boot and a cut one refused, another removed"
    return seen


def options(binary: Path) -> dict[str, str]:
    """Options that cannot be."""
    with tempfile.TemporaryDirectory() as temp:
        store = Store(temp)
        spool, run = ["--spool", str(store.spool)], ["--run-dir", str(store.run)]
        cases = {"a group without a spool": (["--group", "a.b"], "store options without --spool"),
                 "a spool without a run directory": (spool, "--spool needs --run-dir"),
                 "a spool that is not there": (["--spool", str(store.spool / "x"), *run], "No such file"),
                 "an identity too long": ([*spool, *run, "--path-identity", "a" * 201], "--path-identity"),
                 "a group too long": ([*spool, *run, "--group", "a" * 65], "--group"),
                 "an empty group": ([*spool, *run, "--group", ""], "--group"),
                 "65 groups": ([*spool, *run, *(o for k in range(65) for o in ("--group", f"g{k}"))], "--group"),
                 "a network that is none": ([*spool, *run, "--post-from", "10.0.0.0/33"], "not a number"),
                 "an address that is none": ([*spool, *run, "--post-from", "x/8"], "not a network")}
        for options_, said in cases.values():
            refused(binary, options_, 2, said)
    return dict.fromkeys(cases, "refused")


NAMES = {"journal": "JOURNAL", "final": "FINAL", "temp": "TEMP", "quarantine": "QUARANTINE", "tail": "TAIL"}
LETTERS = {"final": "a", "temp": "t", "quarantine": "q", "tail": "j"}


def file_name(kind: str, number: int) -> str:
    return "journal" if kind == "journal" else f"{LETTERS[kind]}{number:016x}"


@dataclass
class Op:
    """An operation as its ten words, the code and the kinds of name by their names."""

    code: str | int
    place: int = 0
    gen: int = 0
    name: str | int = 0
    number: int = 0
    to: str | int = 0
    to_number: int = 0
    offset: int = 0
    length: int = 0
    at: int = 0

    def words(self, w: dict[str, int]) -> list[int]:
        def kind(k: str | int) -> int:
            return k if isinstance(k, int) else w[f"NAME_{NAMES[k]}"]

        code = w[f"OP_{self.code.upper().replace('-', '_')}"] if isinstance(self.code, str) else self.code
        return [code, self.place, self.gen, kind(self.name), self.number, kind(self.to), self.to_number, self.offset,
                self.length, self.at]


class Jobs:
    """A host handed jobs by the driver, not listening; what each completion said, by slot."""

    def __init__(self, binary: Path, options: list[str], points: list[str] | None = None,
                 wrap: tuple[str, ...] = (), wait: float = WAIT) -> None:
        """`points` enables libfiu's points of failure in the test build as it starts, one command each."""
        self.w, self.wait_s = layout(), wait
        env = None if points is None else fiu_environment("\n".join(points))
        self.proc, self.lines = launch(binary, options, "127.0.0.1", env, wrap)
        self.done: dict[int, list[int]] = {}
        self.ended = False
        self.send("listen 0")
        self.fetch()
        if self.ended:
            raise LaneError(f"the host did not start with {options}: {self.said()}")

    def line(self) -> str | None:
        try:
            return self.lines.get(self.wait_s)
        except queue.Empty:
            raise LaneError(f"the host said nothing in {self.wait_s} s") from None

    def fetch(self) -> None:
        """One batch: what it brought, up to its end, or that the host ended."""
        self.send("next")
        while (line := self.line()) not in {".\n", None}:
            if line and line.startswith("done "):
                words = [int(x) for x in line.split()[1:]]
                self.done[words[0]] = words[1:]
        self.ended = line is None

    def send(self, *lines: str) -> None:
        if self.proc.stdin is None:
            raise LaneError("the host has no input")
        try:
            self.proc.stdin.write("".join(line + "\n" for line in lines))
            self.proc.stdin.flush()
        except BrokenPipeError:
            self.ended = True

    def hand(self, slot: int, gen: int, ops: list[Op], data: dict[int, bytes] | None = None, *,
             fetch: bool = True) -> None:
        self.hands([(slot, gen, ops, data or {})], fetch=fetch)

    def hands(self, jobs: list[tuple[int, int, list[Op], dict[int, bytes]]], *, fetch: bool = True) -> None:
        """Jobs handed over together, then a batch unless `fetch` is false."""
        lines = []
        for slot, gen, ops, data in jobs:
            lines += [f"data {slot} {at} {chunk.hex()}" for at, chunk in data.items()]
            lines += [f"op {slot} {i} {' '.join(map(str, op.words(self.w)))}" for i, op in enumerate(ops)]
            lines.append(f"job {slot} {gen} {len(ops)}")
        self.send(*lines, "emit")
        if fetch and not self.ended:
            self.fetch()

    def wait(self, slot: int) -> list[int]:
        """The completion of the job in `slot`: its generation, the operations that succeeded, the class of
        its error and the sixteen result words. A batch follows every hand-over, which takes what has
        completed; this asks for more until the job's comes."""
        while slot not in self.done:
            if self.ended:
                raise LaneError(f"the host ended waiting for job {slot}: {self.said()}")
            self.send("emit")
            self.fetch()
        return self.done.pop(slot)

    def peek(self, slot: int, at: int, n: int) -> bytes:
        self.send(f"peek {slot} {at} {n}")
        line = (self.line() or "").split()
        return b"" if line[1:] == ["-"] else bytes.fromhex(line[1])

    def said(self) -> str:
        if self.proc.poll() is None:
            return "nothing"
        return (self.proc.stderr.read() if self.proc.stderr else "").strip()

    def stop(self) -> None:
        stopped(self.proc, self.lines, self.wait_s)

    def broken(self, said: str, wanted: int = 1) -> None:
        """The host ended the run for a job that breaks the contract, saying `said`, with status `wanted`."""
        self.exited(said, wanted, f"a job that should break the contract ({said})")

    def exited(self, said: str, wanted: int, after: str) -> None:
        """The host ended after `after`, saying `said`, with status `wanted`."""
        try:
            status = self.proc.wait(timeout=self.wait_s)
        except subprocess.TimeoutExpired:
            self.proc.kill()
            self.proc.wait()
            raise LaneError(f"the host went on after {after}") from None
        message = self.said()
        if status != wanted or said not in message:
            raise LaneError(f"status {status}, saying {message!r}, not status {wanted} saying {said!r}")

    def __enter__(self) -> Self:
        return self

    def __exit__(self, *_: object) -> None:
        if self.proc.poll() is None:
            self.proc.kill()
            self.proc.wait()


def ok(done: list[int], ops: int, what: str) -> list[int]:
    if done[1:3] != [ops, 0]:
        raise LaneError(f"{what}: {done[1]} operations succeeded, class {done[2]}, not {ops} and none")
    return done[3:]


def opened(h: Jobs, slot: int, gen: int, kind: str, number: int, code: str = "create") -> tuple[int, int]:
    h.hand(slot, gen, [Op(code, name=kind, number=number)])
    result = ok(h.wait(slot), 1, f"{code} {kind} {number}")
    return result[0], result[1]


def files(binary: Path) -> dict[str, object]:
    data = b"hello world"
    with tempfile.TemporaryDirectory() as temp:
        store = Store(temp)
        with Jobs(binary, store.options()) as h:
            p, g = opened(h, 0, 1, "temp", 1)
            h.hand(0, 2, [Op("write", p, g, offset=0, length=5, at=0), Op("write", p, g, offset=5, length=6, at=5),
                          Op("size", p, g), Op("data-sync", p, g), Op("sync", p, g)], {0: data})
            size = ok(h.wait(0), 5, "writes and syncs")[4]
            h.hand(0, 3, [Op("rename", name="temp", number=1, to="final", to_number=1), Op("sync-dir")])
            ok(h.wait(0), 2, "a rename and a sync of the directory")
            h.hand(0, 4, [Op("read", p, g, offset=0, length=64, at=100), Op("close", p, g)])
            read = ok(h.wait(0), 2, "a read and a close")[0]
            back = h.peek(0, 100, read)
            h.stop()
        left = {f.name: f.read_bytes() for f in store.spool.iterdir()}
    if size != len(data) or read != len(data) or back != data or left != {file_name("final", 1): data}:
        raise LaneError(f"a file written as {data!r}: size {size}, read {read} bytes {back!r}, leaving {left}")
    return {"size": size, "read": read, "left": sorted(left)}


def truncated(binary: Path) -> int:
    with tempfile.TemporaryDirectory() as temp, Jobs(binary, Store(temp).options()) as h:
        p, g = opened(h, 0, 1, "tail", 9)
        h.hand(0, 2, [Op("write", p, g, length=10), Op("truncate", p, g, length=3), Op("size", p, g),
                      Op("close", p, g)], {0: b"0123456789"})
        size = ok(h.wait(0), 4, "a write, a truncation and a size")[4]
        h.stop()
    if size != 3:
        raise LaneError(f"a file truncated to 3 octets has {size}")
    return size


def errors(binary: Path) -> dict[str, list[int]]:
    """Each class an operation's error falls in, and a job stopping at its first failure."""
    w = layout()
    seen = {}
    with tempfile.TemporaryDirectory() as temp:
        store = Store(temp)
        (store.spool / file_name("temp", 7)).write_bytes(b"")
        with Jobs(binary, store.options()) as h:
            cases = {"a name that exists": ([Op("create", name="temp", number=7)], "EXISTS"),
                     "a file not there": ([Op("open", name="temp", number=8)], "NOT_FOUND"),
                     "a rename of no file": ([Op("rename", name="temp", number=8, to="final", to_number=8)],
                                             "NOT_FOUND"),
                     "a removal of no file": ([Op("remove", name="temp", number=8)], "NOT_FOUND"),
                     "a job after its failure": ([Op("remove", name="temp", number=9),
                                                  Op("create", name="temp", number=9)], "NOT_FOUND")}
            for gen, (what, (ops, cls)) in enumerate(cases.items(), 1):
                h.hand(1, gen, ops)
                done = h.wait(1)
                seen[what] = done[:3]
                if done[:3] != [gen, 0, w[f"CLASS_{cls}"]]:
                    raise LaneError(f"{what}: generation, operations and class {done[:3]}, not {gen}, 0, {cls}")
            h.stop()
        if (store.spool / file_name("temp", 9)).exists():
            raise LaneError("an operation after a failed one was carried out")
    return seen


def listing(binary: Path) -> dict[str, int]:
    """The directory listed a page at a time, each name once, none longer than a page refused as another
    error."""
    w = layout()
    with tempfile.TemporaryDirectory() as temp:
        store = Store(temp)
        made = {file_name("temp", k) for k in range(40)}
        for name in made:
            (store.spool / name).write_bytes(b"")
        with Jobs(binary, store.options()) as h:
            p, g = opened(h, 0, 1, "journal", 0, "open-dir")
            names, pages = [], 0
            for gen in range(2, 100):
                h.hand(0, gen, [Op("list", p, g, length=60)])
                count, used = ok(h.wait(0), 1, "a page")[:2]
                if not count:
                    break
                page, pages = h.peek(0, 0, used), pages + 1
                while page:
                    names.append(page[1:1 + page[0]].decode())
                    page = page[1 + page[0]:]
            h.hand(1, 1, [Op("open-dir")])
            q, r = ok(h.wait(1), 1, "a second listing")[:2]
            h.hand(1, 2, [Op("list", q, r, length=5)])
            small = h.wait(1)
            h.hand(0, 200, [Op("close", p, g)])
            ok(h.wait(0), 1, "closing a listing")
            h.stop()
    if sorted(names) != sorted(made) or pages < 14 or small[1:3] != [0, w["CLASS_OTHER"]]:
        raise LaneError(f"listed {len(names)} names of {len(made)} in {pages} pages; a page too small for a name: "
                        f"{small[1:3]}")
    return {"names": len(names), "pages": pages}


def at_once(binary: Path) -> int:
    """Eight jobs at once, three times over: every place given back when its file is closed."""
    jobs = layout()["JOBS"]
    with tempfile.TemporaryDirectory() as temp:
        store = Store(temp)
        with Jobs(binary, store.options()) as h:
            for rounds in range(3):
                for slot in range(jobs):
                    h.hand(slot, 2 * rounds + 1, [Op("create", name="final", number=jobs * rounds + slot)])
                places = {tuple(ok(h.wait(slot), 1, f"job {slot}")[:2]) for slot in range(jobs)}
                if len(places) != jobs:
                    raise LaneError(f"eight files opened at once took places {sorted(places)}")
                for slot, (p, g) in enumerate(sorted(places)):
                    h.hand(slot, 2 * rounds + 2, [Op("close", p, g)])
                for slot in range(jobs):
                    ok(h.wait(slot), 1, f"closing in job {slot}")
            h.stop()
        left = sorted(f.name for f in store.spool.iterdir())
    if left != sorted(file_name("final", k) for k in range(3 * jobs)):
        raise LaneError(f"jobs at once left {left}")
    return 3 * jobs


def fresh(h: Jobs) -> tuple[int, int]:
    return opened(h, 7, 1, "temp", 1)


def closed_file(h: Jobs) -> None:
    pg = fresh(h)
    h.hand(0, 1, [Op("close", *pg)])
    h.wait(0)
    h.hand(0, 2, [Op("size", *pg)])


def stale(h: Jobs) -> None:
    pg = fresh(h)
    h.hand(0, 1, [Op("close", *pg)])
    h.wait(0)
    if opened(h, 0, 2, "temp", 2)[0] != pg[0]:
        raise LaneError("a place given back was not taken again")
    h.hand(0, 3, [Op("size", *pg)])


def nine(h: Jobs) -> None:
    """Eight operations, counted as nine."""
    words = " ".join(map(str, Op("sync-dir").words(h.w)))
    h.send(*(f"op 0 {i} {words}" for i in range(8)), "job 0 1 9", "emit")


def named_twice(h: Jobs) -> None:
    pg = fresh(h)
    h.hands([(0, 1, [Op("size", *pg)], {}), (1, 1, [Op("size", *pg)], {})])


def two_dir_syncs(h: Jobs) -> None:
    h.hands([(0, 1, [Op("sync-dir")], {}), (1, 1, [Op("sync-dir")], {})])


def seventeen(h: Jobs) -> None:
    for slot in range(2):
        h.hand(slot, 1, [Op("create", name="temp", number=8 * slot + k) for k in range(8)])
    for slot in range(2):
        ok(h.wait(slot), 8, "eight files created")
    h.hand(0, 2, [Op("create", name="temp", number=99)])


# Each way a job breaks the contract, with what the host says.
BREACHES: dict[str, tuple[Callable[[Jobs], None], str]] = {
    "no operation": (lambda h: h.hand(0, 1, []), "of 0 operations"),
    "nine operations": (nine, "of 9 operations"),
    "an unknown operation": (lambda h: h.hand(0, 1, [Op(15)]), "of code 15"),
    "a name of no kind": (lambda h: h.hand(0, 1, [Op("create", name=9)]), "names kind 9"),
    "the journal with a number": (lambda h: h.hand(0, 1, [Op("create", name="journal", number=1)]), "names kind"),
    "data past its end": (lambda h: h.hand(0, 1, [Op("write", *fresh(h), length=1000, at=16000)]), "bytes at 16000"),
    "a place past the table": (lambda h: h.hand(0, 1, [Op("size", 16)]), "names place 16"),
    "a closed file": (closed_file, "not open"),
    "a file's old generation": (stale, "not open"),
    "a file closed earlier in the job": (lambda h: h.hand(0, 1, [Op("close", *(pg := fresh(h))), Op("size", *pg)]),
                                         "not open"),
    "a file another job names": (named_twice, "which a job in flight names"),
    "two syncs of the directory": (two_dir_syncs, "while another does"),
    "a list of a file": (lambda h: h.hand(0, 1, [Op("list", *fresh(h), length=60)]), "of the other kind"),
    "a removal of the journal": (lambda h: h.hand(0, 1, [Op("remove", name="journal")]), "the journal"),
    "a rename onto the journal": (lambda h: h.hand(0, 1, [Op("rename", name="temp", number=1, to="journal")]),
                                  "the journal"),
    "a seventeenth file": (seventeen, "all 16 places taken"),
}


def breaches(binary: Path) -> dict[str, str]:
    """Each way a job breaks the contract, each in a run of its own, and a job without a store."""
    seen = {}
    for what, (act, said) in BREACHES.items():
        with tempfile.TemporaryDirectory() as temp, Jobs(binary, Store(temp).options()) as h:
            act(h)
            h.broken(said)
            seen[what] = said
    proc, _, port = start(binary, [], "127.0.0.1")
    try:
        with socket.create_connection(("127.0.0.1", port), timeout=WAIT):
            if proc.stdin is None:
                raise LaneError("the host has no input")
            proc.stdin.write(f"next\nop 0 0 {Op('sync-dir').words(layout())[0]} 0 0 0 0 0 0 0 0 0\njob 0 1 1\nemit\n")
            proc.stdin.flush()
            status = proc.wait(timeout=WAIT)
            said = (proc.stderr.read() if proc.stderr else "").strip()
    finally:
        if proc.poll() is None:
            proc.kill()
            proc.wait()
    if status != 1 or "without a store" not in said:
        raise LaneError(f"a job without a store: status {status}, saying {said!r}")
    seen["a job without a store"] = said
    return seen


def marks(store: Store) -> list[str]:
    """Where a mark of this boot was left."""
    return [w for w in ("spool", "run") if (getattr(store, w) / MARK).is_file()
            and (getattr(store, w) / MARK).read_text().strip() == boot_id()]


def failing(b: Builds, points: list[str], ops: Callable[[tuple[int, int]], list[Op]]) -> dict[str, object]:
    """A file created, then a job of `ops` on it with `points` enabled from the start: its completion, what the
    file holds, the marks left, and whether the host then refuses to start."""
    data = b"hello world"
    with tempfile.TemporaryDirectory() as temp:
        store = Store(temp)
        with Jobs(b.fiu, store.options(), points) as h:
            pg = opened(h, 0, 1, "temp", 1)
            h.hand(0, 2, ops(pg), {0: data})
            done = h.wait(0)
            h.stop()
        held = store.spool / file_name("temp", 1)
        holds = held.read_bytes() if held.exists() else None
        left = marks(store)
        if left:
            refused(b.plain, store.options(), 4, "a sync failed since the machine started")
    return {"done": done[1:3], "holds": holds, "marks": left, "refused after": bool(left)}


def enabled(name: str, error: int, once: bool = False) -> str:
    return f"enable name={name},failinfo={error}" + (",onetime" if once else "")


def faults(b: Builds) -> dict[str, object]:
    """Each failure the disk may give, injected at the test build's points: its class, the mark a failed sync
    leaves and the refused start that follows, and the failures the host gets over."""
    w = layout()
    io, full, other = w["CLASS_IO"], w["CLASS_NO_SPACE"], w["CLASS_OTHER"]

    def write(pg: tuple[int, int]) -> Op:
        return Op("write", *pg, length=11)

    cases: dict[str, tuple[list[str], Callable[[tuple[int, int]], list[Op]], dict[str, object]]] = {
        "a data sync failing": ([enabled("dn/data-sync", errno.EIO)], lambda pg: [write(pg), Op("data-sync", *pg)],
                                {"done": [1, io], "marks": ["spool", "run"]}),
        "a sync failing": ([enabled("dn/sync", errno.EIO)], lambda pg: [write(pg), Op("sync", *pg)],
                           {"done": [1, io], "marks": ["spool", "run"]}),
        "the directory's sync failing": ([enabled("dn/sync-dir", errno.EIO)], lambda _pg: [Op("sync-dir")],
                                         {"done": [0, io], "marks": ["spool", "run"]}),
        "a close failing": ([enabled("dn/close", errno.EIO)], lambda pg: [Op("close", *pg)],
                            {"done": [0, io], "marks": ["spool", "run"]}),
        "no space": ([enabled("dn/write", errno.ENOSPC)], lambda pg: [write(pg)], {"done": [0, full], "marks": []}),
        "an interrupted write": ([enabled("dn/write", errno.EINTR, once=True)], lambda pg: [write(pg)],
                                 {"done": [1, 0], "holds": b"hello world"}),
        "a short write": ([enabled("dn/write-short", 3, once=True)], lambda pg: [write(pg)],
                          {"done": [1, 0], "holds": b"hello world"}),
        "a write of no progress": ([enabled("dn/write-short", 0)], lambda pg: [write(pg)], {"done": [0, full]}),
        "an interrupted sync": ([enabled("dn/sync", errno.EINTR, once=True)],
                                lambda pg: [write(pg), Op("sync", *pg)], {"done": [2, 0], "marks": []}),
        "another error": ([enabled("dn/rename", errno.EXDEV)],
                          lambda _pg: [Op("rename", name="temp", number=1, to="final", to_number=1)],
                          {"done": [0, other], "marks": []}),
        "one mark left": ([enabled("dn/mark-spool", errno.EIO), enabled("dn/data-sync", errno.EIO)],
                          lambda pg: [write(pg), Op("data-sync", *pg)], {"done": [1, io], "marks": ["run"]}),
    }
    seen: dict[str, object] = {}
    for what, (points, ops, wanted) in cases.items():
        got = failing(b, points, ops)
        if any(got[k] != v for k, v in wanted.items()):
            raise LaneError(f"{what}: {got}, not {wanted}")
        seen[what] = {k: v.hex() if isinstance(v, bytes) else v for k, v in got.items() if k in wanted}
    with tempfile.TemporaryDirectory() as temp, \
            Jobs(b.fiu, Store(temp).options(), [enabled("dn/mark-spool", errno.EIO), enabled("dn/mark-run", errno.EIO),
                                                enabled("dn/sync-dir", errno.EIO)]) as h:
        h.hand(0, 1, [Op("sync-dir")], fetch=False)
        h.broken("its mark could be left neither", 2)
        seen["no mark left"] = "the host ended"
    return seen


def in_flight(b: Builds) -> str:
    """A job handed in a slot whose job has not completed, held there by a slow sync."""
    with tempfile.TemporaryDirectory() as temp, \
            Jobs(b.fiu, Store(temp).options(), [enabled("dn/sync-slow", 2000)]) as h:
        h.hand(0, 1, [Op("sync-dir")], fetch=False)
        h.send("wake 1")
        h.fetch()
        if 0 in h.done:
            raise LaneError("a sync slowed down by 2 s completed before a batch that did not wait")
        h.hand(0, 2, [Op("sync-dir")], fetch=False)
        h.broken("still in flight")
    return "refused"


# Helgrind sees a race only in a schedule that shows it, so each scenario runs this many times.
RACE_RUNS = 5
HELGRIND = ("valgrind", "--tool=helgrind", "--error-exitcode=9", "-q")


def race_run(binary: Path, points: list[str] | None, failing_sync: bool) -> None:
    """Eight files created at once, then eight jobs at once writing, syncing and closing them, under
    Helgrind; with `failing_sync`, every data sync fails, so that eight workers leave the mark at once."""
    with tempfile.TemporaryDirectory() as temp:
        store = Store(temp)
        with Jobs(binary, store.options(), points, wrap=HELGRIND, wait=120) as h:
            jobs = h.w["JOBS"]
            h.hands([(slot, 1, [Op("create", name="final", number=slot)], {}) for slot in range(jobs)])
            places = [ok(h.wait(slot), 1, f"job {slot}")[:2] for slot in range(jobs)]
            h.hands([(slot, 2, [Op("write", p, g, length=4), Op("data-sync", p, g), Op("close", p, g)],
                      {0: b"race"}) for slot, (p, g) in enumerate(places)])
            for slot in range(jobs):
                done = h.wait(slot)
                if failing_sync and done[1:3] != [1, h.w["CLASS_IO"]]:
                    raise LaneError(f"job {slot} with its sync failing: {done[1:3]}")
                if not failing_sync:
                    ok(done, 3, f"writes in job {slot}")
            h.stop()
        if failing_sync and marks(store) != ["spool", "run"]:
            raise LaneError(f"eight syncs failing at once left marks in {marks(store)}")


def races(b: Builds) -> dict[str, int]:
    """Eight jobs at once and eight failed syncs marking at once, each run under Helgrind, which has to
    find no race."""
    for _ in range(RACE_RUNS):
        race_run(b.plain, None, failing_sync=False)
    for _ in range(RACE_RUNS):
        race_run(b.fiu, [enabled("dn/data-sync", errno.EIO)], failing_sync=True)
    return {"jobs at once": RACE_RUNS, "marks at once": RACE_RUNS}


def signalled(b: Builds) -> list[str]:
    """SIGTERM to a host with a store, idle and with a slow sync in flight: its loop takes it at the next
    batch and stops serving, status 0, as without a store."""
    seen = []
    for what, binary, points, ops in (("idle", b.plain, None, []),
                                      ("a sync in flight", b.fiu, [enabled("dn/sync-slow", 2000)], [Op("sync-dir")])):
        with tempfile.TemporaryDirectory() as temp, Jobs(binary, Store(temp).options(), points) as h:
            h.hand(0, 1, ops, fetch=False) if ops else h.send("emit")
            h.proc.send_signal(signal.SIGTERM)
            time.sleep(0.2)
            h.send("next")
            h.exited("stopped: a signal", 0, f"SIGTERM, {what}")
        seen.append(what)
    return seen


def on_plain(check: Callable[[Path], object]) -> Callable[[Builds], object]:
    return lambda b: check(b.plain)


# The checks, the quick ones first: a planted defect stops at the first that catches it.
CHECKS: dict[str, Callable[[Builds], object]] = {
    "listening": on_plain(listening), "no store": on_plain(no_store), "handed": on_plain(handed),
    "posting": on_plain(posting), "held": on_plain(held), "marks": on_plain(marks_at_start),
    "options": on_plain(options), "files": on_plain(files), "truncated": on_plain(truncated),
    "errors": on_plain(errors), "listing": on_plain(listing), "at once": on_plain(at_once),
    "breaches": on_plain(breaches), "a signal": signalled, "faults": faults, "in flight": in_flight, "races": races}

# Defects planted: (the file, the name, the text, what it becomes).
DEFECTS = [
    (HOST, "listening from the start",
     "    listen_port = ntohs(where.ss_family == AF_INET ? v4->sin_port : v6->sin6_port);\n",
     "    listen_port = ntohs(where.ss_family == AF_INET ? v4->sin_port : v6->sin6_port);\n    start_listening();\n"),
    (HOST, "a word to listen unchecked", "if (listen_word > 1 || (listening && !listen_word))", "if (0)"),
    (STORE, "the lock not taken", "if (flock(spool, LOCK_EX | LOCK_NB)) {", "if (0) {"),
    (STORE, "a mark of this boot let through", "if (!memcmp(seen, id, BOOT_ID))",
     "if (0 && !memcmp(seen, id, BOOT_ID))"),
    (STORE, "a mark cut short taken for another boot's", "if (n != BOOT_ID)\n        refuse(",
     "if (n < 0)\n        refuse("),
    (STORE, "a mark of another boot kept", "if (unlinkat(dir, MARK, 0) && errno != ENOENT)", "if (0)"),
    (STORE, "the run directory's mark unread", "    check_mark(run, run_path, boot);\n", ""),
    (STORE, "the last bits of a prefix ignored", "if (rest && ", "if (0 && "),
    (STORE, "no network by default", '        add_net("127.0.0.0/8");\n        add_net("::1/128");\n', ""),
    (STORE, "no random octets", "ssize_t n = getrandom(random_octets + got, sizeof random_octets - got, 0);",
     "ssize_t n = (ssize_t)(sizeof random_octets - got);"),
    (STORE, "no groups handed", "dn_put_word(next + DN_SESSION_NEXT_GROUP_COUNT, group_count);",
     "dn_put_word(next + DN_SESSION_NEXT_GROUP_COUNT, 0);"),
    (JOBS, "names in capitals", 'snprintf(name, NAME, "%c%016" PRIx64', 'snprintf(name, NAME, "%c%016" PRIX64'),
    (JOBS, "a generation unchecked", "if (!f->open || f->gen != op->gen || closed[op->place])",
     "if (!f->open || closed[op->place])"),
    (JOBS, "a file in flight named again", "if (f->busy && f->busy != k + 1)", "if (0 && f->busy != k + 1)"),
    (JOBS, "two syncs of the directory let through", "if (j->dir_sync && dir_syncs)", "if (0 && dir_syncs)"),
    (JOBS, "a name lost between pages", "            seekdir(dir, at);\n", "            (void)at;\n"),
    (JOBS, "a job going on after a failure",
     "                if (syncs(j->ops[i].code)) dn_store_mark_failed();\n                break;\n",
     "                if (syncs(j->ops[i].code)) dn_store_mark_failed();\n"),
    (JOBS, "a name not found taken for another error", "    case ENOENT: return DN_SESSION_CLASS_NOT_FOUND;\n", ""),
    (JOBS, "a short read reported whole", "        result[0] = (uint64_t)n;\n", "        result[0] = op->length;\n"),
    (JOBS, "a closed file's place kept", "        *f = (struct file){.fd = -1, .gen = f->gen + 1};",
     "        f->gen++;"),
    (JOBS, "a signal's interruption reported", "while (result_ < 0 && errno == EINTR);", "while (result_ < 0 && 0);"),
    (JOBS, "a short write left short", "        n -= (uint64_t)w;\n", "        n = 0;\n"),
    (JOBS, "a write of no progress taken as done", "        if (w == 0) {", "        if (0 && w == 0) {"),
    (JOBS, "no mark on a failed sync", "                if (syncs(j->ops[i].code)) dn_store_mark_failed();",
     "                if (0 && syncs(j->ops[i].code)) dn_store_mark_failed();"),
    (JOBS, "a failed close not a failed sync", "           code == DN_SESSION_OP_CLOSE;", "           0;"),
    (JOBS, "no space taken for another error", "    case ENOSPC:\n", ""),
    (STORE, "one mark failing ending the host", "    if (!left)\n", "    if (left < 2)\n"),
    (STORE, "no mark leaving the host going on", "    if (!left)\n", "    if (0 && !left)\n"),
    (JOBS, "a worker taking signals", "    sigfillset(&all);\n", "    sigemptyset(&all);\n"),
    (JOBS, "a completion marked without the lock",
     "        pthread_mutex_lock(&lock);\n        j->state = DONE;\n        pthread_mutex_unlock(&lock);\n",
     "        j->state = DONE;\n"),
]


def check() -> Report:
    OUT.mkdir(parents=True, exist_ok=True)
    (OUT / "dn_session_layout.h").write_text(lanes.emit("emit-session-layout"))
    builds = build("host")
    results = {name: run(builds) for name, run in CHECKS.items()}
    caught = {}
    for index, (source, name, text, becomes) in enumerate(DEFECTS):
        planted = OUT / f"defect-{index}.c"
        planted.write_text(lanes.plant(source.read_text(), text, becomes, 1, f"{source.name}, for a planted defect,",
                                       exact=True))
        broken = build(f"defect-{index}", **{{HOST: "host", STORE: "store", JOBS: "jobs"}[source]: planted})
        for check_name, run in CHECKS.items():
            try:
                run(broken)
            except LaneError as error:
                caught[name] = f"{check_name}: {str(error)[:200]}"
                break
        else:
            raise LaneError(f"the defect {name!r} was not caught")
    return Report("checked", None, [HOST, STORE, lanes.NATIVE / "store.h", JOBS, lanes.NATIVE / "jobs.h", DRIVER],
                  {"checks": results, "defects_caught": caught})


def main() -> None:
    lanes.lane_main("HOST", OUT, check)


if __name__ == "__main__":
    main()
