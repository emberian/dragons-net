#!/usr/bin/env python3
# SPDX-License-Identifier: AGPL-3.0-or-later
"""The session (`DN.News.SessionSpec`), driven by a simulated host and judged by `session_ref`.

A scenario is a set of clients: when each connects, what it sends and when, how much of what it is
sent it takes at once and how soon it takes more, when it stops taking for a while, and when it
shuts down its side or resets. The simulated host does what docs/decisions/0003-nntp-slice.md asks
of the real one: it gives each connection the lowest free index and the next generation of it, holds
back connections while every index is in use, reads from a connection only while the program's last
action asked to and everything it carried was taken, reports at most one input a connection a batch
and at most 512 bytes of it, reports a connection ready to write once the client takes more of what
it left, reports the end of input once the client's bytes are all read, takes the connections in
turn when more than a batch has something to report, and runs the next turn at the time the program
asked for or at once when anything waits to be reported. In some scenarios it also reports events
of a connection that is gone — input, readiness, the end of input and its close — while its index
is free and again once the index serves another, which the program has to leave alone; in one a
client is reported ready to write and still takes nothing. Some scenarios run with the longest and
the shortest identity that fit the replies. `dn-compiler session-model` answers the turns a line at
a time.

Every trace has to be one `session_ref.judge` accepts, and every scenario has to end with each
connection closed. Hosts that break the contract are answered with the code of the breach. Each rule
of the session broken in the model (`DN.News.SessionMutant`) has to be caught by the judge on some
scenario, and each defect planted in a recorded trace by the judge's check for it.

Scenarios with a store (decision 0005) also give the session a spool: the host keeps it on the file
system of scripts/fs_ref.py, does each job's operations when the job completes, a delay after it is
handed over, and fails the operations a scenario names, leaving what `fs_ref.fail` allows; the
judge checks the header sections with scripts/article_ref.py, run by the Python of
scripts/requirements-tests.txt.
"""
from __future__ import annotations

import argparse
from collections.abc import Callable, Iterator
from concurrent.futures import ThreadPoolExecutor
import contextlib
import copy
from dataclasses import dataclass, field
import itertools
import os
from pathlib import Path
import queue
import random
import subprocess
import sys
import threading
from typing import IO, Any, Self

sys.path.insert(0, str(Path(__file__).resolve().parent))
import fs_ref
import lanes  # the path above is what makes these importable
from lanes import LaneError, Report
import post_ref as P
import recovery_ref
import session_ref as ref
from session_ref import Action, Event, Turn, Violation
import store_ref as J

REVISION, SOURCE = b"0123abc", b"https://example.org/dragons-net"
Identity = tuple[bytes, bytes]
IDENTITY: Identity = (REVISION, SOURCE)
# The longest identity that fits the replies, of the highest and the lowest visible byte, and the
# shortest.
LONGEST: Identity = (b"~" * 64, b"!" * 200)
SHORTEST: Identity = (b"r", b"s")
GREETING = len(ref.texts(REVISION, SOURCE)["greeting"])
BATCH, TURNS, TIMEOUT = 16, 20_000, 60
# The rules `DN.News.SessionMutant` breaks, by the name `dn-compiler session-model --mutant` takes.
MUTANTS = ("line-renewed", "no-line-deadline", "line-while-busy", "idle-not-renewed", "zero-take-counts",
           "blank-counts", "first-not-cleared", "read-not-resumed", "no-greeting", "stale-applied",
           "end-ignored", "resend-anytime", "wake-early", "answer-while-busy", "quit-tail",
           "article-renewed", "no-article-deadline", "wait-deadlines", "greet-all", "post-after-stop",
           "post-unpermitted", "capabilities-stale", "no-read-control", "fifth-post", "article-longer",
           "unstuffed", "reserved-taken", "no-file-sync", "no-dir-sync",
           "no-journal-sync", "dir-syncs-overlap", "appends-overlap", "numbers-not-above",
           "sync-failure-ignored", "unknown-answered", "names-left", "unseparated", "capacity-over",
           "refused-reserves", "stop-spares-flight", "commit-after-stop", "wait-through-stop", "lowest-first",
           "ninth-read", "lines-unchecked", "crc-unchecked", "longer-served", "no-xref", "status-early",
           "read-lowest-first", "idle-while-fetching", "read-while-fetching", "end-unsought", "header-unchecked",
           "jobs-shared", "left-open", "group-keeps-current", "empty-keeps-current", "unknown-deselects",
           "number-keeps-current", "id-moves", "next-inclusive", "last-inclusive", "move-stays", "number-any-group",
           "group-caseless", "number-without-group", "utf8-unchecked", "group-name-unchecked", "unread-moves",
           "listgroup-keeps-current", "listgroup-later", "range-ignored", "range-end-exclusive", "wildmat-leftmost",
           "negation-ignored", "marks-swapped", "status-fixed", "list-default-newsgroups", "list-keyword-cased",
           "first-negated", "date-monotonic", "date-units", "newgroups-unchecked", "part-longer", "listing-reads",
           "star-non-empty", "wildmat-unanchored", "wildmat-caseless", "group-line-dropped", "end-forced",
           "date-unpadded", "line-while-listing", "reader-unadvertised", "reader-without-store", "mode-stale",
           "mode-deselects", "refused-stays-open", "mode-ungreeted", "xover-by-id", "metadata-served", "field-colon",
           "overview-fmt-args", "headers-any-arg", "id-numbered", "over-range-exclusive", "legacy-empty-refused",
           "over-empty-listed", "over-moves", "folds-kept", "tabs-kept", "fields-cased", "last-field", "space-kept",
           "bytes-stuffed", "bytes-without-xref", "lines-whole", "overview-without-xref", "absent-dropped",
           "absent-listed", "xhdr-numbered", "overview-longer", "overview-early", "status-repeated",
           "view-failure-answered", "range-later", "header-stuffed", "xref-folded", "metadata-cased",
           "first-failure-closed", "refused-after-group")
# Those of reading, tried on the scenarios that read first, those of the selected group, on the
# scenarios that select one, those of the listings, on the scenarios that list, those of READER
# and MODE READER, on the scenarios that ask for them, and those of OVER and HDR, on theirs.
READ_MUTANTS = MUTANTS[MUTANTS.index("ninth-read"):MUTANTS.index("group-keeps-current")]
GROUP_MUTANTS = MUTANTS[MUTANTS.index("group-keeps-current"):MUTANTS.index("listgroup-keeps-current")]
LIST_MUTANTS = MUTANTS[MUTANTS.index("listgroup-keeps-current"):MUTANTS.index("reader-unadvertised")]
MODE_MUTANTS = MUTANTS[MUTANTS.index("reader-unadvertised"):MUTANTS.index("xover-by-id")]
VIEW_MUTANTS = MUTANTS[MUTANTS.index("xover-by-id"):]
REQUIREMENTS = lanes.ROOT / "scripts/requirements-tests.txt"
ARTICLES = lanes.ROOT / "scripts/article_ref.py"


class Unfinished(LaneError):
    """A scenario that could not run to its end, with the turns it had."""

    def __init__(self, message: str, trace: list[Turn]) -> None:
        super().__init__(message)
        self.trace = trace


@dataclass
class Client:
    opens: int
    sends: list[tuple[int, bytes]] = field(default_factory=list)
    shut: int | None = None
    reset: int | None = None
    # the most bytes of one send it takes, from `slow` on, and how long it takes to take more
    take: int | None = None
    slow: int = 0
    pace: int = 1
    # it takes nothing from the first time to the second
    pause: tuple[int, int] = (0, 0)
    # it is reported ready to write even while it takes nothing
    false_ready: bool = False
    # it may post
    post: bool = False

    def stream(self, now: int) -> bytes:
        return b"".join(data for at, data in self.sends if at <= now)

    def paused(self, now: int) -> bool:
        return self.pause[0] <= now < self.pause[1]

    def takes(self, now: int, length: int) -> int:
        if self.paused(now):
            return 0
        return length if self.take is None or now < self.slow else min(length, self.take)

    def ready_at(self, now: int) -> int:
        """When it is reported ready to write after leaving part of a send."""
        if self.false_ready or not self.paused(now + self.pace):
            return now + self.pace
        return max(now + self.pace, self.pause[1])


@dataclass
class Link:
    client: Client
    idx: int
    gen: int
    read: int = 0
    reading: bool = False
    unsent: bool = False
    ready: int = 0
    ended: bool = False

    def asked(self) -> bool:
        return self.reading and not self.unsent


def model_command(mutant: str | None = None) -> list[str]:
    """`dn-compiler session-model`, with a rule broken or not."""
    return [str(lanes.DN_COMPILER), "session-model", *(["--mutant", mutant] if mutant else [])]


class Speaker:
    """A session run as a process, the model or the compiled program, that speaks the line protocol
    of `dn-compiler session-model` a line at a time, with a bound on every wait."""

    def __init__(self, command: list[str], identity: Identity = IDENTITY) -> None:
        self.proc = subprocess.Popen(command, stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                                     text=True, bufsize=1)
        self.lines = lanes.Lines(self.pipe(self.proc.stdout))
        self.complaints: list[str] = []
        self.listener = threading.Thread(target=self.listen, args=(self.pipe(self.proc.stderr),), daemon=True)
        self.listener.start()
        self.say(f"identity {identity[0].hex() or '-'} {identity[1].hex() or '-'}")

    def listen(self, stream: IO[str]) -> None:
        for line in stream:
            self.complaints.append(line.rstrip("\n"))

    def why(self) -> str:
        """What the process said on stderr last, if anything: once it has ended, all it said."""
        if self.proc.poll() is not None:
            self.listener.join(timeout=TIMEOUT)
        return f", saying {self.complaints[-1]!r}" if self.complaints else ""

    def __enter__(self) -> Self:
        return self

    def __exit__(self, *_: object) -> None:
        if self.proc.poll() is None:
            self.proc.kill()
        self.proc.wait(timeout=TIMEOUT)
        for stream in (self.proc.stdin, self.proc.stdout, self.proc.stderr):
            if stream:
                stream.close()

    def pipe(self, stream: IO[str] | None) -> IO[str]:
        if stream is None:
            raise LaneError("the session has no pipe")
        return stream

    def say(self, line: str) -> None:
        try:
            self.pipe(self.proc.stdin).write(line + "\n")
        except OSError as error:
            raise LaneError(f"the session no longer listens ({error}){self.why()}") from None

    def hear(self) -> list[str]:
        try:
            self.pipe(self.proc.stdin).flush()
            line = self.lines.get(TIMEOUT)
        except OSError as error:
            raise LaneError(f"the session no longer listens ({error}){self.why()}") from None
        except queue.Empty:
            raise LaneError(f"the session gave no answer in {TIMEOUT} s") from None
        if not line:
            raise LaneError(f"the session stopped answering (status {self.ended()}){self.why()}")
        return line.rstrip("\n").split(" ")

    def ended(self) -> int:
        try:
            return self.proc.wait(timeout=TIMEOUT)
        except subprocess.TimeoutExpired:
            raise LaneError(f"the session did not end in {TIMEOUT} s") from None

    def output(self) -> list[str]:
        """Every line the session answers until it ends."""
        out: list[str] = []
        while True:
            try:
                line = self.lines.get(TIMEOUT)
            except queue.Empty:
                raise LaneError(f"the session gave no answer in {TIMEOUT} s") from None
            if not line:
                return out
            out.append(line.rstrip("\n"))

    def turn(self, now: int, events: list[Event]) -> list[Action] | int:
        self.say(f"turn {now}")
        for e in events:
            self.say(" ".join([e.kind, str(e.idx), str(e.gen), *([e.data.hex() or "-"] if e.kind == "recv" else [])]))
        self.say("go")
        actions: list[Action] = []
        while (words := self.hear()) != ["done"]:
            match words:
                case ["stop", code]:
                    return int(code)
                case ["send", idx, gen, data, "0" | "1" as read]:
                    actions.append(Action("send", int(idx), int(gen), b"" if data == "-" else bytes.fromhex(data),
                                          read == "1"))
                case ["graceful" | "close" as kind, idx, gen]:
                    actions.append(Action(kind, int(idx), int(gen)))
                case _:
                    raise LaneError(f"the session answered {' '.join(words)}")
        return actions

    def turn_post(self, now: int, wall: int, events: list[Event], dones: list[P.Done]) -> \
            tuple[list[Action], list[tuple[int, int, list[P.Op]]]] | int:
        """A turn with a store: the wall clock, the completions, and the jobs the session answers."""
        self.say(f"turn {now} {wall}")
        for e in events:
            extra = [e.data.hex() or "-"] if e.kind == "recv" else ["1"] if e.kind == "open" and e.post else []
            self.say(" ".join([e.kind, str(e.idx), str(e.gen), *extra]))
        for done in dones:
            said = ",".join(f"{a}:{b}" for a, b in done[3]) or "-"
            self.say(f"complete {done[0]} {done[1]} {done[2]} {said}" + (f" {done[5].hex()}" if done[5] else ""))
        self.say("go")
        actions: list[Action] = []
        jobs: list[tuple[int, int, list[P.Op]]] = []
        while (words := self.hear()) != ["done"]:
            match words:
                case ["stop", code]:
                    return int(code)
                case ["send", idx, gen, data, "0" | "1" as read]:
                    actions.append(Action("send", int(idx), int(gen), b"" if data == "-" else bytes.fromhex(data),
                                          read == "1"))
                case ["graceful" | "close" as kind, idx, gen]:
                    actions.append(Action(kind, int(idx), int(gen)))
                case ["job", slot, gen, *ops]:
                    jobs.append((int(slot), int(gen), [operation(op) for op in ops]))
                case _:
                    raise LaneError(f"the session answered {' '.join(words)}")
        return actions, jobs

    def settle(self, took: list[int]) -> int | str:
        self.say(" ".join(["took", *map(str, took)]))
        match self.hear():
            case ["deadline", at]:
                return int(at)
            case ["stop", code]:
                return f"stop {code}"
            case words:
                raise LaneError(f"the session answered {' '.join(words)} to what was taken")


def operation(token: str) -> P.Op:
    """An operation of a job, as `dn-compiler session-model` writes it."""
    match token.split(":"):
        case ["create" | "remove" | "open" as kind, name]:
            return P.Op(kind, name=name.encode())
        case ["read", place, gen, offset, length]:
            return P.Op("read", int(place), int(gen), int(offset), length=int(length))
        case ["write", place, gen, offset, data]:
            return P.Op("write", int(place), int(gen), int(offset), bytes.fromhex(data))
        case ["datasync" | "close" as kind, place, gen]:
            return P.Op(kind, int(place), int(gen))
        case ["rename", src, dst]:
            return P.Op("rename", name=src.encode(), to=dst.encode())
        case ["syncdir"]:
            return P.Op("syncdir")
    raise LaneError(f"not an operation: {token}")


def run(clients: list[Client], command: list[str], ghosts: bool = False, identity: Identity = IDENTITY) -> list[Turn]:
    """The turns of one scenario, as the simulated host lives them."""
    trace: list[Turn] = []
    with Speaker(command, identity) as session:
        try:
            simulate(session, clients, ghosts, trace)
        except LaneError as error:
            raise Unfinished(str(error), trace) from None
    return trace


def simulate(session: Speaker, clients: list[Client], ghosts: bool, trace: list[Turn]) -> None:
    links: dict[int, Link] = {}
    gens = [0] * ref.CONNS
    waiting = sorted(range(len(clients)), key=lambda k: clients[k].opens)
    echoes: list[Event] = []
    # the generation of a connection gone, whose events come again once its index serves another
    graves: dict[int, int] = {}
    now, start = min((c.opens for c in clients), default=1), 0
    for _ in range(TURNS):
        events = echoes[:BATCH]
        echoes = echoes[BATCH:]
        cut = bool(echoes)
        order = [(start + k) % ref.CONNS for k in range(ref.CONNS)]
        start = (start + 1) % ref.CONNS
        for idx in order:
            if idx not in links:
                continue
            link = links[idx]
            report = news(link, now)
            if report is None:
                continue
            if len(events) == BATCH:
                cut = True
                break
            events.append(report)
            if report.kind == "closed":
                del links[idx]
                if ghosts:
                    graves[idx] = link.gen
                    echoes += haunting(idx, link.gen)
            elif report.kind == "recv":
                link.read += len(report.data)
            elif report.kind == "end":
                link.ended = True
        while waiting and clients[waiting[0]].opens <= now:
            free = [i for i in range(ref.CONNS) if i not in links]
            if not free or len(events) == BATCH:
                break
            idx = free[0]
            gens[idx] += 1
            links[idx] = Link(clients[waiting.pop(0)], idx, gens[idx])
            events.append(Event("open", idx, gens[idx]))
            if idx in graves:
                echoes += haunting(idx, graves.pop(idx))
        answer = session.turn(now, events)
        if isinstance(answer, int):
            raise LaneError(f"the session stopped with code {answer} on a host that kept the contract")
        took = []
        for action in answer:
            target = links.get(action.idx)
            if target is None or target.gen != action.gen:
                raise LaneError(f"an action for {action.idx}/{action.gen}, which the host does not hold")
            if action.kind == "send":
                data = action.data
                k = target.client.takes(now, len(data))
                took.append(k)
                target.unsent = k < len(data)
                target.ready = target.client.ready_at(now)
                target.reading = action.read
            else:
                del links[action.idx]
                if ghosts:
                    graves[action.idx] = action.gen
                    echoes += haunting(action.idx, action.gen)
        deadline = session.settle(took)
        if isinstance(deadline, str):
            raise LaneError(f"the session answered {deadline} to what the host took")
        trace.append(Turn(now, events, answer, took, deadline))
        if not links and not waiting and not echoes:
            return
        later = next_time(now, deadline, links, clients, waiting, cut or bool(echoes))
        if later is None:
            raise LaneError(f"nothing left to happen after {now}, with connections open")
        now = later
    raise LaneError(f"the scenario had not ended after {TURNS} turns, at {now}")


KEY = bytes(range(16))
WALL = 1_790_000_000_000
WALL_LIMIT = 1000 * 2 ** 40


def fresh_spool() -> list[tuple[bytes, bytes]]:
    """An empty spool as recovery leaves it: a journal of its format and a start record."""
    journal = J.frame(KEY, 0, J.FORMAT, J.MAGIC + KEY)
    return [(b"journal", journal + J.frame(KEY, len(journal), J.START, b""))]


def spool_with(groups: list[list[tuple[bytes, int]]]) -> list[tuple[bytes, bytes]]:
    """A spool holding an article for each list of groups and numbers, then a start record."""
    journal = J.frame(KEY, 0, J.FORMAT, J.MAGIC + KEY)
    files = []
    for seq, gs in enumerate(groups, 1):
        octets = b"From: a@b.example\r\n\r\nold\r\n"
        c = (seq, b"<%d@old.example>" % seq, gs, 19, len(octets), J.crc32c(octets))
        journal += J.frame(KEY, len(journal), J.COMMIT, J.payload(c))
        files.append((recovery_ref.name_of("a", seq), octets))
    return [(b"journal", journal + J.frame(KEY, len(journal), J.START, b"")), *files]


def spool_holding(articles: list[tuple[bytes, list[tuple[bytes, int]]]], wrong_crc: tuple[int, ...] = (),
                  header_off: int = 0) -> list[tuple[bytes, bytes]]:
    """A spool holding each file as stored, committed to its groups as `<SEQ@old.example>`, then a
    start record; the commits numbered in `wrong_crc` with a CRC-32C not their file's, each header
    section's size recorded `header_off` octets off."""
    journal = J.frame(KEY, 0, J.FORMAT, J.MAGIC + KEY)
    files = []
    for seq, (octets, gs) in enumerate(articles, 1):
        crc = J.crc32c(octets) ^ (1 if seq in wrong_crc else 0)
        c = (seq, b"<%d@old.example>" % seq, gs, octets.index(b"\r\n\r\n") + 2 + header_off, len(octets), crc)
        journal += J.frame(KEY, len(journal), J.COMMIT, J.payload(c))
        files.append((recovery_ref.name_of("a", seq), octets))
    return [(b"journal", journal + J.frame(KEY, len(journal), J.START, b"")), *files]


def stored(*body: bytes) -> bytes:
    """A file as the store holds an article: its header section, the empty line, its body."""
    return b"From: a@b.example\r\nSubject: s\r\n\r\n" + b"".join(line + b"\r\n" for line in body)


def stored_header(size: int) -> bytes:
    """A file as stored whose header section is of `size` octets, CRLFs counted: X-Pad fields after
    the others; then the empty line and a body of one line."""
    head = b"From: a@b.example\r\nSubject: s\r\n"
    pads = b"".join(b"X-Pad: " + b"p" * (k - 9) + b"\r\n" for k in chunks(size - len(head), 900, 10))
    return head + pads + b"\r\nbody\r\n"


def stored_of(size: int) -> bytes:
    """A file as stored of exactly `size` octets."""
    head = stored()
    return head + b"".join(b"y" * (k - 2) + b"\r\n" for k in chunks(size - len(head), 900, 2))


@dataclass
class Failure:
    """The `nth` operation of `kind` failing, leaving what `fs_ref.fail` makes of `partial`; the
    operations on the journal are `journal-write` and `journal-sync`."""
    kind: str
    nth: int = 1
    partial: int = 0


@dataclass
class Spool:
    """A store for a scenario: its groups, the spool as recovered, how long a job of each kind takes
    (a write, a sync, a rename, ...; one by default), the operations that fail, and files changed
    after recovery, as a disk may change them under the store."""
    groups: list[bytes]
    image: list[tuple[bytes, bytes]] = field(default_factory=fresh_spool)
    delays: dict[str, int] = field(default_factory=dict)
    failures: list[Failure] = field(default_factory=list)
    identity: bytes = b"dn.example"
    run: bytes = bytes.fromhex("0011223344556677")
    journal: tuple[int, int] = (1, 0)
    job_gen: int = 7
    tamper: list[tuple[bytes, bytes]] = field(default_factory=list)
    # the wall clock when the host's clock is zero, and how long after the time the program names the
    # host runs its next turn
    wall: int = WALL
    late: int = 0

    def start(self) -> P.Start:
        return P.Start(self.groups, self.identity, self.run, self.image, self.journal, self.job_gen, self.tamper)

    def line(self) -> str:
        groups = ",".join(g.hex() for g in self.groups) or "-"
        image = ";".join(f"{n.hex()}={o.hex() or '-'}" for n, o in self.image) or "-"
        return (f"store {groups} {self.identity.hex()} {self.run.hex()} {self.journal[0]} {self.journal[1]} "
                f"{self.job_gen} {image}")


class Host:
    """The host's side of the store: the spool on `fs_ref`'s file system, the places of open files,
    and the jobs in flight, each done when it completes."""

    def __init__(self, spool: Spool) -> None:
        self.spool = spool
        self.disk = fs_ref.Disk()
        for name, octets in spool.image:
            self.disk.files.append(fs_ref.File(seen=octets, kept=octets, most=len(octets)))
            self.disk.names[name] = fs_ref.Name(synced=len(self.disk.files) - 1)
        for name, octets in spool.tamper:
            held = self.disk.holding(name)
            if held is None:
                raise LaneError(f"a change to {name!r}, which the spool does not hold")
            self.disk.files[held] = fs_ref.File(seen=octets, kept=octets, most=len(octets))
        self.gens = [0] * P.PLACES
        place, gen = spool.journal
        self.gens[place] = gen
        self.places = {place: self.disk.holding(b"journal") or 0}
        self.jobs: dict[int, tuple[int, int, list[P.Op]]] = {}
        self.counts: dict[str, int] = {}

    def take(self, now: int, jobs: list[tuple[int, int, list[P.Op]]]) -> None:
        for slot, gen, ops in jobs:
            if slot in self.jobs:
                raise LaneError(f"a job in slot {slot}, still in flight")
            delay = max(self.spool.delays.get(self.label(op), 1) for op in ops)
            self.jobs[slot] = (now + delay, gen, ops)

    def label(self, op: P.Op) -> str:
        on_journal = op.kind in ("write", "datasync") and (op.place, op.gen) == self.spool.journal
        return {"write": "journal-write", "datasync": "journal-sync"}[op.kind] if on_journal else op.kind

    def due(self) -> int | None:
        return min((at for at, _, _ in self.jobs.values()), default=None)

    def complete(self, now: int) -> list[P.Done]:
        """The jobs due by `now`, done, in the order of their slots."""
        done: list[P.Done] = []
        for slot in sorted(self.jobs):
            at, gen, ops = self.jobs[slot]
            if at <= now:
                del self.jobs[slot]
                done.append(self.run(slot, gen, ops))
        return done

    def run(self, slot: int, gen: int, ops: list[P.Op]) -> P.Done:
        results: list[tuple[int, int]] = []
        data = b""
        for k, op in enumerate(ops):
            label = self.label(op)
            self.counts[label] = self.counts.get(label, 0) + 1
            failure = next((f for f in self.spool.failures if f.kind == label and f.nth == self.counts[label]), None)
            fop = self.disk_op(op)
            if failure is not None:
                if fop is not None and op.kind not in ("open", "read"):
                    fs_ref.fail(self.disk, fop, failure.partial)
                if op.kind == "close":
                    self.closed(op)
                return slot, gen, k, results, failure.partial, data
            if op.kind == "read" and fop is not None:
                said = fs_ref.do(self.disk, fop)
                data = bytes.fromhex(said[6:]) if said[6:] != "-" else b""
                results.append((len(data), 0))
                continue
            result = self.done(op, fop)
            if result is None:
                return slot, gen, k, results, 0, data
            results.append(result)
        return slot, gen, len(ops), results, 0, data

    def file(self, op: P.Op) -> int:
        if self.places.get(op.place) is None or self.gens[op.place] != op.gen:
            raise LaneError(f"an operation on place {op.place}/{op.gen}, not open")
        return self.places[op.place]

    def disk_op(self, op: P.Op) -> fs_ref.Op | None:
        match op.kind:
            case "create":
                return "create", [op.name.hex()]
            case "open":
                return "open", [op.name.hex()]
            case "read":
                return "read", [str(self.file(op)), str(op.offset), str(op.length)]
            case "write":
                f = self.file(op)
                if op.offset != len(self.disk.files[f].seen):
                    raise LaneError(f"a write at {op.offset}, not where its file ends")
                return "append", [str(f), op.data.hex()]
            case "datasync":
                return "sync", [str(self.file(op))]
            case "rename":
                return "rename", [op.name.hex(), op.to.hex()]
            case "remove":
                return "remove", [op.name.hex()]
            case "syncdir":
                return "sync-dir", []
        self.file(op)
        return None

    def closed(self, op: P.Op) -> None:
        del self.places[op.place]
        self.gens[op.place] += 1

    def done(self, op: P.Op, fop: fs_ref.Op | None) -> tuple[int, int] | None:
        """An operation that succeeds, its result; none when the file system refuses it."""
        if fop is None:
            self.closed(op)
            return 0, 0
        said = fs_ref.do(self.disk, fop)
        if said in ("exists", "missing"):
            return None
        if op.kind in ("create", "open"):
            place = next(p for p in range(P.PLACES) if p not in self.places)
            self.places[place] = int(said[5:])
            return place, self.gens[place]
        return 0, 0


def run_post(clients: list[Client], spool: Spool, command: list[str], line: str | None = None) -> list[Turn]:
    """The turns of a scenario with a store, as the simulated host lives them; `line` tells the
    session of the store, if not the spool's own line."""
    trace: list[Turn] = []
    with Speaker(command) as session:
        session.say(line or spool.line())
        try:
            simulate_post(session, clients, Host(spool), trace)
        except LaneError as error:
            raise Unfinished(str(error), trace) from None
    return trace


def simulate_post(session: Speaker, clients: list[Client], host: Host, trace: list[Turn]) -> None:
    links: dict[int, Link] = {}
    gens = [0] * ref.CONNS
    waiting = sorted(range(len(clients)), key=lambda k: clients[k].opens)
    now = min((c.opens for c in clients), default=1)
    for _ in range(TURNS):
        events: list[Event] = []
        for idx in sorted(links):
            link = links[idx]
            report = news(link, now)
            if report is None or len(events) == BATCH:
                continue
            events.append(report)
            if report.kind == "closed":
                del links[idx]
            elif report.kind == "recv":
                link.read += len(report.data)
            elif report.kind == "end":
                link.ended = True
        while waiting and clients[waiting[0]].opens <= now and len(events) < BATCH:
            free = [i for i in range(ref.CONNS) if i not in links]
            if not free:
                break
            idx = free[0]
            gens[idx] += 1
            client = clients[waiting.pop(0)]
            links[idx] = Link(client, idx, gens[idx])
            events.append(Event("open", idx, gens[idx], post=client.post))
        dones = host.complete(now)
        wall = host.spool.wall + now
        answer = session.turn_post(now, wall, events, dones)
        if isinstance(answer, int):
            raise LaneError(f"the session stopped with code {answer} on a host that kept the contract")
        actions, jobs = answer
        took = []
        for action in actions:
            target = links.get(action.idx)
            if target is None or target.gen != action.gen:
                raise LaneError(f"an action for {action.idx}/{action.gen}, which the host does not hold")
            if action.kind == "send":
                k = target.client.takes(now, len(action.data))
                took.append(k)
                target.unsent = k < len(action.data)
                target.ready = target.client.ready_at(now)
                target.reading = action.read
            else:
                del links[action.idx]
        try:
            host.take(now, jobs)
        except LaneError:
            # The turn is the judge's to see, the jobs that break the host's contract with it.
            trace.append(Turn(now, events, actions, took, 0, wall, dones, jobs))
            raise
        deadline = session.settle(took)
        if isinstance(deadline, str):
            raise LaneError(f"the session answered {deadline} to what the host took")
        trace.append(Turn(now, events, actions, took, deadline, wall, dones, jobs))
        if not links and not waiting and not host.jobs:
            return
        now = next_post_time(now, deadline + host.spool.late if deadline else 0, links, clients, waiting, host)
    raise LaneError(f"the scenario had not ended after {TURNS} turns, at {now}")


def next_post_time(now: int, deadline: int, links: dict[int, Link], clients: list[Client], waiting: list[int],
                   host: Host) -> int:
    due = host.due()
    if due is not None and due <= now:
        return now
    later = [t for t in (next_time(now, deadline, links, clients, waiting, False), due) if t is not None]
    if not later:
        raise LaneError(f"nothing left to happen after {now}, with connections open")
    return min(later)


def haunting(idx: int, gen: int) -> list[Event]:
    """Every kind of event of a connection gone, as a host may still report them."""
    return [Event("closed", idx, gen), Event("recv", idx, gen, b"QUIT\r\n"), Event("writable", idx, gen),
            Event("end", idx, gen)]


def news(link: Link, now: int) -> Event | None:
    """What the host has to report of a connection at `now`, if anything."""
    c = link.client
    if c.reset is not None and c.reset <= now:
        return Event("closed", link.idx, link.gen)
    if link.unsent:
        return Event("writable", link.idx, link.gen) if now >= link.ready else None
    if link.asked():
        stream = c.stream(now)
        if link.read < len(stream):
            return Event("recv", link.idx, link.gen, stream[link.read:link.read + ref.CHUNK])
        if c.shut is not None and c.shut <= now and not link.ended and link.read == len(c.stream(c.shut)):
            return Event("end", link.idx, link.gen)
    return None


def next_time(now: int, deadline: int, links: dict[int, Link], clients: list[Client], waiting: list[int],
              pending: bool) -> int | None:
    """When the host's next turn comes: at once if something waits to be reported, else the
    program's deadline or the first thing that happens; none when nothing is left to happen."""
    free = len(links) < ref.CONNS
    if pending or (deadline and deadline <= now) or (waiting and free and clients[waiting[0]].opens <= now):
        return now
    if any(news(link, now) is not None for link in links.values()):
        return now
    times = [deadline] if deadline else []
    times += [clients[k].opens for k in waiting] if free else []
    for link in links.values():
        c = link.client
        times += [t for t in (c.reset, c.shut) if t is not None]
        if link.unsent:
            times.append(link.ready)
        elif link.asked():
            times += [at for at, _ in c.sends]
    return min((t for t in times if t > now), default=None)


def ascii_lines(*lines: str) -> bytes:
    return b"".join(line.encode() + b"\r\n" for line in lines)


CASES = ("CAPABILITIES", "capabilities foo", "CAPABILITIES 1x", "CAPABILITIES ab", "CAPABILITIES a@b",
         "CAPABILITIES a[b", "CAPABILITIES a`b", "CAPABILITIES a{b", "CAPABILITIES @ab", "CAPABILITIES [ab",
         "CAPABILITIES `ab", "CAPABILITIES {ab", "CAPABILITIES a-.9", "HELP", "hElP",
         "HELP x", "QUIT x", "\tHEAD\t", "HEAD", "HEAD 0", "HEAD 05", "HEAD 2147483647", "HEAD 2147483648",
         "HEAD 99999999999999999999", "HEAD 00000000000000001", "HEAD +5", "HEAD -1", "HEAD 12abc",
         "HEAD <a@b>", "HEAD <a b>", "HEAD <>", "HEAD <a>b>", "HEAD <a@b> extra", "HEAD <" + "a" * 248 + ">",
         "HEAD <" + "a" * 249 + ">", "HEAD <\x7f>", "HEAD <~!>", "STAT", "STAT 1",
         "STAT <x@y>", "STAT z", "MODE", "MODE STREAM", "mode reader x", "MODE READ", "MODE READERS", "XY",
         "LIST", "", "  \t ")
TRANSCRIPT = ascii_lines("CAPABILITIES", "help", "", "HEAD <a@b>", "STAT 12abc", "QUIT", "HELP")
HELP = ascii_lines("HELP")
Scenario = tuple[str, list[Client], bool, Identity]


def letters_changed(lines: list[tuple[str, str, str]]) -> bytes:
    """Each line `before` + keyword + `after` once for each letter of its keyword, that letter changed
    to the next one, so that a keyword compared without some letter would answer it."""
    changed = []
    for before, keyword, after in lines:
        for k, c in enumerate(keyword):
            other = chr((ord(c) - 65 + 1) % 26 + 65)
            changed.append(before + keyword[:k] + other + keyword[k + 1:] + after)
    return ascii_lines(*changed)


# The keywords of a server without a store, each in a line that would be answered were it read.
KEYWORDS = [("", "CAPABILITIES", ""), ("", "HELP", ""), ("", "HEAD", ""), ("", "STAT", ""), ("", "MODE", " READER"),
            ("MODE ", "READER", ""), ("", "QUIT", "")]
# …and those a store adds.
STORE_KEYWORDS = [*KEYWORDS[:-1], ("", "POST", ""), ("", "ARTICLE", ""), ("", "BODY", ""),
                  ("", "GROUP", " local.test"), ("", "NEXT", ""), ("", "LAST", ""), ("", "LISTGROUP", ""),
                  ("", "LIST", ""),
                  ("LIST ", "ACTIVE", ""), ("LIST ", "NEWSGROUPS", ""), ("", "DATE", ""),
                  ("", "NEWGROUPS", " 20260101 000000"), ("NEWGROUPS 20260101 000000 ", "GMT", ""),
                  ("", "OVER", ""), ("", "HDR", " Subject"), ("", "XOVER", ""), ("", "XHDR", " Subject"),
                  ("LIST ", "OVERVIEW.FMT", ""), ("LIST ", "HEADERS", ""), ("LIST HEADERS ", "MSGID", ""),
                  ("LIST HEADERS ", "RANGE", ""), ("HDR :", "BYTES", ""), ("HDR :", "LINES", ""), KEYWORDS[-1]]


DRAWN, DRAWN_SEED = 300, 20261002
PIECES = (b"HELP\r\n", b"HEL", b"P\r\n", b"HE", b"  ", b"\t", b"\r\n", b"\r", b"\n", b"STAT 1\r\n",
          b"QUIT\r\n", b"FOO" + b"x" * 600 + b"\r\n")
GAPS = (0, 1, 2, 10_000, 179_999, 180_000, 180_001, 1_800_000)


def drawn() -> Iterator[Client]:
    """Clients drawn at random, the same on every run: pieces of lines sent after gaps that land on
    and around the deadlines, now and then reading slowly, pausing, ending their input or reset."""
    rng = random.Random(DRAWN_SEED)  # noqa: S311 -- a fixed seed, so that every run draws the same clients
    for _ in range(DRAWN):
        at = rng.choice((1, 5))
        sends = []
        for _ in range(rng.randint(1, 6)):
            at += rng.choice(GAPS)
            sends.append((at, b"".join(rng.choice(PIECES) for _ in range(rng.randint(1, 3)))))
        client = Client(1, sends)
        if rng.random() < 0.2:
            client.take, client.slow, client.pace = rng.choice((1, 7, 60)), 5, rng.choice((1, 1_000))
        if rng.random() < 0.1:
            client.pause = (at, at + rng.choice(GAPS[3:]))
        if rng.random() < 0.15:
            client.shut = at + rng.choice(GAPS)
        elif rng.random() < 0.05:
            client.reset = at + rng.choice(GAPS)
        yield client


def scenarios() -> Iterator[Scenario]:
    for name, clients, ghosts in plain_scenarios():
        yield name, clients, ghosts, IDENTITY
    for k, client in enumerate(drawn()):
        yield f"drawn client {k} of seed {DRAWN_SEED}", [client], False, IDENTITY
    commands = [Client(1, [(5, ascii_lines(*CASES, "QUIT"))])]
    pipeline = [Client(1, [(5, ascii_lines(*["HELP", "CAPABILITIES"] * 20, "QUIT"))], take=100)]
    for label, identity in (("the longest", LONGEST), ("the shortest", SHORTEST)):
        yield f"commands with {label} identity", commands, False, identity
        yield f"a long pipeline with {label} identity", pipeline, False, identity


def plain_scenarios() -> Iterator[tuple[str, list[Client], bool]]:
    yield "commands", [Client(1, [(5, ascii_lines(*CASES, "QUIT"))])], False
    for at in range(1, len(TRANSCRIPT)):
        yield f"cut at {at}", [Client(1, [(5, TRANSCRIPT[:at]), (9, TRANSCRIPT[at:])])], False
    yield "a byte at a time", [Client(1, [(5 + k, TRANSCRIPT[k:k + 1]) for k in range(len(TRANSCRIPT))])], False
    for take in (1, 7, 60):
        yield f"a reader taking {take}", [Client(1, [(5, TRANSCRIPT)], take=take)], False
    yield "a reader that waits", [Client(1, [(5, TRANSCRIPT)], pause=(0, 5_000))], False
    yield "a long pipeline", [Client(1, [(5, ascii_lines(*["HELP", "STAT 1"] * 40, "QUIT"))], take=100)], False
    odd = (b"\n", b" \t\n", b"HELP\n", b"HELP\0\r\n", b"HE\rLP\r\n", b"FOO\n", b"\0\r\n",
           b"HELP " + b"x" * 600 + b"\r\n", b"FOO" + b"x" * 600 + b"\r\n", b" " * 700 + b"\r\n",
           b"HEAD " + b"1" * 505 + b"\r\n", b"HEAD " + b"1" * 506 + b"\r\n", b"QUIT\r\n")
    yield "odd lines", [Client(1, [(5, b"".join(odd))])], False
    yield "a QUIT and more", [Client(1, [(5, ascii_lines("QUIT", "HELP")), (9, HELP)])], False
    yield "MODE READER without a store", [Client(1, [(5, ascii_lines("HELP", "mode Reader", "HELP")), (9, HELP)])], \
        False
    yield "every letter of a keyword changed", [Client(1, [(5, letters_changed(KEYWORDS) + QUIT)])], False
    yield "input ending mid-line", [Client(1, [(5, b"HELP\r\nCAPAB")], shut=9)], False
    yield "input ending at once", [Client(1, [], shut=3)], False
    yield "input ending after commands", [Client(1, [(5, ascii_lines("HELP", "STAT"))], shut=5, take=9)], False
    yield "input ending with a line begun and output untaken", [
        Client(1, [(5, b"HELP\r\nHE")], shut=6, take=10, slow=5, pace=60_000)], False
    yield "no first command", [Client(1)], False
    yield "a clock of zero", [Client(0, [(0, ascii_lines("HELP", "HELP"))])], False
    yield "only empty lines", [Client(1, [(5 + 1_000 * k, b"\r\n") for k in range(15)])], False
    yield "a first command just in time", [Client(1, [(10_000, ascii_lines("HELP", "QUIT"))])], False
    yield "a first command too late", [Client(1, [(10_001, HELP)])], False
    yield "silence after a command", [Client(1, [(5, HELP)])], False
    yield "empty lines after a command", [
        Client(1, [(5, HELP)] + [(60_000 * k, b"\r\n") for k in range(1, 40)])], False
    yield "a command just before the inactivity deadline", [Client(1, [(5, HELP), (1_800_004, HELP)])], False
    yield "a command at the inactivity deadline", [Client(1, [(5, HELP), (1_800_005, HELP)])], False
    yield "a reader slower than the inactivity deadline", [
        Client(1, [(5, HELP)], take=10, slow=5, pace=600_000)], False
    yield "a reader that stops reading", [Client(1, [(5, HELP)], pause=(5, 10 ** 9))], False
    yield "a reader reported ready that takes nothing", [
        Client(1, [(5, HELP)], take=10, slow=5, pace=600_000, pause=(10, 10 ** 9), false_ready=True)], False
    yield "an unfinished line", [Client(1, [(5, b"HELP\r\nHEL")])], False
    yield "a line finished just in time", [Client(1, [(5, HELP), (10, b"HEL"), (180_009, b"P\r\n")])], False
    yield "a line finished too late", [Client(1, [(5, HELP), (10, b"HEL"), (180_010, b"P\r\n")])], False
    yield "a line a byte a minute", [Client(1, [(5, HELP)] + [(6 + 60_000 * k, b"H") for k in range(5)])], False
    yield "a line answered and the next begun in one batch", [
        Client(1, [(5, HELP), (10, b"HEL"), (11, b"P\r\nHE")])], False
    yield "a white-space line and the next begun in one batch", [
        Client(1, [(5, HELP), (10, b"  "), (11, b"\r\nHE")])], False
    yield "an empty line and the next begun in one batch", [
        Client(1, [(5, HELP), (10, b"\r"), (11, b"\nHE")])], False
    yield "a line begun while output is untaken", [
        Client(1, [(5, b"HELP\r\nHE")], take=10, slow=5, pace=60_000)], False
    yield "a reset", [Client(1, [(5, HELP)], reset=6, take=10)], False
    yield "a crowd", [Client(1 + k % 3, [(5, ascii_lines("HELP", "QUIT"))], take=None if k % 2 else 50)
                      for k in range(70)], False
    yield "seventy clients holding sixty-four connections", [Client(1, [(5, HELP)]) for _ in range(70)], False
    yield "events of connections gone", [
        Client(1 + k, [(5 + k, ascii_lines("HELP", "QUIT"))], reset=7 if k % 3 == 0 else None, take=30)
        for k in range(12)] + [Client(20 + k, [(30, HELP)]) for k in range(12)], True
    yield "a slow reader among busy ones", [Client(1, [(5, HELP)], take=5, slow=5, pace=1_000)] + [
        Client(1, [(5 + 7 * k, HELP) for k in range(30)]) for _ in range(3)], False


class Articles:
    """scripts/article_ref.py as a process, answering a header section at a time: the judge's
    checker (`post_ref.Checker`)."""

    def __init__(self) -> None:
        python = str(lanes.pinned_python(REQUIREMENTS))
        self.proc = subprocess.Popen([python, str(ARTICLES), "--each"], stdin=subprocess.PIPE,
                                     stdout=subprocess.PIPE, text=True, bufsize=1)

    def __enter__(self) -> Self:
        return self

    def __exit__(self, *_: object) -> None:
        if self.proc.stdin:
            self.proc.stdin.close()
        self.proc.wait(timeout=TIMEOUT)
        if self.proc.stdout:
            self.proc.stdout.close()

    def __call__(self, wall: int, seq: int, run: int, conn: int, identity: bytes, random: bytes,
                 groups: list[bytes], header: bytes) -> P.Verdict:
        if self.proc.stdin is None or self.proc.stdout is None:
            raise LaneError("the article reference has no pipe")
        listed = ",".join(g.hex() for g in groups) or "-"
        self.proc.stdin.write(f"check {wall} {seq} {run} {conn} {identity.hex()} {random.hex()} {listed} "
                              f"{header.hex()}\n")
        self.proc.stdin.flush()
        match self.proc.stdout.readline().split():
            case ["refused", *_]:
                return None
            case ["accepted", stored, message_id, carried]:
                return (bytes.fromhex(stored), bytes.fromhex(message_id),
                        [] if carried == "-" else [bytes.fromhex(g) for g in carried.split(",")])
            case words:
                raise LaneError(f"the article reference answered {words}")


def article(*fields: str, body: tuple[str, ...] = ("text",)) -> bytes:
    """An article as a client sends it: its lines dot-stuffed, then the terminator. Its body names no
    command, so that an article refused before its 340, read as lines, asks for nothing."""
    return b"".join(((b"." if line.startswith(".") else b"") + line.encode() + b"\r\n")
                    for line in (*fields, "", *body)) + b".\r\n"


BASIC = ("From: a@b.example", "Newsgroups: local.test", "Subject: hi")
GROUPS = [b"local.test", b"local.other"]
QUIT = ascii_lines("QUIT")


ARTICLE_MAX = P.ARTICLE_MAX


def chunks(total: int, most: int, least: int) -> list[int]:
    """`total` cut into pieces of at most `most` and at least `least`."""
    out = []
    while total > 0:
        take = min(most, total)
        if 0 < total - take < least:
            take -= least
        out.append(take)
        total -= take
    return out


def sized(n: int) -> bytes:
    """An article of `n` octets as sent, its terminator counted: lines of `y` after the header."""
    head = article(*BASIC, body=())[:-3]
    body = b"".join(b"y" * (k - 2) + b"\r\n" for k in chunks(n - len(head) - 3, 900, 2))
    return head + body + b".\r\n"


def header_sized(n: int) -> bytes:
    """An article whose header section is of `n` octets, CRLFs counted: X-Pad fields after the
    others."""
    used = sum(len(f) + 2 for f in BASIC)
    pads = ["X-Pad: " + "p" * (k - 9) for k in chunks(n - used, 900, 10)]
    return article(*BASIC, *pads)


def poster(at: int = 5, sent: bytes = article(*BASIC), after: bytes = QUIT, **more: Any) -> Client:
    """A client that posts at `at`, sends the article a moment later, then `after`."""
    return Client(1, [(at, ascii_lines("POST")), (at + 1, sent), (at + 2, after)], post=True, **more)


PostScenario = tuple[str, list[Client], Spool]


def post_scenarios() -> Iterator[PostScenario]:
    yield "a post", [poster()], Spool(GROUPS)
    yield "a post with lines that start with a dot", [
        poster(sent=article(*BASIC, body=(".x", "..y", ".", "...", "")))], Spool(GROUPS)
    yield "a post refused", [poster(sent=article("Newsgroups: local.test", "Subject: hi"))], Spool(GROUPS)
    yield "the capabilities and help, then a post", [
        Client(1, [(5, ascii_lines("CAPABILITIES", "HELP", "POST")), (6, article(*BASIC)), (7, QUIT)],
               post=True)], Spool(GROUPS)
    yield "a client that may not post", [Client(1, [(5, ascii_lines("CAPABILITIES", "POST", "QUIT"))])], Spool(GROUPS)
    yield "a store with no group", [poster()], Spool([])
    yield "an article sent with its POST", [
        Client(1, [(5, ascii_lines("POST") + article(*BASIC) + QUIT)], post=True)], Spool(GROUPS)
    yield "an article, then commands in the same send", [
        Client(1, [(5, ascii_lines("POST")), (6, article(*BASIC) + ascii_lines("HELP", "QUIT"))], post=True)], \
        Spool(GROUPS)
    yield "two posts on one connection", [
        Client(1, [(5, ascii_lines("POST")), (6, article(*BASIC)), (7, ascii_lines("POST")), (8, article(*BASIC)),
                   (9, QUIT)], post=True)], Spool(GROUPS)
    yield "five posts at once", [poster() for _ in range(5)], Spool(GROUPS, delays={"syncdir": 20_000})
    yield "a post waiting longer than a first command may", [poster() for _ in range(4)] + [
        Client(1, [(6, ascii_lines("POST")), (7, article(*BASIC)), (8, QUIT)], post=True)], \
        Spool(GROUPS, delays={"create": 30_000})
    same = article(*BASIC, "Message-ID: <same@x.example>")
    yield "one Message-ID twice at once", [poster(sent=same), poster(sent=same)], \
        Spool(GROUPS, delays={"create": 1_000})
    yield "one Message-ID after another", [poster(sent=same), poster(at=100, sent=same)], Spool(GROUPS)
    lines = tuple(f"line {k} " + "x" * 60 for k in range(700))
    big = article(*BASIC, body=lines)
    yield "a big article", [poster(sent=big)], Spool(GROUPS, delays={"write": 1_000})
    yield "a big article read slowly", [Client(1, [(5, ascii_lines("POST")), *((6 + k, big[k * 400:(k + 1) * 400])
                                                    for k in range(len(big) // 400 + 1)), (999, QUIT)], post=True)], \
        Spool(GROUPS, delays={"write": 3})
    yield "an article of the most octets", [poster(sent=sized(ARTICLE_MAX))], Spool(GROUPS)
    yield "an article one octet longer", [poster(sent=sized(ARTICLE_MAX + 1))], Spool(GROUPS)
    yield "a header section of the most octets", [poster(sent=header_sized(P.HEADER_MAX))], Spool(GROUPS)
    yield "a header section one octet longer", [poster(sent=header_sized(P.HEADER_MAX + 1))], Spool(GROUPS)
    after = [Client(1, [(200, ascii_lines("CAPABILITIES", "POST")), (201, article(*BASIC)), (202, QUIT)],
                    post=True), Client(150, [(200, ascii_lines("CAPABILITIES", "POST", "QUIT"))], post=True)]
    for kind, partial in (("create", 0), ("create", 1), ("write", 0), ("write", 100), ("datasync", 0), ("close", 0),
                          ("rename", 0), ("rename", 1), ("syncdir", 0), ("journal-write", 0),
                          ("journal-write", 40), ("journal-sync", 0)):
        yield f"a {kind} that fails, leaving {partial}", [poster(sent=big), *after], \
            Spool(GROUPS, failures=[Failure(kind, partial=partial)])
    yield "a removal that fails", [poster(sent=big)], \
        Spool(GROUPS, failures=[Failure("write"), Failure("remove")])
    yield "posts to groups with articles", [
        poster(sent=article("From: a@b.example", "Newsgroups: local.other,local.test,local.none", "Subject: s"))], \
        Spool(GROUPS, image=spool_with([[(b"local.test", 1)], [(b"local.test", 2), (b"local.other", 7)]]))
    yield "two articles placed at once", [poster(), poster()], \
        Spool(GROUPS, delays={"syncdir": 5_000, "journal-sync": 20_000})
    half = article(*BASIC)[:30]
    yield "an article not finished", [Client(1, [(5, ascii_lines("POST")), (6, half)], post=True)], Spool(GROUPS)
    yield "an article sent a line every ten minutes", [
        Client(1, [(5, ascii_lines("POST")), *((6 + 600_000 * k, line + b"\r\n")
                                               for k, line in enumerate(article(*BASIC).split(b"\r\n")[:-1]))],
               post=True)], Spool(GROUPS)
    yield "input ending inside an article", [Client(1, [(5, ascii_lines("POST")), (6, big[:20_000])], post=True,
                                                    shut=7)], Spool(GROUPS, delays={"write": 100})
    yield "a reset inside an article", [Client(1, [(5, ascii_lines("POST")), (6, big[:20_000])], post=True,
                                               reset=50)], Spool(GROUPS, delays={"write": 100})
    yield "a reset while the store commits", [poster(after=b"", reset=8)], \
        Spool(GROUPS, delays={"journal-sync": 100})
    yield "an article with no empty line", [poster(sent=b"".join(f.encode() + b"\r\n" for f in BASIC) + b".\r\n")], \
        Spool(GROUPS)
    yield "a line answered and the next begun in one batch, with a store", [
        Client(1, [(5, HELP), (10, b"HEL"), (11, b"P\r\nHE")], post=True)], Spool(GROUPS)
    yield "an article, then the start of a line", [
        Client(1, [(5, ascii_lines("POST")), (6, article(*BASIC) + b"QU"), (20, b"IT\r\n")], post=True)], Spool(GROUPS)
    yield "a close that fails while names are removed", [poster(sent=big)], \
        Spool(GROUPS, failures=[Failure("write"), Failure("close")])
    yield "a store at its capacity", [poster(), poster(at=100)], \
        Spool(GROUPS, image=spool_with([[(b"local.test", k)] for k in range(1, 4096)]))
    named = article(*BASIC, "Message-ID: <again@x.example>")
    yield "a Message-ID free again once its article is refused", [
        poster(sent=article(*BASIC, "Message-ID: <again@x.example>", body=lines)), poster(at=20, sent=named)], \
        Spool(GROUPS, failures=[Failure("write")], delays={"remove": 5_000})
    slow_big = [(6 + k, big[k * 4_000:(k + 1) * 4_000]) for k in range(len(big) // 4_000 + 1)]
    yield "the store stopping with another article in flight", [
        poster(), Client(1, [(5, ascii_lines("POST")), *slow_big, (999, QUIT)], post=True)], \
        Spool(GROUPS, failures=[Failure("datasync")])
    yield "a commit completing after the store stopped", [poster(), poster(at=1_000)], \
        Spool(GROUPS, delays={"journal-sync": 10_000}, failures=[Failure("datasync", nth=2)])
    yield "the store stopping while a POST waits", [poster() for _ in range(5)], \
        Spool(GROUPS, delays={"syncdir": 20_000}, failures=[Failure("datasync")])
    holders = [Client(1, [(5, ascii_lines("POST")), (8 if k == 0 else 400_000, article(*BASIC)),
                          (400_001, QUIT)], post=True) for k in range(4)]
    yield "POSTs waiting in the order they came", [
        *holders, Client(1, [(7, ascii_lines("POST")), (8, article(*BASIC)), (9, QUIT)], post=True),
        Client(1, [(6, ascii_lines("POST")), (8, article(*BASIC)), (9, QUIT)], post=True)], Spool(GROUPS)


SMALL = stored(b"body", b"..dot")
BIG = stored(*(b"line %d " % k + b"y" * 60 for k in range(600)))
ID1, ID2 = "<1@old.example>", "<2@old.example>"
TWO = spool_holding([(SMALL, [(b"local.test", 1)]), (BIG, [(b"local.test", 2), (b"local.other", 7)])])


def reader(*lines: str, at: int = 5, **more: Any) -> Client:
    """A client that sends the lines and QUIT at `at`."""
    return Client(1, [(at, ascii_lines(*lines, "QUIT"))], **more)


def read_scenarios() -> Iterator[PostScenario]:
    yield "reads of the spool's articles", [
        reader(f"ARTICLE {ID1}", f"HEAD {ID2}", f"BODY {ID1}", f"STAT {ID2}", "ARTICLE <none@x.example>",
               "STAT <none@x.example>", "BODY 3", "ARTICLE", "HELP")], Spool(GROUPS, image=TWO)
    yield "a big article sent to a slow reader", [reader(f"ARTICLE {ID2}", f"BODY {ID2}", take=300, slow=5)], \
        Spool(GROUPS, image=TWO)
    yield "a command after a read", [
        Client(1, [(5, ascii_lines(f"ARTICLE {ID2}")), (2_000, QUIT)], take=300, slow=5)], Spool(GROUPS, image=TWO)
    posted = article(*BASIC, "Message-ID: <read@x.example>")
    yield "an article read after it is posted", [
        Client(1, [(5, ascii_lines("POST")), (6, posted),
                   (50, ascii_lines("ARTICLE <read@x.example>", "HEAD <read@x.example>", "STAT <read@x.example>",
                                    "QUIT"))], post=True)], Spool(GROUPS)
    yield "an article asked for while it is posted", [
        poster(sent=posted), Client(1, [(7, ascii_lines("STAT <read@x.example>", "ARTICLE <read@x.example>")),
                                        (20_000, ascii_lines("ARTICLE <read@x.example>", "QUIT"))])], \
        Spool(GROUPS, delays={"journal-sync": 10_000})
    yield "nine readers at once", [reader(f"ARTICLE {ID2}", take=200, slow=5) for _ in range(9)], \
        Spool(GROUPS, image=TWO)
    yield "readers waiting in the order they came", [
        reader(f"ARTICLE {ID1}", take=5, slow=5), *(reader(f"ARTICLE {ID2}", take=100, slow=5) for _ in range(7)),
        reader(f"ARTICLE {ID1}", at=7), reader(f"HEAD {ID2}", at=6)], Spool(GROUPS, image=TWO)
    yield "a file whose CRC-32C is not its commit's", [reader(f"ARTICLE {ID1}", f"HEAD {ID2}")], \
        Spool(GROUPS, image=spool_holding([(SMALL, [(b"local.test", 1)]), (BIG, [(b"local.test", 2)])],
                                          wrong_crc=(1,)))
    yield "a file with a bare LF", [reader(f"BODY {ID1}")], \
        Spool(GROUPS, image=spool_holding([(stored(b"one\nline", b"two"), [(b"local.test", 1)])]))
    yield "a file with a line that starts with one dot", [reader(f"BODY {ID1}")], \
        Spool(GROUPS, image=spool_holding([(stored(b"one", b".two"), [(b"local.test", 1)])]))
    yield "a big file whose CRC-32C is not its commit's", [reader(f"ARTICLE {ID1}")], \
        Spool(GROUPS, image=spool_holding([(BIG, [(b"local.test", 1)])], wrong_crc=(1,)))
    first = recovery_ref.name_of("a", 1)
    yield "a file grown after the start", [reader(f"ARTICLE {ID1}")], \
        Spool(GROUPS, image=TWO, tamper=[(first, SMALL + b"x\r\n")])
    yield "a file cut after the start", [reader(f"ARTICLE {ID1}")], \
        Spool(GROUPS, image=TWO, tamper=[(first, SMALL[:-3])])
    yield "an open that fails", [reader(f"ARTICLE {ID1}", f"HEAD {ID1}")], \
        Spool(GROUPS, image=TWO, failures=[Failure("open")])
    yield "a read that fails after a first", [reader(f"ARTICLE {ID2}")], \
        Spool(GROUPS, image=TWO, failures=[Failure("read", nth=2)])
    yield "a reset during a read", [reader(f"ARTICLE {ID2}", take=100, slow=5, reset=40)], Spool(GROUPS, image=TWO)
    yield "a reader that stops during a read", [reader(f"ARTICLE {ID2}", take=100, slow=5, pause=(30, 10 ** 9))], \
        Spool(GROUPS, image=TWO)
    yield "reads slower than the inactivity deadline", [reader(f"ARTICLE {ID2}")], \
        Spool(GROUPS, image=TWO, delays={"read": 2_000_000})
    long_groups = [b"local." + bytes([97 + k]) * 58 for k in range(16)]
    yield "an Xref folded", [reader(f"HEAD {ID1}", f"ARTICLE {ID1}")], \
        Spool(long_groups, image=spool_holding([(SMALL, [(g, 1) for g in long_groups])]))
    for width, last in ((998, 41), (999, 42)):
        groups = [*long_groups[:14], b"x" * last]
        yield f"an Xref line of {width} octets", [reader(f"HEAD {ID1}")], \
            Spool(groups, image=spool_holding([(SMALL, [(g, 1) for g in groups])]))
    for size in (16_383, 32_767):
        yield f"a header section ending a read past {size + 1:,} octets", [reader(f"ARTICLE {ID1}", f"HEAD {ID1}")], \
            Spool(GROUPS, image=spool_holding([(stored_header(size), [(b"local.test", 1)])]))
    yield "reads once the store has stopped", [poster(), Client(1, [(500, ascii_lines(f"ARTICLE {ID1}", "QUIT"))])], \
        Spool(GROUPS, image=TWO, failures=[Failure("datasync")])
    yield "commands sent with an ARTICLE", [
        Client(1, [(5, ascii_lines(f"ARTICLE {ID1}", "HELP", f"STAT {ID1}", "QUIT"))])], Spool(GROUPS, image=TWO)
    yield "a line begun behind an ARTICLE", [
        Client(1, [(5, ascii_lines(f"ARTICLE {ID1}") + b"HEL"), (900_000, b"P\r\nQUIT\r\n")])], Spool(GROUPS, image=TWO)
    for size in (16_384, 32_768):
        exact = spool_holding([(stored_of(size), [(b"local.test", 1)])])
        yield f"a file of {size:,} octets", [reader(f"ARTICLE {ID1}", f"HEAD {ID1}")], Spool(GROUPS, image=exact)
        yield f"a file of {size:,} octets grown after the start", [reader(f"ARTICLE {ID1}")], \
            Spool(GROUPS, image=exact, tamper=[(first, stored_of(size) + b"z")])
    yield "a header section not where its commit says", [reader(f"HEAD {ID1}")], \
        Spool(GROUPS, image=spool_holding([(SMALL, [(b"local.test", 1)])], header_off=2))
    yield "posts while reads are in flight", [
        *(poster(at=100) for _ in range(4)), *(reader(f"ARTICLE {ID2}", take=500, slow=5) for _ in range(8))], \
        Spool(GROUPS, image=TWO, delays={"read": 1_000, "create": 500}, failures=[Failure("datasync")])
    yield "a reader reset while it waits", [
        *(reader(f"ARTICLE {ID2}", take=200, slow=5) for _ in range(8)), reader(f"ARTICLE {ID1}", at=6, reset=30)], \
        Spool(GROUPS, image=TWO)


# A spool of articles in three groups, one of them empty: numbers with a hole, and two crossposts.
READER_GROUPS = [b"local.test", b"local.other", b"local.empty"]
READER_SPOOL = spool_holding([(stored(b"one"), [(b"local.test", 1)]),
                              (stored(b"two"), [(b"local.test", 2), (b"local.other", 5)]),
                              (stored(b"four"), [(b"local.test", 4)]),
                              (stored(b"six"), [(b"local.other", 6), (b"local.test", 6)])])


def odd_words() -> list[bytes]:
    """`a` and each octet a word may hold, then `a` and UTF-8 cut at its edges: each lead octet near a
    bound, a second octet near one, and none to two continuation octets."""
    octets = [b for b in range(1, 256) if b not in (9, 10, 13, 32)]
    leads = (0xC1, 0xC2, 0xDF, 0xE0, 0xE1, 0xEC, 0xED, 0xEE, 0xEF, 0xF0, 0xF1, 0xF3, 0xF4, 0xF5)
    edges = (0x7F, 0x80, 0x8F, 0x90, 0x9F, 0xA0, 0xBF, 0xC0)
    return [b"a" + bytes([b]) for b in octets] + [b"a" + bytes([lead, edge]) + b"\x80" * k
                                                  for lead in leads for edge in edges for k in range(3)]


def group_scenarios() -> Iterator[PostScenario]:
    yield "a group's articles walked", [
        reader("GROUP local.test", "ARTICLE", "STAT", "NEXT", "NEXT", "NEXT", "NEXT", "LAST", "STAT 3", "STAT",
               "ARTICLE 4", "HEAD", "BODY 2", "LAST", "LAST", "STAT 0005", "STAT <3@old.example>", "STAT", "STAT 2",
               "NEXT", "STAT 4",
               "GROUP local.test", "STAT", "GROUP local.other", "ARTICLE", "NEXT", "HEAD 2147483647")], \
        Spool(READER_GROUPS, image=READER_SPOOL)
    yield "no group selected, and an unknown one", [
        reader("STAT 1", "ARTICLE", "NEXT", "LAST", "HEAD 2", "BODY", "GROUP local.none", "STAT", "GROUP local.test",
               "STAT 2", "GROUP local.none", "STAT", "NEXT", "ARTICLE <1@old.example>", "STAT")], \
        Spool(READER_GROUPS, image=READER_SPOOL)
    yield "an empty group", [
        reader("GROUP local.test", "STAT 2", "GROUP local.empty", "STAT", "NEXT", "LAST", "ARTICLE 1", "HEAD",
               "GROUP local.other", "STAT")], Spool(READER_GROUPS, image=READER_SPOOL)
    names = (b"GROUP", b"GROUP a b", b"GROUP local*", b"GROUP local.test,local.other", b"GROUP LOCAL.TEST",
             b"group local.test", b"GROUP local.\xc3\xa9t\xc3\xa9", b"GROUP local.\xc3", b"GROUP local.\xed\xa0\x80",
             b"GROUP local.\xe2\x82\xac", b"GROUP " + b"a" * 65, b"GROUP !local", b"NEXT 1", b"LAST x",
             b"STAT 2147483648", b"STAT 2147483647", b"QUIT")
    yield "group names and arguments", [Client(1, [(5, b"".join(line + b"\r\n" for line in names))])], \
        Spool(READER_GROUPS, image=READER_SPOOL)
    yield "every octet in a group's name", [Client(1, [(5, b"".join(b"GROUP " + name + b"\r\n" for name in odd_words())
                                                       + b"QUIT\r\n")])], Spool(READER_GROUPS)
    yield "a group with no article at all", [reader("GROUP local.test", "STAT", "NEXT", "ARTICLE 1")], \
        Spool(READER_GROUPS)
    posted = article(*BASIC, "Message-ID: <new@x.example>")
    yield "a group as an article is posted to it", [
        Client(1, [(5, ascii_lines("GROUP local.test", "STAT 6", "NEXT")),
                   (3_000, ascii_lines("NEXT", "STAT", "GROUP local.test", "LAST", "QUIT"))]),
        poster(at=10, sent=posted)], Spool(READER_GROUPS, image=READER_SPOOL)
    yield "an empty group an article is posted to", [
        Client(1, [(5, ascii_lines("GROUP local.empty", "next")),
                   (3_000, ascii_lines("next", "stat", "group local.empty", "last", "QUIT"))]),
        poster(at=10, sent=article("From: a@b.example", "Newsgroups: local.empty", "Subject: hi"))], \
        Spool(READER_GROUPS, image=READER_SPOOL)
    longest = b"local." + b"g" * 58
    sent = b"GROUP " + longest + b"\r\nGROUP " + longest + b"g\r\nQUIT\r\n"
    yield "names of 64 and 65 octets", [Client(1, [(5, sent)])], Spool([longest, longest[:-1]])
    yield "an article by number that cannot be read", [
        reader("GROUP local.test", "ARTICLE 4", "STAT", "HEAD 2", "STAT")], \
        Spool(READER_GROUPS, image=READER_SPOOL, failures=[Failure("open")])
    yield "groups of two readers apart", [
        reader("GROUP local.other", "NEXT", "ARTICLE"), reader("GROUP local.test", "STAT 4", "BODY", at=6)], \
        Spool(READER_GROUPS, image=READER_SPOOL)


# A group of articles 1 to 200, and forty groups of names of 60 octets.
BIG_SPOOL = spool_holding([(stored(b"n"), [(b"local.big", k)]) for k in range(1, 201)])
MANY_GROUPS = [b"local.%s%02d" % (b"g" * 52, k) for k in range(40)]
# As many groups as a store may carry.
ALL_GROUPS = [b"local.g%02d" % k for k in range(64)]
# Wall clocks at the calendar's edges: a year's last second, a leap day of a fourth century, the end
# of a February a century has without one and the next day, the end of a leap day of a fourth century
# past the epoch's era, and seconds into an hour fewer than its number.
CALENDAR = (946_684_799_999, 951_782_400_000, 4_107_542_399_999, 4_107_542_400_000, 13_574_649_599_000,
            1_792_846_805_000)


def list_scenarios() -> Iterator[PostScenario]:
    yield "a group's articles listed", [
        reader("GROUP local.other", "LISTGROUP local.test", "STAT", "NEXT", "LISTGROUP", "STAT",
               "LISTGROUP local.test 2-4", "LISTGROUP local.test 4", "LISTGROUP local.test 5-",
               "LISTGROUP local.test 6-2", "LISTGROUP local.test 3", "LISTGROUP local.test 0-2147483647",
               "LISTGROUP local.empty", "STAT",
               "LISTGROUP local.none", "STAT", "LISTGROUP LOCAL.TEST", "listgroup local.other 6-6", "STAT")], \
        Spool(READER_GROUPS, image=READER_SPOOL)
    yield "LISTGROUP with no group selected", [
        reader("LISTGROUP", "STAT", "LISTGROUP local.none", "LISTGROUP local.test 2", "STAT", "LISTGROUP", "STAT")], \
        Spool(READER_GROUPS, image=READER_SPOOL)
    yield "the groups listed", [
        reader("LIST", "LIST ACTIVE", "list active", "LIST Active local.*", "LIST ACTIVE local.*,!local.empty",
               "LIST ACTIVE *.test,*.other", "LIST ACTIVE local.?????", "LIST ACTIVE *,!*.t*,local.te*",
               "LIST ACTIVE local.x", "LIST ACTIVE local.test*", "LIST ACTIVE *local.test", "LIST ACTIVE local.*test",
               "LIST ACTIVE local.te", "LIST ACTIVE ocal.test", "LIST ACTIVE LOCAL.*", "LIST ACTIVE local.TEST",
               "LIST NEWSGROUPS", "LIST newsgroups local.*", "STAT")], \
        Spool(READER_GROUPS, image=READER_SPOOL)
    lines = (b"LIST ACTIVE !local.test", b"LIST NEWSGROUPS !local.test", b"LIST ACTIVE a,,b", b"LIST ACTIVE a,",
             b"LIST ACTIVE a,!", b"LIST ACTIVE [a]", b"LIST ACTIVE a\\b", b"LIST ACTIVE l\xc3", b"LIST ACTIVE.TIMES",
             b"LIST ACTIVE a b", b"LIST 1x", b"LISTGROUP a*", b"LISTGROUP local.test -3",
             b"LISTGROUP local.test 3-7-9", b"LISTGROUP local.test 2147483648", b"LISTGROUP local.test 1 2",
             b"LISTGROUP " + b"a" * 65 + b" 1", b"DATE x", b"QUIT")
    yield "arguments of the listings", [Client(1, [(5, b"".join(line + b"\r\n" for line in lines))])], \
        Spool(READER_GROUPS, image=READER_SPOOL)
    yield "dates", [
        reader("DATE", "date", "NEWGROUPS 19990624 000000 GMT", "newgroups 990624 235960 gmt",
               "NEWGROUPS 20261024 120000", "NEWGROUPS 20261324 000000", "NEWGROUPS 20261032 000000",
               "NEWGROUPS 20261000 000000",
               "NEWGROUPS 18991231 000000", "NEWGROUPS 20261024 240000", "NEWGROUPS 20261024 126000",
               "NEWGROUPS 20261024 120061", "NEWGROUPS 20261024 120000 UTC", "NEWGROUPS 2026102 120000",
               "NEWGROUPS 20261024 120000 GMT x", "NEWGROUPS 20261024")], Spool(READER_GROUPS)
    yield "DATE past the year 9999", [reader("DATE")], Spool(READER_GROUPS, wall=WALL_LIMIT - 10 ** 7)
    yield "DATE of fields of one digit", [reader("DATE")], Spool(READER_GROUPS, wall=946_782_245_000 - 5)
    yield "DATE at the calendar's edges", [Client(at - 10, [(at, ascii_lines("DATE", "QUIT"))]) for at in CALENDAR], \
        Spool(READER_GROUPS, wall=0)
    yield "long listings to a slow reader", [
        reader("LISTGROUP local.big 98-200", "LISTGROUP local.big", "LIST ACTIVE", "LISTGROUP local.big 150",
               "LISTGROUP local.big 1-122", "LISTGROUP local.big 1-123", "LISTGROUP local.big 1-124",
               "LISTGROUP local.big 1-125", take=40, slow=5)], Spool([b"local.big"], image=BIG_SPOOL)
    yield "forty groups listed to a slow reader as the store stops", [
        reader("LIST ACTIVE", "LIST ACTIVE *1,*3", take=30, slow=5),
        poster(at=10, sent=article("From: a@b.example", f"Newsgroups: {MANY_GROUPS[0].decode()}", "Subject: hi"))], \
        Spool(MANY_GROUPS, failures=[Failure("datasync")])
    yield "sixty-four groups listed", [
        reader("LIST ACTIVE", "LIST ACTIVE *3", "LIST ACTIVE local.g6?,!*0", "LISTGROUP local.g63", "GROUP local.g00",
               take=60, slow=5)], Spool(ALL_GROUPS)
    yield "a listing to a reader that pauses", [
        Client(1, [(5, ascii_lines("LISTGROUP local.big", "QUIT"))], pause=(6, 3_000_000))], \
        Spool([b"local.big"], image=BIG_SPOOL, late=200_000)
    yield "every octet in a wildmat", [
        Client(1, [(5, b"".join(b"LIST ACTIVE " + w + b"\r\n" for w in odd_words()) + b"QUIT\r\n")])], \
        Spool(READER_GROUPS)
    yield "a line begun behind a listing, the host late", [
        Client(1, [(5, ascii_lines("LISTGROUP local.big") + b"HEL")])], \
        Spool([b"local.big"], image=BIG_SPOOL, late=200_000)
    yield "listings with nothing sent after them", [
        Client(1, [(5, ascii_lines("LISTGROUP local.big")), (100_000, ascii_lines("LIST ACTIVE")),
                   (200_000, QUIT)])], Spool([b"local.big"], image=BIG_SPOOL)
    yield "a group listed as an article is posted to it", [
        reader("LISTGROUP local.big", "LISTGROUP local.big 199-", take=20, slow=5),
        poster(at=10, sent=article("From: a@b.example", "Newsgroups: local.big", "Subject: hi"))], \
        Spool([b"local.big"], image=BIG_SPOOL)
    yield "the groups listed once the store has stopped", [
        poster(), Client(1, [(500, ascii_lines("LIST ACTIVE", "LIST", "QUIT"))])], \
        Spool(GROUPS, image=TWO, failures=[Failure("datasync")])
    yield "every letter of a keyword changed, with a store", [
        Client(1, [(5, letters_changed(STORE_KEYWORDS) + QUIT)], post=True)], Spool(READER_GROUPS, image=READER_SPOOL)
    yield "every octet in a range", [Client(1, [(5, range_octets())])], Spool(READER_GROUPS, image=READER_SPOOL)
    yield "every octet in an article's number", [Client(1, [(5, number_octets())])], \
        Spool(READER_GROUPS, image=READER_SPOOL)
    yield "commands and keywords a store does not have", [
        reader("IHAVE <a@b.example>", "NEWNEWS * 20260101 000000", "LIST ACTIVE.TIMES", "LIST DISTRIB.PATS",
               "MODE STREAM")], Spool(READER_GROUPS, image=READER_SPOOL)
    yield "marks of two digits and three", [
        reader("LIST ACTIVE", "GROUP local.test", "LISTGROUP local.other", "LIST ACTIVE local.o*", "STAT 12", "LAST",
               "NEXT", "NEXT", "GROUP local.ten", "GROUP local.nine")], \
        Spool([b"local.test", b"local.other", b"local.nine", b"local.ten"], image=MARKS_SPOOL)


# Each octet a line may hold inside a word, and the article numbers at the most one may be and past it.
OCTETS = [bytes([b]) for b in range(256) if b not in (9, 10, 13, 32)]
LIMITS = (2_147_483_646, 2_147_483_647, 2_147_483_648)


def range_octets() -> bytes:
    """LISTGROUP of `local.test` with each octet a word may hold at each place of a range: a number, its
    start, its end; then numbers at the most an article number may be and past it, alone, as a start
    and as an end."""
    forms = (b"%s", b"1%s", b"%s-", b"1%s-", b"1-%s", b"1-2%s")
    lines = [b"LISTGROUP local.test " + form % o for form in forms for o in OCTETS]
    lines += [b"LISTGROUP local.test " + form % n for form in (b"%d", b"%d-", b"1-%d") for n in LIMITS]
    return b"".join(line + b"\r\n" for line in lines) + QUIT


def number_octets() -> bytes:
    """With `local.test` selected, STAT of each octet a word may hold as a number and after a digit;
    then ARTICLE, HEAD, BODY and STAT of the numbers at the most an article number may be and past it."""
    lines = [b"GROUP local.test", *(b"STAT " + form % o for form in (b"%s", b"1%s") for o in OCTETS),
             *(b"%s %d" % (cmd, n) for cmd in (b"ARTICLE", b"HEAD", b"BODY", b"STAT") for n in LIMITS)]
    return b"".join(line + b"\r\n" for line in lines) + QUIT


# Groups whose lowest numbers have two digits and three, and whose numbers are 9 and 99, 10 and 100.
MARKS_SPOOL = spool_holding([(stored(b"n"), [(b"local.test", 12)]),
                             (stored(b"m"), [(b"local.test", 13), (b"local.other", 130)]),
                             (stored(b"o"), [(b"local.other", 131)]), (stored(b"p"), [(b"local.nine", 9)]),
                             (stored(b"q"), [(b"local.nine", 99), (b"local.ten", 10)]),
                             (stored(b"r"), [(b"local.ten", 100)])])


def mode_scenarios() -> Iterator[PostScenario]:
    yield "MODE READER of a client that may post", [
        Client(1, [(5, ascii_lines("MODE READER", "CAPABILITIES", "mode reader", "QUIT"))], post=True)], Spool(GROUPS)
    yield "MODE READER of a client that may not post", [
        Client(1, [(5, ascii_lines("CAPABILITIES", "MODE READER", "POST", "QUIT"))])], Spool(GROUPS)
    yield "MODE READER keeps the selected group", [
        reader("GROUP local.test", "NEXT", "MODE READER", "STAT", "NEXT", "LISTGROUP local.other", "MODE READER",
               "STAT", "LAST")], Spool(READER_GROUPS, image=READER_SPOOL)
    yield "MODE READER once the store has stopped", [
        poster(), Client(1, [(500, ascii_lines("MODE READER", "CAPABILITIES", "QUIT"))], post=True)], \
        Spool(GROUPS, image=TWO, failures=[Failure("datasync")])
    yield "MODE READER and its arguments", [
        reader("MODE", "MODE STREAM", "MODE READER x", "MODE  READER", "\tmode\treader\t", "MODEREADER", "MODE READ",
               "MODE READERS")], \
        Spool(GROUPS)
    yield "MODE READER of a store with no group", [
        Client(1, [(5, ascii_lines("MODE READER", "CAPABILITIES", "QUIT"))], post=True)], Spool([])


# Articles whose fields test what OVER and HDR take of them: a Subject folded with a TAB, two Keywords, a
# field with a TAB and one that starts with a dot, lines of the body that start with dots; a Subject
# named in lower case and no Date; a crosspost; and holes among the numbers.
RICH = (b"From: a@b.example\r\nSubject: one\r\n\ttwo\r\nDate: Mon, 26 Oct 2026 10:00:00 +0000\r\n"
        b"Message-ID: <1@old.example>\r\nRef: no\r\nReferences: <0@old.example> <00@old.example>\r\nKeywords: x\r\n"
        b"Keywords: y\r\nX-Tab: a\tb\r\n..odd: dot\r\nXref-Like: z\r\nX-Fold:\r\n folded\r\nX-Tabfold:\r\n\tx\r\n"
        b"\r\nbody\r\n..dot line\r\n..\r\nlast\r\n")
LOWER = b"from: c@d.example\r\nsubject:  two spaces\r\nReferences:\r\n\r\nshort\r\n"
OVER_GROUPS = [b"local.test", b"local.other", b"local.empty"]
OVER_SPOOL = spool_holding([(RICH, [(b"local.test", 1), (b"local.other", 3)]), (LOWER, [(b"local.test", 2)]),
                            (BIG, [(b"local.test", 4)]), (stored(b"five"), [(b"local.test", 6), (b"local.other", 4)])])


def over_scenarios() -> Iterator[PostScenario]:
    # First, so that a range taking articles the store takes after the line is answered is caught here.
    yield "overview while an article is posted to its group", [
        reader("GROUP local.test", "OVER 1-", take=100, slow=5), poster(at=6)], Spool(OVER_GROUPS, image=OVER_SPOOL)
    yield "overview of a group", [
        reader("OVER", "XOVER", "XHDR Path", "HDR Subject", "HDR :x-foo", "GROUP local.test", "OVER", "OVER 1-",
               "XOVER 1-2",
               "over 2-4", "OVER 3", "OVER 5-5", "OVER 7-", "XOVER 7-", "OVER 4-2", "XOVER 4-2", "STAT",
               "LIST OVERVIEW.FMT", "LIST HEADERS", "list headers range", "LIST HEADERS MSGID", "GROUP local.empty",
               "OVER", "XOVER", "HDR Subject", "XHDR Subject", "OVER 1-")], Spool(OVER_GROUPS, image=OVER_SPOOL)
    yield "overview by message-id", [
        reader(f"OVER {ID1}", f"HDR Subject {ID1}", f"XHDR Subject {ID1}", f"XHDR Date {ID2}", f"HDR Date {ID2}",
               "OVER <none@x.example>", "HDR Subject <none@x.example>", "XHDR Subject <none@x.example>",
               "GROUP local.test", f"OVER {ID1}", f"HDR :bytes {ID2}", "STAT")], Spool(OVER_GROUPS, image=OVER_SPOOL)
    yield "fields of a range", [
        reader("GROUP local.test", "HDR Subject 1-", "XHDR Subject 1-", "HDR subject 2", "HDR Date 1-", "XHDR Date 1-",
               "HDR Keywords 1", "HDR X-Tab 1", "HDR .odd 1", "HDR Xref 1-", "HDR :BYTES 1-", "HDR :lines 1-",
               "HDR Message-ID 1-", "HDR References 1-2", "HDR Xref-Like 1", "XHDR References 2", "HDR Nothing 1-",
               "XHDR Date 2-", "XHDR Nothing 1-", "HDR X-Fold 1", "HDR X-Tabfold 1",
               "HDR :x-foo 1", "HDR :x-foo", "HDR a:b 1", "HDR : 1", "HDR", "XHDR", "XOVER <1@old.example>",
               "OVER 1 2", "LIST OVERVIEW.FMT x", "LIST HEADERS x", "GROUP local.other", "XHDR Subject 3-4",
               "OVER 1-", "XOVER 1-3")], Spool(OVER_GROUPS, image=OVER_SPOOL)
    yield "overview of a big group to a slow reader", [reader("GROUP local.big", "XOVER 1-", take=300, slow=5)], \
        Spool([b"local.big"], image=BIG_SPOOL)
    yield "overview while others read", [
        reader("GROUP local.test", "OVER 1-", take=100, slow=5), *(reader(f"ARTICLE {ID1}", take=50, slow=5)
                                                                   for _ in range(7)),
        reader("GROUP local.test", "HDR Subject 1-", at=6), reader(f"BODY {ID2}", at=7)], \
        Spool(OVER_GROUPS, image=OVER_SPOOL)
    yield "overview reset while it is read", [reader("GROUP local.test", "OVER 1-", take=100, slow=5, reset=30)], \
        Spool(OVER_GROUPS, image=OVER_SPOOL)
    yield "overview of a file that fails its check first", [reader("GROUP local.test", "OVER 1-2", "HDR Subject 1")], \
        Spool(OVER_GROUPS, image=spool_holding([(RICH, [(b"local.test", 1)]), (LOWER, [(b"local.test", 2)])],
                                               wrong_crc=(1,)))
    yield "overview of a file that fails its check later", [reader("GROUP local.test", "OVER 1-2")], \
        Spool(OVER_GROUPS, image=spool_holding([(RICH, [(b"local.test", 1)]), (LOWER, [(b"local.test", 2)])],
                                               wrong_crc=(2,)))
    yield "overview of header sections at the buffer and past it", [
        reader("GROUP local.test", "HDR :lines 1", "OVER 2", "OVER 1-2")], \
        Spool(OVER_GROUPS, image=spool_holding([(stored_header(69_632), [(b"local.test", 1)]),
                                                (stored_header(69_633), [(b"local.test", 2)])]))
    long_groups = [b"local." + bytes([97 + k]) * 58 for k in range(16)]
    yield "overview of a folded Xref", [reader("GROUP " + long_groups[0].decode(), "OVER", "HDR Xref", "HDR :bytes")], \
        Spool(long_groups, image=spool_holding([(SMALL, [(g, 1) for g in long_groups])]))
    yield "overview once the store has stopped", [
        poster(), Client(1, [(500, ascii_lines("GROUP local.test", "OVER 1-", "QUIT"))])], \
        Spool(GROUPS, image=TWO, failures=[Failure("datasync")])


def read_breaches() -> Iterator[tuple[str, list[str], int]]:
    """Scripts with a store in which a host reports a read, or a file opened at a place still in use,
    as it may not: code 14."""
    old = Spool(GROUPS, image=TWO)
    asked = [old.line(), f"turn 1 {WALL + 1}", "open 0 1", "go", f"took {GREETING}", f"turn 5 {WALL + 5}",
             "recv 0 1 " + ascii_lines(f"ARTICLE {ID1}").hex(), "go", "took 0", f"turn 6 {WALL + 6}"]
    opened = [*asked, "complete 0 8 1 2:0", "go", "took", f"turn 7 {WALL + 7}"]
    more = SMALL + b"xx"
    yield "a read of more octets than it asked", [*opened, f"complete 0 9 2 {len(more)}:0,0:0 {more.hex()}", "go"], 14
    yield "octets a read does not count", [*opened, f"complete 0 9 2 3:0,0:0 {SMALL[:4].hex()}", "go"], 14
    yield "a file opened at the journal's place", [*asked, "complete 0 8 1 1:0", "go"], 14
    yield "a file opened at a place past the table", [*asked, f"complete 0 8 1 {P.PLACES}:0", "go"], 14
    both = ascii_lines(f"ARTICLE {ID1}").hex()
    yield "a file opened at another read's place", [
        old.line(), f"turn 1 {WALL + 1}", "open 0 1", "open 1 1", "go", f"took {GREETING} {GREETING}",
        f"turn 5 {WALL + 5}", f"recv 0 1 {both}", f"recv 1 1 {both}", "go", "took 0 0", f"turn 6 {WALL + 6}",
        "complete 0 8 1 2:0", "complete 1 9 1 2:0", "go"], 14
    spool = Spool(GROUPS)
    greeting = len(ref.texts(*IDENTITY)["greeting-post"])
    yield "a file created at the journal's place", [
        spool.line(), f"turn 1 {WALL + 1}", "open 0 1 1", "go", f"took {greeting}", f"turn 5 {WALL + 5}",
        "recv 0 1 " + ascii_lines("POST").hex(), "go", "took 31", f"turn 6 {WALL + 6}",
        "recv 0 1 " + article(*BASIC).hex(), "go", "took 0", f"turn 7 {WALL + 7}", "complete 0 8 1 1:0", "go"], 14


def breaches() -> Iterator[tuple[str, list[str], int]]:
    """Scripts a host breaks the contract in, and the code the session has to stop with."""
    begin = ["turn 1", "open 0 1", "go", f"took {GREETING}"]
    yield "more events than a batch", ["turn 1", *[f"open {k} 1" for k in range(17)], "go"], 1
    yield "more bytes than a chunk", [*begin, "turn 2", "recv 0 1 " + "41" * 513, "go"], 2
    yield "an index past the table", ["turn 1", "open 64 1", "go"], 3
    yield "input before the greeting was taken", ["turn 1", "open 0 1", "go", "took 0", "turn 2",
                                                  "recv 0 1 41", "go"], 4
    yield "two inputs in one batch", [*begin, "turn 2", "recv 0 1 41", "recv 0 1 41", "go"], 4
    yield "bytes and the end of input in one batch", [*begin, "turn 2", "recv 0 1 41", "end 0 1", "go"], 4
    yield "more taken than sent", ["turn 1", "open 0 1", "go", f"took {GREETING + 1}"], 5
    yield "a count for no send", ["turn 1", "go", "took 1"], 5
    yield "an index opened twice", [*begin, "turn 2", "open 0 2", "go"], 6
    yield "a clock going back", ["turn 5", "go", "took", "turn 4", "go"], 7
    yield "a clock past its limit", [f"turn {2 ** 62}", "go"], 7
    yield "a wall clock past its limit", [f"turn 1 {WALL_LIMIT}", "go"], 7


def post_breaches() -> Iterator[tuple[str, list[str], int]]:
    """Scripts with a store in which a host reports a completion it may not, and the code of the
    breach: 13 for one of no job in flight, 14 for one the job cannot have."""
    spool = Spool(GROUPS)
    greeting = len(ref.texts(*IDENTITY)["greeting-post"])
    posted = [spool.line(), f"turn 1 {WALL + 1}", "open 0 1 1", "go", f"took {greeting}",
              f"turn 5 {WALL + 5}", "recv 0 1 " + ascii_lines("POST").hex(), "go", "took 31",
              f"turn 6 {WALL + 6}", "recv 0 1 " + article(*BASIC).hex(), "go", "took 0", f"turn 7 {WALL + 7}"]
    yield "a completion with no store", ["turn 1", "complete 0 1 0 -", "go"], 13
    yield "a completion of no job", [spool.line(), f"turn 1 {WALL}", "complete 0 1 0 -", "go"], 13
    yield "a completion of another generation", [*posted, "complete 0 9 1 2:0", "go"], 13
    yield "more completions than jobs", [spool.line(), f"turn 1 {WALL}",
                                         *(f"complete {k} 1 0 -" for k in range(P.JOBS + 1)), "go"], 14
    yield "more operations done than the job has", [*posted, "complete 0 8 2 2:0,0:0", "go"], 14
    yield "results for operations not done", [*posted, "complete 0 8 0 2:0", "go"], 14
    yield "a file at a place past the table", [*posted, "complete 0 8 1 16:0", "go"], 14


def breach_output(script: list[str], command: list[str], identity: Identity = IDENTITY) -> tuple[list[str], str]:
    """What a session answers to a whole script, which it may stop reading before its end, and
    how it ended if not well."""
    with Speaker(command, identity) as session:
        stdin = session.pipe(session.proc.stdin)
        try:
            stdin.write("".join(line + "\n" for line in script))
            stdin.close()
        except OSError:
            pass
        out = session.output()
        status = session.ended()
        return out, f" and ended with status {status}{session.why()}" if status else ""


def check_breach(script: list[str], code: int, command: list[str], identity: Identity = IDENTITY) -> list[str]:
    """The session's answers to a script that breaks the contract, which have to end with the code."""
    out, ended = breach_output(script, command, identity)
    if ended or out[-1:] != [f"stop {code}"]:
        raise LaneError(f"the session answered {out[-3:]}{ended}, not stop {code}")
    return out


def sends(trace: list[Turn]) -> list[tuple[Turn, int, int]]:
    """Each send of a trace: its turn, its place among the turn's actions, and among its sends."""
    found = []
    for t in trace:
        places = [k for k, a in enumerate(t.actions) if a.kind == "send"]
        found += [(t, k, n) for n, k in enumerate(places)]
    return found


def replies(trace: list[Turn]) -> list[tuple[Turn, int, int]]:
    return [(t, k, n) for t, k, n in sends(trace) if t.actions[k].data[:3].isdigit()]


def swap_replies(trace: list[Turn]) -> None:
    (t1, k1, n1), (t2, k2, n2) = next((a, b) for a, b in itertools.pairwise(replies(trace)[1:])
                                      if a[0].actions[a[1]].data != b[0].actions[b[1]].data)
    a1, a2 = t1.actions[k1], t2.actions[k2]
    t1.actions[k1], t2.actions[k2] = a1._replace(data=a2.data), a2._replace(data=a1.data)
    t1.took[n1], t2.took[n2] = len(a2.data), len(a1.data)


def double_reply(trace: list[Turn]) -> None:
    t, k, n = replies(trace)[1]
    a = t.actions[k]
    t.actions[k] = a._replace(data=a.data * 2)
    t.took[n] = len(a.data) * 2


def change_byte(trace: list[Turn]) -> None:
    t, k, _ = replies(trace)[2]
    a = t.actions[k]
    t.actions[k] = a._replace(data=a.data[:-3] + b"X" + a.data[-2:])


def read_early(trace: list[Turn]) -> None:
    t, k, _ = next(s for s in replies(trace) if not s[0].actions[s[1]].read)
    t.actions[k] = t.actions[k]._replace(read=True)


def answer_before_taken(trace: list[Turn]) -> None:
    t, k, _ = next(s for s in sends(trace) if s[0].actions[s[1]].data and not s[0].actions[s[1]].data[:3].isdigit())
    later = next(s for s in replies(trace) if s[0].now > t.now)
    t.actions[k] = t.actions[k]._replace(data=later[0].actions[later[1]].data)


def resend_early(trace: list[Turn]) -> None:
    for t, u in itertools.pairwise(trace):
        for _, k, n in sends([t]):
            a = t.actions[k]
            quiet = not any(e.idx == a.idx for e in u.events) and not any(b.idx == a.idx for b in u.actions)
            if t.took[n] < len(a.data) and quiet:
                u.actions.append(a._replace(data=a.data[t.took[n]:]))
                u.took.append(0)
                return
    raise LaneError("no connection left waiting for the host to plant a defect on")


def close_early(trace: list[Turn]) -> None:
    t = trace[1]
    t.actions = [Action("close", t.actions[0].idx, t.actions[0].gen)]
    t.took = []


def no_close(trace: list[Turn]) -> None:
    t = next(t for t in trace if any(a.kind == "close" for a in t.actions))
    t.actions = [a for a in t.actions if a.kind != "close"]


def graceful_early(trace: list[Turn]) -> None:
    t = next(t for t in trace if any(e.kind == "recv" for e in t.events))
    t.actions = [Action("graceful", t.actions[0].idx, t.actions[0].gen)]
    t.took = []


def graceful_untaken(trace: list[Turn]) -> None:
    t, _, n = next(s for s in sends(trace) if s[0].actions[s[1]].data == b"205 Bye\r\n")
    t.took[n] = 3
    t.deadline = t.now + ref.INACTIVITY


def late_turn(trace: list[Turn]) -> None:
    t = next(t for t in trace if t.deadline == t.now)
    t.deadline = t.now + 1


def early_turn(trace: list[Turn]) -> None:
    t = next(t for t in trace if t.deadline > t.now + 1)
    t.deadline -= 1


def no_greeting(trace: list[Turn]) -> None:
    t = trace[0]
    t.actions, t.took = [], []


def stranger(trace: list[Turn]) -> None:
    trace[1].actions.append(Action("send", 9, 1, b"", True))
    trace[1].took.append(0)


# Defects planted in a recorded trace: (name, scenario, the kind of violation, the change).
Plant = Callable[[list[Turn]], None]
PLANTS: list[tuple[str, str, str, Plant]] = [
    ("replies out of order", "commands", "order", swap_replies),
    ("a reply twice in one send", "commands", "whole", double_reply),
    ("a byte of a reply changed", "commands", "order", change_byte),
    ("reading with a line unanswered", "a long pipeline", "read", read_early),
    ("a reply before the last was taken", "a reader taking 7", "untaken", answer_before_taken),
    ("output sent again before the host reported it ready", "a slow reader among busy ones", "unready",
     resend_early),
    ("a close with no deadline passed", "commands", "close", close_early),
    ("no close at a deadline", "no first command", "missed", no_close),
    ("a graceful close with lines unanswered", "input ending mid-line", "graceful-unanswered", graceful_early),
    ("a graceful close before the 205 was taken", "a QUIT and more", "graceful-untaken", graceful_untaken),
    ("the next turn late", "a long pipeline", "turn", late_turn),
    ("the next turn early", "silence after a command", "turn", early_turn),
    ("no greeting", "commands", "greeting", no_greeting),
    ("an action for a connection not open", "commands", "stranger", stranger),
]


def changed_write(trace: list[Turn]) -> None:
    """A byte of an article's file changed as it is written."""
    for t in trace:
        for k, (slot, gen, ops) in enumerate(t.jobs):
            for i, op in enumerate(ops):
                if op.kind == "write" and op.place != 1:
                    data = op.data[:-1] + bytes([op.data[-1] ^ 1])
                    t.jobs[k] = (slot, gen, [*ops[:i], op._replace(data=data), *ops[i + 1:]])
                    return
    raise LaneError("no write of an article to plant a defect on")


def changed_commit(trace: list[Turn]) -> None:
    """An article number changed in a commit appended."""
    for t in trace:
        for k, (slot, gen, ops) in enumerate(t.jobs):
            if ops[0].kind == "write" and ops[0].place == 1:
                data = bytearray(ops[0].data)
                data[-14] ^= 1
                t.jobs[k] = (slot, gen, [ops[0]._replace(data=bytes(data)), *ops[1:]])
                return
    raise LaneError("no commit to plant a defect on")


def posted_refused(trace: list[Turn]) -> None:
    """A refused article answered 240."""
    t, k, _ = next(s for s in sends(trace) if s[0].actions[s[1]].data.startswith(b"441"))
    t.actions[k] = t.actions[k]._replace(data=b"240 Article received OK\r\n")


def changed_read(trace: list[Turn]) -> None:
    """An octet of an article changed as it is sent."""
    t, k, _ = next(s for s in sends(trace) if s[0].actions[s[1]].data.startswith(b"220"))
    data = t.actions[k].data
    t.actions[k] = t.actions[k]._replace(data=data[:-6] + b"X" + data[-5:])


def unreadable_sent(trace: list[Turn]) -> None:
    """A file that fails its check sent all the same."""
    t, k, n = next(s for s in sends(trace) if s[0].actions[s[1]].data.startswith(b"403"))
    sent = b"220 0 <1@old.example>\r\n" + SMALL + b".\r\n"
    t.actions[k] = t.actions[k]._replace(data=sent)
    t.took[n] = len(sent)


def changed_part(trace: list[Turn]) -> None:
    """A number in a part of a listing after its first line changed."""
    for t in trace:
        for k, a in enumerate(t.actions):
            if a.kind == "send" and a.data.split(b"\r\n", 1)[0].isdigit():
                t.actions[k] = a._replace(data=b"9" + a.data[1:])
                return
    raise LaneError("no part of a listing to plant a defect on")


def read_moved(trace: list[Turn]) -> None:
    """A read of the second octets of a file asked one octet further on."""
    for t in trace:
        for k, (slot, gen, ops) in enumerate(t.jobs):
            if ops[0].kind == "read" and ops[0].offset:
                t.jobs[k] = (slot, gen, [ops[0]._replace(offset=ops[0].offset + 1), *ops[1:]])
                return
    raise LaneError("no read on to plant a defect on")


POST_PLANTS: list[tuple[str, str, str, Plant]] = [
    ("an article's octets changed in a write", "a post", "write", changed_write),
    ("an article number changed in a commit", "posts to groups with articles", "journal", changed_commit),
    ("a refused article answered 240", "a post refused", "outcome", posted_refused),
    ("an article's octets changed as they are sent", "reads of the spool's articles", "read-out", changed_read),
    ("a file that fails its check sent", "a file whose CRC-32C is not its commit's", "unreadable", unreadable_sent),
    ("a read asked past where the last ended", "a big article sent to a slow reader", "read", read_moved),
    ("a number of a listing changed", "a group's articles listed", "listing-out", changed_part),
]


Played = Iterator[tuple[str, list[Turn], Identity, Spool | None]]


def played(mutant: str, all_scenarios: list[Scenario]) -> Played:
    """The scenarios with `mutant` broken, each as far as the broken session gets."""
    for name, clients, ghosts, identity in all_scenarios:
        try:
            trace = run(clients, model_command(mutant), ghosts, identity)
        except Unfinished as error:
            trace = error.trace
        yield name, trace, identity, None


def played_post(mutant: str, posts: list[PostScenario]) -> Played:
    for name, clients, spool in posts:
        try:
            trace = run_post(clients, spool, model_command(mutant))
        except Unfinished as error:
            trace = error.trace
        yield name, trace, IDENTITY, spool


def caught(mutant: str, all_scenarios: list[Scenario], posts: list[PostScenario], checker: Articles) -> str:
    """The first scenario on which the judge refuses the session with `mutant` broken, those with a
    store first for a rule of POST, those that read, select a group or list first for a rule of
    theirs; a scenario the broken session cannot finish is judged on the turns it had."""
    if mutant in READ_MUTANTS:
        reads = {name for name, _, _ in read_scenarios()}
        posts = sorted(posts, key=lambda p: p[0] not in reads)
    if mutant in GROUP_MUTANTS:
        selects = {name for name, _, _ in group_scenarios()}
        posts = sorted(posts, key=lambda p: p[0] not in selects)
    if mutant in LIST_MUTANTS:
        lists = {name for name, _, _ in list_scenarios()}
        posts = sorted(posts, key=lambda p: p[0] not in lists)
    if mutant in MODE_MUTANTS:
        modes = {name for name, _, _ in mode_scenarios()}
        posts = sorted(posts, key=lambda p: p[0] not in modes)
    if mutant in VIEW_MUTANTS:
        views = {name for name, _, _ in over_scenarios()}
        posts = sorted(posts, key=lambda p: p[0] not in views)
    plain, stored = played(mutant, all_scenarios), played_post(mutant, posts)
    order = itertools.chain(stored, plain) if MUTANTS.index(mutant) >= 15 else itertools.chain(plain, stored)
    for name, trace, identity, spool in order:
        try:
            ref.judge(*identity, trace, spool.start() if spool else None, checker if spool else None)
        except Violation as error:
            return f"{name}: {error}"
    raise LaneError(f"the judge accepted the session with {mutant} on every scenario")


def caught_apart(mutant: str, all_scenarios: list[Scenario], posts: list[PostScenario]) -> str:
    """`caught`, with an article reference of its own, so that mutants can be run at once."""
    with Articles() as checker:
        return caught(mutant, all_scenarios, posts, checker)


@contextlib.contextmanager
def runs() -> Iterator[ThreadPoolExecutor]:
    """A pool for runs of the session, as many at once as this process may use cores; a refusal is
    told at once, the runs waiting behind it dropped."""
    pool = ThreadPoolExecutor(len(os.sched_getaffinity(0)))
    try:
        yield pool
    finally:
        pool.shutdown(cancel_futures=True)


def check() -> Report:
    all_scenarios = list(scenarios())
    broken = [*breaches(), *post_breaches(), *read_breaches()]
    posts = [*post_scenarios(), *read_scenarios(), *group_scenarios(), *list_scenarios(), *mode_scenarios(),
             *over_scenarios()]
    turns = 0
    traces = {}
    post_traces = {}
    # The model runs as a process for each scenario, in parallel, each judged in order; then the
    # mutants, once the model passed.
    with runs() as pool, Articles() as checker:
        plain = [pool.submit(run, clients, model_command(), ghosts, identity)
                 for _, clients, ghosts, identity in all_scenarios]
        answered = [pool.submit(check_breach, script, code, model_command()) for _, script, code in broken]
        stored = [pool.submit(run_post, clients, spool, model_command()) for _, clients, spool in posts]
        for (name, _, _, identity), played in zip(all_scenarios, plain, strict=True):
            trace = played.result()
            try:
                ref.judge(*identity, trace)
            except Violation as error:
                raise LaneError(f"scenario {name!r}: {error}") from None
            traces[name] = trace
            turns += len(trace)
        for (name, _, _), answer in zip(broken, answered, strict=True):
            try:
                answer.result()
            except LaneError as error:
                raise LaneError(f"breach {name!r}: {error}") from None
        for (name, _, spool), played in zip(posts, stored, strict=True):
            trace = played.result()
            try:
                ref.judge(REVISION, SOURCE, trace, spool.start(), checker)
            except Violation as error:
                raise LaneError(f"scenario {name!r}: {error}") from None
            post_traces[name] = trace
        caught = [pool.submit(caught_apart, m, all_scenarios, posts) for m in MUTANTS]
        mutants = {m: found.result() for m, found in zip(MUTANTS, caught, strict=True)}
        planted = {}
        spools = {name: given for name, _, given in posts}
        for name, scenario, kind, plant in PLANTS + POST_PLANTS:
            trace = copy.deepcopy(traces.get(scenario) or post_traces[scenario])
            plant(trace)
            on = spools.get(scenario) if scenario not in traces else None
            try:
                ref.judge(REVISION, SOURCE, trace, on.start() if on else None, checker if on else None)
            except Violation as error:
                if error.kind != kind:
                    raise LaneError(f"the planted {name!r} was caught as {error.kind}, not {kind}: {error}") from None
                planted[name] = str(error)
                continue
            raise LaneError(f"the planted {name!r} was not caught")
    post_turns = sum(len(t) for t in post_traces.values())
    lanes.require_quoted({"docs/baseline.md": [f"{len(traces)} scenarios and {turns:,} turns",
                                               f"{len(post_traces)} with a store and {post_turns:,} turns"]})
    return Report("checked", None, [ARTICLES, REQUIREMENTS], {
        "scenarios": len(traces), "turns": turns, "store_scenarios": len(post_traces), "store_turns": post_turns,
        "breaches": len(broken), "mutants_caught": mutants,
        "planted_defects_caught": planted})


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.parse_args()
    lanes.lane_main("SESSION MODEL", lanes.ROOT / "build/session-model", check)


if __name__ == "__main__":
    main()
