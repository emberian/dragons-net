#!/usr/bin/env python3
# SPDX-License-Identifier: AGPL-3.0-or-later
"""The runs lane: the store's program (`DN.News.StoreOps`, its start `DN.News.RecoveryRun`) run by
`dn-compiler store-model` on scenarios, and every point of each run held to what a crash may leave
there, the way ALICE (Pillai et al., OSDI 2014) and ShardStore (Bornholt et al., SOSP 2021) check
storage systems, with tools written apart from the model:

- the operations each event makes are done again on scripts/fs_ref.py, which has to end where the
  model says, and which draws, after each, directories a crash may leave;
- recovery of each, by scripts/recovery_ref.py, has to find no corruption and keep what decision
  0005 promises (`store_safe`): every article answered 240, and only articles whose commit was
  appended for an article not refused, each with the octets written for it and their CRC-32C; what
  was answered, appended and refused the lane reads from its own scenario, not from the model;
- once a start is done, the directory is what recovery_ref's actions and a start record make;
- the process ends now and then and the store starts again on the file system as it is, a start's
  operation failing now and then; and runs start again on directories a crash left, what was done
  by then carried over;
- events the program may not make are refused where it may not, for each thing `Cmd.allowed`
  checks; a store as full as it may be takes no commit, and one an article short does, which no
  drawn run reaches;
- the program broken in each of the nine ways `regression_923` sets out, and by a commit of another
  CRC-32C, is caught by drawn scenarios, each at least three times, a scenario counting for 240
  before the journal's sync when it has a commit, and for the others only when the break makes an
  event the program may not make.

A scenario is drawn by a reading of 0005's program kept here: what it may do next, and what each
event does to what it keeps (docs/baseline.md, "Store runs").
"""
from __future__ import annotations

from collections.abc import Callable
import copy
from dataclasses import dataclass, field, replace
from functools import partial
from pathlib import Path
import random
import sys
import time

sys.path.insert(0, str(Path(__file__).resolve().parent))
import abnf_check as C  # the path above is what makes these importable
import fs_ref as F
import lanes
from lanes import LaneError, Report
import recovery_ref as R
import store_ref as J

OUT = lanes.ROOT / "build/runs"
SEED = 20261005
KEY = bytes(range(16))
GROUPS = [b"local.test", b"local.more"]
# How many chains of runs are drawn, and how many directories a crash may leave are drawn at a point.
CHAINS = 120
PER_POINT = 4
# How many times each way of breaking the program has to be caught.
CAUGHT = 3

Commit = tuple[int, bytes, list[tuple[bytes, int]], int, int, int]
NO_COMMIT: Commit = (0, b"", [], 0, 0, 0)


@dataclass
class Post:
    """An article in flight: its octets, how many are written, and where it is."""
    octets: bytes
    written: int = 0
    stage: str = "reserved"


@dataclass
class Prog:
    """What the program keeps: the run, the next sequence number, the last article number the
    records synced gave each group, the articles in flight, the commit appended and not yet synced,
    whether it still accepts articles and still trusts syncs of the journal and the directory, and how
    many commits the records synced hold."""
    run: int
    next: int
    highest: dict[bytes, int]
    posts: dict[int, Post] = field(default_factory=dict)
    committing: Commit | None = None
    accepting: bool = True
    trusting: bool = True
    held: int = 0


@dataclass
class History:
    """What the runs have done that a crash must not undo: the commits answered 240, those appended
    with their run, the articles refused by run and number, and the octets of each number."""
    answered: list[Commit] = field(default_factory=list)
    appended: list[tuple[int, Commit]] = field(default_factory=list)
    refused: set[tuple[int, int]] = field(default_factory=set)
    files: dict[int, bytes] = field(default_factory=dict)


@dataclass(frozen=True)
class Event:
    """What the program does next — the octets it reserves, how many it writes, the commit it
    appends, the name it cleans (1 the final one) — and the outcome its operation fails with, if it
    does; or, as `restart`, the process ending and a start on the file system as it is, its `N`-th
    operation failing with the `K`-th outcome if `start` says so."""
    kind: str
    q: int = 0
    octets: bytes = b""
    m: int = 0
    commit: Commit = NO_COMMIT
    final: int = 0
    fails: int | None = None
    start: tuple[int, int] | None = None

    def text(self) -> str:
        match self.kind:
            case "reserve":
                body = f"reserve:{F.hexed(self.octets)}"
            case "write":
                body = f"write:{self.q}:{self.m}"
            case "commit":
                seq, mid, groups, header, size, crc = self.commit
                listed = ",".join(f"{F.hexed(n)}={k}" for n, k in groups) or "-"
                body = f"commit:{self.q}:{seq}:{F.hexed(mid)}:{listed}:{header}:{size}:{crc}"
            case "clean":
                body = f"clean:{self.q}:{self.final}"
            case "publish":
                body = "publish"
            case "restart":
                return "restart" if self.start is None else f"restart:{self.start[0]}:{self.start[1]}"
            case _:
                body = f"{self.kind}:{self.q}"
        return body if self.fails is None else f"{body}!{self.fails}"


def frame_length(c: Commit) -> int:
    return J.HEADER + len(J.payload(c)) + 1


def allowed(p: Prog, groups: list[bytes], e: Event) -> bool:
    """Whether the program may make the event: each phase of 0005's after the one before, a commit
    only for a file in place, one record at a time, while accepting and the store has room, numbered
    above the group's last."""
    post = p.posts.get(e.q)
    stage = None if post is None else post.stage
    match e.kind:
        case "reserve":
            return p.next + 2 < 2**64
        case "create":
            return stage == "reserved"
        case "write":
            return stage == "writing"
        case "sync":
            return stage == "writing" and post is not None and post.written == len(post.octets)
        case "rename":
            return stage == "synced"
        case "place":
            return stage == "final" and p.trusting
        case "commit":
            if stage != "placed" or post is None or p.committing is not None or not p.accepting:
                return False
            seq, _, gs, _, size, crc = e.commit
            return (seq == e.q and size == len(post.octets) and crc == J.crc32c(post.octets) and J.fits(e.commit)
                    and p.held < R.CAPACITY and all(n in groups and k > p.highest.get(n, 0) for n, k in gs))
        case "publish":
            return p.committing is not None and p.accepting
        case "refuse":
            return post is not None
        case "clean" | "drop":
            return stage == "refused"
    return False


def happen(p: Prog, h: History, e: Event, *, early: bool = False) -> None:
    """What an event does to what the program keeps and to what the runs have done; `early`, a
    program that answers 240 once the record is appended."""
    post = p.posts.get(e.q)
    if e.fails is not None:
        match e.kind:
            case "create" | "write" | "rename" | "sync" | "place":
                if post is not None:
                    post.stage = "refused"
                    h.refused.add((p.run, e.q))
                if e.kind in ("sync", "place"):
                    p.accepting = False
                if e.kind == "place":
                    p.trusting = False
            case "commit":
                p.posts.pop(e.q, None)
                p.committing, p.accepting = e.commit, False
                h.appended.append((p.run, e.commit))
                if early:
                    h.answered.append(e.commit)
            case "publish":
                p.accepting = p.trusting = False
        return
    match e.kind:
        case "reserve":
            p.posts[p.next] = Post(e.octets)
            h.files[p.next] = e.octets
            p.next += 1
        case "create" if post is not None:
            post.stage, post.written = "writing", 0
        case "write" if post is not None and post.stage == "writing":
            post.written += len(post.octets[post.written:post.written + e.m])
        case "sync" if post is not None and post.stage == "writing":
            post.stage = "synced"
        case "rename" if post is not None and post.stage == "synced":
            post.stage = "final"
        case "place" if post is not None and post.stage == "final":
            post.stage = "placed"
        case "commit":
            p.posts.pop(e.q, None)
            p.committing = e.commit
            h.appended.append((p.run, e.commit))
            if early:
                h.answered.append(e.commit)
        case "publish" if p.committing is not None:
            for n, k in p.committing[2]:
                p.highest[n] = max(p.highest.get(n, 0), k)
            p.held += 1
            if not early:
                h.answered.append(p.committing)
            p.committing = None
        case "refuse" if post is not None:
            post.stage = "refused"
            h.refused.add((p.run, e.q))
        case "drop":
            p.posts.pop(e.q, None)


def commit_for(rng: random.Random, p: Prog, groups: list[bytes], q: int) -> Commit:
    post = p.posts[q]
    chosen = rng.sample(groups, rng.randint(1, len(groups)))
    gs = [(n, p.highest.get(n, 0) + rng.choice([1, 1, 2])) for n in chosen]
    return (q, b"<%d.%d@x>" % (q, p.run), gs, rng.randint(0, len(post.octets)), len(post.octets),
            J.crc32c(post.octets))


def failing(rng: random.Random, p: Prog, e: Event) -> Event:
    """The event, now and then failing in one of the ways its operation may."""
    if rng.random() > 0.12:
        return e
    post = p.posts.get(e.q)
    match e.kind:
        case "write" if post is not None:
            k = rng.randint(0, len(post.octets[post.written:post.written + e.m]))
        case "commit":
            k = rng.randint(0, frame_length(e.commit))
        case "create" | "rename" | "clean":
            k = rng.randint(0, 1)
        case "sync" | "place" | "publish":
            k = 0
        case _:
            return e
    return replace(e, fails=k)


def draw_events(rng: random.Random, p: Prog, h: History, groups: list[bytes], n: int) -> list[Event]:
    """Events the program may make, one after another, in an order drawn at random — articles
    reserved, written in parts, synced, moved, placed, committed one at a time and answered, some
    refused and cleaned, some operations failing — each done to `p` and `h` as it is drawn."""
    out: list[Event] = []
    for _ in range(n):
        options: list[Event] = [Event("reserve", octets=rng.randbytes(rng.randint(1, 12)))]
        for q, post in p.posts.items():
            options += [Event(k, q) for k in ("create", "sync", "rename", "place", "refuse", "drop")]
            left = len(post.octets) - post.written
            options.append(Event("write", q, m=rng.choice([max(left, 1), rng.randint(1, 8)])))
            options += [Event("clean", q, final=f) for f in (0, 1)]
            if post.stage == "placed":
                options.append(Event("commit", q, commit=commit_for(rng, p, groups, q)))
        options.append(Event("publish"))
        # an article carried forward more often than one begun, refused or forgotten
        weights = [{"reserve": 1.0 if len(p.posts) < 2 else 0.2, "refuse": 0.1, "drop": 0.5,
                    "clean": 0.5}.get(e.kind, 3.0) for e in options]
        choices = [(e, w) for e, w in zip(options, weights, strict=True) if allowed(p, groups, e)]
        if not choices:
            break
        e = failing(rng, p, rng.choices([c for c, _ in choices], [w for _, w in choices])[0])
        happen(p, h, e)
        out.append(e)
    return out


# What `Cmd.allowed` checks, each a kind of event the program may not make, and how to draw one.
def probe_for(rng: random.Random, kind: str, p: Prog, groups: list[bytes]) -> Event | None:
    """An event of `kind` the program may not make in state `p`, or none if `p` has no place for
    one."""
    def placed() -> int | None:
        qs = [q for q, x in p.posts.items() if x.stage == "placed"]
        return rng.choice(qs) if qs else None

    def commit(q: int) -> Commit:
        post = p.posts[q]
        return (q, b"<p@x>", [(groups[0], p.highest.get(groups[0], 0) + 1)], 0, len(post.octets),
                J.crc32c(post.octets))
    ready = p.committing is None and p.accepting
    q = placed()
    match kind:
        case "no article":
            return Event(rng.choice(["create", "write", "sync", "rename", "place", "refuse", "drop", "clean"]),
                         p.next + 7, m=1)
        case "another stage":
            # the events checked apart below left out
            apart = {("sync", "writing"), ("place", "final")}
            wrong = [Event(k, q2, m=1) for q2, x in p.posts.items()
                     for k in ("create", "write", "sync", "rename", "place", "clean", "drop")
                     if not allowed(p, groups, Event(k, q2, m=1)) and (k, x.stage) not in apart]
            return rng.choice(wrong) if wrong else None
        case "sync before the file is written":
            qs = [q2 for q2, x in p.posts.items() if x.stage == "writing" and x.written < len(x.octets)]
            return Event("sync", rng.choice(qs)) if qs else None
        case "place once syncs are not trusted":
            qs = [q2 for q2, x in p.posts.items() if x.stage == "final"]
            return Event("place", rng.choice(qs)) if qs and not p.trusting else None
        case "commit once not accepting":
            return Event("commit", q, commit=commit(q)) if q is not None and p.committing is None \
                and not p.accepting else None
        case "commit while a record is in flight":
            return Event("commit", q, commit=commit(q)) if q is not None and p.committing is not None \
                and p.accepting else None
        case "publish once not accepting":
            return Event("publish") if p.committing is not None and not p.accepting else None
        case "publish with no record in flight":
            return Event("publish") if p.committing is None else None
    if q is None or not ready:
        return None
    c = commit(q)
    match kind:
        case "commit of another number":
            return Event("commit", q, commit=(q + 1, *c[1:]))
        case "commit of another size":
            return Event("commit", q, commit=(*c[:4], c[4] + 1, c[5]))
        case "commit of another CRC-32C":
            return Event("commit", q, commit=(*c[:5], c[5] ^ 1))
        case "commit in a group not carried":
            return Event("commit", q, commit=(c[0], c[1], [(b"local.other", 1)], *c[3:]))
        case "commit the journal cannot hold":
            return Event("commit", q, commit=(c[0], c[1], [], *c[3:]))
        case "commit numbered not above":
            last = p.highest.get(groups[0], 0)
            return Event("commit", q, commit=(c[0], c[1], [(groups[0], last)], *c[3:])) if last else None
    return None


PROBES = ["no article", "another stage", "sync before the file is written", "place once syncs are not trusted",
          "commit once not accepting", "commit while a record is in flight", "publish once not accepting",
          "publish with no record in flight", "commit of another number", "commit of another size",
          "commit of another CRC-32C", "commit in a group not carried", "commit the journal cannot hold",
          "commit numbered not above"]


def disk_of(image: dict[bytes, bytes]) -> F.Disk:
    """The directory as a crash left it: every name and file synced, the files numbered in order."""
    d = F.Disk()
    for k, (name, octets) in enumerate(image.items()):
        d.files.append(F.File(octets, octets, len(octets), latest=octets))
        d.names[name] = F.Name(k)
    return d


def ordered(image: dict[bytes, bytes]) -> dict[bytes, bytes]:
    return dict(sorted(image.items()))


def image_of(text: str) -> dict[bytes, bytes]:
    return ordered(dict(R.image_of(text)))


def violation(image: dict[bytes, bytes], groups: list[bytes], h: History) -> str | None:
    """What a start on `image` breaks of what 0005 promises after a crash, if anything."""
    try:
        _, _, _, commits, _, _ = R.recover(KEY, groups, list(ordered(image).items()))
    except R.Corrupt as why:
        return f"corrupt {why}"
    for c in h.answered:
        if c not in commits:
            return f"article {c[0]}, answered, is not found"
    for c in commits:
        if not any(a == c and (r, c[0]) not in h.refused for r, a in h.appended):
            return f"article {c[0]} is found, not appended for an article not refused"
        if image.get(R.name_of("a", c[0])) != h.files.get(c[0]):
            return f"article {c[0]}'s file is not its octets"
        if J.crc32c(h.files[c[0]]) != c[5]:
            return f"article {c[0]}'s CRC-32C is not its octets'"
    return None


@dataclass
class Segment:
    """A start on a directory and the events after it, as `dn-compiler store-model` takes them."""
    image: dict[bytes, bytes]
    run: int
    events: list[Event]
    force: bool = False

    def line(self, groups: list[bytes]) -> str:
        img = ";".join(f"{F.hexed(n)}={F.hexed(o)}" for n, o in self.image.items()) or "-"
        evs = ";".join(e.text() for e in self.events) or "-"
        return (f"{'force' if self.force else 'run'} {KEY.hex()} {','.join(g.hex() for g in groups)} {self.run} "
                f"{img} {evs}")


@dataclass
class Points:
    """What holding a segment found: the points and directories tried, the violations, and some
    directories a crash left, each with what the runs had done by then and the next run's number, to
    start again on."""
    points: int = 0
    images: int = 0
    violations: list[str] = field(default_factory=list)
    restarts: list[tuple[dict[bytes, bytes], History, int]] = field(default_factory=list)


def start_state(image: dict[bytes, bytes], run: int, groups: list[bytes]) -> Prog:
    """What the program keeps once a start on `image` is done, as recovery_ref finds it."""
    _, nxt, _, commits, _, _ = R.recover(KEY, groups, list(image.items()))
    highest: dict[bytes, int] = {}
    for c in commits:
        for n, k in c[2]:
            highest[n] = max(highest.get(n, 0), k)
    return Prog(run, nxt, highest, held=len(commits))


def after_start(image: dict[bytes, bytes], groups: list[bytes]) -> dict[bytes, bytes]:
    """The directory a start on `image` leaves: recovery_ref's actions, then a start record."""
    jkey, _, end, _, _, actions = R.recover(KEY, groups, list(image.items()))
    expected = dict(R.apply(list(image.items()), actions))
    expected[b"journal"] = expected[b"journal"] + J.frame(jkey, end, J.START, b"")
    return ordered(expected)


def apply_ops(disk: F.Disk, ops: str, then: Callable[[], None] | None = None,
              point: Callable[[], None] | None = None) -> None:
    for step in R.entries(ops, ";"):
        op, failed = F.op_of(step)
        if failed is None:
            F.do(disk, op)
        else:
            F.fail(disk, op, failed)
        if then is not None:
            then()
        if point is not None:
            point()


def parts(seg: Segment, answer: str, groups: list[bytes]) -> tuple[list[str], str]:
    if not answer.startswith("ok "):
        raise LaneError(f"{seg.line(groups)[:300]}: the model answers {answer[:300]}")
    _, ops_text, final = answer.split(" ")
    segments = ops_text.split("|")
    if len(segments) != len(seg.events) + 1:
        raise LaneError(f"{seg.line(groups)[:200]}: {len(segments)} parts of operations for {len(seg.events)} events")
    return segments, final


def hold(rng: random.Random, seg: Segment, answer: str, groups: list[bytes], h: History, *,
         early: bool = False) -> Points:
    """Hold a segment the model ran to what a crash may leave at each of its points; `h`, what the
    runs before it did, is brought up to its end."""
    segments, final = parts(seg, answer, groups)
    found = Points()
    disk = disk_of(seg.image)
    p = start_state(seg.image, seg.run, groups)
    latest = [seg.run]  # the last run's number given, a start's that has not finished among them

    def point() -> None:
        found.points += 1
        drawn = {F.shown(i): i for i in (F.leaving(disk, rng) for _ in range(PER_POINT))}
        for image in drawn.values():
            found.images += 1
            bad = violation(image, groups, h)
            if bad is not None:
                found.violations.append(bad)
        if rng.random() < 0.1:
            found.restarts.append((rng.choice(list(drawn.values())), copy.deepcopy(h), latest[0] + 1))

    def started(image: dict[bytes, bytes], ops: str) -> None:
        if ordered(F.image(disk)) != after_start(image, groups):
            raise LaneError(f"{seg.line(groups)[:200]}: after a start the directory is not what recovery_ref's "
                            f"actions and a start record make ({ops[:100]})")

    point()
    apply_ops(disk, segments[0], point=point)
    started(seg.image, segments[0])
    for e, ops in zip(seg.events, segments[1:], strict=True):
        if e.kind == "restart":
            image = ordered(F.image(disk))
            run = latest[0] = latest[0] + 1
            apply_ops(disk, ops, point=point)
            if e.start is None:
                started(image, ops)
                p = start_state(image, run, groups)
            else:
                p.run = run
        elif ops == "-":
            happen(p, h, e, early=early)
        else:
            apply_ops(disk, ops, partial(happen, p, h, e, early=early), point)
    if ordered(F.image(disk)) != image_of(final):
        raise LaneError(f"{seg.line(groups)[:200]}: done again, the operations end otherwise than the model says")
    last = F.leaving(disk, rng)
    bad = violation(last, groups, h)
    if bad is not None:
        found.violations.append(bad)
    found.restarts.append((last, copy.deepcopy(h), latest[0] + 1))
    return found


def outcome(rng: random.Random, op: str) -> int:
    """An outcome of the operation failing, as `Fs.failures` numbers them."""
    kind, *args = op.split(":")
    match kind:
        case "append":
            return rng.randint(0, len(R.unhex(args[1])))
        case "sync" | "sync-dir":
            return 0
    return rng.randint(0, 1)


def draw_run(rng: random.Random, model: list[str], image: dict[bytes, bytes], run: int, h: History,
             groups: list[bytes]) -> tuple[list[Event], int]:
    """The events of one run on `image`, the process ending now and then and the store started again
    on the file system as it is, a start's operation failing now and then; and the next run's
    number. Where a start leaves the program, the model's operations, done again on fs_ref, say."""
    p, hh = start_state(image, run, groups), copy.deepcopy(h)
    events: list[Event] = []
    for piece in range(rng.randint(1, 3)):
        events += draw_events(rng, p, hh, groups, rng.randint(10, 40) if piece == 0 else rng.randint(5, 20))
        if piece == 2 or not p.trusting or rng.random() < 0.4:
            break
        ask = Segment(image, run, [*events, Event("restart")])
        segments, _ = parts(ask, C.answer_lines(model, [ask.line(groups)])[0], groups)
        disk = disk_of(image)
        for ops in segments[:-1]:
            apply_ops(disk, ops)
        if rng.random() < 0.3:
            # a start whose operation fails, which ends the process again
            steps = R.entries(segments[-1], ";")
            i = rng.randrange(len(steps))
            for step in steps[:i]:
                F.do(disk, F.op_of(step)[0])
            journal = disk.holding(b"journal")
            k = outcome(rng, steps[i])
            F.fail(disk, F.op_of(steps[i])[0], k)
            events.append(Event("restart", start=(i, k)))
            p.run += 1
            kind, *args = steps[i].split(":")
            if kind == "sync-dir" or (kind == "sync" and int(args[0]) == journal):
                # a failed sync of the directory or the journal: no start is covered after it
                probe = Segment(image, run, [*events, Event("restart")])
                said = C.answer_lines(model, [probe.line(groups)])[0]
                if said != f"not-startable {len(probe.events)}":
                    raise LaneError(f"{probe.line(groups)[:200]}: the model answers {said[:80]}, not that no "
                                    "start may begin")
                break
        live = ordered(F.image(disk))
        events.append(Event("restart"))
        p = start_state(live, p.run + 1, groups)
    return events, p.run + 1


def probes(rng: random.Random, image: dict[bytes, bytes], run: int, h: History, groups: list[bytes],
           events: list[Event]) -> list[tuple[str, Segment]]:
    """For each thing `Cmd.allowed` checks, the events up to a point drawn where an event of that
    kind can be made, before any restart, and then one."""
    upto = next((k for k, e in enumerate(events) if e.kind == "restart"), len(events))
    states = []
    p, hh = start_state(image, run, groups), copy.deepcopy(h)
    for k in range(upto + 1):
        states.append(copy.deepcopy(p))
        if k < upto:
            happen(p, hh, events[k])
    out = []
    for kind in PROBES:
        for k in rng.sample(range(upto + 1), upto + 1):
            e = probe_for(rng, kind, states[k], groups)
            if e is not None:
                if allowed(states[k], groups, e):
                    raise LaneError(f"the lane's probe of {kind!r} is an event the program may make")
                out.append((kind, Segment(image, run, [*events[:k], e])))
                break
    return out


def at_the_bound(model: list[str]) -> dict[str, str]:
    """An article posted to a store of `R.CAPACITY` articles and to one an article short: the model and
    the lane's reading of the program both refuse its commit, and both let it be, there."""
    seen = {}
    for held, taken in ((R.CAPACITY - 1, True), (R.CAPACITY, False)):
        commits = [(s, b"<%d@f>" % s, [(GROUPS[0], s)], 0, 1, J.crc32c(b"\x00")) for s in range(1, held + 1)]
        journal = J.frame(KEY, 0, J.FORMAT, J.MAGIC + KEY)
        for c in commits:
            journal += J.frame(KEY, len(journal), J.COMMIT, J.payload(c))
        image = ordered({b"journal": journal, **{R.name_of("a", c[0]): b"\x00" for c in commits}})
        q = held + 1
        events = [Event("reserve", octets=b"x"), *(Event(k, q, m=1) for k in ("create", "write", "sync", "rename",
                                                                                 "place")),
                  Event("commit", q, commit=(q, b"<new@f>", [(GROUPS[0], q)], 0, 1, J.crc32c(b"x")))]
        p, h = start_state(image, 1, GROUPS), History()
        for e in events[:-1]:
            if not allowed(p, GROUPS, e):
                raise LaneError(f"with {held} articles the lane's reading refuses {e.text()}")
            happen(p, h, e)
        answer = C.answer_lines(model, [Segment(image, 1, events).line(GROUPS)])[0]
        if allowed(p, GROUPS, events[-1]) != taken or answer.startswith("ok ") != taken or (
                not taken and answer != f"not-allowed {len(events)}"):
            raise LaneError(f"a commit to a store of {held} articles: the lane's reading allows it "
                            f"{allowed(p, GROUPS, events[-1])}, the model answers {answer[:80]}")
        seen[str(held)] = "taken" if taken else "refused"
    return seen


# Ways of breaking the program, each taking events it may make to events it may not, or none.
def no_place(events: list[Event]) -> list[Event] | None:
    """A commit appended before the directory is synced after the file's move."""
    k = next((k for k, e in enumerate(events) if e.kind == "place" and e.fails is None), None)
    return None if k is None else events[:k] + events[k + 1:]


def never_moved(events: list[Event]) -> list[Event] | None:
    """A commit naming a number whose file was never moved to its final name."""
    k = next((k for k, e in enumerate(events) if e.kind == "rename" and e.fails is None), None)
    if k is None:
        return None
    q = events[k].q
    return [e for e in events if not (e.q == q and e.kind in ("rename", "place"))]


def changed_commit(events: list[Event], f: Callable[[Commit], Commit]) -> list[Event] | None:
    k = next((k for k, e in enumerate(events) if e.kind == "commit"), None)
    if k is None:
        return None
    new = f(events[k].commit)
    fails = events[k].fails
    out = list(events)
    out[k] = replace(events[k], commit=new, fails=None if fails is None else min(fails, frame_length(new)))
    return out


def other_size(events: list[Event]) -> list[Event] | None:
    """A commit giving another size than the file's."""
    return changed_commit(events, lambda c: (c[0], c[1], c[2], c[3], c[4] + 1, c[5]))


def other_crc(events: list[Event]) -> list[Event] | None:
    """A commit giving another CRC-32C than the file's."""
    return changed_commit(events, lambda c: (c[0], c[1], c[2], c[3], c[4], c[5] ^ 1))


def number_again(events: list[Event]) -> list[Event] | None:
    """A commit giving a group the number the last commit gave it."""
    commits = [k for k, e in enumerate(events) if e.kind == "commit"]
    if len(commits) < 2:
        return None
    first, second = events[commits[0]].commit, events[commits[1]].commit
    gs = [(n, dict(first[2]).get(n, k)) for n, k in second[2]]
    if gs == second[2]:
        return None
    out = list(events)
    out[commits[1]] = replace(events[commits[1]], commit=(*second[:2], gs, *second[3:]))
    return out


def other_group(events: list[Event]) -> list[Event] | None:
    """A commit in a group the store does not carry."""
    return changed_commit(events, lambda c: (c[0], c[1], [(b"local.other", 1)], c[3], c[4], c[5]))


def no_group(events: list[Event]) -> list[Event] | None:
    """A commit the journal cannot hold: in no group."""
    return changed_commit(events, lambda c: (c[0], c[1], [], c[3], c[4], c[5]))


def two_records(events: list[Event]) -> list[Event] | None:
    """Two records appended before either is synced."""
    commits = [k for k, e in enumerate(events) if e.kind == "commit" and e.fails is None]
    pubs = [k for k, e in enumerate(events) if e.kind == "publish" and e.fails is None]
    if len(commits) < 2 or not pubs or pubs[0] > commits[1]:
        return None
    return events[:pubs[0]] + events[pubs[0] + 1:]


def going_on(events: list[Event]) -> list[Event] | None:
    """The store going on after the record's write failed, as if it had not: half the record
    written, then the next one appended."""
    k = next((k for k, e in enumerate(events) if e.kind == "commit" and e.fails is None), None)
    if k is None or not any(e.kind == "commit" for e in events[k + 1:]):
        return None
    out = list(events)
    out[k] = replace(events[k], fails=frame_length(events[k].commit) // 2)
    return out


BREAKS: dict[str, Callable[[list[Event]], list[Event] | None]] = {
    "commit before the directory's sync": no_place, "commit for a file never moved": never_moved,
    "commit of another size": other_size, "commit of another CRC-32C": other_crc,
    "article number not above": number_again, "group not carried": other_group,
    "record the journal cannot hold": no_group, "two records before a sync": two_records,
    "going on after a failed write of the record": going_on}
EARLY = "240 before the journal's sync"


def check() -> Report:
    OUT.mkdir(parents=True, exist_ok=True)
    rng = random.Random(SEED)  # noqa: S311 -- a fixed seed, so that every run draws the same cases
    steps, mark = {}, time.monotonic()
    model = [str(lanes.DN_COMPILER), "store-model"]
    total = Points()
    chains = segments_run = restarts = failed_starts = 0
    caught: dict[str, int] = {name: 0 for name in [*BREAKS, EARLY]}
    tried: dict[str, int] = {name: 0 for name in [*BREAKS, EARLY]}
    probed: dict[str, int] = {kind: 0 for kind in PROBES}
    for _ in range(CHAINS):
        chains += 1
        image: dict[bytes, bytes] = {}
        h = History()
        run = 1
        for _ in range(rng.randint(1, 3)):
            events, _ = draw_run(rng, model, image, run, h, GROUPS)
            restarts += sum(e.kind == "restart" for e in events)
            failed_starts += sum(e.kind == "restart" and e.start is not None for e in events)
            seg = Segment(image, run, events)
            # the events up to the first restart, the program broken, each way that applies to them; a
            # break counts only if the program may not make one of its events
            first = events[:next((k for k, e in enumerate(events) if e.kind == "restart"), len(events))]
            broken = {name: b for name, breaking in BREAKS.items() if (b := breaking(first)) is not None}
            probe = probes(rng, image, run, h, GROUPS, events)
            asked = [seg.line(GROUPS), *(Segment(image, run, b, force=True).line(GROUPS) for b in broken.values()),
                     *(Segment(image, run, b).line(GROUPS) for b in broken.values()),
                     *(s.line(GROUPS) for _, s in probe)]
            said = C.answer_lines(model, asked)
            answer, said = said[0], said[1:]
            forced, checked, refused = said[:len(broken)], said[len(broken):2 * len(broken)], said[2 * len(broken):]
            for (name, b), f_answer, c_answer in zip(broken.items(), forced, checked, strict=True):
                if not c_answer.startswith("not-allowed "):
                    continue
                tried[name] += 1
                if f_answer.startswith("ok ") and hold(rng, Segment(image, run, b, force=True), f_answer, GROUPS,
                                                       copy.deepcopy(h)).violations:
                    caught[name] += 1
            for (kind, s), r_answer in zip(probe, refused, strict=True):
                if r_answer != f"not-allowed {len(s.events)}":
                    raise LaneError(f"{s.line(GROUPS)[:300]}: the model answers {r_answer[:120]}, not that it may "
                                    f"not make the last event ({kind})")
                probed[kind] += 1
            if any(e.kind == "commit" for e in events):
                tried[EARLY] += 1
                if hold(rng, seg, answer, GROUPS, copy.deepcopy(h), early=True).violations:
                    caught[EARLY] += 1
            found = hold(rng, seg, answer, GROUPS, h)
            segments_run += 1
            if found.violations:
                raise LaneError(f"{seg.line(GROUPS)[:300]}: {found.violations[0]}")
            total.points += found.points
            total.images += found.images
            # a crash at one of the points, and a start on what it left
            restart, h, run = rng.choice(found.restarts)
            image = ordered(restart)
    steps["runs"], mark = round(time.monotonic() - mark, 1), time.monotonic()
    bound = at_the_bound(model)
    steps["bound"], mark = round(time.monotonic() - mark, 1), time.monotonic()
    missed = [name for name in caught if caught[name] < CAUGHT]
    if missed:
        raise LaneError(f"drawn scenarios catch the program broken by {missed} fewer than {CAUGHT} times")
    unprobed = [kind for kind in PROBES if not probed[kind]]
    if unprobed:
        raise LaneError(f"no event the program may not make is probed for {unprobed}")
    measured = {"chains of runs": f"{chains:,}", "runs": f"{segments_run:,}", "points": f"{total.points:,}",
                "directories a crash may leave": f"{total.images:,}", "ways": f"{len(caught):,}",
                "events it may not make": f"{sum(probed.values()):,}", "restarts": f"{restarts:,}",
                "starts failing": f"{failed_starts:,}", "kinds of event": f"{len(PROBES):,}"}
    baseline = (lanes.ROOT / "docs/baseline.md").read_text()
    stated = lanes.section(baseline, "\n| Store runs |", "\n|") + lanes.section(baseline, "\n### Store runs\n",
                                                                                "\n### ")
    wrong = lanes.misstated(stated, measured)
    if wrong:
        raise LaneError(f"the documents state otherwise than measured: {wrong}")
    return Report("checked", None, [lanes.ROOT / f"scripts/{name}" for name in ("fs_ref.py", "recovery_ref.py",
                                                                                 "store_ref.py")], {
        "chains": chains, "runs": segments_run, "points": total.points, "images": total.images,
        "restarts": restarts, "failed_starts": failed_starts, "probed": probed, "broken_tried": tried,
        "broken_caught": caught, "at_the_bound": bound, "seconds_by_step": steps})


def main() -> None:
    lanes.lane_main("RUNS", OUT, check)


if __name__ == "__main__":
    main()
