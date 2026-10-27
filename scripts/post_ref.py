# SPDX-License-Identifier: AGPL-3.0-or-later
"""The store's side of POST and of reading (docs/decisions/0005-article-store.md) judged from
outside, apart from `DN.News.PostSpec`, for scripts/session_ref.py.

An article is the block after a 340, read a line at a time as scripts/framing_ref.py reads blocks:
lines end at CRLF, a dot put before a line is taken off, a line holding a NUL, a CR or an LF spoils
the block, and the line of a dot alone ends it. Its header section is checked by
scripts/article_ref.py, run as a process, when the empty line ends it, and an article without the
empty line is refused (RFC 3977 §3.6); the file it is stored in is
that header section as stored, the empty line and the body, a dot put before each line that starts
with one, as a reader receives them. The connection takes octets only while none of its writes is in
flight and fewer than 16,384 octets of the file wait to be written.

The judge keeps its own copy of the spool on the file system of scripts/fs_ref.py, doing a job's
operations when its completion comes, as the simulated host does, and holds every operation to the
order 0005 fixes for an article: the file created under its temporary name, its octets appended in
order, synced, closed, renamed to its final name, the directory synced, the commit of
scripts/store_ref.py appended where the journal ends and the journal synced. A failure before the
commit refuses the article and its names are removed; a failed sync or close stops the store, and
every article not committing is refused; a failed append or sync of the journal, or the store
stopping meanwhile, leaves the outcome unknown. After every 240, crash images of the spool — the one
that keeps only what was synced, the one that keeps everything, and one drawn between them name by
name — are recovered by scripts/recovery_ref.py and have to hold every article answered 240, with
its file: a second check behind the order of operations, which a missing sync breaks first.

A read for ARTICLE, HEAD or BODY holds one of eight places from when its connection gets it until
its file is closed and its connection answered or gone. It opens the article's final file, then
reads on from where it is, only once everything it may give has been given: 16,384 octets, or,
when what is left fits, one octet more than is left, the file closed in the same job, so that the
end of the file is always looked for; a read that failed, or whose connection is gone, closes its
file. What it has read is checked whole as a reader
would: lines end in CRLF and hold no NUL, a line that starts with a dot starts with two, the empty
line lies where the commit says the header section ends, and at the end the octets are as many as
the commit says and have its CRC-32C. A read that fails the check, or reads fewer octets than it
asked for and than are left, or more than are left, fails. It may give the 220, 221 or 222 line
and the octets checked — ARTICLE the file with Xref after the header fields, HEAD the header
section with Xref, BODY what follows the empty line — then, all of the file checked, the dot.

A read for OVER or HDR gives an article's line of scripts/overview_ref.py once all of its file is
checked, the 224, 225 or 221 line before the first, and the dot after the last; then it goes on to
the next article in the same place, from its file not yet opened. One whose article's header
section is longer than 69,632 octets, the longest the store writes, fails before it opens the file.
"""
from __future__ import annotations

from collections.abc import Callable
from dataclasses import dataclass, field
import random
from typing import NamedTuple

import framing_ref as F
import fs_ref
import overview_ref as O
import recovery_ref as R
import store_ref as J

JOBS, JOB_OPS, JOB_DATA, PLACES = 12, 8, 16384, 16
POSTS, READS, ARTICLE_MAX, HEADER_MAX, OVERVIEW_MAX = 4, 8, 1_000_000, 65536, 69632
LINE_MOST = 998
STATUS = {"article": b"220", "head": b"221", "body": b"222"}
CR, LF, NUL, CRLF, DOT = F.CR, F.LF, F.NUL, F.CRLF, F.DOT



class Op(NamedTuple):
    """An operation of a file job: `create`, `remove`, `open` of a name; `write` at an offset of a
    place, `datasync` and `close` of one, `read` of `length` octets at an offset of one; `rename` of a
    name to another; `syncdir`."""
    kind: str
    place: int = 0
    gen: int = 0
    offset: int = 0
    data: bytes = b""
    name: bytes = b""
    to: bytes = b""
    length: int = 0


# What scripts/article_ref.py makes of a header section: `None` when it is refused, else the
# header section as stored, the message identifier and the groups carried.
Verdict = tuple[bytes, bytes, list[bytes]] | None
# The checker takes the wall clock in seconds, the sequence number, the run, the connection's
# number, the path identity, the run's value in hexadecimal digits, the groups and the header section.
Checker = Callable[[int, int, int, int, bytes, bytes, list[bytes], bytes], Verdict]
# A completion as the simulated host reports it, with what a failed operation left (`fs_ref.fail`)
# and the octets a read gave.
Done = tuple[int, int, int, list[tuple[int, int]], int, bytes]


class Violation(Exception):
    def __init__(self, kind: str, message: str) -> None:
        super().__init__(message)
        self.kind = kind


@dataclass
class Start:
    """What a run of the store starts with: the groups, the path identity, the run's eight octets,
    the spool as recovery left it, the journal's place and generation, the last job's generation,
    and files that change after recovery, as a disk may change them under the store."""
    groups: list[bytes]
    identity: bytes
    run: bytes
    image: list[tuple[bytes, bytes]]
    journal: tuple[int, int]
    job_gen: int
    tamper: list[tuple[bytes, bytes]] = field(default_factory=list)


def lines_ok(data: bytes, whole: bool) -> bool:
    """Whether octets from the start of a file can begin it as a reader receives it: no NUL, a CR
    only before an LF and an LF only after a CR, a line that starts with a dot starting with two;
    once `whole`, ending a line."""
    *done, last = data.split(CRLF)
    if NUL in data or any(CR in line or LF in line or (line[:1] == DOT and line[1:2] != DOT) for line in done):
        return False
    if whole:
        return last == b""
    body = last[:-1] if last.endswith(CR) else last
    return CR not in body and LF not in body and not (last[:1] == DOT and len(last) > 1 and last[1:2] != DOT)


def file_ok(c: J.Commit, data: bytes, whole: bool) -> bool:
    """Whether octets from the start of a file can be the article of commit `c`, and, once `whole`,
    are: lines as a reader receives them, the empty line where the header section ends, and the
    commit's size and CRC-32C."""
    header = c[3]
    if len(data) >= header + 2:
        if header < 2 or data[header - 2:header + 2] != CRLF + CRLF:
            return False
    elif whole:
        return False
    return lines_ok(data, whole) and (not whole or (len(data) == c[4] and J.crc32c(data) == c[5]))


def xref(identity: bytes, groups: list[tuple[bytes, int]]) -> bytes:
    """RFC 5536 §3.2.14: the path identity, then each group and its number; a location that would
    take the line past 998 octets (RFC 5322 §2.1.1) starts a folded line."""
    lines = [b"Xref: " + identity]
    for name, number in groups:
        location = name + b":" + str(number).encode()
        if len(lines[-1]) + 1 + len(location) > LINE_MOST:
            lines.append(b"")
        lines[-1] += b" " + location
    return CRLF.join(lines) + CRLF


@dataclass
class View:
    """What a read for OVER or HDR gives besides its article: the field, `None` for OVER's; whether
    the command is XOVER or XHDR, and whether it named the article by message-id; the articles after
    it, each with the number its line gives; whether its first line is still to go."""
    legacy: bool
    field: bytes | None
    by_id: bool
    rest: list[tuple[int, J.Commit]]
    first: bool = True


@dataclass
class Fetch:
    """A read for ARTICLE, HEAD or BODY: its connection while it is to be answered; the command, the
    commit of its article and its place among the reads; its file — `none`, `open` at a place, or
    `gone` — the octets read and checked, how many octets it has given; whether it failed; its job in
    flight; how its connection was answered; the number its first line gives. For OVER or HDR also
    what it reads of its articles, and what it made of those before this one."""
    owner: tuple[int, int] | None
    cmd: str
    commit: J.Commit
    index: int
    file: str = "none"
    place: tuple[int, int] | None = None
    got: bytes = b""
    given: int = 0
    bad: bool = False
    busy: tuple[int, int] | None = None
    answered: str | None = None
    number: int = 0
    view: View | None = None
    done: bytes = b""
    # what `out` last made, for as many octets read and whether they were whole
    made: tuple[tuple[int, bool], bytes] = field(default=((-1, False), b""), repr=False, compare=False)

    def whole(self) -> bool:
        """All of the file read and checked, and found to end there: the read past it closed it."""
        return len(self.got) == self.commit[4] and self.file == "gone"

    def out(self, identity: bytes) -> bytes:
        """Everything it may give so far."""
        key = (len(self.got), self.whole())
        if self.made[0] != key:
            self.made = (key, self.making(identity))
        return self.made[1]

    def making(self, identity: bytes) -> bytes:
        if self.view is not None:
            return self.done + (self.line(identity) if self.whole() else b"")
        if not self.got:
            return b""
        header = self.commit[3]
        x = xref(identity, self.commit[2])
        known = len(self.got) >= header + 2
        if self.cmd == "head":
            stream = self.got[:header] + (x if known else b"")
        elif self.cmd == "body":
            stream = self.got[header + 2:]
        else:
            stream = self.got[:header] + (x + self.got[header:] if known else b"")
        return STATUS[self.cmd] + b" %d " % self.number + self.commit[1] + CRLF + stream + \
            (DOT + CRLF if self.whole() else b"")

    def line(self, identity: bytes) -> bytes:
        """An overview read's first line if still to go, its article's line, and after the last the dot."""
        v = self.view
        if v is None:
            return b""
        x = xref(identity, self.commit[2])
        if v.field is None:
            line = O.overview_line(identity, self.commit, self.got, self.number, x)
        else:
            label = self.commit[1] if v.legacy and v.by_id else b"%d" % self.number
            line = O.hdr_line(v.legacy, label, O.field(identity, self.commit, self.got, x, v.field))
        status = O.STATUS["over" if v.field is None else "xhdr" if v.legacy else "hdr"] if v.first else b""
        return status + line + (b"" if v.rest else DOT + CRLF)

    def advance(self, identity: bytes) -> None:
        """Given its article's line, on to the next article, its file not yet opened."""
        v = self.view
        if v is None or not v.rest:
            raise Violation("read", "an overview read with no article after its last given more")
        self.done = self.out(identity)
        self.number, self.commit = v.rest.pop(0)
        v.first = False
        self.file, self.place, self.got = "none", None, b""
        self.bad = self.commit[3] > OVERVIEW_MAX
        self.made = ((-1, False), b"")

    def held(self) -> bool:
        """Whether it still holds its place: its connection to answer, a job in flight or its file
        open."""
        return self.owner is not None or self.busy is not None or self.file == "open"

    def next_job(self, identity: bytes) -> list[Op] | None:
        if self.busy is not None:
            return None
        if self.file == "none":
            return None if self.bad or self.owner is None else [Op("open", name=R.name_of("a", self.commit[0]))]
        if self.file != "open" or self.place is None:
            return None
        place, gen = self.place
        if self.bad or self.owner is None:
            return [Op("close", place, gen)]
        if self.given < len(self.out(identity)):
            return None
        left = self.commit[4] - len(self.got)
        if left + 1 <= JOB_DATA:
            return [Op("read", place, gen, len(self.got), length=left + 1), Op("close", place, gen)]
        return [Op("read", place, gen, len(self.got), length=JOB_DATA)]


def stuff(line: bytes) -> bytes:
    return DOT + line if line.startswith(DOT) else line


@dataclass
class Article:
    """The article of one POST: its connection while it is to be answered, and the connection's
    number; the octets of the block taken so far, the line being read, the header section's lines
    so far, the body as stored; whether the block has ended and why it is refused; once its header
    section is accepted, its number, the header section as stored with the empty line, its message
    identifier and groups; how far its file has come and its octets written; its job in flight; its
    outcome."""
    owner: tuple[int, int] | None
    conn: int
    size: int = 0
    line: bytearray = field(default_factory=bytearray)
    header: bytearray = field(default_factory=bytearray)
    in_body: bool = False
    body: bytearray = field(default_factory=bytearray)
    ended: bool = False
    refused: str | None = None
    frozen: bytes = b""
    seq: int | None = None
    stored: bytes = b""
    message_id: bytes = b""
    groups: list[bytes] = field(default_factory=list)
    file: str = "none"
    place: tuple[int, int] | None = None
    written: int = 0
    synced: bool = False
    cleaned: bool = False
    busy: tuple[int, int] | None = None
    committing: bool = False
    outcome: str | None = None
    # the reply the connection was given: 240 or 441
    answered: str | None = None

    def partial(self) -> bytes:
        """What the line being read holds so far, its dot taken off, a CR at its end held back."""
        part = bytes(self.line[:-1] if self.line.endswith(F.CR) else self.line)
        return F.unstuff(part)

    def partial_lengths(self) -> tuple[int, int]:
        """The lengths of `partial()`, and of it as stored, without making either."""
        n = len(self.line) - (1 if self.line.endswith(F.CR) else 0)
        if n and self.line[0] == DOT[0]:
            return n - 1, n - 1 + (1 if n >= 2 and self.line[1] == DOT[0] else 0)
        return n, n

    def known(self) -> int:
        """How many octets of the file are known: the length of `octets()`."""
        if self.refused:
            return 0 if self.forgotten() else len(self.frozen)
        if self.seq is None:
            return 0
        return len(self.stored) + len(self.body) + self.partial_lengths()[1]

    def forgotten(self) -> bool:
        """A refused article, its names removed or never made, and nothing of it in flight."""
        return self.cleaned or (self.file == "none" and self.busy is None)

    def octets(self) -> bytes:
        """The file's octets known: none before the header section is accepted, and what was known
        when the article was refused, until it is forgotten."""
        if self.refused:
            return b"" if self.forgotten() else self.frozen
        if self.seq is None:
            return b""
        return self.stored + bytes(self.body) + stuff(self.partial())

    def alive(self) -> bool:
        """Whether the article holds its slot apart from its connection and its jobs."""
        return self.seq is not None and self.outcome not in ("posted", "lost") and not self.cleaned and \
            not (self.refused and self.file == "none")

    def names(self) -> list[bytes]:
        if self.seq is None or self.cleaned:
            return []
        letter = {"open": "t", "closed": "t", "final": "a", "placed": "a"}.get(self.file)
        return [R.name_of(letter, self.seq)] if letter else []


class Store:
    """The spool and what the store does with it, as the judge follows them."""

    def __init__(self, start: Start, checker: Checker) -> None:
        self.start = start
        self.checker = checker
        try:
            self.key, self.next, self.end, self.commits, self.aside, actions = R.recover(
                bytes(16), start.groups, start.image)
        except R.Corrupt as why:
            raise Violation("spool", f"the spool given does not recover: {why}") from None
        if actions:
            raise Violation("spool", f"the spool given has more to do: {actions}")
        self.accepting = True
        self.disk = fs_ref.Disk()
        for name, octets in start.image:
            self.disk.files.append(fs_ref.File(seen=octets, kept=octets, most=len(octets)))
            self.disk.names[name] = fs_ref.Name(synced=len(self.disk.files) - 1)
        for name, octets in start.tamper:
            held = self.disk.holding(name)
            if held is None:
                self.disk.files.append(fs_ref.File())
                held = len(self.disk.files) - 1
                self.disk.names[name] = fs_ref.Name(synced=held)
            self.disk.files[held] = fs_ref.File(seen=octets, kept=octets, most=len(octets))
        journal = self.disk.holding(b"journal")
        if journal is None:
            raise Violation("spool", "the spool given has no journal")
        # places of open files: the file each holds and its generation
        self.places: dict[int, tuple[int, int]] = {start.journal[0]: (journal, start.journal[1])}
        self.jobs: dict[int, tuple[int, list[Op], Article | Fetch]] = {}
        self.job_gen = start.job_gen
        self.articles: list[Article] = []
        self.reads: list[Fetch | None] = [None] * READS
        self.answered: list[Article] = []
        # names a failed operation may have left: a create, a rename's target, a removal
        self.loose: set[bytes] = set()
        self.rng = random.Random(len(start.image))  # noqa: S311 -- crash images drawn the same every run

    # ## Slots and the octets an article takes

    def in_slot(self) -> list[Article]:
        """The articles that hold a slot: from their 340 until their connection is answered or gone,
        nothing of theirs is in flight and nothing is left to remove."""
        return [a for a in self.articles if a.owner is not None or a.busy is not None or a.alive()]

    def free(self) -> bool:
        return len(self.in_slot()) < POSTS

    def reserved(self) -> list[bytes]:
        return [a.message_id for a in self.articles if a.seq is not None and not a.refused
                and a.outcome is None]

    def takes(self, a: Article) -> bool:
        writing = a.busy is not None and any(op.kind == "write" for op in self.jobs[a.busy[0]][1])
        return not a.ended and not writing and a.known() - a.written < JOB_DATA

    def take(self, a: Article, data: bytes, wall: int) -> int:
        """Octets of `data` the article takes, one at a time while it takes them: how many."""
        n = 0
        while n < len(data) and self.takes(a):
            self.octet(a, data[n], wall)
            n += 1
        return n

    def octet(self, a: Article, x: int, wall: int) -> None:
        a.size += 1
        prev = a.line[-1] if a.line else None
        a.line.append(x)
        if a.line.endswith(CRLF):
            line = bytes(a.line[:-2])
            a.line.clear()
            if line == DOT:
                a.ended = True
                if a.size > ARTICLE_MAX:
                    self.refuse(a, "too long")
                if not a.in_body:
                    self.refuse(a, "no empty line")
                return
            if not F.clean(line):
                self.refuse(a, "spoiled")
            elif not a.refused and not a.in_body:
                content = F.unstuff(line)
                if content:
                    a.header += content + CRLF
                else:
                    a.in_body = True
                    self.check(a, bytes(a.header) + CRLF, wall)
            elif not a.refused:
                a.body += stuff(F.unstuff(line)) + CRLF
        elif x in (F.LF[0], F.NUL[0]) or prev == F.CR[0]:
            self.refuse(a, "spoiled")
        if a.size > ARTICLE_MAX:
            self.refuse(a, "too long")
        if not a.in_body and len(a.header) + a.partial_lengths()[0] > HEADER_MAX:
            self.refuse(a, "header too long")

    def refuse(self, a: Article, why: str) -> None:
        if not a.refused:
            a.frozen = a.octets()
            a.refused = why

    def check(self, a: Article, header: bytes, wall: int) -> None:
        run = int.from_bytes(self.start.run, "big")
        verdict = self.checker(wall // 1000, self.next, run, a.conn, self.start.identity,
                               self.start.run.hex().encode(), self.start.groups, header)
        if verdict is None:
            self.refuse(a, "refused")
            return
        stored, message_id, groups = verdict
        reserved = self.reserved()
        if (any(c[1] == message_id for c in self.commits) or message_id in reserved
                or len(self.commits) + len(self.aside) + len(reserved) >= R.CAPACITY
                or self.next + 2 >= 2**64):
            self.refuse(a, "not reserved")
            return
        a.seq, a.message_id, a.groups = self.next, message_id, groups
        a.stored = b"".join(stuff(line) + CRLF for line in stored.split(CRLF)[:-1]) + CRLF
        self.next += 1

    def abandon(self, owner: tuple[int, int]) -> None:
        """The connection gone, or its input ended: its article, if its block has not ended,
        abandoned, and its read left to close its file."""
        for a in self.articles:
            if a.owner == owner:
                a.owner = None
                if not a.ended:
                    self.refuse(a, "abandoned")
        for f in self.reads:
            if f is not None and f.owner == owner:
                f.owner = None

    # ## Reads

    def found(self, message_id: bytes) -> J.Commit | None:
        return next((c for c in self.commits if c[1] == message_id), None)

    def free_reads(self) -> list[int]:
        return [k for k, f in enumerate(self.reads) if f is None or not f.held()]

    def grant(self, owner: tuple[int, int], cmd: str, commit: J.Commit, number: int = 0,
              view: View | None = None) -> Fetch:
        """The lowest free read, given to a connection, its first line giving `number`; for OVER or
        HDR failed at once when the header section is longer than one takes."""
        k = self.free_reads()[0]
        f = Fetch(owner, cmd, commit, k, number=number, view=view, bad=view is not None and commit[3] > OVERVIEW_MAX)
        self.reads[k] = f
        return f

    def fetches(self) -> list[Fetch]:
        return [f for f in self.reads if f is not None and f.held()]

    def fetch_at(self, place: int, gen: int) -> Fetch | None:
        return next((f for f in self.fetches() if f.file == "open" and f.place == (place, gen)), None)

    def fetch_job(self, ops: list[Op]) -> bool:
        return ops[0].kind in ("open", "read") or (ops[0].kind == "close" and
                                                   self.fetch_at(ops[0].place, ops[0].gen) is not None)

    def stop(self) -> None:
        self.accepting = False
        for a in self.articles:
            if a.outcome is None and not a.committing:
                self.refuse(a, "stopped")

    def decided(self, a: Article) -> str | None:
        """The answer an article is due: 240, 441, or none, the connection closed."""
        if a.outcome:
            return a.outcome
        if a.refused and a.ended and a.busy is None:
            return "failed"
        return None

    # ## Jobs

    def commit_of(self, a: Article) -> J.Commit:
        octets = a.octets()
        highest: dict[bytes, int] = {}
        for c in self.commits:
            for name, number in c[2]:
                highest[name] = max(highest.get(name, 0), number)
        groups = [(g, highest.get(g, 0) + 1) for g in a.groups]
        return a.seq or 0, a.message_id, groups, len(a.stored) - 2, len(octets), J.crc32c(octets)

    def at_place(self, place: int, gen: int) -> Article | None:
        return next((a for a in self.articles if a.place == (place, gen) and a.file == "open"), None)

    def named(self, name: bytes, kind: str) -> Article | None:
        found = R.name_kind(name)
        if found is None or found[0] != kind:
            return None
        return next((a for a in self.articles if a.seq == found[1]), None)

    def journal_op(self, ops: list[Op]) -> bool:
        return any(op.kind in ("write", "datasync") and (op.place, op.gen) == self.start.journal for op in ops)

    def handed(self, jobs: list[tuple[int, int, list[Op]]]) -> None:
        """Jobs handed over in a turn, each held to the host's contract and to the order of an
        article's operations."""
        dir_syncs = sum(1 for _, ops, _ in self.jobs.values() if any(op.kind == "syncdir" for op in ops))
        appends = sum(1 for _, ops, _ in self.jobs.values() if self.journal_op(ops))
        wanted = [(f, ops) for f in self.fetches() if (ops := f.next_job(self.start.identity)) is not None]
        for slot, gen, ops in jobs:
            if not 0 <= slot < JOBS or slot in self.jobs:
                raise Violation("job", f"a job in slot {slot}, which is not free")
            if gen <= self.job_gen:
                raise Violation("job", f"a job of generation {gen}, not above {self.job_gen}")
            self.job_gen = gen
            if not 1 <= len(ops) <= JOB_OPS or sum(len(op.data) for op in ops) > JOB_DATA:
                raise Violation("job", f"a job of {len(ops)} operations, or of more octets than one moves")
            if self.fetch_job(ops):
                if not wanted or wanted[0][1] != ops:
                    raise Violation("read", f"a job {ops}, not the next of the reads, "
                                    f"{wanted[0][1] if wanted else 'none'}")
                f, _ = wanted.pop(0)
                f.busy = (slot, gen)
                self.jobs[slot] = (gen, ops, f)
                continue
            dir_syncs += any(op.kind == "syncdir" for op in ops)
            appends += self.journal_op(ops)
            if dir_syncs > 1:
                raise Violation("dir-syncs", "two syncs of the directory in flight")
            if appends > 1:
                raise Violation("appends", "two appends of the journal in flight")
            owner = self.journal_job(ops) if self.journal_op(ops) else self.article_job(ops)
            if owner.busy is not None:
                raise Violation("job", f"article {owner.seq} given a job while one is in flight")
            owner.busy = (slot, gen)
            owner.committing = self.journal_op(ops)
            self.jobs[slot] = (gen, ops, owner)

    def article_job(self, ops: list[Op]) -> Article:
        """The article a job is for, each of its operations the next its article may take."""
        owner: Article | None = None
        file, written, synced = "", 0, False
        for op in ops:
            kind = op.kind
            if kind == "create":
                a = self.named(op.name, "temp")
                if a is None or a.file != "none" or a.refused or owner is not None:
                    raise Violation("job", f"a create of {op.name!r}, not the next for its article")
                owner, file = a, "creating"
                continue
            if kind == "remove":
                a = self.named(op.name, "temp") or self.named(op.name, "final")
                if a is None or not a.refused or op.name not in a.names() or (owner not in (None, a)):
                    raise Violation("job", f"a remove of {op.name!r}, a name of no refused article")
                owner = a
                continue
            if kind in ("write", "datasync", "close"):
                a = self.at_place(op.place, op.gen) if owner is None else owner
                if a is None or a.place != (op.place, op.gen) or a.file != "open":
                    raise Violation("job", f"a {kind} on place {op.place}/{op.gen}, no open article's")
                if owner is None:
                    written, synced = a.written, a.synced
                owner = a
                if kind == "write":
                    octets = a.octets()
                    if a.refused or op.offset != written or not op.data or \
                            octets[written:written + len(op.data)] != op.data:
                        want = octets[written:written + len(op.data)]
                        at = next((k for k, (x, y) in enumerate(zip(op.data, want, strict=False)) if x != y),
                                  min(len(op.data), len(want)))
                        raise Violation("write", f"article {a.seq} written at {op.offset}, not {written}, or "
                                        f"{op.data[at:at + 40]!r} at {op.offset + at}, not {want[at:at + 40]!r}")
                    written += len(op.data)
                elif kind == "datasync":
                    if not a.ended or written != a.known() or a.refused:
                        raise Violation("sync", f"article {a.seq} synced before it was written whole")
                    synced = True
                elif not synced and not a.refused:
                    raise Violation("close", f"article {a.seq} closed before it was synced")
                continue
            if kind == "rename":
                a = self.named(op.name, "temp")
                if a is None or owner is not None or a.file != "closed" or a.refused or \
                        op.to != R.name_of("a", a.seq or 0):
                    raise Violation("job", f"a rename of {op.name!r} to {op.to!r}, not the next for its article")
                owner, file = a, "renaming"
                continue
            if kind == "syncdir" and file == "renaming":
                file = "syncing"
                continue
            raise Violation("job", f"an operation {op}, not the next for any article")
        if owner is None:
            raise Violation("job", "a job for no article")
        return owner

    def journal_job(self, ops: list[Op]) -> Article:
        """An append of the journal and its sync: the commit of an article placed."""
        if [op.kind for op in ops] != ["write", "datasync"] or \
                any((op.place, op.gen) != self.start.journal for op in ops):
            raise Violation("journal", f"a job on the journal that is not an append and its sync: {ops}")
        w = ops[0]
        if w.offset != self.end:
            raise Violation("journal", f"an append at {w.offset}, not where the journal ends, {self.end}")
        c = J.decode(w.data[J.HEADER:-1])
        a = next((x for x in self.articles if c is not None and x.seq == c[0]), None)
        if a is None or a.file != "placed" or a.refused or not a.ended or not self.accepting:
            raise Violation("journal", f"an append of {w.data[:60].hex()}, the commit of no article placed")
        want = J.frame(self.key, self.end, J.COMMIT, J.payload(self.commit_of(a)))
        if w.data != want:
            raise Violation("journal", f"article {a.seq} committed as {w.data.hex()}, not {want.hex()}")
        return a

    # ## Completions

    def complete(self, dones: list[Done]) -> None:
        """Completions, in the order the host reports them: each job's operations done on the spool
        up to the first that failed, which leaves what the host says it left."""
        for slot, gen, ok, results, partial, data in dones:
            if slot not in self.jobs or self.jobs[slot][0] != gen:
                raise Violation("job", f"a completion of job {slot}/{gen}, not in flight")
            _, ops, a = self.jobs.pop(slot)
            if isinstance(a, Fetch):
                self.fetched(a, ops, ok, results, data)
                continue
            accepting = self.accepting
            for k, op in enumerate(ops[:ok + 1]):
                self.disk_op(op, k < ok, partial, results[k] if k < ok else (0, 0))
            a.busy = None
            self.moved(a, ops, ok, accepting, results)

    def fetched(self, f: Fetch, ops: list[Op], ok: int, results: list[tuple[int, int]], data: bytes) -> None:
        """A read's job completed: what it did on the spool, held to the spool's own copy, and what it
        does to the read."""
        f.busy = None
        kind = ops[0].kind
        if kind == "open":
            said = fs_ref.do(self.disk, ("open", [ops[0].name.hex()]))
            if ok == 1:
                if not said.startswith("file:") or not 0 <= results[0][0] < PLACES or results[0][0] in self.places:
                    raise Violation("job", f"an open that succeeded as {said} at place {results[0][0]}")
                self.places[results[0][0]] = (int(said[5:]), results[0][1])
                f.file, f.place = "open", results[0]
            else:
                f.file, f.bad = "gone", True
            return
        if kind == "close":
            self.places.pop(ops[0].place, None)
            f.file = "gone"
            return
        if ok == 0:
            f.bad = True
            return
        op = ops[0]
        held = self.places[op.place][0]
        if data != self.disk.files[held].seen[op.offset:op.offset + op.length] or results[0][0] != len(data):
            raise Violation("job", f"a read of {len(data)} octets at {op.offset}, not what the file holds")
        if len(ops) == 2:
            self.places.pop(op.place, None)
            f.file = "gone"
        left = f.commit[4] - len(f.got)
        if len(data) < min(left, op.length) or len(data) > left or \
                not file_ok(f.commit, f.got + data, len(f.got) + len(data) >= f.commit[4]):
            f.bad = True
        else:
            f.got += data

    def disk_op(self, op: Op, done: bool, partial: int, result: tuple[int, int]) -> None:
        kind = op.kind
        if kind == "close":
            self.places.pop(op.place, None)
            return
        if kind == "create":
            if done:
                said = fs_ref.do(self.disk, ("create", [op.name.hex()]))
                if not said.startswith("file:") or not 0 <= result[0] < PLACES or result[0] in self.places:
                    raise Violation("job", f"a create that succeeded as {said} at place {result[0]}")
                self.places[result[0]] = (int(said[5:]), result[1])
            else:
                fs_ref.fail(self.disk, ("create", [op.name.hex()]), partial)
                self.loose.add(op.name)
            return
        if kind in ("write", "datasync"):
            f = self.places.get(op.place)
            if f is None or f[1] != op.gen:
                raise Violation("job", f"an operation on place {op.place}/{op.gen}, not open")
            if kind == "write" and op.offset != len(self.disk.files[f[0]].seen):
                raise Violation("job", f"a write at {op.offset}, not where its file ends")
            fop: fs_ref.Op = ("append", [str(f[0]), op.data.hex()]) if kind == "write" else ("sync", [str(f[0])])
        elif kind == "rename":
            fop = ("rename", [op.name.hex(), op.to.hex()])
        elif kind == "remove":
            fop = ("remove", [op.name.hex()])
        else:
            fop = ("sync-dir", [])
        if done:
            fs_ref.do(self.disk, fop)
        else:
            fs_ref.fail(self.disk, fop, partial)
            if kind == "rename":
                self.loose.add(op.to)
            elif kind == "remove":
                self.loose.add(op.name)

    def moved(self, a: Article, ops: list[Op], ok: int, accepting: bool, results: list[tuple[int, int]]) -> None:
        """What a completion does to its article and to the store."""
        failed = ops[ok].kind if ok < len(ops) else None
        if a.committing:
            a.committing = False
            if failed is None and accepting:
                a.outcome = "posted"
                c = self.commit_of(a)
                self.commits.append(c)
                self.end += len(J.frame(self.key, self.end, J.COMMIT, J.payload(c)))
                self.answered.append(a)
            else:
                a.outcome = "lost"
                self.stop()
            return
        if ops[0].kind in ("close", "remove") and a.refused:
            if failed == "close" and ok == 0:
                a.file = "closed"
                self.stop()
            else:
                a.cleaned = True
            return
        for op in ops[:ok]:
            match op.kind:
                case "create":
                    a.file, a.place = "open", results[0]
                case "write":
                    a.written += len(op.data)
                case "datasync":
                    a.synced = True
                case "close":
                    a.file = "closed"
                case "rename":
                    a.file = "final"
                case "syncdir":
                    a.file = "placed"
        if failed == "close":
            a.file = "closed"
        if failed is not None:
            self.refuse(a, f"{failed} failed")
        if failed in ("datasync", "close", "syncdir"):
            self.stop()

    # ## What has to hold

    def stalled(self) -> str | None:
        """An article or a read that could move and was given no job: an article has a next step
        whenever nothing of its is in flight, but for the directory's sync or the journal's append in
        flight."""
        for f in self.fetches():
            if f.next_job(self.start.identity) is not None:
                return f"read {f.index} of article {f.commit[0]} given no job"
        placing = any(op.kind == "syncdir" for _, ops, _ in self.jobs.values() for op in ops)
        appending = any(self.journal_op(ops) for _, ops, _ in self.jobs.values())
        for a in self.articles:
            if a.busy is not None or a.outcome or a.seq is None:
                continue
            if a.refused:
                if a.names() and not a.cleaned:
                    return f"article {a.seq}'s names not removed"
                continue
            if a.file == "none":
                return f"article {a.seq} not created"
            if a.file == "open" and (a.known() - a.written >= JOB_DATA or a.ended):
                return f"article {a.seq} not written"
            if a.file == "closed" and not placing:
                return f"article {a.seq} not placed"
            if a.file == "placed" and not appending:
                return f"article {a.seq} not committed"
        return None

    def crashes(self) -> list[dict[bytes, bytes]]:
        """Images a crash may leave (`fs_ref.may_leave`): each name as the directory's last sync left
        it, each file as its last sync did; everything as it is; and each name, then each file, drawn
        from the two."""
        least, drawn = {}, {}
        for n, h in self.disk.names.items():
            if h.synced is not None:
                least[n] = self.disk.files[h.synced].kept
            f = self.rng.choice([h.synced, h.now()])
            if f is not None:
                drawn[n] = self.rng.choice([self.disk.files[f].kept, self.disk.files[f].seen])
        return [least, fs_ref.image(self.disk), drawn]

    def durable(self) -> None:
        """Crash images of the spool recover with every article answered 240, its file whole."""
        for image in self.crashes():
            names = list(image.items())
            try:
                _, _, _, commits, _, actions = R.recover(bytes(16), self.start.groups, names)
            except R.Corrupt as why:
                raise Violation("durable", f"a crash leaves a spool that does not recover: {why}") from None
            seqs = {c[0] for c in commits}
            files = dict(R.apply(names, actions))
            for a in self.answered:
                if a.seq not in seqs or files.get(R.name_of("a", a.seq or 0)) != a.octets():
                    raise Violation("durable", f"a crash loses article {a.seq}, answered 240")

    def finish(self) -> None:
        """At the end of a run, the spool holds the journal, the files of the articles it commits,
        the names it was given, and of a refused article only a name a failed removal left."""
        if self.jobs:
            raise Violation("names", f"jobs still in flight at the end: {sorted(self.jobs)}")
        allowed = {b"journal", *(R.name_of("a", c[0]) for c in self.commits)}
        allowed |= {name for name, _ in self.start.image} | self.loose
        allowed |= {R.name_of("a", a.seq or 0) for a in self.articles if a.outcome == "lost"}
        extra = sorted(set(fs_ref.image(self.disk)) - allowed)
        if extra:
            raise Violation("names", f"the spool is left holding {extra}")
