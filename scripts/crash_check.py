#!/usr/bin/env python3
# SPDX-License-Identifier: AGPL-3.0-or-later
"""The crash lane: the NNTP server — the session's program with native/nntp_host.c and the store's
host — killed before each of its file operations and started again, held from outside to what
decision 0005 promises after a crash (`store_safe`); the kernel keeps what was written.

The host's test build stops the process before the operation `dn/stop` numbers (native/jobs.c); the
lane sees it stopped and kills it, for each number from one until a run it is not stopped in, which
has to come at the same number every time. Meanwhile clients post over sockets: two articles at once
into overlapping groups on an empty spool; then, on the spool those left, one Message-ID from two
connections at once, one the spool holds, a crosspost and a read; then an article on that spool as a
crash leaves it, so that the start's recovery is stopped too. After each run:

- recovered by scripts/recovery_ref.py, the spool is not corrupt, holds each article it held before
  as it was and every article answered 240, each in the groups it named, numbered on from one in each,
  its file what the client sent with each field the server adds once and of its commit's CRC-32C, and
  no article not posted; each client read what it reads in a run not stopped, or the start of it; no
  Message-ID was answered 240 twice, nor one the spool held before, nor a new one refused each time;
  a run not stopped left no name but the journal's, the articles' and those set aside;
- the server started on it again listens, `nntplib` reads each article the spool holds, with its
  Xref, and finds no other; a new article posted is taken, numbered on in each group, and one the
  spool holds refused; it leaves the directory recovery_ref's actions leave with a start record and
  that article after them, on which a start has nothing more to do.

Each defect of `DEFECTS`, planted in the program or the host, has to be caught for the reason named.
"""
from __future__ import annotations

import argparse
from collections.abc import Callable
from concurrent.futures import ThreadPoolExecutor
from dataclasses import dataclass
import functools
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
import threading
import time

sys.path.insert(0, str(Path(__file__).resolve().parent))
import lanes  # the path above is what makes these importable
from lanes import NATIVE, ROOT, LaneError, Report
import nntp_check as N
import recovery_ref as R
import session_check as sessions
import store_ref as J

OUT = ROOT / "build/crash"
JOBS = NATIVE / "jobs.c"
GROUPS = [b"local.a", b"local.b", b"local.c"]
# The key of a journal recovery makes; the server makes its own, which the checks read back.
KEY = bytes(16)
TIMEOUT = 10.0
# The header fields the server adds to an article that lacks them, as a client here sends it.
ADDED = (b"path:", b"date:", b"injection-info:", b"injection-date:")
# The name of the mark of a failed sync, which the host removes, when of another boot, before
# recovery.
MARK = b"sync-failed"
# A whole mark of a boot other than this one, which a start removes.
OTHER_BOOT = b"00000000-0000-4000-8000-000000000000\n"


# The points of native/jobs.c that fail nothing but carry a number.
PARAMETERS = {"dn/write-short", "dn/sync-slow", "dn/stop", "dn/fail"}


def points() -> set[str]:
    """The points of native/jobs.c's operations, which have to be those `dn/fail` fails."""
    text = JOBS.read_text()
    start = text.index("POINTS[] = {")
    end = text.index("};", start)
    listed = set(re.findall(r'"(dn/[a-z-]+)"', text[start:end]))
    named = set(re.findall(r'"(dn/[a-z-]+)"', text[:start] + text[end:])) - PARAMETERS
    if listed != named:
        raise LaneError(f"dn/fail fails {sorted(listed)}, the operations' points being {sorted(named)}")
    return listed


def article(mid: str, groups: str, lines: int = 1) -> bytes:
    body = ("text", ".a line with a dot", *(f"line {k} " + "x" * 70 for k in range(lines)))
    return sessions.article("From: a@b.example", f"Newsgroups: {groups}", "Subject: s", f"Message-ID: {mid}",
                            body=body)


@dataclass
class Part:
    """A client's part: the article it posts, or else the Message-ID it reads."""
    post: bytes = b""
    read: str = ""


@dataclass
class Phase:
    name: str
    parts: list[Part]

    def posted(self) -> dict[bytes, bytes]:
        """Each article posted in this phase and those before, by its Message-ID."""
        return {mid_of(p.post): p.post for phase in PHASES[:PHASES.index(self) + 1] for p in phase.parts if p.post}


def mid_of(post: bytes) -> bytes:
    return next(line[12:] for line in post.split(b"\r\n") if line.lower().startswith(b"message-id: "))


SAME = article("<same@x.example>", "local.c")
PHASES = [
    Phase("an empty spool", [Part(article("<one@x.example>", "local.a")),
                             Part(article("<two@x.example>", "local.b,local.a", lines=300))]),
    Phase("the spool those left", [Part(SAME), Part(SAME), Part(article("<one@x.example>", "local.a")),
                                   Part(article("<three@x.example>", "local.c,local.b")),
                                   Part(read="<two@x.example>")]),
    Phase("that spool as a crash leaves it", [Part(article("<four@x.example>", "local.a,local.c"))]),
]
# Posted to each spool a run left, once the server is started on it again.
AFTER = article("<after@x.example>", "local.b,local.a")
TEXTS = N.TEXTS


def crashed(image: dict[bytes, bytes]) -> dict[bytes, bytes]:
    """`image` as a crash in the middle of two articles leaves it: one's file under its temporary
    name, the other's under its final name, and half of its commit appended to the journal."""
    journal = image[b"journal"]
    at = J.HEADER + len(J.MAGIC)
    nxt = R.recover(KEY, GROUPS, list(image.items()))[1]
    commit = J.payload((nxt + 1, b"<torn@x.example>", [(b"local.a", 9)], 0, 3, 0))
    torn = J.frame(journal[at:at + J.KEY], len(journal), J.COMMIT, commit)
    return {**image, R.name_of("t", nxt): b"par", R.name_of("a", nxt + 1): b"x\r\n",
            b"journal": journal + torn[:len(torn) // 2]}


def converse(port: int, part: Part, together: threading.Barrier, got: list[bytes]) -> None:
    """One client's part: the greeting, POST and its answer if it posts; once every client of the
    phase is there, the article and its answer, or ARTICLE and its text; QUIT. Each line read goes
    into `got`; the part ends where the server stops answering."""
    try:
        with socket.create_connection(("127.0.0.1", port), timeout=TIMEOUT) as s, s.makefile("rb") as f:
            got.append(f.readline())
            if part.post:
                s.sendall(b"POST\r\n")
                got.append(f.readline())
            together.wait()
            s.sendall(part.post or f"ARTICLE {part.read}\r\n".encode())
            got.append(f.readline())
            if got[-1].startswith(b"220"):
                while got[-1] not in (b".\r\n", b""):
                    got.append(f.readline())
            s.sendall(b"QUIT\r\n")
            got.append(f.readline())
    except (OSError, threading.BrokenBarrierError):
        pass


def options(spool: Path, run: Path) -> list[str]:
    return ["--port", "0", "--revision", N.REVISION.decode(), "--source", N.SOURCE.decode(), "--spool", str(spool),
            "--run-dir", str(run), "--path-identity", "dn.example",
            *(a for g in GROUPS for a in ("--group", g.decode()))]


def stopped(proc: subprocess.Popen[str]) -> bool:
    """Whether the server is stopped, as its parent learns it: a tracer's stops at its calls, which
    `/proc` shows alike, are not reported to the parent; nor is anything consumed. One that ended is
    not waited for this way (ECHILD)."""
    try:
        return os.waitid(os.P_PID, proc.pid, os.WSTOPPED | os.WNOHANG | os.WNOWAIT) is not None
    except ChildProcessError:
        return False


def watch(proc: subprocess.Popen[str], done: Callable[[], bool], what: str) -> bool:
    """Whether the server stopped before `done` came true; it may not end meanwhile."""
    deadline = time.monotonic() + TIMEOUT
    while not done():
        if stopped(proc):
            return True
        if proc.poll() is not None and not done():
            raise LaneError(f"the server ended with status {proc.returncode} {what}")
        if time.monotonic() > deadline:
            raise LaneError(f"the server neither stopped nor went on in {TIMEOUT} s {what}")
        time.sleep(0.002)
    return False


def spool_of(spool: Path) -> dict[bytes, bytes]:
    return {os.fsencode(f.name): f.read_bytes() for f in spool.iterdir()}


def laid(where: Path, image: dict[bytes, bytes], spool_at: Path | None = None) -> tuple[Path, Path]:
    """A spool holding `image`, under `spool_at` synced, and a run directory."""
    spool, run = (spool_at or where) / "spool", where / "run"
    spool.mkdir(parents=True)
    run.mkdir(parents=True)
    for name, data in image.items():
        with (spool / os.fsdecode(name)).open("wb") as file:
            file.write(data)
            if spool_at:
                file.flush()
                os.fsync(file.fileno())
    return spool, run


def served(binary: Path, phase: Phase, base: dict[bytes, bytes], enable: str, where: Path,
           spool_at: Path | None = None, ready: Callable[[], None] = lambda: None,
           lost: Callable[[], None] = lambda: None,
           refusing: bool = False) -> tuple[bool, list[list[bytes]], dict[bytes, bytes]]:
    """The phase's clients served on a spool holding `base`, under `spool_at` if given, by the server
    with the points `enable` names if any, started once `ready` is done, killed once stopped and `lost`
    done: whether it stopped, or, with `refusing`, ended at its start with status 4, what each client
    read, and the spool left."""
    spool, run = laid(where, base, spool_at)
    ready()
    env = {k: v for k, v in os.environ.items() if not k.startswith("FIU_")}
    if enable:
        env |= {"LD_PRELOAD": str(fiu() / "fiu_run_preload.so"), "FIU_ENABLE": enable}
    got: list[list[bytes]] = [[] for _ in phase.parts]
    together = threading.Barrier(len(phase.parts), timeout=TIMEOUT)
    threads: list[threading.Thread] = []
    err = where / "stderr"
    with err.open("w") as said, subprocess.Popen([str(binary), *options(spool, run)], stdout=subprocess.PIPE,
                                                 stderr=said, text=True, env=env) as proc:
        out = lanes.Lines(N.Server.pipe(proc.stdout))
        port: list[str | None] = []

        def listening() -> bool:
            try:
                port.append(out.get(0.0))
            except queue.Empty:
                return False
            return True

        try:
            halted = watch(proc, lambda: listening() or (refusing and proc.poll() is not None), "at start")
            given = None if halted or not port else port[0]
            if not halted and given is None:
                if not refusing or proc.wait(TIMEOUT) != 4:
                    raise LaneError(f"the server gave no port: {err.read_text()[-300:]!r}")
                halted = True
            if given is not None:
                at = int(json.loads(given)["port"])
                threads = [threading.Thread(target=converse, args=(at, p, together, g))
                           for p, g in zip(phase.parts, got, strict=True)]
                for t in threads:
                    t.start()
                halted = watch(proc, lambda: not any(t.is_alive() for t in threads), "while serving")
            if not halted:
                proc.send_signal(signal.SIGTERM)
                halted = watch(proc, lambda: proc.poll() is not None, "on SIGTERM")
                if not halted and proc.returncode != 0:
                    raise LaneError(f"on SIGTERM the server ended with status {proc.returncode}: "
                                    f"{err.read_text()[-300:]!r}")
            lost()
        finally:
            if proc.poll() is None:
                proc.kill()
            together.abort()
            for t in threads:
                t.join(TIMEOUT)
            proc.wait()
    return halted, got, spool_of(spool)


def lines_of(octets: bytes) -> list[bytes]:
    return octets.split(b"\r\n")[:-1]


def fields(header: bytes) -> list[bytes]:
    """A header section's fields, each with the lines that continue it."""
    found: list[bytes] = []
    for line in lines_of(header):
        if line[:1] in (b" ", b"\t") and found:
            found[-1] += b"\r\n" + line
        else:
            found.append(line)
    return found


def as_sent(file: bytes, post: bytes) -> bool:
    """Whether a file holds the article as its client sent it: its fields in order, those the server
    adds aside, and its body, dot-stuffed both, without the final line of a dot."""
    head, _, body = file.partition(b"\r\n\r\n")
    sent_head, _, sent_body = post.removesuffix(b".\r\n").partition(b"\r\n\r\n")
    found = fields(head + b"\r\n")
    kept = [f for f in found if not f.lower().startswith(ADDED)]
    added = sorted(f.split(b":", 1)[0].lower() + b":" for f in found if f.lower().startswith(ADDED))
    return body == sent_body and kept == fields(sent_head + b"\r\n") and added == sorted(ADDED)


def groups_of(post: bytes) -> list[bytes]:
    named = next(line[12:] for line in post.split(b"\r\n") if line.startswith(b"Newsgroups: "))
    return [g for g in named.split(b",") if g in GROUPS]


def text_of(file: bytes, commit: J.Commit) -> bytes:
    """A held article's text as ARTICLE sends it: its file, with Xref after its header."""
    head, _, body = file.partition(b"\r\n\r\n")
    xref = b"Xref: dn.example " + b" ".join(g + b":" + str(k).encode() for g, k in commit[2])
    return head + b"\r\n" + xref + b"\r\n\r\n" + body


def read_as(got: list[bytes], wanted: list[bytes], halted: bool) -> bool:
    """Whether a client read the lines `wanted`, or, the server stopped, the start of them."""
    read, whole = b"".join(got), b"".join(wanted)
    return read == whole or (halted and whole.startswith(read))


def posting(answer: bytes) -> list[bytes]:
    return [TEXTS["greeting-post"], TEXTS["post"], answer, TEXTS["quit"]]


def unlike(c: J.Commit, image: dict[bytes, bytes], posted: dict[bytes, bytes]) -> str | None:
    """What a held article is otherwise than its client posted it, if anything."""
    if c[1] not in posted:
        return f"article {c[0]} was not posted"
    file = image[R.name_of("a", c[0])]
    if J.crc32c(file) != c[5]:
        return f"article {c[0]}'s CRC-32C is not its file's"
    if not as_sent(file, posted[c[1]]):
        return f"article {c[0]}'s file is not what its client sent"
    if [g for g, _ in c[2]] != groups_of(posted[c[1]]):
        return f"article {c[0]} is in {c[2]}, not in the groups it named"
    return None


def numbering(commits: list[J.Commit]) -> str | None:
    numbers: dict[bytes, list[int]] = {}
    for c in commits:
        for g, k in c[2]:
            numbers.setdefault(g, []).append(k)
    return next((f"{g.decode()} numbers its articles {ks}" for g, ks in numbers.items()
                 if ks != list(range(1, len(ks) + 1))), None)


def violation(phase: Phase, base: dict[bytes, bytes], image: dict[bytes, bytes], got: list[list[bytes]],
              halted: bool, failing: bool = False, unreadable: bool = False) -> str | None:
    """What the spool a run on `base` left, or what its clients read, breaks of what 0005 promises
    after a crash, if anything; with `failing`, an operation failed, so a post may be refused and, in a
    run not stopped, one connection closed unanswered after its 340, its article held or not; with
    `unreadable`, a read answered 403, or cut short once its text has begun."""
    try:
        commits = R.recover(KEY, GROUPS, list(image.items()))[3]
    except R.Corrupt as why:
        return f"corrupt {why}"
    posted, held = phase.posted(), {c[1]: c for c in commits}
    before = {c[1]: c for c in R.recover(KEY, GROUPS, list(base.items()))[3]}
    for mid, c in before.items():
        name = R.name_of("a", c[0])
        if held.get(mid) != c or image.get(name) != base[name]:
            return f"{mid.decode()}, held before, is not held as it was"
    answers: dict[bytes, list[bytes]] = {}
    unanswered = 0
    for part, lines in zip(phase.parts, got, strict=True):
        if part.read:
            kept = before.get(part.read.encode())
            reply = (b"220 0 " + kept[1] + b"\r\n" + text_of(base[R.name_of("a", kept[0])], kept) + b".\r\n"
                     if kept else TEXTS["no-such-id"])
            wanted = [[TEXTS["greeting-post"], r, TEXTS["quit"]] for r in (reply, TEXTS["unreadable"])[:1 + unreadable]]
        else:
            wanted = [posting(TEXTS["posted"]), posting(TEXTS["failed"])]
        seen = f"a client of {part.read or mid_of(part.post).decode()} read {b''.join(lines)[-160:]!r}"
        if not any(read_as(lines, w, halted or failing) for w in wanted):
            return seen
        if not halted and not any(read_as(lines, w, False) for w in wanted) and not (part.read and unreadable):
            if part.read or b"".join(lines) != TEXTS["greeting-post"] + TEXTS["post"]:
                return seen
            unanswered += 1
        if part.post:
            whole = len(lines) > 2 and lines[2].endswith(b"\r\n")
            answers.setdefault(mid_of(part.post), []).append(lines[2][:3] if whole else b"")
    if unanswered > 1:
        return f"{unanswered} connections were closed unanswered in a run not stopped"
    for mid, said in answers.items():
        new = mid not in before
        if b"240" in said and mid not in held:
            return f"{mid.decode()}, answered 240, is not found"
        refused = new and said.count(b"441") == len(said)
        if said.count(b"240") > new or (refused and not failing):
            return f"{mid.decode()} was answered {said}, the spool holding it before: {not new}"
        if refused and mid in held:
            return f"{mid.decode()}, refused each time it was posted, is found"
    if not halted and not failing:
        files = {R.name_of("a", c[0]) for c in commits}
        stray = [n for n in image if n != b"journal" and n not in files
                 and (R.name_kind(n) or ("",))[0] not in ("quarantine", "tail")]
        if stray:
            return f"after a run not stopped the spool holds {stray}"
    return next(filter(None, (unlike(c, image, posted) for c in commits)), None) or numbering(commits)


def after_start(image: dict[bytes, bytes], now: dict[bytes, bytes]) -> dict[bytes, bytes]:
    """The directory a start on `image` leaves: recovery_ref's actions, then a start record, under
    the key of the journal `now` holds when the start made it."""
    _, _, end, _, _, actions = R.recover(KEY, GROUPS, list(image.items()))
    at = J.HEADER + len(J.MAGIC)
    key = now.get(b"journal", b"")[at:at + J.KEY]
    actions = [f"create:{key.hex()}" if a.startswith("create:") else a for a in actions]
    expected = dict(R.apply(list(image.items()), actions))
    expected[b"journal"] = expected.get(b"journal", b"") + J.frame(key, end, J.START, b"")
    return expected


def restarted(binary: Path, image: dict[bytes, bytes], where: Path, posted: dict[bytes, bytes],
              mark: bytes = b"") -> str | None:
    """What the server started again on `image`, with `mark` as the mark of a failed sync if given,
    does otherwise than 0005 says, if anything: it listens, `nntplib` reads each article the spool
    holds, with its Xref, and finds no other; it takes `AFTER`, numbered on, and refuses an article
    held; it leaves the directory `after_start` gives, the mark removed, with that article after it,
    on which a start has nothing more to do."""
    commits = R.recover(KEY, GROUPS, list(image.items()))[3]
    nntplib = N.import_nntplib()
    spool, run = laid(where, {**image, MARK: mark} if mark else image)
    again = [(AFTER, TEXTS["posted"]), *((posted[c[1]], TEXTS["failed"]) for c in commits[-1:])]
    got: list[list[bytes]] = [[] for _ in again]
    try:
        with N.serving(N.Build(binary, binary, TIMEOUT), False, *options(spool, run)[6:], traced=False) as server, \
                nntplib.NNTP("127.0.0.1", server.port, timeout=TIMEOUT) as news:
            for c in commits:
                unstuffed = [line[1:] if line.startswith(b".") else line
                             for line in lines_of(text_of(image[R.name_of("a", c[0])], c))]
                held = c[1].decode()
                resp, info = news.article(held)
                if resp != f"220 0 {held}" or info.lines != unstuffed:
                    return f"ARTICLE {held} answered {resp!r}, {info.lines[:8]}, not {unstuffed[:8]}"
            for lacked in posted.keys() - {c[1] for c in commits}:
                try:
                    news.stat(lacked.decode())
                except nntplib.NNTPTemporaryError as error:
                    if str(error).startswith("430"):
                        continue
                return f"{lacked.decode()}, which the spool lacks, is found"
            for (post, _), lines in zip(again, got, strict=True):
                converse(server.port, Part(post), threading.Barrier(1), lines)
    except nntplib.NNTPError as error:
        return f"nntplib: {error}"
    except LaneError as error:
        return f"started again: {error}"
    for (post, answer), lines in zip(again, got, strict=True):
        if not read_as(lines, posting(answer), False):
            return f"started again, a client posting {mid_of(post).decode()} read {b''.join(lines)!r}"
    now = spool_of(spool)
    expected = after_start(image, now)
    added = sorted(now.keys() - expected.keys())
    if (len(added) != 1 or not now.get(b"journal", b"").startswith(expected[b"journal"])
            or any(now.get(n) != d for n, d in expected.items() if n != b"journal")):
        return f"after a start and a post the spool holds {sorted(now)}, not what recovery_ref's actions leave"
    try:
        _, _, _, later, _, actions = R.recover(KEY, GROUPS, list(now.items()))
    except R.Corrupt as why:
        return f"after a start and a post: corrupt {why}"
    if actions:
        return "a start after a start has something to do"
    if len(later) != len(commits) + 1 or later[:-1] != commits or R.name_of("a", later[-1][0]) != added[0]:
        return f"after a start the spool holds {later[len(commits):]}, not the article posted"
    return unlike(later[-1], now, {mid_of(AFTER): AFTER}) or numbering(later)


def one(binary: Path, phase: Phase, base: dict[bytes, bytes], stop: int) -> tuple[bool, dict[bytes, bytes]]:
    """A run stopped before operation `stop`, held to 0005: whether it stopped, and the spool left."""
    with tempfile.TemporaryDirectory() as temp:
        halted, got, image = served(binary, phase, base, f"enable name=dn/stop,failinfo={stop}", Path(temp, "first"))
        why = (violation(phase, base, image, got, halted)
               or restarted(binary, image, Path(temp, "again"), phase.posted()))
    if why:
        raise LaneError(f"{phase.name}, {'stopped before operation ' + str(stop) if halted else 'not stopped'}: {why}")
    return halted, image


def sweep(phase: Phase, stopped_at: Callable[[int], tuple[bool, dict[bytes, bytes]]]) -> tuple[int, dict[bytes, bytes]]:
    """The phase stopped before each of its operations by `stopped_at`, `WORKERS` runs at a time,
    until a run is not stopped: how many operations it makes, and the spool the run not stopped left."""
    with ThreadPoolExecutor(lanes.WORKERS) as pool:
        first = 1
        while True:
            batch = list(range(first, first + lanes.WORKERS))
            runs = list(pool.map(stopped_at, batch))
            ran = [halted for halted, _ in runs]
            if all(ran):
                first += len(batch)
                continue
            count = batch[ran.index(False)] - 1
            if count == 0:
                raise LaneError(f"{phase.name}: the server was never stopped")
            if any(ran[ran.index(False):]):
                raise LaneError(f"{phase.name}: the server made {count} operations in one run, more in another")
            return count, runs[ran.index(False)][1]


def phases(binary: Path, bases: list[dict[bytes, bytes]] | None = None) -> tuple[list[int], list[dict[bytes, bytes]]]:
    """Each phase swept, on the spool the phase before left, the last on it as a crash leaves it, or
    on `bases`: the operations of each, and the spools they started on."""
    counts: list[int] = []
    used: list[dict[bytes, bytes]] = []
    left: dict[bytes, bytes] = {}
    for k, phase in enumerate(PHASES):
        base = bases[k] if bases else crashed(left) if phase is PHASES[-1] else left
        count, left = sweep(phase, functools.partial(one, binary, phase, base))
        counts.append(count)
        used.append(base)
    return counts, used


@dataclass
class Defect:
    """A defect planted in the program (a pattern) or in native/jobs.c (exact text), with how many
    times the text occurs, and a part of what the lane has to say of it."""
    name: str
    pattern: str
    becomes: str
    times: int
    sign: str
    program: bool = True


DEFECTS = [
    Defect("a file taken as placed once it is closed", r"(if all \{\n\s+st zs \+ 160, )2;", r"\g<1>4;", 1,
           "corrupt missing-file"),
    Defect("a temporary file left at start", r"if rk == 3 \{", "if 0 {", 1, "not what recovery_ref's actions leave"),
    Defect("a final file no commit names kept at start", r"if rok \{(\n\s+st rsc, 1;)", r"if 1 {\1", 1,
           "not what recovery_ref's actions leave"),
    Defect("the test build's stop never made", "hold(stop);", "(void)hold;", 1, "the server was never stopped",
           program=False),
    Defect("a rename that keeps the temporary name", "renameat(spool, name, spool, to)",
           "linkat(spool, name, spool, to, 0)", 1, "after a start and a post the spool holds", program=False),
]


FIU: list[Path] = []
FIU_ASKED = threading.Lock()


def fiu() -> Path:
    """libfiu, asked for once by a lane however many servers it builds and runs side by side."""
    with FIU_ASKED:
        if not FIU:
            FIU.append(lanes.pinned_tool("libfiu"))
        return FIU[0]


def test_build(cake: str, out: Path, name: str, source: str, defect: Defect | None = None,
               base: Path | None = None) -> Path:
    """The server's test build of the program `source`, as `name` in `out`, which holds the layout's
    header; with `defect`, planted in the program, or in native/jobs.c linked with `base`'s program."""
    flags = ["-DFIU_ENABLE=1", f"-I{fiu()}", f"-L{fiu()}", "-lfiu", f"-Wl,-rpath,{fiu()}"]
    if defect is None or defect.program:
        text = source if defect is None else lanes.plant(source, defect.pattern, defect.becomes, defect.times,
                                                          f"the program, for {defect.name},")
        return lanes.whole_program(cake, name, text, out, N.HOST, N.STORE, flags)
    if base is None:
        raise LaneError(f"{defect.name}: a defect of the host needs a program")
    jobs = out / f"{name}-jobs.c"
    jobs.write_text(lanes.plant(JOBS.read_text(), defect.pattern, defect.becomes, defect.times,
                                f"the host, for {defect.name},", exact=True))
    return lanes.link(out / name, [N.HOST, NATIVE / "store.c", jobs, NATIVE / "cake_header.c",
                                   NATIVE / "cake_runtime.c", base.with_suffix(".S")],
                      includes=[out], flags=flags, check=False)


def check(cake: str) -> Report:
    if sys.version_info[:2] != (3, 12):
        raise LaneError(f"this lane needs the nntplib of Python 3.12, not Python {sys.version.split()[0]}")
    OUT.mkdir(parents=True, exist_ok=True)
    (OUT / "dn_session_layout.h").write_text(lanes.emit("emit-session-layout"))
    source = lanes.emit("emit-session")
    with ThreadPoolExecutor(lanes.WORKERS) as pool:
        base = pool.submit(test_build, cake, OUT, "crash", source)
        builds = [pool.submit(test_build, cake, OUT, f"defect-{k}", source, d) for k, d in enumerate(DEFECTS)
                  if d.program]
        clock = time.monotonic()
        counts, bases = phases(base.result())
        seconds = {"runs": round(time.monotonic() - clock, 1)}
        found = {}
        programs = iter(builds)
        for k, defect in enumerate(DEFECTS):
            binary = (next(programs).result() if defect.program
                      else test_build(cake, OUT, f"defect-{k}", source, defect, base.result()))
            try:
                phases(binary, bases)
            except LaneError as error:
                if defect.sign not in str(error):
                    raise LaneError(f"{defect.name} was caught, but not as {defect.sign!r}: {error}") from None
                found[defect.name] = str(error)[:300]
                continue
            raise LaneError(f"{defect.name} passed")
        seconds["defects"] = round(time.monotonic() - clock - seconds["runs"], 1)
    lanes.require_quoted({"docs/baseline.md": [
        f"{counts[0]}, {counts[1]} and {counts[2]} operations", f"{len(DEFECTS)} planted defects of the crash lane"]})
    return Report("checked", cake, [N.HOST, *N.STORE], {
        "executable_sha256": lanes.digest(base.result()),
        "operations": dict(zip((p.name for p in PHASES), counts, strict=True)), "seconds_by_step": seconds,
        "planted_defects_caught": found})


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--cake", default=os.environ.get("CAKE"))
    args = parser.parse_args()
    lanes.require_platform(parser)
    cake = lanes.given_cake(parser, args.cake)
    lanes.lane_main("CRASH", OUT, lambda: check(cake))


if __name__ == "__main__":
    main()
