#!/usr/bin/env python3
# SPDX-License-Identifier: AGPL-3.0-or-later
"""The faults lane: the crash lane's server (scripts/crash_check.py) on a spool holding an article,
and on that spool as a crash leaves it, its clients one after another, each on a connection of its
own: an article posted, ARTICLE of the one held, another posted, STAT of the one held, then the
capabilities and LIST ACTIVE, POST among the first and `y` in the second only while the store accepts.

- Each operation failed once with ENOSPC at its first point (`dn/fail`): every reply as in a run
  without the failure until it, then as decision 0005 has it for the point and the file: an
  article's creation, write or rename refuses the post, 441, and the store goes on; its sync, close
  or directory's sync refuses it, and the store stops accepting (201, 440), the mark of a failed
  sync left in the spool and the run directory; the journal's write or sync closes the connection
  unanswered and stops the store, its sync leaving the mark; an opening or a read of the article
  answers 403 and the store goes on; a failure at the start ends it with status 4, recovery failed
  of no space. Every point but `dn/read-dir`, which a listing reaches only past `dn/open-dir`, fails
  in some run, and the stop's counters count the one failed file job, for want of space.
- Each operation interrupted once (EINTR): where the host makes the call again, the run as without
  it, no file job failed, and as a failure where it does not, counted as failing otherwise.
- Every write cut to one octet: the run as without it; a write of no progress: the start refused, of
  no space.
- Each index's generations counted up to the last but one (`dn/generation`): every client opens at
  the last generation of an index and the next at another, the run as without it.
- SIGTERM as each operation begins (`dn/term`): the job running it run out before the server ends,
  with status 0, the spool held as after a crash and served again.
- Every index taken at once, a 65th connection waiting; slow reads of the large article, posts with
  slowed syncs and HELP on the rest: all answered, nothing allocated once the server serves, at most
  `RESIDENT` kB resident and `GROWTH` more than as it began to serve.
- A poll that fails (`dn/poll`): the host ends with status 2.
- Every sync slowed by `SLOW` seconds: an article read and a STAT on other connections answered
  before a post's 240, which comes after its three syncs.

Each spool left recovers by scripts/recovery_ref.py, not corrupt, with the article held before and
each one answered 240, as sent, none refused, and nothing else but what recovery sets aside and the
file of a commit unanswered;
started again, on a mark of another boot, the server does as the crash lane holds it to.

An article's file, of one buffer read and of two, changed after the start as the table of
corruptions `fn` keeps has it (`CHANGES`): ARTICLE, HEAD and BODY answered 403, or, a change past the
first buffer, the start of the reply and the connection closed; STAT 223; a post taken; started
again, refused where recovery_ref finds the spool corrupt, recovery failed where the file opens no
more, and else the article still not sent whole.

Each defect of `DEFECTS`, planted in the program or the host, has to be caught for the reason named.
"""
from __future__ import annotations

import argparse
from collections.abc import Callable
from dataclasses import dataclass
import errno
import fcntl
import json
import os
from pathlib import Path
import queue
import re
import signal
import socket
import struct
import subprocess
import sys
import tempfile
import termios
import threading
import time
from typing import BinaryIO

sys.path.insert(0, str(Path(__file__).resolve().parent))
import crash_check as C  # the path above is what makes these importable
import lanes
from lanes import ROOT, LaneError, Report
import nntp_check as N
import recovery_ref as R
import session_native
import store_ref as J

OUT = ROOT / "build/faults"
TEXTS = C.TEXTS
SLOW = 1.0
HELD = C.article("<held@x.example>", "local.a")
LARGE = C.article("<large@x.example>", "local.b", lines=300)
POSTS = [C.article("<first@x.example>", "local.a,local.b"), C.article("<second@x.example>", "local.c", lines=300)]
Image = dict[bytes, bytes]
# A client's step: its command, and the article it posts after a 340.
Step = tuple[bytes, bytes]
READ, STAT = b"ARTICLE <held@x.example>\r\n", b"STAT <held@x.example>\r\n"
STEPS: list[Step] = [(b"POST\r\n", POSTS[0]), (READ, b""), (b"POST\r\n", POSTS[1]), (STAT, b""),
                     (b"CAPABILITIES\r\n", b""), (b"LIST ACTIVE\r\n", b"")]
# LIST ACTIVE, the last step, lists the articles the run leaves, which `judged` holds it to.
LISTING = len(STEPS) - 1
# What a failure does, by its point and the file of its operation, among the outcomes of `expected`.
OUTCOMES = {("dn/create", "article"): "refused", ("dn/write", "article"): "refused",
            ("dn/rename", "article"): "refused", ("dn/data-sync", "article"): "stopped",
            ("dn/close", "article"): "stopped", ("dn/sync-dir", "article"): "stopped",
            ("dn/write", "journal"): "lost", ("dn/data-sync", "journal"): "lost",
            ("dn/open", "read"): "unread", ("dn/read", "read"): "unread", ("dn/close", "read"): "none"}
SYNCS = {"dn/sync", "dn/data-sync", "dn/sync-dir"}
# The files of the operations of `STEPS` after the start, in turn.
ORDER = ["article", "journal", "read", "article", "journal"]
# The points whose calls the host makes again when a signal interrupts them.
RETRIED = {"dn/create", "dn/open", "dn/open-dir", "dn/write", "dn/read", "dn/data-sync", "dn/sync", "dn/sync-dir",
           "dn/truncate", "dn/rename", "dn/remove"}


def reply(f: BinaryIO) -> list[bytes]:
    """A reply's lines: its first and, after 101, 215, 220, 221 or 222, its text to the line of a dot,
    or what came of it before the server stopped."""
    lines = [f.readline()]
    while lines[0][:3] in (b"101", b"215", b"220", b"221", b"222") and lines[-1].endswith(b"\r\n") and \
            (len(lines) == 1 or lines[-1] != b".\r\n"):
        lines.append(f.readline())
    return lines


def talk(port: int, command: bytes, post: bytes = b"") -> list[bytes]:
    """A client: the greeting, `command` and its reply, after a 340 the article `post` and its reply,
    QUIT and its reply; each line read, the last one empty or cut short where the server stopped."""
    got: list[bytes] = []
    try:
        with socket.create_connection(("127.0.0.1", port), timeout=C.TIMEOUT) as s, s.makefile("rb") as f:
            for k, send in enumerate((b"", command, post, b"QUIT\r\n")):
                if k == 2 and not got[-1].startswith(b"340"):
                    continue
                if send:
                    s.sendall(send)
                got += reply(f)
                if not got[-1].endswith(b"\r\n"):
                    break
    except OSError:
        pass
    return got


def image_of(spool: Path) -> Image:
    """The spool's files, without what is no file."""
    return {os.fsencode(f.name): f.read_bytes() for f in spool.iterdir() if f.is_file() and not f.is_symlink()}


@dataclass
class Run:
    started: bool
    status: int
    said: str
    got: list[list[bytes]]
    image: Image
    marks: list[str]

    def failed(self) -> list[str]:
        """The points `dn/fail` failed."""
        return [line.split()[1] for line in self.said.splitlines() if line.startswith("dn/fail ")]


def served(binary: Path, base: Image, where: Path, enable: str = "", steps: list[Step] = STEPS,
           during: Callable[[int, Path], list[list[bytes]]] | None = None, laid: bool = True,
           more: tuple[str, ...] = ()) -> Run:
    """The server with the points `enable` names and the options `more` on a spool holding `base`,
    or, not `laid`, on the spool `where` holds, its clients taking `steps` in turn, or `during` doing
    what it does given the port and the spool; ended by SIGTERM once done."""
    spool, run = C.laid(where, base) if laid else (where / "spool", where / "run")
    env = {k: v for k, v in os.environ.items() if not k.startswith("FIU_")}
    if enable:
        env |= {"LD_PRELOAD": str(C.fiu() / "fiu_run_preload.so"), "FIU_ENABLE": enable}
    err = where / "stderr"
    got: list[list[bytes]] = []
    port: str | None = None
    with err.open("w") as said, subprocess.Popen([str(binary), *C.options(spool, run), *more], stdout=subprocess.PIPE,
                                                 stderr=said, text=True, env=env) as proc:
        try:
            try:
                port = lanes.Lines(N.Server.pipe(proc.stdout)).get(C.TIMEOUT)
            except queue.Empty:
                raise LaneError(f"the server gave no port in {C.TIMEOUT} s") from None
            if port is not None:
                at = int(json.loads(port)["port"])
                got = during(at, spool) if during else [talk(at, *s) for s in steps]
                # A refused post's temporary file goes by a job its 441 does not wait for: the store's
                # last jobs are given their time before the stop, and a file still there is held.
                settled = time.monotonic() + C.TIMEOUT
                while any(f.name.startswith("t") for f in spool.iterdir()) and time.monotonic() < settled and \
                        proc.poll() is None:
                    time.sleep(0.01)
                proc.send_signal(signal.SIGTERM)
            status = proc.wait(C.TIMEOUT)
        finally:
            if proc.poll() is None:
                proc.kill()
            proc.wait()
    marks = [d.name for d in (spool, run) if (d / os.fsdecode(C.MARK)).exists()]
    image = image_of(spool)
    image.pop(C.MARK, None)
    text = err.read_text()
    if port is not None and (status != 0 or "stopped: a signal" not in text):
        raise LaneError(f"on SIGTERM the server ended with status {status}: {text[-300:]!r}")
    return Run(port is not None, status, text, got, image, marks)


def replies(base: Image) -> list[bytes]:
    """The lines ARTICLE of the article `base` holds is answered with."""
    commit = R.recover(C.KEY, C.GROUPS, list(base.items()))[3][0]
    text = C.text_of(base[R.name_of("a", commit[0])], commit)
    return [b"220 0 " + commit[1] + b"\r\n", *(line + b"\r\n" for line in C.lines_of(text)), b".\r\n"]


def listed(commits: list[J.Commit], accepting: bool) -> list[bytes]:
    """LIST ACTIVE of the groups as a store holding `commits` gives it: each group's highest and lowest
    numbers, and `y` while it accepts."""
    numbers = {g: [n for c in commits for name, n in c[2] if name == g] for g in C.GROUPS}
    return [b"215 List of newsgroups follows\r\n",
            *(b"%s %d %d %s\r\n" % (g, max(ns, default=0), min(ns, default=1), b"y" if accepting else b"n")
              for g, ns in numbers.items()), b".\r\n"]


def expected(base: Image, outcome: str = "none", at: int = -1) -> list[list[bytes]]:
    """What each client of `STEPS` but the last reads on a spool holding `base` when step `at` meets
    `outcome`: none, a post refused, a post refused and the store stopped, a post unanswered and the
    store stopped, or an article unread."""
    rows: list[list[bytes]] = []
    stopped = False
    for k, (command, post) in enumerate(STEPS[:LISTING]):
        greeting, quit = TEXTS["greeting" if stopped else "greeting-post"], TEXTS["quit"]
        if command.startswith(b"CAPABILITIES"):
            text = TEXTS["capabilities-reader" if stopped else "capabilities-post"]
            rows.append([greeting, *(line + b"\r\n" for line in text.split(b"\r\n")[:-1]), quit])
        elif post and stopped:
            rows.append([greeting, TEXTS["not-permitted"], quit])
        elif post:
            answer = ([TEXTS["failed"], quit] if k == at and outcome in ("refused", "stopped")
                      else [b""] if k == at and outcome == "lost" else [TEXTS["posted"], quit])
            rows.append([greeting, TEXTS["post"], *answer])
        elif command.startswith(b"STAT"):
            rows.append([greeting, b"223 0 <held@x.example>\r\n", quit])
        else:
            rows.append([greeting, *([TEXTS["unreadable"]] if k == at and outcome == "unread" else replies(base)),
                         quit])
        stopped |= k == at and outcome in ("stopped", "lost")
    return rows


def answered(run: Run, base: Image, retried: bool, cls: str, role: str, counter: int = -1) -> tuple[str, str | None]:
    """The outcome of `run`, an operation on the file of `role` failed or interrupted at its point,
    and what of it 0005 does not allow, if anything; with `retried`, the host made the call again,
    so nothing happened. With `counter`, the stop counts one failed file job, there among those that
    failed for want of space, on an I/O error and otherwise, or none if nothing failed."""
    failed = run.failed()
    point = failed[0] if failed else ""
    marked = run.marks == ["spool", "run"]
    if len(failed) > 1 or (run.marks and not marked):
        return "", f"dn/fail failed {failed}, marks left in {run.marks}"
    if not run.started:
        if not point or retried:
            return "", f"the server ended at its start with status {run.status}: {run.said[-200:]!r}"
        if run.status != 4 or f"recovery failed: a file job failed, class {cls}\n" not in run.said:
            return "", f"{point} failing at the start ended it with status {run.status}: {run.said[-200:]!r}"
        return "start", (f"{point} failing at the start left marks in {run.marks}"
                         if marked != (point in SYNCS or role == "start written") else None)
    at = next((k for k, (got, row) in enumerate(zip(run.got[:LISTING], expected(base), strict=True))
               if got != row), -1)
    outcome = "none" if retried or not point else OUTCOMES.get((point, role), "")
    what = f"{point or 'nothing'} on the {role or 'no'} file failing"
    if not outcome:
        return "", f"{what}, which 0005 does not expect"
    if counter >= 0:
        failures = N.counted(run.said, "at the stop")[8:]
        if failures != [int(point != "" and not retried and k == counter) for k in range(3)]:
            return "", f"{what}, the stop counted {failures} failed file jobs"
    if (outcome == "none") != (at < 0) or run.got[:LISTING] != expected(base, outcome, at):
        step = STEPS[max(at, 0)][0].decode().strip()
        return "", f"{what}, the client of {step} read {b''.join(run.got[max(at, 0)])[-200:]!r}, not as {outcome}"
    if marked != (not retried and (point in SYNCS or (point, role) == ("dn/close", "article"))):
        return outcome, f"{what}, the run answered as it may and left marks in {run.marks}"
    return outcome, None


def judged(run: Run, base: Image, binary: Path, where: Path, retried: bool = False, cls: str = "",
           role: str = "", counter: int = -1) -> str | None:
    """What `run`, an operation on the file of `role` failed or interrupted, does otherwise than 0005
    says, if anything."""
    outcome, why = answered(run, base, retried, cls, role, counter)
    if why:
        return why
    try:
        commits = R.recover(C.KEY, C.GROUPS, list(run.image.items()))[3]
    except R.Corrupt as error:
        return f"corrupt {error}"
    before = R.recover(C.KEY, C.GROUPS, list(base.items()))[3]
    # The store serves the articles it held and those it answered 240; a commit whose append failed
    # may be in the journal, unanswered and not served.
    taken = {C.mid_of(post) for (_, post), got in zip(STEPS, run.got, strict=False)
             if post and got[2:3] == [TEXTS["posted"]]}
    serving = [c for c in commits if c[1] in taken or any(c[1] == b[1] for b in before)]
    stopped = outcome in ("stopped", "lost")
    listing = [TEXTS["greeting" if stopped else "greeting-post"], *listed(serving, not stopped), TEXTS["quit"]]
    if run.started and run.got[LISTING] != listing:
        return f"LIST ACTIVE read {b''.join(run.got[LISTING])[-200:]!r}, not {b''.join(listing)[-200:]!r}"
    held = {c[1]: c for c in commits}
    if any(held.get(c[1]) != c or run.image.get(R.name_of("a", c[0])) != base[R.name_of("a", c[0])] for c in before):
        return "the article held before is not held as it was"
    for (_, post), got in zip(STEPS, run.got if run.started else [], strict=False):
        mid = C.mid_of(post) if post else b""
        if got[2:3] in ([TEXTS["posted"]], [TEXTS["failed"]]) and (mid in held) != (got[2] == TEXTS["posted"]):
            return f"{mid.decode()}, answered {got[2]!r}, is held: {mid in held}"
    files = {R.name_of("a", c[0]) for c in commits}
    # A start that failed may leave any name it found.
    stray = [n for n in run.image if n != b"journal" and n not in files and (run.started or n not in base)
             and (R.name_kind(n) or ("",))[0] not in ("quarantine", "tail")
             and not (outcome == "lost" and (R.name_kind(n) or ("",))[0] == "final")]
    if stray:
        return f"the spool holds {stray}"
    posted = {C.mid_of(p): p for p in (HELD, *POSTS)}
    return (next(filter(None, (C.unlike(c, run.image, posted) for c in commits)), None)
            or C.restarted(binary, run.image, where / "again", posted, C.OTHER_BOOT if run.marks else b""))


def roles(points: list[str], started: list[bool]) -> list[str]:
    """The file each operation of a sweep is on, by their order in a run, one at a time: the start's,
    its close of a file written "start written"; an article's from its creation; the journal's once
    the article's name is synced; a read's from its opening."""
    role, found, wrote = "", [], False
    for point, up in zip(points, started, strict=True):
        wrote = point in ("dn/write", "dn/truncate") or (wrote and point not in ("dn/create", "dn/open"))
        if not up:
            found.append("start written" if point == "dn/close" and wrote else "start")
            continue
        if point in ("dn/create", "dn/open"):
            role = "article" if point == "dn/create" else "read"
        found.append(role)
        if point == "dn/sync-dir" and role == "article":
            role = "journal"
    return found


def swept(binary: Path, base: Image, error: int, cls: str,
          files: list[str] | None = None) -> tuple[list[str], list[str]]:
    """Each operation failed once with `error` in a run of its own, `WORKERS` at a time, until two in
    a row fail nothing (a listing's close fails at no point), on the files of `ORDER`; each run
    held to 0005 for its point and the file it is on, by `roles` or as `files` gives: the point of
    each operation, and its file."""
    with tempfile.TemporaryDirectory() as temp, lanes.pool() as pool:

        def failed_at(k: int) -> Run:
            return served(binary, base, Path(temp, str(k)), f"enable name=dn/fail,failinfo={k * 256 + error}")

        runs: list[Run] = []
        while (end := next((k for k in range(len(runs) - 1) if not runs[k].failed() and not runs[k + 1].failed()),
                           None)) is None:
            runs += pool.map(failed_at, range(len(runs) + 1, len(runs) + 1 + lanes.WORKERS))
        points = [(run.failed() or [""])[0] for run in runs[:end]]
        if files is None:
            files = roles(points, [run.started for run in runs[:end]])
        order = [f for k, f in enumerate(files) if not f.startswith("start") and f and (k == 0 or f != files[k - 1])]
        if order != ORDER or points[-1:] != ["dn/data-sync"] or len(files) != end:
            raise LaneError(f"{errno.errorcode[error]}: {end} operations, on the files of {order}, the last at "
                            f"{points[-1:]}, not the sync of the last commit")

        def judge(k: int) -> str | None:
            why = judged(runs[k], base, binary, Path(temp, str(k + 1)), error == errno.EINTR and points[k] in RETRIED,
                         cls, files[k], 0 if error == errno.ENOSPC else 2)
            return f"operation {k + 1} {errno.errorcode[error]}: {why}" if why else None

        why = next(filter(None, pool.map(judge, range(end))), None)
    if why:
        raise LaneError(why)
    return points, files


def cut(binary: Path, base: Image, no_space: str) -> None:
    """Every write cut to one octet, written on: the run as without it; a write of no progress: the
    start refused, of no space."""
    with tempfile.TemporaryDirectory() as temp:
        run = served(binary, base, Path(temp, "first"), "enable name=dn/write-short,failinfo=1")
        why = judged(run, base, binary, Path(temp), retried=True)
        if why:
            raise LaneError(f"every write cut to one octet: {why}")
        run = served(binary, base, Path(temp, "none"), "enable name=dn/write-short,failinfo=0")
        if run.started or run.marks or run.status != 4 or \
                f"recovery failed: a file job failed, class {no_space}\n" not in run.said:
            raise LaneError(f"a write of no progress: the server started {run.started}, status {run.status}, marks "
                            f"{run.marks}: {run.said[-200:]!r}")


def spent(binary: Path, base: Image, limit: int) -> None:
    """Each index's generations counted up to the last but one as a connection opens there
    (`dn/generation`): every client opens at the last generation of an index, the next at another,
    and the run is as without it."""
    with tempfile.TemporaryDirectory() as temp:
        try:
            run = served(binary, base, Path(temp, "spent"), f"enable name=dn/generation,failinfo={limit - 1}")
            why = judged(run, base, binary, Path(temp))
        except LaneError as error:
            why = str(error)
        if why:
            raise LaneError(f"every index at its last generation: {why}")


def terminated(binary: Path, base: Image, count: int) -> None:
    """SIGTERM as each of the run's `count` operations begins (`dn/term`): the server ends with status
    0 once the job running that operation has run out, none left running; the spool recovers, not
    corrupt, with the article held before and each one answered 240, as sent; started again, it
    serves them."""
    posted = {C.mid_of(p): p for p in (HELD, *POSTS)}
    for n in range(1, count + 1):
        with tempfile.TemporaryDirectory() as temp:
            run = served(binary, base, Path(temp, "term"), f"enable name=dn/term,failinfo={n}")
            stop = re.search(r"at the stop: (\d+) jobs run out, (\d+) dropped before they began, (\d+) still running",
                             run.said)
            if stop is None or stop[1] == "0" or stop[3] != "0":
                raise LaneError(f"SIGTERM at operation {n}: the server said {run.said[-300:]!r}")
            try:
                commits = R.recover(C.KEY, C.GROUPS, list(run.image.items()))[3]
            except R.Corrupt as error:
                raise LaneError(f"SIGTERM at operation {n}: corrupt {error}") from None
            taken = {C.mid_of(post) for (_, post), got in zip(STEPS, run.got, strict=False)
                     if post and got[2:3] == [TEXTS["posted"]]}
            held = {c[1] for c in commits}
            why = (next((f"{m.decode()}, answered 240, is not held" for m in taken | {C.mid_of(HELD)} if m not in held),
                        None)
                   or next(filter(None, (C.unlike(c, run.image, posted) for c in commits)), None)
                   or C.restarted(binary, run.image, Path(temp, "again"), posted))
            if why:
                raise LaneError(f"SIGTERM at operation {n}: {why}")


# The most a load may add, in kB, to what the server held resident as it began to serve, about 4 MB:
# the program's heap and stack, 5 MiB allocated at start and touched as it runs, and a megabyte more.
GROWTH = 6_144
# The server's send buffer and a slow reader's receive buffer: the large article does not fit in both,
# so the server holds the rest until the reader takes more.
SEND_BUFFER, RECEIVE_BUFFER = 4_096, 4_096


def poll_fails(binary: Path, base: Image) -> None:
    """A poll that fails but by a signal (`dn/poll`, ENOMEM), the first as the start waits for its
    jobs: the host ends with status 2, as a fault of what it runs on, naming the poll, rather than
    wait on without its timer."""
    with tempfile.TemporaryDirectory() as temp:
        run = served(binary, base, Path(temp), f"enable name=dn/poll,failinfo={errno.ENOMEM}")
    if run.started or run.status != 2 or "poll: Cannot allocate memory" not in run.said:
        raise LaneError(f"a poll that fails: the server started {run.started}, ended with status {run.status}: "
                        f"{run.said[-200:]!r}")


def spool_files(spool: Path) -> list[str]:
    """The descriptors any process of this user holds on a file of the spool but the journal."""
    held = []
    for fd in Path("/proc").glob("[0-9]*/fd/*"):
        try:
            target = str(fd.readlink())
        except OSError:
            continue
        if target.startswith(f"{spool}/") and not target.endswith("/journal"):
            held.append(target)
    return held


def bounded(binary: Path, base: Image) -> dict[str, int]:
    """Every index taken at once: a 65th connection is greeted only once one of them closes; then
    eight reads of the large article taken slowly through small buffers, so that the server holds what
    they have not taken, one reset midway, whose file the server then closes; eight posts with every
    sync slowed, and HELP on the rest, all answered. The allocator holds no more once the server
    serves than as it began to, and the server holds at most `GROWTH` kB more resident."""
    large = b"ARTICLE " + C.mid_of(LARGE) + b"\r\n"
    held: list[list[str]] = []
    queued: list[int] = []

    def connected(port: int, k: int) -> socket.socket:
        c = socket.socket()
        if k < 8:
            c.setsockopt(socket.SOL_SOCKET, socket.SO_RCVBUF, RECEIVE_BUFFER)
        c.settimeout(C.TIMEOUT)
        c.connect(("127.0.0.1", port))
        return c

    def during(port: int, spool: Path) -> list[list[bytes]]:
        conns = [connected(port, k) for k in range(64)]
        files = [c.makefile("rb") for c in conns]
        greeted = [f.readline() for f in files]
        extra = socket.create_connection(("127.0.0.1", port), timeout=0.5)
        try:
            early = extra.recv(1)
        except TimeoutError:
            early = b""
        files[63].close()
        conns[63].close()
        extra.settimeout(C.TIMEOUT)
        conns[63], files[63] = extra, extra.makefile("rb")
        greeted[63] = files[63].readline()
        got: list[list[bytes]] = [[g] for g in greeted]

        def client(k: int) -> None:
            c, f = conns[k], files[k]
            if k == 7:
                # A reader gone mid-article, its connection reset: its read's job runs on.
                c.sendall(large)
                got[k] += [f.readline(), b".\r\n"]
                c.setsockopt(socket.SOL_SOCKET, socket.SO_LINGER, struct.pack("ii", 1, 0))
                # The socket closes only once its file object, which holds it too, is closed.
                f.close()
                c.close()
                return
            if k < 8:
                c.sendall(large)
                lines = [f.readline()]
                time.sleep(0.2)
                # What the kernel queued for the reader once the server has sent all it could.
                queued.append(int(struct.unpack("i", fcntl.ioctl(c.fileno(), termios.FIONREAD, b"\0" * 4))[0]))
                while lines[-1] not in (b".\r\n", b""):
                    lines.append(f.readline())
                    if len(lines) % 16 == 0:
                        time.sleep(0.01)
                got[k] += [lines[0], lines[-1]]
            elif k < 16:
                c.sendall(b"POST\r\n")
                got[k].append(f.readline())
                c.sendall(C.article(f"<bound{k}@x.example>", "local.a"))
                got[k].append(f.readline())
            else:
                c.sendall(b"HELP\r\n")
                lines = [f.readline()]
                while lines[-1] not in (b".\r\n", b""):
                    lines.append(f.readline())
                got[k].append(lines[0])
            c.sendall(b"QUIT\r\n")
            got[k].append(f.readline())
            c.close()

        threads = [threading.Thread(target=client, args=(k,)) for k in range(64)]
        for t in threads:
            t.start()
        for t in threads:
            t.join()
        settled = time.monotonic() + C.TIMEOUT
        while spool_files(spool) and time.monotonic() < settled:
            time.sleep(0.01)
        held.append(spool_files(spool))
        return [[early], *got]

    with tempfile.TemporaryDirectory() as temp:
        run = served(binary, base, Path(temp), "enable name=dn/sync-slow,failinfo=100", during=during,
                     more=("--send-buffer", str(SEND_BUFFER)))
    if run.got[0] != [b""]:
        raise LaneError(f"a 65th connection was greeted while 64 were open: {run.got[0]}")
    for k, lines in enumerate(run.got[1:]):
        if k == 7:
            if [line[:3] for line in lines[:2]] != [TEXTS["greeting-post"][:3], b"220"]:
                raise LaneError(f"the reader that reset read {lines}")
            continue
        want = (TEXTS["greeting-post"][:3],
                b"220" if k < 8 else b"340" if k < 16 else b"100",
                b".\r\n" if k < 8 else TEXTS["posted"] if k < 16 else None, b"205")
        seen = (lines[0][:3], lines[1][:3], lines[2] if k < 16 else None, lines[-1][:3])
        if seen != want:
            raise LaneError(f"client {k} of 64 read {lines}")
    found = [re.search(rf"^{when}: (\d+) octets allocated, (\d+) kB resident at most$", run.said, re.MULTILINE)
             for when in ("serving", "at the stop")]
    if None in found:
        raise LaneError(f"the server did not say what it allocated: {run.said[-300:]!r}")
    (serving, began), (stop, resident) = ((int(m[1]), int(m[2])) for m in found if m)
    if stop != serving or resident > began + GROWTH:
        raise LaneError(f"the server allocated {serving} octets serving and {stop} at the stop, and held "
                        f"{began} kB resident as it began to serve and {resident} kB at most")
    article = len(LARGE)
    if len(queued) != 7 or max(queued) >= article:
        raise LaneError(f"the slow readers had {queued} octets queued of an article of {article}: the server held none")
    if held != [[]]:
        raise LaneError(f"after every client the server holds {held} of the spool open")
    return {"allocated": serving, "resident_kB": resident, "queued_max": max(queued)}


def slowed(binary: Path, base: Image) -> dict[str, float]:
    """Every sync slowed by `SLOW` s: a read and a STAT on other connections answered before a post's
    240, which comes after its three syncs; when each came."""
    took: dict[str, float] = {}

    def during(port: int, _spool: Path) -> list[list[bytes]]:
        clients = [socket.create_connection(("127.0.0.1", port), timeout=C.TIMEOUT) for _ in range(3)]
        try:
            files = [c.makefile("rb") for c in clients]
            got = [reply(f) for f in files]
            clients[0].sendall(b"POST\r\n")
            got[0] += reply(files[0])
            start = time.monotonic()
            clients[0].sendall(POSTS[0])
            for k, command in ((1, READ), (2, STAT)):
                clients[k].sendall(command)
                got[k] += reply(files[k])
                took[command.split()[0].decode()] = time.monotonic() - start
            got[0] += reply(files[0])
            took["POST"] = time.monotonic() - start
            for k, (c, f) in enumerate(zip(clients, files, strict=True)):
                c.sendall(b"QUIT\r\n")
                got[k] += reply(f)
            return got
        finally:
            for c in clients:
                c.close()

    with tempfile.TemporaryDirectory() as temp:
        run = served(binary, base, Path(temp, "first"), f"enable name=dn/sync-slow,failinfo={round(SLOW * 1000)}",
                     during=during)
    wanted = expected(base)
    if run.got != [wanted[0], wanted[1], wanted[3]]:
        raise LaneError(f"every sync slowed by {SLOW} s, the clients read {run.got}")
    if max(took["ARTICLE"], took["STAT"]) > SLOW / 2 or took["POST"] < 3 * SLOW:
        raise LaneError(f"every sync slowed by {SLOW} s, a read and a STAT were answered after {took['ARTICLE']:.2f} "
                        f"and {took['STAT']:.2f} s, a post's 240 after {took['POST']:.2f} s")
    return {k: round(v, 2) for k, v in took.items()}


def symlinked(f: Path, data: bytes) -> None:
    copy = f.parent.parent / f"copy-{f.name}"
    copy.write_bytes(data)
    f.unlink()
    f.symlink_to(copy)


def directory(f: Path, _data: bytes) -> None:
    f.unlink()
    f.mkdir()


# The ways of the table of corruptions `fn` keeps to change an article's file, each near its end.
CHANGES: dict[str, Callable[[Path, bytes], object]] = {
    "cut short": lambda f, d: f.write_bytes(d[:-1]),
    "an octet changed": lambda f, d: f.write_bytes(d[:-3] + bytes([d[-3] ^ 1]) + d[-2:]),
    "grown": lambda f, d: f.write_bytes(d + b"x"),
    "removed": lambda f, _d: f.unlink(),
    "a symlink to a copy": symlinked,
    "a directory": directory,
}
# The changes after which the file opens no more.
UNOPENED = ("removed", "a symlink to a copy", "a directory")


def unsent(what: str, got: list[bytes], was: list[bytes], first: bool) -> None:
    """That a client read of an article whose file changed what 0005 says, `was` the reading before:
    for STAT the same, and otherwise, with the change in the `first` buffer read, 403, else the
    start of the reply and the connection closed."""
    if was[1].startswith(b"223"):
        if got != was:
            raise LaneError(f"{what}: read {got}, not {was}")
    elif first:
        if got != [TEXTS["greeting-post"], TEXTS["unreadable"], TEXTS["quit"]]:
            raise LaneError(f"{what}: read {b''.join(got)[-200:]!r}, not 403")
    elif got[-1].endswith(b"\r\n") or got[1] != was[1] or not b"".join(was).startswith(b"".join(got)):
        raise LaneError(f"{what}: read {b''.join(got)[-200:]!r}, not the start of its reply cut short")


def corrupted(binary: Path, base: Image, other: str, change: str, mid: bytes) -> None:
    """The file of the article `mid` changed after the start, held to 0005 as the lane's doc says."""
    name = R.name_of("a", next(c[0] for c in R.recover(C.KEY, C.GROUPS, list(base.items()))[3] if c[1] == mid))
    asks = [(b + b" " + mid + b"\r\n", b"") for b in (b"ARTICLE", b"HEAD", b"BODY", b"STAT")]
    post = C.article(f"<after-{len(change)}@x.example>", "local.c")

    def during(port: int, spool: Path) -> list[list[bytes]]:
        before = [talk(port, *a) for a in asks]
        CHANGES[change](spool / os.fsdecode(name), base[name])
        return [*before, *(talk(port, *a) for a in asks), talk(port, b"POST\r\n", post)]

    with tempfile.TemporaryDirectory() as temp:
        where = Path(temp)
        run = served(binary, base, where, during=during)
        before, after, posted = run.got[:4], run.got[4:8], run.got[8]
        for (command, _), was, got in zip(asks, before, after, strict=True):
            unsent(f"{change}, {command.decode().strip()}", got, was, len(base[name]) < 16384 or change in UNOPENED)
        if posted != [TEXTS["greeting-post"], TEXTS["post"], TEXTS["posted"], TEXTS["quit"]]:
            raise LaneError(f"{change}, a post read {posted}")
        if run.marks:
            raise LaneError(f"{change}: the reads failing left marks in {run.marks}")
        again = served(binary, {}, where, steps=asks[:1], laid=False)
    if change in UNOPENED[1:]:
        if again.started or f"recovery failed: a file job failed, class {other}\n" not in again.said:
            raise LaneError(f"{change}: started again, {again.said[-200:]!r}, not recovery failed")
        return
    try:
        R.recover(C.KEY, C.GROUPS, list(run.image.items()))
    except R.Corrupt as why:
        if again.started or f"the store is refused: corrupt {why}\n" not in again.said:
            raise LaneError(f"{change}: started again, {again.said[-200:]!r}, not corrupt {why}") from None
        return
    if not again.started:
        raise LaneError(f"{change}: started again, {again.said[-200:]!r}")
    unsent(f"{change}, started again", again.got[0], before[0], len(base[name]) < 16384)


@dataclass
class Bases:
    held: Image
    both: Image
    crashed: Image


def bases(binary: Path) -> Bases:
    """A spool holding `HELD`, as the server leaves it and as a crash does, and one holding `LARGE`
    too."""
    images: list[Image] = [{}]
    with tempfile.TemporaryDirectory() as temp:
        for article in (HELD, LARGE):
            run = served(binary, images[-1], Path(temp, str(len(images))), steps=[(b"POST\r\n", article)])
            if run.got != [[TEXTS["greeting-post"], TEXTS["post"], TEXTS["posted"], TEXTS["quit"]]]:
                raise LaneError(f"a post on the lane's spool read {run.got}")
            images.append(run.image)
    return Bases(images[1], images[2], C.crashed(images[1]))


def passes(binary: Path, b: Bases, w: dict[str, int]) -> tuple[dict[str, float], list[int]]:
    """Every pass, the quick ones first: when the slowed run's replies came, and how many operations
    failed on each spool."""
    no_space, other = str(w["CLASS_NO_SPACE"]), str(w["CLASS_OTHER"])
    with lanes.pool() as pool:
        list(pool.map(lambda a: corrupted(binary, b.both, other, *a),
                      [(change, C.mid_of(m)) for change in CHANGES for m in (HELD, LARGE)]))
    cut(binary, b.held, no_space)
    spent(binary, b.held, w["GEN_LIMIT"])
    took = slowed(binary, b.held)
    counts: list[int] = []
    fired: set[str] = set()
    for base in (b.held, b.crashed):
        points, files = swept(binary, base, errno.ENOSPC, no_space)
        if swept(binary, base, errno.EINTR, other, files)[0] != points:
            raise LaneError("EINTR fails operations at other points than ENOSPC")
        counts.append(sum(map(bool, points)))
        fired |= set(points)
    terminated(binary, b.held, counts[0])
    unfailed = C.points() - fired - {"dn/read-dir"}
    if unfailed:
        raise LaneError(f"dn/fail never failed {sorted(unfailed)}")
    return took, counts


DEFECTS = [
    C.Defect("an interrupted call reported", "while (result_ < 0 && errno == EINTR);", "while (result_ < 0 && 0);",
             1, "EINTR: the server ended at its start", program=False),
    C.Defect("a short write taken for all of it", "        n -= (uint64_t)w;\n", "        n = 0;\n", 1,
             "every write cut to one octet", program=False),
    C.Defect("a mark left by any failure",
             "if (syncs(j->ops[i].code) && (j->ops[i].code != DN_SESSION_OP_CLOSE || j->wrote[i]))",
             "if (syncs(j->ops[i].code) || 1)", 1, "left marks", program=False),
    C.Defect("one worker", "WORKERS = 2, NAME = 32", "WORKERS = 1, NAME = 32", 1, "a read and a STAT were answered",
             program=False),
    C.Defect("a symlink followed", "flags | O_CLOEXEC | O_NOFOLLOW", "flags | O_CLOEXEC", 1, "a symlink to a copy",
             program=False),
    C.Defect("a commit not synced before its 240", r"(st jb \+ 88, flen;\n\s+st jb \+ 96, 0;\n\s+st jb \+ 104, )6;",
             r"\g<1>5;", 1, "a post's 240 after"),
    C.Defect("the octet past an article's end not read", r"st jb \+ 88, left \+ 1;", "st jb + 88, left;", 1,
             "grown, ARTICLE"),
    C.Defect("a failed commit refused, the store going on",
             r"(\} else \{\n\s+)(st zs \+ 96, 3;\n\s+st zs \+ 104, 0;\n\s+st @base \+ 1032624, 0;)",
             r"\g<1>if ok == 0 { st zs + 160, 3; st zs + 88, 1; st zs + 104, 0; } else { \g<2> }", 1,
             "on the journal file failing"),
    C.Defect("LIST ACTIVE says y once the store has stopped", r"var yn = 110;", "var yn = 121;", 1,
             "LIST ACTIVE read"),
    C.Defect("a stop that does not wait for the jobs running", "if (!counts[2] || elapsed >= ms) return counts[2];",
             "if (!counts[2] || elapsed + ms >= ms) return counts[2];", 1, "still running", program=False),
    C.Defect("an index used past its last generation", " && conns[i].gen < DN_SESSION_GEN_LIMIT;", ";", 1,
             "the program stopped the run: code 6", program=False, loop=True),
]


def check(cake: str) -> Report:
    if sys.version_info[:2] != (3, 12):
        raise LaneError(f"this lane needs the nntplib of Python 3.12, not Python {sys.version.split()[0]}")
    OUT.mkdir(parents=True, exist_ok=True)
    (OUT / "dn_session_layout.h").write_text(lanes.emit("emit-session-layout"))
    w = session_native.layout(OUT)
    source = lanes.emit("emit-session")
    with lanes.pool() as pool:
        base = pool.submit(C.test_build, cake, OUT, "faults", source)
        builds = [pool.submit(C.test_build, cake, OUT, f"defect-{k}", source, d) for k, d in enumerate(DEFECTS)
                  if d.program]
        clock = time.monotonic()
        b = bases(base.result())
        took, counts = passes(base.result(), b, w)
        limits = bounded(base.result(), b.both)
        poll_fails(base.result(), b.held)
        seconds = {"runs": round(time.monotonic() - clock, 1)}
        found = {}
        programs = iter(builds)
        for k, defect in enumerate(DEFECTS):
            binary = (next(programs).result() if defect.program
                      else C.test_build(cake, OUT, f"defect-{k}", source, defect, base.result()))
            try:
                passes(binary, b, w)
            except LaneError as error:
                if not defect.said(str(error)):
                    raise LaneError(f"{defect.name} was caught, but not as {defect.sign!r}: {error}") from None
                found[defect.name] = str(error)[:300]
                continue
            raise LaneError(f"{defect.name} passed")
        seconds["defects"] = round(time.monotonic() - clock - seconds["runs"], 1)
    lanes.require_quoted({"docs/baseline.md": [
        f"each of its {counts[0]} and {counts[1]} operations", f"{len(CHANGES)} ways",
        f"{len(DEFECTS)} planted defects of the faults lane"]})
    return Report("checked", cake, [N.HOST, *N.STORE], {
        "executable_sha256": lanes.digest(base.result()), "operations": counts, "slowed": took, "bounds": limits,
        "seconds_by_step": seconds,
        "planted_defects_caught": found})


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--cake", default=os.environ.get("CAKE"))
    args = parser.parse_args()
    lanes.require_platform(parser)
    cake = lanes.given_cake(parser, args.cake)
    lanes.lane_main("FAULTS", OUT, lambda: check(cake))


if __name__ == "__main__":
    main()
