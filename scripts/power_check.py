#!/usr/bin/env python3
# SPDX-License-Identifier: AGPL-3.0-or-later
"""The power lane: the crash lane's server, clients and judgement (scripts/crash_check.py), the spool
on LazyFS, which keeps what is not synced in a cache of its own (scripts/lazyfs_check.py), so that
dropping the cache, or LazyFS ending, is a loss of power. For each phase of the crash lane:

- the server stopped before each of its operations, the cache dropped, and killed;
- each of its operations failed with EIO at its first point (`dn/fail`), the run ended, and the
  cache dropped; every point of native/jobs.c's operations fails in some run, but `dn/read-dir`,
  which a listing reaches only past `dn/open-dir`;
- each write to the journal, and to a tail recovery keeps, torn by LazyFS into three parts, the
  first, the last or both kept, LazyFS then ending itself.

Each spool left is held to what the crash lane holds it to. Where an operation failed or a write
tore, and only there, a start may end with status 4, a post be refused, one connection be closed
unanswered after its 340, and a read be answered 403 where a read failed; a refused article is not
found. Started again, on a mark of another boot where a sync failed, the server removes it. Each
defect of `DEFECTS`, planted in the program or the host, has to be caught by its pass, for a
reason named.

It needs /dev/fuse and the right to mount it, as the LazyFS lane does.
"""
from __future__ import annotations

import argparse
from collections.abc import Callable, Iterator
from concurrent.futures import ThreadPoolExecutor
import contextlib
import functools
import os
from pathlib import Path
import queue
import shutil
import sys
import tempfile
import time

sys.path.insert(0, str(Path(__file__).resolve().parent))
import crash_check as C  # the path above is what makes these importable
import lanes
from lanes import ROOT, LaneError, Report
import lazyfs_check as L
import nntp_check as N
import recovery_ref as R

OUT = ROOT / "build/power"
EIO = 5
# The parts of a torn write LazyFS keeps: the first, the last, both.
KEPT = ("1", "3", "1,3")
# The points of a read of an article, whose failure answers 403.
READING = {"dn/open", "dn/size", "dn/read"}
Image = dict[bytes, bytes]


class Mounts:
    """LazyFS at as many mount points as runs go at once, each run taking one to itself."""

    def __init__(self, work: Path) -> None:
        self.all: list[L.LazyFS] = []
        self.free: queue.Queue[L.LazyFS] = queue.Queue()
        try:
            lazyfs = lanes.pinned_tool("lazyfs")
            for k in range(lanes.WORKERS):
                (work / f"fs{k}").mkdir()
                fs = L.LazyFS(lazyfs, work / f"fs{k}")
                fs.start()
                self.all.append(fs)
                self.free.put(fs)
        except BaseException:
            self.stop()
            raise

    @contextlib.contextmanager
    def taken(self) -> Iterator[L.LazyFS]:
        fs = self.free.get()
        try:
            yield fs
        finally:
            self.free.put(fs)

    def stop(self) -> None:
        for fs in self.all:
            fs.stop()


def lost(fs: L.LazyFS) -> bool:
    """Power lost: the cache dropped, or LazyFS mounted again if it ended itself, its cache gone with
    it; whether it ended."""
    if fs.process is not None and fs.process.poll() is None:
        try:
            fs.clear_cache()
        except LaneError:
            if fs.process.poll() is None:
                raise
        else:
            return False
    fs.stop()
    fs.start()
    return True


def powered(binary: Path, mounts: Mounts, phase: C.Phase, base: Image, enable: str,
            torn: tuple[str, int, str] | None = None) -> tuple[bool, Image, set[str]]:
    """A run on LazyFS with the points `enable` names, or with a write `torn` as (file, occurrence,
    parts kept), power lost at its end, held to 0005: whether it stopped, or the write tore, the
    spool left, and the point `dn/fail` failed, if any."""
    with mounts.taken() as fs, tempfile.TemporaryDirectory() as temp:
        at = Path(tempfile.mkdtemp(dir=fs.point))
        ended: list[bool] = []
        def tear() -> None:
            if torn:
                name, occurrence, kept = torn
                fs.command(f"lazyfs::torn-op::file={fs.root / at.name / 'spool' / name}::persist={kept}::parts=3"
                           f"::occurrence={occurrence}")
                # Commands are taken in order, and only a clear is answered: once it is, the tear is set.
                fs.clear_cache()

        may_fail = torn is not None or "dn/fail" in enable
        try:
            halted, got, image = C.served(binary, phase, base, enable, Path(temp, "first"), at, tear,
                                          lambda: ended.append(lost(fs)), refusing=may_fail)
        finally:
            shutil.rmtree(at, ignore_errors=True)
        said = [line.split()[1] for line in Path(temp, "first", "stderr").read_text().splitlines()
                if line.startswith("dn/fail ")]
        fired = set(said)
        failed = ended == [True] if torn else bool(fired)
        refused = halted and may_fail
        mark = C.OTHER_BOOT if C.MARK in image else b""
        image.pop(C.MARK, None)
        why = ("dn/fail failed " + ", ".join(said) if len(said) > 1
               else "the server ended at its start with status 4, nothing failing" if refused and not failed
               else C.violation(phase, base, image, got, halted, failed,
                                failed and (torn is not None or bool(fired & READING)))
               or C.restarted(binary, image, Path(temp, "again"), phase.posted(), mark))
    if why:
        raise LaneError(f"{phase.name}, {enable or f'{torn} torn'}: {why}")
    return (failed if torn else halted and not may_fail), image, fired


Run = Callable[..., tuple[bool, Image, set[str]]]


def torn(run: Run, name: str, occurrence: int, kept: str) -> bool:
    return run("", (name, occurrence, kept))[0]


def stopped_at(run: Run, stop: int) -> tuple[bool, Image]:
    return run(f"enable name=dn/stop,failinfo={stop}")[:2]


def failed_at(run: Run, op: int) -> set[str]:
    return run(f"enable name=dn/fail,failinfo={op * 256 + EIO}")[2]


def tears(run: Run, phase: C.Phase, base: Image, pool: ThreadPoolExecutor) -> int:
    """Each write to the journal, and to the tail recovery keeps, torn in each way: how many there
    were."""
    keeps = [os.fsdecode(bytes.fromhex(a.split(":")[1])) for a in R.recover(C.KEY, C.GROUPS, list(base.items()))[5]
             if a.startswith("keep:")]
    count = 0
    for name in ["journal", *keeps]:
        for occurrence in range(1, 100):
            runs = list(pool.map(functools.partial(torn, run, name, occurrence), KEPT))
            if not any(runs):
                break
            if not all(runs):
                raise LaneError(f"{phase.name}: write {occurrence} of {name} torn in some ways only")
            count += 1
    return count


def passes(binary: Path, bases: list[Image] | None = None, only: str = "",
           operations: list[int] | None = None) -> tuple[dict[str, list[int]], list[Image]]:
    """Each phase stopped before each operation, failed at each, and torn at each write to the
    journal, on the spool the phase before left, or on `bases`; with `only`, that pass alone, failing
    as many `operations` as each phase has: how many of each, and the spools the phases started on."""
    counts: dict[str, list[int]] = {"stopped": [], "failed": [], "torn": []}
    used: list[Image] = []
    left: Image = {}
    fired: set[str] = set()
    with tempfile.TemporaryDirectory(prefix="dn-power-") as work:
        mounts = Mounts(Path(work))
        try:
            with lanes.pool() as pool:
                try:
                    for k, phase in enumerate(C.PHASES):
                        base = bases[k] if bases else C.crashed(left) if phase is C.PHASES[-1] else left
                        used.append(base)
                        run = functools.partial(powered, binary, mounts, phase, base)
                        count = operations[k] if operations else 0
                        if only in ("", "stopped"):
                            count, left = C.sweep(phase, functools.partial(stopped_at, run))
                            counts["stopped"].append(count)
                        if only in ("", "failed"):
                            fired.update(*pool.map(functools.partial(failed_at, run), range(1, count + 1)))
                            counts["failed"].append(count)
                        if only in ("", "torn"):
                            counts["torn"].append(tears(run, phase, base, pool))
                except BaseException:
                    pool.shutdown(cancel_futures=True)
                    raise
        finally:
            mounts.stop()
    unfailed = C.points() - fired - {"dn/read-dir"}
    if not only and unfailed:
        raise LaneError(f"dn/fail never failed {sorted(unfailed)}")
    return counts, used


# Each defect with the pass that catches it.
DEFECTS = [
    (C.Defect("an article not synced before it is renamed", r"st jb \+ (104|24), 6;(\n\s+st jb \+ (?:112|32), pl;)",
              r"st jb + \1, 5;\2", 2, "corrupt wrong-size"), "stopped"),
    (C.Defect("a commit not synced before its 240", r"(st jb \+ 88, flen;\n\s+st jb \+ 96, 0;\n\s+st jb \+ 104, )6;",
              r"\g<1>5;", 1, "answered 240, is not found"), "stopped"),
    # An article's sync, the directory's after its rename, or the journal's, whichever fails first.
    (C.Defect("a failed sync taken for done", "return RETRIED(DN_FAULT(point) ? -1 : sync(fd));",
              "return RETRIED(DN_FAULT(point) ? 0 : sync(fd));", 1,
              ("corrupt wrong-size", "corrupt missing-file", "answered 240, is not found"), program=False),
     "failed"),
    (C.Defect("a frame taken without its tag checked", r"if \(r == jtag\) == 0 \{", "if 0 {", 2,
              "not what recovery_ref's actions leave"), "torn"),
]


def check(cake: str) -> Report:
    if sys.version_info[:2] != (3, 12):
        raise LaneError(f"this lane needs the nntplib of Python 3.12, not Python {sys.version.split()[0]}")
    OUT.mkdir(parents=True, exist_ok=True)
    (OUT / "dn_session_layout.h").write_text(lanes.emit("emit-session-layout"))
    source = lanes.emit("emit-session")
    with lanes.pool(1 + len(DEFECTS)) as pool:
        base = pool.submit(C.test_build, cake, OUT, "power", source)
        builds = [pool.submit(C.test_build, cake, OUT, f"defect-{k}", source, d) for k, (d, _) in enumerate(DEFECTS)
                  if d.program]
        clock = time.monotonic()
        counts, bases = passes(base.result())
        seconds = {"runs": round(time.monotonic() - clock, 1)}
        found = {}
        programs = iter(builds)
        for k, (defect, caught_by) in enumerate(DEFECTS):
            built = (next(programs).result() if defect.program
                     else C.test_build(cake, OUT, f"defect-{k}", source, defect, base.result()))
            try:
                passes(built, bases, caught_by, counts["stopped"])
            except LaneError as error:
                if not defect.said(str(error)):
                    raise LaneError(f"{defect.name} was caught, but not as {defect.sign!r}: {error}") from None
                found[defect.name] = str(error)[:300]
                continue
            raise LaneError(f"{defect.name} passed")
        seconds["defects"] = round(time.monotonic() - clock - seconds["runs"], 1)
    stops, torn = counts["stopped"], counts["torn"]
    lanes.require_quoted({"docs/baseline.md": [
        f"each of the {stops[0]}, {stops[1]} and {stops[2]} operations",
        f"each of {torn[0]}, {torn[1]} and {torn[2]} writes", f"each of {sum(torn)} journal writes",
        f"{len(DEFECTS)} planted defects of the power lane"]})
    return Report("checked", cake, [N.HOST, *N.STORE], {
        "executable_sha256": lanes.digest(base.result()), "runs": counts, "seconds_by_step": seconds,
        "planted_defects_caught": found})


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--cake", default=os.environ.get("CAKE"))
    args = parser.parse_args()
    lanes.require_platform(parser)
    cake = lanes.given_cake(parser, args.cake)
    lanes.lane_main("POWER", OUT, lambda: check(cake))


if __name__ == "__main__":
    main()
