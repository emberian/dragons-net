#!/usr/bin/env python3
# SPDX-License-Identifier: AGPL-3.0-or-later
"""The file system lane: the model of the file system the store runs on (`DN.News.FsModel`) and what
a crash may leave of it, as decision 0005 states them, answered by `dn-compiler fs-model` and by
the independent scripts/fs_ref.py, which have to give the same answer on every case:

- a table of runs, each with the answer 0005 gives it: what each operation answers, and whether a
  crash may leave an image — names lost or kept with and without a sync of the directory, octets
  kept by a sync and any octets past them up to the most a file has held, a truncation's octets
  coming back, one file under two names, syncs after a failed one;
- runs drawn at random from a fixed seed, operations failing in each way they may and often tried
  again, the files they work on picked by the reference's state so that most exist; and short lives
  of one file, created, appended to, synced, cut, its name synced or moved;
- after the lives and the shorter runs, the images the model lists (`Fs.crashes`) and those the
  reference lists,
  each of which both have to admit, and each changed: an octet changed, added or taken away, a
  name added, dropped or given another's octets.

Whether a crash may leave an image the model decides with `DN.News.FsLeaves.mayLeave`, proven to
hold exactly of the images a crash leaves of a well-formed file system (`mayLeave_iff`), which the
model's runs leave (`runM_ok`); a crash shows only in the image it leaves. Lines no case may be both have to
refuse, and each version of the model with one rule changed (`DN.News.FsMutant`) has to answer some
case otherwise, and some drawn case, not of the table, too (docs/baseline.md, "File system").
"""
from __future__ import annotations

from dataclasses import dataclass
from pathlib import Path
import random
import subprocess
import sys
import time

sys.path.insert(0, str(Path(__file__).resolve().parent))
import abnf_check as C  # the path above is what makes these importable
import fs_ref as R
import lanes
from lanes import LaneError, Report

OUT = lanes.ROOT / "build/fs"
REFERENCE = lanes.ROOT / "scripts/fs_ref.py"
SEED = 20261004
# The versions of the model with one rule changed, by the name `dn-compiler fs-model --mutant` takes.
MUTANTS = ["names-as-seen", "names-as-synced", "names-latest-only", "kept-ignored", "prefix-only",
           "high-ignored", "files-apart", "append-atomic", "sync-fail-trusted", "dir-sync-fail-trusted",
           "fails-did-nothing", "untrusted-syncs", "untrusted-dir-syncs", "rename-same-loses",
           "sync-keeps-most", "failed-append-most"]
NAMES = ["61", "62", "63"]
# The most images taken from what each side lists after a run, and the most operations of a run
# listed.
TAKEN = 24
LISTED = 6
# Lines both have to refuse to answer.
REFUSED = ["run", "run - -", "run append:0:01!2", "run sync:0!1", "run sync-dir!1", "run remove:61!2",
           "run create:6", "run create:61:62", "run frob:61", "run truncate:0:x", "run create:61!",
           "run create:61!1!1", "run create:61;", "crash - 61=-;61=-", "crash - 61", "crash - 61=0",
           "crashes", " ", "\r", "run -\r", "run create:", "run append:0:", "crash - =", "crash - 61="]


@dataclass(frozen=True)
class Case:
    """A line to answer and, when the lane knows it, the answer."""
    line: str
    want: str | None = None

    def holds(self, said: str) -> bool:
        return self.want is None or said == self.want


def table() -> list[Case]:
    """Runs decision 0005 sets out, each with the answer it gives them."""
    out: list[Case] = []

    def run(ops: str, want: str) -> None:
        out.append(Case(f"run {ops}", want))

    def crash(ops: str, image: str, may: bool) -> None:
        out.append(Case(f"crash {ops} {image}", "yes" if may else "no"))

    # What operations answer, and what the program then finds.
    run("-", "- -")
    run("create:61", "file:0 61=-")
    run("create:61;create:61;open:61;open:62", "file:0;exists;file:0;missing 61=-")
    run("create:61;append:0:0102;read:0:1:5;size:0;size:1", "file:0;done;bytes:02;size:2;missing 61=0102")
    run("create:61;truncate:0:3;append:0:01;truncate:0:2", "file:0;done;done;done 61=0000")
    run("create:61;create:62;rename:61:62;list", "file:0;file:1;done;names:62 62=-")
    run("create:61;rename:61:61;rename:62:61", "file:0;done;missing 61=-")
    run("create:61;remove:61;remove:61;create:61", "file:0;done;missing;file:1 61=-")
    run("append:0:01;sync:0;truncate:0:1", "missing;missing;missing -")
    run("create:-;create:61;list", "file:0;file:1;names:-,61 -=-;61=-")
    # A failed operation: an append, any first part of its octets; anything else, all or nothing.
    run("create:61;append:0:010203!2", "file:0;failed 61=0102")
    run("create:61!0", "failed -")
    run("create:61!1", "failed 61=-")
    run("create:61;rename:61:62!0;rename:61:63!1", "file:0;failed;failed 63=-")
    # Names: what a name held at the directory's last sync, or anything it has held since.
    crash("create:61", "-", True)
    crash("create:61", "61=-", True)
    crash("create:61;sync-dir", "-", False)
    crash("create:61", "62=-", False)
    crash("create:61;sync-dir;rename:61:62", "61=-", True)
    crash("create:61;sync-dir;rename:61:62", "62=-", True)
    crash("create:61;sync-dir;rename:61:62", "61=-;62=-", True)
    crash("create:61;sync-dir;rename:61:62", "-", True)
    crash("create:61;sync-dir;rename:61:62;sync-dir", "61=-", False)
    crash("create:61;sync-dir;remove:61", "61=-", True)
    crash("create:61;sync-dir;remove:61;sync-dir", "61=-", False)
    crash("create:61;create:62;append:1:07;rename:61:62", "62=07", True)
    crash("create:61;create:62;append:1:07;rename:61:62;remove:62;create:62", "62=07", True)
    # Files: the octets a sync kept, then any octets, up to the most the file has held since.
    synced = "create:61;append:0:01;sync:0;sync-dir"
    crash(synced, "61=01", True)
    crash(synced, "61=-", False)
    crash(synced, "61=02", False)
    crash(synced, "61=0100", False)
    grown = "create:61;sync-dir;append:0:0102"
    crash(grown, "61=-", True)
    crash(grown, "61=01", True)
    crash(grown, "61=ff", True)
    crash(grown, "61=ffee", True)
    crash(grown, "61=010203", False)
    cut = "create:61;append:0:0102;sync:0;sync-dir;truncate:0:0"
    crash(cut, "61=-", True)
    crash(cut, "61=0102", True)
    crash(cut, "61=ffff", True)
    crash(cut, "61=010203", False)
    crash(f"{synced};append:0:02;sync:0", "61=01", False)
    crash(f"{synced};append:0:02", "61=01ee", True)
    # A sync while trusted lowers the most a file may hold; a failed append raises it only by what
    # it wrote.
    crash("create:61;append:0:0102;sync:0;sync-dir;truncate:0:1;sync:0", "61=0102", False)
    crash("create:61;sync-dir;append:0:0102;sync:0!0;truncate:0:0;sync:0", "61=0102", True)
    crash("create:61;sync-dir;append:0:0102!1", "61=0102", False)
    # One file under two names holds the same octets under both.
    crash("create:61;sync-dir;append:0:01;rename:61:62", "61=-;62=01", False)
    crash("create:61;sync-dir;append:0:01;rename:61:62", "61=01;62=01", True)
    # After a failed sync of a file or of the directory no later sync of it is trusted.
    crash("create:61;sync-dir;append:0:01;sync:0!0;sync:0", "61=-", True)
    crash("create:61;sync-dir!0;sync-dir", "-", True)
    crash("create:61;append:0:01;sync:0!0;sync-dir", "-", False)
    crash("create:61;append:0:01;sync-dir!0;sync:0", "61=-", False)
    return out


def random_ops(rng: random.Random) -> str:
    """Operations on a few names and on the files they hold, now and then on one there is not, some
    failing in a way each may, and one that failed often tried again; the reference's state says which
    files there are, so that most of the operations on a file reach one."""
    disk = R.Disk()
    ops: list[str] = []
    for _ in range(rng.randint(0, 10)):
        if ops and "!" in ops[-1] and rng.random() < 0.7:
            again = ops[-1].split("!")[0]
            R.do(disk, R.op_of(again)[0])
            ops.append(again)
            continue
        n = len(disk.files)
        # mostly the file created last, so that runs follow one file through its life
        f = str(rng.choice([n - 1] * 7 + [rng.randrange(n)] * 2 + [n]) if n else 0)
        octets = rng.choice(["-", "00", "01", "ff", "0102", "0a0b0c", rng.randbytes(rng.randint(1, 3)).hex()])
        name, other = rng.choice(NAMES), rng.choice(NAMES)
        kind, k = (f"create:{name}", 1) if not n and rng.random() < 0.8 else rng.choice(
            [(f"create:{name}", 1)] + [(f"append:{f}:{octets}", len(octets) // 2)] * 4
            + [(f"sync:{f}", 0)] * 4 + [(f"truncate:{f}:{rng.randint(0, 3)}", 1)] * 3 + [("sync-dir", 0)] * 2
            + [(f"rename:{name}:{other}", 1), (f"remove:{name}", 1), (f"open:{name}", 1),
               (f"read:{f}:{rng.randint(0, 3)}:{rng.randint(0, 4)}", 1), (f"size:{f}", 1), ("list", 1)])
        step = f"{kind}!{rng.randint(0, k)}" if rng.random() < (0.25 if kind.startswith("sync") else 0.1) else kind
        op, failed = R.op_of(step)
        if failed is None:
            R.do(disk, op)
        else:
            R.fail(disk, op, failed)
        ops.append(step)
    return ";".join(ops) or "-"


def random_life(rng: random.Random) -> str:
    """One file followed through a short life: created, then appended to, synced, cut, its name
    synced or moved, operations failing in a way each may and often tried again; the reference's
    state says which name holds it."""
    disk = R.Disk()
    ops: list[str] = []

    def emit(step: str) -> None:
        op, failed = R.op_of(step)
        if failed is None:
            R.do(disk, op)
        else:
            R.fail(disk, op, failed)
        ops.append(step)

    emit(f"create:{rng.choice(NAMES)}")
    for _ in range(rng.randint(1, 6)):
        if "!" in ops[-1] and rng.random() < 0.7:
            emit(ops[-1].split("!")[0])
            continue
        name = next(n for n, h in disk.names.items() if h.now() == 0).hex()
        octets = rng.choice(["00", "01", "ff", "0102", "0a0b0c", rng.randbytes(rng.randint(1, 3)).hex()])
        kind, k = rng.choice([(f"append:0:{octets}", len(octets) // 2)] * 3 + [("sync:0", 0)] * 3
                             + [(f"truncate:0:{rng.randint(0, 3)}", 1)] * 2 + [("sync-dir", 0)] * 2
                             + [(f"rename:{name}:{rng.choice(NAMES)}", 1), ("size:0", 1)])
        emit(f"{kind}!{rng.randint(0, k)}" if rng.random() < 0.2 else kind)
    return ";".join(ops)


def parsed(image: str) -> dict[str, str]:
    return {} if image == "-" else dict(p.split("=") for p in image.split(";"))


def shown(image: dict[str, str]) -> str:
    return ";".join(f"{n}={o}" for n, o in sorted(image.items())) or "-"


def changed(rng: random.Random, image: str) -> list[str]:
    """`image` with one thing changed: an octet changed, added or taken away, a name added, dropped,
    or given another's octets."""
    img = parsed(image)
    out = []
    names = sorted(img)
    if names:
        n = rng.choice(names)
        o = "" if img[n] == "-" else img[n]
        if o:
            flipped = o[:-2] + f"{int(o[-2:], 16) ^ 1:02x}"
            out += [shown({**img, n: flipped}), shown({**img, n: o[:-2] or "-"})]
        out += [shown({**img, n: o + "00"}), shown({k: v for k, v in img.items() if k != n})]
        others = [m for m in names if img[m] != img[n]]
        if others:
            out.append(shown({**img, n: img[rng.choice(others)]}))
    free = [n for n in NAMES if n not in img]
    if free:
        out.append(shown({**img, rng.choice(free): "-"}))
    return out


def check() -> Report:
    OUT.mkdir(parents=True, exist_ok=True)
    rng = random.Random(SEED)  # noqa: S311 -- a fixed seed, so that every run draws the same cases
    steps, mark = {}, time.monotonic()
    model_command = [str(lanes.DN_COMPILER), "fs-model"]
    reference_command = [sys.executable, str(REFERENCE)]

    def both(asked: list[str]) -> list[str]:
        model = C.answer_lines(model_command, asked, C.WORKERS)
        problem = lanes.differing(asked, model, C.answer_lines(reference_command, asked, C.WORKERS))
        if problem:
            raise LaneError(problem)
        return model

    written = table()
    runs = [random_ops(rng) for _ in range(1500)]
    lives = [random_life(rng) for _ in range(600)]
    families: dict[str, list[Case]] = {"table": written, "runs": [Case(f"run {ops}") for ops in runs + lives]}
    small = [ops for ops in runs if ops.count(";") < LISTED] + lives
    listed = C.answer_lines(model_command, [f"crashes {ops}" for ops in small], C.WORKERS)
    left = C.answer_lines(reference_command, [f"leavings {ops}" for ops in small], C.WORKERS)
    must, candidates = [], []
    for ops, theirs, ours in zip(small, listed, left, strict=True):
        images = list(dict.fromkeys(theirs.split(" ") + ours.split(" ")))
        taken = rng.sample(images, min(TAKEN, len(images)))
        must += [f"crash {ops} {i}" for i in taken]
        for i in taken:
            candidates += [f"crash {ops} {c}" for c in changed(rng, i)]
    families["listed"] = [Case(line, "yes") for line in must]
    families["changed"] = [Case(line) for line in dict.fromkeys(candidates) if line not in set(must)]
    cases = [c for family in families.values() for c in family]
    lines = [c.line for c in cases]
    steps["cases"], mark = round(time.monotonic() - mark, 1), time.monotonic()
    answers = both(lines)
    steps["answers"], mark = round(time.monotonic() - mark, 1), time.monotonic()
    for case, said in zip(cases, answers, strict=True):
        if not case.holds(said):
            raise LaneError(f"{case.line[:300]}: answered {said[:300]}, not {case.want}")
    verdicts = [a for c, a in zip(cases, answers, strict=True) if c.line.startswith("crash ")]
    if {"yes", "no"} - set(verdicts):
        raise LaneError("no crash case is answered both ways")
    for asked in REFUSED:
        for command in (model_command, reference_command):
            done = subprocess.run(command, input=asked + "\n", capture_output=True, text=True, timeout=600,
                                  check=False)
            if done.returncode == 0:
                raise LaneError(f"{command[-1]} answered a line no case may be: {asked!r}")
    held = list(zip(lines, answers, strict=True))
    where: dict[str, str] = {}
    for name, family in families.items():
        for k, c in enumerate(family):
            where.setdefault(c.line, f"{name} {k}")
    caught = {}
    for mutant in MUTANTS:
        differs = C.first_difference([*model_command, "--mutant", mutant], held)
        if differs is None:
            raise LaneError(f"the version {mutant} was not caught")
        caught[mutant] = where[differs]
    drawn = [(ln, a) for ln, a in held if not where[ln].startswith("table ")]
    alone = {}
    for mutant in MUTANTS:
        differs = C.first_difference([*model_command, "--mutant", mutant], drawn)
        if differs is None:
            raise LaneError(f"no drawn case catches the version {mutant}")
        alone[mutant] = where[differs]
    steps["mutants"] = round(time.monotonic() - mark, 1)
    measured = {"cases": f"{len(cases):,}", "versions of the model": f"{len(MUTANTS):,}",
                "table cases": f"{len(written):,}", "runs drawn": f"{len(runs):,}",
                "lives of one file": f"{len(lives):,}",
                "images listed": f"{len(must):,}", "images changed": f"{len(families['changed']):,}"}
    baseline = (lanes.ROOT / "docs/baseline.md").read_text()
    assurance = (lanes.ROOT / "docs/assurance.md").read_text()
    stated = lanes.section(baseline, "\n| File system |", "\n|") + lanes.section(baseline, "\n### File system\n",
                                                                                "\n### ")
    wrong = lanes.misstated(stated, measured)
    wrong += lanes.misstated(lanes.section(assurance, "\n| File system and crashes", "\n|"),
                             {k: measured[k] for k in ("cases", "versions of the model")})
    if wrong:
        raise LaneError(f"the documents state otherwise than measured: {wrong}")
    return Report("checked", None, [REFERENCE], {
        "cases": len(cases), "by_family": {k: len(v) for k, v in families.items()},
        "crash_verdicts": {v: verdicts.count(v) for v in ("yes", "no")}, "refused_lines": len(REFUSED),
        "mutants_caught": caught, "mutants_caught_by_drawn_cases": alone, "seconds_by_step": steps})


def main() -> None:
    lanes.lane_main("FS", OUT, check)


if __name__ == "__main__":
    main()
