#!/usr/bin/env python3
# SPDX-License-Identifier: AGPL-3.0-or-later
"""The article's check as Pancake functions (`DN.News.ArticleProg`), compiled by CakeML and run by
native/accept_check.c, held to `dn-compiler article-model`: the two have to give the same answer, to
the byte, on every case of the article lane (scripts/article_check.py), on the dates it writes and
reads back, and on cases that reach what only the program does: years of any length, lines with a CR
alone. The contexts past the bounds the program has to refuse, as the model does, but for numbers
no word holds, which its host refuses. Each mutant of the program has to answer some case otherwise.
Articles of forms a client can make hard, as long as a header section may be, are answered as the
model answers them and timed: per octet, no slower than twice their time at a sixteenth of the
size. On every call the host requires the heap outside the program's area untouched and the header
the compiler theorem requires intact (docs/baseline.md, "Article acceptance in Pancake").
"""
from __future__ import annotations

import argparse
from collections.abc import Callable
from dataclasses import replace
import os
from pathlib import Path
import random
import subprocess
import sys
import time

sys.path.insert(0, str(Path(__file__).resolve().parent))
import article_check as R  # the path above is what makes these importable
import lanes
from lanes import NATIVE, ROOT, LaneError, Report

OUT = ROOT / "build/accept"
HOST = NATIVE / "accept_check.c"
MUTANTS = ["cr-ends-line", "caseful", "weekday-unchecked", "year-short", "fold-early", "escape-kept"]
# How much slower per octet a long article may be than a small one of the same form.
SLOWER = 2
LONGEST, SMALL = 65536, 4096
# The wall clocks the program takes are below this (`ArticleProg.wallMax`).
WALL_MAX = 2**40
RUNS = 3
CRLF = b"\r\n"


def extra() -> list[bytes]:
    """Articles for what the program does that the article lane's cases need not reach."""
    years = [b"29 Feb 100000", b"29 Feb 100100", b"29 Feb 100400", b"28 Feb 99999999999999999999",
             b"1 Mar 2000000000000000000000000000000001", b"29 Feb 1900", b"29 Feb 2000"]
    dates = [b"Date: " + y + b" 00:00:00 +0000" for y in years]
    dates += [b"Date: Sat, 29 Feb 100000 00:00:00 +0000", b"Date: Tue, 29 Feb 100000 00:00:00 +0000",
              b"Expires: 1 Jan 3000000 00:00:00 GMT"]
    lone = [b"Subject: a\rb", b"X-A: a\r\r", b"Subject: hi\r", b"Summary: \r\n x"]
    refs = [b"References: (a\\) <b@c>) <x@y.example>", b"References: (\\(<" + b"a" * 260 + b">) <x@y.example>",
            b"In-Reply-To: (c\\)) <x@y.example>"]
    return [R.plus(f) for f in dates + lone + refs] + [R.article(*R.MINIMAL, b"Path: x\r\n !y")]


def hard(most: int) -> list[tuple[str, bytes]]:
    """Articles of each form that make the checks work, each as long as fits `most` octets."""
    forms: dict[str, Callable[[int], bytes]] = {
        "fields": lambda k: R.plus(*[b"X-A: b"] * k),
        "folds": lambda k: R.plus(b"Summary: a" + b"\r\n b" * k),
        "groups": lambda k: R.article(b"From: a@b.example", b"Newsgroups: " + b",\r\n ".join([b"a.b"] * k),
                                      b"Subject: hi"),
        "references": lambda k: R.plus(b"References: " + b"\r\n ".join([b"<a.b@c.d>"] * k)),
        "comments": lambda k: R.plus(b"References: <a@b.c>" + b"".join([b"\r\n " + b"(" * 400 + b")" * 400] * k)),
        "path": lambda k: R.plus(b"Path: " + b"\r\n !".join([b"a"] * k)),
        "dates": lambda k: R.plus(*[b"Received: from a by b; " + R.date(R.WALL)] * k),
        "quoted": lambda k: R.plus(b"Received: " + b"\r\n ".join([b'"a;" ' * 100] * k) + b"; " + R.date(R.WALL)),
        "mailboxes": lambda k: R.article(b"From: " + b",\r\n ".join([b"a@b.example"] * k), *R.MINIMAL[1:]),
    }
    out = []
    for name, make in forms.items():
        lo, hi = 1, 1
        while len(make(hi)) <= most:
            lo, hi = hi, hi * 2
        while hi - lo > 1:
            mid = (lo + hi) // 2
            lo, hi = (mid, hi) if len(make(mid)) <= most else (lo, mid)
        out.append((name, make(lo)))
    return out


def run(binary: Path, lines: list[str], what: str, *, timed: bool = False) -> list[str]:
    try:
        done = subprocess.run([str(binary), *(["--time"] if timed else [])],
                              input="".join(f"{ln}\n" for ln in lines), text=True, capture_output=True,
                              check=False, timeout=1800)
    except subprocess.TimeoutExpired as error:
        raise LaneError(f"{what} ran past its time") from error
    if done.returncode:
        raise LaneError(f"{what} failed with status {done.returncode}:\n{done.stderr[-2000:]}")
    said = done.stdout.splitlines()
    if len(said) != len(lines):
        raise LaneError(f"{what} answered {len(said)} cases of {len(lines)}")
    return said


def build(cake: str, name: str, source: str) -> Path:
    return lanes.whole_program(cake, name, source, OUT, HOST)


def check(cake: str) -> Report:
    OUT.mkdir(parents=True, exist_ok=True)
    steps, mark = {}, time.monotonic()
    (OUT / "dn_article_layout.h").write_text(lanes.emit("emit-article-layout"))
    binary = build(cake, "article", lanes.emit("emit-article"))
    rng = random.Random(R.SEED)  # noqa: S311 -- the article lane's seed, so that these are its cases
    written = R.targeted()
    inn = R.corpus()
    cases = written + R.date_forms(rng) + inn + R.printed() + R.generated(rng)
    lines = [R.line(c, a) for c, a, _ in cases] + [R.line(R.BASE, a) for a in extra()]
    lines += [R.line(c, R.plus()) for c in R.BOUNDS] + [R.line(replace(R.BASE, wall=WALL_MAX - 1), R.plus())]
    formats = [*R.dates(), f"format {WALL_MAX - 1}"]
    model_command = [str(lanes.DN_COMPILER), "article-model"]
    model = R.run(model_command, lines + formats)
    reads = [f"parse {d}" for d in model[len(lines):]]
    asked = lines + formats + reads
    model += R.run(model_command, reads)
    steps["build and model"], mark = round(time.monotonic() - mark, 1), time.monotonic()
    native = run(binary, asked, "the program")
    for case, want, got in zip(asked, model, native, strict=True):
        if want != got:
            raise LaneError(f"{case[:300]}: the model answers {want[:300]}, the program {got[:300]}")
    # The article lane's, and an empty group, which a host that dropped it would let through.
    for ctx in [*R.PAST_BOUNDS, replace(R.BASE, groups=(b"local.test", b""))]:
        done = subprocess.run([str(binary)], input=R.line(ctx, R.plus()) + "\n", capture_output=True, text=True,
                              timeout=600, check=False)
        wide = max(ctx.seq, ctx.run, ctx.conn) >= 2**64
        if done.returncode != (2 if wide else 3):
            raise LaneError(f"a context past its bounds ended the run with {done.returncode}: {ctx}\n{done.stderr}")
    for past in (R.line(replace(R.BASE, wall=WALL_MAX), R.plus()), f"format {WALL_MAX}"):
        done = subprocess.run([str(binary)], input=past + "\n", capture_output=True, text=True, timeout=600,
                              check=False)
        if done.returncode != 3:
            raise LaneError(f"a wall clock past the program's ended the run with {done.returncode}: {past[:60]}")
    steps["program"], mark = round(time.monotonic() - mark, 1), time.monotonic()
    caught = {}
    for mutant in MUTANTS:
        planted = build(cake, f"article-{mutant}", lanes.emit("emit-article-mutant", mutant))
        # The articles alone: the dates written and read back reach no code the mutants change.
        said = run(planted, lines, f"the mutant {mutant}")
        differs = next((case for case, want, got in zip(lines, model, said, strict=True) if want != got), None)
        if differs is None:
            raise LaneError(f"the mutant {mutant} was not caught")
        caught[mutant] = differs[:120]
    steps["mutants"], mark = round(time.monotonic() - mark, 1), time.monotonic()
    timed = {}
    small, long = hard(SMALL), hard(LONGEST)
    timing = [R.line(R.BASE, a) for _, a in small] + [R.line(R.BASE, a) for _, a in long]
    expected = R.run(model_command, timing)
    runs = [run(binary, timing, "the timed run", timed=True) for _ in range(RUNS)]
    for k, (name, a) in enumerate(long):
        answer = runs[0][len(small) + k].rsplit(" ", 1)[0]
        if answer != expected[len(small) + k]:
            raise LaneError(f"the long article of {name}: the model answers {expected[len(small) + k][:200]}, "
                            f"the program {answer[:200]}")
        t_small = min(int(r[k].rsplit(" ", 1)[1]) for r in runs)
        t_long = min(int(r[len(small) + k].rsplit(" ", 1)[1]) for r in runs)
        if t_long * len(small[k][1]) > SLOWER * max(t_small, 1) * len(a):
            raise LaneError(f"{name}: {t_long} us for {len(a)} octets, {t_small} us for {len(small[k][1])}")
        timed[name] = {"octets": len(a), "microseconds": t_long, "small_octets": len(small[k][1]),
                       "small_microseconds": t_small}
    steps["timed"] = round(time.monotonic() - mark, 1)
    worst = max(timed, key=lambda name: timed[name]["microseconds"])
    measured = {"cases": f"{len(asked):,}", "hard forms": f"{len(long)}", "mutants": f"{len(MUTANTS)}"}
    lanes.require_stated([
        ("docs/baseline.md", [("\n| Article acceptance in Pancake |", "\n|")], measured),
        ("docs/baseline.md", [("\n### Article acceptance in Pancake\n", "\n### ")],
         {**measured, "contexts past the bounds": f"{len(R.PAST_BOUNDS)}"}),
        ("docs/assurance.md", [("\n| Article acceptance in Pancake (", "\n|")],
         {k: v for k, v in measured.items() if k != "cases"})])
    return Report("matched", cake, [HOST], {
        "cases": len(asked), "articles": len(lines), "past_bounds": len(R.PAST_BOUNDS),
        "mutants_caught": caught, "timed": timed, "slowest": worst,
        "seconds_by_step": steps})


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--cake", default=os.environ.get("CAKE"))
    args = parser.parse_args()
    lanes.require_platform(parser)
    cake = lanes.given_cake(parser, args.cake)
    lanes.lane_main("ACCEPT", OUT, lambda: check(cake))


if __name__ == "__main__":
    main()
