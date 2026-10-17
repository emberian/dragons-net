#!/usr/bin/env python3
# SPDX-License-Identifier: AGPL-3.0-or-later
"""The grammar of header fields as Pancake functions (`DN.News.AbnfProg`), compiled by CakeML and run
by native/grammar_check.c, held to the Lean interpreter (`dn-compiler abnf-model`): the two have to
give the same answer on every case of the grammar lane (scripts/abnf_check.py) and on fields that are
long, nested or ambiguous in the ways a client can make them, each at a size the interpreter answers
in time. Some cases start the matches from several positions, answered as the interpreter answers
the input after each. Each mutant of the program has to answer some case otherwise. The same fields,
as long as a header section may be, are answered as at the smaller size and timed: per octet, no
slower than twice their time there, which a match whose work grew with the square of the field's
length would be. On every call the host requires the heap outside the program's area
untouched and the header the compiler theorem requires intact (docs/baseline.md, "Header field
grammar in Pancake").
"""
from __future__ import annotations

import argparse
from collections.abc import Callable
import os
from pathlib import Path
import random
import subprocess
import sys

sys.path.insert(0, str(Path(__file__).resolve().parent))
import abnf_check as A  # the path above is what makes these importable
import gen_abnf as G
import lanes
from lanes import NATIVE, ROOT, LaneError, Report

OUT = ROOT / "build/grammar"
HOST = NATIVE / "grammar_check.c"
MUTANTS = ["rep-past-bound", "alt-last", "caseful", "comment-escape", "comment-fold", "union-window",
           "window-order"]
# The bound on a header section (decision 0005), which no field can pass.
LONGEST = 65536
# The size of a hostile field the interpreter answers, which takes time that grows faster than its
# length does.
SMALL = 4096
# How much slower per octet a long field may be than a small one of the same form: twice, where
# planted work growing with the square of a field takes 4.6 times.
SLOWER = 2
# Times are the least of this many runs.
RUNS = 3
CRLF = b"\r\n"
SEED = 20261016
# Two comments, the second inside the first and ending first: `(` at 0 and 70, `)` at 99 and 199.
NESTED = b"(" + b"a" * 69 + b"(" + b"a" * 28 + b")" + b"a" * 99 + b")"
# A case: a rule, the bytes, and the positions the matches start from.
Case = tuple[str, bytes, tuple[int, ...]]


def fold(parts: list[bytes], sep: bytes) -> bytes:
    """The parts joined by `sep` on lines of at most 990 octets, each line after the first folded
    with a space, which stands for the space `sep` may end with."""
    lines, line = [], b""
    for part in parts:
        if line and len(line) + len(sep) + len(part) > 990:
            lines.append(line + sep.rstrip(b" "))
            line = b" " + part
        else:
            line = line + sep + part if line else part
    lines.append(line)
    return CRLF.join(lines)


# Forms of field that make a match work hard, each a rule and a field of `k` repeated parts.
FORMS: dict[str, tuple[str, Callable[[int], bytes]]] = {
    "words": ("subject", lambda k: b"Subject: " + fold([b"word"] * k, b" ") + CRLF),
    "long pieces": ("optional-field", lambda k: b"X-Long: " + fold([b"x" * 900] * k, b" ") + CRLF),
    "nested comments": ("from", lambda k: b"From: " + b"(" * k + b")" * k + b" a@b.c" + CRLF),
    "comments": ("from", lambda k: b"From: a@b.c " + fold([b"(c)"] * k, b" ") + CRLF),
    "folded comments": ("from", lambda k: b"From: a@b.c" + b" \r\n (x)" * k + CRLF),
    "mailboxes": ("from", lambda k: b"From: " + fold([b"a@b.c"] * k, b", ") + CRLF),
    "quoted": ("from", lambda k: b'From: "' + fold([b"q"] * k, b" ") + b'" <a@b.c>' + CRLF),
    "references": ("references", lambda k: b"References: " + fold([b"<a.b@c.d>"] * k, b" ") + CRLF),
    "path": ("path", lambda k: b"Path: " + b"!".join([b"a"] * k) + CRLF),
    "newsgroups": ("newsgroups", lambda k: b"Newsgroups: " + b",".join([b"a.b"] * k) + CRLF),
    "keywords": ("keywords", lambda k: b"Keywords: " + b",".join([b"a"] * k) + CRLF),
    "spaced keywords": ("keywords", lambda k: b"Keywords: " + b" ".join([b"a"] * k) + CRLF),
    "products": ("user-agent", lambda k: b"User-Agent: " + fold([b"a/1 (c)"] * k, b" ") + CRLF),
    # Refused, after the work of the forms above.
    "keywords spoiled at the end": ("keywords", lambda k: b"Keywords: " + b",".join([b"a"] * k) + b",\x01" + CRLF),
    "path spoiled at the end": ("path", lambda k: b"Path: " + b"!".join([b"a"] * k) + b"!\x01" + CRLF),
    "comments left open": ("from", lambda k: b"From: a@b.c " + b"(" * k + CRLF),
    "quote left open": ("from", lambda k: b'From: "' + fold([b"q"] * k, b" ") + b" <a@b.c>" + CRLF),
}


def largest(make: Callable[[int], bytes], most: int) -> int:
    """The most parts whose field is at most `most` octets."""
    lo, hi = 1, 1
    while len(make(hi)) <= most:
        lo, hi = hi, hi * 2
    while hi - lo > 1:
        mid = (lo + hi) // 2
        lo, hi = (mid, hi) if len(make(mid)) <= most else (lo, mid)
    return lo


def hostile(most: int) -> list[tuple[str, str, bytes]]:
    """Each form at the most parts that fit `most` octets: its name, rule and field."""
    return [(name, rule, make(largest(make, most))) for name, (rule, make) in FORMS.items()]


def numbered(cases: list[Case], index: dict[str, int]) -> list[str]:
    """The cases as the host reads them: the rule's place in the grammar, the bytes in hex, and the
    starts unless they are 0 alone."""
    return [f"{index[rule]} {data.hex() or '-'}" + ("" if starts == (0,) else " " + ",".join(map(str, starts)))
            for rule, data, starts in cases]


def started(cases: list[Case], rng: random.Random) -> list[Case]:
    """Cases from several starts: the comments of `NESTED`, and every twentieth case from its start and
    two positions drawn in it."""
    return [(rule, NESTED, (0, 70)) for rule in ("comment", "cfws")] + [
        (rule, data, tuple(sorted({0, *rng.sample(range(1, len(data) + 1), 2)})))
        for rule, data, _ in cases[::20] if len(data) >= 2]


def answered(cases: list[Case]) -> list[str]:
    """What the interpreter answers of each case: 1 if the rule matches all of the input after one of
    its starts."""
    after = sorted({(rule, data[start:]) for rule, data, starts in cases for start in starts})
    said = dict(zip(after, A.answers([str(lanes.DN_COMPILER), "abnf-model"], after, A.WORKERS), strict=True))
    if "fuel" in said.values():
        raise LaneError("the interpreter ran out of fuel")
    return ["1" if any(said[(rule, data[start:])] == "1" for start in starts) else "0"
            for rule, data, starts in cases]


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


def times(binary: Path, lines: list[str]) -> list[int]:
    """The least time in microseconds the program took on each case, over `RUNS` runs."""
    runs = [[int(said.split()[1]) for said in run(binary, lines, "the timed run", timed=True)]
            for _ in range(RUNS)]
    return [min(column) for column in zip(*runs, strict=True)]


def check(cake: str) -> Report:
    OUT.mkdir(parents=True, exist_ok=True)
    layout = lanes.emit("emit-grammar-layout")
    (OUT / "dn_grammar_layout.h").write_text(layout)
    names = sorted(G.taken()[1])
    if f"#define DN_GRAMMAR_RULES {len(names)}\n" not in layout:
        raise LaneError(f"the program does not know the grammar's {len(names)} rules")
    index = {rule: k for k, rule in enumerate(names)}
    binary = build(cake, "grammar", lanes.emit("emit-grammar"))
    abnfgen = subprocess.run([sys.executable, str(ROOT / "scripts/bootstrap_tool.py"), "abnfgen"],
                             capture_output=True, text=True, check=True).stdout.strip()
    small = hostile(SMALL)
    once: list[Case] = [(rule, data, (0,)) for rule, data in A.corpus(abnfgen)[0]]
    once += [(rule, data, (0,)) for _, rule, data in small]
    cases = once + started(once, random.Random(SEED))  # noqa: S311 -- a fixed seed: the same cases each run
    model = answered(cases)
    lines = numbered(cases, index)
    native = run(binary, lines, "the program")
    for (rule, data, starts), want, got in zip(cases, model, native, strict=True):
        if want != got:
            raise LaneError(f"{rule} {data[:200]!r} from {starts}: the interpreter answers {want}, "
                            f"the program {got}")
    caught = {}
    for mutant in MUTANTS:
        planted = build(cake, f"grammar-{mutant}", lanes.emit("emit-grammar-mutant", mutant))
        said = run(planted, lines, f"the mutant {mutant}")
        differs = next(((case, want) for case, want, got in zip(cases, model, said, strict=True)
                        if want != got), None)
        if differs is None:
            raise LaneError(f"the mutant {mutant} was not caught")
        (rule, data, starts), want = differs
        caught[mutant] = f"{rule} {data[:60]!r} from {starts}: {want}"
    long = hostile(LONGEST)
    small_times = times(binary, numbered([(r, d, (0,)) for _, r, d in small], index))
    long_times = times(binary, numbered([(r, d, (0,)) for _, r, d in long], index))
    long_answers = [said.split()[0] for said in run(binary, numbered([(r, d, (0,)) for _, r, d in long], index),
                                                    "the long fields")]
    timed = {}
    for (name, _, short), (_, _, field), t_small, t_long, said, want in zip(
            small, long, small_times, long_times, long_answers, model[len(once) - len(small):len(once)],
            strict=True):
        if said != want:
            raise LaneError(f"the long field of {name} is answered {said}, its short one {want}")
        if t_long * len(short) > SLOWER * max(t_small, 1) * len(field):
            raise LaneError(f"{name}: {t_long} us for {len(field)} octets, {t_small} us for {len(short)}")
        timed[name] = {"accepted": want == "1", "octets": len(field), "microseconds": t_long,
                       "small_octets": len(short), "small_microseconds": t_small}
    worst = max(timed, key=lambda name: timed[name]["microseconds"])
    measured = {"cases": f"{len(cases):,}", "hostile fields": f"{len(FORMS):,}", "mutants": f"{len(MUTANTS):,}"}
    lanes.require_stated([
        ("docs/baseline.md", [("\n| Header field grammar in Pancake |", "\n|")], measured),
        ("docs/baseline.md", [("\n### Header field grammar in Pancake\n", "\n### ")],
         {**measured, "from several starts": f"{len(cases) - len(once):,}"}),
        ("docs/assurance.md", [("\n| Header field grammar in Pancake (", "\n|")],
         {k: v for k, v in measured.items() if k != "cases"})])
    return Report("matched", cake, [HOST], {
        "cases": len(cases), "from_several_starts": len(cases) - len(once), "accepted": model.count("1"),
        "hostile_forms": len(FORMS),
        "mutants_caught": caught, "timed": timed, "slowest": worst})


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--cake", default=os.environ.get("CAKE"))
    args = parser.parse_args()
    lanes.require_platform(parser)
    cake = lanes.given_cake(parser, args.cake)
    lanes.lane_main("GRAMMAR", OUT, lambda: check(cake))


if __name__ == "__main__":
    main()
