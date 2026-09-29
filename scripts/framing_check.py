#!/usr/bin/env python3
# SPDX-License-Identifier: AGPL-3.0-or-later
"""The framers (`DN.News.FramerProg`) held three ways: the Lean model `dn-compiler frame-model`
runs, an independent reference over the whole stream (`framing_ref`), and the code CakeML compiles
from the printed source, fed by `native/framing_driver.c` a chunk at a time, each call from where the
last one stopped.

The cases are every string of up to six bytes over CR, LF, ".", NUL, space and "A", whole and cut in
two at every point, for command lines of at most four octets and blocks of at most four bytes, where
every limit is within reach; the same strings, shorter, alone and after a line or a block at its
limit or up to three bytes short of it, for the sizes the session uses: lines of 512 octets and blocks
of 64 bytes; and vectors at both sizes: variants of the end-of-data sequences of SMTP smuggling
(2023), lines ended by a bare CR or LF, lines of 510 to 514 octets with their line end, a block's
end cut every way, blocks at their buffer's size, each also fed a byte at a time. A block that ends
is followed by the next from the same state, so the cases also show the state a block leaves.

The three have to agree on every case, and every way through each of the four programs has to be
taken, as the model counts them. Each defect planted in the printed programs has to be caught: a
defect of the framing rules, planted in both programs of its kind, by the cases of each; a defect
the host exists to catch, by the host, with its own message or fault.
"""
from __future__ import annotations

import argparse
from collections import Counter
from collections.abc import Iterator
from dataclasses import dataclass, field
import itertools
import os
from pathlib import Path
import signal
import subprocess
import sys

sys.path.insert(0, str(Path(__file__).resolve().parent))
import framing_ref as ref  # the path above is what makes these importable
import lanes
from lanes import NATIVE, ROOT, LaneError, Report

OUT = ROOT / "build/framing"
HOST = NATIVE / "framing_driver.c"
HOSTS = [HOST, *lanes.RUNTIME]
FRAMERS = ("frame-line", "frame-line-4", "frame-block-64", "frame-block-4")
# Each program as the model names it: its mode, its size and its function.
PROGRAMS = {"L512": ("L", 512, "dn_frame_line"), "L4": ("L", 4, "dn_frame_line_4"),
            "B64": ("B", 64, "dn_frame_block_64"), "B4": ("B", 4, "dn_frame_block_4")}
ALPHABET = bytes([0x0D, 0x0A, 0x2E, 0x00, 0x20, 0x41])
LONGEST = 6
# The longest string after a line or a block near its limit, at the real sizes.
NEAR = {"L": 3, "B": 5}
# How often every way through a program has to be taken.
TIMES = 3
SMUGGLING = (b"\n.\n", b"\n.\r\n", b"\r.\r", b"\r.\n", b"\r\n.\r", b"\r\n.\n", b"\r\n\0.\r\n",
             b"\r\n.\0\r\n")
ROOM = ("room", "full")


def line_paths() -> list[str]:
    ways = ["lf-overlong", "lf-command", "lf-malformed"]
    return ways + [f"byte-cr{c}-nul{n}-room{r}" for c in "01" for n in "01" for r in "01"]


def block_paths() -> list[str]:
    held = [f"-post-{r}" for r in ROOM]
    both = ["-pre-room-post-room", "-pre-room-post-full", "-pre-full-post-full"]
    ways = ["bol-dot", "bol-cr", "data-cr", "dot-cr", "end-accepted", "end-refused", "end-too-large"]
    ways += [f"bol-{c}{h}" for c in ("lf", "nul", "other") for h in held]
    ways += [f"data-{c}{h}" for c in ("lf", "dot", "nul", "other") for h in held]
    ways += [f"dot-{c}{h}" for c in ("lf", "dot", "nul", "other") for h in held]
    ways += [f"cr-lf{b}" for b in both] + [f"cr-cr-pre-{r}" for r in ROOM]
    ways += [f"cr-{c}{b}" for c in ("dot", "nul", "other") for b in both]
    ways += [f"dotcr-cr-pre-{r}" for r in ROOM]
    ways += [f"dotcr-{c}{b}" for c in ("dot", "nul", "other") for b in both]
    return ways


@dataclass(frozen=True)
class Defect:
    """A defect planted in the printed programs: in each of `programs`, `pattern` found `times` times
    and replaced, with `{size}` in either standing for the program's size and `{more}` for one more.
    `stops` gives, for a program, what the host has to say or the signal it has to end with; the
    cases of a program it does not name have to show the defect some way."""

    name: str
    programs: tuple[str, ...]
    pattern: str
    becomes: str
    times: int
    stops: dict[str, str] = field(default_factory=dict)


LINES, BLOCKS = ("L512", "L4"), ("B64", "B4")
FAULT = signal.Signals.SIGSEGV.name
DEFECTS = [
    # the framing rules, in both programs of their kind
    Defect("a line of the limit taken for a command", LINES, r"if {size} <= len \{", "if {more} <= len {", 1),
    Defect("a CR before another byte not spoiling the line", LINES, r"if cr \{(\n\s*)bad = 1;",
           r"if cr {\1bad = bad;", 1),
    Defect("a NUL not spoiling the line", LINES, r"if b == 0 \{(\n\s*)bad = 1;", r"if b == 0 {\1bad = bad;", 1),
    Defect("a bare LF ending a command", LINES, r"if cr & \(bad == 0\) \{", "if bad == 0 {", 1),
    Defect("a command keeping its CR", LINES, r"kept = len - 1;", "kept = len;", 1),
    Defect("the line not started afresh", LINES, r"\n\s*len = 0;\n", "\n", 1),
    Defect("one byte more kept than the limit", LINES, r"if len < {size} \{", "if len <= {size} {", 1,
           {"L512": FAULT, "L4": "wrote outside its block"}),
    Defect("a NUL not spoiling the block", BLOCKS, r"if b == 0 \{(\n\s*)bad = 1;", r"if b == 0 {\1bad = bad;", 3),
    Defect("an LF inside a line not spoiling the block", BLOCKS, r"if b == 10 \{(\n\s*)bad = 1;",
           r"if b == 10 {\1bad = bad;", 3),
    Defect("a CR inside a line not spoiling the block", BLOCKS, r"pre = 1;(\n\s*)bad = 1;",
           r"pre = 1;\1bad = bad;", 2),
    Defect("a dot starting a line taken as data", BLOCKS, r"if b == 46 \{(\n\s*)ph = 3;",
           r"if b == 46 {\1post = 1;\1ph = 1;", 1),
    Defect("a line end not held", BLOCKS, r"pre = 1;(\n\s*)post = 1;(\n\s*)ph = 0;", "ph = 0;", 1),
    Defect("one byte more held than the buffer", BLOCKS, r"if size < {size} \{", "if size <= {size} {", 2,
           {"B64": FAULT, "B4": "wrote outside its block"}),
    Defect("a block of the buffer's size taken for too large", BLOCKS, r"if {size} < size \{",
           "if {size} <= size {", 1),
    Defect("a spoiled block too large taken for too large", BLOCKS, r"if bad \{",
           "if bad & (size <= {size}) {", 1),
    Defect("a dot and a bare LF ending the block", BLOCKS, r"if b == 13 \{(\n\s*)ph = 4;",
           r"if (b == 13) + (b == 10) {\1ph = 4;", 1),
    Defect("a block not started afresh: still spoiled", BLOCKS, r"(ph = 0;\n\s*)bad = 0;", r"\1", 1),
    Defect("a block not started afresh: still at its end", BLOCKS, r"ph = 0;(\n\s*bad = 0;)", r"\1", 1),
    Defect("a block not started afresh: still holding its bytes", BLOCKS, r"if kind \{(\n\s*)size = 0;",
           r"if kind {\1size = size;", 1),
    Defect("a block read from the start of the chunk", BLOCKS, r"(\n\s*)while \(i < n\)",
           r"\1i = 0;\1while (i < n)", 1),
    # what the host is there to see, each at the size the session uses
    Defect("a position past the chunk not refused", ("L512",), r"if n < i \{", "if n + 1 < i {", 1,
           {"L512": "was not refused"}),
    Defect("a refused call writing its state", ("L512",), r"(\n\s*)return 4294967295;",
           r"\1st blk, 0;\1return 4294967295;", 3, {"L512": "a refused call wrote"}),
    Defect("a refused call reading its input", ("L512",), r"return 4294967295;", "return ld8 p;", 3,
           {"L512": FAULT}),
    Defect("a call returning past its chunk", ("L512",), r"return i;", "return i + (i == n);", 1,
           {"L512": "returned"}),
    Defect("a call stopping with nothing to report", ("L512",), r"(\n\s*)i = i \+ 1;",
           r"\1i = i + 1;\1n = i;", 1, {"L512": "with nothing to report"}),
    Defect("a line reported at a CR", ("L512",), r"if b == 10 \{", "if b == 13 {", 1,
           {"L512": "not after an LF"}),
    Defect("a line of kind 7", ("L512",), r"kind = 3;", "kind = 7;", 1, {"L512": "a line of kind 7"}),
    Defect("a line keeping more than its limit", ("L512",), r"kind = 3;(\n\s*)kept = len;",
           r"kind = 3;\1kept = len + 1;", 1, {"L512": "a line keeps 513 bytes"}),
    Defect("a line state out of range", ("L512",), r"if cr \{(\n\s*)bad = 1;", r"if cr {\1bad = 2;", 1,
           {"L512": "a state out of range"}),
    Defect("a read past the chunk", ("L512",), r"while \(i < n\)", "while (i <= n)", 1, {"L512": FAULT}),
    Defect("a block of kind 7", ("B64",), r"kind = 3;", "kind = 7;", 1, {"B64": "a block of kind 7"}),
    Defect("a block holding more than its buffer", ("B64",), r"held = size;", "held = size + 1;", 1,
           {"B64": "a block holds 65 bytes"}),
    Defect("a block state out of range", ("B64",), r"ph = 4;", "ph = 5;", 1,
           {"B64": "a block state out of range"}),
    Defect("a write into the chunk", ("B64",), r"(\n\s*)b = ld8 \(p \+ i\);", r"\1b = ld8 (p + i);\1st8 p + i, b;",
           1, {"B64": FAULT}),
]


def case(mode: str, size: int, chunks: list[bytes]) -> str:
    return " ".join([mode, str(size), *(c.hex() or "-" for c in chunks)])


def cut(stream: bytes, points: tuple[int, ...]) -> list[bytes]:
    edges = (0, *points, len(stream))
    return [stream[a:b] for a, b in itertools.pairwise(edges)]


def whole_and_halves(mode: str, size: int, stream: bytes) -> Iterator[str]:
    yield case(mode, size, [stream])
    for at in range(1, len(stream)):
        yield case(mode, size, cut(stream, (at,)))


def strings(longest: int) -> Iterator[bytes]:
    for length in range(longest + 1):
        for letters in itertools.product(ALPHABET, repeat=length):
            yield bytes(letters)


def exhaustive() -> Iterator[str]:
    for mode in ("L", "B"):
        for stream in strings(LONGEST):
            yield from whole_and_halves(mode, 4, stream)


def near_limits() -> Iterator[str]:
    """At the real sizes, short strings alone and after a line or a block at its limit or up to three
    bytes short of it."""
    for mode, size, _ in (PROGRAMS["L512"], PROGRAMS["B64"]):
        for fill in (0, size - 3, size - 2, size - 1, size):
            for stream in strings(NEAR[mode]):
                yield case(mode, size, [b"H" * fill + stream])


def every_cut_within(stream: bytes, start: int, end: int) -> Iterator[list[bytes]]:
    """The stream cut at every set of points between `start` and `end`."""
    inner = range(max(start, 1), min(end, len(stream)))
    for k in range(len(inner) + 1):
        for points in itertools.combinations(inner, k):
            yield cut(stream, points)


def vector_streams() -> Iterator[tuple[str, int, bytes, tuple[int, int] | None]]:
    """(mode, size, stream, the window to cut every way, if any)."""
    for size in (64, 4):
        for variant in SMUGGLING:
            stream = b"x" + variant + b"MAIL FROM:<a@b>\r\n.\r\n"
            yield "B", size, stream, (1, 1 + len(variant))
        for body in (b"line", b"..stuffed", b"", b".", b"a\0b", b"a\rb"):
            stream = body + b"\r\n.\r\n" + b"after"
            yield "B", size, stream, (len(body), len(body) + 5)
        # at the buffer's size, one byte below, one above
        for extra in (-1, 0, 1):
            length = size - 2 + extra
            if length >= 0:
                yield "B", size, b"a" * length + b"\r\n.\r\n", None
        yield "B", size, b"a" * (size + 10) + b"\0\r\n.\r\n", None
        yield "B", size, b"one\r\ntwo\r\n..three\r\n", None
        # a line starting with a dot and a CR, with room for one byte more and with none, each way it
        # can go on
        for fill in (size - 3, size):
            for after in (b"\r", b".", b"\0", b"A"):
                yield "B", size, b"a" * fill + b"\r\n.\r" + after + b"\r\n.\r\n", None
    for lim in (512, 4):
        for length in (lim - 3, lim - 2, lim - 1, lim, lim + 1, 3 * lim):
            if length >= 1:
                yield "L", lim, b"H" * (length - 1) + b"\r\n", None
                yield "L", lim, b"H" * length + b"\n", None
        for stream in (b"HELP\r\n", b"HELP\n", b"HEAD\rX\r\n", b"STAT\0\r\n", b"\r\n", b"\n",
                       b"QUIT\r\nHELP\r\nCAPABILITIES\r\n", b"\r\r\n", b"A\rB\rC\r\n", b"HELP\r"):
            yield "L", lim, stream, (0, len(stream))


def vectors() -> Iterator[str]:
    for mode, size, stream, window in vector_streams():
        yield from whole_and_halves(mode, size, stream)
        yield case(mode, size, [bytes([b]) for b in stream])
        if window and window[1] - window[0] <= 12:
            for chunks in every_cut_within(stream, *window):
                yield case(mode, size, chunks)


def build(cake: str, name: str, source: str) -> Path:
    pnk = OUT / f"{name}.pnk"
    pnk.write_text(source)
    asm = lanes.assemble(cake, pnk)
    return lanes.link(OUT / name, [HOST, NATIVE / "cake_runtime.c", asm], check=name == "framers")


def run(command: list[str], cases: list[str], what: str) -> subprocess.CompletedProcess[str]:
    try:
        return subprocess.run(command, input="".join(c + "\n" for c in cases), text=True,
                              capture_output=True, check=False, timeout=1800)
    except subprocess.TimeoutExpired as error:
        raise LaneError(f"{what} ran past its time") from error


def answers(command: list[str], cases: list[str], what: str) -> list[str]:
    done = run(command, cases, what)
    if done.returncode:
        raise LaneError(f"{what} failed with status {done.returncode}:\n{done.stderr[-2000:]}")
    return done.stdout.splitlines()


def program(c: str) -> str:
    mode, size, *_ = c.split(" ", 2)
    return mode + size


def model(cases: list[str]) -> tuple[list[str], Counter[str]]:
    """The model's answers, and how often it took each way through each program."""
    out = answers([str(lanes.DN_COMPILER), "frame-model"], cases, "the model")
    lines = [line for line in out if not line.startswith("path ")]
    paths: Counter[str] = Counter()
    for line in out:
        if line.startswith("path "):
            _, name, way, times = line.split(" ")
            paths[f"{name} {way}"] = int(times)
    if len(lines) != len(cases):
        raise LaneError(f"the model answered {len(lines)} of {len(cases)} cases")
    return lines, paths


def disagreement(cases: list[str], expected: list[str], got: list[str], who: str) -> str | None:
    if len(got) != len(cases):
        return f"{who} answered {len(got)} of {len(cases)} cases"
    for c, e, g in zip(cases, expected, got, strict=True):
        if e != g:
            return f"{who} on {c!r}: {g!r}, the model: {e!r}"
    return None


def functions(source: str) -> dict[str, str]:
    parts = source.split("export fun ")
    return {part.split("(", 1)[0]: "export fun " + part for part in parts if part}


def plant(source: str, defect: Defect) -> str:
    parts = functions(source)
    for name in defect.programs:
        _, size, function = PROGRAMS[name]
        pattern = defect.pattern.replace("{size}", str(size))
        becomes = defect.becomes.replace("{size}", str(size)).replace("{more}", str(size + 1))
        parts[function] = lanes.plant(parts[function], pattern, becomes, defect.times,
                                      f"{function}, for the planted defect {defect.name!r},")
    return "".join(parts.values())


def outcome(binary: Path, cases: list[str], expected: list[str], what: str) -> tuple[str, str]:
    """How the code met the cases: "wrong" and the first wrong answer, "stopped" and what the host
    said, or the signal that ended it; "right" when it answered every case as the model did."""
    done = run([str(binary)], cases, what)
    if done.returncode < 0:
        return signal.Signals(-done.returncode).name, "a page without access"
    if done.returncode == 1:
        return "stopped", done.stderr.strip()[-300:]
    if done.returncode:
        raise LaneError(f"the host failed on {what}:\n{done.stderr[-2000:]}")
    found = disagreement(cases, expected, done.stdout.splitlines(), what)
    return ("wrong", found) if found else ("right", "")


def ended_as(want: str, how: str, detail: str) -> bool:
    """Whether the code ended as `want` says: by the fault it names, or stopped by the host saying it."""
    return how == want if want == FAULT else how == "stopped" and want in detail


def caught(cake: str, source: str, index: int, defect: Defect, by_program: dict[str, tuple[list[str], list[str]]]
           ) -> dict[str, str]:
    """Each program the defect is planted in, and how its cases caught it."""
    planted = build(cake, f"defect-{index}", plant(source, defect))
    seen = {}
    for name in defect.programs:
        cases, expected = by_program[name]
        how, detail = outcome(planted, cases, expected, f"{name} with {defect.name}")
        want = defect.stops.get(name)
        if how == "right":
            raise LaneError(f"{name} with {defect.name} agreed with the model on every case")
        if want is not None and not ended_as(want, how, detail):
            raise LaneError(f"{name} with {defect.name}: wanted {want!r}, got {how}: {detail}")
        seen[name] = f"{how}: {detail}"
    return seen


def check(cake: str) -> Report:
    OUT.mkdir(parents=True, exist_ok=True)
    source = "".join(lanes.emit(f"emit-{name}") for name in FRAMERS)
    binary = build(cake, "framers", source)
    cases = [*exhaustive(), *near_limits(), *vectors()]
    expected, paths = model(cases)
    for c, e in zip(cases, expected, strict=True):
        r = ref.answer(c)
        if r != e:
            raise LaneError(f"the reference on {c!r}: {r!r}, the model: {e!r}")
    problem = disagreement(cases, expected, answers([str(binary)], cases, "the compiled framers"),
                           "the compiled framers")
    if problem:
        raise LaneError(problem)
    wanted = [f"{name} {way}" for name, (mode, _, _) in PROGRAMS.items()
              for way in (line_paths() if mode == "L" else block_paths())]
    thin = {way: paths[way] for way in wanted if paths[way] < TIMES}
    if thin:
        raise LaneError(f"ways through the programs taken fewer than {TIMES} times: {thin}")
    unknown = sorted(set(paths) - set(wanted))
    if unknown:
        raise LaneError(f"ways the lane does not list: {unknown}")
    by_program: dict[str, tuple[list[str], list[str]]] = {name: ([], []) for name in PROGRAMS}
    for c, e in zip(cases, expected, strict=True):
        by_program[program(c)][0].append(c)
        by_program[program(c)][1].append(e)
    seen = {d.name: caught(cake, source, index, d, by_program) for index, d in enumerate(DEFECTS)}
    lanes.require_quoted({"docs/baseline.md": [f"{len(cases):,} cases"]})
    return Report("checked", cake, HOSTS, {
        "source_sha256": lanes.digest(OUT / "framers.pnk"), "executable_sha256": lanes.digest(binary),
        "cases": len(cases), "longest_exhaustive": LONGEST, "alphabet": ALPHABET.hex(),
        "ways": {way: paths[way] for way in wanted}, "planted_defects_caught": seen})


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--cake", default=os.environ.get("CAKE"))
    args = parser.parse_args()
    lanes.require_platform(parser)
    cake = lanes.given_cake(parser, args.cake)
    lanes.lane_main("FRAMING", OUT, lambda: check(cake))


if __name__ == "__main__":
    main()
