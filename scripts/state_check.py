#!/usr/bin/env python3
# SPDX-License-Identifier: AGPL-3.0-or-later
"""Check the Lean model's stopping states against an independent implementation.

The differential lanes run emitted code and compare the value a program computes.
They never reach the states a run stops in — a missing local, an address outside
the memory domain, an exhausted clock, a return, an external call that ends the
run — because those produce no value to compare. A transcription can drift there
unnoticed, which is what `docs/reviews/compiler-assurance.md` asks to guard
against: "a small generated differential corpus over model states and this
fragment ... Compare result constructor, locals, memory, FFI state, base address,
and clock — not only the computed word."

This is that comparison. `dn-compiler dump-states` prints every case of
`DN.Compiler.StateCorpus` with the state the Lean model ends in; the clauses
below re-derive the same answer from the same input, written from the semantics
the model was transcribed from (`docs/pancake-semantics.md`: `evaluate`, `eval`,
`mem_load_byte`, `mem_store_byte`, `write_bytearray`, `call_FFI`, `fix_clock`,
`dec_clock`, `empty_locals`, `res_var`), and every printed field is compared. A
case that disagrees is written to `build/states/` with both answers, and each
case is small enough to read: they are one construct apiece by construction.
"""
from __future__ import annotations

import argparse
import json
from pathlib import Path
import sys
from typing import Any

sys.path.insert(0, str(Path(__file__).resolve().parent))
# The path above is what makes these importable.
import lanes
from lanes import ROOT
from state_corpus import FIELDS, pairs, parse_cases, parse_sexp
from words import MASK, signed, word_op

# The corpus the HOL lane runs through panSem (scripts/check_semantics.sh).
CORPUS = ROOT / "backend/semantics/states.txt"
# The lowered operators, by the source operator that computes them.
OPERATORS = {"add": "+", "sub": "-", "and": "&", "mul": "*", "less": "<", "equal": "==", "shr": ">>>",
             "xor": "^", "or": "|", "shl": "<<"}


def byte_align(a: int) -> int:
    return a & ~7 & MASK


def byte_index(a: int, be: bool) -> int:
    """`byte_index a be`, the endianness choice (byteScript)."""
    return 8 * (7 - a % 8) if be else 8 * (a % 8)


def get_byte(a: int, w: int, be: bool) -> int:
    return (w >> byte_index(a, be)) & 0xFF


def set_byte(a: int, b: int, w: int, be: bool) -> int:
    shift = byte_index(a, be)
    return (w & ~(0xFF << shift) & MASK) | ((b & 0xFF) << shift)


class State:
    """The fields of `panSem state` the subset reads."""

    def __init__(self, locals_: dict[str, int], memory: dict[int, int], dom: set[int],
                 be: bool, clock: int, base: int, code: dict[str, tuple[list[str], Any]]) -> None:
        self.locals = dict(locals_)
        self.code = code
        self.memory = dict(memory)
        self.dom = dom
        self.be = be
        self.clock = clock
        self.base = base
        self.calls = 0
        self.trace: list[str] = []

    def copy(self) -> State:
        other = State(self.locals, self.memory, self.dom, self.be, self.clock, self.base, self.code)
        other.calls, other.trace = self.calls, list(self.trace)
        return other

    def word(self, a: int) -> int:
        return self.memory.get(a, 0)

    def load_byte(self, a: int) -> int | None:
        aligned = byte_align(a)
        return get_byte(a, self.word(aligned), self.be) if aligned in self.dom else None

    def stored(self, memory: dict[int, int], a: int, b: int) -> dict[int, int] | None:
        """`mem_store_byte`: the memory with that byte written, or nothing when the
        address is outside the domain."""
        aligned = byte_align(a)
        if aligned not in self.dom:
            return None
        return {**memory, aligned: set_byte(a, b, memory.get(aligned, 0), self.be)}

    def store_byte(self, a: int, b: int) -> bool:
        written = self.stored(self.memory, a, b)
        if written is None:
            return False
        self.memory = written
        return True

    def read_bytes(self, a: int, n: int) -> list[int] | None:
        out = []
        for i in range(n):
            b = self.load_byte((a + i) & MASK)
            if b is None:
                return None
            out.append(b)
        return out

    def write_bytes(self, a: int, bs: list[int]) -> None:
        """`write_bytearray`: the tail is written first, and a store out of range
        returns the memory *that call* was given — the writes of the tail go with
        it, not only the byte that failed. The recursion is the clause itself."""
        def written(a: int, bs: list[int], memory: dict[int, int]) -> dict[int, int]:
            if not bs:
                return memory
            tail = written((a + 1) & MASK, bs[1:], memory)
            head = self.stored(tail, a, bs[0])
            return memory if head is None else head

        self.memory = written(a, bs, self.memory)


def evaluate(exp: Any, s: State) -> int | None:
    """`eval s e`, the region subset."""
    head = exp[0]
    if head == "const":
        return int(exp[1])
    if head == "var":
        return s.locals.get(exp[1])
    if head == "base":
        return s.base
    if head in (*OPERATORS, "notless"):
        a, b = evaluate(exp[1], s), evaluate(exp[2], s)
        if a is None or b is None:
            return None
        if head == "notless":
            return 0 if signed(a) < signed(b) else 1
        # `word_sh` has no value for a shift of a whole word or more.
        return word_op(OPERATORS[head], a, b)
    if head == "loadb":
        a = evaluate(exp[1], s)
        return None if a is None else s.load_byte(a)
    if head == "loadw":
        a = evaluate(exp[1], s)
        if a is None or a not in s.dom:
            return None
        return s.word(a)
    raise SystemExit(f"unknown expression {head}")


def hex_bytes(bs: list[int]) -> str:
    return "".join(f"{b:02x}" for b in bs) if bs else "-"


def call_ffi(s: State, name: str, conf: list[int], arr: list[int],
             answers: list[str]) -> tuple[str, Any]:
    """`call_FFI`: the empty name never reaches the oracle, and a reply of the
    wrong length ends the run instead of being written back."""
    if name == "":
        return ("ret", arr)
    answer = answers[s.calls] if s.calls < len(answers) else "ret:" + hex_bytes(arr)
    record = f"{name}:{hex_bytes(conf)}:{hex_bytes(arr)}"
    if answer.startswith("final:"):
        return ("final", (name, conf, arr, answer.split(":", 1)[1]))
    s.calls += 1
    s.trace.append(record)
    if answer == "short":
        reply = arr[1:]
    else:
        body = answer.split(":", 1)[1]
        reply = [] if body == "-" else [int(body[i:i + 2], 16) for i in range(0, len(body), 2)]
    if len(reply) != len(arr):
        return ("final", (name, conf, arr, "failed"))
    return ("ret", reply)


def run(prog: Any, s: State, answers: list[str]) -> tuple[Any, State]:
    """`evaluate (prog, s)`, the region subset. Returns the result and the state."""
    head = prog[0]
    if head == "skip":
        return (None, s)
    if head == "dec":
        value = evaluate(prog[2], s)
        if value is None:
            return (("error",), s)
        before = s.locals.get(prog[1])
        inner = s.copy()
        inner.locals[prog[1]] = value
        result, after = run(prog[3], inner, answers)
        if before is None:
            after.locals.pop(prog[1], None)
        else:
            after.locals[prog[1]] = before
        return (result, after)
    if head == "assign":
        value = evaluate(prog[2], s)
        if value is None or prog[1] not in s.locals:
            return (("error",), s)
        after = s.copy()
        after.locals[prog[1]] = value
        return (None, after)
    if head in ("store", "storeb"):
        addr, value = evaluate(prog[1], s), evaluate(prog[2], s)
        if addr is None or value is None:
            return (("error",), s)
        after = s.copy()
        if head == "store":
            if addr not in s.dom:
                return (("error",), s)
            after.memory[addr] = value
            return (None, after)
        if not after.store_byte(addr, value & 0xFF):
            return (("error",), s)
        return (None, after)
    if head == "extcall":
        name = "" if prog[1] == "_" else prog[1]
        values = [evaluate(e, s) for e in prog[2:6]]
        if any(v is None for v in values):
            return (("error",), s)
        cp, cl, ap, al = (v for v in values if v is not None)
        conf, arr = s.read_bytes(cp, cl), s.read_bytes(ap, al)
        if conf is None or arr is None:
            return (("error",), s)
        after = s.copy()
        kind, payload = call_ffi(after, name, conf, arr, answers)
        if kind == "final":
            # `FFI_final` ends the run in the state the call started from: what the
            # oracle did to its own state is not kept, only the locals are cleared.
            ended = s.copy()
            ended.locals = {}
            return (("final", *payload), ended)
        after.write_bytes(ap, payload)
        return (None, after)
    if head == "seq":
        result, after = run(prog[1], s, answers)
        after.clock = min(s.clock, after.clock)
        if result is None:
            return run(prog[2], after, answers)
        return (result, after)
    if head == "if":
        value = evaluate(prog[1], s)
        if value is None:
            return (("error",), s)
        return run(prog[2] if value != 0 else prog[3], s, answers)
    if head == "while":
        value = evaluate(prog[1], s)
        if value is None:
            return (("error",), s)
        if value == 0:
            return (None, s)
        if s.clock == 0:
            after = s.copy()
            after.locals = {}
            return (("timeout",), after)
        inner = s.copy()
        inner.clock = s.clock - 1
        result, after = run(prog[2], inner, answers)
        after.clock = min(s.clock - 1, after.clock)
        if result is None or result == ("continue",):
            return run(prog, after, answers)
        if result == ("break",):
            return (None, after)
        return (result, after)
    if head == "ret":
        value = evaluate(prog[1], s)
        if value is None:
            return (("error",), s)
        after = s.copy()
        after.locals = {}
        return (("return", value), after)
    if head == "deccall":
        return call(prog, s, answers)
    raise SystemExit(f"unknown statement {head}")


def call(prog: Any, s: State, answers: list[str]) -> tuple[Any, State]:
    """`DecCall rt One f args cont`: `lookup_code` wants distinct parameters, one per argument;
    the body runs on them alone with the clock one down, `fix_clock` keeps the clock from
    growing, and only a return goes on to the continuation, with `rt` restored after it."""
    rt, fname, argexps, cont = prog[1], prog[2], prog[3], prog[4]
    args = [evaluate(e, s) for e in argexps]
    values = [a for a in args if a is not None]
    found = s.code.get(fname)
    if len(values) != len(args) or found is None:
        return (("error",), s)
    params, body = found
    if len(set(params)) != len(params) or len(params) != len(values):
        return (("error",), s)
    if s.clock == 0:
        after = s.copy()
        after.locals = {}
        return (("timeout",), after)
    inner = s.copy()
    inner.clock = s.clock - 1
    inner.locals = dict(zip(params, values, strict=True))
    result, after = run(body, inner, answers)
    after.clock = min(s.clock - 1, after.clock)
    if result is None or result in (("break",), ("continue",)):
        return (("error",), after)
    if result[0] != "return":
        ended = after.copy()
        ended.locals = {}
        return (result, ended)
    resumed = after.copy()
    resumed.locals = {**s.locals, rt: result[1]}
    outcome, final = run(cont, resumed, answers)
    if rt in s.locals:
        final.locals[rt] = s.locals[rt]
    else:
        final.locals.pop(rt, None)
    return (outcome, final)


def prog_names(prog: Any) -> set[str]:
    """The names a program binds or reads, so the comparison of locals does not
    depend on the list the dump prints."""
    head = prog[0]
    if head in ("dec", "assign"):
        return {prog[1]} | exp_names(prog[2]) | (prog_names(prog[3]) if head == "dec" else set())
    if head in ("store", "storeb"):
        return exp_names(prog[1]) | exp_names(prog[2])
    if head == "extcall":
        return set().union(*(exp_names(e) for e in prog[2:6]))
    if head == "seq":
        return prog_names(prog[1]) | prog_names(prog[2])
    if head == "if":
        return exp_names(prog[1]) | prog_names(prog[2]) | prog_names(prog[3])
    if head == "while":
        return exp_names(prog[1]) | prog_names(prog[2])
    if head == "ret":
        return exp_names(prog[1])
    if head == "deccall":
        return {prog[1]} | set().union(*(exp_names(e) for e in prog[3])) | prog_names(prog[4])
    return set()


def exp_names(exp: Any) -> set[str]:
    if exp[0] == "var":
        return {exp[1]}
    if exp[0] in ("const", "base"):
        return set()
    return set().union(*(exp_names(e) for e in exp[1:]))


def answer_of(case: dict[str, str]) -> dict[str, str]:
    """What the independent implementation says this case ends in."""
    prog, _ = parse_sexp(case["PROG"])
    functions, _ = parse_sexp(case["CODE"])
    code = {f: (params, body) for f, params, body in functions}
    dom = {int(a) for a in case["DOM"].split(",") if a}
    state = State({k: int(v) for k, v in pairs(case["LOCALS"])},
                  {int(a): int(w) for a, w in pairs(case["MEM"])},
                  dom, case["BE"] == "1", int(case["CLOCK"]), int(case["BASE"]), code)
    answers = [a for a in case["ANSWERS"].split(";") if a]
    result, final = run(prog, state, answers)
    if result is None:
        printed = "none"
    elif result[0] == "return":
        printed = f"return:{result[1]}"
    elif result[0] == "final":
        name, conf, arr, outcome = result[1], result[2], result[3], result[4]
        printed = f"final:{name or '_'}:{hex_bytes(conf)}:{hex_bytes(arr)}:{outcome}"
    else:
        printed = result[0]
    names = [n for n in case["NAMES"].split(",") if n]
    # The dump decides which locals are compared, so it has to name them all.
    expected = (prog_names(prog) | {k for k, _ in pairs(case["LOCALS"])}
                | set().union(*(set(params) | prog_names(body) for _, params, body in functions)))
    if not expected <= set(names):
        raise SystemExit(f"state check: {case['CASE']} does not print the names "
                         f"{sorted(expected - set(names))}, so their locals are not compared")
    return {
        "RESULT": printed,
        "FLOCALS": ",".join(f"{n}={final.locals.get(n, '')}" for n in names),
        "FMEM": ",".join(f"{a}={final.word(a)}" for a in sorted(dom)),
        "FCALLS": str(final.calls),
        "FTRACE": ";".join(final.trace),
        "FCLOCK": str(final.clock),
        "FBASE": str(final.base),
    }


def write_answer_of(case: dict[str, str]) -> dict[str, str]:
    """What the independent implementation leaves in memory after a write-back."""
    dom = {int(a) for a in case["WDOM"].split(",") if a}
    body = case["WBYTES"]
    bytes_ = [] if body == "-" else [int(body[i:i + 2], 16) for i in range(0, len(body), 2)]
    state = State({}, {int(a): int(w) for a, w in pairs(case["WMEM"])}, dom,
                  case["WBE"] == "1", 0, 0, {})
    state.write_bytes(int(case["WADDR"]), bytes_)
    return {"WRESULT": ",".join(f"{a}={state.word(a)}" for a in sorted(dom))}


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--compiler", type=Path, default=lanes.DN_COMPILER,
                        help="the built dn-compiler, which prints the corpus")
    parser.add_argument("--out", type=Path, default=ROOT / "build/states",
                        help="where a disagreeing case is written")
    parser.add_argument("--dump", type=Path,
                        help="read the corpus from a file instead of running the compiler")
    args = parser.parse_args()

    if args.dump is not None:
        cases = parse_cases(args.dump.read_text())
        least = 1
    else:
        try:
            printed = lanes.emit("dump-states", timeout=600, compiler=args.compiler)
        except lanes.LaneError as error:
            raise SystemExit(f"state check: {error}") from None
        # The HOL lane reads the corpus from this file, so it has to be what the model prints now.
        if not CORPUS.exists() or CORPUS.read_text() != printed:
            raise SystemExit(f"state check: {CORPUS.relative_to(ROOT)} is not what the model prints; "
                             "write it with `dn-compiler dump-states`")
        cases = parse_cases(printed)
        least = 80
    # The corpus is the point: a dump that lost most of its cases, or all of them,
    # would otherwise pass this lane in silence.
    if len(cases) < least:
        raise SystemExit(f"state check: only {len(cases)} cases; the corpus is not there")
    mismatches = []
    for case in cases:
        fields: tuple[str, ...]
        if "WRITE" in case:
            ours, fields, name = write_answer_of(case), ("WRESULT",), case["WRITE"]
        else:
            ours, fields, name = answer_of(case), FIELDS, case["CASE"]
        differing = {field: (case[field], ours[field]) for field in fields
                     if case[field] != ours[field]}
        if differing:
            # The whole case, so the file reproduces it without the compiler.
            mismatches.append({"case": name, "input": case, "ours": ours,
                               "differing": differing})
    if mismatches:
        args.out.mkdir(parents=True, exist_ok=True)
        report = args.out / "mismatches.json"
        report.write_text(json.dumps(mismatches, indent=2))
        for bad in mismatches:
            print(f"state check: {bad['case']} disagrees: {bad['differing']}", file=sys.stderr)
        print(f"state check: {len(mismatches)} of {len(cases)} cases disagree; see {report}",
              file=sys.stderr)
        return 1
    states = [c for c in cases if "CASE" in c]
    stopping = sum(1 for c in states if c["RESULT"] != "none")
    print(f"state check: {len(states)} cases agree on every field, {stopping} of them stopping, "
          f"and {len(cases) - len(states)} write-backs agree")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
