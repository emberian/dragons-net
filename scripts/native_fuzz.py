#!/usr/bin/env python3
# SPDX-License-Identifier: AGPL-3.0-or-later
"""Generated programs, held three ways: the Lean model, an independent interpreter, and the code
CakeML compiles from the printed source.

`dn-compiler emit-fuzz SEED COUNT VECTORS` draws bounded programs of the subset the gate accepts
(`DN.Compiler.Gen`), prints each through the gate, runs its lowering in the model on each input,
and gives the canonical tree for the parser contract. This script

- runs every program on every input in `fuzz_interp`, which reads the source rather than the
  lowering, and requires the value and every changed word to be the model's;
- holds every printed program against the tree the pinned parser builds from it
  (`parser_contract.compare`, with what it compiles in `build/fuzz/parser/`);
- compiles all programs into one file, links them with `native/fuzz_driver.c`, which maps each
  buffer between pages without access, writes the real addresses into the page of pointers and
  stops a call that runs too long, and requires every call to return the model's value and change
  exactly the model's words; the host is first shown to catch a call that hangs, one that reads
  past its buffer and one that writes beside the result slot;
- counts what the calls reached and fails if any construct the generator is meant to reach was
  reached by none;
- reduces the first disagreement of any of the three kinds (`fuzz_reduce`) to a small case in
  `build/fuzz/minimized/`;
- prints the programs through printers with one defect planted in each, requires the lane to catch
  every one, and reduces again the program each case in `tests/corpus/mutants/` was reduced from,
  requiring the same case; and runs each case in `tests/corpus/found/` as it stands, requiring
  agreement. `DN.Compiler.GenCorpus` holds both sets as well.

The run on every change uses the fixed seed below. `--seed`, `--count` and `--vectors` make other
runs, which leave out the planted defects and the corpus; `--bootstrapped` runs the lane with the
compiler built from the patched source, after checking its digest.
"""
from __future__ import annotations

import argparse
from collections import Counter
from collections.abc import Callable
import json
import os
from pathlib import Path
import re
import shutil
import signal
import subprocess
import sys
import time
from typing import Any

sys.path.insert(0, str(Path(__file__).resolve().parent))
# The path above is what makes these importable.
import fuzz_interp as interp
import fuzz_reduce as reducer
import lanes
from lanes import NATIVE, ROOT, Diagnostics, LaneError, Report
import parser_contract as contract

OUT = ROOT / "build/fuzz"
MUTANT_CASES = ROOT / "tests/corpus/mutants"
FOUND_CASES = ROOT / "tests/corpus/found"
HOST = NATIVE / "fuzz_driver.c"
# The run on every change: chosen so that it reaches every construct below; a choice, not a
# derived bound.
SEED, COUNT, VECTORS = 1, 300, 4
# What some call has to reach, as the interpreter counts it.
REACHED = ("load word", "load byte", "store word", "store byte", "word in word address",
           "byte in word address", "word in byte address", "byte in byte address",
           "pointer from the table", "pointer local", "computed address",
           "one byte through two pointers, stored to", "branch taken", "branch not taken",
           "loop iteration", "declaration in an inner block", "return in a loop", "return in a branch",
           *(f"{edge} {size} of buffer {b}" for edge in ("first", "last") for size in ("byte", "word")
             for b in range(interp.BUFFERS)),
           *(f"operator {op}" for op in ("+", "-", "*", "&", "<", "<=", "==", ">>>")))
# What some program has to use, as the type check counts it.
USED = ("a name declared again in a sibling block", *(f"{n} parameters" for n in range(4)))
Transform = Callable[[str], str] | None


def shift_plus_one(source: str) -> str:
    def moved(m: re.Match[str]) -> str:
        k = int(m.group(1))
        return f">>> {k + 1 if k < 63 else k - 1}"
    return re.sub(r">>> (\d+)", moved, source)


# Printers with one defect each: what the lane has to catch.
MUTANTS: dict[str, Callable[[str], str]] = {
    # `<=` printed as `<`
    "le-as-lt": lambda s: s.replace(" <= ", " < "),
    # a byte store printed as a word store
    "st8-as-st": lambda s: re.sub(r"(?m)^(\s*)st8 ", r"\1st ", s),
    # a byte load printed as a word load
    "ld8-as-lds": lambda s: s.replace("ld8 ", "lds 1 "),
    # the condition of an `if` printed negated, which swaps its branches
    "if-negated": lambda s: re.sub(r"(?m)^(\s*)if (.*) \{$", r"\1if (\2) == 0 {", s),
    # a shift distance printed one off
    "shift-off-by-one": shift_plus_one,
}
# The host's own checks: a call that never returns, one that reads the page after its buffer, and
# one that writes beside the result slot, each with what the host has to report.
HOST_CHECKS = [
    (("export fun dn_hang(1 dn_result) {\n  var i = 0;\n  while 0 < 1 {\n    i = i + 1;\n  }\n"
      "  st dn_result, i;\n  return 0;\n}\n"), "dn_hang", [], "timeout"),
    ("export fun dn_past(1 p, 1 dn_result) {\n  st dn_result, ld8 (p + 4096);\n  return 0;\n}\n", "dn_past",
     [{"name": "p", "kind": "pointer", "buffer": 0, "offset": 0}], "fault"),
    ("export fun dn_beside(1 dn_result) {\n  st dn_result - 8, 1;\n  st dn_result, 0;\n  return 0;\n}\n",
     "dn_beside", [], "beside the slot"),
]


def dn(args: list[str], stdin: str | None = None, timeout: int = 600) -> Any:
    return json.loads(lanes.emit(*args, stdin=stdin, timeout=timeout))


def replay(cases: list[dict[str, Any]]) -> list[dict[str, Any]]:
    """Programs given as data, checked, printed and run by the model."""
    inputs = [{"program": c["program"], "plan": c["plan"], "vectors": c["vectors"]} for c in cases]
    records: list[dict[str, Any]] = dn(["run-fuzz"], json.dumps(inputs))
    return records


def disagreement(record: dict[str, Any], reached: Counter[str] | None = None) -> tuple[int, str] | None:
    """The first input on which the interpreter does not give the model's answer, and how."""
    for index, vector in enumerate(record["vectors"]):
        try:
            result, changed, got = interp.run(record["program"], record["plan"], vector)
        except interp.Fault as fault:
            return index, f"the interpreter stops ({fault}), the model returns {vector['result']}"
        if (result, changed) != (vector["result"], vector["changed"]):
            return index, (f"the model and the interpreter disagree\nmodel:       {vector['result']} "
                           f"{vector['changed']}\ninterpreter: {result} {changed}")
        if reached is not None:
            reached.update(got)
    return None


def call_line(index: int, plan: dict[str, Any], vector: dict[str, Any]) -> str:
    seed, mask = vector["fill"]
    parts = [str(index), str(seed), str(mask), str(len(plan["entries"]))]
    parts += [str(x) for b, o in plan["entries"] for x in (b, o)]
    parts.append(str(len(plan["params"])))
    for p in plan["params"]:
        if p["kind"] == "data":
            parts += ["d", str(vector["data"][p["name"]])]
        elif p["kind"] == "pointer":
            parts += ["p", str(p["buffer"]), str(p["offset"])]
        else:
            parts.append("t")
    return " ".join(parts) + "\n"


class Native:
    """Compiles programs into one executable with the host and runs calls through it. The host and
    the runtime are compiled once, and the protections of the linked binary read back once: the
    flags and the host are the same for every binary of the run."""

    def __init__(self, cake: str, out: Path) -> None:
        self.cake, self.out = cake, out
        self.objects = [lanes.compile_object(source, out / f"{source.stem}.o")
                        for source in (HOST, NATIVE / "cake_runtime.c")]
        self.hardened = False

    def build(self, name: str, sources: list[tuple[str, str, int]], *, symbols: bool = False) -> Path:
        """Each source with the function it defines and its parameter count. `symbols` checks the
        names the programs export, for programs whose names the script did not choose."""
        pnk, asm = self.out / f"{name}.pnk", self.out / f"{name}.S"
        pnk.write_text("".join(source for source, _, _ in sources))
        asm.write_bytes(lanes.pancake(self.cake, pnk, timeout=600 + len(sources) // 10))
        if symbols:
            lanes.check_symbols(asm)
        calls = ['#include <stddef.h>', '#include <stdint.h>']
        for _, fn, arity in sources:
            calls.append(f"uint32_t {fn}({', '.join(['uint64_t'] * (arity + 1))});")
        calls.append("int dn_fuzz_call(size_t fn, const uint64_t *args, size_t count, uint32_t *status) {")
        calls.append("    switch (fn) {")
        for index, (_, fn, arity) in enumerate(sources):
            arguments = ", ".join(f"args[{k}]" for k in range(arity + 1))
            calls.append(f"    case {index}: if (count != {arity + 1}) return -1; "
                         f"*status = {fn}({arguments}); return 0;")
        calls.append("    default: return -1;\n    }\n}\n")
        dispatch = self.out / f"{name}-calls.c"
        dispatch.write_text("\n".join(calls))
        binary = lanes.link(self.out / name, [*self.objects, dispatch, asm], timeout=120 + len(sources) // 10,
                            check=not self.hardened)
        self.hardened = True
        return binary

    def run(self, binary: Path, lines: list[str]) -> list[Any]:
        """What each call did: status, result and changed words; or `fault` for a call that touched
        a page without access, `timeout` for one the host stopped, `beside the slot` for one that
        wrote next to the result slot. Each of those ends the host, so the calls after it are run
        again."""
        outcomes: list[Any] = []
        while len(outcomes) < len(lines):
            try:
                done = subprocess.run([str(binary)], input="".join(lines[len(outcomes):]), capture_output=True,
                                      text=True, timeout=60 + len(lines), check=False)
            except subprocess.TimeoutExpired as late:
                raise LaneError(f"the host did not finish after call {len(outcomes)} of {len(lines)}") from late
            for line in done.stdout.splitlines():
                numbers = [int(x) for x in line.split()]
                status, result, count = numbers[:3]
                changed = [numbers[3 + 3 * k:6 + 3 * k] for k in range(count)]
                outcomes.append((status, result, changed))
            if done.returncode == 0:
                if len(outcomes) != len(lines):
                    raise LaneError("the host answered fewer calls than it was given")
            elif done.returncode in (-signal.SIGSEGV, -signal.SIGBUS):
                outcomes.append("fault")
            elif done.returncode == -signal.SIGALRM:
                outcomes.append("timeout")
            elif done.returncode == 1 and "wrote beside the result slot" in done.stderr:
                outcomes.append("beside the slot")
            else:
                raise LaneError(f"the host stopped with status {done.returncode}:\n{done.stderr}")
        return outcomes


def native_outcomes(native: Native, name: str, records: list[dict[str, Any]],
                    transform: Transform = None) -> list[list[Any]]:
    """Every record's outcome on each of its inputs, compiled from its source as printed or as
    `transform` rewrites it."""
    sources = []
    for record in records:
        source = record["source"]
        sources.append((transform(source) if transform else source, record["name"], len(record["plan"]["params"])))
    binary = native.build(name, sources, symbols=name == "programs")
    lines = [call_line(i, r["plan"], v) for i, r in enumerate(records) for v in r["vectors"]]
    flat = native.run(binary, lines)
    out, at = [], 0
    for record in records:
        out.append(flat[at:at + len(record["vectors"])])
        at += len(record["vectors"])
    return out


def agrees(outcome: Any, vector: dict[str, Any]) -> bool:
    return bool(outcome == (0, vector["result"], vector["changed"]))


def case_of(record: dict[str, Any], vector_index: int) -> reducer.Case:
    vector = record["vectors"][vector_index]
    return {"program": record["program"], "plan": record["plan"],
            "vector": {"data": vector["data"], "fill": vector["fill"]}}


def renamed(case: reducer.Case, name: str) -> dict[str, Any]:
    return {"program": {**case["program"], "name": name}, "plan": case["plan"], "vectors": [case["vector"]]}


def valid(cases: list[reducer.Case]) -> list[tuple[int, dict[str, Any]]]:
    """The candidates the gate accepts and the model runs, as records, with their positions."""
    records = replay([renamed(c, f"dn_reduce_{k}") for k, c in enumerate(cases)])
    return [(k, r) for k, r in enumerate(records) if "error" not in r]


def native_verdicts(native: Native, records: list[dict[str, Any]], transform: Transform) -> list[bool]:
    """Whether the code of each record still disagrees on its input and, for a planted defect,
    agrees when printed without it. A batch the compiler warns about is judged one by one, and a
    candidate it warns about does not count as failing."""
    try:
        planted = native_outcomes(native, "reduce", records, transform)
        control = native_outcomes(native, "control", records) if transform else None
    except Diagnostics:
        if len(records) == 1:
            return [False]
        return [v for r in records for v in native_verdicts(native, [r], transform)]
    return [not agrees(planted[n][0], r["vectors"][0]) and (control is None or agrees(control[n][0], r["vectors"][0]))
            for n, r in enumerate(records)]


def native_failure(native: Native, transform: Transform) -> Callable[[list[reducer.Case]], list[bool]]:
    """The reducer's question for a disagreement of the compiled code: still valid, the model and
    the interpreter still agree, and the code still disagrees - for a planted defect, only as the
    defective printer prints it, so the disagreement is the defect's."""
    def fails(cases: list[reducer.Case]) -> list[bool]:
        verdict = [False] * len(cases)
        chosen = [(k, r) for k, r in valid(cases) if disagreement(r) is None]
        if chosen:
            for (k, _), v in zip(chosen, native_verdicts(native, [r for _, r in chosen], transform), strict=True):
                verdict[k] = v
        return verdict
    return fails


def model_failure(cases: list[reducer.Case]) -> list[bool]:
    """The reducer's question for a disagreement of the model and the interpreter."""
    verdict = [False] * len(cases)
    for k, record in valid(cases):
        verdict[k] = disagreement(record) is not None
    return verdict


def parser_failure(cake: str) -> Callable[[list[reducer.Case]], list[bool]]:
    """The reducer's question for a program the parser does not read as its lowering."""
    def fails(cases: list[reducer.Case]) -> list[bool]:
        verdict = [False] * len(cases)
        for k, record in valid(cases):
            try:
                contract.compare(cake, [record["tree"]], "reduce", out=OUT / "parser")
            except contract.ContractError:
                verdict[k] = True
        return verdict
    return fails


def fixture(kind: str, name: str, case: reducer.Case, original: reducer.Case, origin: dict[str, Any],
            stats: dict[str, int], native: Native | None = None, transform: Transform = None,
            cake: str | None = None) -> dict[str, Any]:
    """A reduced case as it is recorded: the program, its input, what the model says, and what the
    side that disagrees says; with the case it was reduced from."""
    [record] = replay([renamed(case, "dn_min")])
    vector = record["vectors"][0]
    out: dict[str, Any] = {
        "name": name, "kind": kind, "origin": origin, "reduction": stats,
        "original": {"program": original["program"], "plan": original["plan"], "input": original["vector"]},
        "plan": record["plan"], "program": record["program"], "source": record["source"],
        "input": {"data": vector["data"], "fill": vector["fill"]},
        "model": {"result": vector["result"], "changed": vector["changed"]}}
    if kind == "native" and native is not None:
        [[observed]] = native_outcomes(native, "fixture", [record], transform)
        out["printed"] = transform(record["source"]) if transform else record["source"]
        out["native"] = observed if isinstance(observed, str) else {
            "status": observed[0], "result": observed[1], "changed": observed[2]}
    elif kind == "model":
        found = disagreement(record)
        out["interpreter"] = found[1] if found else "agrees"
    elif kind == "parser":
        if cake is None:
            raise LaneError("a parser disagreement is recorded with the compiler whose parser it is")
        try:
            contract.compare(cake, [record["tree"]], "fixture", out=OUT / "parser")
            out["parser"] = "agrees"
        except contract.ContractError as error:
            out["parser"] = str(error)
    return out


def dumped(data: Any) -> str:
    return json.dumps(data, indent=1, sort_keys=True) + "\n"


def minimized(kind: str, case: reducer.Case, fails: Callable[[list[reducer.Case]], list[bool]],
              origin: dict[str, Any], **side: Any) -> str:
    """Reduce a disagreement found in a run, keep it in build/fuzz/minimized/, and say so."""
    small, stats = reducer.reduce(case, fails)
    text = dumped(fixture(kind, "disagreement", small, case, origin, stats, **side))
    (OUT / "minimized").mkdir(parents=True, exist_ok=True)
    (OUT / "minimized" / f"{kind}.json").write_text(text)
    return f"reduced to build/fuzz/minimized/{kind}.json:\n{text}"


def smallest_failure(records: list[dict[str, Any]], outcomes: list[list[Any]]) -> tuple[int, int] | None:
    failing = [(reducer.size(case_of(r, j)), i, j) for i, r in enumerate(records)
               for j, (o, v) in enumerate(zip(outcomes[i], r["vectors"], strict=True)) if not agrees(o, v)]
    if not failing:
        return None
    _, i, j = min(failing)
    return i, j


def check_host(native: Native) -> int:
    """The host catches what it says it catches: without this, a hang or a stray access would be
    judged by nothing but the time limit of the job."""
    binary = native.build("host", [(source, fn, len(params)) for source, fn, params, _ in HOST_CHECKS])
    lines = [call_line(i, {"params": params, "entries": []}, {"fill": [0, 0], "data": {}})
             for i, (_, _, params, _) in enumerate(HOST_CHECKS)]
    got = native.run(binary, lines)
    wanted = [outcome for _, _, _, outcome in HOST_CHECKS]
    if got != wanted:
        raise LaneError(f"the host reports {got} for calls that should give {wanted}")
    return len(HOST_CHECKS)


def check_mutant(native: Native, records: list[dict[str, Any]], name: str, seed: int,
                 write: bool) -> dict[str, Any]:
    """The lane catches the planted defect, and the case recorded for it is what reducing the
    program it came from gives, again."""
    transform = MUTANTS[name]
    changed = sum(transform(r["source"]) != r["source"] for r in records)
    if not changed:
        raise LaneError(f"the planted defect {name} changes no printed program; it tests nothing here")
    outcomes = native_outcomes(native, f"mutant-{name}", records, transform)
    caught = sum(not agrees(o, v) for r, got in zip(records, outcomes, strict=True)
                 for o, v in zip(got, r["vectors"], strict=True))
    if not caught:
        raise LaneError(f"the lane does not catch the planted defect {name}")
    path = MUTANT_CASES / f"{name}.json"
    fails = native_failure(native, transform)
    recorded: dict[str, Any] = {} if write else json.loads(path.read_text())
    if write:
        found = smallest_failure(records, outcomes)
        if found is None:
            raise LaneError(f"no call disagrees under {name}")
        i, j = found
        original, origin = case_of(records[i], j), {"seed": seed, "program": records[i]["name"], "input": j}
    else:
        start = recorded["original"]
        original = {"program": start["program"], "plan": start["plan"], "vector": start["input"]}
        origin = recorded["origin"]
        if not fails([original])[0]:
            raise LaneError(f"the case {path.name} was reduced from no longer shows {name}")
    started = time.monotonic()
    case, stats = reducer.reduce(original, fails)
    result = fixture("native", name, case, original, origin, stats, native, transform)
    if write:
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(dumped(result))
    else:
        # How many candidates the reducer asked about is a note, not part of the case.
        if {**recorded, "reduction": None} != {**result, "reduction": None}:
            (OUT / "minimized").mkdir(parents=True, exist_ok=True)
            (OUT / "minimized" / f"{name}.json").write_text(dumped(result))
            raise LaneError(f"reducing again gives another case than {path.relative_to(ROOT)}; the new one is in "
                            f"build/fuzz/minimized/{name}.json (--write-corpus records it)")
    return {"programs_changed": changed, "calls_caught": caught, "reduced_nodes": reducer.size(case)[0],
            "asked": stats["asked"], "taken": stats["taken"], "seconds": round(time.monotonic() - started, 1)}


def check_corpus(native: Native) -> dict[str, int]:
    """The recorded cases are the ones the Lean corpus holds; the planted ones match the planted
    defects, and each found one now runs as the model says."""
    held = dn(["emit-corpus"])
    sets = {"mutants": MUTANT_CASES, "found": FOUND_CASES}
    for kind, directory in sets.items():
        files = {p.stem: json.loads(p.read_text()) for p in sorted(directory.glob("*.json"))}
        lean = {c["name"]: c for c in held[kind]}
        if sorted(files) != sorted(lean):
            raise LaneError(f"{directory.relative_to(ROOT)} holds {sorted(files)}, "
                            f"DN.Compiler.GenCorpus {sorted(lean)}")
        for name, recorded in files.items():
            for field in ("plan", "program", "input", "model"):
                if recorded[field] != lean[name][field]:
                    raise LaneError(f"{directory.relative_to(ROOT)}/{name}.json: its {field} is not the one "
                                    f"DN.Compiler.GenCorpus holds")
    if sorted(c["name"] for c in held["mutants"]) != sorted(MUTANTS):
        raise LaneError(f"the planted cases are {sorted(c['name'] for c in held['mutants'])}, "
                        f"the planted defects {sorted(MUTANTS)}")
    found = [{"program": c["program"], "plan": c["plan"], "vectors": [c["input"]]} for c in held["found"]]
    if found:
        records = replay(found)
        for record, case in zip(records, held["found"], strict=True):
            if "error" in record or disagreement(record) is not None:
                raise LaneError(f"the found case {case['name']} no longer runs in the model and the interpreter")
        for outcome, record in zip(native_outcomes(native, "found", records), records, strict=True):
            if not agrees(outcome[0], record["vectors"][0]):
                raise LaneError(f"the compiled code disagrees again on the found case {record['name']}")
    return {"mutants": len(held["mutants"]), "found": len(held["found"])}


def parsed_as_lowered(cake: str, records: list[dict[str, Any]], origin: dict[str, Any]) -> int:
    """Every program read by the parser as its lowering: how many functions matched. A program
    that is not is reduced; a batch that fails with every program in it read right alone is
    reported as such."""
    # `cake --explore` prints every intermediate program, and on thousands of functions at once
    # it runs out of its own memory, so the contract takes them a few hundred at a time.
    matched = 0
    for k in range(0, len(records), 500):
        chunk = records[k:k + 500]
        try:
            matched += contract.compare(cake, [r["tree"] for r in chunk], f"fuzz-{k}", out=OUT / "parser")
        except contract.ContractError as error:
            record = next((r for r in chunk if parser_failure(cake)([case_of(r, 0)])[0]), None)
            if record is None:
                raise LaneError(f"the parser contract fails on programs {k}-{k + len(chunk) - 1} together and "
                                f"on none alone:\n{error}") from error
            # The contract's message starts with the function's name already.
            raise LaneError(f"{error}\n" + minimized(
                "parser", case_of(record, 0), parser_failure(cake),
                {**origin, "program": record["name"], "input": 0}, cake=cake)) from error
    return matched


def generated(cake: str, seed: int, count: int, vectors: int, standard: bool, write: bool) -> Report:
    shutil.rmtree(OUT / "minimized", ignore_errors=True)
    records = dn(["emit-fuzz", str(seed), str(count), str(vectors)], timeout=600 + count * vectors // 50)
    (OUT / "programs.json").write_text(json.dumps(records))
    origin = {"seed": seed, "count": count, "vectors": vectors}
    reached: Counter[str] = Counter()
    used: Counter[str] = Counter()
    for record in records:
        try:
            used.update(interp.check_types(record["program"], record["plan"]))
        except interp.TypeViolation as violation:
            raise LaneError(f"{record['name']} lets a pointer into a value: {violation}") from violation
        found = disagreement(record, reached)
        if found is not None:
            j, how = found
            raise LaneError(f"{record['name']} input {j}: {how}\n" + minimized(
                "model", case_of(record, j), model_failure, {**origin, "program": record["name"], "input": j}))
    matched = parsed_as_lowered(cake, records, origin)
    native = Native(cake, OUT)
    host = check_host(native)
    outcomes = native_outcomes(native, "programs", records)
    failure = smallest_failure(records, outcomes)
    if failure is not None:
        i, j = failure
        raise LaneError(f"{records[i]['name']} input {j}: the compiled code disagrees with the model; " + minimized(
            "native", case_of(records[i], j), native_failure(native, None),
            {**origin, "program": records[i]["name"], "input": j}, native=native))
    missing = [what for what in REACHED if not reached[what]] + [what for what in USED if not used[what]]
    if missing:
        raise LaneError(f"no call reaches {missing}; the generator no longer covers them")
    mutants: dict[str, Any] = {}
    corpus = {"mutants": 0, "found": 0}
    calls = sum(len(r["vectors"]) for r in records)
    if standard:
        mutants = {name: check_mutant(native, records, name, seed, write) for name in MUTANTS}
        corpus = check_corpus(native)
        lanes.require_quoted({"docs/baseline.md": (f"{len(records)} generated programs", f"{calls:,} calls"),
                              "docs/assurance.md": (f"{len(records)} generated programs",),
                              "README.md": (f"{len(records)} generated programs",)})
    return Report("matched", cake, [HOST, *lanes.RUNTIME], {
        "seed": seed, "programs": len(records), "calls": calls, "parsed_functions": matched,
        "host_checks": host, "reached": dict(sorted(reached.items())), "used": dict(sorted(used.items())),
        "mutants": mutants, "corpus": corpus})


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--cake", default=os.environ.get("CAKE", ""))
    parser.add_argument("--bootstrapped", action="store_true",
                        help="run with the compiler built from the patched source (backend/bootstrap-record.json)")
    parser.add_argument("--seed", type=int, default=SEED)
    parser.add_argument("--count", type=int, default=COUNT)
    parser.add_argument("--vectors", type=int, default=VECTORS)
    parser.add_argument("--write-corpus", action="store_true",
                        help="record the planted cases in tests/corpus/mutants instead of comparing")
    args = parser.parse_args()
    lanes.require_platform(parser)
    cake = None if args.bootstrapped else lanes.given_cake(parser, args.cake)
    standard = (args.seed, args.count, args.vectors) == (SEED, COUNT, VECTORS)
    if args.write_corpus and not standard:
        parser.error("the corpus is recorded from the standard run only")
    lanes.lane_main("GENERATED PROGRAMS", OUT, lambda: generated(
        cake or lanes.bootstrapped(), args.seed, args.count, args.vectors, standard, args.write_corpus))


if __name__ == "__main__":
    main()
