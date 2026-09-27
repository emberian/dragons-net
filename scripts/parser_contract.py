#!/usr/bin/env python3
# SPDX-License-Identifier: AGPL-3.0-or-later
"""Hold every printed program against the tree CakeML's own parser builds from it.

`dn-compiler emit-trees` gives each program the compiler prints, with the canonical tree of its
lowering (DN.Compiler.Canon). `cake --pancake --explore` prints, under "initial pancake
program", the tree the parser of that compiler built from the source. This script brings the
parser's tree to the same canonical form and requires the two to be equal, function by
function, for every compiler it is given, and no function besides. Together the programs have
to use every statement and expression form the gate accepts. Three variants of the
printed source have to be refused: one whose tree differs, one the parser does not accept, and
one with a function nobody printed.

It also holds each parser to the table `DN.Compiler.Precedence.reads`, which says where an
operand may stand without parentheses and on which the printer's proof rests: every cell the
table allows has to read as intended, and every other cell has to be refused by the parser or
read otherwise. A table with one cell turned either way has to be refused.

The release compiler, which the native lanes use, is checked on every run. `--bootstrapped` adds
the compiler built from the patched source, whose parser differs, after checking its digest
against backend/bootstrap-record.json.

The canonical form nests a chain of `+`, `*` or `&` to the right and makes statements a list;
`DN.Compiler.Canon.canon_eval` proves that this identifies only expressions that evaluate alike.
Any form of the parser's tree that this script does not know fails the check.
"""
from __future__ import annotations

import argparse
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
from typing import Any

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(Path(__file__).resolve().parent))
import native_baseline as baseline  # noqa: E402 - the path above is what makes it importable

OUT = ROOT / "build/parser"
SECTION = "# initial pancake program"
RECORD = ROOT / "backend/bootstrap-record.json"
# The mutants: a subtraction whose parentheses matter, and a nested load the parser refuses bare.
REGROUPED = ("a - (b - 1)", "a - b - 1")
BARE_LOAD = ("ld8 (ld8 p)", "ld8 ld8 p")
EXTRA = "\nfun dn_extra() {\n  return 0;\n}\n"
# What the two ways of not reading an operand as one look like.
PARSE_ERROR = "### ERROR: parse error"
MISREAD = "is not the lowered one"
# A cell the parsers read, and one they read otherwise, each with what turning it has to raise.
TURNED = (("lds/left: lds 1 ld8 x", "and it does"), ("sub/right: a - x - y", MISREAD))
# Every form the gate lets through, each of which some printed program has to use. The gate
# refuses `@base`, external calls and calls, so those are covered by the table's cells only.
STATEMENTS = {"dec", "assign", "store", "storebyte", "if", "while", "return"}
EXPRESSIONS = {"Const", "Var", "Add", "And", "Sub", "Mul", "Less", "NotLess", "Equal", "MemLoad",
               "MemLoadByte", "Lsr"}
# The function the compiler adds to every program.
ADDED_MAIN = {"params": [], "body": [["return", ["Const", 0]]]}


class ContractError(Exception):
    """The parser's tree is not the lowered one, or has a form this check does not know."""


def tokens(text: str) -> list[str]:
    out: list[str] = []
    i = 0
    while i < len(text):
        c = text[i]
        if c.isspace():
            i += 1
        elif c in "()":
            out.append(c)
            i += 1
        elif c == '"':
            end = text.index('"', i + 1)
            out.append(text[i:end + 1])
            i = end + 1
        else:
            start = i
            while i < len(text) and not text[i].isspace() and text[i] not in "()":
                i += 1
            out.append(text[start:i])
    return out


def forms(text: str) -> list[Any]:
    """The s-expressions in `text`, as nested lists of atoms."""
    stack: list[list[Any]] = [[]]
    for piece in tokens(text):
        if piece == "(":
            stack.append([])
        elif piece == ")":
            if len(stack) == 1:
                raise ContractError("an unbalanced parenthesis in the parser's tree")
            done = stack.pop()
            stack[-1].append(done)
        else:
            stack[-1].append(piece)
    if len(stack) != 1:
        raise ContractError("an unclosed parenthesis in the parser's tree")
    return stack[0]


def chain(op: str, e: list[Any]) -> list[list[Any]]:
    return chain(op, e[1]) + chain(op, e[2]) if e[0] == op else [e]


def right_nested(op: str, operands: list[list[Any]]) -> list[Any]:
    return operands[0] if len(operands) == 1 else [op, operands[0], right_nested(op, operands[1:])]


def expression(form: Any) -> list[Any]:
    if not isinstance(form, list) or not form or not isinstance(form[0], str):
        raise ContractError(f"not an expression: {form}")
    head, args = form[0], form[1:]
    if head == "Const" and len(args) == 1:
        return ["Const", int(args[0], 0)]
    if head == "Var" and len(args) == 2 and args[0] == "local":
        return ["Var", args[1]]
    if head == "BaseAddr" and not args:
        return ["BaseAddr"]
    if (head in ("Add", "And") and len(args) >= 2) or (head == "Mul" and len(args) == 2):
        operands = [operand for arg in args for operand in chain(head, expression(arg))]
        return right_nested(head, operands)
    if head in ("Sub", "Less", "NotLess", "Equal") and len(args) == 2:
        return [head, expression(args[0]), expression(args[1])]
    if head == "Lsr" and len(args) == 2:
        # One pinned parser keeps the distance as an expression, the other as a number.
        distance = ["Const", int(args[1], 0)] if isinstance(args[1], str) else expression(args[1])
        return ["Lsr", expression(args[0]), distance]
    if head == "MemLoad" and len(args) == 2 and args[0] == "1":
        return ["MemLoad", expression(args[1])]
    if head == "MemLoadByte" and len(args) == 1:
        return ["MemLoadByte", expression(args[0])]
    raise ContractError(f"an expression form this check does not know: {form}")


def block(form: Any) -> list[Any]:
    if form == "skip":
        return []
    if not isinstance(form, list) or not form or not isinstance(form[0], str):
        raise ContractError(f"not a statement: {form}")
    head, args = form[0], form[1:]
    if head == "seq":
        return [statement for arg in args for statement in block(arg)]
    if head == "annot":
        return []
    if head == "dec" and len(args) == 2 and len(args[0]) == 5 and args[0][:2] == ["local", "1"] \
            and args[0][3] == ":=":
        return [["dec", args[0][2], expression(args[0][4]), block(args[1])]]
    if head == "local" and len(args) == 3 and args[1] == ":=":
        return [["assign", args[0], expression(args[2])]]
    if head == "mem" and len(args) == 4 and args[1:3] == [":=", "byte"]:
        return [["storebyte", expression(args[0]), expression(args[3])]]
    if head == "mem" and len(args) == 3 and args[1] == ":=":
        return [["store", expression(args[0]), expression(args[2])]]
    if head == "if" and len(args) == 3:
        return [["if", expression(args[0]), block(args[1]), block(args[2])]]
    if head == "while" and len(args) == 2:
        return [["while", expression(args[0]), block(args[1])]]
    if head == "return" and len(args) == 1:
        return [["return", expression(args[0])]]
    raise ContractError(f"a statement form this check does not know: {head}")


def function(form: Any) -> tuple[str, dict[str, Any]]:
    if not (isinstance(form, list) and len(form) == 5 and form[:2] == ["func", "1"]):
        raise ContractError(f"not a function: {str(form)[:120]}")
    params = []
    for param in form[3]:
        if not (isinstance(param, list) and len(param) == 3 and param[1:] == [":", "1"]):
            raise ContractError(f"a parameter of another shape: {param}")
        params.append(param[0])
    return form[2], {"params": params, "body": block(form[4])}


def parsed(cake: str, source: str, path: Path, *, warnings: bool = True) -> dict[str, dict[str, Any]]:
    """The functions the parser of `cake` built from `source`, in canonical form. A printed
    program has to compile without a diagnostic. A cell of the table only has to parse: the
    compiler still warns about its loads from a literal address, and those warnings are beside
    what the cell asks, so for a cell they are not failures (they are not silenced either)."""
    path.write_text(source)
    with path.open("rb") as inp:
        done = subprocess.run([cake, "--pancake", "--explore", "--main_return=true"], stdin=inp,
                              capture_output=True, timeout=300, check=False)
    if done.returncode or (warnings and done.stderr):
        raise ContractError(f"{path.name} does not compile:\n{done.stderr.decode(errors='replace')}")
    text = done.stdout.decode()
    if text.count(SECTION) != 1:
        raise ContractError(f"{path.name}: the compiler did not print its parsed program once")
    section = text.split(SECTION, 1)[1].split("\n# ", 1)[0]
    functions = [function(form) for form in forms(section)]
    by_name = dict(functions)
    if len(by_name) != len(functions):
        raise ContractError(f"{path.name}: the parser's program defines a function twice")
    return by_name


def forms_used(programs: list[dict[str, Any]]) -> tuple[set[str], set[str]]:
    """The statement and expression forms the programs' lowered trees use."""
    statements: set[str] = set()
    expressions: set[str] = set()

    def exp(e: list[Any]) -> None:
        expressions.add(e[0])
        for arg in e[1:]:
            if isinstance(arg, list):
                exp(arg)

    def stmts(body: list[Any]) -> None:
        for s in body:
            statements.add(s[0])
            for arg in s[1:]:
                if isinstance(arg, list) and arg and isinstance(arg[0], str):
                    exp(arg)
                elif isinstance(arg, list):
                    stmts(arg)

    for program in programs:
        stmts(program["body"])
    return statements, expressions


def batches(programs: list[dict[str, Any]]) -> list[list[dict[str, Any]]]:
    """Programs grouped so that no two in a group share a name, to compile them together."""
    groups: list[list[dict[str, Any]]] = []
    for program in programs:
        for group in groups:
            if all(other["name"] != program["name"] for other in group):
                group.append(program)
                break
        else:
            groups.append([program])
    return groups


def compare(cake: str, programs: list[dict[str, Any]], tag: str, *, warnings: bool = True) -> int:
    """How many functions matched; any difference raises."""
    matched = 0
    for index, group in enumerate(batches(programs)):
        trees = parsed(cake, "\n".join(p["source"] for p in group), OUT / f"{tag}-{index}.pnk",
                       warnings=warnings)
        if trees.pop("main", None) != ADDED_MAIN:
            raise ContractError(f"{tag}-{index}: the parser's program lacks the `main` the compiler adds")
        extra = set(trees) - {p["name"] for p in group}
        if extra:
            raise ContractError(f"{tag}-{index}: the parser's program has functions nobody printed: "
                                f"{sorted(extra)}")
        for program in group:
            name = program["name"]
            got = trees.get(name)
            want = {"params": program["params"], "body": program["body"]}
            if got != want:
                raise ContractError(f"{name}: the parser's tree is not the lowered one\n"
                                    f"parser:  {json.dumps(got)}\nlowered: {json.dumps(want)}")
            matched += 1
    return matched


def variant(programs: list[dict[str, Any]], old: str, new: str) -> list[dict[str, Any]]:
    """One program with `old` in its source replaced by `new`; the rest are left out."""
    for program in programs:
        if program["source"].count(old) == 1:
            return [{**program, "source": program["source"].replace(old, new)}]
    raise RuntimeError(f"no printed program contains {old!r} once; the variant has nothing to change")


def refused(cake: str, programs: list[dict[str, Any]], message: str, tag: str) -> None:
    try:
        compare(cake, programs, tag)
    except ContractError as error:
        if message not in str(error):
            raise RuntimeError(f"the {tag} variant was refused for another reason: {error}") from error
        return
    raise RuntimeError(f"the {tag} variant was accepted; the contract compares nothing")


def cells_hold(cake: str, cells: list[dict[str, Any]], tag: str) -> int:
    """Hold the parser to every cell of the precedence table, both ways."""
    allowed = [cell["tree"] for cell in cells if cell["reads"]]
    if allowed:
        compare(cake, allowed, f"{tag}-cells", warnings=False)
    for index, cell in enumerate(c for c in cells if not c["reads"]):
        try:
            compare(cake, [cell["tree"]], f"{tag}-cell-{index}", warnings=False)
        except ContractError as error:
            if PARSE_ERROR in str(error) or MISREAD in str(error):
                continue
            raise
        raise ContractError(f"{cell['cell']}: the table says the parser does not read this as one "
                            f"operand, and it does")
    return len(cells)


def turned(cake: str, cells: list[dict[str, Any]], tag: str) -> None:
    """A table with one cell turned has to be refused, each way: the cell check can fail."""
    for label, message in TURNED:
        cell = next(c for c in cells if c["cell"] == label)
        try:
            cells_hold(cake, [{**cell, "reads": not cell["reads"]}], f"{tag}-turned")
        except ContractError as error:
            if message in str(error):
                continue
            raise RuntimeError(f"{label} turned was refused for another reason: {error}") from error
        raise RuntimeError(f"{label} turned was accepted; the table checks nothing")


def bootstrapped() -> str:
    """The compiler built from the patched source, if it is the one the record describes."""
    record = json.loads(RECORD.read_text())
    cake = ROOT / record["cake_path"]
    if not cake.is_file():
        raise RuntimeError(f"{cake} has not been built here; see backend/README.md")
    if baseline.digest(str(cake)) != record["cake_sha256"]:
        raise RuntimeError(f"{cake} is not the compiler {RECORD.name} records")
    return str(cake)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--cake", default=os.environ.get("CAKE", ""),
                        help="the release compiler, whose parser to hold the printed programs against")
    parser.add_argument("--bootstrapped", action="store_true",
                        help="also the compiler built from the patched source (backend/bootstrap-record.json)")
    args = parser.parse_args()
    release = shutil.which(args.cake) if args.cake else None
    if not release:
        parser.error("provide --cake or CAKE")
    compilers = [("release", release)] + ([("bootstrapped", bootstrapped())] if args.bootstrapped else [])
    OUT.mkdir(parents=True, exist_ok=True)
    report_path = OUT / "report.json"
    report_path.unlink(missing_ok=True)
    emitted = baseline.loud([str(ROOT / ".lake/build/bin/dn-compiler"), "emit-trees"], timeout=120,
                            what="emitting the printed programs")
    programs: list[dict[str, Any]] = json.loads(emitted)
    cells: list[dict[str, Any]] = json.loads(baseline.loud(
        [str(ROOT / ".lake/build/bin/dn-compiler"), "emit-cells"], timeout=120, what="emitting the table's cells"))
    names = {p["name"] for p in programs}
    statements, expressions = forms_used(programs)
    if (statements, expressions) != (STATEMENTS, EXPRESSIONS):
        raise RuntimeError(f"the printed programs do not use exactly the gate's forms: missing "
                           f"{sorted((STATEMENTS - statements) | (EXPRESSIONS - expressions))}, unknown "
                           f"{sorted((statements - STATEMENTS) | (expressions - EXPRESSIONS))}")
    used = [c for c in cells if c["used_by_proof"]]
    if not all(c["reads"] for c in used):
        raise RuntimeError("a cell the proof relies on is one the table says the parser does not read")
    results = []
    for tag, cake in compilers:
        matched = compare(cake, programs, tag)
        refused(cake, variant(programs, *REGROUPED), MISREAD, f"{tag}-regrouped")
        refused(cake, variant(programs, *BARE_LOAD), PARSE_ERROR, f"{tag}-bare-load")
        refused(cake, [{**programs[0], "source": programs[0]["source"] + EXTRA}], "nobody printed",
                f"{tag}-extra")
        held = cells_hold(cake, cells, tag)
        turned(cake, cells, tag)
        results.append({"compiler": tag, "compiler_sha256": baseline.digest(cake), "functions": matched,
                        "table_cells": held})
    report = {"status": "matched", "programs": len(programs), "distinct_names": len(names),
              "distinct_sources": len({p["source"] for p in programs}),
              "table_cells": len(cells), "table_cells_read_bare": sum(1 for c in cells if c["reads"]),
              "table_cells_used_by_proof": len(used),
              "compilers": results, "refused_variants": 3, "turned_cells": 2}
    # The counts the documents quote have to be the ones this run held.
    quotes = {
        "docs/baseline.md": (f"{len(programs)} printed programs", f"{len(cells)} cells of the precedence table",
                             f"`printed_well` relies on {len(used)}"),
        "docs/assurance.md": (f"Each of the {len(programs)} programs", f"{len(programs)} in all",
                              f"each of the {len(programs)} programs",
                              f"that table's {len(cells)} cells", f"`printed_well` relies on {len(used)}"),
    }
    for name, phrases in quotes.items():
        text = (ROOT / name).read_text()
        for phrase in phrases:
            if phrase not in text:
                raise RuntimeError(f"{name} does not say {phrase!r}")
    report_path.write_text(json.dumps(report, indent=2) + "\n")
    print(report_path.read_text(), end="")


if __name__ == "__main__":
    main()
