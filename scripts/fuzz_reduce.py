# SPDX-License-Identifier: AGPL-3.0-or-later
"""Reduce a generated program that exposes a failure to a small one that still exposes it.

A case is a program in the form `dn-compiler emit-fuzz` prints, its memory plan and one input.
The reducer tries smaller cases in a fixed order, the way hierarchical delta debugging does:
dropping unused parameters, deleting runs of statements (halves first, then smaller runs),
replacing an `if` or a loop by the statements inside it, replacing an expression by one of its
own operands (hoisting) or by a literal, and simplifying the input. A candidate is taken only
if it is smaller, so the reduction ends; candidates are judged in batches, and of each batch the
first one that still fails is taken, which is the one a one-at-a-time search would take. The
order, the batches and the cache involve no clock or randomness, so the same case always
reduces to the same result.

Whether a candidate still fails is the caller's question. Candidates that break the pointer
discipline (`fuzz_interp.check_types`) are dropped before it is asked; one the gate refuses or
the model does not run, the caller answers no.
"""
from __future__ import annotations

from collections.abc import Callable, Iterator
import copy
import json
from typing import Any

import fuzz_interp as interp

Case = dict[str, Any]
TreePath = tuple[Any, ...]


def expression_positions(statement: list[Any]) -> list[int]:
    """Where a statement holds expressions."""
    head = statement[0]
    if head in ("var", "set"):
        return [2]
    if head in ("st", "st8"):
        return [1, 2]
    if head in ("if", "while", "return"):
        return [1]
    return []


def block_positions(statement: list[Any]) -> list[int]:
    return {"if": [2, 3], "while": [2]}.get(statement[0], [])


def get(tree: Any, path: TreePath) -> Any:
    for step in path:
        tree = tree[step]
    return tree


def blocks(body: list[Any], path: TreePath = ("body",)) -> Iterator[TreePath]:
    """Every block, outermost first."""
    yield path
    for i, statement in enumerate(body):
        for k in block_positions(statement):
            yield from blocks(statement[k], (*path, i, k))


def expressions(e: Any, path: TreePath) -> Iterator[TreePath]:
    """Every expression inside `e`, `e` first."""
    yield path
    if isinstance(e, list):
        parts = {"lds": [2], "ld8": [1]}.get(e[0], [1, 2])
        for k in parts:
            yield from expressions(e[k], (*path, k))


def all_expressions(program: dict[str, Any]) -> Iterator[TreePath]:
    for block_path in blocks(program["body"]):
        for i, statement in enumerate(get(program, block_path)):
            for k in expression_positions(statement):
                yield from expressions(statement[k], (*block_path, i, k))


def size(case: Case) -> tuple[int, int]:
    """Nodes, then the bits of the literals and the input: smaller in either is simpler. A name
    weighs more than a literal, since a literal depends on nothing."""
    nodes = 0
    bits = 0

    def count(x: Any) -> None:
        nonlocal nodes, bits
        if isinstance(x, list):
            nodes += 1
            for part in x:
                count(part)
        elif isinstance(x, int) and not isinstance(x, bool):
            nodes += 1
            bits += x.bit_length()
        elif isinstance(x, str):
            nodes += 2

    count(case["program"]["body"])
    nodes += len(case["plan"]["params"]) + len(case["plan"]["entries"])
    bits += sum(v.bit_length() for v in case["vector"]["data"].values())
    bits += sum(v.bit_length() for v in case["vector"]["fill"])
    return nodes, bits


def names(x: Any) -> set[str]:
    if isinstance(x, str):
        return {x}
    if isinstance(x, list):
        return set().union(*(names(part) for part in x))
    return set()


def without_param(case: Case, name: str) -> Case:
    out = copy.deepcopy(case)
    out["plan"]["params"] = [p for p in out["plan"]["params"] if p["name"] != name]
    out["program"]["params"] = [p for p in out["program"]["params"] if p != name]
    out["vector"]["data"].pop(name, None)
    if not any(p["kind"] == "table" for p in out["plan"]["params"]):
        out["plan"]["entries"] = []
    return out


def replaced(case: Case, path: TreePath, value: Any) -> Case:
    out = copy.deepcopy(case)
    parent = get(out["program"], path[:-1])
    parent[path[-1]] = value
    return out


def spliced(case: Case, block_path: TreePath, start: int, end: int, items: list[Any]) -> Case:
    out = copy.deepcopy(case)
    block = get(out["program"], block_path)
    block[start:end] = copy.deepcopy(items)
    return out


def candidates(case: Case) -> Iterator[Case]:
    """Smaller cases, most promising first."""
    program = case["program"]
    used = names(program["body"])
    for param in case["plan"]["params"]:
        if param["name"] not in used:
            yield without_param(case, param["name"])
    for block_path in blocks(program["body"]):
        block = get(program, block_path)
        chunk = len(block)
        while chunk >= 1:
            for start in range(0, len(block), chunk):
                yield spliced(case, block_path, start, start + chunk, [])
            chunk //= 2
    for block_path in blocks(program["body"]):
        for i, statement in enumerate(get(program, block_path)):
            for k in block_positions(statement):
                yield spliced(case, block_path, i, i + 1, statement[k])
    for path in all_expressions(program):
        e = get(program, path)
        if isinstance(e, list):
            for k in {"lds": [], "ld8": []}.get(e[0], [1, 2]):
                yield replaced(case, path, e[k])
        for literal in (0, 1):
            if e != literal:
                yield replaced(case, path, literal)
    for name, value in sorted(case["vector"]["data"].items()):
        for literal in (0, 1):
            if value != literal:
                out = copy.deepcopy(case)
                out["vector"]["data"][name] = literal
                yield out
    seed, mask = case["vector"]["fill"]
    for fill in ([0, mask], [seed, 0]):
        if fill != [seed, mask]:
            out = copy.deepcopy(case)
            out["vector"]["fill"] = fill
            yield out


def key(case: Case) -> str:
    return json.dumps([case["program"]["params"], case["program"]["body"], case["plan"], case["vector"]],
                      sort_keys=True)


def well_typed(case: Case) -> bool:
    try:
        interp.check_types(case["program"], case["plan"])
    except interp.TypeViolation:
        return False
    return True


def reduce(case: Case, fails: Callable[[list[Case]], list[bool]], *, batch: int = 64,
           steps: int = 1000) -> tuple[Case, dict[str, int]]:
    """The smallest case this search reaches from `case` for which `fails` still holds, and how
    many candidates it asked about and took."""
    seen: dict[str, bool] = {}
    asked = taken = 0
    while taken < steps:
        current = size(case)
        found = None
        pending: list[Case] = []

        def judge(group: list[Case]) -> Case | None:
            nonlocal asked
            fresh = [c for c in group if key(c) not in seen]
            if fresh:
                asked += len(fresh)
                for c, verdict in zip(fresh, fails(fresh), strict=True):
                    seen[key(c)] = verdict
            return next((c for c in group if seen[key(c)]), None)

        for candidate in candidates(case):
            if size(candidate) >= current or not well_typed(candidate):
                continue
            pending.append(candidate)
            if len(pending) == batch:
                found = judge(pending)
                pending = []
                if found is not None:
                    break
        if found is None and pending:
            found = judge(pending)
        if found is None:
            break
        case = found
        taken += 1
    return case, {"asked": asked, "taken": taken}
