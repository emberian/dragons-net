# SPDX-License-Identifier: AGPL-3.0-or-later
"""Reduce a generated program that exposes a failure to a small one that still exposes it.

A case is a program in the form `dn-compiler emit-fuzz` prints, the functions it calls, its memory
plan and one input. The reducer tries smaller cases in a fixed order, the way hierarchical delta
debugging does: dropping unused parameters and functions nothing calls, deleting runs of
statements (halves first, then smaller runs), replacing an `if` or a loop by the statements inside
it and a call by a literal or one of its arguments, replacing an expression by one of its own
operands (hoisting) or by a literal, and simplifying the input. A candidate is taken only
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


def expression_positions(statement: list[Any]) -> list[TreePath]:
    """Where a statement holds expressions."""
    head = statement[0]
    if head in ("var", "set"):
        return [(2,)]
    if head in ("st", "st8"):
        return [(1,), (2,)]
    if head in ("if", "while", "return"):
        return [(1,)]
    if head == "call":
        return [(3, k) for k in range(len(statement[3]))]
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


def functions(case: Case) -> list[dict[str, Any]]:
    return list(case.get("functions", []))


def all_blocks(case: Case) -> Iterator[TreePath]:
    """Every block of the program, then of each function it calls."""
    yield from blocks(case["program"]["body"], ("program", "body"))
    for n, f in enumerate(functions(case)):
        yield from blocks(f["body"], ("functions", n, "body"))


def all_expressions(case: Case) -> Iterator[TreePath]:
    for block_path in all_blocks(case):
        for i, statement in enumerate(get(case, block_path)):
            for k in expression_positions(statement):
                yield from expressions(get(statement, k), (*block_path, i, *k))


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
    for f in functions(case):
        count(f["body"])
    nodes += len(case["plan"]["params"]) + len(case["plan"]["entries"])
    nodes += sum(1 + len(f["params"]) for f in case["plan"].get("functions", []))
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


def calls(case: Case) -> Iterator[tuple[TreePath, list[Any]]]:
    """Every call statement, with where it is."""
    for block_path in all_blocks(case):
        for i, statement in enumerate(get(case, block_path)):
            if statement[0] == "call":
                yield (*block_path, i), statement


def without_function(case: Case, n: int) -> Case:
    out = copy.deepcopy(case)
    del out["functions"][n]
    del out["plan"]["functions"][n]
    return out


def without_function_param(case: Case, n: int, k: int) -> Case:
    """Function `n` without its parameter `k`, and every call of it without that argument."""
    out = copy.deepcopy(case)
    name = out["functions"][n]["name"]
    del out["functions"][n]["params"][k]
    del out["plan"]["functions"][n]["params"][k]
    for _, statement in calls(out):
        if statement[2] == name:
            del statement[3][k]
    return out


def replaced(case: Case, path: TreePath, value: Any) -> Case:
    out = copy.deepcopy(case)
    parent = get(out, path[:-1])
    parent[path[-1]] = value
    return out


def spliced(case: Case, block_path: TreePath, start: int, end: int, items: list[Any]) -> Case:
    out = copy.deepcopy(case)
    block = get(out, block_path)
    block[start:end] = copy.deepcopy(items)
    return out


def candidates(case: Case) -> Iterator[Case]:
    """Smaller cases, most promising first."""
    program = case["program"]
    used = names(program["body"])
    for param in case["plan"]["params"]:
        if param["name"] not in used:
            yield without_param(case, param["name"])
    called = {statement[2] for _, statement in calls(case)}
    for n, f in enumerate(functions(case)):
        if f["name"] not in called:
            yield without_function(case, n)
    for n, f in enumerate(functions(case)):
        for k, param in enumerate(f["params"]):
            if param not in names(f["body"]):
                yield without_function_param(case, n, k)
    for block_path in all_blocks(case):
        block = get(case, block_path)
        chunk = len(block)
        while chunk >= 1:
            for start in range(0, len(block), chunk):
                yield spliced(case, block_path, start, start + chunk, [])
            chunk //= 2
    for block_path in all_blocks(case):
        for i, statement in enumerate(get(case, block_path)):
            for k in block_positions(statement):
                yield spliced(case, block_path, i, i + 1, statement[k])
    for path, statement in calls(case):
        for value in (0, *statement[3]):
            yield replaced(case, path, ["var", statement[1], value])
    for path in all_expressions(case):
        e = get(case, path)
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
    return json.dumps([case["program"]["params"], case["program"]["body"], functions(case), case["plan"],
                       case["vector"]], sort_keys=True)


def well_typed(case: Case) -> bool:
    try:
        interp.check_types(case["program"], case["plan"], functions(case))
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
