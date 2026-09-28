# SPDX-License-Identifier: AGPL-3.0-or-later
"""An independent interpreter of generated programs, written from the source language.

It reads the program as `dn-compiler emit-fuzz` prints it (`DN.Compiler.SyntaxJson.funJson`): the
source, before any lowering, with the operators as printed and statements in blocks. It shares
no code with the Lean model, which runs the lowered program, and computes `<=` and every other
operator from what the source means rather than from what the lowering turns it into, so a
defect in either shows as a disagreement.

`check_types` holds a program to the discipline the generator keeps: a pointer is only ever
used as an address, so the model's addresses and the host's never meet in a value.
"""
from __future__ import annotations

from collections import Counter
import json
from pathlib import Path
import sys
from typing import Any

sys.path.insert(0, str(Path(__file__).resolve().parent))
from words import MASK, word_op  # the path above is what makes it importable

PAGE = 4096
BUFFERS = 3
WORDS = PAGE // 8
TABLE_BASE = 0x400000
GOLDEN = 0x9E3779B97F4A7C15
# A bound on loop iterations, the model's clock (`DN.Compiler.Gen.modelClock`).
CLOCK = 10000


def buffer_base(b: int) -> int:
    return 0x100000 * (b + 1)


def mix(z: int) -> int:
    z = ((z ^ (z >> 30)) * 0xBF58476D1CE4E5B9) & MASK
    z = ((z ^ (z >> 27)) * 0x94D049BB133111EB) & MASK
    return z ^ (z >> 31)


def splitmix(seed: int, i: int) -> int:
    """Output `i` (from zero) of SplitMix64 started at `seed`."""
    return mix((seed + GOLDEN * (i + 1)) & MASK)


def fill_word(seed: int, mask: int, b: int, i: int) -> int:
    return splitmix(seed, b * WORDS + i) & mask


class Fault(Exception):
    """The run has no value in the semantics: memory outside the plan, a shift of a whole word,
    an unbound name, or the clock run out."""


class Return(Exception):
    def __init__(self, value: int) -> None:
        super().__init__(value)
        self.value = value


class Machine:
    """One call of a program: its memory, filled as the host fills it, and what it reached."""

    def __init__(self, plan: dict[str, Any], vector: dict[str, Any]) -> None:
        seed, mask = vector["fill"]
        self.regions: dict[int, bytearray] = {}
        for b in range(BUFFERS):
            words = (fill_word(seed, mask, b, i).to_bytes(8, "little") for i in range(WORDS))
            self.regions[buffer_base(b)] = bytearray(b"".join(words))
        table = bytearray(PAGE)
        for k, (b, offset) in enumerate(plan["entries"]):
            table[8 * k:8 * k + 8] = (buffer_base(b) + offset).to_bytes(8, "little")
        self.regions[TABLE_BASE] = table
        self.initial = {base: bytes(region) for base, region in self.regions.items()}
        self.clock = CLOCK
        self.reached: Counter[str] = Counter()
        # The loads whose address is being computed, outermost first.
        self.loading: list[str] = []
        # The kinds of block the running statement is in.
        self.blocks: list[str] = []
        # For each pointer local and parameter, the pointer it was computed from, and whether the
        # offset it holds was computed from data.
        self.roots: dict[str, tuple[str, bool]] = {}
        # For each byte accessed, the pointers it was reached through, and the bytes stored to.
        self.through: dict[int, set[str]] = {}
        self.stored: set[int] = set()

    def root(self, e: Any) -> tuple[str, bool] | None:
        """The pointer an address is computed from, and whether data went into its offset: a
        pointer parameter, or an entry of the page of pointers named by the expression that loads
        it, followed through pointer locals."""
        if isinstance(e, str):
            return self.roots.get(e)
        if isinstance(e, list) and e[0] in ("+", "-"):
            found = self.root(e[1]) or self.root(e[2])
            return None if found is None else (found[0], found[1] or "&" in json.dumps(e))
        if isinstance(e, list) and e[0] == "lds" and self.root(e[2]) is not None:
            return (json.dumps(e), False)
        return None

    def locate(self, address: int, width: int, address_expr: Any, store: bool) -> tuple[bytearray, int]:
        base, offset = address & ~(PAGE - 1), address & (PAGE - 1)
        region = self.regions.get(base)
        if region is None or offset + width > PAGE or (width == 8 and offset % 8):
            raise Fault(f"an access of {width} at {address:#x} outside the plan")
        if base != TABLE_BASE:
            size = "word" if width == 8 else "byte"
            edge = "first" if offset == 0 else "last" if offset == PAGE - width else None
            if edge:
                self.reached[f"{edge} {size} of buffer {(base >> 20) - 1}"] += 1
            root = self.root(address_expr)
            if root is not None:
                if root[1]:
                    self.reached["computed address"] += 1
                for byte in range(address, address + width):
                    self.through.setdefault(byte, set()).add(root[0])
                    if store:
                        self.stored.add(byte)
        return region, offset

    def load(self, kind: str, address_expr: Any, env: list[dict[str, int]]) -> int:
        self.loading.append(kind)
        try:
            address = self.value(address_expr, env)
        finally:
            self.loading.pop()
        width = 8 if kind == "word" else 1
        region, offset = self.locate(address, width, address_expr, store=False)
        if address & ~(PAGE - 1) == TABLE_BASE:
            self.reached["pointer from the table"] += 1
        else:
            self.reached[f"load {kind}"] += 1
            if self.loading:
                self.reached[f"{kind} in {self.loading[-1]} address"] += 1
        return int.from_bytes(region[offset:offset + width], "little")

    def value(self, e: Any, env: list[dict[str, int]]) -> int:
        if isinstance(e, bool):
            raise Fault("not an expression")
        if isinstance(e, int):
            return e
        if isinstance(e, str):
            for scope in reversed(env):
                if e in scope:
                    return scope[e]
            raise Fault(f"{e} is not bound")
        head = e[0]
        if head == "lds":
            if e[1] != 1:
                raise Fault("a load of another shape")
            return self.load("word", e[2], env)
        if head == "ld8":
            return self.load("byte", e[1], env)
        x, y = self.value(e[1], env), self.value(e[2], env)
        self.reached[f"operator {head}"] += 1
        try:
            value = word_op(head, x, y)
        except ValueError as unknown:
            raise Fault(str(unknown)) from None
        if value is None:
            raise Fault("a shift of a whole word")
        return value

    def block(self, statements: list[Any], env: list[dict[str, int]], kind: str) -> None:
        env.append({})
        self.blocks.append(kind)
        try:
            for statement in statements:
                self.statement(statement, env)
        finally:
            env.pop()
            self.blocks.pop()

    def store(self, width: int, address_expr: Any, value_expr: Any, env: list[dict[str, int]]) -> None:
        address = self.value(address_expr, env)
        value = self.value(value_expr, env)
        region, offset = self.locate(address, width, address_expr, store=True)
        region[offset:offset + width] = (value & ((1 << (8 * width)) - 1)).to_bytes(width, "little")
        self.reached[f"store {'word' if width == 8 else 'byte'}"] += 1

    def statement(self, s: Any, env: list[dict[str, int]]) -> None:
        head = s[0]
        if head == "var":
            env[-1][s[1]] = self.value(s[2], env)
            if len(self.blocks) > 1:
                self.reached["declaration in an inner block"] += 1
            root = self.root(s[2])
            if root is None:
                self.roots.pop(s[1], None)
            else:
                self.roots[s[1]] = root
                self.reached["pointer local"] += 1
        elif head == "set":
            value = self.value(s[2], env)
            for scope in reversed(env):
                if s[1] in scope:
                    scope[s[1]] = value
                    break
            else:
                raise Fault(f"{s[1]} is not bound")
        elif head == "st":
            self.store(8, s[1], s[2], env)
        elif head == "st8":
            self.store(1, s[1], s[2], env)
        elif head == "if":
            taken = self.value(s[1], env) != 0
            self.reached["branch taken" if taken else "branch not taken"] += 1
            self.block(s[2] if taken else s[3], env, "if")
        elif head == "while":
            while self.value(s[1], env) != 0:
                if self.clock == 0:
                    raise Fault("the clock ran out")
                self.clock -= 1
                self.reached["loop iteration"] += 1
                self.block(s[2], env, "while")
        elif head == "return":
            value = self.value(s[1], env)
            if "while" in self.blocks:
                self.reached["return in a loop"] += 1
            elif "if" in self.blocks:
                self.reached["return in a branch"] += 1
            raise Return(value)
        else:
            raise Fault(f"a statement this interpreter does not run: {head}")

    def aliased(self) -> bool:
        """Whether some byte was reached through two pointers, and stored to."""
        return any(len(self.through[byte]) > 1 for byte in self.stored)

    def changed(self) -> list[list[int]]:
        """Every word of the buffers that differs from its fill, as buffer, offset and value."""
        out = []
        for b in range(BUFFERS):
            now, before = self.regions[buffer_base(b)], self.initial[buffer_base(b)]
            for i in range(WORDS):
                if now[8 * i:8 * i + 8] != before[8 * i:8 * i + 8]:
                    out.append([b, 8 * i, int.from_bytes(now[8 * i:8 * i + 8], "little")])
        return out


def run(program: dict[str, Any], plan: dict[str, Any],
        vector: dict[str, Any]) -> tuple[int, list[list[int]], Counter[str]]:
    """The value `program` returns on `vector`, the words it changes, and what it reached."""
    machine = Machine(plan, vector)
    scope: dict[str, int] = {}
    for param in plan["params"]:
        if param["kind"] == "data":
            scope[param["name"]] = vector["data"][param["name"]]
        elif param["kind"] == "pointer":
            scope[param["name"]] = buffer_base(param["buffer"]) + param["offset"]
            machine.roots[param["name"]] = (param["name"], False)
        else:
            scope[param["name"]] = TABLE_BASE
            machine.roots[param["name"]] = (param["name"], False)
    if [p["name"] for p in plan["params"]] != program["params"]:
        raise Fault("the plan and the program name different parameters")
    try:
        machine.block(program["body"], [scope], "function")
    except Return as done:
        if machine.regions[TABLE_BASE] != machine.initial[TABLE_BASE]:
            raise Fault("the program wrote into the page of pointers") from None
        if machine.aliased():
            machine.reached["one byte through two pointers, stored to"] += 1
        return done.value, machine.changed(), machine.reached
    raise Fault("the program ran to its end without returning")


class TypeViolation(Exception):
    """A pointer used as a value, or a value used as a pointer."""


def expression_type(e: Any, types: dict[str, str]) -> str:
    """`data`, `pointer` (into a buffer) or `table` (into the page of pointers)."""
    if isinstance(e, bool):
        raise TypeViolation("a boolean")
    if isinstance(e, int):
        return "data"
    if isinstance(e, str):
        if e not in types:
            raise TypeViolation(f"{e} is not bound")
        return types[e]
    head = e[0]
    if head in ("lds", "ld8"):
        address = expression_type(e[-1], types)
        if head == "lds" and address == "table":
            return "pointer"
        if address != "pointer":
            raise TypeViolation(f"{head} of a {address}")
        return "data"
    left, right = expression_type(e[1], types), expression_type(e[2], types)
    if head in ("+", "-") and left in ("pointer", "table") and right == "data":
        return left
    if left != "data" or right != "data":
        raise TypeViolation(f"{head} of a {left} and a {right}")
    return "data"


def check_types(program: dict[str, Any], plan: dict[str, Any]) -> Counter[str]:
    """Raise if a pointer can leak into a value; otherwise count the forms the program uses."""
    kinds = {"data": "data", "pointer": "pointer", "table": "table"}
    types = {p["name"]: kinds[p["kind"]] for p in plan["params"]}
    used: Counter[str] = Counter()

    def address(e: Any, scope: dict[str, str]) -> None:
        if expression_type(e, scope) != "pointer":
            raise TypeViolation("an access through something other than a pointer")

    def walk_expression(e: Any, scope: dict[str, str]) -> None:
        if not isinstance(e, list):
            return
        if e[0] in ("lds", "ld8") and expression_type(e[-1], scope) != "table":
            address(e[-1], scope)
        for part in e[1:]:
            walk_expression(part, scope)

    def block(statements: list[Any], outer: dict[str, str], siblings: set[str]) -> set[str]:
        scope = dict(outer)
        declared: set[str] = set()
        for s in statements:
            head = s[0]
            for part in s[1:]:
                if isinstance(part, list) and part and not isinstance(part[0], list):
                    walk_expression(part, scope)
            if head == "var":
                t = expression_type(s[2], scope)
                if t == "table":
                    raise TypeViolation("a local holding the page of pointers")
                if s[1] in siblings:
                    used["a name declared again in a sibling block"] += 1
                scope[s[1]] = t
                declared.add(s[1])
            elif head == "set":
                if scope.get(s[1]) != "data" or expression_type(s[2], scope) != "data":
                    raise TypeViolation(f"an assignment to {s[1]} of other than data")
            elif head in ("st", "st8"):
                address(s[1], scope)
                if expression_type(s[2], scope) != "data":
                    raise TypeViolation("a store of a pointer")
            elif head in ("if", "while", "return"):
                if expression_type(s[1], scope) != "data":
                    raise TypeViolation(f"a {head} on a pointer")
                if head == "if":
                    seen = block(s[2], scope, set())
                    block(s[3], scope, seen)
                elif head == "while":
                    block(s[2], scope, set())
            else:
                raise TypeViolation(f"a statement outside the subset: {head}")
        return declared

    block(program["body"], types, set())
    used[f"{len(plan['params'])} parameters"] += 1
    return used
