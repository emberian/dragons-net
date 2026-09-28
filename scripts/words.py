# SPDX-License-Identifier: AGPL-3.0-or-later
"""Machine words as Pancake computes them, for the reference implementations the lanes hold the
Lean model against: the differential lane's, the independent interpreter's and the state check's.
They share this with each other, and nothing with the model."""
from __future__ import annotations

MASK = (1 << 64) - 1


def signed(w: int) -> int:
    """A machine word as the signed integer `word_lt` compares."""
    return w - (1 << 64) if w >= 1 << 63 else w


def word_op(op: str, x: int, y: int) -> int | None:
    """Operator `op` of the source language on two words: `+ - * &` wrap, `< <=` are signed, and
    `>>>` is a logical shift, which has no value for a distance of a whole word or more."""
    if op == ">>>":
        return None if y >= 64 else x >> y
    results = {"+": (x + y) & MASK, "-": (x - y) & MASK, "*": (x * y) & MASK, "&": x & y,
               "<": int(signed(x) < signed(y)), "<=": int(signed(x) <= signed(y)), "==": int(x == y)}
    if op not in results:
        raise ValueError(f"unknown operator {op}")
    return results[op]
