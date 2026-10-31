# SPDX-License-Identifier: AGPL-3.0-or-later
"""The printed form of the state corpus, `dn-compiler dump-states`: a case is `KEY value` lines up to
`END`, programs are S-expressions. Read by the state lane and by the HOL lane."""
from __future__ import annotations

from typing import Any

# The fields of a case's answer.
FIELDS = ("RESULT", "FLOCALS", "FMEM", "FCALLS", "FTRACE", "FCLOCK", "FBASE")


def parse_sexp(text: str, at: int = 0) -> tuple[Any, int]:
    """The printed S-expression back into a nested list."""
    while text[at] == " ":
        at += 1
    if text[at] != "(":
        start = at
        while at < len(text) and text[at] not in " ()":
            at += 1
        return (text[start:at], at)
    at += 1
    items: list[Any] = []
    while True:
        while text[at] == " ":
            at += 1
        if text[at] == ")":
            return (items, at + 1)
        item, at = parse_sexp(text, at)
        items.append(item)


def pairs(text: str) -> list[tuple[str, str]]:
    return [] if not text else [(p.split("=", 1)[0], p.split("=", 1)[1]) for p in text.split(",")]


def parse_cases(dump: str) -> list[dict[str, str]]:
    cases: list[dict[str, str]] = []
    current: dict[str, str] = {}
    for line in dump.splitlines():
        if line == "END":
            cases.append(current)
            current = {}
            continue
        key, _, value = line.partition(" ")
        current[key] = value
    return cases
