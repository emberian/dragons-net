#!/usr/bin/env python3
# SPDX-License-Identifier: AGPL-3.0-or-later
"""Keep prose short: in each Markdown file given, a paragraph or list item holds at most 60 words, a
sentence at most 45 and a table cell at most 40; a code span counts as a word, and code blocks and
headings are not prose."""
from __future__ import annotations

from pathlib import Path
import re
import sys

LIMITS = {"paragraph": 60, "sentence": 45, "cell": 40}
ITEM = re.compile(r"\s*(?:[-*+]|\d+\.)\s")


def words(text: str) -> int:
    return sum(1 for w in re.sub(r"`[^`]*`", " code ", text).split() if re.search(r"\w", w))


def sentences(text: str) -> list[str]:
    """`text` cut after a full stop, a question or an exclamation mark that a capital letter, a digit or code
    follows."""
    found = [""]
    for piece in re.split(r"(?<=[.!?])\s+", text):
        first = piece.lstrip("*_\"'([")[:1]
        if found[-1] and (first.isupper() or first.isdigit() or first == "`"):
            found.append(piece)
        else:
            found[-1] = f"{found[-1]} {piece}".strip()
    return found


def blocks(text: str) -> list[tuple[int, str, str]]:
    """The prose blocks of `text`: its line, its kind (paragraph or cell) and its text."""
    found: list[tuple[int, str, str]] = []
    start, fenced = 0, False
    lines: list[str] = []

    def close() -> None:
        if lines:
            found.append((start, "paragraph", " ".join(lines)))
            lines.clear()

    for number, line in enumerate(text.splitlines(), 1):
        stripped = line.strip()
        if stripped.startswith(("```", "~~~")):
            close()
            fenced = not fenced
        elif fenced:
            continue
        elif not stripped or stripped.startswith("#"):
            close()
        elif stripped.startswith("|"):
            close()
            cells = [c.strip() for c in stripped.strip("|").split("|")]
            if not all(re.fullmatch(r":?-+:?", c) for c in cells):
                found += [(number, "cell", c) for c in cells]
        else:
            if ITEM.match(line):
                close()
            if not lines:
                start = number
            lines.append(stripped)
    close()
    return found


def problems(text: str) -> list[str]:
    """Each block or sentence of `text` past its limit, with its line and its start."""
    wrong = []
    for line, kind, block in blocks(text):
        if words(block) > LIMITS[kind]:
            wrong.append(f"line {line}: a {kind} of {words(block)} words, over {LIMITS[kind]}: {block[:60]}")
        for sentence in sentences(block) if kind == "paragraph" else []:
            if words(sentence) > LIMITS["sentence"]:
                wrong.append(f"line {line}: a sentence of {words(sentence)} words, over {LIMITS['sentence']}: "
                             f"{sentence[:60]}")
    return wrong


def main() -> int:
    failed = False
    for name in sys.argv[1:]:
        for problem in problems(Path(name).read_text()):
            print(f"{name}: {problem}", file=sys.stderr)
            failed = True
    return 1 if failed else 0


if __name__ == "__main__":
    sys.exit(main())
