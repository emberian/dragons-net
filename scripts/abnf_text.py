# SPDX-License-Identifier: AGPL-3.0-or-later
"""ABNF (RFC 5234, with its verified errata 2968 and 3076) read from the text of an RFC.

`extract` finds a rule's definition in an RFC as the RFC editor lays it out: the rule name
indented, its continuation lines indented further, comments after `;`, and page breaks — the
footer, the form feed and the running header — anywhere inside it. `parse` reads the definition
into terms; `show` prints terms back as ABNF. Rule names are compared without regard to case, as
RFC 5234 §2.1 says.
"""
from __future__ import annotations

from dataclasses import dataclass
import re

PAGE_FOOTER = re.compile(r"^\S.*\[Page \d+\]\s*$")
RUNNING_HEADER = re.compile(r"^RFC \d+ .*\d{4}\s*$")


def body_lines(text: str) -> list[str]:
    """The lines of an RFC without its page furniture: a footer, a form feed and the running
    header become nothing, so a rule a page break cuts in two reads as one."""
    lines = []
    for raw in text.split("\n"):
        line = raw.replace("\f", "").rstrip()
        if PAGE_FOOTER.match(line) or RUNNING_HEADER.match(line):
            continue
        lines.append(line)
    return lines


def indent(line: str) -> int:
    return len(line) - len(line.lstrip(" "))


def looks_like_abnf(line: str) -> bool:
    """A line that goes on with a definition rather than prose: one starting as ABNF does."""
    first = line.lstrip()[:1]
    return first in {"/", "(", "[", "*", "%", '"', ";", "<"} or first.isdigit()


class RuleMissing(Exception):
    pass


def extract(text: str, name: str, *, occurrence: int = 1) -> str:
    """The definition of `name` (`=` or `=/`) as the RFC prints it, from its name to its last
    continuation line, page furniture removed, trailing blank lines dropped. `occurrence` picks
    the n-th definition when an RFC repeats one, as RFC 3986 does in its collected ABNF."""
    lines = body_lines(text)
    start = re.compile(r"^( +)" + re.escape(name) + r"\s*=/?(\s|$)", re.IGNORECASE)
    found = [k for k, line in enumerate(lines) if start.match(line)]
    if len(found) < occurrence:
        raise RuleMissing(f"{name} is defined {len(found)} times, not {occurrence}")
    k = found[occurrence - 1]
    base = indent(lines[k])
    taken = [lines[k]]
    j = k + 1
    while j < len(lines):
        line = lines[j]
        if not line.strip():
            nxt = next((m for m in range(j, len(lines)) if lines[m].strip()), None)
            if nxt is None or indent(lines[nxt]) <= base or not looks_like_abnf(lines[nxt]):
                break
            j = nxt
            continue
        if indent(line) <= base:
            break
        taken.append(line)
        j += 1
    return "\n".join(taken)


# Terms. A rule's definition is an alternation of concatenations of repetitions of elements.

@dataclass(frozen=True)
class Range:
    lo: int
    hi: int


@dataclass(frozen=True)
class Text:
    """A quoted string: ASCII letters match in either case (RFC 5234 §2.3)."""
    value: bytes


@dataclass(frozen=True)
class Exact:
    """A sequence of numeric values, `%d112.111`: every byte as written."""
    value: bytes


@dataclass(frozen=True)
class Ref:
    name: str


@dataclass(frozen=True)
class Seq:
    items: tuple[Term, ...]


@dataclass(frozen=True)
class Alt:
    items: tuple[Term, ...]


@dataclass(frozen=True)
class Rep:
    lo: int
    hi: int | None
    item: Term


@dataclass(frozen=True)
class Prose:
    text: str


Term = Range | Text | Exact | Ref | Seq | Alt | Rep | Prose


class Syntax(Exception):
    pass


def strip_comments(definition: str) -> str:
    """The definition with each `;` comment removed, outside quoted strings and prose."""
    out = []
    for line in definition.split("\n"):
        kept, quote, prose = [], False, False
        for ch in line:
            if ch == '"' and not prose:
                quote = not quote
            elif ch == "<" and not quote:
                prose = True
            elif ch == ">" and prose:
                prose = False
            elif ch == ";" and not quote and not prose:
                break
            kept.append(ch)
        out.append("".join(kept))
    return " ".join(out)


class Parser:
    def __init__(self, text: str) -> None:
        self.s = text
        self.i = 0

    def ws(self) -> None:
        while self.i < len(self.s) and self.s[self.i] in " \t":
            self.i += 1

    def peek(self) -> str:
        return self.s[self.i] if self.i < len(self.s) else ""

    def expect(self, ch: str) -> None:
        self.ws()
        if self.peek() != ch:
            raise Syntax(f"expected {ch!r} at {self.i} in {self.s!r}")
        self.i += 1

    def rulename(self) -> str:
        m = re.compile(r"[A-Za-z][A-Za-z0-9-]*").match(self.s, self.i)
        if not m:
            raise Syntax(f"expected a rule name at {self.i} in {self.s!r}")
        self.i = m.end()
        return m.group().lower()

    def alternation(self) -> Term:
        items = [self.concatenation()]
        while True:
            self.ws()
            if self.peek() != "/":
                break
            self.i += 1
            items.append(self.concatenation())
        return items[0] if len(items) == 1 else Alt(tuple(items))

    def concatenation(self) -> Term:
        items = [self.repetition()]
        while True:
            self.ws()
            if self.peek() in {"", "/", ")", "]"}:
                break
            items.append(self.repetition())
        return items[0] if len(items) == 1 else Seq(tuple(items))

    def repetition(self) -> Term:
        self.ws()
        m = re.compile(r"(\d*)\*(\d*)|(\d+)").match(self.s, self.i)
        if m:
            self.i = m.end()
            if m.group(3) is not None:
                n = int(m.group(3))
                return Rep(n, n, self.element())
            lo = int(m.group(1)) if m.group(1) else 0
            hi = int(m.group(2)) if m.group(2) else None
            return Rep(lo, hi, self.element())
        return self.element()

    def element(self) -> Term:
        self.ws()
        ch = self.peek()
        if ch == "(":
            self.i += 1
            inner = self.alternation()
            self.expect(")")
            return inner
        if ch == "[":
            self.i += 1
            inner = self.alternation()
            self.expect("]")
            return Rep(0, 1, inner)
        if ch == '"':
            end = self.s.index('"', self.i + 1)
            value = self.s[self.i + 1:end]
            self.i = end + 1
            return Text(value.encode("ascii"))
        if ch == "%":
            return self.num_val()
        if ch == "<":
            end = self.s.index(">", self.i)
            text = self.s[self.i + 1:end]
            self.i = end + 1
            return Prose(text)
        return Ref(self.rulename())

    def num_val(self) -> Term:
        m = re.compile(r"%([bdx])([0-9A-Fa-f]+)((?:\.[0-9A-Fa-f]+)+|-[0-9A-Fa-f]+)?").match(self.s, self.i)
        if not m:
            raise Syntax(f"bad numeric value at {self.i} in {self.s!r}")
        self.i = m.end()
        base = {"b": 2, "d": 10, "x": 16}[m.group(1).lower()]
        first = int(m.group(2), base)
        rest = m.group(3)
        if rest is None:
            return Range(first, first)
        if rest.startswith("-"):
            return Range(first, int(rest[1:], base))
        return Exact(bytes([first, *(int(v, base) for v in rest[1:].split("."))]))


def parse(definition: str) -> tuple[str, bool, Term]:
    """A definition's rule name, whether it adds alternatives (`=/`), and its terms."""
    p = Parser(strip_comments(definition))
    p.ws()
    name = p.rulename()
    p.ws()
    incremental = p.s.startswith("=/", p.i)
    p.i += 2 if incremental else 1
    if p.s[p.i - 1] != "=" and not incremental:
        raise Syntax(f"expected = after {name}")
    term = p.alternation()
    p.ws()
    if p.i != len(p.s):
        raise Syntax(f"unparsed text {p.s[p.i:]!r} in {name}")
    return name, incremental, term


def show(t: Term) -> str:
    """The term as ABNF, fully bracketed where precedence could be in doubt."""
    match t:
        case Range(lo, hi):
            return f"%x{lo:02X}" if lo == hi else f"%x{lo:02X}-{hi:02X}"
        case Text(v):
            return '"' + v.decode("ascii") + '"'
        case Exact(v):
            return "%x" + ".".join(f"{b:02X}" for b in v)
        case Ref(name):
            return name
        case Seq(items):
            return " ".join(show_in(i) for i in items)
        case Alt(items):
            return " / ".join(show_in(i) if isinstance(i, Alt) else show(i) for i in items)
        case Rep(lo, hi, item):
            if (lo, hi) == (0, 1):
                return "[" + show(item) + "]"
            count = f"{lo}" if lo == hi else f"{lo or ''}*{'' if hi is None else hi}"
            # A repetition of a repetition keeps its brackets: `*(4x)` is not `*4x`.
            return count + (f"({show(item)})" if isinstance(item, Rep) else show_in(item))
        case Prose(text):
            return f"<{text}>"
    raise TypeError(t)


def show_in(t: Term) -> str:
    """A term as an operand: in brackets unless it is one element."""
    return f"({show(t)})" if isinstance(t, (Seq, Alt)) else show(t)
