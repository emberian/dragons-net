#!/usr/bin/env python3
# SPDX-License-Identifier: AGPL-3.0-or-later AND BSD-3-Clause
"""The grammar of header fields, held two ways. `DN.News.AbnfRules`, run by the Lean interpreter
of `DN.News.Abnf` (`dn-compiler abnf-model`), and the same grammar text read by the `abnf`
library (scripts/abnf_ref.py) have to give the same answer on every case: the cases abnfgen, a
third reading of ABNF, derives from the grammar text while trying to cover every branch; the
derivations of this file, which make every choice of every alternation; each of those with a
byte dropped, replaced or inserted at a few places; comments nested deep; and the examples the
RFCs print. The grammar has to be the one scripts/gen_abnf.py takes from the RFCs, no case may
run the interpreter out of fuel, and the rule of every field has to be seen both to accept and to
refuse.

The grammar has to agree with the RFCs, not only with itself: every derivation is accepted, and
so is every example the RFCs print, but those of forms RFC 5536 does not allow; and what a rule
taken from RFC 5322 or RFC 3986 unchanged, or only narrowed, accepts, the library's own
transcription of that RFC accepts too. Defects planted in the reference's grammar text, and the
mutants of the interpreter (`DN.News.AbnfMutant`), have to show as answers that differ
(docs/baseline.md, "Header field grammar").
"""
from __future__ import annotations

from concurrent.futures import ThreadPoolExecutor
import os
from pathlib import Path
import random
import re
import subprocess
import sys
import time

sys.path.insert(0, str(Path(__file__).resolve().parent))
import abnf_text as A  # the path above is what makes these importable
import gen_abnf as G
import lanes
from lanes import LaneError, Report

OUT = lanes.ROOT / "build/abnf"
GRAMMAR = lanes.ROOT / "scripts/netnews.abnf"
REFERENCE = lanes.ROOT / "scripts/abnf_ref.py"
REQUIREMENTS = lanes.ROOT / "scripts/requirements-tests.txt"
SEED = 20260929
CASES = 40
CHUNK = 2000
# The model and the reference each run in this many processes at once.
WORKERS = max(1, min(4, len(os.sched_getaffinity(0))))
# Rules inside the fields whose own branches are worth covering apart from a field's.
INNER = ["date-time", "zone", "mailbox-list", "address-list", "msg-id", "path-identity",
         "newsgroup-list", "comment", "quoted-string", "domain-literal", "dot-atom", "phrase",
         "unstructured", "ipv6address", "ipv4address", "parameter", "product"]
# Bytes a changed case is given: the ones that separate, quote, fold or end, and some outside.
BYTES = [0, 9, 10, 13, 32, 34, 40, 41, 44, 46, 58, 59, 60, 62, 64, 91, 92, 93, 127, 128]
# Bytes a changed case writes again, to cross a repetition's upper bound: letters, digits and the
# signs that end a run of them.
REPEATED = frozenset(b"abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789+/=%:.")
# Cases one past a repetition's upper bound that no change of a derivation makes.
PAST_BOUNDS = [("ipv4address", b"256.1.1.1"), ("ipv6address", b"1:2:3:4:5:6:7:8:9")]

# Defects planted in the reference's grammar text, each of which some case has to show. The rule
# texts are scripts/netnews.abnf's, under its notice.
DEFECTS = [
    ("the obsolete phrase dropped", "phrase = 1*word / obs-phrase", "phrase = 1*word"),
    ("no white space before GMT", 'zone = fws ("+" / "-") 4digit / [fws] obs-zone',
     'zone = fws ("+" / "-") 4digit / obs-zone'),
    ("a day of two digits only", "day = [fws] 1*2digit fws", "day = [fws] 2digit fws"),
    ("a backslash in a comment", "ctext = %x21-27 / %x2A-5B / %x5D-7E", "ctext = %x21-27 / %x2A-7E"),
    ("no domain literals", "domain = dot-atom / domain-literal", "domain = dot-atom"),
    ("comments not nested", "ccontent = ctext / quoted-pair / comment",
     "ccontent = ctext / quoted-pair"),
    ("an empty unstructured body", "unstructured = *wsp vchar *([fws] vchar) *wsp",
     "unstructured = *wsp *([fws] vchar) *wsp"),
    ("Message-ID without its space", 'message-id = "Message-ID:" sp *wsp msg-id *wsp crlf',
     'message-id = "Message-ID:" *wsp msg-id *wsp crlf'),
    ("a distribution as RFC 5536 writes it", 'dist-name = (alpha / digit) *(alpha / digit / "+" / "-" / "_")',
     'dist-name = alpha / digit *(alpha / digit / "+" / "-" / "_")'),
    ("no IPv6 address that starts with ::",
     'ipv6address = 6(h16 ":") ls32 / "::" 5(h16 ":") ls32 /', 'ipv6address = 6(h16 ":") ls32 /'),
    ("no white space before a parameter's =",
     'regular-parameter = regular-parameter-name [cfws] "=" [cfws] value [cfws]',
     'regular-parameter = regular-parameter-name "=" [cfws] value [cfws]'),
    ("To without its space", 'to = "To:" sp address-list crlf', 'to = "To:" address-list crlf'),
    ("a day of three digits", "day = [fws] 1*2digit fws", "day = [fws] 1*3digit fws"),
    ("an hour of three digits", "hour = 2digit", "hour = 2*3digit"),
    ("a minute of three digits", "minute = 2digit", "minute = 2*3digit"),
    ("a second of three digits", "second = 2digit", "second = 2*3digit"),
    ("a zone of five digits", 'zone = fws ("+" / "-") 4digit /', 'zone = fws ("+" / "-") 4*5digit /'),
    ("an octet of 256 to 259", 'dec-octet = digit / %x31-39 digit / "1" 2digit / "2" %x30-34 digit / "25" %x30-35',
     'dec-octet = digit / %x31-39 digit / "1" 2digit / "2" %x30-34 digit / "25" %x30-39'),
    ("an IPv6 address of seven groups before its last",
     'ipv6address = 6(h16 ":") ls32 /', 'ipv6address = 6*7(h16 ":") ls32 /'),
    ("an escaped octet of three digits", 'ext-octet = "%" 2(digit', 'ext-octet = "%" 2*3(digit'),
    ("a base64 end of three characters before ==", 'base64-terminal = 2base64-char "=="',
     'base64-terminal = 2*3base64-char "=="'),
]
# The rules DN.News.AbnfMutant breaks, by the name `dn-compiler abnf-model --mutant` takes.
MUTANTS = ["case-sensitive", "first-alternative", "greedy-repetition", "bound-off-by-one",
           "memo-by-position"]
# How deep the deep cases nest: past where the reference's Rust backend stops.
NESTED = 500
# RFC 5536 prints no header field whole; these are the pieces its text gives as examples.
QUOTED = [("parameter", 'posting-host = "posting.example.com:192.0.2.1"'), ("dist-name", "world"),
          ("dist-name", "local")]
# The origins a rule may have, by the note scripts/netnews.abnf gives it, for the library's own
# transcription of an RFC to have to accept whatever the rule does: the RFC's text as it is, or
# with no more than the obsolete syntax taken out and a space asked for.
UNCHANGED = {"rfc5322": {"RFC 5322", f"RFC 5322, with {G.SPACED.replace('§', 'section ')}"},
             "rfc3986": {"RFC 3986"}}


def field_rule(name: str) -> str:
    for field, (rule, _) in G.FIELDS.items():
        if field.lower() == name.lower():
            return rule
    return G.OPTIONAL[0]


def generated(abnfgen: str, rule: str, seed: int) -> list[bytes]:
    """What abnfgen writes for `rule`, trying to cover every branch: CASES documents, each from a
    run of its own, since within one run only the first document follows from the seed."""
    out = []
    for k in range(CASES):
        done = subprocess.run([abnfgen, "-l", "-c", "-r", str(seed * CASES + k), "-y", "30", "-s", rule,
                               str(GRAMMAR)], capture_output=True, timeout=60, check=False)
        if done.returncode:
            raise LaneError(f"abnfgen refused {rule}: {done.stderr.decode(errors='replace')[:300]}")
        out.append(done.stdout)
    return out


def changed(case: bytes, rng: random.Random) -> list[bytes]:
    """`case` changed where the rules of a field line are (RFC 5536 §2.2): without the space after
    the name's colon, without its line end, with a bare LF for it, with a space before it; with a
    byte dropped, replaced or inserted at a few places; and with a letter, a digit or a sign that
    ends a run of them written twice and three times, which can take a run past its upper bound."""
    out = []
    colon = case.find(b":")
    if 0 < colon < len(case) - 1 and case[colon + 1:colon + 2] == b" ":
        out.append(case[:colon + 1] + case[colon + 2:])
    if case.endswith(b"\r\n"):
        out += [case[:-2], case[:-2] + b"\n", case[:-2] + b" \r\n"]
    for p in sorted(rng.sample(range(len(case) + 1), min(4, len(case) + 1))):
        b = bytes([rng.choice(BYTES)])
        if p < len(case):
            out += [case[:p] + case[p + 1:], case[:p] + b + case[p + 1:]]
        out.append(case[:p] + b + case[p:])
    runs = [p for p, b in enumerate(case) if b in REPEATED]
    for p in sorted(rng.sample(runs, min(2, len(runs)))):
        out += [case[:p + 1] + case[p:], case[:p + 1] + case[p:p + 1] + case[p:]]
    return out


# Branch coverage: a derivation of every rule for each choice of each of its alternations.
DEPTH = 12
CORE = {"alpha": [(65, 90), (97, 122)], "digit": [(48, 57)], "hexdig": [(48, 57), (65, 70), (97, 102)],
        "sp": [(32, 32)], "htab": [(9, 9)], "wsp": [(32, 32), (9, 9)], "vchar": [(33, 126)],
        "dquote": [(34, 34)], "cr": [(13, 13)], "lf": [(10, 10)], "ctl": [(0, 31), (127, 127)],
        "char": [(1, 127)], "octet": [(0, 255)], "bit": [(48, 49)]}


def grammar() -> dict[str, A.Term]:
    return {name: term for name, (term, _) in noted().items()}


def noted() -> dict[str, tuple[A.Term, str]]:
    """The rules of the grammar text, each with the note on where it comes from."""
    rules, note = {}, ""
    for line in GRAMMAR.read_text(encoding="ascii").splitlines():
        if line.startswith("; "):
            note = line[2:]
        elif " = " in line:
            name, _, term = A.parse(line)
            rules[name] = (term, note)
    return rules


def shortest(rules: dict[str, A.Term]) -> dict[str, int]:
    """The length of each rule's shortest derivation, so that one past the depth limit ends."""
    inf = 1 << 30
    best = {n: inf for n in rules}

    def length(t: A.Term) -> int:
        match t:
            case A.Range():
                return 1
            case A.Text(v) | A.Exact(v):
                return len(v)
            case A.Ref(name):
                return 2 if name == "crlf" else 1 if name in CORE else best.get(name, inf)
            case A.Seq(items):
                return min(inf, sum(length(i) for i in items))
            case A.Alt(items):
                return min(length(i) for i in items)
            case A.Rep(lo, _, item):
                return min(inf, lo * length(item)) if lo else 0
        return inf

    while True:
        new = {n: length(t) for n, t in rules.items()}
        if new == best:
            return best
        best = new


class Deriver:
    """Derivations from the grammar text: random choices, except one alternation's choice
    forced, and past DEPTH the choices that end soonest."""

    def __init__(self, rules: dict[str, A.Term], rng: random.Random) -> None:
        self.rules, self.rng = rules, rng
        self.best = shortest(rules)

    def cost(self, t: A.Term) -> int:
        match t:
            case A.Ref(name):
                return 2 if name == "crlf" else 1 if name in CORE else self.best[name]
            case A.Seq(items):
                return sum(self.cost(i) for i in items)
            case A.Alt(items):
                return min(self.cost(i) for i in items)
            case A.Rep(lo, _, item):
                return lo * self.cost(item)
            case A.Text(v) | A.Exact(v):
                return len(v)
        return 1

    def derive(self, t: A.Term, depth: int, forced: dict[int, int]) -> bytes:
        """A derivation of `t`: `forced` maps an alternation, by the object that is it, to the
        choice it has to make wherever it is met."""
        match t:
            case A.Range(lo, hi):
                return bytes([self.rng.randint(lo, hi)])
            case A.Text(v):
                return bytes(c ^ 32 if chr(c).isalpha() and self.rng.random() < 0.5 else c for c in v)
            case A.Exact(v):
                return v
            case A.Ref("crlf"):
                return b"\r\n"
            case A.Ref(name) if name in CORE:
                lo, hi = self.rng.choice(CORE[name])
                return bytes([self.rng.randint(lo, hi)])
            case A.Ref(name):
                return self.derive(self.rules[name], depth + 1, {})
            case A.Seq(items):
                return b"".join(self.derive(i, depth, forced) for i in items)
            case A.Alt(items):
                if id(t) in forced:
                    choice = forced[id(t)]
                elif depth > DEPTH:
                    choice = min(range(len(items)), key=lambda k: self.cost(items[k]))
                else:
                    choice = self.rng.randrange(len(items))
                return self.derive(items[choice], depth, forced)
            case A.Rep(lo, hi, item):
                most = lo if depth > DEPTH else lo + 3 if hi is None else min(hi, lo + 3)
                n = self.rng.randint(lo, most)
                return b"".join(self.derive(item, depth, forced) for _ in range(n))
        raise TypeError(t)


def alternations(t: A.Term) -> list[A.Alt]:
    """The alternations written in `t`, each once."""
    match t:
        case A.Alt(items):
            return [t] + [a for i in items for a in alternations(i)]
        case A.Seq(items):
            return [a for i in items for a in alternations(i)]
        case A.Rep(_, _, item):
            return alternations(item)
    return []


def covering(rng: random.Random) -> list[tuple[str, bytes]]:
    """For each rule and each choice of each alternation written in it, two derivations of the
    rule with that choice made."""
    rules = grammar()
    d = Deriver(rules, rng)
    out = []
    for name, term in sorted(rules.items()):
        for alt in alternations(term):
            for choice in range(len(alt.items)):
                for _ in range(2):
                    out.append((name, d.derive(term, 0, {id(alt): choice})))
    return out


FIELD_LINE = re.compile(r"^( +)([A-Za-z][A-Za-z0-9-]*)[ \t]*:")
# The examples of RFC 5322's obsolete forms (its appendix A.6) that RFC 5536 §2.1 does not allow,
# by their line, other than those with white space before the colon (RFC 5322 §4.5) or none after
# it (RFC 5536 §2.2), which `examples` tells by that.
OBSOLETE = {
    "To: Mary Smith <@node.test:mary@example.net>, , jdoe@test  . example":
        "a route, an empty member and white space in a domain (RFC 5322 §4.4)",
    "Date: 21 Nov 97 09:55:06 GMT": "a year of two digits (RFC 5322 §4.3)",
}


# What RFC 5322 appendix A.6.3 prints for a line of blank spaces.
BLANKS = "__"


def printed(number: int) -> list[tuple[str, bytes]]:
    """The header fields an RFC prints in its examples, unfolded as they would travel: a line
    naming a field the checks know, and the lines indented under it. An example starts after a
    blank line or a line of dashes, as the RFCs set them apart, or right after another; a line of
    prose that happens to start with a field's name is not one."""
    lines = A.body_lines(G.rfc(number))
    known = {f.lower() for f in G.FIELDS}
    found = []
    k, apart = 0, True
    while k < len(lines):
        m = FIELD_LINE.match(lines[k])
        if not (m and apart and m.group(2).lower() in known):
            apart = not lines[k].strip() or lines[k].strip() == "----"
            k += 1
            continue
        base = len(m.group(1))
        text = lines[k][base:]
        k += 1
        while k < len(lines) and (lines[k].strip() == BLANKS or (
                lines[k].strip() and not FIELD_LINE.match(lines[k])
                and len(lines[k]) - len(lines[k].lstrip()) > base)):
            text += "\r\n" + ("  " if lines[k].strip() == BLANKS else " " + lines[k].strip())
            k += 1
        found.append((field_rule(m.group(2)), (text + "\r\n").encode("ascii", errors="replace")))
    return found


def examples() -> list[tuple[tuple[str, bytes], str, str]]:
    """The examples of the RFCs, each with the answer it has to get and, if that is a refusal,
    why: one RFC 5322 prints is refused if it has white space before the colon or none after it,
    or is one of `OBSOLETE`; every other is accepted, among them RFC 5322's obsolete phrase, which
    RFC 5536 §2.1 keeps."""
    out = []
    seen = set()
    for rule, data in printed(5322):
        line = data.split(b"\r\n")[0].decode("ascii")
        after = line.lstrip("ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789-")
        seen.add(line)
        if not after.startswith(":"):
            why = "white space before the colon (RFC 5322 §4.5)"
        elif not after.startswith(": "):
            why = "no space after the colon (RFC 5536 §2.2)"
        else:
            why = OBSOLETE.get(line, "")
        out.append(((rule, data), "0" if why else "1", why))
    missing = set(OBSOLETE) - seen
    if missing:
        raise LaneError(f"RFC 5322 does not print {sorted(missing)}")
    out += [((rule, data), "1", "") for rule, data in printed(5537) + printed(8315)]
    text = G.rfc(5536)
    for rule, quoted in QUOTED:
        if quoted not in text:
            raise LaneError(f"RFC 5536 does not print {quoted!r}")
        out.append(((rule, quoted.encode()), "1", ""))
    return out


def depth() -> int:
    """The depth the grammar's Lean data gives its interpreter's fuel, which the generator keeps
    current."""
    found = re.search(r"^def depth : Nat := (\d+)$", G.LEAN_OUT.read_text(encoding="utf-8"),
                      re.MULTILINE)
    if found is None:
        raise LaneError(f"{G.LEAN_OUT.relative_to(lanes.ROOT)} gives no depth")
    return int(found.group(1))


def nested() -> list[tuple[str, bytes]]:
    """Comments nested NESTED deep, alone and in a field, each of which has to be accepted."""
    deep = b"(" * NESTED + b"x" + b")" * NESTED
    return [("comment", deep), ("from", b"From: a@b.example " + deep + b"\r\n")]


def reaching(rule: str) -> set[str]:
    """The rules of the grammar text whose definitions reach `rule`, itself included."""
    refs = {name: set(G.refs(term)) for name, term in grammar().items()}
    reached = {rule}
    while True:
        more = {n for n, rs in refs.items() if rs & reached} - reached
        if not more:
            return reached
        reached |= more


def case_line(case: tuple[str, bytes]) -> str:
    rule, data = case
    return f"{rule} {data.hex() or '-'}"


def answer_lines(command: list[str], lines: list[str], workers: int = 1) -> list[str]:
    """The answers `command` gives to `lines`, a line each, from `workers` processes run at once,
    each given a share."""
    shares = [lines[k::workers] for k in range(workers)]

    def run(share: list[str]) -> list[str]:
        done = subprocess.run(command, input="".join(f"{ln}\n" for ln in share), capture_output=True,
                              text=True, timeout=3600, check=False)
        if done.returncode:
            raise LaneError(f"{command[0]} failed: {done.stderr[-500:]}")
        said = done.stdout.splitlines()
        if len(said) != len(share):
            raise LaneError(f"{command[0]} answered {len(said)} cases of {len(share)}")
        return said

    merged = [""] * len(lines)
    with ThreadPoolExecutor(workers) as pool:
        for k, said in enumerate(pool.map(run, shares)):
            merged[k::workers] = said
    return merged


def answers(command: list[str], cases: list[tuple[str, bytes]], workers: int = 1) -> list[str]:
    """The answers `command` gives to `cases`, a rule and bytes each."""
    return answer_lines(command, [case_line(c) for c in cases], workers)


def library_cases(cases: list[tuple[str, bytes]], model: list[str]) -> dict[str, list[tuple[str, bytes]]]:
    """For each of the library's transcriptions, the cases the model accepts on a rule that the
    transcription has to accept too: one whose definition and every rule it reaches came from
    that RFC unchanged or only narrowed (`UNCHANGED`)."""
    rules = noted()
    out: dict[str, list[tuple[str, bytes]]] = {}
    for library, origins in UNCHANGED.items():
        held = set()
        for name in rules:
            reached, todo = set(), [name]
            while todo:
                n = todo.pop()
                if n not in reached and n in rules:
                    reached.add(n)
                    todo.extend(G.refs(rules[n][0]))
            if all(rules[n][1] in origins for n in reached):
                held.add(name)
        out[library] = [c for c, a in zip(cases, model, strict=True) if a == "1" and c[0] in held]
    return out


def first_difference(command: list[str], tried: list[tuple[str, str]]) -> str | None:
    """The first case, a line, on which `command` answers otherwise than the answer it is paired
    with, trying them a chunk at a time as far as the first chunk that shows one."""
    for k in range(0, len(tried), CHUNK):
        chunk = tried[k:k + CHUNK]
        other = answer_lines(command, [c for c, _ in chunk], WORKERS)
        differs = [c for (c, a), b in zip(chunk, other, strict=True) if a != b]
        if differs:
            return differs[0]
    return None


def check() -> Report:
    OUT.mkdir(parents=True, exist_ok=True)
    current = subprocess.run([sys.executable, str(lanes.ROOT / "scripts/gen_abnf.py"), "--check"],
                             capture_output=True, text=True, check=False)
    if current.returncode:
        raise LaneError(current.stderr.strip() or current.stdout.strip())
    abnfgen = subprocess.run([sys.executable, str(lanes.ROOT / "scripts/bootstrap_tool.py"), "abnfgen"],
                             capture_output=True, text=True, check=True).stdout.strip()
    python = str(lanes.pinned_python(REQUIREMENTS))
    backend = subprocess.run([python, "-c", "import abnf.parser; print(abnf.parser._BACKEND)"],
                             capture_output=True, text=True, check=True).stdout.strip()
    if backend != "rust":
        raise LaneError(f"the reference runs on its {backend} backend, not the Rust one pinned")
    rng = random.Random(SEED)  # noqa: S311 -- a fixed seed, so that every run draws the same cases
    rules = [r for r, _ in G.FIELDS.values()] + [G.OPTIONAL[0]] + INNER
    steps, mark = {}, time.monotonic()
    cases: list[tuple[str, bytes]] = []
    derived: list[tuple[str, bytes]] = []
    for k, rule in enumerate(rules):
        for case in generated(abnfgen, rule, SEED + k):
            derived.append((rule, case))
            cases.append((rule, case))
            cases += [(rule, c) for c in changed(case, rng)]
    raw = len(derived)
    derived += covering(rng)
    for rule, case in derived[raw:]:
        cases.append((rule, case))
        cases += [(rule, c) for c in changed(case, rng)]
    derived += nested()
    cases += nested()
    expected = examples()
    cases += [c for c, _, _ in expected]
    cases += PAST_BOUNDS
    steps["cases"], mark = round(time.monotonic() - mark, 1), time.monotonic()
    model_command = [str(lanes.DN_COMPILER), "abnf-model"]
    model = answers(model_command, cases, WORKERS)
    steps["model"], mark = round(time.monotonic() - mark, 1), time.monotonic()
    reference = answers([python, str(REFERENCE)], cases, WORKERS)
    steps["reference"], mark = round(time.monotonic() - mark, 1), time.monotonic()
    if "fuel" in model:
        rule, data = cases[model.index("fuel")]
        raise LaneError(f"the interpreter ran out of fuel on {rule} {data!r}")
    for (rule, data), a, b in zip(cases, model, reference, strict=True):
        if a != b:
            raise LaneError(f"{rule} {data[:200]!r}: the model answers {a}, the reference {b}")
    said = dict(zip(cases, model, strict=True))
    refused = [(rule, case) for rule, case in derived if said[(rule, case)] != "1"]
    if refused:
        rule, case = refused[0]
        raise LaneError(f"{len(refused)} derivations refused, first {rule} {case[:200]!r}")
    past = [c for c in PAST_BOUNDS if said[c] != "0"]
    if past:
        raise LaneError(f"accepted past a repetition's bound: {past}")
    for (rule, data), want, _ in expected:
        if said[(rule, data)] != want:
            raise LaneError(f"the RFCs' example {rule} {data!r} is answered {said[(rule, data)]}, "
                            f"not {want}")
    for rule in rules:
        seen = {a for (r, _), a in zip(cases, model, strict=True) if r == rule}
        if seen != {"0", "1"}:
            raise LaneError(f"{rule} was never seen to {'refuse' if '0' not in seen else 'accept'}")
    held = library_cases(cases, model)
    for library, tried in held.items():
        if not tried:
            raise LaneError(f"no case is held to the library's {library}")
        other = first_difference([python, str(REFERENCE), "--library", library],
                                 [(case_line(c), "1") for c in tried])
        if other is not None:
            raise LaneError(f"the library's {library} refuses {other[:300]}")
    steps["library"], mark = round(time.monotonic() - mark, 1), time.monotonic()
    caught = {}
    for name, before, after in DEFECTS:
        text = GRAMMAR.read_text(encoding="ascii")
        if text.count(before) != 1:
            raise LaneError(f"the defect {name!r} names text the grammar does not hold once")
        planted = OUT / "planted.abnf"
        planted.write_bytes(text.replace(before, after).encode())
        # Only the cases of rules that reach the changed one can differ.
        near = reaching(before.split(" = ")[0])
        answered = [(case_line(c), a) for c, a in zip(cases, model, strict=True) if c[0] in near]
        differs = first_difference([python, str(REFERENCE), "--grammar", str(planted)], answered)
        if differs is None:
            raise LaneError(f"the defect {name!r} was not caught")
        caught[name] = differs[:120]
    steps["defects"], mark = round(time.monotonic() - mark, 1), time.monotonic()
    mutants = {}
    for mutant in MUTANTS:
        differs = first_difference([*model_command, "--mutant", mutant],
                                   [(case_line(c), a) for c, a in zip(cases, model, strict=True)])
        if differs is None:
            raise LaneError(f"the mutant {mutant} was not caught")
        mutants[mutant] = differs[:120]
    steps["mutants"] = round(time.monotonic() - mark, 1)
    accepted = model.count("1")
    refusals = [[data.split(b"\r\n")[0].decode("ascii"), why] for (_, data), _, why in expected if why]
    most = depth()
    measured = {"cases": f"{len(cases):,}", "defects planted in the reference's grammar": f"{len(DEFECTS):,}",
                "mutants of the interpreter": f"{len(MUTANTS):,}", "examples the RFCs print": f"{len(expected):,}"}
    baseline = (lanes.ROOT / "docs/baseline.md").read_text()
    assurance = (lanes.ROOT / "docs/assurance.md").read_text()
    stated = lanes.section(baseline, "\n| Header field grammar |", "\n|") + lanes.section(
        baseline, "\n### Header field grammar\n", "\n### ")
    wrong = lanes.misstated(stated, measured)
    wrong += lanes.misstated(lanes.section(assurance, "\n| Header field grammar (", "\n|"),
                             {k: v for k, v in measured.items() if k != "examples the RFCs print"})
    if wrong:
        raise LaneError(f"the documents state otherwise than measured: {wrong}")
    lanes.require_quoted({"docs/baseline.md": [f"refused, {len(refusals)} in all", f"{most} for this grammar"]})
    return Report("checked", None, [GRAMMAR, REFERENCE, REQUIREMENTS], {
        "fields": len(G.FIELDS) + 1, "grammar_rules": len(grammar()), "cases": len(cases),
        "accepted": accepted, "refused": len(cases) - accepted, "derivations": len(derived),
        "abnfgen_derivations": raw, "examples": len(expected), "examples_refused": refusals,
        "depth": most,
        "held_to_library": {library: len(tried) for library, tried in held.items()},
        "planted_defects_caught": caught, "mutants_caught": mutants,
        "seconds_by_step": steps, "reference_backend": backend})


def main() -> None:
    lanes.lane_main("ABNF", OUT, check)


if __name__ == "__main__":
    main()
