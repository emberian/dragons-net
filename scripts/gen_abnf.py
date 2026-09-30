#!/usr/bin/env python3
# SPDX-License-Identifier: AGPL-3.0-or-later AND BSD-3-Clause
"""The grammar of a Netnews article's header fields, taken from the RFCs in rfcs/.

Each rule is the RFC's own text, found by `abnf_text.extract`, except where this file says
otherwise and why: a verified erratum replaces a rule with its corrected text; the rules of RFC
2045 and RFC 2231, written in the notation of RFC 822 rather than ABNF, are carried over by hand,
each with the text it comes from; the obsolete syntax of RFC 5322 §4, which RFC 5536 §2.1 makes an
article non-conformant for, is taken out, except `obs-phrase` and the "GMT" zone, which RFC 5536
§2.1 and §3.1.1 keep; and the fields of RFC 5322 get the space after the colon that RFC 5536 §2.2
asks of every field. RFC 5536 restates some rules of RFC 5322 (§2.2, §3.1, §3.2); its version is
the one taken.

The grammar is the rules that the checks of the header fields reach (`FIELDS`), closed under
reference, and none of them may be left-recursive. It is written twice: as ABNF text
(`scripts/netnews.abnf`), which the independent reference loads, and as Lean data
(`DN.News.AbnfRules`), which the specification runs, together with the most terms a match can nest
at one position of its input, which bounds the interpreter's recursion. With `--check`, nothing is
written and a difference fails.

The rule texts in this file and in what it writes are code taken from IETF RFCs, under the notice
`notice` gives.
"""
from __future__ import annotations

import argparse
from collections.abc import Iterator
from pathlib import Path
import re
import sys

sys.path.insert(0, str(Path(__file__).resolve().parent))
import abnf_text as A  # the path above is what makes it importable

ROOT = Path(__file__).resolve().parent.parent
TEXT_OUT = ROOT / "scripts/netnews.abnf"
LEAN_OUT = ROOT / "lean/DN/News/AbnfRules.lean"
SPDX = "SPDX-License-Identifier: AGPL-3.0-or-later AND BSD-3-Clause"

# Where a rule comes from, when more than one RFC defines it or the name alone does not say.
FROM_5536 = [
    "unstructured", "msg-id", "msg-id-core", "id-left", "id-right", "no-fold-literal", "mdtext",
    "message-id", "orig-date", "from", "sender", "reply-to", "comments", "keywords", "subject",
    "references", "newsgroups", "newsgroup-list", "newsgroup-name", "component", "component-char",
    "path", "path-list", "path-diagnostic", "diag-match", "diag-other", "diag-deprecated",
    "diag-keyword", "diag-identity", "tail-entry", "path-identity", "path-nodot", "label",
    "toplabel", "alphanum", "approved", "archive", "archive-param", "control", "control-command",
    "verb", "argument", "distribution", "dist-list", "dist-name", "expires", "followup-to",
    "poster-text", "injection-date", "injection-info", "organization", "summary", "supersedes",
    "user-agent", "product", "product-version", "xref", "server-name", "location",
    "article-locator", "lines",
]
FROM_8315 = [
    "cancel-lock", "c-lock-list", "c-lock", "c-lock-string", "base64-char", "base64-terminal",
    "cancel-key", "c-key-list", "c-key", "c-key-string", "scheme", "scheme-char", "obs-scheme",
    "obs-c-key-string", "base64-octet",
]
FROM_3986 = ["ipv4address", "ipv6address", "h16", "ls32", "dec-octet"]
FROM_5234 = ["alpha", "bit", "char", "cr", "crlf", "ctl", "digit", "dquote", "hexdig", "htab",
             "lf", "lwsp", "octet", "sp", "vchar", "wsp"]

# Verified errata that change a rule, with the corrected text (www.rfc-editor.org/errata).
ERRATA = {
    "zone": ("RFC 5322", 6639, """
   zone            =   (FWS ( "+" / "-" ) 4DIGIT) / [FWS] obs-zone"""),
    "received": ("RFC 5322", 3979, """
   received        =   "Received:" [1*received-token / CFWS]
                       ";" date-time CRLF"""),
}

# Every verified erratum the grammar follows: the two above; RFC 5234's two on its own grammar
# (§4), which the reading of ABNF in abnf_text.py follows; RFC 2045's on `tspecials` and RFC 2231's
# two on its grammar, which the rules carried over from them follow; and RFC 5536's, by which the
# table of fields below stands for its `fields`. The upstream check keeps each one verified, with
# its corrected text where a rule here holds it.
APPLIED_ERRATA = [("RFC5322", 6639), ("RFC5322", 3979), ("RFC5234", 2968), ("RFC5234", 3076),
                  ("RFC2045", 512), ("RFC2231", 477), ("RFC2231", 7326), ("RFC5536", 5116)]

# RFC 5536 §2.1: of RFC 5322's obsolete syntax, only the phrase and the "GMT" zone are conformant.
# RFC 8315 §6 has agents accept its own obsolete scheme and key.
KEPT_OBSOLETE = {"obs-phrase", "obs-zone", "obs-scheme", "obs-c-key-string"}
RESTRICTED = {
    "obs-zone": ("RFC 5536 §2.1, §3.1.1", 'obs-zone = "GMT"'),
}

# Where a rule's text says other than it means. RFC 5536 §3.2.4's dist-name reads, by the
# precedence of RFC 5234 §3.10, as one letter or a digit followed by more; its own text names
# "world" and "local" as dist-names, which only the grouped reading admits. RFC 5536 §3.1.3's
# msg-id, which has none of the comments and white space RFC 5322's carries around it, "applies
# wherever <msg-id> is used"; RFC 5536 §3.2.10 moves them into References' own rule, and In-Reply-To
# and Resent-Message-ID, which it does not restate, get them the same way, where RFC 5322's msg-id
# had them.
CORRECTED = {
    "dist-name": ("RFC 5536 §3.2.4, grouped as its text intends",
                  'dist-name = (ALPHA / DIGIT) *(ALPHA / DIGIT / "+" / "-" / "_")'),
    "in-reply-to": ("RFC 5322 §3.6.4 with the msg-id of RFC 5536 §3.1.3",
                    'in-reply-to = "In-Reply-To:" [CFWS] msg-id *([CFWS] msg-id) [CFWS] CRLF'),
    "resent-msg-id": ("RFC 5322 §3.6.6 with the msg-id of RFC 5536 §3.1.3",
                      'resent-msg-id = "Resent-Message-ID:" [CFWS] msg-id [CFWS] CRLF'),
}

# RFC 5322 §3.6.7 names Return-Path's address `path`, a name RFC 5536 gives the Path field; the
# address is renamed where Return-Path refers to it.
ALIASES = {"return-path-address": "path"}
RENAMES = {"return": {"path": "return-path-address"}}

# RFC 2045 §5.1 and RFC 2231 §7, in RFC 822 notation, carried over into ABNF. `token` is a CHAR
# that is not SPACE, a CTL or one of `tspecials` (erratum 512), and `attribute-char` one that is
# not those nor "*", "'" or "%", written as the ranges that leaves (`check_transcriptions`);
# `charset` and `language` are prose in RFC 2231 ("registered character set name", "registered
# language tag"), read here for their syntax only. `other-sections` is as erratum 7326 corrects
# it, and `extended-value` is `extended-initial-value` (erratum 477). RFC 822's notation lets
# comments and white space stand between any two tokens of a rule, which, as RFC 5536 §3.2.8 notes,
# puts [CFWS] on either side of a parameter's "=" (and RFC 2045 §1, as erratum 2586 corrects it,
# says the same of all its fields); the parameters say so, with [CFWS] after the value, before the
# ";" that may follow it.
TRANSCRIBED = {
    "token": ("RFC 2045 §5.1, erratum 512", (
        "token = 1*(%d33 / %d35-39 / %d42-43 / %d45-46 / %d48-57 / %d65-90 / %d94-126)")),
    "value": ("RFC 2045 §5.1", "value = token / quoted-string"),
    "parameter": ("RFC 2231 §7", "parameter = regular-parameter / extended-parameter"),
    "regular-parameter": ("RFC 2231 §7, with the CFWS of RFC 5536 §3.2.8", (
        'regular-parameter = regular-parameter-name [CFWS] "=" [CFWS] value [CFWS]')),
    "regular-parameter-name": ("RFC 2231 §7", "regular-parameter-name = attribute [section]"),
    "attribute": ("RFC 2231 §7", "attribute = 1*attribute-char"),
    "attribute-char": ("RFC 2231 §7", (
        "attribute-char = %d33 / %d35-36 / %d38 / %d43 / %d45-46 / %d48-57 / %d65-90 / %d94-126")),
    "section": ("RFC 2231 §7", "section = initial-section / other-sections"),
    "initial-section": ("RFC 2231 §7", 'initial-section = "*0"'),
    "other-sections": ("RFC 2231 §7, erratum 7326", 'other-sections = "*" %d49-57 *DIGIT'),
    "extended-parameter": ("RFC 2231 §7, erratum 477, with the CFWS of RFC 5536 §3.2.8", (
        'extended-parameter = (extended-initial-name [CFWS] "=" [CFWS] extended-initial-value '
        '[CFWS]) / (extended-other-names [CFWS] "=" [CFWS] extended-other-values [CFWS])')),
    "extended-initial-name": ("RFC 2231 §7", 'extended-initial-name = attribute [initial-section] "*"'),
    "extended-other-names": ("RFC 2231 §7", 'extended-other-names = attribute other-sections "*"'),
    "extended-initial-value": ("RFC 2231 §7", (
        "extended-initial-value = [charset] \"'\" [language] \"'\" extended-other-values")),
    "extended-other-values": ("RFC 2231 §7", "extended-other-values = *(ext-octet / attribute-char)"),
    "ext-octet": ("RFC 2231 §7", 'ext-octet = "%" 2(DIGIT / "A" / "B" / "C" / "D" / "E" / "F")'),
    "charset": ("RFC 2231 §7", "charset = 1*attribute-char"),
    "language": ("RFC 2231 §7", 'language = 1*(ALPHA / DIGIT / "-")'),
}

# Each header field the checks know, by its name, with the rule for the whole field line and the
# section that defines it. A field of another name is an `optional-field` (RFC 5322 §3.6.8) with
# RFC 5536's `unstructured`. So is each of MIME's fields: RFC 5536 §3.2 gives them the meanings of
# RFC 2045 under the rules of §2.2, and a server, which stores and serves an article without
# reading its MIME structure, checks them by those rules alone.
FIELDS = {
    "Date": ("orig-date", "RFC 5536 §3.1.1"),
    "From": ("from", "RFC 5536 §3.1.2"),
    "Message-ID": ("message-id", "RFC 5536 §3.1.3"),
    "Newsgroups": ("newsgroups", "RFC 5536 §3.1.4"),
    "Path": ("path", "RFC 5536 §3.1.5"),
    "Subject": ("subject", "RFC 5536 §3.1.6"),
    "Comments": ("comments", "RFC 5536 §3.2"),
    "Keywords": ("keywords", "RFC 5536 §3.2"),
    "Reply-To": ("reply-to", "RFC 5536 §3.2"),
    "Sender": ("sender", "RFC 5536 §3.2"),
    "Approved": ("approved", "RFC 5536 §3.2.1"),
    "Archive": ("archive", "RFC 5536 §3.2.2"),
    "Control": ("control", "RFC 5536 §3.2.3"),
    "Distribution": ("distribution", "RFC 5536 §3.2.4"),
    "Expires": ("expires", "RFC 5536 §3.2.5"),
    "Followup-To": ("followup-to", "RFC 5536 §3.2.6"),
    "Injection-Date": ("injection-date", "RFC 5536 §3.2.7"),
    "Injection-Info": ("injection-info", "RFC 5536 §3.2.8"),
    "Organization": ("organization", "RFC 5536 §3.2.9"),
    "References": ("references", "RFC 5536 §3.2.10"),
    "Summary": ("summary", "RFC 5536 §3.2.11"),
    "Supersedes": ("supersedes", "RFC 5536 §3.2.12"),
    "User-Agent": ("user-agent", "RFC 5536 §3.2.13"),
    "Xref": ("xref", "RFC 5536 §3.2.14"),
    "Lines": ("lines", "RFC 5536 §3.3.1"),
    "Cancel-Lock": ("cancel-lock", "RFC 8315 §2.1"),
    "Cancel-Key": ("cancel-key", "RFC 8315 §2.2"),
    "To": ("to", "RFC 5322 §3.6.3"),
    "Cc": ("cc", "RFC 5322 §3.6.3"),
    "Bcc": ("bcc", "RFC 5322 §3.6.3"),
    "Resent-Date": ("resent-date", "RFC 5322 §3.6.6"),
    "Resent-From": ("resent-from", "RFC 5322 §3.6.6"),
    "Resent-Sender": ("resent-sender", "RFC 5322 §3.6.6"),
    "Resent-To": ("resent-to", "RFC 5322 §3.6.6"),
    "Resent-Cc": ("resent-cc", "RFC 5322 §3.6.6"),
    "Resent-Bcc": ("resent-bcc", "RFC 5322 §3.6.6"),
    "Return-Path": ("return", "RFC 5322 §3.6.7"),
    "Received": ("received", "RFC 5322 §3.6.7, erratum 3979"),
    "In-Reply-To": ("in-reply-to", "RFC 5322 §3.6.4"),
    "Resent-Message-ID": ("resent-msg-id", "RFC 5322 §3.6.6"),
}
OPTIONAL = ("optional-field", "RFC 5322 §3.6.8")

# RFC 5536 §2.2 asks for a space after the colon of every field, "even those documented in
# [RFC5322]", and lets news agents accept a field without it. RFC 5536's rules write the space;
# RFC 5322's do not, and get it here: an injecting agent refuses what RFC 5536 does not allow
# (RFC 5537 §3.5), and what it stores is served on to agents that may count on the space.
SPACED = "a space after the colon, as RFC 5536 §2.2 asks of every field"

# The rules are Code Components of IETF documents (the IETF Trust's Legal Provisions, §4.a). What
# is written with them is the attribution §4.d asks for, the notification §6.d allows in place of
# the Revised BSD License's text, and RFC 2231's notice, which its permission to derive works from
# it asks be kept.
SOURCES = "RFC 5536, RFC 8315, RFC 5322, RFC 5234, RFC 3986, RFC 2045 and RFC 2231"


def rfc(number: int) -> str:
    return (ROOT / "rfcs" / f"rfc{number}.txt").read_text(encoding="ascii")


def notice() -> list[str]:
    """The notice the rules carry, a paragraph a line."""
    return [
        (f"This code was derived from IETF {SOURCES}, changed where a rule's note says. Please "
         "reproduce this note if possible."),
        ("Copyright (c) 2009, 2018 IETF Trust and the persons identified as authors of the code "
         "(RFC 5536, RFC 8315). Copyright (C) The IETF Trust (2008) (RFC 5322, RFC 5234). Copyright "
         "(C) The Internet Society (2005) (RFC 3986). All rights reserved."),
        ("Redistribution and use in source and binary forms, with or without modification, is "
         "permitted pursuant to, and subject to the license terms contained in, the Revised BSD "
         "License set forth in Section 4.c of the IETF Trust's Legal Provisions Relating to IETF "
         "Documents (https://trustee.ietf.org/license-info)."),
        *rfc2231_notice(),
    ]


def rfc2231_notice() -> list[str]:
    """RFC 2231's copyright notice and the paragraph it asks derived works to carry, as its Full
    Copyright Statement prints them."""
    lines = A.body_lines(rfc(2231))
    heading = "12.  Full Copyright Statement"
    if heading not in lines:
        raise SystemExit(f"RFC 2231 has no {heading!r}")
    paragraphs: list[list[str]] = [[]]
    for line in lines[lines.index(heading) + 1:]:
        if line.strip():
            paragraphs[-1].append(line.strip())
        elif paragraphs[-1]:
            if len(paragraphs) == 2:
                break
            paragraphs.append([])
    text = [" ".join(" ".join(p).split()) for p in paragraphs]
    if len(text) != 2 or not text[0].startswith("Copyright (C) The Internet Society") \
            or not text[1].startswith("This document and translations of it may be copied"):
        raise SystemExit("RFC 2231's Full Copyright Statement is not its notice and permission")
    return [f"RFC 2231: {text[0]}", text[1]]


class Grammar:
    def __init__(self) -> None:
        self.texts = {n: rfc(n) for n in (5234, 5322, 5536, 3986, 8315)}
        self.rules: dict[str, A.Term] = {}
        self.origin: dict[str, str] = {}

    def definition(self, name: str) -> tuple[str, str]:
        """The text defining `name` and where it comes from."""
        if name in RESTRICTED:
            where, text = RESTRICTED[name]
            return text, where
        if name in CORRECTED:
            where, text = CORRECTED[name]
            return text, where
        if name in ALIASES:
            return A.extract(self.texts[5322], ALIASES[name]), "RFC 5322, renamed"
        if name in TRANSCRIBED:
            where, text = TRANSCRIBED[name]
            return text, where
        if name in ERRATA:
            source, number, text = ERRATA[name]
            return text, f"{source}, erratum {number}"
        for number, names in ((5536, FROM_5536), (8315, FROM_8315), (3986, FROM_3986),
                              (5234, FROM_5234)):
            if name in names:
                return A.extract(self.texts[number], name), f"RFC {number}"
        return A.extract(self.texts[5322], name), "RFC 5322"

    def take(self, root: str) -> None:
        todo = [root]
        while todo:
            name = todo.pop()
            if name in self.rules or excluded(name):
                continue
            text, where = self.definition(name)
            parsed, incremental, term = A.parse(text)
            if parsed != ALIASES.get(name, name) or incremental:
                raise SystemExit(f"{where} defines {parsed} where {name} was looked for")
            term = rename(term, RENAMES.get(name, {}))
            if name == root:
                with_space = spaced(name, term)
                if with_space != term:
                    term, where = with_space, f"{where}, with {SPACED}"
            self.rules[name] = term
            self.origin[name] = where
            todo.extend(refs(term))

    def pruned(self) -> dict[str, A.Term]:
        """The rules with every alternative that needs excluded syntax taken out."""
        out = {}
        for name, term in self.rules.items():
            kept = prune(term)
            if kept is None:
                raise SystemExit(f"{name} can match nothing once the obsolete syntax is gone")
            out[name] = kept
        # A rule only the excluded syntax reached is dropped with it.
        reached: set[str] = set()
        todo = [FIELDS[f][0] for f in FIELDS] + [OPTIONAL[0]]
        while todo:
            name = todo.pop()
            if name not in reached:
                reached.add(name)
                todo.extend(refs(out[name]))
        return {n: t for n, t in out.items() if n in reached}


def spaced(name: str, t: A.Term) -> A.Term:
    """A field's rule with SP after the colon that ends the field's name, if it has none."""
    items = list(t.items) if isinstance(t, A.Seq) else []
    colon = next((k for k, i in enumerate(items) if isinstance(i, A.Text) and i.value.endswith(b":")),
                 None)
    if colon is None:
        raise SystemExit(f"the rule of the field {name} has no colon ending the field's name")
    if items[colon + 1:colon + 2] == [A.Ref("sp")]:
        return t
    return A.Seq((*items[:colon + 1], A.Ref("sp"), *items[colon + 1:]))


def rename(t: A.Term, names: dict[str, str]) -> A.Term:
    match t:
        case A.Ref(name):
            return A.Ref(names.get(name, name))
        case A.Seq(items):
            return A.Seq(tuple(rename(i, names) for i in items))
        case A.Alt(items):
            return A.Alt(tuple(rename(i, names) for i in items))
        case A.Rep(lo, hi, item):
            return A.Rep(lo, hi, rename(item, names))
    return t


def excluded(name: str) -> bool:
    return name.startswith("obs-") and name not in KEPT_OBSOLETE


def refs(t: A.Term) -> list[str]:
    match t:
        case A.Ref(name):
            return [name]
        case A.Seq(items) | A.Alt(items):
            return [r for i in items for r in refs(i)]
        case A.Rep(_, _, item):
            return refs(item)
        case A.Prose(text):
            raise SystemExit(f"prose value <{text}> where a rule is needed")
    return []


EMPTY = A.Seq(())


def prune(t: A.Term) -> A.Term | None:
    """`t` without what needs excluded syntax: None if nothing is left of it."""
    match t:
        case A.Ref(name):
            return None if excluded(name) else t
        case A.Seq(items):
            kept = [prune(i) for i in items]
            if any(k is None for k in kept):
                return None
            return A.Seq(tuple(k for k in kept if k is not None))
        case A.Alt(items):
            alts = [k for k in (prune(i) for i in items) if k is not None]
            if not alts:
                return None
            return alts[0] if len(alts) == 1 else A.Alt(tuple(alts))
        case A.Rep(lo, hi, item):
            inner = prune(item)
            if inner is None:
                return EMPTY if lo == 0 else None
            return A.Rep(lo, hi, inner)
    return t


def nullable(rules: dict[str, A.Term]) -> set[str]:
    """The rules that match the empty string."""
    found: set[str] = set()
    while True:
        more = {n for n, t in rules.items() if n not in found and empty(t, found)}
        if not more:
            return found
        found |= more


def empty(t: A.Term, null: set[str]) -> bool:
    """Whether `t` matches the empty string, the rules of `null` being those that do."""
    match t:
        case A.Text(v) | A.Exact(v):
            return not v
        case A.Ref(name):
            return name in null
        case A.Seq(items):
            return all(empty(i, null) for i in items)
        case A.Alt(items):
            return any(empty(i, null) for i in items)
        case A.Rep(lo, hi, item):
            return lo == 0 or hi == 0 or empty(item, null)
    return False


def subterms(t: A.Term) -> Iterator[A.Term]:
    yield t
    match t:
        case A.Seq(items) | A.Alt(items):
            for i in items:
                yield from subterms(i)
        case A.Rep(_, _, item):
            yield from subterms(item)


def depth(rules: dict[str, A.Term]) -> int:
    """The most terms a match can go through, one inside the next, without the input moving on:
    a match of a term starting where its parent's starts is one level down, and a match that
    starts further on is a new run of levels. Without left recursion (a rule reached again at the
    position it started from, which is refused here) the levels at one position are finite, and
    this is their greatest number, the interpreter's `depth`. A run starts with a reference to the
    rule it matches, so a reference to each rule counts, whether the grammar makes it or not."""
    null = nullable(rules)
    done: dict[str, int] = {}
    active: list[str] = []

    def rule(name: str) -> int:
        if name in done:
            return done[name]
        if name in active:
            cycle = [*active[active.index(name):], name]
            raise SystemExit("the grammar is left-recursive: " + " -> ".join(cycle))
        active.append(name)
        done[name] = term(rules[name])
        active.pop()
        return done[name]

    def term(t: A.Term) -> int:
        """The most levels a match of `t` can go down at the position it starts from."""
        match t:
            case A.Ref(name):
                return 1 + rule(name)
            case A.Seq(items):
                most = 0
                for i in items:
                    most = max(most, term(i))
                    if not empty(i, null):
                        break
                return 1 + most
            case A.Alt(items):
                return 1 + max((term(i) for i in items), default=0)
            case A.Rep(_, _, item):
                return 1 + term(item)
        return 1

    starts = [A.Ref(name) for name in rules] + [s for t in rules.values() for s in subterms(t)]
    return max(term(s) for s in starts)


def notation(number: int, name: str) -> str:
    """A definition in RFC 822 notation, `name := ...`, as RFC `number` first prints it, up to the
    blank line after it, comments dropped and white space squeezed."""
    lines = A.body_lines(rfc(number))
    start = re.compile(r"^ +" + re.escape(name) + r" +:=")
    k = next((k for k, line in enumerate(lines) if start.match(line)), None)
    if k is None:
        raise SystemExit(f"RFC {number} does not define {name} in the notation of RFC 822")
    taken = []
    while lines[k].strip():
        taken.append(A.strip_comments(lines[k]))
        k += 1
    return " ".join(" ".join(taken).split())


def quoted(definition: str) -> set[str]:
    """The characters a definition names, each in quotes, `<">` for the quote itself."""
    return set(re.findall(r'"(.)"', definition)) | ({'"'} if '<">' in definition else set())


def check_transcriptions() -> None:
    """The ranges written for `token` and `attribute-char` leave exactly what RFC 2045 and RFC
    2231 describe: a CHAR that is not SPACE, a CTL or one of the characters each names."""
    tspecials = notation(2045, "tspecials")
    described = {
        "token": (notation(2045, "token"),
                  "token := 1*<any (US-ASCII) CHAR except SPACE, CTLs, or tspecials>",
                  quoted(tspecials)),
        "attribute-char": (notation(2231, "attribute-char"),
                           ("attribute-char := <any (US-ASCII) CHAR except SPACE, CTLs, "
                            "\"*\", \"'\", \"%\", or tspecials>"),
                           quoted(tspecials) | quoted(notation(2231, "attribute-char"))),
    }
    for name, (text, expected, excluded_chars) in described.items():
        if text != expected:
            raise SystemExit(f"the RFC defines {name} as {text!r}, not as the transcription reads it")
        _, _, t = A.parse(TRANSCRIBED[name][1])
        allowed = set(chars(t))
        wanted = {c for c in range(33, 127) if chr(c) not in excluded_chars}
        if allowed != wanted:
            raise SystemExit(f"{name}: the ranges allow {sorted(allowed ^ wanted)} differently")


def chars(t: A.Term) -> list[int]:
    match t:
        case A.Range(lo, hi):
            return list(range(lo, hi + 1))
        case A.Alt(items):
            return [c for i in items for c in chars(i)]
        case A.Rep(_, _, item):
            return chars(item)
    raise SystemExit(f"not a set of characters: {A.show(t)}")


WIDTH = 100


def lean_name(rule: str) -> str:
    """A Lean name for a rule, clear of Lean's keywords (`from`, `return`, `section`)."""
    return "r" + "".join(part[:1].upper() + part[1:] for part in rule.split("-"))


def lean_string(value: bytes) -> str:
    return '"' + value.decode("ascii").replace("\\", "\\\\").replace('"', '\\"') + '"'


def lean_term(t: A.Term, index: dict[str, int]) -> str:
    match t:
        case A.Range(lo, hi):
            return f".range {lo} {hi}"
        case A.Text(v):
            return f".text {lean_string(v)}"
        case A.Exact(v):
            return ".exact [" + ", ".join(str(b) for b in v) + "]"
        case A.Ref(name):
            return f".ref {index[name]}"
        case A.Seq(items) | A.Alt(items):
            kind = "seq" if isinstance(t, A.Seq) else "alt"
            return f".{kind} [" + ", ".join(lean_term(i, index) for i in items) + "]"
        case A.Rep(lo, hi, item):
            return f".rep {lo} {'none' if hi is None else f'(some {hi})'} ({lean_term(item, index)})"
    raise TypeError(t)


def pieces(text: str) -> list[str]:
    """`text` cut after each space outside a string literal: the places a line may break."""
    out, cur, quoted, escaped = [], "", False, False
    for ch in text:
        cur += ch
        if escaped:
            escaped = False
        elif ch == "\\" and quoted:
            escaped = True
        elif ch == '"':
            quoted = not quoted
        elif ch == " " and not quoted:
            out.append(cur)
            cur = ""
    return [*out, cur] if cur else out


def wrapped(text: str, first: int, indent: str) -> list[str]:
    """`text` broken at spaces outside string literals so that no line is wider than WIDTH, the
    first line having `first` characters before it and the others starting with `indent`."""
    lines, line, width = [], "", WIDTH - first
    for piece in pieces(text):
        if line.strip() and len(line) + len(piece.rstrip()) > width:
            lines.append(line.rstrip())
            line, width = indent, WIDTH
        line += piece
    return [*lines, line.rstrip()]


def words(text: str, width: int) -> list[str]:
    """`text` broken at spaces into lines of at most `width` characters, an RFC's number kept with
    its name."""
    lines, line = [], ""
    for w in re.findall(r"RFC \d+\S*|\S+", text):
        if line and len(line) + 1 + len(w) > width:
            lines.append(line)
            line = ""
        line = f"{line} {w}" if line else w
    return [*lines, line]


def doc(text: str) -> list[str]:
    """A doc comment holding `text`, wrapped, with nothing in it that opens or closes a comment."""
    text = text.replace("/-", "/ -").replace("-/", "- /")
    lines, line = [], "/--"
    for w in text.split(" "):
        if len(line) + 1 + len(w) > WIDTH - 3:
            lines.append(line)
            line = ""
        line = f"{line} {w}" if line else w
    return [*lines, f"{line} -/"]


def lean_file(rules: dict[str, A.Term], origin: dict[str, str], most: int) -> str:
    names = sorted(rules)
    index = {n: k for k, n in enumerate(names)}
    out = [
        f"-- {SPDX}",
        "import DN.News.Abnf",
        "",
        "/-!",
        "# DN.News.AbnfRules",
        "",
        "The grammar of a Netnews article's header fields, as `scripts/gen_abnf.py` takes it from the",
        "RFCs in `rfcs/`: that script says where each rule comes from and where, and why, it differs",
        "from an RFC's text, and writes this file, which a check keeps current. Rules refer to each",
        "other by their place in `grammar`, which is the order of their names.",
        "",
        "## Notice",
        "",
    ]
    for paragraph in notice():
        out += [*words(paragraph.replace("-/", "- /"), WIDTH), ""]
    out += ["-/", "", "namespace DN.News.AbnfRules", "", "open DN.News.Abnf", ""]
    for n in names:
        out += doc(f"`{n} = {A.show(rules[n])}` ({origin[n]})")
        head = f"def {lean_name(n)} : Term := "
        body = wrapped(lean_term(rules[n], index), len(head), "    ")
        out.append(head + body[0])
        out += body[1:]
        out.append("")
    out.append("/-- The rules, in the order of their names. -/")
    out += wrapped("def grammar : Array Term := #[" + ", ".join(lean_name(n) for n in names) + "]",
                   0, "  ")
    out.append("")
    out.append("/-- The rules' names, as the RFCs write them in lower case. -/")
    out += wrapped("def names : Array String := #[" + ", ".join(f'"{n}"' for n in names) + "]", 0, "  ")
    out.append("")
    out.append("/-- The rule each field is checked by, by the field's name, and the rule for any other. -/")
    fields = ", ".join(f'("{f}", {index[r]})' for f, (r, _) in FIELDS.items())
    out += wrapped(f"def fieldRules : List (String × Nat) := [{fields}]", 0, "  ")  # noqa: RUF001 -- Lean's product
    out.append("")
    out.append(f"def optionalField : Nat := {index[OPTIONAL[0]]}")
    out.append("")
    out += doc("The most terms a match of this grammar goes through, one inside the next, at one "
               "position of its input: the grammar has no left recursion, and `scripts/gen_abnf.py` "
               "counts them (`DN.News.Abnf.fuel`).")
    out.append(f"def depth : Nat := {most}")
    out += ["", "end DN.News.AbnfRules", ""]
    return "\n".join(out)


def abnf_file(rules: dict[str, A.Term], origin: dict[str, str]) -> str:
    """The rules as ABNF text, without the core rules of RFC 5234 appendix B, which every ABNF
    implementation has as its own and the reference refuses to have redefined. Its lines end in LF,
    as every text file here does; its readers take lines as lines."""
    out = [f"; {SPDX}",
           "; The grammar of a Netnews article's header fields, written by scripts/gen_abnf.py from",
           "; the RFCs in rfcs/; each rule says where it comes from. The core rules of RFC 5234",
           "; appendix B are not repeated.", ";"]
    for paragraph in notice():
        out += [f"; {line}" for line in words(paragraph, WIDTH - 2)] + [";"]
    out[-1] = ""
    for n in sorted(r for r in rules if r not in FROM_5234):
        line = f"{n} = {A.show(rules[n])}"
        if A.parse(line) != (n, False, rules[n]):
            raise SystemExit(f"{n} is printed as ABNF that reads back otherwise: {line}")
        out.append("; " + origin[n].replace("§", "section "))
        out.append(line)
    return "\n".join(out) + "\n"


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    parser.add_argument("--check", action="store_true", help="fail if the written files differ")
    args = parser.parse_args()
    check_transcriptions()
    g = Grammar()
    for rule, _ in [*FIELDS.values(), OPTIONAL]:
        g.take(rule)
    rules = g.pruned()
    most = depth(rules)
    outputs = {TEXT_OUT: abnf_file(rules, g.origin), LEAN_OUT: lean_file(rules, g.origin, most)}
    stale = [path for path, text in outputs.items()
             if not path.exists() or path.read_bytes() != text.encode("utf-8")]
    if args.check:
        if stale:
            sys.exit("the grammar is not current: run python3 scripts/gen_abnf.py: "
                     + ", ".join(str(p.relative_to(ROOT)) for p in stale))
        return
    for path in stale:
        path.write_bytes(outputs[path].encode("utf-8"))
    print(f"{len(rules)} rules, depth {most}; wrote {len(stale)} files", file=sys.stderr)


if __name__ == "__main__":
    main()
