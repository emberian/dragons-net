#!/usr/bin/env python3
# SPDX-License-Identifier: AGPL-3.0-or-later
"""Which proto-articles a POST accepts and what the server adds, held two ways.
`DN.News.ArticleSpec`, run by `dn-compiler article-model`, and the independent reference
scripts/article_ref.py have to give the same answer, to the byte, on every case:

- cases written for each rule, on both sides of each bound, each with the answer RFC 5536, RFC
  5537 §3.5 and decision 0005 give it, which both have to give;
- articles built around fields the grammar derives, for each field's rule, and those articles
  with a byte dropped, replaced or inserted;
- dates written each way the grammar lets them be, each accepted, and with another day of the
  week refused;
- the header fields the RFCs print, each in an article;
- INN's test articles (tests/corpus/inn-articles), as they are and as proto-articles, with the
  answers recorded here, which both have to give;
- contexts at each bound the server's configuration may reach, and past each, which both have to
  refuse to run;
- the date the server writes for a wall clock at every day from 1970 to 2400, and that date read
  back, which has to give the wall clock again.

Each version of the rules with one of them changed (`DN.News.ArticleSpec.Mutant`) has to answer
some case otherwise than the reference (docs/baseline.md, "Article acceptance").
"""
from __future__ import annotations

import calendar
from dataclasses import dataclass, replace
import email.utils
import hashlib
import json
from pathlib import Path
import random
import subprocess
import sys
import time

sys.path.insert(0, str(Path(__file__).resolve().parent))
import abnf_check as C  # the path above is what makes these importable
import gen_abnf as G
import lanes
from lanes import LaneError, Report

OUT = lanes.ROOT / "build/article"
REFERENCE = lanes.ROOT / "scripts/article_ref.py"
REQUIREMENTS = lanes.ROOT / "scripts/requirements-tests.txt"
CORPUS = lanes.ROOT / "tests/corpus/inn-articles"
PROVENANCE = lanes.ROOT / "docs/provenance.json"
SEED = 20260930
DERIVED = 20
# Mon, 21 Sep 2026 14:13:20 +0000.
WALL = 1790000000
DAY = 86400
AHEAD, PAST = DAY, 3 * DAY
IDENTITY, RANDOM = b"news.example.org", b"5f3a"
GROUPS = [b"local.test", b"local.other"]
# The versions of the rules with one changed, by the name `dn-compiler article-model --mutant`
# takes.
MUTANTS = ["header-longer", "line-longer", "injection-info-allowed", "xref-allowed",
           "traces-allowed", "deprecated-allowed", "control-allowed", "supersedes-allowed",
           "approved-allowed", "blank-allowed", "repeats-allowed", "subject-optional",
           "posted-allowed", "id-longer", "sender-unneeded", "all-allowed", "dates-unread",
           "ahead-longer", "past-longer", "groups-more", "reserved-allowed", "unknown-accepted",
           "injection-date-always", "replaced"]
REASONS = ["no-header", "no-separator", "header-too-long", "line-too-long", "malformed",
           "injected", "traced", "deprecated", "not-offered", "blank-line", "bad-field",
           "repeated", "missing", "posted", "long-message-id", "no-sender", "distribution-all",
           "bad-date", "date-ahead", "date-past", "too-many-groups", "reserved-group",
           "no-known-group"]
# The last day whose date is written and read back: 2400-01-01.
LAST_DAY = calendar.timegm((2400, 1, 1, 0, 0, 0)) // DAY

WEEK = ["Mon", "Tue", "Wed", "Thu", "Fri", "Sat", "Sun"]
MONTHS = ["Jan", "Feb", "Mar", "Apr", "May", "Jun", "Jul", "Aug", "Sep", "Oct", "Nov", "Dec"]


@dataclass(frozen=True)
class Ctx:
    """What the server and the connection bring to a POST."""
    wall: int = WALL
    seq: int = 7
    run: int = 1
    conn: int = 2
    identity: bytes = IDENTITY
    random: bytes = RANDOM
    groups: tuple[bytes, ...] = tuple(GROUPS)


Case = tuple[Ctx, bytes, str | None]
BASE = Ctx()


def line(ctx: Ctx, article: bytes) -> str:
    groups = ",".join(g.hex() for g in ctx.groups) or "-"
    return (f"check {ctx.wall} {ctx.seq} {ctx.run} {ctx.conn} {ctx.identity.hex()} "
            f"{ctx.random.hex()} {groups} {article.hex() or '-'}")


def date(when: int, *, weekday: bool = True, zone: str = "+0000") -> bytes:
    """A date as RFC 5322 writes it, from the standard library's clock arithmetic."""
    t = time.gmtime(when)
    head = f"{WEEK[t.tm_wday]}, " if weekday else ""
    return (f"{head}{t.tm_mday:02d} {MONTHS[t.tm_mon - 1]} {t.tm_year} "
            f"{t.tm_hour:02d}:{t.tm_min:02d}:{t.tm_sec:02d} {zone}").encode()


MINIMAL = [b"From: a@b.example", b"Newsgroups: local.test", b"Subject: hi"]


def article(*fields: bytes, body: bytes = b"body\r\n") -> bytes:
    return b"".join(f + b"\r\n" for f in fields) + b"\r\n" + body


def plus(*fields: bytes) -> bytes:
    """The minimal proto-article with more fields before its own."""
    return article(*fields, *MINIMAL)


def without(name: bytes, *fields: bytes) -> bytes:
    """The minimal proto-article without its field `name`, with `fields` before it."""
    return article(*fields, *(f for f in MINIMAL if not f.lower().startswith(name.lower() + b":")))


def refused(reason: str, name: bytes = b"") -> str:
    return f"refused {reason} {name.hex() or '-'}"


ACCEPTED = "accepted"

# A value each field that may appear once can have.
VALUE = {
    b"Date": date(WALL - 60), b"From": b"a@b.example", b"Message-ID": b"<a@b.example>",
    b"Newsgroups": b"local.test", b"Path": b"a.example!not-for-mail", b"Subject": b"hi",
    b"Archive": b"no", b"Distribution": b"local", b"Expires": date(WALL + 30 * DAY),
    b"Followup-To": b"poster", b"Injection-Date": date(WALL - 60), b"Lines": b"1",
    b"Organization": b"O", b"Summary": b"S", b"User-Agent": b"UA/1.0", b"Sender": b"a@b.example",
    b"Reply-To": b"a@b.example", b"To": b"a@b.example", b"Cc": b"a@b.example",
    b"Bcc": b"a@b.example", b"In-Reply-To": b"<c@d.example>", b"References": b"<c@d.example>",
    b"Cancel-Lock": b"sha256:s/pmK/3grrz++29ce2/mQydzJuc7iqHn1nqcJiQTPMc=",
    b"Cancel-Key": b"sha256:qv1VXHYiCGjkX/N1nhfYKcAeUn8bCVhrWhoKuBSnpMA=",
    b"Keywords": b"a, b", b"MIME-Version": b"1.0", b"Content-Type": b"text/plain; charset=us-ascii",
    b"Content-Transfer-Encoding": b"7bit",
}


def field(name: bytes) -> bytes:
    return name + b": " + VALUE[name]


def padded(size: int) -> bytes:
    """The minimal proto-article with X-Pad fields that bring its header section to `size`
    octets, CRLFs counted, no line longer than 998."""
    base = sum(len(f) + 2 for f in MINIMAL)
    pads: list[bytes] = []
    left = size - base
    while left:
        n = min(left, 998 + 2)
        if 0 < left - n < 10:  # leave room for one more field
            n = left - 10
        pads.append(b"X-Pad: " + b"x" * (n - 2 - 7))
        left -= n
    return plus(*pads)


def msg_id(length: int) -> bytes:
    return b"<" + b"a" * (length - 12) + b"@b.example>"


def path_with_first_line(length: int) -> bytes:
    """A Path field whose first line, after the server writes its identity and `!.POSTED!` before
    it, is `length` octets long."""
    head = len(b"Path: " + IDENTITY + b"!.POSTED!")
    rest = b"!not-for-mail"
    return b"Path: " + b"a" * (length - head - len(rest)) + rest


# Contexts at the bounds `Context.ok` sets, and one past each, which both have to refuse to run.
LONGEST = b".".join([b"a" * 63] * 3) + b".bb" * 3
BOUNDS = [replace(BASE, identity=b"n"), replace(BASE, identity=LONGEST),
          replace(BASE, seq=2**64 - 1, run=2**64 - 1, conn=2**64 - 1),
          replace(BASE, random=b"0123456789abcdef"), replace(BASE, groups=()),
          replace(BASE, groups=tuple(b"g%02d." % k + b"x" * 60 for k in range(64)))]
PAST_BOUNDS = [replace(BASE, identity=LONGEST + b"b"), replace(BASE, identity=b"a..b"),
               replace(BASE, seq=2**64), replace(BASE, run=2**64), replace(BASE, conn=2**64),
               replace(BASE, random=b""), replace(BASE, random=b"0123456789abcdef0"),
               replace(BASE, random=b"5F3A"),
               replace(BASE, groups=tuple(b"g%02d.x" % k for k in range(65))),
               replace(BASE, groups=(b"g." + b"x" * 63,)), replace(BASE, groups=(b"example.a",)),
               replace(BASE, groups=(b"a.b", b"a.b")), replace(BASE, groups=(b"a..b",))]


def targeted() -> list[Case]:
    """For each rule, cases on both sides of it, each with the answer it has to get."""
    c = BASE
    cases: list[Case] = [
        (c, b"", refused("no-header")),
        (c, b"\r\nbody\r\n", refused("no-header")),
        (c, b"From: a@b.example\r\n", refused("no-separator")),
        (c, b"From: a@b.example\r\nNewsgroups: local.test\r\nSubject: hi", refused("no-separator")),
        (c, padded(65536), ACCEPTED),
        (c, padded(65537), refused("header-too-long")),
        (c, plus(b"Summary: " + b"x" * 989), ACCEPTED),
        (c, plus(b"Summary: " + b"x" * 990), refused("line-too-long")),
        (c, article(b" continued", *MINIMAL), refused("malformed")),
        (c, plus(b"NoColon"), refused("malformed")),
        (c, plus(b"Name : x"), refused("malformed")),
        (c, plus(b": x"), refused("malformed")),
        (c, plus(b"N\xe4me: x"), refused("malformed")),
    ]
    rules = [("injected", ["Injection-Info", "Xref"]),
             ("traced", ["NNTP-Posting-Host", "NNTP-Posting-Date", "X-Trace", "X-Complaints-To"]),
             ("deprecated", ["Date-Received", "Posting-Version", "Relay-Version", "Also-Control",
                             "Article-Names", "Article-Updates", "See-Also",
                             "Disposition-Notification-To"]),
             ("not-offered", ["Control", "Supersedes", "Approved"])]
    for reason, names in rules:
        for n in names:
            for written in (n.encode(), n.lower().encode()):
                cases.append((c, plus(written + b": x"), refused(reason, written)))
    cases += [
        (c, without(b"Subject", b"Subject:"), refused("blank-line", b"Subject")),
        (c, without(b"Subject", b"Subject: "), refused("blank-line", b"Subject")),
        (c, without(b"Subject", b"Subject: \t "), refused("blank-line", b"Subject")),
        (c, without(b"From", b"From: a ", b" ", b" <a@b.example>"), refused("blank-line", b"From")),
        (c, without(b"From", b"From: a ", b" <a@b.example>"), ACCEPTED),
        (c, without(b"Subject", b"Subject:hi"), refused("bad-field", b"Subject")),
        (c, plus(b"X-Foo:bar"), refused("bad-field", b"X-Foo")),
        (c, without(b"Subject", b"Subject: caf\xc3\xa9"), refused("bad-field", b"Subject")),
        (c, plus(b"Message-ID: <a b@c.example>"), refused("bad-field", b"Message-ID")),
        (c, without(b"Newsgroups", b"Newsgroups: local.test,,local.other"),
         refused("bad-field", b"Newsgroups")),
        (c, plus(b"Comments: one", b"Comments: two", b"Content-ID: <a@b>", b"Content-ID: <c@d>"),
         ACCEPTED),
        (c, plus(b"In-Reply-To: not an id"), refused("bad-field", b"In-Reply-To")),
        (c, plus(b"In-Reply-To: <a@b.example> (a comment)<c@d.example>"), ACCEPTED),
        (c, plus(b"In-Reply-To:<a@b.example>"), refused("bad-field", b"In-Reply-To")),
        (c, plus(b"Resent-Message-ID: <a b@c.example>"), refused("bad-field", b"Resent-Message-ID")),
        (c, plus(b"Resent-Message-ID:  <a@b.example> "), ACCEPTED),
    ]
    for name, value in VALUE.items():
        if name in (b"From", b"Newsgroups", b"Subject"):
            cases.append((c, plus(field(name)), refused("repeated", name)))
        else:
            cases.append((c, plus(field(name), field(name)), refused("repeated", name)))
            cases.append((c, plus(name.upper() + b": " + value, field(name)), refused("repeated", name)))
    for name in (b"From", b"Newsgroups", b"Subject"):
        cases.append((c, without(name), refused("missing", name)))
    cases += [
        (c, plus(b"Path: a.example!.POSTED!not-for-mail"), refused("posted")),
        (c, plus(b"Path: a.example!.posted.b.example!not-for-mail"), refused("posted")),
        (c, plus(b"Path: a.example!.POSTED.192.0.2.1!x!not-for-mail"), refused("posted")),
        (c, plus(b"Path: a.example!.SEEN.b.example!not-for-mail"), ACCEPTED),
        (c, plus(b"Path: posted.example!POSTED!not-for-mail"), ACCEPTED),
        (c, plus(b"Message-ID: " + msg_id(250)), ACCEPTED),
        (c, plus(b"Message-ID: " + msg_id(251)), refused("long-message-id", b"Message-ID")),
        (c, plus(b"References: <c@d.example> " + msg_id(250)), ACCEPTED),
        (c, plus(b"References: <c@d.example> " + msg_id(251)), refused("long-message-id", b"References")),
        (c, plus(b"References: <c@d.example> (<" + b"x" * 300 + b">)"), ACCEPTED),
        (c, plus(b"In-Reply-To: <c@d.example> " + msg_id(250)), ACCEPTED),
        (c, plus(b"In-Reply-To: <c@d.example> " + msg_id(251)), refused("long-message-id", b"In-Reply-To")),
        (c, plus(b"Resent-Message-ID: " + msg_id(251)), refused("long-message-id", b"Resent-Message-ID")),
        (c, plus(b"message-id: " + msg_id(251)), refused("long-message-id", b"message-id")),
        (c, without(b"From", b"From: a@b.example, c@d.example"), refused("no-sender")),
        (c, without(b"From", b"From: a@b.example, c@d.example", b"Sender: a@b.example"), ACCEPTED),
        (c, without(b"From", b'From: "a, b" <a@b.example>'), ACCEPTED),
        (c, plus(b"Distribution: all"), refused("distribution-all")),
        (c, plus(b"Distribution: local, ALL"), refused("distribution-all")),
        (c, plus(b"Distribution: world,allx"), ACCEPTED),
    ]
    # Within a day of the wall clock, and, for the fields no window applies to, anywhere.
    near = [date(WALL - 60), date(WALL - 60, weekday=False), date(WALL - 60, zone="GMT"),
            b"Mon, 21 Sep 2026 15:12:20 +0100", b"Sun, 20 Sep 2026 23:59:60 +0000",
            b"mon, 21 sep 2026 14:12:20 gmt", date(WALL - 60) + b" (a comment)",
            b"Mon,21 Sep 2026 14:12:20 +0000", b"Mon,\r\n 21 Sep 2026 14:12:20 +0000",
            b"21 Sep 2026 14:12:20GMT"]
    far = [b"Thu, 29 Feb 2024 12:00:00 +0000 (leap)", b"Tue, 29 Feb 2000 12:00:00 +0000",
           b"Sat, 01 Jan 10000 00:00:00 +0000"]
    bad = [b"Sat, 29 Feb 2025 12:00:00 +0000", b"Mon, 29 Feb 2100 12:00:00 +0000",
           b"Fri, 31 Apr 2026 12:00:00 +0000", b"Sun, 21 Sep 2026 14:12:20 +0000",
           b"Mon, 21 Sep 2026 24:00:00 +0000", b"Mon, 21 Sep 2026 14:60:00 +0000",
           b"Mon, 21 Sep 2026 14:12:61 +0000", b"Mon, 21 Sep 2026 14:12:20 +0060",
           b"Mon, 21 Sep 1899 14:12:20 +0000"]
    for name in (b"Date", b"Injection-Date", b"Expires", b"Resent-Date"):
        for v in near + ([] if name in (b"Date", b"Injection-Date") else far):
            cases.append((c, plus(name + b": " + v), ACCEPTED))
        for v in bad:
            cases.append((c, plus(name + b": " + v), refused("bad-date", name)))
    received = b"Received: from a.example (a;b \"c) by [192.0.2.1] (x[;]y); "
    for v in near[:2] + far:
        cases.append((c, plus(received + v), ACCEPTED))
    for v in bad:
        cases.append((c, plus(received + v), refused("bad-date", b"Received")))
    cases.append((c, plus(b'Received: from "a;b" by b.example; ' + bad[0]), refused("bad-date", b"Received")))
    for name in (b"Date", b"Injection-Date"):
        cases += [
            (c, plus(name + b": " + date(WALL + AHEAD)), ACCEPTED),
            (c, plus(name + b": " + date(WALL + AHEAD + 1)), refused("date-ahead", name)),
            (c, plus(name + b": " + date(WALL - PAST)), ACCEPTED),
            (c, plus(name + b": " + date(WALL - PAST - 1)), refused("date-past", name)),
            (c, plus(name + b": " + date(WALL + AHEAD + 3600, zone="+0100")), ACCEPTED),
            (c, plus(name + b": " + date(WALL + AHEAD + 1 - 3600, zone="-0100")),
             refused("date-ahead", name)),
        ]
    many = b",".join(b"a." + bytes([97 + k]) for k in range(15))
    cases += [
        (c, without(b"Newsgroups", b"Newsgroups: local.test," + many), ACCEPTED),
        (c, without(b"Newsgroups", b"Newsgroups: local.test," + many + b",a.z"), refused("too-many-groups")),
        (c, without(b"Newsgroups", b"Newsgroups: alt.a,alt.b"), refused("no-known-group")),
        (c, without(b"Newsgroups", b"Newsgroups: alt.a,local.other,local.test,local.other"), ACCEPTED),
        (c, without(b"Newsgroups", b"Newsgroups: local.test,\r\n local.other"), ACCEPTED),
    ]
    for g in (b"example", b"example.x", b"poster", b"to.x", b"to", b"control", b"control.cancel",
              b"x.all", b"all", b"x.ctl.y", b"junk"):
        cases.append((c, without(b"Newsgroups", b"Newsgroups: local.test," + g), refused("reserved-group")))
    for g in (b"examples.x", b"tox.y", b"junk.x", b"x.allx", b"Example.x"):
        cases.append((c, without(b"Newsgroups", b"Newsgroups: local.test," + g), ACCEPTED))
    for has_id in (False, True):
        for has_date in (False, True):
            for has_injected in (False, True):
                extra = ([field(b"Message-ID")] if has_id else []) + \
                        ([field(b"Date")] if has_date else []) + \
                        ([field(b"Injection-Date")] if has_injected else [])
                cases.append((c, plus(*extra), ACCEPTED))
    head = len(b"Path: " + IDENTITY + b"!.POSTED!")
    cases += [(c, plus(path_with_first_line(n)), ACCEPTED) for n in (997, 998, 999, 1000)]
    # A folded Path: the server's identity goes before its first line, the rest stays.
    cases.append((c, plus(path_with_first_line(head + 30), b" !more!not-for-mail"), ACCEPTED))
    for ctx in BOUNDS:
        cases.append((ctx, plus(), None))
    return cases


def date_forms(rng: random.Random) -> list[Case]:
    """Dates written each way the grammar lets them be, near the wall clock: with the day of the
    week or without, white space after its comma or none, folded or not, one digit for the day or
    two, seconds or none, zones either side and GMT, a comment after; each has to be accepted in
    Date and Injection-Date. And each made to name another day of the week, which has to be
    refused."""
    cases: list[Case] = []

    def ws() -> str:
        return rng.choice([" ", "  ", "\t", "\r\n ", "\r\n\t"])

    for k in range(400):
        when = WALL + rng.randrange(-2 * DAY, DAY)
        minutes = rng.choice([0, 0, 60, -210, 330, 1439, -1439])
        t = time.gmtime(when + minutes * 60)
        zone = ("GMT" if minutes == 0 and rng.random() < 0.5 else
                f"{'+' if minutes >= 0 else '-'}{abs(minutes) // 60:02d}{abs(minutes) % 60:02d}")
        day = f"{t.tm_mday}" if rng.random() < 0.5 else f"{t.tm_mday:02d}"
        seconds = f":{t.tm_sec:02d}" if t.tm_sec or rng.random() < 0.5 else ""
        tail = rng.choice(["", " (UTC)", " (a (nested) comment)"])
        rest = (f"{day}{ws()}{MONTHS[t.tm_mon - 1]}{ws()}{t.tm_year}{ws()}{t.tm_hour:02d}:"
                f"{t.tm_min:02d}{seconds}{ws() if zone != 'GMT' or rng.random() < 0.5 else ''}{zone}{tail}")
        after = rng.choice(["", " ", "\r\n "])
        name = b"Date" if k % 2 else b"Injection-Date"
        if rng.random() < 0.8:
            right = f"{WEEK[t.tm_wday]},{after}{rest}"
            wrong = f"{WEEK[(t.tm_wday + 1) % 7]},{after}{rest}"
            cases.append((BASE, plus(name + b": " + wrong.encode()), refused("bad-date", name)))
        else:
            right = rest
        cases.append((BASE, plus(name + b": " + right.encode()), ACCEPTED))
    return cases


def generated(rng: random.Random) -> list[Case]:
    """Articles built around the fields the grammar derives for each field's rule, and each
    changed at a few places."""
    rules = C.grammar()
    d = C.Deriver(rules, rng)
    c = BASE
    cases: list[Case] = []
    for name, (rule, _) in [*G.FIELDS.items(), ("X-Other", G.OPTIONAL)]:
        for _ in range(DERIVED):
            derived = d.derive(rules[rule], 0, {})
            fields = [f for f in MINIMAL if not f.lower().startswith(name.lower().encode() + b":")]
            a = derived + article(*fields)
            cases.append((c, a, None))
            cases += [(c, m, None) for m in C.changed(a, rng)]
    return cases


def printed() -> list[Case]:
    """The header fields the RFCs print, each in an article."""
    c = BASE
    cases: list[Case] = []
    for number in (5322, 5537, 8315):
        for _, data in C.printed(number):
            name = data.split(b":")[0].lower()
            fields = [f for f in MINIMAL if not f.lower().startswith(name + b":")]
            cases.append((c, data + article(*fields), None))
    return cases


def corpus_files() -> dict[str, bytes]:
    """INN's test articles, each held to the digest docs/provenance.json records for it, as is
    INN's licence beside them."""
    entries = json.loads(PROVENANCE.read_text())["files"]
    recorded = {Path(e["destination"]).name: e["source_sha256"] for e in entries
                if e["destination"].startswith("tests/corpus/inn-articles/")}
    files = {p.name: p.read_bytes() for p in sorted(CORPUS.iterdir())}
    if set(files) != set(recorded):
        raise LaneError(f"the corpus is not what docs/provenance.json records: {sorted(set(files) ^ set(recorded))}")
    for name, data in files.items():
        if hashlib.sha256(data).hexdigest() != recorded[name]:
            raise LaneError(f"tests/corpus/inn-articles/{name} is not the file recorded")
    del files["LICENSE"]
    return files


def as_posted(name: str, data: bytes) -> bytes:
    """An INN test article as a POST's block framer would give it: a native one with CRLF line
    ends, a wire one without its terminator and with its leading dots unstuffed."""
    if not name.startswith("wire-"):
        return data.replace(b"\n", b"\r\n")
    lines = data.split(b"\r\n")
    if lines[-2:] == [b".", b""]:
        lines = [*lines[:-2], b""]
    return b"\r\n".join(ln[1:] if ln.startswith(b"..") else ln for ln in lines)


def as_proto(posted: bytes) -> bytes:
    """An article made a proto-article: without the fields an injecting agent adds (Path, Xref),
    and posted to the groups the lane's server carries in place of INN's example groups."""
    end = posted.find(b"\r\n\r\n")
    head, rest = (posted[:end + 2], posted[end + 2:]) if end >= 0 else (posted, b"")
    kept, dropping = [], False
    for ln in head.split(b"\r\n")[:-1]:
        if ln[:1] in (b" ", b"\t"):
            if not dropping:
                kept.append(ln)
            continue
        dropping = ln.lower().startswith((b"path:", b"xref:"))
        if not dropping:
            kept.append(ln.replace(b"example.test", b"local.test").replace(b"example.config", b"local.other"))
    return b"".join(ln + b"\r\n" for ln in kept) + rest


# What each of INN's test articles gets, as INN keeps it and as a proto-article, at a wall clock
# an hour after its own Date. INN's parser tests take them as a relaying agent would, with a limit
# of 8,192 octets; an injecting agent is stricter: every article INN kept has an Xref, a header
# line may not pass 998 octets, and a line of a field body may not be white space alone. A NUL in
# a body is the block framer's to refuse, before these checks.
CORPUS_EXPECTED = {
    "1": (refused("injected", b"Xref"), ACCEPTED),
    "2": (refused("injected", b"Xref"), ACCEPTED),
    "3": (refused("injected", b"Xref"), ACCEPTED),
    "4": (refused("blank-line", b"Subject"), refused("blank-line", b"Subject")),
    "5": (refused("line-too-long"), refused("line-too-long")),
    "6": (refused("injected", b"Xref"), ACCEPTED),
    "7": (refused("missing", b"From"), refused("missing", b"From")),
    "bad-empty": (refused("no-header"), refused("no-header")),
    "bad-hdr-empty": (refused("blank-line", b"From"), refused("blank-line", b"From")),
    "bad-hdr-nospc": (refused("bad-field", b"Test"), refused("bad-field", b"Test")),
    "bad-hdr-space": (refused("malformed"), refused("malformed")),
    "bad-hdr-trunc": (refused("blank-line", b"Test"), refused("blank-line", b"Test")),
    "bad-long-cont": (refused("line-too-long"), refused("line-too-long")),
    "bad-long-hdr": (refused("line-too-long"), refused("line-too-long")),
    "bad-msgid": (refused("bad-field", b"Subject"), refused("bad-field", b"Subject")),
    "bad-no-body": (refused("no-separator"), refused("no-separator")),
    "bad-no-header": (refused("no-header"), refused("no-header")),
    "bad-nul-body": (refused("injected", b"Xref"), ACCEPTED),
    "bad-nul-header": (refused("bad-field", b"Subject"), refused("bad-field", b"Subject")),
    "bad-subj": (refused("injected", b"Xref"), refused("missing", b"Subject")),
    "wire-7": (refused("missing", b"From"), refused("missing", b"From")),
    "wire-no-body": (refused("no-separator"), refused("no-separator")),
    "wire-strange": (refused("bad-field", b"Subject"), refused("bad-field", b"Subject")),
    "wire-truncated": (refused("no-separator"), refused("no-separator")),
    "xref": (refused("injected", b"Xref"), ACCEPTED),
}


def date_of(posted: bytes) -> int | None:
    """The time an article's Date says, read by the standard library, if it has one it can read."""
    for ln in posted.split(b"\r\n"):
        if ln.lower().startswith(b"date:"):
            try:
                return int(email.utils.parsedate_to_datetime(ln[5:].decode("latin-1")).timestamp())
            except (ValueError, TypeError):
                return None
    return None


def corpus() -> list[Case]:
    files = corpus_files()
    if set(files) != set(CORPUS_EXPECTED):
        raise LaneError(f"no expected answer for {sorted(set(files) ^ set(CORPUS_EXPECTED))}")
    cases: list[Case] = []
    for name, data in files.items():
        raw_expected, proto_expected = CORPUS_EXPECTED[name]
        posted = as_posted(name, data)
        when = date_of(posted)
        c = replace(BASE, wall=WALL if when is None else when + 3600)
        cases.append((c, posted, raw_expected))
        cases.append((c, as_proto(posted), proto_expected))
    return cases


def dates() -> list[str]:
    """The date the server writes for a wall clock at every day from 1970 to 2400, at a time of
    day that moves from one day to the next, and that date read back."""
    walls = [day * DAY + (day * 7919) % DAY for day in range(LAST_DAY + 1)]
    return [f"format {w}" for w in walls]


def check() -> Report:
    OUT.mkdir(parents=True, exist_ok=True)
    python = str(lanes.pinned_python(REQUIREMENTS))
    rng = random.Random(SEED)  # noqa: S311 -- a fixed seed, so that every run draws the same cases
    steps, mark = {}, time.monotonic()
    written = targeted()
    inn = corpus()
    cases = written + date_forms(rng) + inn + printed() + generated(rng)
    lines = [line(c, a) for c, a, _ in cases]
    formats = dates()
    steps["cases"], mark = round(time.monotonic() - mark, 1), time.monotonic()
    model_command = [str(lanes.DN_COMPILER), "article-model"]
    model = run(model_command, lines + formats)
    steps["model"], mark = round(time.monotonic() - mark, 1), time.monotonic()
    reference = run([python, str(REFERENCE)], lines + formats)
    steps["reference"], mark = round(time.monotonic() - mark, 1), time.monotonic()
    for asked, a, b in zip(lines + formats, model, reference, strict=True):
        if a != b:
            raise LaneError(f"{asked[:300]}: the model answers {a[:300]}, the reference {b[:300]}")
    for (_, posted, want), said in zip(cases, model[:len(lines)], strict=True):
        if want is not None and not (said == want or (want == ACCEPTED and said.startswith("accepted "))):
            raise LaneError(f"{posted[:300]!r}: answered {said[:200]}, not {want}")
    for ctx in PAST_BOUNDS:
        asked = line(ctx, plus()) + "\n"
        for command in (model_command, [python, str(REFERENCE)]):
            done = subprocess.run(command, input=asked, capture_output=True, text=True, timeout=600,
                                  check=False)
            if done.returncode == 0:
                raise LaneError(f"{command[-1]} ran a context past its bounds: {asked[:200]}")
    written_dates = model[len(lines):]
    reads = [f"parse {d}" for d in written_dates]
    read_model = run(model_command, reads)
    read_reference = run([python, str(REFERENCE)], reads)
    for asked, a, b, w in zip(reads, read_model, read_reference, formats, strict=True):
        if not a == b == w.split()[1]:
            raise LaneError(f"{asked}: read back as {a} by the model and {b} by the reference, "
                            f"not {w.split()[1]}")
    steps["dates"], mark = round(time.monotonic() - mark, 1), time.monotonic()
    answers = [s.split()[0] if s.startswith("accepted") else s.split()[1] for s in model[:len(lines)]]
    unseen = [r for r in [*REASONS, "accepted"] if r not in answers]
    if unseen:
        raise LaneError(f"no case is answered {unseen}")
    caught = {}
    held = list(zip(lines, reference[:len(lines)], strict=True))
    for mutant in MUTANTS:
        differs = C.first_difference([*model_command, "--mutant", mutant], held)
        if differs is None:
            raise LaneError(f"the version {mutant} was not caught")
        shown = differs.split()[-1]
        caught[mutant] = repr((b"" if shown == "-" else bytes.fromhex(shown))[:100])
    steps["mutants"] = round(time.monotonic() - mark, 1)
    accepted = answers.count("accepted")
    lanes.require_quoted({"docs/baseline.md": [
        f"{len(cases):,} cases", f"{len(MUTANTS)} versions of the rules", f"{LAST_DAY + 1:,} days",
        f"{len(inn) // 2} of INN's test articles", f"{len(PAST_BOUNDS)} contexts past"]})
    return Report("checked", None, [REFERENCE, REQUIREMENTS], {
        "cases": len(cases), "accepted": accepted, "refused": len(cases) - accepted,
        "written_with_answers": sum(1 for _, _, w in written if w is not None),
        "corpus_articles": len(inn) // 2, "days": LAST_DAY + 1,
        "reasons_seen": {r: answers.count(r) for r in REASONS},
        "mutants_caught": caught, "seconds_by_step": steps})


def run(command: list[str], asked: list[str]) -> list[str]:
    """The answers `command` gives, a line each, from processes run at once, each given a
    share."""
    return C.answer_lines(command, asked, C.WORKERS)


def main() -> None:
    lanes.lane_main("ARTICLE", OUT, check)


if __name__ == "__main__":
    main()
