#!/usr/bin/env python3
# SPDX-License-Identifier: AGPL-3.0-or-later
"""The independent reference of the article lane: which proto-articles a POST accepts and what the
server adds, from RFC 5536, RFC 5537 §3.5 and decision 0005, written apart from
`DN.News.ArticleSpec` and answering the cases `dn-compiler article-model` answers, in the same
form. Header fields are held to the grammar of scripts/netnews.abnf through the `abnf` library;
dates are read and written with the standard library's calendar. Run by the Python of
scripts/requirements-tests.txt, which pins the library.
"""
from __future__ import annotations

import argparse
import calendar
from dataclasses import dataclass
import datetime
from pathlib import Path
import re
import subprocess
import sys

from abnf import ParseError, Rule

sys.path.insert(0, str(Path(__file__).resolve().parent))
import gen_abnf  # the path above is what makes it importable

HERE = Path(__file__).resolve().parent
HEADER_MAX, LINE_MAX, ID_MAX, GROUPS_MAX = 65536, 998, 250, 16
AHEAD, PAST = 24 * 3600, 72 * 3600
INJECTED = {"injection-info", "xref"}
TRACED = {"nntp-posting-host", "nntp-posting-date", "x-trace", "x-complaints-to"}
DEPRECATED = {"date-received", "posting-version", "relay-version", "also-control", "article-names",
              "article-updates", "see-also", "disposition-notification-to"}
NOT_OFFERED = {"control", "supersedes", "approved"}
ONCE = {"date", "from", "message-id", "newsgroups", "path", "subject", "approved", "archive",
        "control", "distribution", "expires", "followup-to", "injection-date", "injection-info",
        "lines", "organization", "summary", "supersedes", "user-agent", "xref", "sender",
        "reply-to", "to", "cc", "bcc", "in-reply-to", "references", "cancel-lock", "cancel-key",
        "keywords", "mime-version", "content-type", "content-transfer-encoding"}
ID_FIELDS = {"message-id", "references", "in-reply-to", "resent-message-id"}
REQUIRED = ["From", "Newsgroups", "Subject"]
DATED = {"date", "injection-date", "expires", "resent-date"}
RULES = {field.lower(): rule for field, (rule, _) in gen_abnf.FIELDS.items()}
WS = b" \t\r\n"
MONTHS = ["jan", "feb", "mar", "apr", "may", "jun", "jul", "aug", "sep", "oct", "nov", "dec"]
DAYS = ["mon", "tue", "wed", "thu", "fri", "sat", "sun"]  # the order of calendar.weekday
DATE = re.compile(rb"^\s*(?:([A-Za-z]{3}),)?\s*(\d{1,2})\s+([A-Za-z]{3})\s+(\d{4,})\s+"
                  rb"(\d\d):(\d\d)(?::(\d\d))?\s*([+-]\d{4}|[Gg][Mm][Tt])\s*(?:\(.*)?$", re.DOTALL)
FIELD_START = re.compile(rb"^([\x21-\x39\x3b-\x7e]+):")


class Netnews(Rule):
    """The rules of scripts/netnews.abnf."""


@dataclass(frozen=True)
class Context:
    wall: int
    seq: int
    run: int
    conn: int
    identity: bytes
    random: bytes
    groups: list[bytes]


class Refused(Exception):
    def __init__(self, reason: str, name: bytes = b"") -> None:
        super().__init__(reason)
        self.reason, self.name = reason, name


class Grammar:
    """The grammar's answers, each case asked once. A case the Rust backend stops on for its depth
    is decided by scripts/abnf_ref.py's pure-Python backend."""

    def __init__(self) -> None:
        self.said: dict[tuple[str, bytes], bool] = {}
        self.text = HERE / "netnews.abnf"

    def __call__(self, rule: str, data: bytes) -> bool:
        key = (rule, data)
        if key not in self.said:
            try:
                Netnews(rule).parse_all(data.decode("latin-1"))
                self.said[key] = True
            except ParseError as e:
                if isinstance(e.__cause__, RecursionError):
                    self.said[key] = self.deep(rule, data)
                else:
                    self.said[key] = False
        return self.said[key]

    def deep(self, rule: str, data: bytes) -> bool:
        done = subprocess.run([sys.executable, str(HERE / "abnf_ref.py"), "--grammar", str(self.text)],
                              input=f"{rule} {data.hex() or '-'}\n", capture_output=True, text=True,
                              check=True)
        return done.stdout.strip() == "1"


grammar = Grammar()


def epoch(year: int, month: int, day: int, hour: int, minute: int, second: int) -> int:
    """Seconds since 1970-01-01T00:00:00Z; a year past the calendar module's reach is moved by
    whole cycles of 400 years, which repeat the calendar."""
    cycles, year = divmod(year - 2000, 400)
    return (calendar.timegm((2000 + year, month, day, hour, minute, 0)) + second
            + cycles * 146097 * 86400)


def date_value(value: bytes) -> int | None:
    """What a date-time says, in seconds, or None if it says no date (RFC 5322 §3.3)."""
    m = DATE.match(value)
    if m is None:
        return None
    weekday, day, month, year, hour, minute, second, zone = m.groups()
    d, y, h, mi, s = int(day), int(year), int(hour), int(minute), int(second or b"0")
    if month.lower().decode() not in MONTHS:
        return None
    mo = MONTHS.index(month.lower().decode()) + 1
    if y < 1900 or not 1 <= d <= calendar.monthrange(2000 + (y - 2000) % 400, mo)[1] \
            or h > 23 or mi > 59 or s > 60:
        return None
    if zone.lower() == b"gmt":
        offset = 0
    else:
        zh, zm = int(zone[1:3]), int(zone[3:5])
        if zm > 59:
            return None
        offset = (zh * 3600 + zm * 60) * (1 if zone[:1] == b"+" else -1)
    if weekday is not None:
        if weekday.lower().decode() not in DAYS:
            return None
        if DAYS.index(weekday.lower().decode()) != calendar.weekday(2000 + (y - 2000) % 400, mo, d):
            return None
    return epoch(y, mo, d, h, mi, s) - offset


def format_date(wall: int) -> bytes:
    """The date the server writes, in English whatever the locale."""
    at = datetime.datetime.fromtimestamp(wall, datetime.UTC)
    return (f"{DAYS[at.weekday()].title()}, {at.day:02d} {MONTHS[at.month - 1].title()} {at.year} "
            f"{at.hour:02d}:{at.minute:02d}:{at.second:02d} +0000").encode()


def message_ids(value: bytes) -> list[bytes]:
    """The message identifiers of a body where they stand among comments and white space."""
    found, depth, k = [], 0, 0
    while k < len(value):
        c = value[k:k + 1]
        if depth:
            if c == b"\\":
                k += 1
            depth += {b"(": 1, b")": -1}.get(c, 0)
        elif c == b"(":
            depth = 1
        elif c == b"<":
            end = value.find(b">", k)
            if end < 0:
                break
            found.append(value[k:end + 1])
            k = end
        k += 1
    return found


def received_date(value: bytes) -> bytes | None:
    """The date-time of a Received field's body: what follows its rightmost `;` that the grammar
    reads a date-time after. What follows a `;` in the date-time's own comment closes that comment,
    which no date-time does; what follows a `;` before the field's own holds that `;` outside any
    comment, which no date-time does either."""
    for k in range(len(value) - 1, -1, -1):
        if value[k:k + 1] == b";" and grammar("date-time", value[k + 1:]):
            return value[k + 1:]
    return None


def squeezed(value: bytes) -> bytes:
    return bytes(b for b in value if b not in WS)


def reserved(group: bytes) -> bool:
    parts = group.split(b".")
    return (parts[0] in (b"example", b"to", b"control") or group in (b"poster", b"junk")
            or any(p in (b"all", b"ctl") for p in parts))


class Field:
    def __init__(self, name: bytes, lines: list[bytes]) -> None:
        self.name, self.lines = name, lines

    @property
    def key(self) -> str:
        return self.name.decode("latin-1").lower()

    @property
    def text(self) -> bytes:
        return b"".join(line + b"\r\n" for line in self.lines)

    @property
    def value(self) -> bytes:
        return b"\r\n".join([self.lines[0][len(self.name) + 1:], *self.lines[1:]])


def split(article: bytes) -> list[Field]:
    if not article or article.startswith(b"\r\n"):
        raise Refused("no-header")
    end = article.find(b"\r\n\r\n")
    if end < 0:
        raise Refused("no-separator")
    head = article[:end + 2]
    if len(head) > HEADER_MAX:
        raise Refused("header-too-long")
    lines = head.split(b"\r\n")[:-1]
    if any(len(line) > LINE_MAX for line in lines):
        raise Refused("line-too-long")
    fields: list[Field] = []
    for line in lines:
        if line[:1] in (b" ", b"\t"):
            if not fields:
                raise Refused("malformed")
            fields[-1].lines.append(line)
            continue
        m = FIELD_START.match(line)
        if m is None:
            raise Refused("malformed")
        fields.append(Field(m.group(1), [line]))
    return fields


def check_field(f: Field) -> None:
    for names, reason in ((INJECTED, "injected"), (TRACED, "traced"), (DEPRECATED, "deprecated"),
                          (NOT_OFFERED, "not-offered")):
        if f.key in names:
            raise Refused(reason, f.name)
    if any(not line[len(f.name) + 1 if k == 0 else 0:].strip(b" \t") for k, line in enumerate(f.lines)):
        raise Refused("blank-line", f.name)
    if not grammar(RULES.get(f.key, gen_abnf.OPTIONAL[0]), f.text):
        raise Refused("bad-field", f.name)


def check_article(ctx: Context, fields: list[Field]) -> None:
    seen: set[str] = set()
    for f in fields:
        if f.key in ONCE and f.key in seen:
            raise Refused("repeated", f.name)
        seen.add(f.key)
    by = {}
    for f in reversed(fields):
        by[f.key] = f
    for name in REQUIRED:
        if name.lower() not in by:
            raise Refused("missing", name.encode())
    if "path" in by:
        for element in squeezed(by["path"].value).split(b"!"):
            if element[:1] == b"." and element[1:].split(b".")[0].upper() == b"POSTED":
                raise Refused("posted")
    for f in fields:
        if f.key in ID_FIELDS and any(len(i) > ID_MAX for i in message_ids(f.value)):
            raise Refused("long-message-id", f.name)
    if "sender" not in by and not grammar("mailbox", by["from"].value):
        raise Refused("no-sender")
    if "distribution" in by and any(d.lower() == b"all" for d in squeezed(by["distribution"].value).split(b",")):
        raise Refused("distribution-all")
    for f in fields:
        if f.key in DATED or f.key == "received":
            dated = f.value if f.key in DATED else received_date(f.value)
            if dated is None or date_value(dated) is None:
                raise Refused("bad-date", f.name)
    for name in ("Date", "Injection-Date"):
        when = date_value(by[name.lower()].value) if name.lower() in by else None
        if when is not None and when - ctx.wall > AHEAD:
            raise Refused("date-ahead", name.encode())
        if when is not None and ctx.wall - when > PAST:
            raise Refused("date-past", name.encode())
    groups = [g for g in squeezed(by["newsgroups"].value).split(b",") if g]
    if len(groups) > GROUPS_MAX:
        raise Refused("too-many-groups")
    if any(reserved(g) for g in groups):
        raise Refused("reserved-group")
    if not any(g in ctx.groups for g in groups):
        raise Refused("no-known-group")


def path_field(ctx: Context, old: Field | None) -> bytes:
    head = b"Path: " + ctx.identity + b"!.POSTED"
    if old is None:
        return head + b"!not-for-mail\r\n"
    first = old.lines[0][len(old.name) + 1:].lstrip(b" \t")
    joined = head + b"!" + first
    lead = [joined] if len(joined) <= LINE_MAX else [head, b" !" + first]
    return b"".join(line + b"\r\n" for line in [*lead, *old.lines[1:]])


def accept(ctx: Context, fields: list[Field]) -> tuple[bytes, bytes, list[bytes]]:
    by = {f.key: f for f in reversed(fields)}
    new_id, new_date = "message-id" not in by, "date" not in by
    msg_id = (b"<%d." % ctx.seq + ctx.random + b"@" + ctx.identity + b">" if new_id
              else message_ids(by["message-id"].value)[0])
    out = [path_field(ctx, by.get("path"))]
    out += [f.text for f in fields if f.key != "path"]
    if new_id:
        out.append(b"Message-ID: " + msg_id + b"\r\n")
    if new_date:
        out.append(b"Date: " + format_date(ctx.wall) + b"\r\n")
    out.append(b"Injection-Info: " + ctx.identity + b"; logging-data=%d.%d\r\n" % (ctx.run, ctx.conn))
    if "injection-date" not in by and (new_id or new_date):
        out.append(b"Injection-Date: " + format_date(ctx.wall) + b"\r\n")
    groups: list[bytes] = []
    for g in squeezed(by["newsgroups"].value).split(b","):
        if g in ctx.groups and g not in groups:
            groups.append(g)
    return b"".join(out), msg_id, groups


def check(ctx: Context, article: bytes) -> str:
    try:
        fields = split(article)
        for f in fields:
            check_field(f)
        check_article(ctx, fields)
    except Refused as r:
        return f"refused {r.reason} {r.name.hex() or '-'}"
    header, msg_id, groups = accept(ctx, fields)
    return f"accepted {header.hex()} {msg_id.hex()} {','.join(g.hex() for g in groups) or '-'}"


def context_fits(ctx: Context) -> bool:
    groups = ctx.groups
    return (grammar("path-identity", ctx.identity) and len(ctx.identity) <= 200
            and 1 <= len(ctx.random) <= 16 and re.fullmatch(rb"[0-9a-f]+", ctx.random) is not None
            and max(ctx.seq, ctx.run, ctx.conn) < 2**64
            and len(groups) <= 64 and len(set(groups)) == len(groups)
            and all(len(g) <= 64 and not reserved(g) and grammar("newsgroup-name", g) for g in groups))


def unhex(s: str) -> bytes:
    return b"" if s == "-" else bytes.fromhex(s)


def answer(line: str) -> str:
    words = line.split()
    match words:
        case ["check", wall, seq, run, conn, identity, random, groups, article]:
            ctx = Context(int(wall), int(seq), int(run), int(conn), unhex(identity), unhex(random),
                          [] if groups == "-" else [unhex(g) for g in groups.split(",")])
            if not context_fits(ctx):
                sys.exit(f"the context does not fit: {line}")
            return check(ctx, unhex(article))
        case ["format", wall]:
            return format_date(int(wall)).hex()
        case ["parse", value]:
            when = date_value(unhex(value))
            return "-" if when is None else str(when)
    sys.exit(f"not a case: {line}")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    parser.add_argument("--grammar", type=Path, default=HERE / "netnews.abnf",
                        help="the grammar text the fields are held to")
    grammar.text = parser.parse_args().grammar
    Netnews.load_grammar(grammar.text.read_text(encoding="ascii"))
    sys.stdout.write("".join(answer(line) + "\n" for line in sys.stdin if line.strip()))


if __name__ == "__main__":
    main()
