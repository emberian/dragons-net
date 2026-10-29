# SPDX-License-Identifier: AGPL-3.0-or-later
"""What OVER and HDR give of an article (RFC 3977 §8) judged from outside, apart from
`DN.News.Overview`, for scripts/post_ref.py: from the article's file as the store keeps it, lines
ending in CRLF and a dot put before each line that starts with one, and its commit.

A field is a header line that does not start with SP or TAB and the lines after it that do,
unfolded; its name is what comes before the first colon, compared without regard to case, and the
first field of a name is the one taken. Its content follows the colon and the SP after it, the
first octet after the colon once the lines are joined (§8.5.2), each TAB, NUL, CR and LF made one
SP (§8.3.2). `:bytes` counts the article as ARTICLE sends it, Xref among it, without
the dots put before lines; `:lines` the lines after the empty line (§8.1). An overview line is the
number, Subject, From, Date, Message-ID and References, `:bytes`, `:lines` and Xref whole, TAB
between them; HDR's is the label, SP and the content, and XHDR leaves out an article whose field is
absent or empty, as INN does.
"""
from __future__ import annotations

import re

import store_ref as J

CRLF = b"\r\n"
FIELDS = (b"Subject", b"From", b"Date", b"Message-ID", b"References")
STATUS = {"over": b"224 Overview information follows\r\n", "hdr": b"225 Headers follow\r\n",
          "xhdr": b"221 Header follows\r\n"}


def fields(header: bytes) -> list[tuple[bytes, bytes]]:
    """The fields of a header section as stored, each its name and what follows the colon, its lines
    joined; a continued line before any field, and a field without a colon, belong to none."""
    found: list[list[bytes]] = []
    for raw in header.split(CRLF)[:-1]:
        line = raw[1:] if raw.startswith(b"..") else raw
        if line[:1] in (b" ", b"\t"):
            if found:
                found[-1].append(line)
        else:
            found.append([line])
    named = []
    for parts in found:
        name, colon, rest = b"".join(parts).partition(b":")
        if colon:
            named.append((name, rest))
    return named


def value(header: bytes, name: bytes) -> bytes | None:
    """The content of the first field named `name`, without regard to case, if there is one."""
    for n, rest in fields(header):
        if n.lower() == name.lower():
            return re.sub(rb"[\t\0\r\n]", b" ", rest[1:] if rest.startswith(b" ") else rest)
    return None


def counted(file: bytes, xref: bytes) -> int:
    """`:bytes`: the file and its Xref, less the dots put before lines."""
    return len(file) + len(xref) - sum(1 for line in file.split(CRLF)[:-1] if line.startswith(b"."))


def lines(file: bytes, header: int) -> int:
    """`:lines`: the lines after the header section and the empty line."""
    return file[header + 2:].count(CRLF)


def xref_whole(identity: bytes, groups: list[tuple[bytes, int]]) -> bytes:
    return b"Xref: " + identity + b"".join(b" %s:%d" % (name, n) for name, n in groups)


def overview_line(identity: bytes, commit: J.Commit, file: bytes, number: int, xref: bytes) -> bytes:
    header = file[:commit[3]]
    parts = [b"%d" % number, *(value(header, f) or b"" for f in FIELDS), b"%d" % counted(file, xref),
             b"%d" % lines(file, commit[3]), xref_whole(identity, commit[2])]
    return b"\t".join(parts) + CRLF


def field(identity: bytes, commit: J.Commit, file: bytes, xref: bytes, name: bytes) -> bytes | None:
    """HDR's content of field `name`: the metadata counted, Xref's what follows its name, else the
    header's."""
    lower = name.lower()
    if lower == b":bytes":
        return b"%d" % counted(file, xref)
    if lower == b":lines":
        return b"%d" % lines(file, commit[3])
    if lower == b"xref":
        return xref_whole(identity, commit[2])[len(b"Xref: "):]
    return value(file[:commit[3]], name)


def hdr_line(legacy: bool, label: bytes, content: bytes | None) -> bytes:
    if legacy and not content:
        return b""
    return label + b" " + (content or b"") + CRLF
