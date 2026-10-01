#!/usr/bin/env python3
# SPDX-License-Identifier: AGPL-3.0-or-later
"""The store's journal and the names of its files, held two ways. `DN.News.Journal`, run by
`dn-compiler journal-model`, and the independent reference scripts/store_ref.py have to give the
same answer, to the byte, on every case:

- SipHash-2-4 on the 64 vectors of the authors' reference implementation
  (tests/corpus/siphash/vectors.h) and on inputs drawn from a fixed seed, on which the lane's own
  SipHash has to agree too;
- the CRC-32C, which a commit gives of its article's file, of the examples RFC 7143 prints
  (appendix A.4), read from its text, of the check value catalogues of CRCs give, and of inputs
  drawn up to 4 MiB, which google-crc32c, a third implementation, has to give as well;
- commits on both sides of each bound a correct store keeps, commits drawn at random and starts,
  framed at their offset under a key, which the lane frames itself too;
- journals: commits and starts one after the other under keys drawn at random; each followed by
  every proper prefix of a frame, bare, filled to the frame's length with zeros and filled with
  junk; frames torn into parts of which a proper subset is kept, the rest zeros or junk, as LazyFS
  tears a write; zeros and junk on both sides of the format's frame and of the largest; a frame
  that does not check with one that does after it; every byte of a journal changed, with little or
  much after it; frames that check but hold no record, frames too long, frames without their end
  mark, frames tagged under another key or copied to another place; first frames that are not the
  format or only look like it, and formats twice; and journals drawn and damaged at random;
- the names the store gives, and names it does not.

Lines no case may be — a number with more than digits, hex in capitals or of an odd length, a key
not of sixteen octets, an offset or a sequence number past sixteen hexadecimal digits, a group list
ending in a comma, white space alone, a carriage return — both have to refuse.

What the theorems of `DN.News.Journal` say of a case, both have to answer: a journal of records
reads back as them and ends cleanly (`scan_encoded`); a frame cut short reads as a torn tail
where it starts, bare (`scan_torn`, `scan_torn_format`), filled with zeros (`scan_torn_zeros`,
`scan_torn_format_zeros`) or filled with junk not ending in the end mark (`scan_torn_fill`,
`scan_torn_format_fill`); a frame that does not check with a record after it is corruption
(`scan_damaged`); a name reads as what it names (`parseName_bytes`). So they have to answer what
the lane knows otherwise: the authors' tags and the RFC's CRCs, each record's frame as the lane
frames it, a changed or torn frame never read as a record, and why each frame is refused. Each
version of the rules of reading with one of them changed (`DN.News.Journal.Mutant`) has to answer
some case otherwise (docs/baseline.md, "Journal").
"""
from __future__ import annotations

from dataclasses import dataclass
import functools
import hashlib
import json
from pathlib import Path
import random
import re
import struct
import subprocess
import sys
import time

sys.path.insert(0, str(Path(__file__).resolve().parent))
import abnf_check as C  # the path above is what makes these importable
import lanes
from lanes import LaneError, Report

OUT = lanes.ROOT / "build/journal"
REFERENCE = lanes.ROOT / "scripts/store_ref.py"
REQUIREMENTS = lanes.ROOT / "scripts/requirements-tests.txt"
RFC = lanes.ROOT / "rfcs/rfc7143.txt"
SIP_VECTORS = lanes.ROOT / "tests/corpus/siphash/vectors.h"
PROVENANCE = lanes.ROOT / "docs/provenance.json"
SEED = 20261001
FORMAT, COMMIT, START = 1, 2, 3
TITLE = b"dragons-net journal"
MAGIC = TITLE + b"\x01"
END = 0xA5
HEADER = 4 + 8 + 1
MAX_PAYLOAD = 1376
MAX_FRAME = HEADER + MAX_PAYLOAD + 1
FIRST_FRAME = HEADER + len(MAGIC) + 16 + 1
START_FRAME = HEADER + 1
MASK = (1 << 64) - 1
# The key of the examples, and of the authors' vectors: the octets 00 to 0f.
KEY = bytes(range(16))
# The largest article number (RFC 3977 §6).
ARTICLES = 2**31 - 1
# The CRC-32C of "123456789": the check value catalogues of CRCs give (CRC-32/ISCSI in Greg Cook's
# catalogue of parametrised CRC algorithms).
CHECK = 0xE3069283
# The versions of the rules of reading with one changed, by the name `dn-compiler journal-model
# --mutant` takes.
MUTANTS = ["tag-unchecked", "torn-longer", "torn-shorter", "length-longer", "length-shorter",
           "end-unchecked", "torn-at-start", "format-again", "inexact", "unchecked",
           "not-a-record-torn", "later-unchecked", "key-unshaped"]
REASONS = ["short", "too-long", "unterminated", "tag", "not-a-record", "format-again"]
# What an append the crash cut short can leave.
TORN = {"short", "too-long", "unterminated", "tag"}
# The names of an article's files and of a tail kept, by the letter they begin with.
LETTERS = {b"a": "final", b"t": "temp", b"q": "quarantine", b"j": "tail"}
# Lines both have to refuse to answer.
REFUSED = [f"encode {KEY.hex()} 0 1_0 61 1 1 1 67=1", f"encode {KEY.hex()} 0 1 61 1 1 1 67=+1",
           f"encode {KEY.hex()} {2**64} 1 61 1 1 1 67=1", "encode 0001 0 1 61 1 1 1 67=1",
           "crc 0A0B", "crc 0a0", "scan 0 1", f"names {2**64}", "name journal", "siphash 00 -",
           f"siphash {KEY.hex()} 0a0", "format 00", "start 00 0", f"start {KEY.hex()} {2**64}",
           f"start {KEY.hex()} 0x1", f"encode {KEY.hex()} 0 1 61 1 1 1 67=1,", " ", "\t", "scan 00\r",
           "\r"]

Group = tuple[bytes, int]
Commit = tuple[int, bytes, tuple[Group, ...], int, int, int]
# A record after a journal's format: a commit, or a start.
Item = Commit | str
START_RECORD: Item = "start"


@dataclass(frozen=True)
class Case:
    """A line to answer and, when the lane knows it, the answer: the whole of it or, with
    `prefix`, how it starts."""
    line: str
    want: str | None = None
    prefix: bool = False

    def holds(self, said: str) -> bool:
        return self.want is None or (said.startswith(self.want) if self.prefix else said == self.want)


def siphash(key: bytes, msg: bytes) -> int:
    """SipHash-2-4, the lane's own, for the frames it makes."""
    def rot(x: int, b: int) -> int:
        return ((x << b) | (x >> (64 - b))) & MASK

    def sip(v0: int, v1: int, v2: int, v3: int) -> tuple[int, int, int, int]:
        v0 = (v0 + v1) & MASK
        v2 = (v2 + v3) & MASK
        v1, v3 = rot(v1, 13) ^ v0, rot(v3, 16) ^ v2
        v0 = rot(v0, 32)
        v2 = (v2 + v1) & MASK
        v0 = (v0 + v3) & MASK
        v1, v3 = rot(v1, 17) ^ v2, rot(v3, 21) ^ v0
        return v0, v1, rot(v2, 32), v3

    k0 = int.from_bytes(key[:8], "little")
    k1 = int.from_bytes(key[8:], "little")
    v = (k0 ^ 0x736F6D6570736575, k1 ^ 0x646F72616E646F6D, k0 ^ 0x6C7967656E657261,
         k1 ^ 0x7465646279746573)
    padded = msg + bytes(7 - len(msg) % 8) + bytes([len(msg) & 0xFF])
    for i in range(0, len(padded), 8):
        m = int.from_bytes(padded[i:i + 8], "little")
        v = sip(*sip(v[0], v[1], v[2], v[3] ^ m))
        v = (v[0] ^ m, v[1], v[2], v[3])
    v = (v[0], v[1], v[2] ^ 0xFF, v[3])
    for _ in range(4):
        v = sip(*v)
    return v[0] ^ v[1] ^ v[2] ^ v[3]


def payload(c: Commit) -> bytes:
    seq, message_id, groups, header, size, crc = c
    out = struct.pack("<QB", seq, len(message_id)) + message_id + bytes([len(groups)])
    for name, number in groups:
        out += bytes([len(name)]) + name + struct.pack("<I", number)
    return out + struct.pack("<III", header, size, crc)


def frame(key: bytes, offset: int, kind: int, body: bytes, *, length: int | None = None,
          end: int = END) -> bytes:
    """A frame at `offset` under `key`, with `length` in its length field and `end` as its last
    octet if they are given."""
    tag = siphash(key, struct.pack("<QB", offset, kind) + body)
    return struct.pack("<IQB", len(body) if length is None else length, tag, kind) + body + bytes([end])


def format_frame(key: bytes) -> bytes:
    return frame(key, 0, FORMAT, MAGIC + key)


@functools.cache
def encoded(key: bytes, offset: int, item: Item) -> bytes:
    if isinstance(item, str):
        return frame(key, offset, START, b"")
    return frame(key, offset, COMMIT, payload(item))


def journal(key: bytes, items: list[Item]) -> bytes:
    out = format_frame(key)
    for item in items:
        out += encoded(key, len(out), item)
    return out


def shown(item: Item) -> str:
    """A record as both print it."""
    if isinstance(item, str):
        return "S"
    seq, message_id, groups, header, size, crc = item
    listed = ",".join(f"{name.hex()}={number}" for name, number in groups)
    return f"C:{seq}:{message_id.hex()}:{header}:{size}:{crc}:{listed}"


def hexed(data: bytes) -> str:
    return data.hex() or "-"


def records(key: bytes, items: list[Item] | None) -> list[str]:
    """What a journal read as its format and `items`, or as nothing at all, prints."""
    return [] if items is None else [f"F:{key.hex()}", *map(shown, items)]


def clean(data: bytes, key: bytes, items: list[Item] | None) -> Case:
    return Case(f"scan {hexed(data)}", " ".join([*records(key, items), "end clean"]))


def corrupt(data: bytes, key: bytes, items: list[Item] | None, offset: int, why: str) -> Case:
    return Case(f"scan {hexed(data)}", " ".join([*records(key, items), f"end corrupt {offset} {why}"]))


def stopped(data: bytes, key: bytes, items: list[Item] | None, offset: int, why: str | None, *,
            later: bool = False) -> Case:
    """Reading `data` stops at `offset`, after its format carrying `key` and the records `items`
    (None: not even the format), at a frame that fails for `why`, or for a reason a torn append can
    leave if the lane does not know it: in a torn tail if a torn append can leave it, what is left
    fits the append that can have been cut and, `later` false, no frame that checks starts in it
    after its first octet; in corruption otherwise."""
    head = " ".join([*records(key, items), "end"])
    bound = FIRST_FRAME if items is None else MAX_FRAME
    if (why is None or why in TORN) and len(data) - offset <= bound and not later:
        return Case(f"scan {hexed(data)}", f"{head} torn {offset}")
    if why is None:
        return Case(f"scan {hexed(data)}", f"{head} corrupt {offset} ", prefix=True)
    return corrupt(data, key, items, offset, why)


def why_at(data: bytes, start: int) -> str:
    """Why the frame at `start` of `data`, which does not check, fails: the first of its header,
    its length, its end mark and its tag that does."""
    rest = data[start:]
    if len(rest) < HEADER:
        return "short"
    length: int = struct.unpack_from("<I", rest)[0]
    if length > MAX_PAYLOAD:
        return "too-long"
    if len(rest) < HEADER + length + 1:
        return "short"
    return "tag" if rest[HEADER + length] == END else "unterminated"


def random_commit(rng: random.Random, *, most: int = 250, groups: int = 16, name: int = 64) -> Commit:
    """A commit a correct store writes, no larger than the sizes given."""
    def number(bits: int) -> int:
        return rng.choice([1, (1 << bits) - 1, rng.randint(1, (1 << bits) - 1), rng.randint(1, 1 << 20)])
    def article() -> int:
        return rng.choice([1, ARTICLES, rng.randint(1, ARTICLES), rng.randint(1, 1 << 20)])
    named: dict[bytes, int] = {}
    for _ in range(rng.randint(1, groups)):
        named.setdefault(rng.randbytes(rng.randint(1, name)), article())
    size = number(32)
    return (number(64), rng.randbytes(rng.randint(1, most)), tuple(named.items()),
            rng.choice([0, size, rng.randint(0, size)]), size, number(32))


SAMPLE: Commit = (1, b"<a@b.example>", ((b"local.test", 1),), 100, 200, 12345)
SMALLEST: Commit = (1, b"x", ((b"g", 1),), 0, 0, 0)
LARGEST: Commit = (2**64 - 1, b"<" + b"i" * 248 + b">",
                   tuple((bytes([97 + k]) * 64, ARTICLES) for k in range(16)), 2**32 - 1, 2**32 - 1,
                   2**32 - 1)


def after(key: bytes, head: bytes) -> bytes:
    """Records enough after `head` that what follows any byte before them is more than the
    largest frame."""
    out = b""
    while len(out) <= MAX_FRAME:
        out += encoded(key, len(head) + len(out), SAMPLE)
    return out


# SipHash-2-4 and the CRC-32C


def sip_vectors() -> list[int]:
    """The 64 tags of SipHash-2-4 in the authors' `vectors.h`: the key 00 to 0f, the message of
    each length from 0 to 63 its octets 00, 01 and so on, each tag printed octet by octet, least
    significant first."""
    text = SIP_VECTORS.read_text(encoding="ascii")
    block = text[text.index("vectors_sip64[64][8]"):text.index("vectors_sip128")]
    octets = [int(x, 16) for x in re.findall(r"0x([0-9a-f]{2})", block)]
    if len(octets) != 64 * 8:
        raise LaneError(f"{SIP_VECTORS.name} holds {len(octets)} octets of SipHash-2-4-64 tags, not 512")
    return [int.from_bytes(bytes(octets[8 * i:8 * i + 8]), "little") for i in range(64)]


def sip_cases(rng: random.Random) -> list[Case]:
    """The authors' vectors, and keys and messages drawn up to 600 octets, the lane's own
    SipHash giving the answer."""
    cases = [Case(f"siphash {KEY.hex()} {hexed(bytes(range(i)))}", str(tag))
             for i, tag in enumerate(sip_vectors())]
    for n in [*range(65), *(rng.randint(65, 600) for _ in range(100))]:
        key, msg = rng.randbytes(16), rng.randbytes(n)
        cases.append(Case(f"siphash {key.hex()} {hexed(msg)}", str(siphash(key, msg))))
    return cases


def filled(rows: list[tuple[int, bytes] | None]) -> bytes:
    """The octets of rows of four at their offsets, a row left out (None) filled in by the steady
    step from the row before the gap to the row after, which every octet of both has to keep."""
    out = b""
    for k, row in enumerate(rows):
        if row is None:
            continue
        offset, octets = row
        if k and rows[k - 1] is None:
            before = rows[k - 2] if k >= 2 else None
            if before is None:
                raise LaneError("a gap in RFC 7143's examples has no row before it")
            first, last = before[1][0], octets[0]
            step, uneven = divmod(last - first, offset - before[0])
            if uneven or any(o != first + step * i for i, o in enumerate(before[1])) or \
                    any(o != last + step * i for i, o in enumerate(octets)):
                raise LaneError(f"the rows around a gap in RFC 7143's examples make no steady step: "
                                f"{before}, {row}")
            out += bytes(first + step * i for i in range(4, offset - before[0]))
        if offset != len(out):
            raise LaneError(f"a row of RFC 7143's examples is at {offset}, not {len(out)}")
        out += octets
    return out


def vectors() -> list[tuple[str, bytes, int]]:
    """RFC 7143's examples of the CRC-32C (appendix A.4), read from its text: a name, the octets
    its rows of four give, and the CRC, printed octet by octet, least significant first."""
    text = RFC.read_text(encoding="ascii")
    section = text[text.index("\nA.4.  CRC Examples"):text.index("\nAppendix B.")]
    out: list[tuple[str, bytes, int]] = []
    name = ""
    rows: list[tuple[int, bytes] | None] = []
    for line in (s.strip() for s in section.splitlines()):
        if (row := re.fullmatch(r"(\d+):((?: +[0-9a-f]{2}){4})", line)) is not None:
            rows.append((int(row[1]), bytes.fromhex(row[2].replace(" ", ""))))
        elif line == "...":
            rows.append(None)
        elif line.startswith("CRC:"):
            crc = int.from_bytes(bytes.fromhex(line.removeprefix("CRC:").replace(" ", "")), "little")
            out.append((name, filled(rows), crc))
        elif line.endswith(":") and not line.startswith("Byte:"):
            name, rows = line.removesuffix(":"), []
    if len(out) != 5:
        raise LaneError(f"RFC 7143 appendix A.4 read as {len(out)} examples, not 5")
    for name, data, _ in out:
        said = re.match(r"(\d+) bytes", name)
        if said is not None and len(data) != int(said[1]):
            raise LaneError(f"RFC 7143's example {name!r} read as {len(data)} octets")
    return out


def crc_cases(rng: random.Random) -> list[Case]:
    """RFC 7143's examples, the check value, nothing, and inputs drawn up to 4 MiB long."""
    cases = [Case(f"crc {hexed(data)}", str(crc)) for _, data, crc in vectors()]
    cases += [Case(f"crc {b'123456789'.hex()}", str(CHECK)), Case("crc -", "0")]
    sizes = [*range(1, 257), *(2**k + d for k in range(9, 17) for d in (-1, 0, 1)), 1 << 20, 4 << 20]
    return cases + [Case(f"crc {rng.randbytes(n).hex()}") for n in sizes]


# Commits


def encode_line(key: bytes, offset: int, c: Commit) -> str:
    seq, message_id, groups, header, size, crc = c
    listed = ",".join(f"{hexed(name)}={number}" for name, number in groups) or "-"
    return f"encode {key.hex()} {offset} {seq} {hexed(message_id)} {header} {size} {crc} {listed}"


def bounded(base: Commit) -> list[tuple[Commit, bool]]:
    """Commits at and past each bound a correct store keeps, and whether it writes each."""
    seq, message_id, groups, header, size, crc = base
    def named(n: int) -> tuple[Group, ...]:
        return tuple((b"g%d" % k, k + 1) for k in range(n))
    out = [((s, message_id, groups, header, size, crc), 1 <= s < 2**64) for s in (0, 1, 2**64 - 1, 2**64)]
    out += [((seq, b"m" * n, groups, header, size, crc), 1 <= n <= 250) for n in (0, 1, 250, 251)]
    out += [((seq, message_id, named(n), header, size, crc), 1 <= n <= 16) for n in (0, 1, 16, 17)]
    for n in (0, 1, 64, 65):
        out += [((seq, message_id, ((b"n" * n, 1),), header, size, crc), 1 <= n <= 64),
                ((seq, message_id, (*named(15), (b"n" * n, 1)), header, size, crc), 1 <= n <= 64)]
    out += [((seq, message_id, ((b"g", v),), header, size, crc), 1 <= v <= ARTICLES)
            for v in (0, 1, ARTICLES, ARTICLES + 1, 2**32 - 1, 2**32)]
    out += [((seq, message_id, ((b"g", 1), (b"g", 2)), header, size, crc), False),
            ((seq, message_id, ((b"g", 1), (b"h", 1)), header, size, crc), True),
            ((seq, message_id, groups, size, size, crc), True),
            ((seq, message_id, groups, size + 1, size, crc), False)]
    for v in (2**32 - 1, 2**32):
        out += [((seq, message_id, groups, v, v, crc), v < 2**32),
                ((seq, message_id, groups, header, v, crc), v < 2**32),
                ((seq, message_id, groups, header, size, v), v < 2**32)]
    return out


def packable(c: Commit) -> bool:
    """Whether every number of a commit fits the octets it is written in, whatever else it is."""
    return c[0] < 2**64 and max(c[3], c[4], c[5], *(n for _, n in c[2])) < 2**32


def encode_cases(rng: random.Random, commits: list[Commit]) -> list[Case]:
    """Each commit at and past the bounds, and each drawn, framed as the lane frames it, at
    offsets from 0 to the largest and under keys drawn at random; starts and formats too."""
    offsets = [0, 1, FIRST_FRAME, 2**32, 2**64 - 1]
    cases = [Case(encode_line(KEY, o, c), encoded(KEY, o, c).hex() if ok else "not-ok")
             for base in (SAMPLE, SMALLEST) for c, ok in bounded(base) for o in offsets[:2]]
    for c in commits:
        key, offset = rng.randbytes(16), rng.choice([*offsets, rng.getrandbits(64)])
        cases.append(Case(encode_line(key, offset, c), encoded(key, offset, c).hex()))
    for offset in [*offsets, *(rng.getrandbits(64) for _ in range(20))]:
        key = rng.randbytes(16)
        cases.append(Case(f"start {key.hex()} {offset}", encoded(key, offset, START_RECORD).hex()))
    return cases + [Case(f"format {key.hex()}", format_frame(key).hex())
                    for key in (KEY, bytes(16), b"\xff" * 16, rng.randbytes(16))]


# Journals


def with_starts(rng: random.Random, chosen: list[Commit]) -> list[Item]:
    """Commits with starts among them, as runs of the store append them, one first."""
    items: list[Item] = [START_RECORD]
    for c in chosen:
        items += [START_RECORD] * (rng.random() < 0.3) + [c]
    return items + [START_RECORD] * (rng.random() < 0.3)


def clean_cases(rng: random.Random, commits: list[Commit]) -> list[Case]:
    """Journals of records one after the other (`scan_encoded`), and nothing at all."""
    cases = [clean(b"", KEY, None), clean(format_frame(KEY), KEY, [])]
    for _ in range(200):
        key = rng.randbytes(16)
        items = with_starts(rng, rng.sample(commits, rng.randint(1, 8)))
        cases.append(clean(journal(key, items), key, items))
    whole: list[Item] = [START_RECORD, SAMPLE, SMALLEST, LARGEST, START_RECORD, START_RECORD, SAMPLE]
    return [*cases, clean(journal(KEY, whole), KEY, whole)]


def junk_for(rng: random.Random, rest: bytes) -> bytes:
    """Junk as long as `rest` and not equal to it: what the crash left instead of the frame's
    rest."""
    junk = rng.randbytes(len(rest))
    return junk if junk != rest else junk[:-1] + bytes([junk[-1] ^ 0xFF])


def torn_cases(rng: random.Random, commits: list[Commit]) -> list[Case]:
    """Every proper prefix of a frame, bare (`scan_torn`), filled with zeros to the frame's length
    (`scan_torn_zeros`) and filled with junk, as a file system may leave an append it did not
    finish (`scan_torn_fill` when the junk does not end in the end mark): of the format's alone
    (`scan_torn_format`, `scan_torn_format_zeros`, `scan_torn_format_fill`), and of the format's,
    a start's and commits' after the records of a journal."""
    cases = []
    first = format_frame(KEY)
    for n in range(1, len(first)):
        junk = junk_for(rng, first[n:])
        cases += [stopped(first[:n], KEY, None, 0, "short"),
                  stopped(first[:n] + bytes(len(first) - n), KEY, None, 0, "unterminated"),
                  stopped(first[:n] + junk, KEY, None, 0, "unterminated" if n >= 4 and junk[-1] != END else None)]
    before: list[Item] = [START_RECORD, SAMPLE, SMALLEST]
    head = journal(KEY, before)
    frames = [frame(KEY, len(head), FORMAT, MAGIC + KEY), encoded(KEY, len(head), START_RECORD),
              *(encoded(KEY, len(head), c) for c in [SAMPLE, SMALLEST, LARGEST, *rng.sample(commits, 3)])]
    for data in frames:
        for n in range(1, len(data)):
            junk = junk_for(rng, data[n:])
            cases += [stopped(head + data[:n], KEY, before, len(head), "short"),
                      stopped(head + data[:n] + bytes(len(data) - n), KEY, before, len(head), "unterminated"),
                      stopped(head + data[:n] + junk, KEY, before, len(head),
                              "unterminated" if n >= 4 and junk[-1] != END else None)]
    return cases


def partitions(data: bytes, start: int) -> list[list[tuple[int, int]]]:
    """A frame written at `start` of a file, torn at the file's units of 512 and of 64 octets and
    into three nearly equal parts, as LazyFS's `torn-op` tears one write: each list the parts, as
    ranges within the frame, of more than one part."""
    out: list[list[tuple[int, int]]] = []
    for unit in (512, 64):
        cuts = list(range(unit - start % unit, len(data), unit))
        parts = [(a, b) for a, b in zip([0, *cuts], [*cuts, len(data)], strict=True) if a < b]
        if len(parts) > 1 and parts not in out:
            out.append(parts)
    third = len(data) // 3
    return [*out, [(0, third), (third, 2 * third), (2 * third, len(data))]]


def kept_sets(rng: random.Random, n: int) -> list[int]:
    """Proper subsets of `n` parts, as masks: every one if there are 62 or fewer, otherwise the
    start alone, the end alone, both ends, and others drawn at random."""
    if 2**n - 2 <= 62:
        return list(range(1, 2**n - 1))
    ends = [1, 1 << (n - 1), 1 | 1 << (n - 1)]
    return [*ends, *(rng.randint(1, 2**n - 2) for _ in range(62 - len(ends)))]


def part_cases(rng: random.Random, commits: list[Commit]) -> list[Case]:
    """Frames torn into parts, a proper subset of them kept and the rest zeros or junk — the end
    kept and the start lost, the ends kept and the middle lost — each read as a torn tail where the
    frame starts: a tag made under the key, which a crash does not have, does not check. A part
    lost to octets it already held, as a start's length to zeros, loses nothing and is left out."""
    def torn(whole: bytes) -> list[bytes]:
        out = []
        for parts in partitions(whole, len(head)):
            for kept in kept_sets(rng, len(parts)):
                for fill in (0, 1):
                    data = bytearray(whole)
                    for i, (a, b) in enumerate(parts):
                        if not kept >> i & 1:
                            data[a:b] = bytes(b - a) if fill == 0 else rng.randbytes(b - a)
                    if data != whole:
                        out.append(bytes(data))
        return out

    head = b""
    cases = [stopped(data, KEY, None, 0, None) for data in torn(format_frame(KEY))]
    before: list[Item] = [START_RECORD, SAMPLE, SMALLEST]
    head = journal(KEY, before)
    for item in [START_RECORD, SAMPLE, LARGEST, *rng.sample(commits, 6)]:
        cases += [stopped(head + data, KEY, before, len(head), None)
                  for data in torn(encoded(KEY, len(head), item))]
    return cases


def tail_cases(rng: random.Random) -> list[Case]:
    """Zeros and junk on both sides of the format's frame and of the largest, where a journal
    starts and after its records; and zeros with records after them, which no torn append
    leaves."""
    cases = []
    for before in (None, [], [START_RECORD, SAMPLE, SMALLEST]):
        head = b"" if before is None else journal(KEY, before)
        for n in (1, 12, 13, 14, FIRST_FRAME - 1, FIRST_FRAME, FIRST_FRAME + 1, MAX_FRAME - 1, MAX_FRAME,
                  MAX_FRAME + 1, 2 * MAX_FRAME):
            # Zeros are a frame of no payload, short of its end mark or without it.
            cases += [stopped(head + bytes(n), KEY, before, len(head), "short" if n < 14 else "unterminated"),
                      stopped(head + rng.randbytes(n), KEY, before, len(head), None)]
        cases.append(stopped(head + bytes(14) + after(KEY, head + bytes(14)), KEY, before, len(head),
                             "unterminated"))
    return cases


def later_cases(rng: random.Random, commits: list[Commit]) -> list[Case]:
    """A frame that does not check with one that does after it, where what is left would fit a
    torn append: corruption (`scan_damaged`), since an append the crash cut short is the last thing
    written. A frame that is whole but would not check where it lies — under another key, or
    copied from another place — does not count, and what is left is still a torn tail."""
    cases = []
    before: list[Item] = [START_RECORD, SAMPLE]
    head = journal(KEY, before)
    at = len(head)
    for item in [SAMPLE, SMALLEST, START_RECORD, *rng.sample([c for c in commits if len(payload(c)) < 300], 4)]:
        changed_frame = encoded(KEY, at, item)
        follow = encoded(KEY, at + len(changed_frame), rng.choice([START_RECORD, SMALLEST]))
        for p in sorted({0, 3, 4, 11, 12, len(changed_frame) - 1, *rng.sample(range(len(changed_frame)), 6)}):
            data = bytearray(head + changed_frame + follow)
            data[at + p] ^= rng.randint(1, 255)
            cases.append(stopped(bytes(data), KEY, before, at, why_at(bytes(data), at), later=True))
    for n in (1, 5, 12, 13, 14, 40, 200):
        for fill in (bytes(n), rng.randbytes(n)):
            for item in (START_RECORD, SAMPLE):
                whole = head + fill + encoded(KEY, at + n, item)
                cases.append(stopped(whole, KEY, before, at, why_at(whole, at), later=True))
                misplaced = head + fill + encoded(KEY, at, item)
                elsewhere = head + fill + encoded(bytes(16), at + n, item)
                cases += [stopped(misplaced, KEY, before, at, why_at(misplaced, at)),
                          stopped(elsewhere, KEY, before, at, why_at(elsewhere, at))]
    return cases


def frame_starts(data: bytes) -> list[int]:
    """Where each frame of a journal the lane made starts."""
    starts, at = [], 0
    while at < len(data):
        starts.append(at)
        at += HEADER + 1 + struct.unpack_from("<I", data, at)[0]
    return starts


def flip_cases(rng: random.Random, commits: list[Commit]) -> tuple[list[Case], int]:
    """Each byte of a journal changed three ways, the journal ending with the changed frame, soon
    after it and with much after it: reading stops where the frame of the changed byte starts,
    whatever the byte was, the records before it all it reads, and for the reason the lane finds —
    in a torn tail only if the changed frame is the last and fits a torn append. Also how many of
    the cases rest on the tag: all but those the end mark or the length refuses."""
    chosen: list[Item] = [SMALLEST, START_RECORD,
                          *rng.sample([c for c in commits if len(payload(c)) < 110], 2)]
    base = journal(KEY, chosen)
    starts = frame_starts(base)
    cases, on_tag = [], 0
    for data in (base, base + after(KEY, base)):
        for p in range(len(base)):
            k = max(i for i, s in enumerate(starts) if s <= p)
            for mask in (0x01, 0x80, 0xFF):
                changed = bytearray(data)
                changed[p] ^= mask
                why = why_at(bytes(changed), starts[k])
                last = k == len(starts) - 1 and data == base
                cases.append(stopped(bytes(changed), KEY, chosen[:k - 1] if k else None, starts[k], why,
                                     later=k > 0 and not last))
                on_tag += why == "tag"
    return cases, on_tag


def refused_cases() -> list[Case]:
    """Frames that check but hold no record, frames too long, frames without their end mark,
    frames tagged under another key or copied to another place, and lengths that run into what
    follows, each last in a journal and with records after it; and first frames that are not the
    format, look like it without being it, or are a format of another version, and formats
    twice."""
    body = payload(SAMPLE)
    largest = payload(LARGEST)
    before: list[Item] = [START_RECORD, SAMPLE]
    head = journal(KEY, before)
    at = len(head)
    refused = [(frame(KEY, at, k, body), "not-a-record") for k in (0, 4, 0x7F, 0xFF)]
    refused += [(frame(KEY, at, k, MAGIC + KEY), "not-a-record") for k in (0, COMMIT, START, 4)]
    refused += [(frame(KEY, at, START, b), "not-a-record") for b in (b"\0", b"\xa5", body)]
    refused += [(frame(KEY, at, FORMAT, m), "not-a-record")
                for m in (MAGIC[:-1] + b"\x02" + KEY, MAGIC + KEY[:-1], MAGIC + KEY + b"\0",
                          b"D" + MAGIC[1:] + KEY, b"", body)]
    refused += [(frame(KEY, at, COMMIT, body[:n]), "not-a-record") for n in range(len(body))]
    refused += [(frame(KEY, at, COMMIT, body + bytes(n)), "not-a-record") for n in (1, 2, 3)]
    refused += [(frame(KEY, at, COMMIT, payload(c)), "not-a-record") for c, ok in bounded(SAMPLE)
                if not ok and packable(c)]
    refused += [(frame(KEY, at, COMMIT, bytes(MAX_PAYLOAD)), "not-a-record"),
                (frame(KEY, at, COMMIT, largest + b"\0"), "too-long"),
                (frame(KEY, at, COMMIT, bytes(MAX_PAYLOAD + 1)), "too-long"),
                (frame(KEY, at, COMMIT, body, length=2**32 - 1), "too-long"),
                (frame(KEY, at, COMMIT, body, end=0x00), "unterminated"),
                (frame(KEY, at, COMMIT, body, end=0xFF), "unterminated"),
                (frame(KEY, at, START, b"", end=0x00), "unterminated"),
                (frame(bytes(16), at, COMMIT, body), "tag"),
                (frame(KEY[::-1], at, COMMIT, body), "tag"),
                (frame(bytes(16), at, START, b""), "tag"),
                (encoded(KEY, len(format_frame(KEY)), SAMPLE), "tag"),
                (encoded(KEY, at + 1, SAMPLE), "tag"),
                (encoded(KEY, at - 1, START_RECORD), "tag"),
                (frame(KEY, at, FORMAT, MAGIC + bytes(16)), "format-again"),
                (frame(bytes(16), at, FORMAT, MAGIC + bytes(16)), "tag")]
    cases = [stopped(head + data + tail, KEY, before, at, why, later=bool(tail))
             for data, why in refused for tail in (b"", after(KEY, head + data))]
    # A length that runs into what follows: short when nothing does, anything when it does.
    long_length = frame(KEY, at, COMMIT, body, length=MAX_PAYLOAD)
    cases += [stopped(head + long_length, KEY, before, at, "short"),
              stopped(head + long_length + after(KEY, head + long_length), KEY, before, at, None, later=True)]
    start = encoded(KEY, 0, SAMPLE)
    second_format = frame(KEY, len(format_frame(KEY)), FORMAT, MAGIC + KEY)
    newer = frame(KEY, 0, FORMAT, MAGIC[:-1] + b"\x02" + KEY)
    # First frames that carry no key the way the format does, under the key they hold: of another
    # title, of another type, one octet longer.
    unshaped = [frame(KEY, 0, FORMAT, b"X" * len(TITLE) + b"\x01" + KEY), frame(KEY, 0, COMMIT, MAGIC + KEY),
                frame(KEY, 0, FORMAT, MAGIC + KEY + b"\0"), encoded(KEY, 0, START_RECORD)]
    cases += [stopped(f + tail, KEY, None, 0, "tag")
              for f in unshaped for tail in (b"", encoded(KEY, len(f), SAMPLE))]
    # A journal whose first frame is not its format has no key to check it with; a second format
    # and a format of another version are never torn tails, however little follows.
    return [*cases, stopped(start, KEY, None, 0, "tag"), stopped(start + start, KEY, None, 0, "tag"),
            corrupt(format_frame(KEY) + second_format, KEY, [], len(format_frame(KEY)), "format-again"),
            corrupt(head + frame(KEY, at, FORMAT, MAGIC + KEY) + encoded(KEY, at + FIRST_FRAME, SAMPLE),
                    KEY, before, at, "format-again"),
            corrupt(newer, KEY, None, 0, "not-a-record")]


def damaged(rng: random.Random, data: bytes, way: int) -> bytes:
    """A journal damaged one of nine ways."""
    p = rng.randrange(len(data))
    starts = frame_starts(data) if way == 8 else []
    match way:
        case 0:
            return data[:p]
        case 1:
            return data[:p] + bytes([data[p] ^ rng.randint(1, 255)]) + data[p + 1:]
        case 2:
            return data[:p] + rng.randbytes(rng.randint(1, 16)) + data[p:]
        case 3:
            return data[:p] + data[p + 1:]
        case 4:
            return data + rng.randbytes(rng.randint(1, 2 * MAX_FRAME))
        case 5:
            return data + bytes(rng.randint(1, 2 * MAX_FRAME))
        case 6:
            return data + data
        case 7:
            return data[FIRST_FRAME:]
        case _:
            s = rng.choice(starts)
            e = ([*starts, len(data)])[starts.index(s) + 1]
            return data + data[s:e]


def damaged_cases(rng: random.Random, commits: list[Commit]) -> list[Case]:
    """Journals drawn at random and damaged at random, which both have to answer alike."""
    cases = []
    for k in range(1800):
        key = rng.randbytes(16)
        data = journal(key, with_starts(rng, rng.sample(commits, rng.randint(0, 6))))
        cases.append(Case(f"scan {hexed(damaged(rng, data, k % 9))}"))
    return cases


# Names


def name_cases(rng: random.Random) -> list[Case]:
    """The names of an article (`parseName_bytes`), and names the store does not give."""
    seqs = [0, 1, 9, 10, 15, 16, 255, 2**32 - 1, 2**32, 2**63, 2**64 - 1,
            *(rng.getrandbits(64) for _ in range(40))]
    cases = [Case("name " + b"journal".hex(), "journal")]
    for seq in seqs:
        named = {kind: b"%s%016x" % (letter, seq) for letter, kind in LETTERS.items()}
        cases.append(Case(f"names {seq}", " ".join(n.hex() for n in named.values())))
        cases += [Case(f"name {n.hex()}", f"{kind} {seq}") for kind, n in named.items()]
    digits = b"0123456789abcdef"
    others = [b"", b"a", b"t", b"journal\n", b"Journal", b"journals", b"journa", b"journal.tmp", b".", b"..",
              b"a" + digits[:15], b"a" + digits + b"0", b"A" + digits, b"T" + digits, b"a" + digits.upper(),
              b"a" + b"g" + digits[1:], b"b" + digits, b"x" + digits, b" a" + digits, b"a" + digits + b" ",
              b"t" + digits + b"\0", b"a0x" + digits[2:], b"a-" + digits[1:], b"aa" + digits, b"tmp",
              b"lost+found", b"Q" + digits, b"j" + digits[:15], b"u" + digits]
    return cases + [Case(f"name {hexed(n)}", "none") for n in others]


def ending(said: str) -> str:
    """How a journal's answer says it ends: clean, torn, or the reason for corruption."""
    words = said.split(" end ", 1)[-1].removeprefix("end ").split()
    return words[2] if words[0] == "corrupt" else words[0]


def corpus_digests() -> None:
    """The authors' vectors are the ones docs/provenance.json records."""
    recorded = {e["destination"]: e["source_sha256"] for e in json.loads(PROVENANCE.read_text())["files"]
                if e["destination"].startswith("tests/corpus/siphash/")}
    held = {f"tests/corpus/siphash/{p.name}": hashlib.sha256(p.read_bytes()).hexdigest()
            for p in SIP_VECTORS.parent.iterdir()}
    if held != recorded:
        raise LaneError(f"tests/corpus/siphash is not what docs/provenance.json records: "
                        f"{sorted(set(held.items()) ^ set(recorded.items()))}")


def check() -> Report:
    OUT.mkdir(parents=True, exist_ok=True)
    corpus_digests()
    python = str(lanes.pinned_python(REQUIREMENTS))
    implementation = subprocess.run([python, "-c", "import google_crc32c; print(google_crc32c.implementation)"],
                                    capture_output=True, text=True, check=True).stdout.strip()
    if implementation != "c":
        raise LaneError(f"google-crc32c runs its {implementation} implementation, not its C extension")
    rng = random.Random(SEED)  # noqa: S311 -- a fixed seed, so that every run draws the same cases
    steps, mark = {}, time.monotonic()
    if (len(encoded(KEY, 0, LARGEST)), len(format_frame(KEY)), len(encoded(KEY, 0, START_RECORD))) != \
            (MAX_FRAME, FIRST_FRAME, START_FRAME):
        raise LaneError("the largest commit, the format or a start does not fill the frame the bounds give")
    commits = [SAMPLE, SMALLEST, LARGEST, *(random_commit(rng) for _ in range(400)),
               *(random_commit(rng, most=20, groups=3, name=12) for _ in range(200))]
    flips, on_tag = flip_cases(rng, commits)
    families = {"siphash": sip_cases(rng), "crc": crc_cases(rng), "encode": encode_cases(rng, commits),
                "clean": clean_cases(rng, commits), "torn": torn_cases(rng, commits),
                "parts": part_cases(rng, commits), "tails": tail_cases(rng),
                "later": later_cases(rng, commits), "flips": flips,
                "refused": refused_cases(), "damaged": damaged_cases(rng, commits), "names": name_cases(rng)}
    cases = [c for family in families.values() for c in family]
    lines = [c.line for c in cases]
    steps["cases"], mark = round(time.monotonic() - mark, 1), time.monotonic()
    model_command = [str(lanes.DN_COMPILER), "journal-model"]
    model = C.answer_lines(model_command, lines, C.WORKERS)
    steps["model"], mark = round(time.monotonic() - mark, 1), time.monotonic()
    reference = C.answer_lines([python, str(REFERENCE)], lines, C.WORKERS)
    steps["reference"], mark = round(time.monotonic() - mark, 1), time.monotonic()
    for asked, a, b in zip(lines, model, reference, strict=True):
        if a != b:
            raise LaneError(f"{asked[:300]}: the model answers {a[:300]}, the reference {b[:300]}")
    crcs = [c.line for c in families["crc"]]
    first_crc = lines.index(crcs[0])
    library = C.answer_lines([python, str(REFERENCE)], [f"crc-library {ln.split()[1]}" for ln in crcs],
                             C.WORKERS)
    for asked, a, b in zip(crcs, model[first_crc:first_crc + len(crcs)], library, strict=True):
        if a != b:
            raise LaneError(f"{asked[:300]}: the model answers {a}, google-crc32c {b}")
    for case, said in zip(cases, model, strict=True):
        if not case.holds(said):
            raise LaneError(f"{case.line[:300]}: answered {said[:300]}, not {case.want}")
    for asked in REFUSED:
        for command in (model_command, [python, str(REFERENCE)]):
            done = subprocess.run(command, input=asked + "\n", capture_output=True, text=True, timeout=600,
                                  check=False)
            if done.returncode == 0:
                raise LaneError(f"{command[-1]} answered a line no case may be: {asked}")
    steps["library"], mark = round(time.monotonic() - mark, 1), time.monotonic()
    ends = [ending(said) for ln, said in zip(lines, model, strict=True) if ln.startswith("scan ")]
    unseen = [r for r in ["clean", "torn", *REASONS] if r not in ends]
    if unseen:
        raise LaneError(f"no journal ends {unseen}")
    held = [(ln, a) for ln, a in zip(lines, model, strict=True) if ln.startswith("scan ")]
    caught = {}
    for mutant in MUTANTS:
        differs = C.first_difference([*model_command, "--mutant", mutant], held)
        if differs is None:
            raise LaneError(f"the version {mutant} was not caught")
        caught[mutant] = differs[:120]
    steps["mutants"] = round(time.monotonic() - mark, 1)
    lanes.require_quoted({
        "docs/baseline.md": [f"{len(cases):,} cases", f"{len(MUTANTS)} versions of the rules of reading",
                             f"{len(vectors())} examples of RFC 7143", f"{on_tag:,} of the {len(flips):,}",
                             f"{len(families['parts']):,} frames torn into parts"],
        "docs/assurance.md": [f"{len(cases):,} cases", f"{len(MUTANTS)} versions of the rules of reading"]})
    return Report("checked", None, [REFERENCE, REQUIREMENTS], {
        "cases": len(cases), "by_family": {k: len(v) for k, v in families.items()},
        "with_answers": sum(1 for c in cases if c.want is not None), "flips_resting_on_the_tag": on_tag,
        "refused_lines": len(REFUSED),
        "ends_seen": {r: ends.count(r) for r in ["clean", "torn", *REASONS]},
        "crc_implementation": implementation, "mutants_caught": caught, "seconds_by_step": steps})


def main() -> None:
    lanes.lane_main("JOURNAL", OUT, check)


if __name__ == "__main__":
    main()
