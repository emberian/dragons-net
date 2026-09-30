#!/usr/bin/env python3
# SPDX-License-Identifier: AGPL-3.0-or-later
"""The store's journal and the names of its files, held two ways. `DN.News.Journal`, run by
`dn-compiler journal-model`, and the independent reference scripts/store_ref.py have to give the
same answer, to the byte, on every case:

- the CRC-32C of the examples RFC 7143 prints (appendix A.4), read from its text, of the check
  value catalogues of CRCs give, and of inputs drawn from a fixed seed, up to 4 MiB, which
  google-crc32c, a third implementation, has to give as well;
- commits on both sides of each bound a correct store keeps, and commits drawn at random, which
  the lane encodes itself too;
- journals: records one after the other; each followed by every proper prefix of a frame, bare,
  filled to the frame's length with zeros and filled with junk; zeros and junk on both sides of
  the format's frame and of the largest; every byte of a journal changed, with little or much
  after it; frames that check but hold no record, frames too long, frames without their end mark;
  journals whose first record is not their format or that hold it twice; appends cut short whose
  fill is chosen to put the end mark in place and make the CRC-32C right, which the proofs assume
  a crash never leaves; and journals drawn and damaged at random;
- the names the store gives, and names it does not.

Lines no case may be — a number with more than digits, hex in capitals or of an odd length, a
sequence number past sixteen hexadecimal digits — both have to refuse.

What the theorems of `DN.News.Journal` say of a case, both have to answer: a journal of records
reads back as them and ends cleanly (`scan_encoded`); a frame cut short reads as a torn tail
where it starts, bare (`scan_torn`, `scan_torn_format`), filled with zeros (`scan_torn_zeros`,
`scan_torn_format_zeros`) or filled with junk not ending in the end mark (`scan_torn_fill`,
`scan_torn_format_fill`); a
name reads as what it names (`parseName_names`). So they have to answer what the lane knows
otherwise: the RFC's CRCs, each commit's frame as the lane encodes it, a changed byte never read
as a record, and why each frame is refused. Each version of the rules of reading with one of them
changed (`DN.News.Journal.Mutant`) has to answer some case otherwise (docs/baseline.md,
"Journal").
"""
from __future__ import annotations

from dataclasses import dataclass
import functools
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
SEED = 20261001
FORMAT, COMMIT = 1, 2
MAGIC = b"dragons-net journal\x01"
END = 0xA5
MAX_PAYLOAD = 1376
MAX_FRAME = 9 + MAX_PAYLOAD + 1
FIRST_FRAME = 9 + len(MAGIC) + 1
# The largest article number (RFC 3977 §6).
ARTICLES = 2**31 - 1
# The CRC-32C of "123456789": the check value catalogues of CRCs give (CRC-32/ISCSI in Greg Cook's
# catalogue of parametrised CRC algorithms).
CHECK = 0xE3069283
# The versions of the rules of reading with one changed, by the name `dn-compiler journal-model
# --mutant` takes.
MUTANTS = ["crc-unchecked", "torn-longer", "torn-shorter", "length-longer", "length-shorter",
           "end-unchecked", "torn-at-start", "format-not-first", "format-again", "inexact",
           "unchecked", "not-a-record-torn"]
REASONS = ["short", "too-long", "unterminated", "checksum", "not-a-record", "no-format",
           "format-again"]
# What an append the crash cut short can leave.
TORN = {"short", "too-long", "unterminated", "checksum"}
# Lines both have to refuse to answer.
REFUSED = ["encode 1_0 61 1 1 1 67=1", "encode 1 61 1 1 1 67=+1", "crc 0A0B", "crc 0a0", "scan 0 1",
           f"names {2**64}", "name journal"]

Group = tuple[bytes, int]
Commit = tuple[int, bytes, tuple[Group, ...], int, int, int]


@dataclass(frozen=True)
class Case:
    """A line to answer and, when the lane knows it, the answer: the whole of it or, with
    `prefix`, how it starts."""
    line: str
    want: str | None = None
    prefix: bool = False

    def holds(self, said: str) -> bool:
        return self.want is None or (said.startswith(self.want) if self.prefix else said == self.want)


def crc32c(data: bytes) -> int:
    """A bit at a time, as RFC 7143 §13.1 defines it: the lane's own, for the frames it makes."""
    crc = 0xFFFFFFFF
    for byte in data:
        crc ^= byte
        for _ in range(8):
            crc = (crc >> 1) ^ 0x82F63B78 if crc & 1 else crc >> 1
    return crc ^ 0xFFFFFFFF


def payload(c: Commit) -> bytes:
    seq, message_id, groups, header, size, crc = c
    out = struct.pack("<QB", seq, len(message_id)) + message_id + bytes([len(groups)])
    for name, number in groups:
        out += bytes([len(name)]) + name + struct.pack("<I", number)
    return out + struct.pack("<III", header, size, crc)


def frame(kind: int, body: bytes, *, length: int | None = None, end: int = END) -> bytes:
    """A frame, with `length` in its length field and `end` as its last octet if they are
    given."""
    return (struct.pack("<IIB", len(body) if length is None else length, crc32c(bytes([kind]) + body),
                        kind) + body + bytes([end]))


FORMAT_FRAME = frame(FORMAT, MAGIC)


@functools.cache
def encoded(c: Commit) -> bytes:
    return frame(COMMIT, payload(c))


def journal(commits: list[Commit]) -> bytes:
    return FORMAT_FRAME + b"".join(map(encoded, commits))


def shown(c: Commit) -> str:
    """A commit as both print it."""
    seq, message_id, groups, header, size, crc = c
    listed = ",".join(f"{name.hex()}={number}" for name, number in groups)
    return f"C:{seq}:{message_id.hex()}:{header}:{size}:{crc}:{listed}"


def hexed(data: bytes) -> str:
    return data.hex() or "-"


def records(commits: list[Commit] | None) -> list[str]:
    """What a journal read as the format and `commits`, or as nothing at all, prints."""
    return [] if commits is None else ["F", *map(shown, commits)]


def clean(data: bytes, commits: list[Commit] | None) -> Case:
    return Case(f"scan {hexed(data)}", " ".join([*records(commits), "end clean"]))


def corrupt(data: bytes, commits: list[Commit] | None, offset: int, why: str) -> Case:
    return Case(f"scan {hexed(data)}", " ".join([*records(commits), f"end corrupt {offset} {why}"]))


def stopped(data: bytes, commits: list[Commit] | None, offset: int, why: str | None) -> Case:
    """Reading `data` stops at `offset`, after the records of `commits` (None: not even the
    format), at a frame that fails for `why`, or for a reason a torn append can leave if the lane
    does not know it: in a torn tail if a torn append can leave it and what is left fits the
    append that can have been cut, in corruption otherwise."""
    head = " ".join([*records(commits), "end"])
    bound = FIRST_FRAME if commits is None else MAX_FRAME
    if (why is None or why in TORN) and len(data) - offset <= bound:
        return Case(f"scan {hexed(data)}", f"{head} torn {offset}")
    if why is None:
        return Case(f"scan {hexed(data)}", f"{head} corrupt {offset} ", prefix=True)
    return corrupt(data, commits, offset, why)


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
# Records enough that what follows any byte before them is more than the largest frame.
AFTER = encoded(SAMPLE) * (MAX_FRAME // len(encoded(SAMPLE)) + 1)


# CRC-32C


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


def encode_line(c: Commit) -> str:
    seq, message_id, groups, header, size, crc = c
    listed = ",".join(f"{hexed(name)}={number}" for name, number in groups) or "-"
    return f"encode {seq} {hexed(message_id)} {header} {size} {crc} {listed}"


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


def encode_cases(commits: list[Commit]) -> list[Case]:
    """Each commit at and past the bounds, and each drawn, as the lane encodes it."""
    cases = [Case(encode_line(c), encoded(c).hex() if ok else "not-ok")
             for base in (SAMPLE, SMALLEST) for c, ok in bounded(base)]
    return cases + [Case(encode_line(c), encoded(c).hex()) for c in commits]


# Journals


def clean_cases(rng: random.Random, commits: list[Commit]) -> list[Case]:
    """Journals of records one after the other (`scan_encoded`), and nothing at all."""
    cases = [clean(b"", None), clean(FORMAT_FRAME, [])]
    for _ in range(200):
        chosen = rng.sample(commits, rng.randint(1, 8))
        cases.append(clean(journal(chosen), chosen))
    return [*cases, clean(journal([SAMPLE, SMALLEST, LARGEST, SAMPLE]), [SAMPLE, SMALLEST, LARGEST, SAMPLE])]


def torn_cases(rng: random.Random, commits: list[Commit]) -> list[Case]:
    """Every proper prefix of a frame, bare (`scan_torn`), filled with zeros to the frame's length
    (`scan_torn_zeros`) and filled with junk, as a file system may leave an append it did not
    finish (`scan_torn_fill` when the junk does not end in the end mark): of the format's alone
    (`scan_torn_format`, `scan_torn_format_zeros`, `scan_torn_format_fill`), and of the format's
    and commits' after the records of a journal."""
    cases = []
    for n in range(1, len(FORMAT_FRAME)):
        junk = rng.randbytes(len(FORMAT_FRAME) - n)
        cases += [stopped(FORMAT_FRAME[:n], None, 0, "short"),
                  stopped(FORMAT_FRAME[:n] + bytes(len(FORMAT_FRAME) - n), None, 0, "unterminated"),
                  stopped(FORMAT_FRAME[:n] + junk, None, 0, "unterminated" if n >= 4 and junk[-1] != END else None)]
    before = [SAMPLE, SMALLEST]
    head = journal(before)
    for data in (FORMAT_FRAME, *map(encoded, [SAMPLE, SMALLEST, LARGEST, *rng.sample(commits, 3)])):
        for n in range(1, len(data)):
            junk = rng.randbytes(len(data) - n)
            cases += [stopped(head + data[:n], before, len(head), "short"),
                      stopped(head + data[:n] + bytes(len(data) - n), before, len(head), "unterminated"),
                      stopped(head + data[:n] + junk, before, len(head),
                              "unterminated" if n >= 4 and junk[-1] != END else None)]
    return cases


def tail_cases(rng: random.Random) -> list[Case]:
    """Zeros and junk on both sides of the format's frame and of the largest, where a journal
    starts and after its records; and zeros with records after them, which no torn append
    leaves."""
    cases = []
    for before in (None, [], [SAMPLE, SMALLEST]):
        head = b"" if before is None else journal(before)
        for n in (1, 8, 9, 10, FIRST_FRAME - 1, FIRST_FRAME, FIRST_FRAME + 1, MAX_FRAME - 1, MAX_FRAME,
                  MAX_FRAME + 1, 2 * MAX_FRAME):
            # Zeros are a frame of no payload, short of its end mark or without it.
            cases += [stopped(head + bytes(n), before, len(head), "short" if n < 10 else "unterminated"),
                      stopped(head + rng.randbytes(n), before, len(head), None)]
        cases.append(stopped(head + bytes(10) + AFTER, before, len(head), "unterminated"))
    return cases


def frame_starts(data: bytes) -> list[int]:
    """Where each frame of a journal the lane made starts."""
    starts, at = [], 0
    while at < len(data):
        starts.append(at)
        at += 10 + struct.unpack_from("<I", data, at)[0]
    return starts


def by_construction(data: bytes, start: int, p: int) -> bool:
    """Whether reading refuses the frame at `start` of `data`, whose byte `p` was changed, for a
    reason that does not rest on the CRC-32C missing a change: the CRC-32C's guarantee for a
    change in what it covers or in itself, the end mark, or a length past a payload's or the
    journal's end."""
    if p - start >= 4:
        return True
    length: int = struct.unpack_from("<I", data, start)[0]
    return length > MAX_PAYLOAD or len(data) - start < 10 + length or data[start + 9 + length] != END


def flip_cases(rng: random.Random, commits: list[Commit]) -> tuple[list[Case], int]:
    """Each byte of a journal changed three ways, the journal ending soon after it and with much
    after it: reading stops where the frame of the changed byte starts, whatever the byte was,
    and the records before it are all it reads. Also how many of the cases rest on the CRC-32C not
    matching by chance: a changed length that puts the end mark where one is."""
    chosen = [SMALLEST, *rng.sample([c for c in commits if len(encoded(c)) < 120], 2)]
    base = journal(chosen)
    starts = frame_starts(base)
    cases, chance = [], 0
    for data in (base, base + AFTER):
        for p in range(len(base)):
            k = max(i for i, s in enumerate(starts) if s <= p)
            for mask in (0x01, 0x80, 0xFF):
                changed = bytearray(data)
                changed[p] ^= mask
                cases.append(stopped(bytes(changed), chosen[:k - 1] if k else None, starts[k], None))
                chance += not by_construction(bytes(changed), starts[k], p)
    return cases, chance


def refused_cases() -> list[Case]:
    """Frames that check but hold no record, frames too long, frames without their end mark and
    lengths that run into what follows, each last in a journal and with records after it; and
    journals whose first record is not their format or that hold it twice."""
    commit = payload(SAMPLE)
    refused = [(frame(k, commit), "not-a-record") for k in (0, 3, 0x7F, 0xFF)]
    refused += [(frame(k, MAGIC), "not-a-record") for k in (0, COMMIT, 3)]
    refused += [(frame(FORMAT, m), "not-a-record")
                for m in (MAGIC[:-1] + b"\x02", MAGIC[:-1], MAGIC + b"\0", b"D" + MAGIC[1:], b"", commit)]
    refused += [(frame(COMMIT, commit[:n]), "not-a-record") for n in range(len(commit))]
    refused += [(frame(COMMIT, commit + bytes(n)), "not-a-record") for n in (1, 2, 3)]
    refused += [(frame(COMMIT, payload(c)), "not-a-record") for c, ok in bounded(SAMPLE)
                if not ok and packable(c)]
    refused += [(frame(COMMIT, bytes(MAX_PAYLOAD)), "not-a-record"),
                (frame(COMMIT, payload(LARGEST) + b"\0"), "too-long"),
                (frame(COMMIT, bytes(MAX_PAYLOAD + 1)), "too-long"),
                (frame(COMMIT, commit, length=2**32 - 1), "too-long"),
                (frame(COMMIT, commit, end=0x00), "unterminated"),
                (frame(COMMIT, commit, end=0xFF), "unterminated"),
                (frame(FORMAT, MAGIC, end=0x00), "unterminated")]
    before = [SAMPLE]
    head = journal(before)
    cases = [stopped(head + data + tail, before, len(head), why)
             for data, why in refused for tail in (b"", AFTER)]
    # A length that runs into what follows: short when nothing does, anything torn when it does.
    long_length = frame(COMMIT, commit, length=MAX_PAYLOAD)
    cases += [stopped(head + long_length, before, len(head), "short"),
              stopped(head + long_length + AFTER, before, len(head), None)]
    commit_frame = encoded(SAMPLE)
    # Neither is ever a torn tail, however little follows.
    return [*cases, corrupt(commit_frame, None, 0, "no-format"),
            corrupt(commit_frame + FORMAT_FRAME + AFTER, None, 0, "no-format"),
            corrupt(FORMAT_FRAME * 2, [], len(FORMAT_FRAME), "format-again"),
            corrupt(head + FORMAT_FRAME + commit_frame, before, len(head), "format-again")]


def forged(data: bytes, at: int, target: int) -> bytes:
    """`data` with the four octets at `at` changed so that its CRC-32C is `target`. For inputs of
    one length the CRC-32C is affine over GF(2), so the change is the solution of 32 linear
    equations, one for each bit of the CRC."""
    base = crc32c(data)
    # The rows of an echelon basis: a combination of the CRC's columns and which bits make it.
    rows: list[tuple[int, int]] = []
    for bit in range(32):
        changed = bytearray(data)
        changed[at + bit // 8] ^= 1 << (bit % 8)
        vector, bits = crc32c(bytes(changed)) ^ base, 1 << bit
        for v, b in rows:
            if vector ^ v < vector:
                vector, bits = vector ^ v, bits ^ b
        if vector:
            rows = sorted([*rows, (vector, bits)], reverse=True)
    vector, bits = base ^ target, 0
    for v, b in rows:
        if vector ^ v < vector:
            vector, bits = vector ^ v, bits ^ b
    out = bytearray(data)
    for bit in range(32):
        if bits >> bit & 1:
            out[at + bit // 8] ^= 1 << (bit % 8)
    if vector or crc32c(bytes(out)) != target:
        raise LaneError("four octets could not be chosen to make the CRC-32C wanted")
    return bytes(out)


def cut_and_forged(whole: bytes, n: int, fill: bytes) -> bytes:
    """The first `n` octets of a frame, then `fill`, its last four octets chosen to make the CRC-32C
    the frame's header gives right, and the end mark: to the frame's length."""
    if n < 8 or n + len(fill) + 1 != len(whole):
        raise LaneError("a forged fill has to leave the header whole and end where the frame ends")
    span = whole[:n] + fill
    crc: int = struct.unpack_from("<I", whole, 4)[0]
    return whole[:8] + forged(span[8:], len(span) - 12, crc) + bytes([END])


def forged_cases() -> list[Case]:
    """Appends cut short whose fill is chosen to put the end mark in place and make the CRC-32C
    right, which the proofs assume a crash never leaves: without that, a crash could stop the
    store — a frame that checks but holds no record — or make it read a record nobody wrote."""
    head = journal([SAMPLE])
    whole = encoded(SAMPLE)
    made = cut_and_forged(whole, len(whole) - 13, struct.pack("<III", 1, 2, 0))
    nobody: Commit = (*SAMPLE[:3], 1, 2, struct.unpack_from("<I", made, len(made) - 5)[0])
    return [corrupt(cut_and_forged(FORMAT_FRAME, 8, bytes(len(FORMAT_FRAME) - 9)), None, 0, "not-a-record"),
            corrupt(head + cut_and_forged(whole, 8, bytes(len(whole) - 9)), [SAMPLE], len(head),
                    "not-a-record"),
            clean(head + made, [SAMPLE, nobody])]


def damaged(rng: random.Random, data: bytes, way: int) -> bytes:
    """A journal damaged one of eight ways."""
    p = rng.randrange(len(data))
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
        case _:
            return data[len(FORMAT_FRAME):]


def damaged_cases(rng: random.Random, commits: list[Commit]) -> list[Case]:
    """Journals drawn at random and damaged at random, which both have to answer alike."""
    return [Case(f"scan {hexed(damaged(rng, journal(rng.sample(commits, rng.randint(0, 6))), k % 8))}")
            for k in range(1600)]


# Names


def name_cases(rng: random.Random) -> list[Case]:
    """The names of an article (`parseName_names`), and names the store does not give."""
    seqs = [0, 1, 9, 10, 15, 16, 255, 2**32 - 1, 2**32, 2**63, 2**64 - 1,
            *(rng.getrandbits(64) for _ in range(40))]
    cases = [Case("name " + b"journal".hex(), "journal")]
    for seq in seqs:
        final, temp = b"a%016x" % seq, b"t%016x" % seq
        cases += [Case(f"names {seq}", f"{final.hex()} {temp.hex()}"),
                  Case(f"name {final.hex()}", f"final {seq}"), Case(f"name {temp.hex()}", f"temp {seq}")]
    digits = b"0123456789abcdef"
    others = [b"", b"a", b"t", b"journal\n", b"Journal", b"journals", b"journa", b"journal.tmp", b".", b"..",
              b"a" + digits[:15], b"a" + digits + b"0", b"A" + digits, b"T" + digits, b"a" + digits.upper(),
              b"a" + b"g" + digits[1:], b"b" + digits, b"x" + digits, b" a" + digits, b"a" + digits + b" ",
              b"t" + digits + b"\0", b"a0x" + digits[2:], b"a-" + digits[1:], b"aa" + digits, b"tmp",
              b"lost+found"]
    return cases + [Case(f"name {hexed(n)}", "none") for n in others]


def ending(said: str) -> str:
    """How a journal's answer says it ends: clean, torn, or the reason for corruption."""
    words = said.split(" end ", 1)[-1].removeprefix("end ").split()
    return words[2] if words[0] == "corrupt" else words[0]


def check() -> Report:
    OUT.mkdir(parents=True, exist_ok=True)
    python = str(lanes.pinned_python(REQUIREMENTS))
    implementation = subprocess.run([python, "-c", "import google_crc32c; print(google_crc32c.implementation)"],
                                    capture_output=True, text=True, check=True).stdout.strip()
    if implementation != "c":
        raise LaneError(f"google-crc32c runs its {implementation} implementation, not its C extension")
    rng = random.Random(SEED)  # noqa: S311 -- a fixed seed, so that every run draws the same cases
    steps, mark = {}, time.monotonic()
    if len(encoded(LARGEST)) != MAX_FRAME:
        raise LaneError(f"the largest commit is a frame of {len(encoded(LARGEST))} octets, not {MAX_FRAME}")
    commits = [SAMPLE, SMALLEST, LARGEST, *(random_commit(rng) for _ in range(400)),
               *(random_commit(rng, most=20, groups=3, name=12) for _ in range(200))]
    flips, chance = flip_cases(rng, commits)
    families = {"crc": crc_cases(rng), "encode": encode_cases(commits), "clean": clean_cases(rng, commits),
                "torn": torn_cases(rng, commits), "tails": tail_cases(rng), "flips": flips,
                "refused": refused_cases(), "forged": forged_cases(), "damaged": damaged_cases(rng, commits),
                "names": name_cases(rng)}
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
    library = C.answer_lines([python, str(REFERENCE)], [f"crc-library {ln.split()[1]}" for ln in crcs],
                             C.WORKERS)
    for asked, a, b in zip(crcs, model[:len(crcs)], library, strict=True):
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
                             f"{len(vectors())} examples of RFC 7143", f"{chance} of the {len(flips):,}"],
        "docs/assurance.md": [f"{len(cases):,} cases", f"{len(MUTANTS)} versions of the rules of reading"]})
    return Report("checked", None, [REFERENCE, REQUIREMENTS], {
        "cases": len(cases), "by_family": {k: len(v) for k, v in families.items()},
        "with_answers": sum(1 for c in cases if c.want is not None), "flips_resting_on_chance": chance,
        "refused_lines": len(REFUSED),
        "ends_seen": {r: ends.count(r) for r in ["clean", "torn", *REASONS]},
        "crc_implementation": implementation, "mutants_caught": caught, "seconds_by_step": steps})


def main() -> None:
    lanes.lane_main("JOURNAL", OUT, check)


if __name__ == "__main__":
    main()
