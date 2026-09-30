#!/usr/bin/env python3
# SPDX-License-Identifier: AGPL-3.0-or-later
"""The independent reference of the journal lane: the store's journal and the names of its files,
as decision 0005 ("On disk") fixes them, written apart from `DN.News.Journal` and answering the
cases `dn-compiler journal-model` answers, in the same form. The CRC-32C is computed a byte at a
time from a table of remainders, not a bit at a time as the specification does; asked as
`crc-library`, it is google-crc32c's instead, a third implementation. Run by the Python of
scripts/requirements-tests.txt, which pins that library.
"""
from __future__ import annotations

import re
import struct
import sys

import google_crc32c


def table() -> list[int]:
    """The remainder each byte leaves, for Castagnoli's reflected polynomial."""
    out = []
    for byte in range(256):
        crc = byte
        for _ in range(8):
            crc = (crc >> 1) ^ 0x82F63B78 if crc & 1 else crc >> 1
        out.append(crc)
    return out


TABLE = table()
FORMAT, COMMIT = 1, 2
MAGIC = b"dragons-net journal\x01"
END = 0xA5
# The largest commit: an identifier of 250 octets and 16 groups named in 64.
MAX_PAYLOAD = 8 + 1 + 250 + 1 + 16 * (1 + 64 + 4) + 3 * 4
MAX_FRAME = 9 + MAX_PAYLOAD + 1
# Before any record, only the format's frame can have been cut short.
FIRST_FRAME = 9 + len(MAGIC) + 1
# What an append the crash cut short can leave.
TORN = {"short", "too-long", "unterminated", "checksum"}
NAME = re.compile(rb"([at])([0-9a-f]{16})")
NUMBER = re.compile(r"[0-9]+")
HEX = re.compile(r"(?:[0-9a-f]{2})*")

Group = tuple[bytes, int]
Commit = tuple[int, bytes, list[Group], int, int, int]
# A record is a commit or, for the format record, "F".
Record = Commit | str


def crc32c(data: bytes) -> int:
    crc = 0xFFFFFFFF
    for byte in data:
        crc = TABLE[(crc ^ byte) & 0xFF] ^ (crc >> 8)
    return crc ^ 0xFFFFFFFF


def fits(c: Commit) -> bool:
    """Whether a correct store writes the commit: numbered from 1, its groups named once each,
    with the article numbers RFC 3977 §6 allows, and a header no larger than the file."""
    seq, message_id, groups, header, size, crc = c
    names = [name for name, _ in groups]
    return (1 <= seq < 2**64 and 1 <= len(message_id) <= 250 and 1 <= len(groups) <= 16
            and all(1 <= len(name) <= 64 and 1 <= number <= 2_147_483_647 for name, number in groups)
            and len(set(names)) == len(names) and header <= size < 2**32 and crc < 2**32)


def payload(c: Commit) -> bytes:
    seq, message_id, groups, header, size, crc = c
    named = b"".join(bytes([len(name)]) + name + struct.pack("<I", number) for name, number in groups)
    return (struct.pack("<QB", seq, len(message_id)) + message_id + bytes([len(groups)]) + named
            + struct.pack("<III", header, size, crc))


def frame(kind: int, body: bytes) -> bytes:
    return struct.pack("<IIB", len(body), crc32c(bytes([kind]) + body), kind) + body + bytes([END])


def decode(body: bytes) -> Commit | None:
    """The commit a payload holds, if it holds exactly one that a correct store writes."""
    # Each read past the end raises, so a slice that came out short is never kept.
    try:
        seq, n = struct.unpack_from("<QB", body)
        message_id = body[9:9 + n]
        at = 9 + n
        count = body[at]
        at += 1
        groups = []
        for _ in range(count):
            n = body[at]
            (number,) = struct.unpack_from("<I", body, at + 1 + n)
            groups.append((body[at + 1:at + 1 + n], number))
            at += 1 + n + 4
        header, size, crc = struct.unpack_from("<III", body, at)
    except (IndexError, struct.error):
        return None
    c = (seq, message_id, groups, header, size, crc)
    return c if at + 12 == len(body) and fits(c) else None


def record_of(kind: int, body: bytes) -> Record | None:
    if kind == FORMAT and body == MAGIC:
        return "F"
    return decode(body) if kind == COMMIT else None


def read_frame(rest: bytes) -> str | tuple[Record, int]:
    """Why the frame at the start of `rest` does not check, or the record it holds and its size."""
    if len(rest) < 9:
        return "short"
    length, crc, kind = struct.unpack_from("<IIB", rest)
    if length > MAX_PAYLOAD:
        return "too-long"
    if len(rest) < 10 + length:
        return "short"
    if rest[9 + length] != END:
        return "unterminated"
    if crc32c(rest[8:9 + length]) != crc:
        return "checksum"
    record = record_of(kind, rest[9:9 + length])
    return "not-a-record" if record is None else (record, 10 + length)


def scan(data: bytes) -> tuple[list[Record], str]:
    """The records a journal holds and how it ends."""
    records: list[Record] = []
    at = 0
    while at < len(data):
        got = read_frame(data[at:])
        if isinstance(got, str):
            bound = MAX_FRAME if records else FIRST_FRAME
            torn = got in TORN and len(data) - at <= bound
            return records, f"torn {at}" if torn else f"corrupt {at} {got}"
        record, taken = got
        if not records and record != "F":
            return [], f"corrupt {at} no-format"
        if records and record == "F":
            return records, f"corrupt {at} format-again"
        records.append(record)
        at += taken
    return records, "clean"


def show(record: Record) -> str:
    if isinstance(record, str):
        return record
    seq, message_id, groups, header, size, crc = record
    listed = ",".join(f"{name.hex()}={number}" for name, number in groups)
    return f"C:{seq}:{message_id.hex()}:{header}:{size}:{crc}:{listed}"


def unhex(s: str) -> bytes:
    if s == "-":
        return b""
    if not HEX.fullmatch(s):
        sys.exit(f"not hex: {s}")
    return bytes.fromhex(s)


def nat(s: str) -> int:
    if not NUMBER.fullmatch(s):
        sys.exit(f"not a number: {s}")
    return int(s)


def group(s: str) -> Group:
    name, number = s.split("=")
    return unhex(name), nat(number)


def answer(line: str) -> str:
    match line.split(" "):
        case ["crc", data]:
            return str(crc32c(unhex(data)))
        case ["crc-library", data]:
            return str(google_crc32c.value(unhex(data)))
        case ["encode", seq, message_id, header, size, crc, groups]:
            listed = [] if groups == "-" else [group(g) for g in groups.split(",")]
            c = (nat(seq), unhex(message_id), listed, nat(header), nat(size), nat(crc))
            return frame(COMMIT, payload(c)).hex() if fits(c) else "not-ok"
        case ["scan", data]:
            records, ending = scan(unhex(data))
            return " ".join([*map(show, records), "end", ending])
        case ["name", data]:
            name = unhex(data)
            if name == b"journal":
                return "journal"
            m = NAME.fullmatch(name)
            if m is None:
                return "none"
            return f"{'final' if m[1] == b'a' else 'temp'} {int(m[2], 16)}"
        case ["names", seq]:
            number = nat(seq)
            if number >= 2**64:
                sys.exit(f"not a sequence number: {seq}")
            digits = b"%016x" % number
            return f"{(b'a' + digits).hex()} {(b't' + digits).hex()}"
    sys.exit(f"not a case: {line}")


def main() -> None:
    sys.stdout.write("".join(answer(line.rstrip("\n")) + "\n" for line in sys.stdin if line.strip()))


if __name__ == "__main__":
    main()
