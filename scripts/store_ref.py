#!/usr/bin/env python3
# SPDX-License-Identifier: AGPL-3.0-or-later
"""The independent reference of the journal lane: the store's journal and the names of its files,
as decision 0005 ("On disk") fixes them, written apart from `DN.News.Journal` and answering the
cases `dn-compiler journal-model` answers, in the same form. SipHash-2-4 is written from the
authors' paper as a loop over the message's words; the CRC-32C a byte at a time from a table of
remainders, not a bit at a time as the specification does; asked as `crc-library`, it is
google-crc32c's instead, a third implementation. Run by the Python of
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
FORMAT, COMMIT, START = 1, 2, 3
TITLE = b"dragons-net journal"
MAGIC = TITLE + b"\x01"
KEY = 16
END = 0xA5
# The length, the tag and the type.
HEADER = 4 + 8 + 1
# The largest commit: an identifier of 250 octets and 16 groups named in 64.
MAX_PAYLOAD = 8 + 1 + 250 + 1 + 16 * (1 + 64 + 4) + 3 * 4
MAX_FRAME = HEADER + MAX_PAYLOAD + 1
# Before any record, only the format's frame can have been cut short.
FIRST_FRAME = HEADER + len(MAGIC) + KEY + 1
# What an append the crash cut short can leave.
TORN = {"short", "too-long", "unterminated", "tag"}
MASK = (1 << 64) - 1
NAME = re.compile(rb"([atqj])([0-9a-f]{16})")
NUMBER = re.compile(r"[0-9]+")
HEX = re.compile(r"(?:[0-9a-f]{2})*")

Group = tuple[bytes, int]
Commit = tuple[int, bytes, list[Group], int, int, int]
# A record is a commit, the key the format record carries, or a start.
Record = Commit | bytes | str


def rotl(x: int, b: int) -> int:
    return ((x << b) | (x >> (64 - b))) & MASK


def siphash(key: bytes, msg: bytes) -> int:
    """SipHash-2-4 with a tag of 64 bits (Aumasson and Bernstein, 2012)."""
    k0, k1 = struct.unpack("<QQ", key)
    v: list[int] = [k0 ^ 0x736F6D6570736575, k1 ^ 0x646F72616E646F6D, k0 ^ 0x6C7967656E657261,
         k1 ^ 0x7465646279746573]

    def rounds(n: int) -> None:
        for _ in range(n):
            v[0] = (v[0] + v[1]) & MASK
            v[1] = rotl(v[1], 13) ^ v[0]
            v[0] = rotl(v[0], 32)
            v[2] = (v[2] + v[3]) & MASK
            v[3] = rotl(v[3], 16) ^ v[2]
            v[0] = (v[0] + v[3]) & MASK
            v[3] = rotl(v[3], 21) ^ v[0]
            v[2] = (v[2] + v[1]) & MASK
            v[1] = rotl(v[1], 17) ^ v[2]
            v[2] = rotl(v[2], 32)

    whole = len(msg) - len(msg) % 8
    words = [m for (m,) in struct.iter_unpack("<Q", msg[:whole])]
    words.append((len(msg) & 0xFF) << 56 | int.from_bytes(msg[whole:], "little"))
    for m in words:
        v[3] ^= m
        rounds(2)
        v[0] ^= m
    v[2] ^= 0xFF
    rounds(4)
    return v[0] ^ v[1] ^ v[2] ^ v[3]


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


def frame(key: bytes, offset: int, kind: int, body: bytes) -> bytes:
    tag = siphash(key, struct.pack("<QB", offset, kind) + body)
    return struct.pack("<IQB", len(body), tag, kind) + body + bytes([END])


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


def key_in(kind: int, body: bytes) -> bytes | None:
    """The key a frame of the format's shape carries: the journal's title, a version, a key."""
    if kind == FORMAT and len(body) == len(MAGIC) + KEY and body.startswith(TITLE):
        return body[len(MAGIC):]
    return None


def record_of(kind: int, body: bytes) -> Record | None:
    if kind == FORMAT:
        return body[len(MAGIC):] if len(body) == len(MAGIC) + KEY and body.startswith(MAGIC) else None
    if kind == START:
        return "start" if not body else None
    return decode(body) if kind == COMMIT else None


def read_frame(data: bytes, at: int, key: bytes | None) -> str | tuple[Record, int]:
    """Why the frame at offset `at` of `data` does not check, or the record it holds and its size;
    `key` is the journal's, once its format has been read."""
    left = len(data) - at
    if left < HEADER:
        return "short"
    length, tag, kind = struct.unpack_from("<IQB", data, at)
    if length > MAX_PAYLOAD:
        return "too-long"
    if left < HEADER + length + 1:
        return "short"
    if data[at + HEADER + length] != END:
        return "unterminated"
    body = data[at + HEADER:at + HEADER + length]
    checking = key if key is not None else key_in(kind, body)
    if checking is None or siphash(checking, struct.pack("<QB", at, kind) + body) != tag:
        return "tag"
    record = record_of(kind, body)
    return "not-a-record" if record is None else (record, HEADER + length + 1)


def checks_after(data: bytes, at: int, key: bytes) -> bool:
    """Whether a frame whose tag the key makes starts anywhere in `data` after offset `at`."""
    for p in range(at + 1, len(data)):
        got = read_frame(data, p, key)
        if not isinstance(got, str) or got == "not-a-record":
            return True
    return False


def scan(data: bytes) -> tuple[list[Record], str]:
    """The records a journal holds and how it ends."""
    records: list[Record] = []
    key: bytes | None = None
    at = 0
    while at < len(data):
        got = read_frame(data, at, key)
        if isinstance(got, str):
            bound = MAX_FRAME if key is not None else FIRST_FRAME
            torn = (got in TORN and len(data) - at <= bound
                    and (key is None or not checks_after(data, at, key)))
            return records, f"torn {at}" if torn else f"corrupt {at} {got}"
        record, taken = got
        if records and isinstance(record, bytes):
            return records, f"corrupt {at} format-again"
        if isinstance(record, bytes):
            key = record
        records.append(record)
        at += taken
    return records, "clean"


def show(record: Record) -> str:
    if isinstance(record, bytes):
        return f"F:{record.hex()}"
    if isinstance(record, str):
        return "S"
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
    parts = s.split("=")
    if len(parts) != 2:
        sys.exit(f"not a group: {s}")
    return unhex(parts[0]), nat(parts[1])


def key_of(s: str) -> bytes:
    key = unhex(s)
    if len(key) != KEY:
        sys.exit(f"not a key: {s}")
    return key


def answer(line: str) -> str:
    match line.split(" "):
        case ["crc", data]:
            return str(crc32c(unhex(data)))
        case ["crc-library", data]:
            return str(google_crc32c.value(unhex(data)))
        case ["siphash", key, data]:
            return str(siphash(key_of(key), unhex(data)))
        case ["format", key]:
            return frame(key_of(key), 0, FORMAT, MAGIC + key_of(key)).hex()
        case ["start", key, offset]:
            at = nat(offset)
            if at >= 2**64:
                sys.exit(f"not an offset: {offset}")
            return frame(key_of(key), at, START, b"").hex()
        case ["encode", key, offset, seq, message_id, header, size, crc, groups]:
            at = nat(offset)
            if at >= 2**64:
                sys.exit(f"not an offset: {offset}")
            listed = [] if groups == "-" else [group(g) for g in groups.split(",")]
            c = (nat(seq), unhex(message_id), listed, nat(header), nat(size), nat(crc))
            return frame(key_of(key), at, COMMIT, payload(c)).hex() if fits(c) else "not-ok"
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
            kind = {b"a": "final", b"t": "temp", b"q": "quarantine", b"j": "tail"}[m[1]]
            return f"{kind} {int(m[2], 16)}"
        case ["names", seq]:
            number = nat(seq)
            if number >= 2**64:
                sys.exit(f"not a sequence number: {seq}")
            digits = b"%016x" % number
            return " ".join((letter + digits).hex() for letter in (b"a", b"t", b"q", b"j"))
    sys.exit(f"not a case: {line}")


def main() -> None:
    # Lines end in LF alone, as the model reads them: a CR is part of its line.
    lines = sys.stdin.buffer.read().decode().split("\n")
    sys.stdout.write("".join(answer(line) + "\n" for line in lines if line))


if __name__ == "__main__":
    main()
