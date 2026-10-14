#!/usr/bin/env python3
# SPDX-License-Identifier: AGPL-3.0-or-later
"""The independent reference of the store lane: how the store recovers when it starts, as decision
0005 ("On disk") fixes it, written from its text apart from `DN.News.Recovery` and answering the
cases `dn-compiler recovery-model` answers, in the same form. The journal is read by
scripts/store_ref.py, the journal lane's own reference.
"""
from __future__ import annotations

from pathlib import Path
import re
import struct
import sys

sys.path.insert(0, str(Path(__file__).resolve().parent))
import store_ref as J  # the path above is what makes it importable

LIMIT = 2**64
# The most articles the store holds (0005, "Bounds").
CAPACITY = 4096
NAME = re.compile(rb"([atqj])([0-9a-f]{16})")
NUMBER = re.compile(r"[0-9]+")
HEX = re.compile(r"(?:[0-9a-f]{2})*")
# The length of a new journal: its format's frame alone.
FIRST = J.HEADER + len(J.MAGIC) + J.KEY + 1

# What recovery starts with: the journal's key, the next sequence number, where the journal ends, its
# commits, the numbers of the files set aside, and the actions.
Found = tuple[bytes, int, int, list[J.Commit], list[int], list[str]]


class Corrupt(Exception):
    """Why the store does not start."""


def hexed(data: bytes) -> str:
    return data.hex() if data else "-"


def unhex(s: str) -> bytes:
    if s == "-":
        return b""
    if not HEX.fullmatch(s):
        sys.exit(f"not hex: {s}")
    return bytes.fromhex(s)


def entries(s: str, sep: str) -> list[str]:
    if s == "-":
        return []
    out = s.split(sep)
    if any(not e for e in out):
        sys.exit(f"an empty item: {s}")
    return out


def image_of(s: str) -> list[tuple[bytes, bytes]]:
    out = []
    for e in entries(s, ";"):
        parts = e.split("=")
        if len(parts) != 2:
            sys.exit(f"not a file: {e}")
        out.append((unhex(parts[0]), unhex(parts[1])))
    if len({n for n, _ in out}) != len(out):
        sys.exit(f"a name twice: {s}")
    return out


def name_kind(name: bytes) -> tuple[str, int] | None:
    """What a name in the spool directory is and its number, none for the journal, or why the store
    is corrupt."""
    if name == b"journal":
        return None
    m = NAME.fullmatch(name)
    if m is None:
        raise Corrupt(f"bad-name {hexed(name)}")
    return {b"a": "final", b"t": "temp", b"q": "quarantine", b"j": "tail"}[m[1]], int(m[2], 16)


def name_of(letter: str, seq: int) -> bytes:
    return letter.encode() + b"%016x" % seq


def fresh(key: bytes, actions: list[str]) -> Found:
    return key, 1, FIRST, [], [], actions


def check_records(commits: list[J.Commit], groups: list[bytes], files: dict[bytes, bytes]) -> None:
    """The rules across records, after more articles than the store holds, each over the records in
    the journal's order before the next: a number a later record repeats, a group the configuration
    lacks, an article number not above, a file missing or of another size."""
    if len(commits) > CAPACITY:
        raise Corrupt(f"too-many {len(commits)}")
    for at, c in enumerate(commits):
        if any(later[0] == c[0] for later in commits[at + 1:]):
            raise Corrupt(f"seq-twice {c[0]}")
    for c in commits:
        for name, _ in c[2]:
            if name not in groups:
                raise Corrupt(f"unknown-group {hexed(name)}")
    highest: dict[bytes, int] = {}
    for c in commits:
        for name, number in c[2]:
            if number <= highest.get(name, 0):
                raise Corrupt(f"number-not-above {hexed(name)} {number}")
        for name, number in c[2]:
            highest[name] = max(highest.get(name, 0), number)
    for c in commits:
        held = files.get(name_of("a", c[0]))
        if held is None:
            raise Corrupt(f"missing-file {c[0]}")
        if len(held) != c[4]:
            raise Corrupt(f"wrong-size {c[0]}")


def recover(key: bytes, groups: list[bytes], image: list[tuple[bytes, bytes]]) -> Found:
    """The store recovery starts with, as a tuple, or `Corrupt`."""
    if len(key) != J.KEY:
        raise Corrupt("bad-key")
    kinds = [(name, k[0], k[1]) for name, _ in image if (k := name_kind(name)) is not None]
    files = dict(image)
    if b"journal" not in files:
        if image:
            raise Corrupt("no-journal")
        return fresh(key, [f"create:{hexed(key)}", "sync-dir"])
    content = files[b"journal"]
    records, ending = J.scan(content)
    words = ending.split(" ")
    if words[0] == "corrupt":
        raise Corrupt(f"journal {words[1]} {words[2]}")
    if not records:
        # Only a format cut short is left: made again when nothing else is there.
        if len(image) != 1:
            raise Corrupt("no-journal")
        return fresh(key, [f"create:{hexed(key)}"])
    if not isinstance(records[0], bytes):
        raise Corrupt("journal 0 not-a-record")
    commits = [r for r in records[1:] if isinstance(r, tuple)]
    check_records(commits, groups, files)
    cut = int(words[1]) if words[0] == "torn" else None
    numbers = [c[0] for c in commits] + [seq for _, _, seq in kinds]
    first_free = max(numbers, default=0) + 1
    nxt = first_free + 1 if cut is not None else first_free
    if nxt >= LIMIT:
        raise Corrupt("exhausted")
    actions: list[str] = []
    aside: list[int] = []
    if cut is not None:
        kept = struct.pack("<Q", cut) + content[cut:]
        actions += [f"keep:{name_of('j', first_free).hex()}:{kept.hex()}", "sync-dir", f"cut:{cut}"]
    recorded = {c[0] for c in commits}
    quarantined = {seq for _, kind, seq in kinds if kind == "quarantine"}
    tails = [seq for _, kind, seq in kinds if kind == "tail"]
    tidied = []
    for name, kind, seq in kinds:
        if kind == "temp":
            tidied.append(f"remove:{name.hex()}")
        elif kind == "final" and seq not in recorded:
            # Set aside when a torn tail or a tail kept above it may have held its record.
            may_have = cut is not None or any(seq < t for t in tails)
            if seq in quarantined or not may_have:
                tidied.append(f"remove:{name.hex()}")
            else:
                tidied.append(f"rename:{name.hex()}:{name_of('q', seq).hex()}")
                aside.append(seq)
        elif kind in ("quarantine", "tail"):
            aside.append(seq)
    actions += tidied + (["sync-dir"] if tidied else [])
    if cut is not None:
        aside.append(first_free)
    end = cut if cut is not None else len(content)
    return records[0], nxt, end, commits, aside, actions


def finding(key: bytes, groups: list[bytes], image: list[tuple[bytes, bytes]]) -> str:
    try:
        journal_key, nxt, end, commits, aside, actions = recover(key, groups, image)
    except Corrupt as why:
        return f"corrupt {why}"
    listed = ";".join(J.show(c) for c in commits) or "-"
    numbers = ",".join(map(str, aside)) or "-"
    done = ";".join(actions) or "-"
    return f"ok {hexed(journal_key)} {nxt} {end} {listed} {numbers} {done}"


def apply(image: list[tuple[bytes, bytes]], actions: list[str]) -> list[tuple[bytes, bytes]]:
    """The directory once the actions are done and durable."""
    files = list(image)

    def put(name: bytes, data: bytes) -> None:
        files[:] = [f for f in files if f[0] != name] + [(name, data)]

    for action in actions:
        parts = action.split(":")
        match parts:
            case ["keep", name, data]:
                put(unhex(name), unhex(data))
            case ["rename", src, dst]:
                held = next((d for n, d in files if n == unhex(src)), None)
                if held is not None:
                    files[:] = [f for f in files if f[0] != unhex(src)]
                    put(unhex(dst), held)
            case ["remove", name]:
                files[:] = [f for f in files if f[0] != unhex(name)]
            case ["sync-dir"]:
                pass
            case ["cut", n]:
                if not NUMBER.fullmatch(n):
                    sys.exit(f"not a number: {n}")
                files[:] = [(f, d[:int(n)] if f == b"journal" else d) for f, d in files]
            case ["create", key]:
                k = unhex(key)
                if len(k) != J.KEY:
                    sys.exit(f"not a key: {key}")
                put(b"journal", J.frame(k, 0, J.FORMAT, J.MAGIC + k))
            case _:
                sys.exit(f"not an action: {action}")
    return files


def answer(line: str) -> str:
    match line.split(" "):
        case ["recover", key, groups, image]:
            return finding(unhex(key), [unhex(g) for g in entries(groups, ",")], image_of(image))
        case ["apply", image, actions]:
            done = apply(image_of(image), entries(actions, ";"))
            return ";".join(f"{hexed(n)}={hexed(d)}" for n, d in done) or "-"
    sys.exit(f"not a case: {line}")


def main() -> None:
    lines = sys.stdin.buffer.read().decode().split("\n")
    sys.stdout.write("".join(answer(line) + "\n" for line in lines if line))


if __name__ == "__main__":
    main()
