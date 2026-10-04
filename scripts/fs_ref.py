#!/usr/bin/env python3
# SPDX-License-Identifier: AGPL-3.0-or-later
"""The independent reference of the file system lane: the file system the store runs on and what a
crash may leave of it, as decision 0005 states them ("File operations through the host" and the
model of crashes under "What is proved and what is tested"), written from its text apart from
`DN.News.FsModel` and answering the cases `dn-compiler fs-model` answers, in the same form:

- a name holds a file or nothing; a crash leaves it holding what it held at the directory's last
  sync or anything it has held since; a sync of the directory, while trusted, makes the names as
  they are durable;
- a file's octets: those no operation touched since its last sync, then any octets, up to the most
  it has held since; a sync of the file, while trusted, makes it durable as it is;
- a failed operation may have done any part of what it was asked: an append, any first part of its
  octets; a sync of a file or of the directory, nothing for certain, and no later sync of it is
  trusted; anything else, all or nothing.

Octets are written in hex, `-` for none and never as an empty text.
"""
from __future__ import annotations

from dataclasses import dataclass, field
import itertools
import random
import re
import sys

NUMBER = re.compile(r"[0-9]+")
HEX = re.compile(r"(?:[0-9a-f]{2})+")


@dataclass
class File:
    seen: bytes = b""
    # the octets no operation has touched since the last sync, and the most it has held since
    kept: bytes = b""
    most: int = 0
    trusted: bool = True
    # since the last sync: the last octets written at each place, which a cut does not take back,
    # and each append with where it was made
    latest: bytes = b""
    appends: list[tuple[int, bytes]] = field(default_factory=list)


@dataclass
class Name:
    # what the name held at the directory's last sync, and everything it has held since
    synced: int | None = None
    since: list[int | None] = field(default_factory=list)

    def now(self) -> int | None:
        return self.since[-1] if self.since else self.synced


@dataclass
class Disk:
    names: dict[bytes, Name] = field(default_factory=dict)
    files: list[File] = field(default_factory=list)
    dir_trusted: bool = True

    def holding(self, name: bytes) -> int | None:
        n = self.names.get(name)
        return None if n is None else n.now()

    def bind(self, name: bytes, f: int | None) -> None:
        self.names.setdefault(name, Name()).since.append(f)

    def file(self, f: int) -> File | None:
        return self.files[f] if f < len(self.files) else None


def hexed(data: bytes) -> str:
    return data.hex() or "-"


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


def entries(s: str, sep: str) -> list[str]:
    if s == "-":
        return []
    out = s.split(sep)
    if any(not e for e in out):
        sys.exit(f"an empty item: {s}")
    return out


def image_of(s: str) -> dict[bytes, bytes]:
    out: dict[bytes, bytes] = {}
    for e in entries(s, ";"):
        parts = e.split("=")
        if len(parts) != 2 or unhex(parts[0]) in out:
            sys.exit(f"not an image: {s}")
        out[unhex(parts[0])] = unhex(parts[1])
    return out


Op = tuple[str, list[str]]


def op_of(s: str) -> tuple[Op, int | None]:
    body, failed, k = s.partition("!")
    kind, *args = body.split(":")
    shapes = {"create": 1, "open": 1, "append": 2, "truncate": 2, "sync": 1, "read": 3, "size": 1,
              "rename": 2, "remove": 1, "sync-dir": 0, "list": 0}
    if shapes.get(kind) != len(args):
        sys.exit(f"not an operation: {s}")
    for a, number in zip(args, {"append": [1, 0], "truncate": [1, 1], "read": [1, 1, 1], "sync": [1],
                                "size": [1]}.get(kind, [0] * len(args)), strict=True):
        (nat if number else unhex)(a)
    return (kind, args), (nat(k) if failed else None)


def do(d: Disk, op: Op) -> str:
    """What an operation does when it succeeds, and what it answers."""
    kind, args = op
    match kind:
        case "create":
            name = unhex(args[0])
            if d.holding(name) is not None:
                return "exists"
            d.files.append(File())
            d.bind(name, len(d.files) - 1)
            return f"file:{len(d.files) - 1}"
        case "open":
            f = d.holding(unhex(args[0]))
            return "missing" if f is None else f"file:{f}"
        case "rename":
            src, dst = unhex(args[0]), unhex(args[1])
            f = d.holding(src)
            if f is None:
                return "missing"
            if d.holding(dst) != f:
                d.bind(dst, f)
                d.bind(src, None)
            return "done"
        case "remove":
            name = unhex(args[0])
            if d.holding(name) is None:
                return "missing"
            d.bind(name, None)
            return "done"
        case "sync-dir":
            if d.dir_trusted:
                d.names = {n: Name(h.now()) for n, h in d.names.items() if h.now() is not None}
            return "done"
        case "list":
            held = sorted(n for n, h in d.names.items() if h.now() is not None)
            return "names:" + (",".join(map(hexed, held)) or "-")
    data = d.file(nat(args[0]))
    if data is None:
        return "missing"
    match kind:
        case "append":
            at, octets = len(data.seen), unhex(args[1])
            data.seen += octets
            data.most = max(data.most, len(data.seen))
            data.latest = data.latest[:at].ljust(at, b"\x00") + octets + data.latest[at + len(octets):]
            data.appends.append((at, octets))
        case "truncate":
            n = nat(args[1])
            data.seen = data.seen[:n] + bytes(max(0, n - len(data.seen)))
            data.kept = data.kept[:n]
            data.most = max(data.most, n)
            data.latest = data.latest.ljust(n, b"\x00")
        case "sync":
            if data.trusted:
                data.kept, data.most = data.seen, len(data.seen)
                data.latest, data.appends = data.seen, []
        case "read":
            at, n = nat(args[1]), nat(args[2])
            return f"bytes:{hexed(data.seen[at:at + n])}"
        case "size":
            return f"size:{len(data.seen)}"
    return "done"


def fail(d: Disk, op: Op, k: int) -> None:
    """What the `k`-th way of the operation failing leaves."""
    kind, args = op
    if kind == "append":
        octets = unhex(args[1])
        if k > len(octets):
            sys.exit(f"no such failure: {kind} {k}")
        do(d, ("append", [args[0], octets[:k].hex() or "-"]))
    elif kind == "sync":
        if k != 0:
            sys.exit(f"no such failure: {kind} {k}")
        f = d.file(nat(args[0]))
        if f is not None:
            f.trusted = False
    elif kind == "sync-dir":
        if k != 0:
            sys.exit(f"no such failure: {kind} {k}")
        d.dir_trusted = False
    elif k == 1:
        do(d, op)
    elif k != 0:
        sys.exit(f"no such failure: {kind} {k}")


def run(ops: str) -> tuple[list[str], Disk]:
    d = Disk()
    said = []
    for s in entries(ops, ";"):
        op, k = op_of(s)
        if k is None:
            said.append(do(d, op))
        else:
            fail(d, op, k)
            said.append("failed")
    return said, d


def image(d: Disk) -> dict[bytes, bytes]:
    out = {}
    for n, h in d.names.items():
        f = h.now()
        if f is not None:
            out[n] = d.files[f].seen
    return out


def shown(img: dict[bytes, bytes]) -> str:
    return ";".join(f"{hexed(n)}={hexed(o)}" for n, o in sorted(img.items())) or "-"


def allowed(f: File, octets: bytes) -> bool:
    return octets.startswith(f.kept) and len(octets) <= f.most


def may_leave(d: Disk, img: dict[bytes, bytes]) -> bool:
    """Whether a crash may leave the names holding what `img` says: each name what it held at the
    last sync of the directory or since, a name left holding nothing absent; each file one octets,
    allowed by its rule."""
    if any(n not in d.names for n in img):
        return False
    choices: list[list[tuple[bytes, int | None]]] = []
    for n, h in d.names.items():
        held = {h.synced, *h.since}
        if n in img:
            choices.append([(n, f) for f in held if f is not None and allowed(d.files[f], img[n])])
        else:
            choices.append([(n, None)] if None in held else [])
    for picked in itertools.product(*choices):
        content: dict[int, bytes] = {}
        if all(content.setdefault(f, img[n]) == img[n] for n, f in picked if f is not None):
            return True
    return False


def octets_by_kind(f: File) -> dict[str, list[bytes]]:
    """Octets a crash may leave a file holding, by kind: what is kept, alone or followed by zeros or
    0xff up to the most the file has held; what the program sees cut at each length, alone or followed
    by zeros or 0xff; the last octets written at each place, which a cut does not take back, cut at
    each length; an append made past what is kept whole, those before it zeros; and what the program
    sees with one such append lost."""
    k, most = len(f.kept), f.most
    cuts = range(k, min(len(f.seen), most) + 1)
    kinds = {
        "kept": [f.kept, f.kept + bytes(most - k), f.kept + b"\xff" * (most - k)],
        "cut": [f.seen[:m] for m in cuts],
        "cut-then-zeros": [f.seen[:m] + bytes(most - m) for m in cuts],
        "cut-then-junk": [f.seen[:m] + b"\xff" * (most - m) for m in cuts],
        "latest": [f.latest[:m] for m in range(k, min(len(f.latest), most) + 1)],
        "later-whole": [f.kept + bytes(at - k) + octets for at, octets in f.appends if at >= k],
        "one-lost": [f.seen[:at] + bytes(len(octets)) + f.seen[at + len(octets):] for at, octets in f.appends
                     if at >= k],
    }
    return {kind: list(dict.fromkeys(o for o in found if allowed(f, o))) for kind, found in kinds.items()}


def octets_of(f: File) -> list[bytes]:
    """Octets a crash may leave a file holding, each kind `octets_by_kind` lists."""
    return list(dict.fromkeys(o for found in octets_by_kind(f).values() for o in found))


def leavings(d: Disk) -> list[dict[bytes, bytes]]:
    """Images a crash may leave, a few for each file: what is kept, what the program sees, each
    length between, zeros or 0xff after what is kept, up to the most the file has held."""
    per_name = []
    for n, h in d.names.items():
        per_name.append([(n, f) for f in dict.fromkeys([h.synced, *h.since])])
    found = []
    for picked in itertools.islice(itertools.product(*per_name), 64):
        files = sorted({f for _, f in picked if f is not None})
        for contents in itertools.islice(itertools.product(*(octets_of(d.files[f]) for f in files)), 64):
            given = dict(zip(files, contents, strict=True))
            found.append({n: given[f] for n, f in picked if f is not None})
    return list({shown(i): i for i in found}.values())


def leaving(d: Disk, rng: random.Random) -> dict[bytes, bytes]:
    """An image a crash may leave: each name holding what it held at the last sync of the directory
    or since, each file octets of a kind `octets_by_kind` lists, the kind drawn first."""
    files: dict[int, bytes] = {}
    out = {}
    for n, h in d.names.items():
        f = rng.choice(list(dict.fromkeys([h.synced, *h.since])))
        if f is not None:
            if f not in files:
                kinds = [found for found in octets_by_kind(d.files[f]).values() if found]
                files[f] = rng.choice(rng.choice(kinds))
            out[n] = files[f]
    return out


def answer(line: str) -> str:
    match line.split(" "):
        case ["run", ops]:
            said, d = run(ops)
            return f"{';'.join(said) or '-'} {shown(image(d))}"
        case ["crash", ops, img]:
            _, d = run(ops)
            return "yes" if may_leave(d, image_of(img)) else "no"
        case ["leavings", ops]:
            _, d = run(ops)
            return " ".join(shown(i) for i in leavings(d))
    sys.exit(f"not a case: {line}")


def main() -> None:
    lines = sys.stdin.buffer.read().decode().split("\n")
    sys.stdout.write("".join(answer(line) + "\n" for line in lines if line))


if __name__ == "__main__":
    main()
