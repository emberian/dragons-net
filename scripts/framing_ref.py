# SPDX-License-Identifier: AGPL-3.0-or-later
"""The framing rules of docs/decisions/0003-nntp-slice.md ("How input is framed"), computed over the
whole stream, apart from the Lean model and the compiled code it is held against.

Nothing here reads a byte at a time or carries state from one chunk to the next: the chunks of a
case are joined first, lines are the pieces between LFs, and a block ends at the first CRLF "."
CRLF of what is left of the stream with a CRLF put before it; the next block starts after it. The
answer has the form `dn-compiler frame-model` prints (see `DN.News.FrameModel`). The state of a
block that has not ended is given as the framer keeps it (its phase, whether it is spoiled, its size
up to one past the buffer and the first bytes it holds), so that part of the answer checks the
framer's representation as well as what it does.
"""
from __future__ import annotations

CR, LF, NUL, DOT = b"\r", b"\n", b"\0", b"."
CRLF = CR + LF
TERMINATOR = CRLF + DOT + CRLF


def hexed(data: bytes) -> str:
    return data.hex() or "-"


def classify(lim: int, body: bytes) -> tuple[str, bytes]:
    """A line, from its bytes before the LF."""
    if len(body) + 1 > lim:
        return "overlong", body[:lim]
    if body.endswith(CR) and CR not in body[:-1] and NUL not in body:
        return "command", body[:-1]
    return "malformed", body


def lines(lim: int, stream: bytes) -> str:
    *bodies, tail = stream.split(LF)
    found = "".join(f" {kind}:{hexed(kept)}" for kind, kept in (classify(lim, b) for b in bodies))
    cr = int(tail.endswith(CR))
    bad = int(NUL in tail or CR in tail[:-1])
    return f"L lines{found} state {min(len(tail), lim)} {cr} {bad} {hexed(tail[:lim])}"


def clean(line: bytes) -> bool:
    return not any(c in line for c in (CR, LF, NUL))


def unstuff(line: bytes) -> bytes:
    return line[1:] if line.startswith(DOT) else line


def ended(cap: int, ls: list[bytes]) -> str:
    """The verdict on a block of the lines `ls`."""
    if not all(clean(line) for line in ls):
        return "refused:-"
    content = b"".join(unstuff(line) + CRLF for line in ls)
    if len(content) > cap:
        return "too-large:-"
    return f"accepted:{hexed(content)}"


def blocks(cap: int, stream: bytes) -> str:
    found = ""
    while (at := (CRLF + stream).find(TERMINATOR)) >= 0:
        region = stream[:at]
        read = at + len(DOT + CRLF)
        found += f" end {ended(cap, region.split(CRLF)[:-1] if region else [])} {read}"
        stream = stream[read:]
    return f"B{found} {unfinished(cap, stream)}"


def unfinished(cap: int, stream: bytes) -> str:
    """A block that has not ended: its phase, whether it is spoiled, its size and what it holds."""
    *ls, rest = stream.split(CRLF)
    if rest == b"":
        phase = "bol"
    elif rest == DOT:
        phase = "dot"
    elif rest == DOT + CR:
        phase = "dotcr"
    elif rest.endswith(CR):
        phase = "cr"
    else:
        phase = "data"
    held = rest[:-1] if rest.endswith(CR) else rest
    bad = int(not all(clean(line) for line in ls) or not clean(held))
    content = b"".join(unstuff(line) + CRLF for line in ls) + unstuff(held)
    return f"open {phase} {bad} {min(len(content), cap + 1)} {hexed(content[:cap])}"


def answer(case: str) -> str:
    """The answer to one case: `L LIM CHUNK...` or `B CAP CHUNK...`."""
    mode, size, *chunks = case.split()
    stream = b"".join(b"" if chunk == "-" else bytes.fromhex(chunk) for chunk in chunks)
    if mode == "L":
        return lines(int(size), stream)
    if mode == "B":
        return blocks(int(size), stream)
    raise ValueError(f"no mode {mode}")
