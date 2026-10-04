# SPDX-License-Identifier: AGPL-3.0-or-later
"""The session of docs/decisions/0003-nntp-slice.md judged from outside, apart from the Lean model
(`DN.News.SessionSpec`) it is held against.

A trace is what a host saw, turn by turn: the time, the events it reported, the actions the program
answered with, how much of each send it took, and the time the program asked to be woken at. From
the bytes each connection sent, split at LF and each line classified by RFC 3977 and 0003, `judge`
computes what the client should have received — the greeting, then one reply per command line, in
order, up to and including the reply to QUIT — and from the times things happened, when each of the
three deadlines of 0003 passes. It does not run an automaton: the replies come from the whole input
received so far, and the deadlines from what the host saw.

Every turn is judged: each send is the next whole reply, or the rest of an untaken one once the host
reported the connection ready to write; the program asks to read exactly when every whole line is
answered and the connection takes commands; a connection is greeted in the turn it opens, closed at
once exactly when a deadline has passed, and closed gracefully only when everything is answered and
taken after a QUIT or the end of input; nothing is left waiting; and the next turn is at once when a
connection can go on, else exactly at the earliest deadline.
"""
from __future__ import annotations

from dataclasses import dataclass, field
import re
from typing import NamedTuple

import framing_ref

FIRST_COMMAND, INACTIVITY, LINE_TIME = 10_000, 1_800_000, 180_000
LINE_LIMIT, CHUNK, CONNS = 512, 512, 64
COMMANDS = (b"CAPABILITIES", b"HELP", b"QUIT", b"HEAD", b"STAT")


def words(kept: bytes) -> list[bytes]:
    return [w for w in re.split(rb"[ \t]+", kept) if w]


def is_article_number(w: bytes) -> bool:
    """RFC 3977 §6 and §9.8: at most sixteen digits, no more than 2,147,483,647."""
    return re.fullmatch(rb"[0-9]{1,16}", w) is not None and int(w) <= 2_147_483_647


def is_message_id(w: bytes) -> bool:
    """RFC 3977 §3.6 and §9.8: "<", 1 to 248 printable octets other than ">", ">"."""
    return re.fullmatch(rb"<[\x21-\x3d\x3f-\x7e]{1,248}>", w) is not None


def is_keyword(w: bytes) -> bool:
    """RFC 3977 §9.8: a letter, then two or more letters, digits, dots or hyphens."""
    return re.fullmatch(rb"[A-Za-z][A-Za-z0-9.-]{2,}", w) is not None


def reply(kind: str, kept: bytes) -> str:
    """The reply 0003 gives a line of this kind keeping these bytes."""
    ws = words(kept)
    if not ws:
        return "unknown" if kind == "overlong" else "ignore"
    name, args = ws[0].upper(), ws[1:]
    if name not in COMMANDS:
        return "unknown"
    if kind != "command":
        return "syntax"
    if name == b"CAPABILITIES" and (not args or (len(args) == 1 and is_keyword(args[0]))):
        return "capabilities"
    if name in (b"HELP", b"QUIT") and not args:
        return name.decode().lower()
    if name in (b"HEAD", b"STAT") and len(args) <= 1:
        if not args or is_article_number(args[0]):
            return "no-group"
        if is_message_id(args[0]):
            return "no-such-id"
    return "syntax"


def texts(revision: bytes, source: bytes) -> dict[str, bytes]:
    return {
        "greeting": b"201 dragons-net " + revision + b" ready, no posting; source code at " + source
        + b"\r\n",
        "capabilities": b"101 Capability list:\r\nVERSION 2\r\nIMPLEMENTATION dragons-net " + revision
        + b"\r\n.\r\n",
        "help": b"100 Help text follows\r\nCAPABILITIES [keyword]\r\nHEAD [message-ID|number]\r\nHELP\r\n"
        b"QUIT\r\nSTAT [message-ID|number]\r\ndragons-net " + revision
        + b" is free software under the GNU AGPL; source code at " + source + b"\r\n.\r\n",
        "quit": b"205 Bye\r\n",
        "no-group": b"412 No newsgroup selected\r\n",
        "no-such-id": b"430 No article with that message-id\r\n",
        "unknown": b"500 Unknown command\r\n",
        "syntax": b"501 Syntax error\r\n",
    }


def answers(stream: bytes) -> list[str]:
    """The replies to the whole lines of `stream`, in order, up to and including a QUIT's."""
    found = []
    for body in stream.split(b"\n")[:-1]:
        kind, kept = framing_ref.classify(LINE_LIMIT, body)
        r = reply(kind, kept)
        if r != "ignore":
            found.append(r)
        if r == "quit":
            break
    return found


class Violation(Exception):
    """A trace the session may not produce; `kind` names the rule it breaks."""

    def __init__(self, kind: str, message: str) -> None:
        super().__init__(message)
        self.kind = kind


class Event(NamedTuple):
    """An event, as `dn-compiler session-model` takes it: its kind, the connection's index and
    generation, and the bytes of a `recv`."""
    kind: str
    idx: int
    gen: int
    data: bytes = b""


class Action(NamedTuple):
    """An action, as the model gives it: its kind, the connection's index and generation, and for a
    send its bytes and whether to read once they are taken."""
    kind: str
    idx: int
    gen: int
    data: bytes = b""
    read: bool = False


@dataclass
class Turn:
    now: int
    events: list[Event]
    actions: list[Action]
    took: list[int]
    deadline: int


@dataclass
class Conn:
    opened: int
    delivered: bytearray = field(default_factory=bytearray)
    ended: bool = False
    emitted: bytearray = field(default_factory=bytearray)
    taken: int = 0
    replies: int = 0
    # when the first command was answered
    answered: int | None = None
    # the last command answered or output taken, or the opening
    activity: int = 0
    # whether the last action asked the host to read
    reading: bool = False
    # a send was left partly untaken and the host has not reported the connection ready since
    blocked: bool = False
    # when the program began waiting for the rest of a line; a line answered starts it again
    since: int | None = None

    def pending(self) -> bytes:
        return bytes(self.emitted[self.taken:])


class Judge:
    def __init__(self, revision: bytes, source: bytes) -> None:
        self.text = texts(revision, source)
        self.conns: dict[int, tuple[int, Conn]] = {}

    def replies(self, c: Conn) -> list[str]:
        return answers(bytes(c.delivered))

    def expected(self, c: Conn) -> bytes:
        return self.text["greeting"] + b"".join(self.text[r] for r in self.replies(c))

    def quitting(self, c: Conn) -> bool:
        """Whether the connection has been answered its QUIT."""
        return c.replies > 0 and self.replies(c)[c.replies - 1] == "quit"

    def owed(self, c: Conn) -> bool:
        """Whether a whole line the client sent waits for its reply."""
        return c.replies < len(self.replies(c))

    def takes_commands(self, c: Conn) -> bool:
        return not self.quitting(c) and not c.ended

    def ready(self, c: Conn) -> bool:
        """Whether the connection can go on without the host: nothing untaken, and a line to answer
        or a close to make."""
        return not c.pending() and (self.owed(c) or not self.takes_commands(c))

    def waiting(self, c: Conn) -> bool:
        """Whether the program waits for the rest of a line: everything taken and answered, commands
        still taken, and a line begun."""
        tail = bytes(c.delivered).rsplit(b"\n", 1)[-1]
        return bool(tail) and not c.pending() and not self.owed(c) and self.takes_commands(c)

    def deadlines(self, c: Conn) -> dict[str, int]:
        found = {"inactivity": c.activity + INACTIVITY}
        if c.answered is None:
            found["first command"] = c.opened + FIRST_COMMAND
        if c.since is not None and not c.ended:
            found["line"] = c.since + LINE_TIME
        return found

    def due(self, c: Conn, now: int) -> str | None:
        passed = [name for name, at in self.deadlines(c).items() if at <= now]
        return passed[0] if passed else None

    def live(self, idx: int, gen: int) -> Conn:
        if idx not in self.conns or self.conns[idx][0] != gen:
            raise Violation("stranger", f"an action for {idx}/{gen}, which is not open")
        return self.conns[idx][1]

    def turn(self, t: Turn) -> None:
        opened = set()
        for event in t.events:
            kind, idx, gen = event.kind, event.idx, event.gen
            if kind == "open":
                self.conns[idx] = (gen, Conn(opened=t.now, activity=t.now))
                opened.add(idx)
            elif idx in self.conns and self.conns[idx][0] == gen:
                c = self.conns[idx][1]
                if kind == "recv":
                    c.delivered += event.data
                elif kind == "end":
                    c.ended = True
                elif kind == "writable":
                    c.blocked = False
                elif kind == "closed":
                    del self.conns[idx]
        due = {idx: self.due(c, t.now) for idx, (_, c) in self.conns.items()}
        replied = {idx: c.replies for idx, (_, c) in self.conns.items()}
        acted: set[int] = set()
        sends = []
        for action in t.actions:
            kind, idx, gen = action.kind, action.idx, action.gen
            if idx in acted:
                raise Violation("twice", f"two actions for {idx} in one turn")
            acted.add(idx)
            c = self.live(idx, gen)
            if kind == "close":
                if due[idx] is None:
                    raise Violation("close", f"{idx}/{gen} closed at {t.now} with no deadline passed")
                del self.conns[idx]
            elif due[idx] is not None:
                raise Violation("missed", f"{idx}/{gen} not closed at {t.now}, after its {due[idx]} deadline")
            elif kind == "graceful":
                if c.pending():
                    raise Violation("graceful-untaken", f"{idx}/{gen} closed before its output was taken")
                if not (self.quitting(c) or (c.ended and not self.owed(c))):
                    raise Violation("graceful-unanswered", f"{idx}/{gen} closed gracefully with lines unanswered")
                del self.conns[idx]
            else:
                self.send(c, idx, gen, action.data, action.read, t.now)
                sends.append((idx, len(action.data)))
        for idx, (gen, c) in self.conns.items():
            if idx in acted:
                continue
            if due.get(idx) is not None:
                raise Violation("missed", f"{idx}/{gen} not closed at {t.now}, after its {due[idx]} deadline")
            if idx in opened:
                raise Violation("greeting", f"{idx}/{gen} opened at {t.now} and not greeted")
            if c.pending() and not c.blocked:
                raise Violation("stalled", f"{idx}/{gen} has output to send again and was not sent it")
        if len(t.took) != len(sends):
            raise Violation("counts", f"{len(t.took)} counts for {len(sends)} sends")
        for (idx, length), n in zip(sends, t.took, strict=True):
            c = self.conns[idx][1]
            c.taken += n
            c.blocked = n < length
            if n:
                c.activity = t.now
        for idx, (gen, c) in self.conns.items():
            if not c.pending() and self.takes_commands(c) and not self.owed(c) and not c.reading:
                raise Violation("stalled", f"{idx}/{gen} does not read with nothing to answer")
            # A line answered ends the wait for it, even when the next one begins in the same batch.
            if not self.waiting(c):
                c.since = None
            elif c.since is None or c.replies != replied[idx]:
                c.since = t.now
        self.check_deadline(t)

    def send(self, c: Conn, idx: int, gen: int, data: bytes, read: bool, now: int) -> None:
        pending = c.pending()
        if pending:
            if data != pending:
                raise Violation("untaken", f"{idx}/{gen} sent {data[:40]!r} while {pending[:40]!r} was untaken")
            if c.blocked:
                raise Violation("unready", f"{idx}/{gen} sent again before the host reported it ready")
        elif data:
            before = len(c.emitted)
            c.emitted += data
            expected = self.expected(c)
            if not expected.startswith(bytes(c.emitted)):
                at = next(k for k, (x, y) in enumerate(zip(c.emitted, expected + b"\0" * len(c.emitted),
                                                         strict=False)) if x != y)
                raise Violation("order", f"{idx}/{gen} was sent {bytes(c.emitted[at:at + 40])!r} at {at}, "
                                f"not a start of {expected[at:at + 40]!r}")
            if len(c.emitted) != min(b for b in self.boundaries(c) if b > before):
                raise Violation("whole", f"{idx}/{gen} was sent part of a reply or more than one")
            if before:
                c.replies += 1
                c.activity = now
                if c.answered is None:
                    c.answered = now
        wanted = self.takes_commands(c) and not self.owed(c)
        if read != wanted:
            raise Violation("read", f"{idx}/{gen} asked {'' if read else 'not '}to read at {now}")
        c.reading = read

    def boundaries(self, c: Conn) -> list[int]:
        """Where each reply ends in the expected output, the greeting first."""
        at = len(self.text["greeting"])
        ends = [at]
        for r in self.replies(c):
            at += len(self.text[r])
            ends.append(at)
        return ends

    def check_deadline(self, t: Turn) -> None:
        if not self.conns:
            if t.deadline:
                raise Violation("turn", f"a next turn at {t.deadline} with no connection open")
            return
        ready = [idx for idx, (_, c) in self.conns.items() if self.ready(c)]
        if ready:
            # At once: the clock of this turn, or 1 at a clock of zero, since zero means none.
            if t.deadline != max(t.now, 1):
                raise Violation("turn", f"{ready[0]} can go on at {t.now}, but the next turn is at {t.deadline}")
            return
        earliest = min(min(self.deadlines(c).values()) for _, c in self.conns.values())
        if t.deadline != earliest:
            raise Violation("turn", f"the next turn at {t.deadline}, not at the earliest deadline {earliest}")


def judge(revision: bytes, source: bytes, turns: list[Turn]) -> None:
    """Raise `Violation` at the first turn the session may not produce."""
    j = Judge(revision, source)
    for index, t in enumerate(turns):
        try:
            j.turn(t)
        except Violation as error:
            raise Violation(error.kind, f"turn {index} at {t.now}: {error}") from None
