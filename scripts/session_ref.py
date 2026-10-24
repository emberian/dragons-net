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
import post_ref as P
import store_ref as J

FIRST_COMMAND, INACTIVITY, LINE_TIME, ARTICLE_TIME = 10_000, 1_800_000, 180_000, 1_800_000
LINE_LIMIT, CHUNK, CONNS = 512, 512, 64
COMMANDS = (b"CAPABILITIES", b"HELP", b"QUIT", b"HEAD", b"STAT")
# The commands a server with a store has besides.
STORED = (b"POST", b"ARTICLE", b"BODY", b"GROUP", b"NEXT", b"LAST")
# The replies a server with a store decides as it gives them.
DECIDED = ("capabilities", "post", "lookup", "group", "number", "current", "next", "last")


def words(kept: bytes) -> list[bytes]:
    return [w for w in re.split(rb"[ \t]+", kept) if w]


def is_article_number(w: bytes) -> bool:
    """RFC 3977 §6 and §9.8: at most sixteen digits, no more than 2,147,483,647."""
    return re.fullmatch(rb"[0-9]{1,16}", w) is not None and int(w) <= 2_147_483_647


def is_message_id(w: bytes) -> bool:
    """RFC 3977 §3.6 and §9.8: "<", 1 to 248 printable octets other than ">", ">"."""
    return re.fullmatch(rb"<[\x21-\x3d\x3f-\x7e]{1,248}>", w) is not None


def is_group_name(w: bytes) -> bool:
    """RFC 3977 §9.8: one or more `wildmat-exact` characters, printable US-ASCII but for `!*,?[\\]`,
    or characters past it in UTF-8 (RFC 3629)."""
    try:
        text = w.decode("utf-8")
    except UnicodeDecodeError:
        return False
    return bool(text) and all(ord(ch) > 0x7F or (0x21 < ord(ch) < 0x7F and ch not in "*,?[\\]") for ch in text)


def is_keyword(w: bytes) -> bool:
    """RFC 3977 §9.8: a letter, then two or more letters, digits, dots or hyphens."""
    return re.fullmatch(rb"[A-Za-z][A-Za-z0-9.-]{2,}", w) is not None


def reply(kind: str, kept: bytes, offered: bool = False) -> str:
    """The reply 0003 gives a line of this kind keeping these bytes; with a store, POST, ARTICLE,
    BODY, GROUP, NEXT and LAST are commands too, and the session decides what a well-formed POST
    gets (`post`), what a message-id finds in the store (`lookup`), a number in the selected group
    (`number`), no argument (`current`), a GROUP (`group`), a NEXT and a LAST."""
    ws = words(kept)
    if not ws:
        return "unknown" if kind == "overlong" else "ignore"
    name, args = ws[0].upper(), ws[1:]
    if name not in COMMANDS and not (offered and name in STORED):
        return "unknown"
    if kind != "command":
        return "syntax"
    if name == b"CAPABILITIES" and (not args or (len(args) == 1 and is_keyword(args[0]))):
        return "capabilities"
    if name in (b"HELP", b"QUIT") and not args:
        return name.decode().lower()
    if name in (b"HEAD", b"STAT", b"ARTICLE", b"BODY") and len(args) <= 1:
        if not args:
            return "current" if offered else "no-group"
        if is_article_number(args[0]):
            return "number" if offered else "no-group"
        if is_message_id(args[0]):
            return "lookup" if offered else "no-such-id"
    if name == b"POST" and not args:
        return "post"
    if name == b"GROUP" and len(args) == 1 and is_group_name(args[0]):
        return "group"
    if name in (b"NEXT", b"LAST") and not args:
        return name.decode().lower()
    return "syntax"


def texts(revision: bytes, source: bytes) -> dict[str, bytes]:
    help_lines = (b"100 Help text follows\r\nCAPABILITIES [keyword]\r\nHEAD [message-ID|number]\r\nHELP\r\n",
                  b"QUIT\r\nSTAT [message-ID|number]\r\ndragons-net " + revision
                  + b" is free software under the GNU AGPL; source code at " + source + b"\r\n.\r\n")
    return {
        "greeting": b"201 dragons-net " + revision + b" ready, no posting; source code at " + source
        + b"\r\n",
        "greeting-post": b"200 dragons-net " + revision + b" ready, posting allowed; source code at " + source
        + b"\r\n",
        "capabilities-post": b"101 Capability list:\r\nVERSION 2\r\nIMPLEMENTATION dragons-net " + revision
        + b"\r\nPOST\r\n.\r\n",
        "help-post": b"100 Help text follows\r\nARTICLE [message-ID|number]\r\nBODY [message-ID|number]\r\n"
        + help_lines[0][len(b"100 Help text follows\r\n"):] + b"POST\r\n" + help_lines[1],
        "unreadable": b"403 Article not readable\r\n",
        "post": b"340 Send article to be posted\r\n",
        "posted": b"240 Article received OK\r\n",
        "failed": b"441 Posting failed\r\n",
        "not-permitted": b"440 Posting not permitted\r\n",
        "unavailable": b"403 Not accepting articles\r\n",
        "capabilities": b"101 Capability list:\r\nVERSION 2\r\nIMPLEMENTATION dragons-net " + revision
        + b"\r\n.\r\n",
        "help": b"100 Help text follows\r\nCAPABILITIES [keyword]\r\nHEAD [message-ID|number]\r\nHELP\r\n"
        b"QUIT\r\nSTAT [message-ID|number]\r\ndragons-net " + revision
        + b" is free software under the GNU AGPL; source code at " + source + b"\r\n.\r\n",
        "quit": b"205 Bye\r\n",
        "no-group": b"412 No newsgroup selected\r\n",
        "no-such-id": b"430 No article with that message-id\r\n",
        "no-such-group": b"411 No such newsgroup\r\n",
        "no-current": b"420 Current article number is invalid\r\n",
        "no-next": b"421 No next article in this group\r\n",
        "no-previous": b"422 No previous article in this group\r\n",
        "no-number": b"423 No article with that number\r\n",
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
    generation, the bytes of a `recv`, and whether an opened connection may post."""
    kind: str
    idx: int
    gen: int
    data: bytes = b""
    post: bool = False


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
    """A turn, with a store: the wall clock, the completions the host reported (each with what a
    failed operation left, `post_ref.Done`) and the jobs the program handed over."""
    now: int
    events: list[Event]
    actions: list[Action]
    took: list[int]
    deadline: int
    wall: int = 0
    dones: list[P.Done] = field(default_factory=list)
    jobs: list[tuple[int, int, list[P.Op]]] = field(default_factory=list)


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
    # with a store: its number and whether it was greeted with 200; the replies decided when
    # given — the capabilities, and each POST's answer; each POST answered 340, with where its
    # article starts in what the connection sent; whether a POST waits for a slot; when its 340
    # went out
    number: int = 0
    greeted: bool = False
    decisions: list[str] = field(default_factory=list)
    posts: list[tuple[int, P.Article]] = field(default_factory=list)
    waiting: bool = False
    sent340: int = 0
    # the reads that answered its ARTICLE, HEAD and BODY; the one it waits for, with the command, the
    # number its first line gives and the commit, until it gets it
    fetches: list[P.Fetch] = field(default_factory=list)
    wanted: tuple[str, int, J.Commit] | None = None
    # the selected group and the current article number, None and 0 while invalid
    group: bytes | None = None
    current: int = 0

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
        wanted = self.read_wanted(c)
        if read != wanted:
            raise Violation("read", f"{idx}/{gen} asked {'' if read else 'not '}to read at {now}")
        c.reading = read

    def read_wanted(self, c: Conn) -> bool:
        """Whether the program has to ask the host to read: the connection takes commands and no
        line waits for its reply."""
        return self.takes_commands(c) and not self.owed(c)

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


class PostJudge(Judge):
    """The session of a server with a store (decision 0005). A connection is greeted with 200 when it
    may post and the store accepts and carries a group. Its replies are the 0003 ones, HELP's naming
    POST; the capabilities name POST while it was greeted with 200 and the store accepts. A POST is
    answered at once 440 when it was greeted with 201, 403 once the store has stopped accepting, else
    340 once one of four slots is free for it: POSTs that wait, unread and with no deadline, get the
    slots that free in the order they came. The article after a 340 is `post_ref`'s; it has 1,800
    seconds from the 340 to end, and once it has, no deadline runs until it is answered 240 or 441,
    or the connection closed when its outcome is unknown, at once; with the answer, what follows the
    article is read as lines. An ARTICLE, HEAD or BODY of an article the store holds waits, unread
    and with no deadline, for one of eight reads (`post_ref.Fetch`), in the order they came; what
    the read may give goes out a send at a time, of 512 octets or what there is, as soon as what went
    before was taken, inactivity running only while some of it is untaken; a read that fails is
    answered 403 when it gave nothing, else its connection is closed once what it gave was taken.
    STAT of an article the store holds is answered 223, any of the four of one it does not hold 430.
    Each turn, after the events and the completions, the connections in order: the octets an article
    takes, a read's next octets, then the connection's action; then the jobs.

    A connection's selected group and current article are RFC 3977's (§6.1, §6.2), over the articles
    the store holds as each line is answered: GROUP of a group the store carries selects it, its
    first article current, none if it is empty, answered 211 with the count and the lowest and highest
    numbers, an empty group's 1 and 0; of another, 411. A number finds the article in the selected
    group, no argument the current one, and NEXT and LAST the nearest above or below; a message-id
    leaves both as they are and is answered with the number 0."""

    def __init__(self, revision: bytes, source: bytes, start: P.Start, checker: P.Checker) -> None:
        super().__init__(revision, source)
        self.store = P.Store(start, checker)
        self.opened = 0
        # the connections whose POST waits, by index and generation, in the order they came, and
        # those that wait for a read
        self.waiters: list[tuple[int, int]] = []
        self.readers: list[tuple[int, int]] = []

    def items(self, c: Conn) -> tuple[list[str], int, P.Article | P.Fetch | None]:
        """The replies the connection has had or is due, in order; where what it sent is read to;
        and its article not ended or not answered, or its read not ended, if any. A reply decided
        when given and not yet given, a waiting POST, an article not answered or a read not ended
        ends the list."""
        out: list[str] = []
        data, at, d, k = c.delivered, 0, 0, 0
        while (nl := data.find(b"\n", at)) >= 0:
            kind, kept = framing_ref.classify(LINE_LIMIT, bytes(data[at:nl]))
            r = reply(kind, kept, offered=True)
            if r == "ignore":
                at = nl + 1
                continue
            if r in DECIDED:
                if d == len(c.decisions):
                    return out, at, None
                r = c.decisions[d]
                d += 1
            elif r == "help":
                r = "help-post"
            if r.startswith("read "):
                f = c.fetches[int(r[5:])]
                if f.answered is None:
                    return out, nl + 1, f
                r = f.answered
            out.append(r)
            at = nl + 1
            if r == "quit":
                return out, at, None
            if r == "post":
                start, a = c.posts[k]
                k += 1
                if a.answered is None:
                    return out, start + a.size, a
                out.append(a.answered)
                at = start + a.size
        return out, at, None

    def replies(self, c: Conn) -> list[str]:
        return self.items(c)[0]

    def greeting(self, c: Conn) -> bytes:
        return self.text["greeting-post" if c.greeted else "greeting"]

    def text_of(self, c: Conn, r: str) -> bytes:
        if r.startswith("stat "):
            n, message_id = r[5:].split()
            return b"223 " + n.encode() + b" " + bytes.fromhex(message_id) + P.CRLF
        if r.startswith("text "):
            return bytes.fromhex(r[5:])
        if r.startswith("read "):
            return c.fetches[int(r[5:])].out(self.store.start.identity)
        return self.text[r]

    def expected(self, c: Conn) -> bytes:
        return self.greeting(c) + b"".join(self.text_of(c, r) for r in self.replies(c))

    def boundaries(self, c: Conn) -> list[int]:
        at = len(self.greeting(c))
        ends = [at]
        for r in self.replies(c):
            at += len(self.text_of(c, r))
            ends.append(at)
        return ends

    def article(self, c: Conn) -> P.Article | None:
        """Its article from its 340 until it is answered."""
        if c.posts and c.posts[-1][1].owner is not None:
            return c.posts[-1][1]
        return None

    def fetch(self, c: Conn) -> P.Fetch | None:
        """The read that answers it, from when it gets it until it has given everything or failed."""
        if c.fetches and c.fetches[-1].answered is None:
            return c.fetches[-1]
        return None

    def busy(self, c: Conn) -> bool:
        """Whether a read waits for a place or answers it."""
        return c.wanted is not None or self.fetch(c) is not None

    def due_line(self, c: Conn) -> tuple[str, bytes] | None:
        """The reply its next whole line is due, if one is due and not decided, with what the line
        keeps."""
        _, at, a = self.items(c)
        if a is not None:
            return None
        nl = c.delivered.find(b"\n", at)
        while nl >= 0:
            kind, kept = framing_ref.classify(LINE_LIMIT, bytes(c.delivered[at:nl]))
            r = reply(kind, kept, offered=True)
            if r != "ignore":
                return r, kept
            at = nl + 1
            nl = c.delivered.find(b"\n", at)
        return None

    def next_line(self, c: Conn) -> str | None:
        """The reply its next whole line is due, if one is due and not decided."""
        due = self.due_line(c)
        return None if due is None else due[0]

    def owed(self, c: Conn) -> bool:
        return c.replies < len(self.replies(c)) or \
            (self.next_line(c) is not None and not c.waiting and not self.busy(c))

    def admitted(self, idx: int, gen: int) -> bool:
        """Whether a POST that waits gets a slot now: fewer came before it than slots are free."""
        return (idx, gen) in self.waiters and \
            self.waiters.index((idx, gen)) < P.POSTS - len(self.store.in_slot())

    def admitted_read(self, idx: int, gen: int) -> bool:
        """Whether a connection that waits for a read gets one now: fewer came before it than reads
        are free."""
        return (idx, gen) in self.readers and self.readers.index((idx, gen)) < len(self.store.free_reads())

    def read_wanted(self, c: Conn) -> bool:
        if not self.takes_commands(c) or c.waiting or self.busy(c):
            return False
        a = self.article(c)
        if a is not None:
            start = c.posts[-1][0]
            return not a.ended and self.store.takes(a) and len(c.delivered) == start + a.size
        return not self.owed(c)

    def deadlines(self, c: Conn) -> dict[str, int]:
        a = self.article(c)
        if c.waiting or (a is not None and a.ended) or c.wanted is not None:
            return {}
        if self.fetch(c) is not None:
            return {"inactivity": c.activity + INACTIVITY} if c.pending() else {}
        if a is not None:
            return {"article": c.sent340 + ARTICLE_TIME}
        found = super().deadlines(c)
        if c.posts:
            found.pop("first command", None)
        return found

    def waiting_line(self, c: Conn) -> bool:
        """Whether the program waits for the rest of a command line."""
        _, at, a = self.items(c)
        if a is not None or c.waiting or self.busy(c) or c.pending() or self.owed(c) or not self.takes_commands(c):
            return False
        return bool(bytes(c.delivered[at:]).rsplit(b"\n", 1)[-1])

    def ready(self, c: Conn, idx: int = 0, gen: int = 0) -> bool:
        if c.pending():
            return False
        if c.waiting:
            return not self.store.accepting or self.admitted(idx, gen)
        if c.wanted is not None:
            return self.admitted_read(idx, gen)
        f = self.fetch(c)
        if f is not None:
            return f.bad or f.given < len(f.out(self.store.start.identity))
        a = self.article(c)
        if a is not None:
            start = c.posts[-1][0]
            return not a.ended and len(c.delivered) > start + a.size and self.store.takes(a)
        return self.owed(c) or not self.takes_commands(c)

    def gone(self, idx: int, gen: int) -> None:
        self.store.abandon((idx, gen))
        for waiting in (self.waiters, self.readers):
            if (idx, gen) in waiting:
                waiting.remove((idx, gen))

    def turn(self, t: Turn) -> None:
        for event in t.events:
            kind, idx, gen = event.kind, event.idx, event.gen
            if kind == "open":
                self.opened += 1
                greeted = event.post and self.store.accepting and bool(self.store.start.groups)
                self.conns[idx] = (gen, Conn(opened=t.now, activity=t.now, number=self.opened, greeted=greeted))
            elif idx in self.conns and self.conns[idx][0] == gen:
                c = self.conns[idx][1]
                if kind == "recv":
                    c.delivered += event.data
                elif kind == "end":
                    c.ended = True
                    self.gone(idx, gen)
                elif kind == "writable":
                    c.blocked = False
                elif kind == "closed":
                    self.gone(idx, gen)
                    del self.conns[idx]
        posted = len(self.store.answered)
        self.store.complete(t.dones)
        actions = {a.idx: a for a in t.actions}
        if len(actions) != len(t.actions):
            raise Violation("twice", "two actions for one connection in a turn")
        replied = {idx: c.replies for idx, (_, c) in self.conns.items()}
        sends: list[tuple[int, int]] = []
        for idx in sorted(set(self.conns) | set(actions)):
            self.connection(t, idx, actions.get(idx), sends)
        self.store.handed(t.jobs)
        stalled = self.store.stalled()
        if stalled:
            raise Violation("job-stalled", stalled)
        if len(self.store.answered) > posted:
            self.store.durable()
        if len(t.took) != len(sends):
            raise Violation("counts", f"{len(t.took)} counts for {len(sends)} sends")
        for (idx, length), n in zip(sends, t.took, strict=True):
            c = self.conns[idx][1]
            c.taken += n
            c.blocked = n < length
            if n and not c.waiting and self.article(c) is None:
                c.activity = t.now
        for idx, (gen, c) in self.conns.items():
            wanted = self.read_wanted(c)
            if not c.pending() and self.takes_commands(c) and wanted != c.reading:
                raise Violation("stalled" if wanted else "read",
                                f"{idx}/{gen} {'does not read' if wanted else 'reads'} at {t.now}")
            # A line answered ends the wait for it, even when the next one begins in the same batch.
            if not self.waiting_line(c):
                c.since = None
            elif c.since is None or c.replies != replied.get(idx, c.replies):
                c.since = t.now
        self.check_deadline(t)

    def connection(self, t: Turn, idx: int, action: Action | None, sends: list[tuple[int, int]]) -> None:
        """One connection's turn: the octets its article takes, then its action."""
        if idx not in self.conns:
            raise Violation("stranger", f"an action for {idx}, which is not open")
        gen, c = self.conns[idx]
        due = self.due(c, t.now)
        if due is not None:
            if action is None or action.kind != "close":
                raise Violation("missed", f"{idx}/{gen} not closed at {t.now}, after its {due} deadline")
            self.gone(idx, gen)
            del self.conns[idx]
            return
        a = self.article(c)
        if a is not None and not c.pending() and not a.ended:
            start = c.posts[-1][0]
            self.store.take(a, bytes(c.delivered[start + a.size:]), t.wall)
        answer = self.store.decided(a) if a is not None and a.ended else None
        if a is not None and answer == "lost" and not c.pending():
            if action is None or action.kind != "close":
                raise Violation("unanswered", f"{idx}/{gen} not closed at {t.now}, its article's outcome unknown")
            a.owner = None
            del self.conns[idx]
            return
        if a is not None and answer in ("posted", "failed") and not c.pending() and \
                (action is None or action.kind != "send" or not action.data):
            raise Violation("stalled", f"{idx}/{gen} not answered its article's {answer} at {t.now}")
        f = self.fetch(c)
        if f is not None and not c.pending() and self.read_turn(t, idx, gen, c, f, action, sends):
            return
        if a is None and not c.pending() and self.next_line(c) == "post" and c.replies == len(self.replies(c)):
            self.post_due(t, idx, gen, c, action)
        if a is None and f is None and c.wanted is None and not c.pending() and c.replies == len(self.replies(c)):
            line = self.due_line(c)
            if line is not None and line[0] in ("lookup", "number", "current"):
                self.lookup_due(t, idx, gen, c, line[0], line[1])
        if c.wanted is not None and self.admitted_read(idx, gen):
            cmd, number, commit = c.wanted
            c.fetches.append(self.store.grant((idx, gen), cmd, commit, number))
            c.decisions.append(f"read {len(c.fetches) - 1}")
            c.wanted = None
            self.readers.remove((idx, gen))
        if action is None:
            self.unacted(t, idx, gen, c)
            return
        if action.gen != gen:
            raise Violation("stranger", f"an action for {idx}/{action.gen}, which is not open")
        if action.kind == "close":
            raise Violation("close", f"{idx}/{gen} closed at {t.now} with no deadline passed")
        if action.kind == "graceful":
            if c.pending():
                raise Violation("graceful-untaken", f"{idx}/{gen} closed before its output was taken")
            if not (self.quitting(c) or (c.ended and not self.owed(c))):
                raise Violation("graceful-unanswered", f"{idx}/{gen} closed gracefully with lines unanswered")
            del self.conns[idx]
            return
        if not c.pending() and action.data:
            self.decide(t, idx, gen, c, a, answer, action.data)
        self.send(c, idx, gen, action.data, action.read, t.now)
        sends.append((idx, len(action.data)))

    def read_turn(self, t: Turn, idx: int, gen: int, c: Conn, f: P.Fetch, action: Action | None,
                  sends: list[tuple[int, int]]) -> bool:
        """The turn of a connection a read answers, with nothing untaken: its read's next octets
        sent, or the 403 or the close of a read that failed. Whether it took the action whole; the
        403, a whole reply, is left to `send`."""
        identity = self.store.start.identity
        if f.bad:
            if f.given == 0:
                if action is None or action.kind != "send" or action.data != self.text["unreadable"]:
                    raise Violation("unreadable", f"{idx}/{gen} not answered 403 at {t.now}, its read failed")
                f.answered, f.owner = "unreadable", None
                return False
            if action is None or action.kind != "close":
                raise Violation("unread", f"{idx}/{gen} not closed at {t.now}, its read failed after giving")
            self.gone(idx, gen)
            del self.conns[idx]
            return True
        piece = f.out(identity)[f.given:f.given + CHUNK]
        if not piece:
            return False
        if action is None or action.kind != "send" or action.data != piece or action.gen != gen:
            sent = action.data[:40] if action is not None else None
            raise Violation("read-out", f"{idx}/{gen} sent {sent!r} at {t.now}, not the next of its read, "
                            f"{piece[:40]!r}")
        if f.given == 0 and f.number:
            # Its first line answers the command: only now is the article current (RFC 3977 §6.2.1.2).
            c.current = f.number
        f.given += len(piece)
        c.emitted += piece
        c.activity = t.now
        if f.whole() and f.given == len(f.out(identity)):
            f.answered, f.owner = f"read {c.fetches.index(f)}", None
            c.replies += 1
        if action.read != self.read_wanted(c):
            raise Violation("read", f"{idx}/{gen} asked {'' if action.read else 'not '}to read at {t.now}")
        c.reading = action.read
        sends.append((idx, len(piece)))
        return True

    def in_group(self, g: bytes) -> list[tuple[int, J.Commit]]:
        """The articles the store holds in group `g`, each with its number there."""
        return sorted((n, commit) for commit in self.store.commits for name, n in commit[2] if name == g)

    def target(self, c: Conn, kind: str, ws: list[bytes]) -> tuple[int, J.Commit] | str:
        """The article a line of ARTICLE, HEAD, BODY or STAT names, with the number its reply gives,
        or the reply when there is none."""
        if kind == "lookup":
            commit = self.store.found(ws[1])
            return "no-such-id" if commit is None else (0, commit)
        if c.group is None:
            return "no-group"
        n = int(ws[1]) if kind == "number" else c.current
        if kind == "current" and n == 0:
            return "no-current"
        hit = [x for x in self.in_group(c.group) if x[0] == n]
        if not hit:
            return "no-number" if kind == "number" else "no-current"
        return hit[0]

    def reader(self, c: Conn, kind: str, ws: list[bytes]) -> str:
        """What a GROUP, NEXT, LAST, or a STAT, is answered, deciding it now, and where it leaves the
        selected group and the current article; an ARTICLE, HEAD or BODY that finds an article waits
        for a read instead."""
        if kind == "group":
            g = ws[1]
            if g not in self.store.start.groups:
                return "no-such-group"
            numbers = [n for n, _ in self.in_group(g)]
            c.group, c.current = g, numbers[0] if numbers else 0
            low, high = (numbers[0], numbers[-1]) if numbers else (1, 0)
            return "text " + (b"211 %d %d %d " % (len(numbers), low, high) + g + P.CRLF).hex()
        if kind in ("next", "last"):
            if c.group is None:
                return "no-group"
            if c.current == 0:
                return "no-current"
            near = [x for x in self.in_group(c.group) if (x[0] > c.current if kind == "next" else x[0] < c.current)]
            if not near:
                return "no-next" if kind == "next" else "no-previous"
            n, commit = near[0] if kind == "next" else near[-1]
            c.current = n
            return f"stat {n} {commit[1].hex()}"
        found = self.target(c, kind, ws)
        if isinstance(found, str):
            return found
        if ws[0].upper() != b"STAT":
            raise Violation("read", f"{ws[0]!r} answered at once, before a read")
        n, commit = found
        if n:
            c.current = n
        return f"stat {n} {commit[1].hex()}"

    def lookup_due(self, t: Turn, idx: int, gen: int, c: Conn, kind: str, kept: bytes) -> None:
        """An ARTICLE, HEAD or BODY of an article the store holds: the connection waits for a read,
        which makes the article current as it answers when it was named by its number."""
        ws = words(kept)
        cmd = ws[0].decode().lower()
        found = self.target(c, kind, ws)
        if isinstance(found, str) or cmd == "stat":
            return
        n, commit = found
        c.wanted = (cmd, n, commit)
        if c.answered is None:
            c.answered = t.now
        if (idx, gen) not in self.readers:
            self.readers.append((idx, gen))

    def post_due(self, t: Turn, idx: int, gen: int, c: Conn, action: Action | None) -> None:
        """A POST its connection is due an answer to: one at once, but for a slot it waits for."""
        if c.greeted and self.store.accepting:
            if (idx, gen) not in self.waiters:
                self.waiters.append((idx, gen))
            if not self.admitted(idx, gen):
                if not c.waiting:
                    c.waiting = True
                    c.answered = c.answered if c.answered is not None else t.now
                return
        if action is None or action.kind != "send" or not action.data:
            raise Violation("stalled", f"{idx}/{gen} not answered its POST at {t.now}")

    def decide(self, t: Turn, idx: int, gen: int, c: Conn, a: P.Article | None, answer: str | None,
               data: bytes) -> None:
        """A new reply sent, when the next is not decided yet: decided now, as the rules say."""
        if c.replies < len(self.replies(c)):
            return
        if a is not None and answer in ("posted", "failed"):
            if data != self.text[answer]:
                raise Violation("outcome", f"{idx} sent {data[:40]!r}, not its article's {answer}")
            a.owner, a.answered = None, answer
            c.activity = t.now
            return
        due = self.next_line(c)
        if due in ("lookup", "number", "current", "group", "next", "last"):
            line = self.due_line(c)
            try:
                c.decisions.append(self.reader(c, due, words(line[1] if line else b"")))
            except Violation as error:
                raise Violation(error.kind, f"{idx} {error}") from None
            return
        if due == "capabilities":
            c.decisions.append("capabilities-post" if c.greeted and self.store.accepting else "capabilities")
        elif due == "post":
            if not c.greeted:
                c.decisions.append("not-permitted")
            elif not self.store.accepting:
                c.decisions.append("unavailable")
            elif self.admitted(idx, gen):
                _, at, _ = self.items(c)
                c.decisions.append("post")
                art = P.Article(owner=(idx, gen), conn=c.number)
                self.store.articles.append(art)
                c.posts.append((c.delivered.find(b"\n", at) + 1, art))
                c.sent340 = t.now
            else:
                raise Violation("slots", f"{idx} answered a POST before its turn for a slot")
            c.waiting = False
            if (idx, gen) in self.waiters:
                self.waiters.remove((idx, gen))

    def unacted(self, t: Turn, idx: int, gen: int, c: Conn) -> None:
        """A connection with no action: nothing it is due now, but for output the host left."""
        if idx in {e.idx for e in t.events if e.kind == "open"}:
            raise Violation("greeting", f"{idx}/{gen} opened at {t.now} and not greeted")
        if c.pending() and not c.blocked:
            raise Violation("stalled", f"{idx}/{gen} has output to send again and was not sent it")

    def check_deadline(self, t: Turn) -> None:
        ready = [idx for idx, (gen, c) in self.conns.items() if self.ready(c, idx, gen)]
        if ready:
            if t.deadline != max(t.now, 1):
                raise Violation("turn", f"{ready[0]} can go on at {t.now}, but the next turn is at {t.deadline}")
            return
        times = [v for _, c in self.conns.values() for v in self.deadlines(c).values()]
        earliest = min(times, default=0)
        if t.deadline != earliest:
            raise Violation("turn", f"the next turn at {t.deadline}, not at the earliest deadline {earliest}")


def judge(revision: bytes, source: bytes, turns: list[Turn], start: P.Start | None = None,
          checker: P.Checker | None = None) -> None:
    """Raise `Violation` at the first turn the session may not produce; with a store, also at its
    end when the spool is left holding what it may not."""
    j: Judge = Judge(revision, source) if start is None or checker is None else PostJudge(revision, source, start,
                                                                                          checker)
    for index, t in enumerate(turns):
        try:
            j.turn(t)
        except (Violation, P.Violation) as error:
            raise Violation(error.kind, f"turn {index} at {t.now}: {error}") from None
    if isinstance(j, PostJudge) and not j.conns:
        try:
            j.store.finish()
        except P.Violation as error:
            raise Violation(error.kind, f"at the end: {error}") from None
