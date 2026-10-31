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
import time
from typing import NamedTuple

import framing_ref
import post_ref as P
import store_ref as J

FIRST_COMMAND, INACTIVITY, LINE_TIME, ARTICLE_TIME = 10_000, 1_800_000, 180_000, 1_800_000
LINE_LIMIT, CHUNK, CONNS = 512, 512, 64
COMMANDS = (b"CAPABILITIES", b"HELP", b"QUIT", b"HEAD", b"STAT", b"MODE", b"AUTHINFO")
# The commands a server with a store has besides.
STORED = (b"POST", b"ARTICLE", b"BODY", b"GROUP", b"NEXT", b"LAST", b"LISTGROUP", b"LIST", b"DATE", b"NEWGROUPS",
          b"OVER", b"HDR", b"XOVER", b"XHDR")
# The replies a server with a store decides as it gives them.
DECIDED = ("capabilities", "post", "lookup", "group", "number", "current", "next", "last", "listgroup", "list-active",
           "date", "mode-reader", "overview", "authinfo")
# The replies after which the connection closes: QUIT's, and MODE READER's 502 of a server that does not
# advertise READER (RFC 3977 §5.3.2).
CLOSING = ("quit", "mode-reader")
NUMBER_MAX = 2_147_483_647
# The longest name and password AUTHINFO takes: no account has a longer one.
NAME_MAX, PASSWORD_MAX = 64, 256


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


def article_range(w: bytes) -> tuple[int, int] | None:
    """RFC 3977 §6.1.2.2 and §9.8: a number, a number and a dash, or two numbers and a dash between
    them; the lowest and the highest number it takes in."""
    m = re.fullmatch(rb"([^-]*)(-([^-]*))?", w)
    if m is None or not is_article_number(m[1]):
        return None
    if m[2] is None:
        return int(m[1]), int(m[1])
    if not m[3]:
        return int(m[1]), NUMBER_MAX
    return (int(m[1]), int(m[3])) if is_article_number(m[3]) else None


def wildmat(w: bytes) -> list[tuple[bool, str]] | None:
    """RFC 3977 §4.1: patterns of `wildmat-exact` characters, `*` and `?`, separated by commas, each
    after the first negated by `!` or not; each with whether it is negated."""
    try:
        text = w.decode("utf-8")
    except UnicodeDecodeError:
        return None
    patterns = []
    for k, part in enumerate(text.split(",")):
        negated = k > 0 and part.startswith("!")
        body = part[1:] if negated else part
        if not body or not all(ch in "*?" or ord(ch) > 0x7F or (0x21 < ord(ch) < 0x7F and ch not in "*,?[\\]")
                               for ch in body):
            return None
        patterns.append((negated, body))
    return patterns


def wildmatch(patterns: list[tuple[bool, str]], name: bytes) -> bool:
    """§4.2: the rightmost pattern that matches the whole name decides, against it when negated."""
    text, verdict = name.decode("utf-8"), False
    for negated, body in patterns:
        regex = "".join(".*" if ch == "*" else "." if ch == "?" else re.escape(ch) for ch in body)
        if re.fullmatch(regex, text, re.DOTALL):
            verdict = not negated
    return verdict


def is_date(w: bytes) -> bool:
    """§7.3.2: `[xx]yymmdd`, its century from 19, its month from 1 to 12, its day from 1 to 31."""
    m = re.fullmatch(rb"([0-9]{2})?[0-9]{2}([0-9]{2})([0-9]{2})", w)
    return m is not None and (m[1] is None or int(m[1]) >= 19) and 1 <= int(m[2]) <= 12 and 1 <= int(m[3]) <= 31


def is_time(w: bytes) -> bool:
    """§7.3.2: `hhmmss`, to 23:59:60."""
    m = re.fullmatch(rb"([0-9]{2})([0-9]{2})([0-9]{2})", w)
    return m is not None and int(m[1]) <= 23 and int(m[2]) <= 59 and int(m[3]) <= 60


def date_digits(wall: int) -> bytes:
    """§7.1: the wall clock, in milliseconds, as `yyyymmddhhmmss` in UTC."""
    return b"%04d%02d%02d%02d%02d%02d" % time.gmtime(wall // 1000)[:6]


def is_field_name(w: bytes) -> bool:
    """§9.8: a header's name, printable US-ASCII but for the colon, or a metadata item's, a colon before
    one."""
    return re.fullmatch(rb":?[\x21-\x39\x3b-\x7e]+", w) is not None


def is_keyword(w: bytes) -> bool:
    """RFC 3977 §9.8: a letter, then two or more letters, digits, dots or hyphens."""
    return re.fullmatch(rb"[A-Za-z][A-Za-z0-9.-]{2,}", w) is not None


def reply(kind: str, kept: bytes, offered: bool = False) -> str:
    """The reply 0003 gives a line of this kind keeping these bytes, MODE READER's 502 of a server
    that does not advertise READER among them (RFC 3977 §5.3.2); with a store, POST, ARTICLE, BODY,
    GROUP, NEXT and LAST are commands too, and the session decides what a well-formed POST gets
    (`post`), what a message-id finds in the store (`lookup`), a number in the selected group
    (`number`), no argument (`current`), a GROUP (`group`), a NEXT, a LAST and a MODE READER."""
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
    if name == b"MODE" and len(args) == 1 and args[0].upper() == b"READER":
        return "mode-reader"
    if name == b"AUTHINFO":
        return "authinfo"
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
    if name == b"LISTGROUP" and (not args or (len(args) <= 2 and is_group_name(args[0]) and
                                             (len(args) == 1 or article_range(args[1]) is not None))):
        return "listgroup"
    if name in (b"OVER", b"XOVER") and len(args) <= 1 and \
            (not args or article_range(args[0]) is not None or (name == b"OVER" and is_message_id(args[0]))):
        return "overview"
    if name in (b"HDR", b"XHDR") and 1 <= len(args) <= 2 and \
            (len(args) == 1 or is_message_id(args[1]) or article_range(args[1]) is not None) and is_field_name(args[0]):
        served = not args[0].startswith(b":") or args[0].lower() in (b":bytes", b":lines")
        return "overview" if served else "field-refused"
    if name == b"LIST" and args and args[0].upper() == b"OVERVIEW.FMT":
        return "overview-fmt" if len(args) == 1 else "syntax"
    if name == b"LIST" and args and args[0].upper() == b"HEADERS":
        return "header-list" if len(args) == 1 or (len(args) == 2 and args[1].upper() in (b"MSGID", b"RANGE")) \
            else "syntax"
    if name == b"LIST" and len(args) <= 2 and (len(args) < 2 or wildmat(args[1]) is not None):
        keyword = args[0].upper() if args else b"ACTIVE"
        if keyword in (b"ACTIVE", b"NEWSGROUPS"):
            return "list-active" if keyword == b"ACTIVE" else "list-newsgroups"
    if name == b"DATE" and not args:
        return "date"
    if name == b"NEWGROUPS" and len(args) in (2, 3) and is_date(args[0]) and is_time(args[1]) and \
            (len(args) == 2 or args[2].upper() == b"GMT"):
        return "new-groups"
    return "syntax"


def texts(revision: bytes, source: bytes) -> dict[str, bytes]:
    return {
        "greeting": b"201 dragons-net " + revision + b" ready, no posting; source code at " + source
        + b"\r\n",
        "greeting-post": b"200 dragons-net " + revision + b" ready, posting allowed; source code at " + source
        + b"\r\n",
        "capabilities-post": b"101 Capability list:\r\nVERSION 2\r\nIMPLEMENTATION dragons-net " + revision
        + b"\r\nREADER\r\nHDR\r\nLIST ACTIVE HEADERS NEWSGROUPS OVERVIEW.FMT\r\nOVER MSGID\r\nPOST\r\n.\r\n",
        "capabilities-reader": b"101 Capability list:\r\nVERSION 2\r\nIMPLEMENTATION dragons-net " + revision
        + b"\r\nREADER\r\nHDR\r\nLIST ACTIVE HEADERS NEWSGROUPS OVERVIEW.FMT\r\nOVER MSGID\r\n.\r\n",
        "capabilities-post-auth": b"101 Capability list:\r\nVERSION 2\r\nIMPLEMENTATION dragons-net " + revision
        + b"\r\nREADER\r\nHDR\r\nLIST ACTIVE HEADERS NEWSGROUPS OVERVIEW.FMT\r\nOVER MSGID\r\nPOST\r\n"
        b"AUTHINFO USER\r\n.\r\n",
        "capabilities-reader-auth": b"101 Capability list:\r\nVERSION 2\r\nIMPLEMENTATION dragons-net " + revision
        + b"\r\nREADER\r\nHDR\r\nLIST ACTIVE HEADERS NEWSGROUPS OVERVIEW.FMT\r\nOVER MSGID\r\nAUTHINFO USER\r\n.\r\n",
        "mode-reader": b"502 Reading service unavailable\r\n",
        "reader-posting": b"200 Posting allowed\r\n",
        "reader-no-posting": b"201 Posting prohibited\r\n",
        "help-post": b"100 Help text follows\r\nARTICLE, BODY, HEAD, STAT [message-ID|number]\r\n"
        b"CAPABILITIES [keyword]\r\nDATE\r\nGROUP newsgroup\r\nHDR\r\nHELP\r\nLAST\r\nLIST\r\nLISTGROUP\r\n"
        b"NEWGROUPS\r\nNEXT\r\nOVER\r\nPOST\r\nQUIT\r\ndragons-net "
        + revision + b" is free software (GNU AGPL); source at " + source + b"\r\n.\r\n",
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
        + b" is free software (GNU AGPL); source at " + source + b"\r\n.\r\n",
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
        "list-newsgroups": b"215 Information follows\r\n.\r\n",
        "new-groups": b"231 List of new newsgroups follows\r\n.\r\n",
        "overview-fmt": b"215 Order of fields in overview database\r\nSubject:\r\nFrom:\r\nDate:\r\nMessage-ID:\r\n"
        b"References:\r\nBytes:\r\nLines:\r\nXref:full\r\n.\r\n",
        "header-list": b"215 Field list follows\r\n:\r\n:bytes\r\n:lines\r\n.\r\n",
        "no-range": b"423 No articles in that range\r\n",
        "field-refused": b"503 HDR not permitted on that field\r\n",
        "none-over": b"224 Overview information follows\r\n.\r\n",
        "none-hdr": b"221 Header follows\r\n.\r\n",
        # RFC 4643 §2.3; a server offering no logins answers 502 as one does once logged in (§2.2)
        "authinfo": b"502 Command unavailable\r\n",
        "auth-done": b"502 Command unavailable\r\n",
        "auth-user": b"381 Password required\r\n",
        "auth-accepted": b"281 Authentication accepted\r\n",
        "auth-failed": b"481 Authentication failed\r\n",
        "auth-sequence": b"482 Authentication commands issued out of sequence\r\n",
        "encryption-required": b"483 Encryption required\r\n",
        "auth-required": b"480 Authentication required\r\n",
    }


def answers(stream: bytes) -> list[str]:
    """The replies to the whole lines of `stream`, in order, up to and including the one after which
    the connection closes."""
    found = []
    for body in stream.split(b"\n")[:-1]:
        kind, kept = framing_ref.classify(LINE_LIMIT, body)
        r = reply(kind, kept)
        if r != "ignore":
            found.append(r)
        if r in CLOSING:
            break
    return found


class Violation(Exception):
    """A trace the session may not produce; `kind` names the rule it breaks."""

    def __init__(self, kind: str, message: str) -> None:
        super().__init__(message)
        self.kind = kind


class Event(NamedTuple):
    """An event, as `dn-compiler session-model` takes it: its kind, the connection's index and
    generation, the bytes of a `recv`, whether an opened connection may post, may log in and runs
    over TLS, and whether a verdict takes the name and password."""
    kind: str
    idx: int
    gen: int
    data: bytes = b""
    post: bool = False
    logins: bool = False
    tls: bool = False
    ok: bool = False


class Action(NamedTuple):
    """An action, as the model gives it: its kind, the connection's index and generation, for a
    send its bytes and whether to read once they are taken, and for a check the name and the
    password."""
    kind: str
    idx: int
    gen: int
    data: bytes = b""
    read: bool = False
    secret: bytes = b""


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
class Listing:
    """A reply of many lines going out a part at a time: what of it went out, its first line first;
    LISTGROUP's numbers, or LIST ACTIVE's wildmat, `None` for every group; how far it has gone among
    them; and whether its terminating line went out."""
    sent: bytearray
    numbers: list[int] | None = None
    patterns: list[tuple[bool, str]] | None = None
    at: int = 0
    done: bool = False


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
    # the reads that answered its ARTICLE, HEAD, BODY, OVER and HDR; the one it waits for, with the
    # command, the number its first line gives, the commit, and for OVER and HDR what it reads, until
    # it gets it
    fetches: list[P.Fetch] = field(default_factory=list)
    wanted: tuple[str, int, J.Commit, P.View | None] | None = None
    # the selected group and the current article number, None and 0 while invalid
    group: bytes | None = None
    current: int = 0
    # its replies of many lines, the last going out while it is not done
    listings: list[Listing] = field(default_factory=list)
    # whether it may post now; whether it may log in and runs over TLS; the name of its last 381 until a 481 or
    # a check, the name and password with the host, and whether it has logged in
    posting: bool = False
    logins: bool = False
    tls: bool = False
    name: bytes | None = None
    checking: tuple[bytes, bytes] | None = None
    logged: bool = False

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
        """Whether the connection has been answered its QUIT, or MODE READER's 502."""
        return c.replies > 0 and self.replies(c)[c.replies - 1] in CLOSING

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
    POST; the capabilities name READER and LIST ACTIVE NEWSGROUPS, and POST while it was greeted with
    200 and the store accepts, and MODE READER is answered 200 then, else 201, changing nothing
    (RFC 3977 §5.3.2). A POST is answered at once 440 when it was greeted with 201, or 480 where a
    login would let it post, 403 once the store has stopped accepting, else 340 once one of four slots
    is free for it: POSTs that wait, unread and with no deadline, get the slots that free in the order
    they came. The article after a 340 is `post_ref`'s; it has 1,800
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
    leaves both as they are and is answered with the number 0.

    LISTGROUP selects its group, the named one or the selected one, as GROUP does, answering 211 as
    GROUP does, then lists, one a line, the numbers of the articles the group holds as it is selected
    within its range (RFC 3977 §6.1.2). LIST and LIST ACTIVE answer 215, then a line for each group in
    the order of the start's, of those the wildmat matches (§4): its name, highest and lowest
    numbers as GROUP gives them, and `y` while the store accepts, else `n`, as the store is when the
    line goes out. Such a reply goes out a part at a time, each when what went before was taken: its
    lines that follow, as many whole as one send holds, then its terminating line once it fits too;
    nothing is read and no line answered until it ends. LIST NEWSGROUPS answers 215 and NEWGROUPS
    231, each with an empty list; DATE, 111 and the wall clock of the turn in UTC.

    OVER, HDR and their RFC 2980 spellings XOVER and XHDR name an article by message-id (0 its number,
    or for XHDR the message-id itself; XOVER takes none), the selected group's articles in a range, or
    the current article, and wait for a read as ARTICLE does: one read gives each article's line in
    turn (`post_ref.Fetch`), making none current. With none to give: 430, 412, 420, and for a range
    423, or for XOVER and XHDR 224 and 221 with an empty list, as INN answers. A metadata item other
    than `:bytes` and `:lines` is answered 503. LIST OVERVIEW.FMT and LIST HEADERS answer their fixed
    lists.

    AUTHINFO USER and PASS (RFC 4643 §2.3) where the host lets the connection log in, else 502 as
    after a login (§2.2); anything but USER or PASS and one argument, 501; in the clear, 483. USER
    is answered 381, its name kept until a 481 or the PASS after it, or at once 481 for a name longer
    than any account's; PASS without a name, 482; with one, and a password no longer than an
    account's may be, the two go to the host, unread and with no deadline until its verdict, 281 or
    481, of which 281 lets the connection post while the store accepts and carries a group. Over
    TLS, until logged in, the capabilities name AUTHINFO USER."""

    def __init__(self, revision: bytes, source: bytes, start: P.Start, checker: P.Checker) -> None:
        super().__init__(revision, source)
        self.store = P.Store(start, checker)
        self.opened = 0
        # the connections whose POST waits, by index and generation, in the order they came, and
        # those that wait for a read
        self.waiters: list[tuple[int, int]] = []
        self.readers: list[tuple[int, int]] = []

    def items(self, c: Conn) -> tuple[list[str], int, P.Article | P.Fetch | Listing | None]:
        """The replies the connection has had or is due, in order; where what it sent is read to;
        and its article not ended or not answered, its read not ended, or its listing going out, if
        any. A reply decided when given and not yet given, a waiting POST, an article not answered, a
        read not ended or a listing going out ends the list."""
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
            if r.startswith("listing ") and not c.listings[int(r[8:])].done:
                return out, at, c.listings[int(r[8:])]
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
        if r.startswith("listing "):
            return bytes(c.listings[int(r[8:])].sent)
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

    def listing(self, c: Conn) -> Listing | None:
        """The reply of many lines going out, from its first line until its terminating one."""
        return c.listings[-1] if c.listings and not c.listings[-1].done else None

    def busy(self, c: Conn) -> bool:
        """Whether a read waits for a place or answers it, a listing goes out, or a name and
        password are with the host."""
        return c.wanted is not None or self.fetch(c) is not None or self.listing(c) is not None or \
            c.checking is not None

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
        if c.waiting or (a is not None and a.ended) or c.wanted is not None or c.checking is not None:
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
        if c.pending() or c.checking is not None:
            return False
        if self.listing(c) is not None:
            return True
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
                self.conns[idx] = (gen, Conn(opened=t.now, activity=t.now, number=self.opened, greeted=greeted,
                                             posting=greeted, logins=event.logins, tls=event.tls))
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
                elif kind == "verdict" and c.checking is not None:
                    c.checking, c.logged = None, event.ok
                    c.decisions.append("auth-accepted" if event.ok else "auth-failed")
                    c.posting |= event.ok and self.store.accepting and bool(self.store.start.groups)
                    c.activity = t.now
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
        listing = self.listing(c)
        if listing is not None and not c.pending():
            self.list_turn(t, idx, gen, c, listing, action, sends)
            return
        f = self.fetch(c)
        if f is not None and not c.pending() and self.read_turn(t, idx, gen, c, f, action, sends):
            return
        if a is None and not c.pending() and self.next_line(c) == "post" and c.replies == len(self.replies(c)):
            self.post_due(t, idx, gen, c, action)
        if a is None and f is None and c.wanted is None and not c.pending() and c.replies == len(self.replies(c)):
            line = self.due_line(c)
            if line is not None and line[0] in ("lookup", "number", "current"):
                self.lookup_due(t, idx, gen, c, line[0], line[1])
            elif line is not None and line[0] == "overview":
                self.view_due(t, idx, gen, c, line[1])
        check = self.check_due(c) if a is None and f is None and not self.busy(c) and not c.pending() and \
            c.replies == len(self.replies(c)) else None
        if check is not None:
            if action is None or action.kind != "verify" or action.gen != gen or (action.data, action.secret) != check:
                raise Violation("unchecked", f"{idx}/{gen} not handed its name and password to check at {t.now}")
            c.checking, c.name, c.reading = check, None, False
            if c.answered is None:
                c.answered = t.now
            return
        if action is not None and action.kind == "verify":
            raise Violation("verify", f"{idx}/{gen} handed a name and password to check at {t.now} with none due")
        if c.wanted is not None and self.admitted_read(idx, gen):
            cmd, number, commit, view = c.wanted
            c.fetches.append(self.store.grant((idx, gen), cmd, commit, number, view))
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
            # An article whose XHDR line is left out gives nothing: its read goes on to the next.
            if f.whole() and f.given == len(f.out(identity)) and f.view is not None and f.view.rest:
                f.advance(identity)
            return False
        if action is None or action.kind != "send" or action.data != piece or action.gen != gen:
            sent = action.data[:40] if action is not None else None
            raise Violation("read-out", f"{idx}/{gen} sent {sent!r} at {t.now}, not the next of its read, "
                            f"{piece[:40]!r}")
        if f.given == 0 and f.number and f.view is None:
            # Its first line answers the command: only now is the article current (RFC 3977 §6.2.1.2).
            c.current = f.number
        f.given += len(piece)
        c.emitted += piece
        c.activity = t.now
        if f.whole() and f.given == len(f.out(identity)):
            if f.view is not None and f.view.rest:
                f.advance(identity)
            else:
                f.answered, f.owner = f"read {c.fetches.index(f)}", None
                c.replies += 1
        if action.read != self.read_wanted(c):
            raise Violation("read", f"{idx}/{gen} asked {'' if action.read else 'not '}to read at {t.now}")
        c.reading = action.read
        sends.append((idx, len(piece)))
        return True

    def lines_left(self, listing: Listing) -> list[tuple[int, bytes]]:
        """The lines of a listing still to go out, as the store is now, each with how far the
        listing has gone once it is out."""
        if listing.numbers is not None:
            return [(k + 1, b"%d\r\n" % n) for k, n in enumerate(listing.numbers[listing.at:], listing.at)]
        found = []
        for k, g in enumerate(self.store.start.groups[listing.at:], listing.at):
            if listing.patterns is None or wildmatch(listing.patterns, g):
                numbers = [n for n, _ in self.in_group(g)]
                low, high = (numbers[0], numbers[-1]) if numbers else (1, 0)
                found.append((k + 1, g + b" %d %d %s\r\n" % (high, low, b"y" if self.store.accepting else b"n")))
        return found

    def list_turn(self, t: Turn, idx: int, gen: int, c: Conn, listing: Listing, action: Action | None,
                  sends: list[tuple[int, int]]) -> None:
        """The turn of a connection a listing answers, with nothing untaken: the listing's next part
        sent, its lines that follow as many whole as one send holds, then its terminating line once
        it fits too."""
        part, at, done = b"", listing.at, False
        for after, line in self.lines_left(listing):
            if len(part) + len(line) > CHUNK:
                break
            part, at = part + line, after
        else:
            if len(part) + 3 <= CHUNK:
                part, done = part + b".\r\n", True
        if action is None or action.kind != "send" or action.gen != gen or action.data != part:
            sent = action.data[:40] if action is not None else None
            raise Violation("listing-out", f"{idx}/{gen} sent {sent!r} at {t.now}, not the next part of its "
                            f"listing, {part[:40]!r}")
        listing.sent += part
        listing.at, listing.done = at, done
        c.emitted += part
        c.activity = t.now
        if action.read != self.read_wanted(c):
            raise Violation("read", f"{idx}/{gen} asked {'' if action.read else 'not '}to read at {t.now}")
        c.reading = action.read
        sends.append((idx, len(part)))

    def listed(self, t: Turn, c: Conn, kind: str, ws: list[bytes]) -> str:
        """What a LISTGROUP, a LIST, or a DATE is answered, deciding it now; a LISTGROUP selects its
        group, the first article current, and lists the numbers in its range of the articles the
        group holds now."""
        if kind == "date":
            return "text " + (b"111 " + date_digits(t.wall) + P.CRLF).hex()
        if kind == "list-active":
            listing = Listing(bytearray(b"215 List of newsgroups follows\r\n"),
                              patterns=wildmat(ws[2]) if len(ws) > 2 else None)
        else:
            g = ws[1] if len(ws) > 1 else c.group
            if g is None:
                return "no-group"
            if g not in self.store.start.groups:
                return "no-such-group"
            span = article_range(ws[2]) if len(ws) > 2 else (1, NUMBER_MAX)
            if span is None:
                raise Violation("syntax", f"{ws[2]!r} taken for a range")
            lo, hi = span
            numbers = [n for n, _ in self.in_group(g)]
            c.group, c.current = g, numbers[0] if numbers else 0
            low, high = (numbers[0], numbers[-1]) if numbers else (1, 0)
            listing = Listing(bytearray(b"211 %d %d %d " % (len(numbers), low, high) + g + P.CRLF),
                              numbers=[n for n in numbers if lo <= n <= hi])
        c.listings.append(listing)
        return f"listing {len(c.listings) - 1}"

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
        c.wanted = (cmd, n, commit, None)
        if c.answered is None:
            c.answered = t.now
        if (idx, gen) not in self.readers:
            self.readers.append((idx, gen))

    def view_of(self, c: Conn, kept: bytes) -> tuple[str, int, J.Commit, P.View] | str:
        """The articles an OVER, XOVER, HDR or XHDR names, as the store holds them now: the first, with
        the number its line gives, and what is read of it and of those after it; or the reply when
        there is none (RFC 3977 §8.3.2, §8.5.2; for XOVER's and XHDR's empty range INN's empty list)."""
        ws = words(kept)
        legacy = ws[0].upper() in (b"XOVER", b"XHDR")
        name = ws[1] if ws[0].upper() in (b"HDR", b"XHDR") else None
        rest = ws[2:] if name is not None else ws[1:]
        arg = rest[0] if rest else None
        by_id = arg is not None and is_message_id(arg)
        if arg is not None and by_id:
            commit = self.store.found(arg)
            if commit is None:
                return "no-such-id"
            items = [(0, commit)]
        elif c.group is None:
            return "no-group"
        elif arg is not None:
            span = article_range(arg)
            if span is None:
                raise Violation("syntax", f"{arg!r} taken for a range")
            items = [x for x in self.in_group(c.group) if span[0] <= x[0] <= span[1]]
            if not items:
                return ("none-hdr" if name is not None else "none-over") if legacy else "no-range"
        else:
            items = [x for x in self.in_group(c.group) if c.current and x[0] == c.current]
            if not items:
                return "no-current"
        n, commit = items[0]
        return "hdr" if name is not None else "over", n, commit, P.View(legacy, name, by_id, items[1:])

    def view_due(self, t: Turn, idx: int, gen: int, c: Conn, kept: bytes) -> None:
        """An OVER or HDR that names articles the store holds: the connection waits for a read, which
        gives their lines one after another and makes none of them current."""
        found = self.view_of(c, kept)
        if isinstance(found, str):
            return
        c.wanted = found
        if c.answered is None:
            c.answered = t.now
        if (idx, gen) not in self.readers:
            self.readers.append((idx, gen))

    def post_due(self, t: Turn, idx: int, gen: int, c: Conn, action: Action | None) -> None:
        """A POST its connection is due an answer to: one at once, but for a slot it waits for."""
        if c.posting and self.store.accepting:
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
        if due in ("listgroup", "list-active", "date"):
            line = self.due_line(c)
            c.decisions.append(self.listed(t, c, due, words(line[1] if line else b"")))
            return
        if due == "overview":
            line = self.due_line(c)
            found = self.view_of(c, line[1] if line else b"")
            if not isinstance(found, str):
                raise Violation("read", f"{idx} {found[0]} answered at once, before a read")
            c.decisions.append(found)
            return
        if due in ("lookup", "number", "current", "group", "next", "last"):
            line = self.due_line(c)
            try:
                c.decisions.append(self.reader(c, due, words(line[1] if line else b"")))
            except Violation as error:
                raise Violation(error.kind, f"{idx} {error}") from None
            return
        if due == "capabilities":
            listed = "capabilities-post" if c.posting and self.store.accepting else "capabilities-reader"
            c.decisions.append(listed + "-auth" if c.logins and c.tls and not c.logged else listed)
        elif due == "authinfo":
            line = self.due_line(c)
            r = self.auth_reply(c, words(line[1])[1:] if line else [])
            if r == "check":
                raise Violation("check", f"{idx} answered AUTHINFO PASS at once, before its check")
            c.decisions.append(r)
            if r == "auth-user" and line:
                c.name = words(line[1])[2]
            elif r == "auth-failed":
                c.name = None
        elif due == "mode-reader":
            c.decisions.append("reader-posting" if c.posting and self.store.accepting else "reader-no-posting")
        elif due == "post":
            if not c.posting:
                # RFC 4643 §2.2: 480 where a login over TLS would let it post.
                login_posts = (c.logins and c.tls and not c.logged and self.store.accepting
                               and bool(self.store.start.groups))
                c.decisions.append("auth-required" if login_posts else "not-permitted")
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

    def auth_reply(self, c: Conn, args: list[bytes]) -> str:
        """What an AUTHINFO with these arguments is answered, `check` when its name and password go to
        the host."""
        if not c.logins or c.logged:
            return "auth-done"
        if len(args) != 2 or args[0].upper() not in (b"USER", b"PASS"):
            return "syntax"
        if not c.tls:
            return "encryption-required"
        if args[0].upper() == b"USER":
            return "auth-failed" if len(args[1]) > NAME_MAX else "auth-user"
        if c.name is None:
            return "auth-sequence"
        return "auth-failed" if len(args[1]) > PASSWORD_MAX else "check"

    def check_due(self, c: Conn) -> tuple[bytes, bytes] | None:
        """The name and the password its next line hands the host, if it is such an AUTHINFO PASS."""
        line = self.due_line(c)
        if line is None or line[0] != "authinfo":
            return None
        args = words(line[1])[1:]
        return (c.name or b"", args[1]) if self.auth_reply(c, args) == "check" else None

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
    if isinstance(j, PostJudge):
        if j.conns:
            raise Violation("leak", f"at the end connections {sorted(j.conns)} are still open, the store unchecked")
        try:
            j.store.finish()
        except P.Violation as error:
            raise Violation(error.kind, f"at the end: {error}") from None
