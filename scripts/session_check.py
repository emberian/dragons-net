#!/usr/bin/env python3
# SPDX-License-Identifier: AGPL-3.0-or-later
"""The session (`DN.News.SessionSpec`), driven by a simulated host and judged by `session_ref`.

A scenario is a set of clients: when each connects, what it sends and when, how much of what it is
sent it takes at once and how soon it takes more, when it stops taking for a while, and when it
shuts down its side or resets. The simulated host does what docs/decisions/0003-nntp-slice.md asks
of the real one: it gives each connection the lowest free index and the next generation of it, holds
back connections while every index is in use, reads from a connection only while the program's last
action asked to and everything it carried was taken, reports at most one input a connection a batch
and at most 512 bytes of it, reports a connection ready to write once the client takes more of what
it left, reports the end of input once the client's bytes are all read, takes the connections in
turn when more than a batch has something to report, and runs the next turn at the time the program
asked for or at once when anything waits to be reported. In some scenarios it also reports events
of a connection that is gone — input, readiness, the end of input and its close — while its index
is free and again once the index serves another, which the program has to leave alone; in one a
client is reported ready to write and still takes nothing. Some scenarios run with the longest and
the shortest identity that fit the replies. `dn-compiler session-model` answers the turns a line at
a time.

Every trace has to be one `session_ref.judge` accepts, and every scenario has to end with each
connection closed. Hosts that break the contract are answered with the code of the breach. Each rule
of the session broken in the model (`DN.News.SessionMutant`) has to be caught by the judge on some
scenario, and each defect planted in a recorded trace by the judge's check for it.
"""
from __future__ import annotations

import argparse
from collections.abc import Callable, Iterator
import copy
from dataclasses import dataclass, field
import itertools
from pathlib import Path
import queue
import random
import subprocess
import sys
import threading
from typing import IO, Self

sys.path.insert(0, str(Path(__file__).resolve().parent))
import lanes  # the path above is what makes these importable
from lanes import LaneError, Report
import session_ref as ref
from session_ref import Action, Event, Turn, Violation

REVISION, SOURCE = b"0123abc", b"https://example.org/dragons-net"
Identity = tuple[bytes, bytes]
IDENTITY: Identity = (REVISION, SOURCE)
# The longest identity that fits the replies, of the highest and the lowest visible byte, and the
# shortest.
LONGEST: Identity = (b"~" * 64, b"!" * 200)
SHORTEST: Identity = (b"r", b"s")
GREETING = len(ref.texts(REVISION, SOURCE)["greeting"])
BATCH, TURNS, TIMEOUT = 16, 20_000, 60
# The rules `DN.News.SessionMutant` breaks, by the name `dn-compiler session-model --mutant` takes.
MUTANTS = ("line-renewed", "no-line-deadline", "line-while-busy", "idle-not-renewed", "zero-take-counts",
           "blank-counts", "first-not-cleared", "read-not-resumed", "no-greeting", "stale-applied",
           "end-ignored", "resend-anytime", "wake-early", "answer-while-busy", "quit-tail")


class Unfinished(LaneError):
    """A scenario that could not run to its end, with the turns it had."""

    def __init__(self, message: str, trace: list[Turn]) -> None:
        super().__init__(message)
        self.trace = trace


@dataclass
class Client:
    opens: int
    sends: list[tuple[int, bytes]] = field(default_factory=list)
    shut: int | None = None
    reset: int | None = None
    # the most bytes of one send it takes, from `slow` on, and how long it takes to take more
    take: int | None = None
    slow: int = 0
    pace: int = 1
    # it takes nothing from the first time to the second
    pause: tuple[int, int] = (0, 0)
    # it is reported ready to write even while it takes nothing
    false_ready: bool = False

    def stream(self, now: int) -> bytes:
        return b"".join(data for at, data in self.sends if at <= now)

    def paused(self, now: int) -> bool:
        return self.pause[0] <= now < self.pause[1]

    def takes(self, now: int, length: int) -> int:
        if self.paused(now):
            return 0
        return length if self.take is None or now < self.slow else min(length, self.take)

    def ready_at(self, now: int) -> int:
        """When it is reported ready to write after leaving part of a send."""
        if self.false_ready or not self.paused(now + self.pace):
            return now + self.pace
        return max(now + self.pace, self.pause[1])


@dataclass
class Link:
    client: Client
    idx: int
    gen: int
    read: int = 0
    reading: bool = False
    unsent: bool = False
    ready: int = 0
    ended: bool = False

    def asked(self) -> bool:
        return self.reading and not self.unsent


def model_command(mutant: str | None = None) -> list[str]:
    """`dn-compiler session-model`, with a rule broken or not."""
    return [str(lanes.DN_COMPILER), "session-model", *(["--mutant", mutant] if mutant else [])]


class Speaker:
    """A session run as a process, the model or the compiled program, that speaks the line protocol
    of `dn-compiler session-model` a line at a time, with a bound on every wait."""

    def __init__(self, command: list[str], identity: Identity = IDENTITY) -> None:
        self.proc = subprocess.Popen(command, stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                                     text=True, bufsize=1)
        self.lines = lanes.Lines(self.pipe(self.proc.stdout))
        self.complaints: list[str] = []
        threading.Thread(target=self.listen, args=(self.pipe(self.proc.stderr),), daemon=True).start()
        self.say(f"identity {identity[0].hex() or '-'} {identity[1].hex() or '-'}")

    def listen(self, stream: IO[str]) -> None:
        for line in stream:
            self.complaints.append(line.rstrip("\n"))

    def why(self) -> str:
        """What the process said on stderr last, if anything."""
        return f", saying {self.complaints[-1]!r}" if self.complaints else ""

    def __enter__(self) -> Self:
        return self

    def __exit__(self, *_: object) -> None:
        if self.proc.poll() is None:
            self.proc.kill()
        self.proc.wait(timeout=TIMEOUT)
        for stream in (self.proc.stdin, self.proc.stdout, self.proc.stderr):
            if stream:
                stream.close()

    def pipe(self, stream: IO[str] | None) -> IO[str]:
        if stream is None:
            raise LaneError("the session has no pipe")
        return stream

    def say(self, line: str) -> None:
        try:
            self.pipe(self.proc.stdin).write(line + "\n")
        except OSError as error:
            raise LaneError(f"the session no longer listens ({error}){self.why()}") from None

    def hear(self) -> list[str]:
        try:
            self.pipe(self.proc.stdin).flush()
            line = self.lines.get(TIMEOUT)
        except OSError as error:
            raise LaneError(f"the session no longer listens ({error}){self.why()}") from None
        except queue.Empty:
            raise LaneError(f"the session gave no answer in {TIMEOUT} s") from None
        if not line:
            raise LaneError(f"the session stopped answering (status {self.ended()}){self.why()}")
        return line.rstrip("\n").split(" ")

    def ended(self) -> int:
        try:
            return self.proc.wait(timeout=TIMEOUT)
        except subprocess.TimeoutExpired:
            raise LaneError(f"the session did not end in {TIMEOUT} s") from None

    def output(self) -> list[str]:
        """Every line the session answers until it ends."""
        out: list[str] = []
        while True:
            try:
                line = self.lines.get(TIMEOUT)
            except queue.Empty:
                raise LaneError(f"the session gave no answer in {TIMEOUT} s") from None
            if not line:
                return out
            out.append(line.rstrip("\n"))

    def turn(self, now: int, events: list[Event]) -> list[Action] | int:
        self.say(f"turn {now}")
        for e in events:
            self.say(" ".join([e.kind, str(e.idx), str(e.gen), *([e.data.hex() or "-"] if e.kind == "recv" else [])]))
        self.say("go")
        actions: list[Action] = []
        while (words := self.hear()) != ["done"]:
            match words:
                case ["stop", code]:
                    return int(code)
                case ["send", idx, gen, data, "0" | "1" as read]:
                    actions.append(Action("send", int(idx), int(gen), b"" if data == "-" else bytes.fromhex(data),
                                          read == "1"))
                case ["graceful" | "close" as kind, idx, gen]:
                    actions.append(Action(kind, int(idx), int(gen)))
                case _:
                    raise LaneError(f"the session answered {' '.join(words)}")
        return actions

    def settle(self, took: list[int]) -> int | str:
        self.say(" ".join(["took", *map(str, took)]))
        match self.hear():
            case ["deadline", at]:
                return int(at)
            case ["stop", code]:
                return f"stop {code}"
            case words:
                raise LaneError(f"the session answered {' '.join(words)} to what was taken")


def run(clients: list[Client], command: list[str], ghosts: bool = False, identity: Identity = IDENTITY) -> list[Turn]:
    """The turns of one scenario, as the simulated host lives them."""
    trace: list[Turn] = []
    with Speaker(command, identity) as session:
        try:
            simulate(session, clients, ghosts, trace)
        except LaneError as error:
            raise Unfinished(str(error), trace) from None
    return trace


def simulate(session: Speaker, clients: list[Client], ghosts: bool, trace: list[Turn]) -> None:
    links: dict[int, Link] = {}
    gens = [0] * ref.CONNS
    waiting = sorted(range(len(clients)), key=lambda k: clients[k].opens)
    echoes: list[Event] = []
    # the generation of a connection gone, whose events come again once its index serves another
    graves: dict[int, int] = {}
    now, start = min((c.opens for c in clients), default=1), 0
    for _ in range(TURNS):
        events = echoes[:BATCH]
        echoes = echoes[BATCH:]
        cut = bool(echoes)
        order = [(start + k) % ref.CONNS for k in range(ref.CONNS)]
        start = (start + 1) % ref.CONNS
        for idx in order:
            if idx not in links:
                continue
            link = links[idx]
            report = news(link, now)
            if report is None:
                continue
            if len(events) == BATCH:
                cut = True
                break
            events.append(report)
            if report.kind == "closed":
                del links[idx]
                if ghosts:
                    graves[idx] = link.gen
                    echoes += haunting(idx, link.gen)
            elif report.kind == "recv":
                link.read += len(report.data)
            elif report.kind == "end":
                link.ended = True
        while waiting and clients[waiting[0]].opens <= now:
            free = [i for i in range(ref.CONNS) if i not in links]
            if not free or len(events) == BATCH:
                break
            idx = free[0]
            gens[idx] += 1
            links[idx] = Link(clients[waiting.pop(0)], idx, gens[idx])
            events.append(Event("open", idx, gens[idx]))
            if idx in graves:
                echoes += haunting(idx, graves.pop(idx))
        answer = session.turn(now, events)
        if isinstance(answer, int):
            raise LaneError(f"the session stopped with code {answer} on a host that kept the contract")
        took = []
        for action in answer:
            target = links.get(action.idx)
            if target is None or target.gen != action.gen:
                raise LaneError(f"an action for {action.idx}/{action.gen}, which the host does not hold")
            if action.kind == "send":
                data = action.data
                k = target.client.takes(now, len(data))
                took.append(k)
                target.unsent = k < len(data)
                target.ready = target.client.ready_at(now)
                target.reading = action.read
            else:
                del links[action.idx]
                if ghosts:
                    graves[action.idx] = action.gen
                    echoes += haunting(action.idx, action.gen)
        deadline = session.settle(took)
        if isinstance(deadline, str):
            raise LaneError(f"the session answered {deadline} to what the host took")
        trace.append(Turn(now, events, answer, took, deadline))
        if not links and not waiting and not echoes:
            return
        now = next_time(now, deadline, links, clients, waiting, cut or bool(echoes))
    raise LaneError(f"the scenario had not ended after {TURNS} turns, at {now}")


def haunting(idx: int, gen: int) -> list[Event]:
    """Every kind of event of a connection gone, as a host may still report them."""
    return [Event("closed", idx, gen), Event("recv", idx, gen, b"QUIT\r\n"), Event("writable", idx, gen),
            Event("end", idx, gen)]


def news(link: Link, now: int) -> Event | None:
    """What the host has to report of a connection at `now`, if anything."""
    c = link.client
    if c.reset is not None and c.reset <= now:
        return Event("closed", link.idx, link.gen)
    if link.unsent:
        return Event("writable", link.idx, link.gen) if now >= link.ready else None
    if link.asked():
        stream = c.stream(now)
        if link.read < len(stream):
            return Event("recv", link.idx, link.gen, stream[link.read:link.read + ref.CHUNK])
        if c.shut is not None and c.shut <= now and not link.ended and link.read == len(c.stream(c.shut)):
            return Event("end", link.idx, link.gen)
    return None


def next_time(now: int, deadline: int, links: dict[int, Link], clients: list[Client], waiting: list[int],
              pending: bool) -> int:
    """When the host's next turn comes: at once if something waits to be reported, else the
    program's deadline or the first thing that happens."""
    free = len(links) < ref.CONNS
    if pending or (deadline and deadline <= now) or (waiting and free and clients[waiting[0]].opens <= now):
        return now
    if any(news(link, now) is not None for link in links.values()):
        return now
    times = [deadline] if deadline else []
    times += [clients[k].opens for k in waiting] if free else []
    for link in links.values():
        c = link.client
        times += [t for t in (c.reset, c.shut) if t is not None]
        if link.unsent:
            times.append(link.ready)
        elif link.asked():
            times += [at for at, _ in c.sends]
    later = [t for t in times if t > now]
    if not later:
        raise LaneError(f"nothing left to happen after {now}, with connections open")
    return min(later)


def ascii_lines(*lines: str) -> bytes:
    return b"".join(line.encode() + b"\r\n" for line in lines)


CASES = ("CAPABILITIES", "capabilities foo", "CAPABILITIES 1x", "CAPABILITIES ab", "CAPABILITIES a@b",
         "CAPABILITIES a[b", "CAPABILITIES a`b", "CAPABILITIES a{b", "CAPABILITIES @ab", "CAPABILITIES [ab",
         "CAPABILITIES `ab", "CAPABILITIES {ab", "CAPABILITIES a-.9", "HELP", "hElP",
         "HELP x", "QUIT x", "\tHEAD\t", "HEAD", "HEAD 0", "HEAD 05", "HEAD 2147483647", "HEAD 2147483648",
         "HEAD 99999999999999999999", "HEAD 00000000000000001", "HEAD +5", "HEAD -1", "HEAD 12abc",
         "HEAD <a@b>", "HEAD <a b>", "HEAD <>", "HEAD <a>b>", "HEAD <a@b> extra", "HEAD <" + "a" * 248 + ">",
         "HEAD <" + "a" * 249 + ">", "HEAD <\x7f>", "HEAD <~!>", "STAT", "STAT 1",
         "STAT <x@y>", "STAT z", "MODE READER", "XY", "LIST", "", "  \t ")
TRANSCRIPT = ascii_lines("CAPABILITIES", "help", "", "HEAD <a@b>", "STAT 12abc", "QUIT", "HELP")
HELP = ascii_lines("HELP")
Scenario = tuple[str, list[Client], bool, Identity]


DRAWN, DRAWN_SEED = 300, 20261002
PIECES = (b"HELP\r\n", b"HEL", b"P\r\n", b"HE", b"  ", b"\t", b"\r\n", b"\r", b"\n", b"STAT 1\r\n",
          b"QUIT\r\n", b"FOO" + b"x" * 600 + b"\r\n")
GAPS = (0, 1, 2, 10_000, 179_999, 180_000, 180_001, 1_800_000)


def drawn() -> Iterator[Client]:
    """Clients drawn at random, the same on every run: pieces of lines sent after gaps that land on
    and around the deadlines, now and then reading slowly, pausing, ending their input or reset."""
    rng = random.Random(DRAWN_SEED)  # noqa: S311 -- a fixed seed, so that every run draws the same clients
    for _ in range(DRAWN):
        at = rng.choice((1, 5))
        sends = []
        for _ in range(rng.randint(1, 6)):
            at += rng.choice(GAPS)
            sends.append((at, b"".join(rng.choice(PIECES) for _ in range(rng.randint(1, 3)))))
        client = Client(1, sends)
        if rng.random() < 0.2:
            client.take, client.slow, client.pace = rng.choice((1, 7, 60)), 5, rng.choice((1, 1_000))
        if rng.random() < 0.1:
            client.pause = (at, at + rng.choice(GAPS[3:]))
        if rng.random() < 0.15:
            client.shut = at + rng.choice(GAPS)
        elif rng.random() < 0.05:
            client.reset = at + rng.choice(GAPS)
        yield client


def scenarios() -> Iterator[Scenario]:
    for name, clients, ghosts in plain_scenarios():
        yield name, clients, ghosts, IDENTITY
    for k, client in enumerate(drawn()):
        yield f"drawn client {k} of seed {DRAWN_SEED}", [client], False, IDENTITY
    commands = [Client(1, [(5, ascii_lines(*CASES, "QUIT"))])]
    pipeline = [Client(1, [(5, ascii_lines(*["HELP", "CAPABILITIES"] * 20, "QUIT"))], take=100)]
    for label, identity in (("the longest", LONGEST), ("the shortest", SHORTEST)):
        yield f"commands with {label} identity", commands, False, identity
        yield f"a long pipeline with {label} identity", pipeline, False, identity


def plain_scenarios() -> Iterator[tuple[str, list[Client], bool]]:
    yield "commands", [Client(1, [(5, ascii_lines(*CASES, "QUIT"))])], False
    for at in range(1, len(TRANSCRIPT)):
        yield f"cut at {at}", [Client(1, [(5, TRANSCRIPT[:at]), (9, TRANSCRIPT[at:])])], False
    yield "a byte at a time", [Client(1, [(5 + k, TRANSCRIPT[k:k + 1]) for k in range(len(TRANSCRIPT))])], False
    for take in (1, 7, 60):
        yield f"a reader taking {take}", [Client(1, [(5, TRANSCRIPT)], take=take)], False
    yield "a reader that waits", [Client(1, [(5, TRANSCRIPT)], pause=(0, 5_000))], False
    yield "a long pipeline", [Client(1, [(5, ascii_lines(*["HELP", "STAT 1"] * 40, "QUIT"))], take=100)], False
    odd = (b"\n", b" \t\n", b"HELP\n", b"HELP\0\r\n", b"HE\rLP\r\n", b"FOO\n", b"\0\r\n",
           b"HELP " + b"x" * 600 + b"\r\n", b"FOO" + b"x" * 600 + b"\r\n", b" " * 700 + b"\r\n",
           b"HEAD " + b"1" * 505 + b"\r\n", b"HEAD " + b"1" * 506 + b"\r\n", b"QUIT\r\n")
    yield "odd lines", [Client(1, [(5, b"".join(odd))])], False
    yield "a QUIT and more", [Client(1, [(5, ascii_lines("QUIT", "HELP")), (9, HELP)])], False
    yield "input ending mid-line", [Client(1, [(5, b"HELP\r\nCAPAB")], shut=9)], False
    yield "input ending at once", [Client(1, [], shut=3)], False
    yield "input ending after commands", [Client(1, [(5, ascii_lines("HELP", "STAT"))], shut=5, take=9)], False
    yield "input ending with a line begun and output untaken", [
        Client(1, [(5, b"HELP\r\nHE")], shut=6, take=10, slow=5, pace=60_000)], False
    yield "no first command", [Client(1)], False
    yield "a clock of zero", [Client(0, [(0, ascii_lines("HELP", "HELP"))])], False
    yield "only empty lines", [Client(1, [(5 + 1_000 * k, b"\r\n") for k in range(15)])], False
    yield "a first command just in time", [Client(1, [(10_000, ascii_lines("HELP", "QUIT"))])], False
    yield "a first command too late", [Client(1, [(10_001, HELP)])], False
    yield "silence after a command", [Client(1, [(5, HELP)])], False
    yield "empty lines after a command", [
        Client(1, [(5, HELP)] + [(60_000 * k, b"\r\n") for k in range(1, 40)])], False
    yield "a command just before the inactivity deadline", [Client(1, [(5, HELP), (1_800_004, HELP)])], False
    yield "a command at the inactivity deadline", [Client(1, [(5, HELP), (1_800_005, HELP)])], False
    yield "a reader slower than the inactivity deadline", [
        Client(1, [(5, HELP)], take=10, slow=5, pace=600_000)], False
    yield "a reader that stops reading", [Client(1, [(5, HELP)], pause=(5, 10 ** 9))], False
    yield "a reader reported ready that takes nothing", [
        Client(1, [(5, HELP)], take=10, slow=5, pace=600_000, pause=(10, 10 ** 9), false_ready=True)], False
    yield "an unfinished line", [Client(1, [(5, b"HELP\r\nHEL")])], False
    yield "a line finished just in time", [Client(1, [(5, HELP), (10, b"HEL"), (180_009, b"P\r\n")])], False
    yield "a line finished too late", [Client(1, [(5, HELP), (10, b"HEL"), (180_010, b"P\r\n")])], False
    yield "a line a byte a minute", [Client(1, [(5, HELP)] + [(6 + 60_000 * k, b"H") for k in range(5)])], False
    yield "a line answered and the next begun in one batch", [
        Client(1, [(5, HELP), (10, b"HEL"), (11, b"P\r\nHE")])], False
    yield "a white-space line and the next begun in one batch", [
        Client(1, [(5, HELP), (10, b"  "), (11, b"\r\nHE")])], False
    yield "an empty line and the next begun in one batch", [
        Client(1, [(5, HELP), (10, b"\r"), (11, b"\nHE")])], False
    yield "a line begun while output is untaken", [
        Client(1, [(5, b"HELP\r\nHE")], take=10, slow=5, pace=60_000)], False
    yield "a reset", [Client(1, [(5, HELP)], reset=6, take=10)], False
    yield "a crowd", [Client(1 + k % 3, [(5, ascii_lines("HELP", "QUIT"))], take=None if k % 2 else 50)
                      for k in range(70)], False
    yield "seventy clients holding sixty-four connections", [Client(1, [(5, HELP)]) for _ in range(70)], False
    yield "events of connections gone", [
        Client(1 + k, [(5 + k, ascii_lines("HELP", "QUIT"))], reset=7 if k % 3 == 0 else None, take=30)
        for k in range(12)] + [Client(20 + k, [(30, HELP)]) for k in range(12)], True
    yield "a slow reader among busy ones", [Client(1, [(5, HELP)], take=5, slow=5, pace=1_000)] + [
        Client(1, [(5 + 7 * k, HELP) for k in range(30)]) for _ in range(3)], False


def breaches() -> Iterator[tuple[str, list[str], int]]:
    """Scripts a host breaks the contract in, and the code the session has to stop with."""
    begin = ["turn 1", "open 0 1", "go", f"took {GREETING}"]
    yield "more events than a batch", ["turn 1", *[f"open {k} 1" for k in range(17)], "go"], 1
    yield "more bytes than a chunk", [*begin, "turn 2", "recv 0 1 " + "41" * 513, "go"], 2
    yield "an index past the table", ["turn 1", "open 64 1", "go"], 3
    yield "input before the greeting was taken", ["turn 1", "open 0 1", "go", "took 0", "turn 2",
                                                  "recv 0 1 41", "go"], 4
    yield "two inputs in one batch", [*begin, "turn 2", "recv 0 1 41", "recv 0 1 41", "go"], 4
    yield "bytes and the end of input in one batch", [*begin, "turn 2", "recv 0 1 41", "end 0 1", "go"], 4
    yield "more taken than sent", ["turn 1", "open 0 1", "go", f"took {GREETING + 1}"], 5
    yield "a count for no send", ["turn 1", "go", "took 1"], 5
    yield "an index opened twice", [*begin, "turn 2", "open 0 2", "go"], 6
    yield "a clock going back", ["turn 5", "go", "took", "turn 4", "go"], 7
    yield "a clock past its limit", [f"turn {2 ** 62}", "go"], 7


def breach_output(script: list[str], command: list[str], identity: Identity = IDENTITY) -> tuple[list[str], str]:
    """What a session answers to a whole script, which it may stop reading before its end, and
    how it ended if not well."""
    with Speaker(command, identity) as session:
        stdin = session.pipe(session.proc.stdin)
        try:
            stdin.write("".join(line + "\n" for line in script))
            stdin.close()
        except OSError:
            pass
        out = session.output()
        status = session.ended()
        return out, f" and ended with status {status}{session.why()}" if status else ""


def check_breach(script: list[str], code: int, command: list[str], identity: Identity = IDENTITY) -> list[str]:
    """The session's answers to a script that breaks the contract, which have to end with the code."""
    out, ended = breach_output(script, command, identity)
    if ended or out[-1:] != [f"stop {code}"]:
        raise LaneError(f"the session answered {out[-3:]}{ended}, not stop {code}")
    return out


def sends(trace: list[Turn]) -> list[tuple[Turn, int, int]]:
    """Each send of a trace: its turn, its place among the turn's actions, and among its sends."""
    found = []
    for t in trace:
        places = [k for k, a in enumerate(t.actions) if a.kind == "send"]
        found += [(t, k, n) for n, k in enumerate(places)]
    return found


def replies(trace: list[Turn]) -> list[tuple[Turn, int, int]]:
    return [(t, k, n) for t, k, n in sends(trace) if t.actions[k].data[:3].isdigit()]


def swap_replies(trace: list[Turn]) -> None:
    (t1, k1, n1), (t2, k2, n2) = next((a, b) for a, b in itertools.pairwise(replies(trace)[1:])
                                      if a[0].actions[a[1]].data != b[0].actions[b[1]].data)
    a1, a2 = t1.actions[k1], t2.actions[k2]
    t1.actions[k1], t2.actions[k2] = a1._replace(data=a2.data), a2._replace(data=a1.data)
    t1.took[n1], t2.took[n2] = len(a2.data), len(a1.data)


def double_reply(trace: list[Turn]) -> None:
    t, k, n = replies(trace)[1]
    a = t.actions[k]
    t.actions[k] = a._replace(data=a.data * 2)
    t.took[n] = len(a.data) * 2


def change_byte(trace: list[Turn]) -> None:
    t, k, _ = replies(trace)[2]
    a = t.actions[k]
    t.actions[k] = a._replace(data=a.data[:-3] + b"X" + a.data[-2:])


def read_early(trace: list[Turn]) -> None:
    t, k, _ = next(s for s in replies(trace) if not s[0].actions[s[1]].read)
    t.actions[k] = t.actions[k]._replace(read=True)


def answer_before_taken(trace: list[Turn]) -> None:
    t, k, _ = next(s for s in sends(trace) if s[0].actions[s[1]].data and not s[0].actions[s[1]].data[:3].isdigit())
    later = next(s for s in replies(trace) if s[0].now > t.now)
    t.actions[k] = t.actions[k]._replace(data=later[0].actions[later[1]].data)


def resend_early(trace: list[Turn]) -> None:
    for t, u in itertools.pairwise(trace):
        for _, k, n in sends([t]):
            a = t.actions[k]
            quiet = not any(e.idx == a.idx for e in u.events) and not any(b.idx == a.idx for b in u.actions)
            if t.took[n] < len(a.data) and quiet:
                u.actions.append(a._replace(data=a.data[t.took[n]:]))
                u.took.append(0)
                return
    raise LaneError("no connection left waiting for the host to plant a defect on")


def close_early(trace: list[Turn]) -> None:
    t = trace[1]
    t.actions = [Action("close", t.actions[0].idx, t.actions[0].gen)]
    t.took = []


def no_close(trace: list[Turn]) -> None:
    t = next(t for t in trace if any(a.kind == "close" for a in t.actions))
    t.actions = [a for a in t.actions if a.kind != "close"]


def graceful_early(trace: list[Turn]) -> None:
    t = next(t for t in trace if any(e.kind == "recv" for e in t.events))
    t.actions = [Action("graceful", t.actions[0].idx, t.actions[0].gen)]
    t.took = []


def graceful_untaken(trace: list[Turn]) -> None:
    t, _, n = next(s for s in sends(trace) if s[0].actions[s[1]].data == b"205 Bye\r\n")
    t.took[n] = 3
    t.deadline = t.now + ref.INACTIVITY


def late_turn(trace: list[Turn]) -> None:
    t = next(t for t in trace if t.deadline == t.now)
    t.deadline = t.now + 1


def early_turn(trace: list[Turn]) -> None:
    t = next(t for t in trace if t.deadline > t.now + 1)
    t.deadline -= 1


def no_greeting(trace: list[Turn]) -> None:
    t = trace[0]
    t.actions, t.took = [], []


def stranger(trace: list[Turn]) -> None:
    trace[1].actions.append(Action("send", 9, 1, b"", True))
    trace[1].took.append(0)


# Defects planted in a recorded trace: (name, scenario, the kind of violation, the change).
Plant = Callable[[list[Turn]], None]
PLANTS: list[tuple[str, str, str, Plant]] = [
    ("replies out of order", "commands", "order", swap_replies),
    ("a reply twice in one send", "commands", "whole", double_reply),
    ("a byte of a reply changed", "commands", "order", change_byte),
    ("reading with a line unanswered", "a long pipeline", "read", read_early),
    ("a reply before the last was taken", "a reader taking 7", "untaken", answer_before_taken),
    ("output sent again before the host reported it ready", "a slow reader among busy ones", "unready",
     resend_early),
    ("a close with no deadline passed", "commands", "close", close_early),
    ("no close at a deadline", "no first command", "missed", no_close),
    ("a graceful close with lines unanswered", "input ending mid-line", "graceful-unanswered", graceful_early),
    ("a graceful close before the 205 was taken", "a QUIT and more", "graceful-untaken", graceful_untaken),
    ("the next turn late", "a long pipeline", "turn", late_turn),
    ("the next turn early", "silence after a command", "turn", early_turn),
    ("no greeting", "commands", "greeting", no_greeting),
    ("an action for a connection not open", "commands", "stranger", stranger),
]


def caught(mutant: str, all_scenarios: list[Scenario]) -> str:
    """The first scenario on which the judge refuses the session with `mutant` broken; a scenario
    the broken session cannot finish is judged on the turns it had."""
    for name, clients, ghosts, identity in all_scenarios:
        try:
            trace = run(clients, model_command(mutant), ghosts, identity)
        except Unfinished as error:
            trace = error.trace
        try:
            ref.judge(*identity, trace)
        except Violation as error:
            return f"{name}: {error}"
    raise LaneError(f"the judge accepted the session with {mutant} on every scenario")


def check() -> Report:
    all_scenarios = list(scenarios())
    turns = 0
    traces = {}
    for name, clients, ghosts, identity in all_scenarios:
        trace = run(clients, model_command(), ghosts, identity)
        try:
            ref.judge(*identity, trace)
        except Violation as error:
            raise LaneError(f"scenario {name!r}: {error}") from None
        traces[name] = trace
        turns += len(trace)
    for name, script, code in breaches():
        try:
            check_breach(script, code, model_command())
        except LaneError as error:
            raise LaneError(f"breach {name!r}: {error}") from None
    mutants = {m: caught(m, all_scenarios) for m in MUTANTS}
    planted = {}
    for name, scenario, kind, plant in PLANTS:
        trace = copy.deepcopy(traces[scenario])
        plant(trace)
        try:
            ref.judge(REVISION, SOURCE, trace)
        except Violation as error:
            if error.kind != kind:
                raise LaneError(f"the planted {name!r} was caught as {error.kind}, not {kind}: {error}") from None
            planted[name] = str(error)
            continue
        raise LaneError(f"the planted {name!r} was not caught")
    lanes.require_quoted({"docs/baseline.md": [f"{len(traces)} scenarios and {turns:,} turns"]})
    return Report("checked", None, [], {"scenarios": len(traces), "turns": turns,
                                        "breaches": sum(1 for _ in breaches()), "mutants_caught": mutants,
                                        "planted_defects_caught": planted})


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.parse_args()
    lanes.lane_main("SESSION MODEL", lanes.ROOT / "build/session-model", check)


if __name__ == "__main__":
    main()
