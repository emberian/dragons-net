#!/usr/bin/env python3
# SPDX-License-Identifier: AGPL-3.0-or-later
"""The session's program (`DN.Server.Session`), compiled, held against its model turn by turn.

The gate prints the program; CakeML compiles it without `--main_return`; `native/session_host.c`
runs it and speaks the line protocol of `dn-compiler session-model`, so the host simulator of
`scripts/session_check.py` drives the compiled code exactly as it drives the model. Every scenario
is run on both and the two traces — every batch, every action, what the host took, every next
turn — have to be the same. So do their whole answers to each host that breaks the contract, to
scripts at the edges of what it allows, and to hosts drawn at random from a fixed seed. Hosts that
break the contract in ways the model's protocol cannot say — an identity that does not fit the
replies, an event of no kind the layout has — have to stop the compiled code with their codes. The
host checks, on every call and at the end of the run, the heap header, and the heap before the
program's first area and past its layout, which it fills before the run so that the program cannot
lean on what it did not write.

Each defect planted in the printed program has to be caught, and caught the way it names.
"""
from __future__ import annotations

import argparse
from collections import Counter
from collections.abc import Iterator
import os
from pathlib import Path
import random
import re
import sys

sys.path.insert(0, str(Path(__file__).resolve().parent))
import lanes  # the path above is what makes these importable
from lanes import NATIVE, ROOT, LaneError, Report
import session_check as sessions
from session_check import GREETING, IDENTITY, LONGEST, SHORTEST, SOURCE, Identity, Speaker
from session_ref import Turn

OUT = ROOT / "build/session"
HOST = NATIVE / "session_host.c"
HOSTS = [HOST, NATIVE / "cake_header.c", *lanes.RUNTIME]
LIMIT = 2 ** 62
# The hosts drawn at random: how many, how many turns each at most, and the seed.
RUNS, STEPS, SEED = 200, 60, 20_260_928

# Defects planted in the printed program: (name, a pattern, what it becomes, how many times, and
# what the message that catches it says).
TRACE = "differs at turn"
DEFECTS = [
    ("the first command's deadline a second late", r"now \+ 10000;", "now + 11000;", 1, TRACE),
    ("a line's deadline a millisecond late", r"now \+ 180000;", "now + 180001;", 2, TRACE),
    ("keywords compared with regard to case", r"\(32 \* \(", "(0 * (", 5, TRACE),
    ("an article number of any size", r"val <= 2147483647", "val <= 9999999999999999", 1, TRACE),
    ("a bare LF ending a command", r"if cr & \(bad == 0\) \{", "if bad == 0 {", 1, TRACE),
    ("an overlong line with no word left unanswered", r"if kind == 3 \{(\s*)r = 6;", r"if kind == 3 {\1r = 0;", 1,
     TRACE),
    ("a message-id of 251 bytes accepted", r"\(l1 <= 250\)", "(l1 <= 251)", 1, TRACE),
    ("a byte after Z taken for a letter inside a keyword",
     r"ok = 0 < \(\(0 < \(\(0 < \(\(\(64 < cz\) & \(cz < 91\)\)", "ok = 0 < ((0 < ((0 < (((64 < cz) & (cz < 92))",
     1, TRACE),
    ("output sent again before the host reports it ready", r"if \(lds 1 \(cb \+ 32\)\) == 0 \{", "if 1 {", 1, TRACE),
    ("lines after a QUIT answered", r"st cb \+ 16, 1;", "st cb + 16, 0;", 1, TRACE),
    ("output taken not counted as activity", r"if 0 < tk \{(\s*)st cb \+ 48, now \+ 1800000;",
     r"if 0 < tk {\1st cb + 48, lds 1 (cb + 48);", 1, TRACE),
    ("a send of which nothing was taken counted as activity", r"if 0 < tk \{", "if 0 <= tk {", 1, TRACE),
    ("reading asked with a line held",
     r"var wants = \(\(lds 1 \(cb \+ 16\)\) == 0\) & \(\(lds 1 \(cb \+ 80\)\) == \(lds 1 \(cb \+ 72\)\)\);",
     "var wants = (lds 1 (cb + 16)) == 0;", 1, TRACE),
    ("received bytes not held", r"st cb \+ 72, el;", "st cb + 72, 0;", 1, TRACE),
    ("input of a connection gone applied", r"(?s)(if ek == 2 \{.*?)if lv \{", r"\1if lds 1 cb {", 1,
     "code 4 on a host that kept the contract"),
    ("readiness of a connection gone applied", r"if ek == 3 \{(\s*)if lv \{", r"if ek == 3 {\1if lds 1 cb {", 1,
     TRACE),
    ("the end of input of a connection gone applied", r"if ek == 4 \{(\s*)if lv \{", r"if ek == 4 {\1if lds 1 cb {",
     1, "code 4 on a host that kept the contract"),
    ("the table not emptied at the start", r"while zt < 64 \{", "while zt < 0 {", 1,
     "code 6 on a host that kept the contract"),
    ("the longest revision refused", r"\(64 < rvl\)", "(63 < rvl)", 1, "code 9 on a host that kept the contract"),
    ("an identity with a space accepted", r"\(cz < 33\)", "(cz < 32)", 2, "not stop 9"),
    ("an event of an unknown kind accepted", r"\(5 < ek\)", "(6 < ek)", 1, "not stop 8"),
    ("a clock going back accepted", r"\(now < \(lds 1 \(@base \+ \d+\)\)\)", "(now < 0)", 1, "not stop 7"),
    ("a clock refused just below its limit", r"4611686018427387904 <= now", "4611686018427387903 <= now", 1,
     "at the edge 'a clock just below its limit'"),
    ("a word to read of two", r"st slot \+ 32, wants;", "st slot + 32, wants * 2;", 1, "word to read is 2"),
    ("a store past the program's layout", r"st @base \+ \d+, now;", "st @base + 200000, now;", 1,
     "wrote past its layout"),
    ("a store before the program's first area", r"st @base \+ 64, 2;", "st @base + 64, 2;\n  st @base + 48, 7;", 1,
     "wrote before its layout"),
    ("a store past the layout as the run stops", r"st @base \+ 45000, 7;",
     "st @base + 200000, 1;\n      st @base + 45000, 7;", 1, "the end of the run: the program wrote past its layout"),
]


def build(cake: str, name: str, source: str) -> Path:
    """Compile a program without `--main_return`, make its bitmaps label global for the heap
    header (native/cake_header.c), and link it with the host."""
    pnk = OUT / f"{name}.pnk"
    pnk.write_text(source)
    asm = lanes.assemble(cake, pnk, main_return=False)
    text = asm.read_text()
    if text.count("\ncake_bitmaps:\n") != 1:
        raise LaneError(f"{asm.name}: the bitmaps label is not where the host expects it")
    asm.write_text(text.replace("\ncake_bitmaps:\n", "\n     .globl cake_bitmaps\ncake_bitmaps:\n"))
    return lanes.link(OUT / name, [HOST, NATIVE / "cake_header.c", NATIVE / "cake_runtime.c", asm],
                      includes=[OUT])


def plant(source: str, pattern: str, becomes: str, times: int) -> str:
    planted, found = re.subn(pattern, becomes, source)
    if found != times:
        raise LaneError(f"the program holds {pattern!r} {found} times, not {times}, for a planted defect")
    return planted


def first_difference(expected: list[Turn], got: list[Turn], broken: str | None) -> str | None:
    """Where a trace first differs from the model's: at a turn both have, else where it broke
    off, else in its length."""
    for k, (e, g) in enumerate(zip(expected, got, strict=False)):
        if e != g:
            return f"{TRACE} {k}, at {e.now}: {g.actions} then {g.deadline}, the model {e.actions} then {e.deadline}"
    if broken:
        return broken
    if len(expected) != len(got):
        return f"{len(got)} turns, the model {len(expected)}"
    return None


def trace(clients: list[sessions.Client], command: list[str], ghosts: bool,
          identity: Identity) -> tuple[list[Turn], str | None]:
    """The turns of a scenario, and why it could not run to its end, if it could not."""
    try:
        return sessions.run(clients, command, ghosts, identity), None
    except sessions.Unfinished as error:
        return error.trace, str(error)


def edges() -> Iterator[tuple[str, list[str]]]:
    """Scripts at the edges of what the contract allows; each ends with the end of input, between
    turns."""
    begin = ["turn 1", "open 0 1", "go", f"took {GREETING}"]
    quit_, help_ = b"QUIT\r\n".hex(), b"HELP\r\n".hex()
    yield "a clock just below its limit", [f"turn {LIMIT - 1}", "open 0 1", "go", f"took {GREETING}",
                                           f"turn {LIMIT - 1}", "go", "took"]
    yield "a clock of zero", ["turn 0", "open 0 1", "go", "took 0", "turn 0", "go", "took"]
    yield "a batch of sixteen events", ["turn 1", *[f"open {k} 1" for k in range(16)], "go",
                                        "took " + " ".join([str(GREETING)] * 16)]
    yield "a chunk of 512 bytes", [*begin, "turn 2", "recv 0 1 " + (b"HELP\r\n" * 85 + b"ST").hex(), "go", "took 10"]
    yield "the last index", ["turn 1", "open 63 7", "go", f"took {GREETING}", "turn 2", f"recv 63 7 {help_}", "go",
                             "took 5"]
    stale = ["writable 0 1", "end 0 1", "closed 0 1"]
    yield "events of a connection gone", [
        *begin, "turn 2", "closed 0 1", "go", "took", "turn 3", f"recv 0 1 {quit_}", *stale, "go", "took",
        "turn 4", "open 0 2", f"recv 0 1 {quit_}", *stale, "go", f"took {GREETING}",
        "turn 5", f"recv 0 2 {help_}", f"recv 0 1 {quit_}", *stale, "go", "took 3",
        "turn 6", "writable 0 1", "writable 0 2", "go", "took 0"]


def program_breaches() -> Iterator[tuple[str, Identity, list[str], int]]:
    """Hosts that break the contract in ways only the program is asked to see, and their codes."""
    first = ["turn 1", "go", "took"]
    yield "no identity", (b"", b""), first, 9
    yield "no revision", (b"", SOURCE), first, 9
    yield "no address of the source", (b"r", b""), first, 9
    yield "a revision one byte too long", (b"r" * 65, SOURCE), first, 9
    yield "an address one byte too long", (b"r", b"s" * 201), first, 9
    yield "a space in the revision", (b"0123 abc", SOURCE), first, 9
    yield "a DEL in the address", (b"r", b"https://x\x7f"), first, 9
    for kind in (0, 6, 2 ** 63):
        yield f"an event of kind {kind}", IDENTITY, ["turn 1", f"raw {kind} 0 1", "go", "took"], 8


PIECES = (b"HELP", b"help", b"QUIT", b"CAPABILITIES", b"HEAD", b"STAT", b"LIST", b" ", b"\t", b"\r", b"\n",
          b"\r\n", b"\r\n", b"\r\n", b"<a@b>", b"<>", b"123", b"2147483648", b"x", b"\0", b"a-b.c", b".")
QUIT = b"QUIT\r\n".hex()


class Wander:
    """A host drawn at random: it mostly keeps the contract, as far as it can tell what the session
    asked for, and now and then breaks it. The model and the compiled code are told the same and
    have to answer the same."""

    def __init__(self, rng: random.Random, binary: Path) -> None:
        self.rng = rng
        identity = rng.choice([IDENTITY, LONGEST, SHORTEST])
        self.pair = [Speaker(sessions.model_command(), identity), Speaker([str(binary)], identity)]
        self.gens = [0] * 64
        # each open connection: its generation, whether it asked for input, whether output is untaken
        self.live: dict[int, list[int]] = {}
        self.gone: list[tuple[int, int]] = []
        self.now = rng.choice([0, 1, 5, LIMIT - 10 ** 7])
        self.wake = 0

    def both(self, lines: list[str], ends: tuple[str, ...]) -> list[list[str]]:
        answers = []
        for session in self.pair:
            for line in lines:
                session.say(line)
            got = [session.hear()]
            while got[-1][0] not in ends:
                got.append(session.hear())
            answers.append(got)
        if answers[0] != answers[1]:
            raise LaneError(f"the compiled session answered {answers[1][-3:]}, the model {answers[0][-3:]}")
        return answers[0]

    def events(self) -> list[str]:
        rng, out, fed = self.rng, [], set()
        for _ in range(rng.choice([0, 1, 1, 2, 3, 16])):
            pick = rng.random()
            free = sorted(set(range(64)) - set(self.live))
            asked = [i for i, c in self.live.items() if c[1] and i not in fed]
            if pick < 0.25 and free:
                idx = free[0] if rng.random() < 0.8 else rng.choice(free)
                self.gens[idx] += 1
                self.live[idx] = [self.gens[idx], 0, 0]
                out.append(f"open {idx} {self.gens[idx]}")
            elif pick < 0.65 and asked:
                idx = rng.choice(asked)
                fed.add(idx)
                data = b"".join(rng.choice(PIECES) for _ in range(rng.randint(1, 8)))
                out.append(f"recv {idx} {self.live[idx][0]} {data.hex()}")
            elif pick < 0.8 and any(c[2] for c in self.live.values()):
                idx = rng.choice([i for i, c in self.live.items() if c[2]])
                self.live[idx][2] = 0
                out.append(f"writable {idx} {self.live[idx][0]}")
            elif pick < 0.85 and asked:
                idx = rng.choice(asked)
                fed.add(idx)
                self.live[idx][1] = 0
                out.append(f"end {idx} {self.live[idx][0]}")
            elif pick < 0.9 and self.live:
                idx = rng.choice(sorted(self.live))
                self.gone.append((idx, self.live.pop(idx)[0]))
                out.append(f"closed {idx} {self.gone[-1][1]}")
            elif self.gone:
                idx, gen = rng.choice(self.gone)
                out.append(rng.choice([f"recv {idx} {gen} {QUIT}", f"writable {idx} {gen}", f"end {idx} {gen}",
                                       f"closed {idx} {gen}"]))
        return out

    def breach(self) -> list[str]:
        choices = [[f"open {k} 9" for k in range(17)], [f"open 64 {self.gens[0] + 1}"], ["recv 0 1 " + "41" * 513]]
        choices += [[f"open {idx} {c[0] + 1}"] for idx, c in self.live.items()]
        choices += [[f"recv {idx} {c[0]} 41"] for idx, c in self.live.items() if not c[1]]
        return self.rng.choice(choices)

    def run(self, steps: int) -> tuple[int, int | None]:
        """How many turns the host ran, and the code the session stopped with, if it stopped."""
        rng = self.rng
        for step in range(steps):
            if rng.random() < 0.2 and self.wake:
                self.now = max(self.now, self.wake + rng.choice([-1, 0, 0, 1]))
            else:
                self.now += rng.choice([0, 1, 3, 1000, 9999, 10000, 180000, 1800000])
            now = self.now - 1 if rng.random() < 0.005 and self.now else self.now
            lines = self.events() + (self.breach() if rng.random() < 0.01 else [])
            answer = self.both([f"turn {now}", *lines, "go"], ("done", "stop"))
            if answer[-1][0] == "stop":
                return step + 1, int(answer[-1][1])
            took = self.settle(answer[:-1])
            if rng.random() < 0.005:
                took.append(1)
            end = self.both(["took " + " ".join(map(str, took))], ("deadline", "stop"))[-1]
            if end[0] == "stop":
                return step + 1, int(end[1])
            self.wake = int(end[1])
        return steps, None

    def settle(self, actions: list[list[str]]) -> list[int]:
        """What the kernel takes of each send, and what the host learns of each connection."""
        took = []
        for words in actions:
            idx = int(words[1])
            if words[0] != "send":
                self.gone.append((idx, self.live.pop(idx)[0]))
                continue
            size = 0 if words[3] == "-" else len(words[3]) // 2
            k = self.rng.choice([size, size, size, 0, self.rng.randint(0, size)])
            k += self.rng.random() < 0.005
            took.append(k)
            self.live[idx][1:] = [int(words[4] == "1" and k >= size), int(k < size)]
        return took

    def close(self) -> None:
        for session in self.pair:
            session.__exit__()


def wander(binary: Path, runs: int) -> dict[str, int]:
    """Runs of hosts drawn at random, the same for every program: how many turns, and how each
    ended."""
    rng = random.Random(SEED)  # noqa: S311 -- a fixed seed, so that every run draws the same hosts
    seen: Counter[str] = Counter()
    for run in range(runs):
        host = Wander(rng, binary)
        try:
            steps, code = host.run(STEPS)
        except LaneError as error:
            raise LaneError(f"random host {run} of seed {SEED}: {error}") from None
        finally:
            host.close()
        seen["runs"] += 1
        seen["turns"] += steps
        seen["unstopped" if code is None else f"stop {code}"] += 1
    return dict(seen)


def scenarios_hold(binary: Path, scenarios: list[sessions.Scenario], expected: dict[str, list[Turn]]) -> None:
    for name, clients, ghosts, identity in scenarios:
        native, broken = trace(clients, [str(binary)], ghosts, identity)
        problem = first_difference(expected[name], native, broken)
        if problem:
            raise LaneError(f"scenario {name!r}: {problem}")


def scripts_hold(binary: Path, answers: dict[str, list[str]]) -> None:
    for name, script, code in sessions.breaches():
        out, ended = sessions.breach_output(script, [str(binary)])
        if ended or out != answers[name]:
            raise LaneError(f"breach {name!r}: the compiled session answered {out[-3:]}{ended}, "
                            f"not stop {code} as the model")
    for name, identity, script, code in program_breaches():
        try:
            sessions.check_breach(script, code, [str(binary)], identity)
        except LaneError as error:
            raise LaneError(f"breach {name!r}: {error}") from None
    for name, script in edges():
        out, ended = sessions.breach_output(script, [str(binary)])
        if ended or out != answers[name]:
            raise LaneError(f"at the edge {name!r}: the compiled session answered {out[-4:]}{ended}, "
                            f"the model {answers[name][-4:]}")


def edge_answers(model: list[str]) -> dict[str, list[str]]:
    """The model's answers to the scripts at the edges, each of which it has to take to its end."""
    answers = {}
    for name, script in edges():
        out, ended = sessions.breach_output(script, model)
        if ended:
            raise LaneError(f"at the edge {name!r}: the model answered {out[-3:]}{ended}")
        answers[name] = out
    return answers


def check(cake: str) -> Report:
    OUT.mkdir(parents=True, exist_ok=True)
    (OUT / "dn_session_layout.h").write_text(lanes.emit("emit-session-layout"))
    source = lanes.emit("emit-session")
    binary = build(cake, "session", source)
    scenarios = list(sessions.scenarios())
    model = sessions.model_command()
    expected = {name: sessions.run(clients, model, ghosts, identity) for name, clients, ghosts, identity in scenarios}
    turns = sum(len(t) for t in expected.values())
    answers = {name: sessions.check_breach(script, code, model) for name, script, code in sessions.breaches()}
    answers |= edge_answers(model)
    scenarios_hold(binary, scenarios, expected)
    scripts_hold(binary, answers)
    random_hosts = wander(binary, RUNS)
    caught = {}
    for index, (name, pattern, becomes, times, sign) in enumerate(DEFECTS):
        planted = build(cake, f"defect-{index}", plant(source, pattern, becomes, times))
        try:
            scenarios_hold(planted, scenarios, expected)
            scripts_hold(planted, answers)
            wander(planted, RUNS)
        except LaneError as error:
            if sign not in str(error):
                raise LaneError(f"the program with {name} was caught, but not as {sign!r}: {error}") from None
            caught[name] = str(error)[:400]
            continue
        raise LaneError(f"the program with {name} answered every host as the model")
    lanes.require_quoted({"docs/baseline.md": [f"on the model's {len(scenarios)} scenarios and {turns:,} turns",
                                               f"{RUNS} hosts drawn at random"]})
    return Report("checked", cake, HOSTS, {
        "source_sha256": lanes.digest(OUT / "session.pnk"), "executable_sha256": lanes.digest(binary),
        "layout_sha256": lanes.digest(OUT / "dn_session_layout.h"), "scenarios": len(scenarios), "turns": turns,
        "breaches": sum(1 for _ in sessions.breaches()), "program_breaches": sum(1 for _ in program_breaches()),
        "edges": sum(1 for _ in edges()), "random_hosts": random_hosts, "random_seed": SEED,
        "planted_defects_caught": caught})


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--cake", default=os.environ.get("CAKE"))
    args = parser.parse_args()
    lanes.require_platform(parser)
    cake = lanes.given_cake(parser, args.cake)
    lanes.lane_main("SESSION", OUT, lambda: check(cake))


if __name__ == "__main__":
    main()
