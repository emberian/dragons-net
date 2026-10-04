# SPDX-License-Identifier: AGPL-3.0-or-later
"""The runs lane's own tools, on inputs made to test them: its reading of the program allows the
phases in 0005's order and keeps what each event does, its judgement refuses each way of losing what
0005 promises, each way of breaking the program changes the scenario, and its probes are of events
the program may not make."""
from __future__ import annotations

import copy
from dataclasses import replace
import random
from typing import Any
import unittest

from gatekit import script

RC = script("runs_check")
J = script("store_ref")
R = script("recovery_ref")

GROUPS = RC.GROUPS
TEST, MORE = GROUPS


def article(rng: random.Random) -> tuple[Any, Any, list[Any]]:
    """A program just started, what the runs did, and the events that carry one article to 240."""
    p, h = RC.Prog(1, 1, {}), RC.History()
    octets = rng.randbytes(5)
    c = (1, b"<1@x>", [(TEST, 1)], 0, 5, J.crc32c(octets))
    events = [RC.Event("reserve", octets=octets), RC.Event("create", 1), RC.Event("write", 1, m=5),
              RC.Event("sync", 1), RC.Event("rename", 1), RC.Event("place", 1), RC.Event("commit", 1, commit=c),
              RC.Event("publish")]
    return p, h, events


class Program(unittest.TestCase):
    """The lane's reading of 0005's program."""

    def test_an_article_goes_through_the_phases_in_order(self) -> None:
        p, h, events = article(random.Random(1))  # noqa: S311 -- a fixed seed
        for k, e in enumerate(events):
            with self.subTest(event=e.text()):
                later = [f for f in events[k + 1:] if f.kind != "publish"]
                self.assertTrue(RC.allowed(p, GROUPS, e))
                self.assertFalse(any(RC.allowed(p, GROUPS, f) for f in later if f.kind != "reserve"))
                RC.happen(p, h, e)
        self.assertEqual([c[0] for c in h.answered], [1])
        self.assertEqual(p.highest, {TEST: 1})
        self.assertEqual(p.next, 2)

    def test_a_commit_is_allowed_only_as_0005_says(self) -> None:
        p, h, events = article(random.Random(1))  # noqa: S311 -- a fixed seed
        for e in events[:6]:
            RC.happen(p, h, e)
        c = events[6].commit
        for bad in ((2, *c[1:]), (*c[:4], 6, c[5]), (*c[:5], c[5] ^ 1), (*c[:2], [(b"local.other", 1)], *c[3:]),
                    (*c[:2], [], *c[3:])):
            with self.subTest(commit=bad):
                self.assertFalse(RC.allowed(p, GROUPS, RC.Event("commit", 1, commit=bad)))
        p.highest[TEST] = 1
        self.assertFalse(RC.allowed(p, GROUPS, events[6]))

    def test_failures_do_what_0005_says(self) -> None:
        for kind, accepting, trusting in (("create", True, True), ("write", True, True), ("sync", False, True),
                                           ("rename", True, True), ("place", False, False)):
            p, h, events = article(random.Random(1))  # noqa: S311 -- a fixed seed
            stop = {"create": 1, "write": 2, "sync": 3, "rename": 4, "place": 5}[kind]
            for e in events[:stop]:
                RC.happen(p, h, e)
            RC.happen(p, h, RC.Event(kind, 1, fails=0))
            with self.subTest(kind=kind):
                self.assertEqual(p.posts[1].stage, "refused")
                self.assertEqual(h.refused, {(1, 1)})
                self.assertEqual((p.accepting, p.trusting), (accepting, trusting))
        p, h, events = article(random.Random(1))  # noqa: S311 -- a fixed seed
        for e in events[:6]:
            RC.happen(p, h, e)
        RC.happen(p, h, RC.Event("commit", 1, commit=events[6].commit, fails=3))
        self.assertEqual(h.appended, [(1, events[6].commit)])
        self.assertFalse(p.accepting)
        self.assertEqual(h.answered, [])
        RC.happen(p, h, RC.Event("publish", fails=0))
        self.assertEqual((p.accepting, p.trusting, h.answered), (False, False, []))
        self.assertIsNotNone(p.committing)
        before = (copy.deepcopy(p), copy.deepcopy(h))
        RC.happen(p, h, RC.Event("clean", 1, final=1, fails=1))
        self.assertEqual((p, h), before)

    def test_events_read_as_the_model_takes_them(self) -> None:
        c = (3, b"<a>", [(TEST, 2), (MORE, 1)], 1, 4, 99)
        self.assertEqual(RC.Event("commit", 3, commit=c, fails=2).text(),
                         f"commit:3:3:{b'<a>'.hex()}:{TEST.hex()}=2,{MORE.hex()}=1:1:4:99!2")
        self.assertEqual(RC.Event("write", 2, m=7).text(), "write:2:7")
        self.assertEqual(RC.Event("clean", 2, final=1).text(), "clean:2:1")
        self.assertEqual(RC.Event("reserve", octets=b"").text(), "reserve:-")
        self.assertEqual(RC.Event("restart").text(), "restart")
        self.assertEqual(RC.Event("restart", start=(3, 1)).text(), "restart:3:1")

    def test_drawn_events_are_allowed_where_they_are_drawn(self) -> None:
        rng = random.Random(1)  # noqa: S311 -- a fixed seed, so that every run draws the same cases
        commits = 0
        for _ in range(40):
            p, h = RC.Prog(1, 1, {}), RC.History()
            events = RC.draw_events(rng, p, h, GROUPS, 30)
            q, g = RC.Prog(1, 1, {}), RC.History()
            for e in events:
                self.assertTrue(RC.allowed(q, GROUPS, replace(e, fails=None)))
                RC.happen(q, g, e)
            commits += sum(e.kind == "commit" for e in events)
        self.assertGreater(commits, 20)

    def test_each_probe_ends_in_an_event_of_its_kind_the_program_may_not_make(self) -> None:
        rng = random.Random(1)  # noqa: S311 -- a fixed seed, so that every run draws the same cases
        seen = set()
        for _ in range(60):
            events = RC.draw_events(rng, RC.Prog(1, 1, {}), RC.History(), GROUPS, 30)
            for kind, probe in RC.probes(rng, {}, 1, RC.History(), GROUPS, events):
                q, g = RC.start_state({}, 1, GROUPS), RC.History()
                for e in probe.events[:-1]:
                    RC.happen(q, g, e)
                self.assertFalse(RC.allowed(q, GROUPS, probe.events[-1]), kind)
                seen.add(kind)
        self.assertGreaterEqual(len(seen), len(RC.PROBES) - 4)


class Judgement(unittest.TestCase):
    """What the lane holds a directory a crash left to."""

    def stored(self, octets: bytes, c: tuple[object, ...]) -> dict[bytes, bytes]:
        fmt = J.frame(RC.KEY, 0, J.FORMAT, J.MAGIC + RC.KEY)
        journal = fmt + J.frame(RC.KEY, len(fmt), J.COMMIT, J.payload(c))
        return {b"journal": journal, R.name_of("a", 1): octets}

    def test_a_directory_keeping_what_was_promised_passes(self) -> None:
        octets = b"hello"
        c = (1, b"<1@x>", [(TEST, 1)], 0, 5, J.crc32c(octets))
        h = RC.History([c], [(1, c)], set(), {1: octets})
        self.assertIsNone(RC.violation(self.stored(octets, c), GROUPS, h))

    def test_each_way_of_losing_it_is_told(self) -> None:
        octets = b"hello"
        c = (1, b"<1@x>", [(TEST, 1)], 0, 5, J.crc32c(octets))
        h = RC.History([c], [(1, c)], set(), {1: octets})
        self.assertIn("is not found", RC.violation({}, GROUPS, h))
        unappended = RC.History([], [], set(), {1: octets})
        refused = RC.History([], [(1, c)], {(1, 1)}, {1: octets})
        self.assertIn("not appended", RC.violation(self.stored(octets, c), GROUPS, unappended))
        self.assertIn("not appended", RC.violation(self.stored(octets, c), GROUPS, refused))
        self.assertIn("is not its octets", RC.violation(self.stored(b"hellO", c), GROUPS, h))
        bad = (1, b"<1@x>", [(TEST, 1)], 0, 5, J.crc32c(octets) ^ 1)
        wrong = RC.History([bad], [(1, bad)], set(), {1: octets})
        self.assertIn("CRC-32C", RC.violation(self.stored(octets, bad), GROUPS, wrong))
        self.assertIn("corrupt", RC.violation({b"x": b""}, GROUPS, RC.History()))


class Holding(unittest.TestCase):
    """How the lane holds what the model ran: done again on fs_ref, at every point."""

    def start(self) -> tuple[str, bytes]:
        fmt = J.frame(RC.KEY, 0, J.FORMAT, J.MAGIC + RC.KEY)
        rec = J.frame(RC.KEY, len(fmt), J.START, b"")
        ops = f"sync-dir;create:{b'journal'.hex()};append:0:{fmt.hex()};sync:0;sync-dir;append:0:{rec.hex()};sync:0"
        return ops, fmt + rec

    def test_a_start_on_nothing_holds_at_each_point(self) -> None:
        ops, journal = self.start()
        seg = RC.Segment({}, 1, [])
        found = RC.hold(random.Random(1), seg, f"ok {ops} {b'journal'.hex()}={journal.hex()}", GROUPS,  # noqa: S311
                        RC.History())
        self.assertEqual(found.points, 8)
        self.assertEqual(found.violations, [])

    def test_operations_that_end_elsewhere_are_refused(self) -> None:
        ops, journal = self.start()
        fmt = J.frame(RC.KEY, 0, J.FORMAT, J.MAGIC + RC.KEY)
        no_record = f"sync-dir;create:{b'journal'.hex()};append:0:{fmt.hex()};sync:0;sync-dir"
        seg = RC.Segment({}, 1, [])
        for answer in (f"ok {ops} {b'journal'.hex()}={journal[:-1].hex()}", f"ok {ops}|- -", "not-allowed 1",
                       f"ok {no_record} {b'journal'.hex()}={fmt.hex()}"):
            with self.subTest(answer=answer[-40:]), self.assertRaises(RC.LaneError):
                RC.hold(random.Random(1), seg, answer, GROUPS, RC.History())  # noqa: S311 -- a fixed seed

    def test_every_directory_drawn_is_one_a_crash_may_leave(self) -> None:
        rng = random.Random(1)  # noqa: S311 -- a fixed seed, so that every run draws the same cases
        F = script("fs_ref")
        for _ in range(200):
            disk = F.Disk()
            for step in script("fs_check").random_ops(rng).split(";"):
                if step == "-":
                    continue
                op, failed = F.op_of(step)
                if failed is None:
                    F.do(disk, op)
                else:
                    F.fail(disk, op, failed)
            for _ in range(5):
                self.assertTrue(F.may_leave(disk, F.leaving(disk, rng)))


class Breaking(unittest.TestCase):
    """Each way of breaking the program."""

    def test_each_way_changes_a_scenario_it_applies_to(self) -> None:
        rng = random.Random(3)  # noqa: S311 -- a fixed seed, so that every run draws the same cases
        applied = {name: 0 for name in RC.BREAKS}
        for _ in range(200):
            events = RC.draw_events(rng, RC.Prog(1, 1, {}), RC.History(), GROUPS, 40)
            for name, breaking in RC.BREAKS.items():
                broken = breaking(events)
                if broken is not None:
                    applied[name] += 1
                    self.assertNotEqual(broken, events, name)
        self.assertEqual([name for name, n in applied.items() if not n], [])


if __name__ == "__main__":
    unittest.main()
