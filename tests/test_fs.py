# SPDX-License-Identifier: AGPL-3.0-or-later
"""The file system lane's own tools, on inputs made to test them: the reference gives the table's
answers, the runs it draws are ones the reference takes and mostly reach files, the images it changes
differ, and what it tries is what Lean has."""
from __future__ import annotations

import io
import random
import re
import unittest
from unittest import mock

from gatekit import ROOT, script

F = script("fs_check")
R = script("fs_ref")


def answered(line: str) -> str:
    return str(R.answer(line))


class Reference(unittest.TestCase):
    """The reference against the answers 0005 gives."""

    def test_the_reference_gives_the_tables_answers(self) -> None:
        for case in F.table():
            with self.subTest(line=case.line):
                self.assertEqual(answered(case.line), case.want)

    def test_the_reference_admits_what_it_lists(self) -> None:
        for ops in ("create:61;sync-dir;append:0:0102;rename:61:62", "create:61;append:0:01;sync:0!0;sync:0"):
            for image in answered(f"leavings {ops}").split(" "):
                with self.subTest(ops=ops, image=image):
                    self.assertEqual(answered(f"crash {ops} {image}"), "yes")

    def test_the_reference_refuses_what_no_case_may_be(self) -> None:
        for line in F.REFUSED:
            with self.subTest(line=line), mock.patch("sys.stdin", io.TextIOWrapper(io.BytesIO(line.encode()))):
                with self.assertRaises(SystemExit) as raised:
                    R.main()
                self.assertNotEqual(raised.exception.code, 0)


class Drawn(unittest.TestCase):
    """The runs and images the lane makes."""

    def test_drawn_runs_fail_only_in_ways_operations_may(self) -> None:
        rng = random.Random(1)  # noqa: S311 -- a fixed seed, so that every run draws the same cases
        runs = [F.random_ops(rng) for _ in range(500)]
        for ops in runs:
            answered(f"run {ops}")
        steps = [s for ops in runs if ops != "-" for s in ops.split(";")]
        self.assertTrue(any("!" in s for s in steps))
        kinds = {s.split("!")[0].split(":")[0] for s in steps}
        self.assertEqual(kinds, {"create", "open", "append", "truncate", "sync", "read", "size", "rename",
                                 "remove", "sync-dir", "list"})

    def test_most_operations_on_a_file_reach_one(self) -> None:
        rng = random.Random(1)  # noqa: S311 -- a fixed seed, so that every run draws the same cases
        said = []
        for _ in range(500):
            ops = F.random_ops(rng)
            if ops == "-":
                continue
            answers, _ = R.run(ops)
            said += [a for s, a in zip(ops.split(";"), answers, strict=True)
                     if "!" not in s and s.split(":")[0] in ("append", "truncate", "sync", "read", "size")]
        self.assertGreater(len(said), 500)
        self.assertLess(said.count("missing"), len(said) // 4)

    def test_a_life_follows_one_file(self) -> None:
        rng = random.Random(1)  # noqa: S311 -- a fixed seed, so that every run draws the same cases
        for _ in range(300):
            ops = F.random_life(rng)
            answers, _ = R.run(ops)
            self.assertTrue(ops.startswith("create:"))
            self.assertEqual(answers[0], "file:0")
            on_file = [a for s, a in zip(ops.split(";"), answers, strict=True)
                       if s.split(":")[0] in ("append", "sync", "truncate", "size")]
            self.assertNotIn("missing", on_file)

    def test_every_change_of_an_image_changes_it(self) -> None:
        rng = random.Random(1)  # noqa: S311 -- a fixed seed, so that every run draws the same cases
        for image in ("-", "61=-", "61=01", "61=0102;62=-", "61=01;62=01", "61=ff;62=01;63=0a0b"):
            for other in F.changed(rng, image):
                with self.subTest(image=image, other=other):
                    self.assertNotEqual(F.parsed(other), F.parsed(image))
                    self.assertEqual(F.shown(F.parsed(other)), other)

    def test_the_table_answers_both_ways(self) -> None:
        wants = {c.want for c in F.table() if c.line.startswith("crash ")}
        self.assertEqual(wants, {"yes", "no"})


class Names(unittest.TestCase):
    """The lane tries what the model has."""

    def test_the_lane_tries_every_version_of_the_model(self) -> None:
        text = (ROOT / "lean/DN/News/FsMutant.lean").read_text()
        block = text[text.index("def names :"):]
        names = re.findall(r'\("([a-z-]+)",', block[:block.index("\n\n")])
        self.assertEqual(names, F.MUTANTS)


if __name__ == "__main__":
    unittest.main()
