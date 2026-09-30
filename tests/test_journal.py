# SPDX-License-Identifier: AGPL-3.0-or-later
"""The journal lane's own tools, on inputs made to test them: RFC 7143's examples are read as its
text prints them, the frames and cases the lane makes are the ones it says, and what it tries and
knows is what Lean has."""
from __future__ import annotations

import ast
from pathlib import Path
import random
import re
import struct
import tempfile
import unittest
from unittest import mock

from gatekit import ROOT, script

K = script("journal_check")


def evaluated(expression: str) -> int:
    """The value of sums and products of numbers, as a Lean definition writes them."""
    def value(node: ast.expr) -> int:
        match node:
            case ast.Constant(value=int() as v):
                return v
            case ast.BinOp(left, ast.Add(), right):
                return value(left) + value(right)
            case ast.BinOp(left, ast.Mult(), right):
                return value(left) * value(right)
        raise ValueError(ast.dump(node))
    return value(ast.parse(expression, mode="eval").body)


class Rfc(unittest.TestCase):
    """RFC 7143's examples of the CRC-32C, read from its text."""

    def test_the_examples_are_read_as_the_rfc_prints_them(self) -> None:
        found = K.vectors()
        data = [d for _, d, _ in found]
        self.assertEqual(data[:4], [bytes(32), b"\xff" * 32, bytes(range(32)), bytes(reversed(range(32)))])
        self.assertEqual((len(data[4]), data[4][:2], data[4][40]), (48, b"\x01\xc0", 2))
        self.assertEqual([crc for _, _, crc in found], [0x8A9136AA, 0x62A8AB43, 0x46DD794E, 0x113FDB5C, 0xD9963A56])

    def test_the_lean_examples_pin_the_same_values(self) -> None:
        text = (ROOT / "lean/DN/News/JournalModel.lean").read_text()
        for _, _, crc in K.vectors():
            self.assertIn(f"0x{crc:08X}", text)
        self.assertIn(f"0x{K.CHECK:08X}", text)

    def test_the_lanes_own_crc_gives_them(self) -> None:
        for _, data, crc in K.vectors():
            self.assertEqual(K.crc32c(data), crc)
        self.assertEqual(K.crc32c(b"123456789"), K.CHECK)
        # Nine zeros are a frame whose CRC-32C does not check.
        self.assertNotEqual(K.crc32c(b"\0"), 0)

    def test_a_gap_is_filled_only_by_a_steady_step(self) -> None:
        self.assertEqual(K.filled([(0, bytes([0, 2, 4, 6])), None, (12, bytes([24, 26, 28, 30]))]),
                         bytes(range(0, 32, 2)))
        for rows in ([(0, bytes([0, 2, 4, 6])), None, (12, bytes([24, 26, 28, 31]))],
                     [(0, bytes([0, 2, 4, 6])), None, (12, bytes([23, 25, 27, 29]))],
                     [None, (4, bytes(4))], [(4, bytes(4))]):
            with self.subTest(rows=rows), self.assertRaises(K.LaneError):
                K.filled(rows)

    def test_a_text_with_an_example_missing_is_refused(self) -> None:
        text = K.RFC.read_text(encoding="ascii")
        with tempfile.TemporaryDirectory() as temp:
            changed = Path(temp) / "rfc7143.txt"
            changed.write_text(text.replace("CRC:       aa 36 91 8a", "", 1))
            with mock.patch.object(K, "RFC", changed), self.assertRaises(K.LaneError) as refused:
                K.vectors()
        self.assertIn("4 examples", str(refused.exception))


class Frames(unittest.TestCase):
    """The frames and commits the lane makes."""

    def test_the_bounds_and_the_end_mark_are_leans(self) -> None:
        text = (ROOT / "lean/DN/News/Journal.lean").read_text()
        found = re.search(r"def maxPayload : Nat := (.+)", text)
        mark = re.search(r"def endMark : Byte := BitVec.ofNat 8 0x([0-9A-F]+)", text)
        assert found is not None and mark is not None
        self.assertEqual(evaluated(found[1]), K.MAX_PAYLOAD)
        self.assertEqual(int(mark[1], 16), K.END)
        self.assertEqual(len(K.encoded(K.LARGEST)), K.MAX_FRAME)
        self.assertEqual(len(K.FORMAT_FRAME), K.FIRST_FRAME)
        self.assertGreater(len(K.AFTER), K.MAX_FRAME)

    def test_a_frame_says_its_length_crc_and_type_and_ends_in_its_mark(self) -> None:
        self.assertEqual(struct.unpack_from("<IIB", K.frame(2, b"abc")), (3, K.crc32c(b"\x02abc"), 2))
        self.assertEqual(K.frame(2, b"abc")[-1], K.END)
        self.assertEqual(K.frame(2, b"abc", end=0)[-1], 0)
        self.assertEqual(struct.unpack_from("<I", K.frame(2, b"abc", length=7))[0], 7)

    def test_frames_start_where_the_lane_says(self) -> None:
        data = K.journal([K.SAMPLE, K.SMALLEST])
        first = len(K.FORMAT_FRAME)
        self.assertEqual(K.frame_starts(data), [0, first, first + len(K.encoded(K.SAMPLE))])

    def test_the_bounded_commits_are_on_both_sides_of_each_bound(self) -> None:
        cases = K.bounded(K.SAMPLE)
        ids = {len(c[1]): ok for c, ok in cases if c[2] == K.SAMPLE[2] and c[0] == K.SAMPLE[0]}
        self.assertEqual({n: ids.get(n) for n in (0, 1, 250, 251)}, {0: False, 1: True, 250: True, 251: False})
        counts = {len(c[2]): ok for c, ok in cases if all(g[0].startswith(b"g") for g in c[2]) and c[2]}
        self.assertEqual(counts[16], True)
        self.assertEqual(counts[17], False)
        self.assertEqual([ok for c, ok in cases if c[0] >= 2**64 - 1], [True, False])
        numbers = {c[2][0][1]: ok for c, ok in cases if c[2][:1] and c[2][0][0] == b"g"}
        self.assertEqual(numbers, {0: False, 1: True, 2**31 - 1: True, 2**31: False, 2**32 - 1: False,
                                   2**32: False})
        self.assertEqual([ok for c, ok in cases if c[0] in (0, 2**64)], [False, False])
        self.assertIn(((1, K.SAMPLE[1], ((b"g", 1), (b"g", 2)), 100, 200, 12345), False), cases)
        self.assertIn(((1, K.SAMPLE[1], K.SAMPLE[2], 201, 200, 12345), False), cases)
        self.assertEqual(sum(ok for _, ok in cases), 17)
        self.assertEqual(sum(not ok for _, ok in cases), 19)


class Cases(unittest.TestCase):
    """What the lane expects of a journal."""

    def test_reading_stops_in_a_torn_tail_only_within_the_frame_that_can_have_been_cut(self) -> None:
        self.assertEqual(K.stopped(bytes(10 + K.MAX_FRAME), [], 10, "checksum").want, "F end torn 10")
        past = K.stopped(bytes(11 + K.MAX_FRAME), [], 10, "checksum")
        self.assertEqual((past.want, past.prefix), ("F end corrupt 10 checksum", False))
        self.assertEqual(K.stopped(bytes(K.FIRST_FRAME), None, 0, "short").want, "end torn 0")
        self.assertEqual(K.stopped(bytes(K.FIRST_FRAME + 1), None, 0, "unterminated").want,
                         "end corrupt 0 unterminated")
        self.assertEqual(K.stopped(bytes(10), [], 0, "not-a-record").want, "F end corrupt 0 not-a-record")
        unknown = K.stopped(bytes(K.FIRST_FRAME + 11), None, 10, None)
        self.assertTrue(unknown.holds("end corrupt 10 too-long"))
        self.assertFalse(unknown.holds("end corrupt 100 too-long"))
        self.assertFalse(unknown.holds("end torn 10"))

    def test_an_answer_ends_as_it_says(self) -> None:
        self.assertEqual(K.ending("F C:1:61:1:2:3:62=1 end torn 29"), "torn")
        self.assertEqual(K.ending("end clean"), "clean")
        self.assertEqual(K.ending("F end corrupt 29 format-again"), "format-again")

    def test_every_frame_cut_short_is_expected_torn(self) -> None:
        rng = random.Random(1)  # noqa: S311 -- a fixed seed, so that every run draws the same cases
        cases = K.torn_cases(rng, [K.SAMPLE, K.SMALLEST, K.LARGEST])
        self.assertTrue(all(c.want is not None and " end torn " in f" {c.want}" for c in cases))

    def test_a_changed_length_rests_on_the_crc_only_where_an_end_mark_is(self) -> None:
        data = K.journal([K.SAMPLE])
        start = len(K.FORMAT_FRAME)
        self.assertTrue(K.by_construction(data, start, start + 4))
        longer = bytearray(data)
        longer[start] += 1
        self.assertTrue(K.by_construction(bytes(longer), start, start))
        body = len(K.payload(K.SAMPLE))
        shorter = bytearray(data)
        shorter[start] = body - 1
        shorter[start + 9 + body - 1] = K.END
        self.assertFalse(K.by_construction(bytes(shorter), start, start))

    def test_a_forged_fill_changes_four_octets_to_the_crc_wanted(self) -> None:
        data = bytes(range(40))
        for target in (0, 1, 0xDEADBEEF, 0xFFFFFFFF):
            with self.subTest(target=target):
                made = K.forged(data, 30, target)
                self.assertEqual(K.crc32c(made), target)
                self.assertEqual(made[:30] + made[34:], data[:30] + data[34:])
        whole = K.encoded(K.SAMPLE)
        made = K.cut_and_forged(whole, 8, bytes(len(whole) - 9))
        self.assertEqual((len(made), made[:8], made[-1]), (len(whole), whole[:8], K.END))
        self.assertEqual(K.crc32c(made[8:-1]), struct.unpack_from("<I", whole, 4)[0])
        for n, fill in ((7, bytes(len(whole) - 8)), (8, bytes(3))):
            with self.subTest(n=n), self.assertRaises(K.LaneError):
                K.cut_and_forged(whole, n, fill)

    def test_every_way_of_damage_changes_the_journal(self) -> None:
        rng = random.Random(1)  # noqa: S311 -- a fixed seed, so that every run draws the same cases
        data = K.journal([K.SAMPLE])
        for way in range(8):
            with self.subTest(way=way):
                self.assertNotEqual(K.damaged(rng, data, way), data)


class Names(unittest.TestCase):
    """The lane names what the specification has, so that none of it goes untried."""

    @staticmethod
    def block(path: str, start: str) -> str:
        text = (ROOT / path).read_text()
        found = text[text.index(start):]
        return found[:found.index("\n\n")]

    def test_the_lane_tries_every_version_of_the_rules(self) -> None:
        names = re.findall(r'\("([a-z-]+)",', self.block("lean/DN/News/Journal.lean", "def names :"))
        self.assertEqual(names, K.MUTANTS)

    def test_the_lane_knows_every_reason(self) -> None:
        reasons = re.findall(r'=> "([a-z-]+)"', self.block("lean/DN/News/JournalModel.lean", "def whyText"))
        self.assertEqual(reasons, K.REASONS)


if __name__ == "__main__":
    unittest.main()
