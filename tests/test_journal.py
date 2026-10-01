# SPDX-License-Identifier: AGPL-3.0-or-later
"""The journal lane's own tools, on inputs made to test them: the authors' SipHash vectors and RFC
7143's examples are read as their files print them, the frames and cases the lane makes are the
ones it says, and what it tries and knows is what Lean has."""
from __future__ import annotations

import ast
import itertools
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


class Vectors(unittest.TestCase):
    """The authors' SipHash vectors and RFC 7143's examples, read from their files."""

    def test_the_lanes_siphash_gives_the_authors_tags(self) -> None:
        tags = K.sip_vectors()
        self.assertEqual(len(tags), 64)
        self.assertEqual(tags[0], 0x726FDB47DD0E0E31)
        for i, tag in enumerate(tags):
            with self.subTest(length=i):
                self.assertEqual(K.siphash(K.KEY, bytes(range(i))), tag)

    def test_a_vectors_file_short_of_tags_is_refused(self) -> None:
        text = K.SIP_VECTORS.read_text(encoding="ascii")
        with tempfile.TemporaryDirectory() as temp:
            changed = Path(temp) / "vectors.h"
            changed.write_text(text.replace("0x31,", "", 1))
            with mock.patch.object(K, "SIP_VECTORS", changed), self.assertRaises(K.LaneError):
                K.sip_vectors()

    def test_the_lean_examples_pin_the_same_values(self) -> None:
        text = (ROOT / "lean/DN/News/JournalModel.lean").read_text()
        tags = K.sip_vectors()
        for tag in (tags[0], tags[15]):
            self.assertIn(f"0x{tag:016X}", text)
        for _, _, crc in K.vectors():
            self.assertIn(f"0x{crc:08X}", text)
        self.assertIn(f"0x{K.CHECK:08X}", text)

    def test_the_examples_are_read_as_the_rfc_prints_them(self) -> None:
        found = K.vectors()
        data = [d for _, d, _ in found]
        self.assertEqual(data[:4], [bytes(32), b"\xff" * 32, bytes(range(32)), bytes(reversed(range(32)))])
        self.assertEqual((len(data[4]), data[4][:2], data[4][40]), (48, b"\x01\xc0", 2))
        self.assertEqual([crc for _, _, crc in found], [0x8A9136AA, 0x62A8AB43, 0x46DD794E, 0x113FDB5C, 0xD9963A56])

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

    def test_the_vectors_are_the_recorded_ones(self) -> None:
        K.corpus_digests()
        with tempfile.TemporaryDirectory() as temp:
            copy = Path(temp) / "vectors.h"
            copy.write_bytes(K.SIP_VECTORS.read_bytes() + b"\n")
            (Path(temp) / "LICENSE_CC0").write_bytes((K.SIP_VECTORS.parent / "LICENSE_CC0").read_bytes())
            with mock.patch.object(K, "SIP_VECTORS", copy), self.assertRaises(K.LaneError):
                K.corpus_digests()


class Frames(unittest.TestCase):
    """The frames and commits the lane makes."""

    def test_the_bounds_and_the_end_mark_are_leans(self) -> None:
        text = (ROOT / "lean/DN/News/Journal.lean").read_text()
        found = re.search(r"def maxPayload : Nat := (.+)", text)
        mark = re.search(r"def endMark : Byte := BitVec.ofNat 8 0x([0-9A-F]+)", text)
        header = re.search(r"def headerLength : Nat := (\d+)", text)
        assert found is not None and mark is not None and header is not None
        self.assertEqual(evaluated(found[1]), K.MAX_PAYLOAD)
        self.assertEqual(int(mark[1], 16), K.END)
        self.assertEqual(int(header[1]), K.HEADER)
        self.assertEqual(len(K.encoded(K.KEY, 0, K.LARGEST)), K.MAX_FRAME)
        self.assertEqual(len(K.format_frame(K.KEY)), K.FIRST_FRAME)
        self.assertEqual(len(K.encoded(K.KEY, 0, K.START_RECORD)), K.START_FRAME)
        types = {name: int(v) for name, v in re.findall(r"def (\w+)Type : Nat := (\d+)", text)}
        self.assertEqual(types, {"format": K.FORMAT, "commit": K.COMMIT, "start": K.START})

    def test_a_frame_says_its_length_tag_and_type_and_ends_in_its_mark(self) -> None:
        made = K.frame(K.KEY, 5, 2, b"abc")
        tag = K.siphash(K.KEY, struct.pack("<QB", 5, 2) + b"abc")
        self.assertEqual(struct.unpack_from("<IQB", made), (3, tag, 2))
        self.assertEqual(made[-1], K.END)
        self.assertEqual(K.frame(K.KEY, 5, 2, b"abc", end=0)[-1], 0)
        self.assertEqual(struct.unpack_from("<I", K.frame(K.KEY, 5, 2, b"abc", length=7))[0], 7)
        self.assertNotEqual(K.frame(K.KEY, 6, 2, b"abc")[4:12], made[4:12])

    def test_frames_start_where_the_lane_says(self) -> None:
        data = K.journal(K.KEY, [K.SAMPLE, K.START_RECORD, K.SMALLEST])
        first = len(K.format_frame(K.KEY))
        second = first + len(K.encoded(K.KEY, first, K.SAMPLE))
        self.assertEqual(K.frame_starts(data), [0, first, second, second + K.START_FRAME])

    def test_a_start_is_a_frame_of_no_payload_and_shows_as_one(self) -> None:
        made = K.encoded(K.KEY, 7, K.START_RECORD)
        self.assertEqual(struct.unpack_from("<IQB", made), (0, K.siphash(K.KEY, struct.pack("<QB", 7, 3)), 3))
        self.assertEqual((made[-1], K.shown(K.START_RECORD)), (K.END, "S"))

    def test_runs_begin_with_a_start(self) -> None:
        rng = random.Random(1)  # noqa: S311 -- a fixed seed, so that every run draws the same cases
        for _ in range(20):
            items = K.with_starts(rng, [K.SAMPLE, K.SMALLEST])
            self.assertEqual(items[0], K.START_RECORD)
            self.assertEqual([i for i in items if i != K.START_RECORD], [K.SAMPLE, K.SMALLEST])

    def test_what_follows_is_more_than_the_largest_frame(self) -> None:
        head = K.journal(K.KEY, [K.SAMPLE])
        tail = K.after(K.KEY, head)
        self.assertGreater(len(tail), K.MAX_FRAME)
        self.assertEqual(K.frame_starts(head + tail)[:2], [0, len(K.format_frame(K.KEY))])

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
        key = K.KEY.hex()
        self.assertEqual(K.stopped(bytes(10 + K.MAX_FRAME), K.KEY, [], 10, "tag").want, f"F:{key} end torn 10")
        past = K.stopped(bytes(11 + K.MAX_FRAME), K.KEY, [], 10, "tag")
        self.assertEqual((past.want, past.prefix), (f"F:{key} end corrupt 10 tag", False))
        self.assertEqual(K.stopped(bytes(K.FIRST_FRAME), K.KEY, None, 0, "short").want, "end torn 0")
        self.assertEqual(K.stopped(bytes(K.FIRST_FRAME + 1), K.KEY, None, 0, "unterminated").want,
                         "end corrupt 0 unterminated")
        self.assertEqual(K.stopped(bytes(10), K.KEY, [], 0, "not-a-record").want,
                         f"F:{key} end corrupt 0 not-a-record")
        unknown = K.stopped(bytes(K.FIRST_FRAME + 11), K.KEY, None, 10, None)
        self.assertTrue(unknown.holds("end corrupt 10 too-long"))
        self.assertFalse(unknown.holds("end corrupt 100 too-long"))
        self.assertFalse(unknown.holds("end torn 10"))
        later = K.stopped(bytes(20), K.KEY, [], 0, "unterminated", later=True)
        self.assertEqual(later.want, f"F:{key} end corrupt 0 unterminated")

    def test_an_answer_ends_as_it_says(self) -> None:
        self.assertEqual(K.ending("F:00 C:1:61:1:2:3:62=1 end torn 29"), "torn")
        self.assertEqual(K.ending("end clean"), "clean")
        self.assertEqual(K.ending("F:00 end corrupt 29 format-again"), "format-again")

    def test_every_frame_cut_short_is_expected_torn(self) -> None:
        rng = random.Random(1)  # noqa: S311 -- a fixed seed, so that every run draws the same cases
        cases = K.torn_cases(rng, [K.SAMPLE, K.SMALLEST, K.LARGEST])
        self.assertTrue(all(c.want is not None and " end torn " in f" {c.want}" for c in cases))

    def test_junk_never_restores_what_it_replaces(self) -> None:
        rng = random.Random(1)  # noqa: S311 -- a fixed seed, so that every run draws the same cases
        for rest in (b"\xa5", b"ab", bytes(8)):
            with self.subTest(rest=rest):
                self.assertTrue(all(K.junk_for(rng, rest) != rest for _ in range(600)))

    def test_parts_cover_a_frame_and_follow_the_files_units(self) -> None:
        whole = K.encoded(K.KEY, 1000, K.LARGEST)
        found = K.partitions(whole, 1000)
        self.assertEqual(len(found), 3)
        for parts in found:
            self.assertEqual(parts[0][0], 0)
            self.assertEqual(parts[-1][1], len(whole))
            self.assertTrue(all(a < b == c for (a, b), (c, _) in itertools.pairwise(parts)))
        self.assertEqual([(1000 + b) % 512 for _, b in found[0][:-1]], [0] * (len(found[0]) - 1))
        self.assertEqual(len(found[2]), 3)
        self.assertEqual(len(K.partitions(K.encoded(K.KEY, 0, K.START_RECORD), 0)), 1)

    def test_kept_sets_are_proper_and_keep_the_ends(self) -> None:
        rng = random.Random(1)  # noqa: S311 -- a fixed seed, so that every run draws the same cases
        self.assertEqual(K.kept_sets(rng, 3), list(range(1, 7)))
        many = K.kept_sets(rng, 23)
        self.assertEqual(len(many), 62)
        self.assertTrue(all(0 < m < 2**23 - 1 for m in many))
        self.assertTrue({1, 1 << 22, 1 | 1 << 22} <= set(many))
        self.assertTrue(any(m >> 22 & 1 and m & 1 == 0 for m in many))

    def test_why_a_frame_fails_is_the_first_check_it_fails(self) -> None:
        data = K.journal(K.KEY, [K.SAMPLE])
        start = len(K.format_frame(K.KEY))
        body = len(K.payload(K.SAMPLE))
        changed = bytearray(data)
        changed[start + 4] ^= 1
        self.assertEqual(K.why_at(bytes(changed), start), "tag")
        changed = bytearray(data)
        changed[start + K.HEADER + body] ^= 1
        self.assertEqual(K.why_at(bytes(changed), start), "unterminated")
        changed = bytearray(data)
        changed[start + 1] ^= 0x80
        self.assertEqual(K.why_at(bytes(changed), start), "too-long")
        changed = bytearray(data)
        changed[start] += 1
        self.assertEqual(K.why_at(bytes(changed), start), "short")
        self.assertEqual(K.why_at(data[:start + 5], start), "short")

    def test_every_way_of_damage_changes_the_journal(self) -> None:
        rng = random.Random(1)  # noqa: S311 -- a fixed seed, so that every run draws the same cases
        data = K.journal(K.KEY, [K.SAMPLE])
        for way in range(9):
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
