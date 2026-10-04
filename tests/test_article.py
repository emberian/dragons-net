# SPDX-License-Identifier: AGPL-3.0-or-later
"""The article lane's own tools, on inputs made to test them: the cases written for the bounds are
the sizes they say, INN's test articles are read as a POST gets them and held to their recorded
digests, and every one of them has an answer recorded."""
from __future__ import annotations

from pathlib import Path
import re
import tempfile
import unittest
from unittest import mock

from gatekit import ROOT, script

K = script("article_check")


def header_size(article: bytes) -> int:
    return article.find(b"\r\n\r\n") + 2


class Cases(unittest.TestCase):
    """The cases written for a bound are on its two sides."""

    def test_padded_articles_have_the_header_sections_they_say(self) -> None:
        for size in (65536, 65537, 1000, 1001, 1009, 1010):
            with self.subTest(size=size):
                a = K.padded(size)
                self.assertEqual(header_size(a), size)
                self.assertLessEqual(max(len(ln) for ln in a[:header_size(a)].split(b"\r\n")), 998)

    def test_message_ids_and_paths_have_the_lengths_they_say(self) -> None:
        for n in (250, 251):
            self.assertEqual(len(K.msg_id(n)), n)
        head = len(b"Path: " + K.IDENTITY + b"!.POSTED!")
        for n in (997, 998, 999):
            path = K.path_with_first_line(n)
            self.assertEqual(head + len(path) - len(b"Path: "), n)

    def test_contexts_at_the_bounds_are_on_them(self) -> None:
        for ctx in K.BOUNDS:
            self.assertLessEqual(len(ctx.identity), 200)
            self.assertLessEqual(len(ctx.groups), 64)
            self.assertTrue(all(len(g) <= 64 for g in ctx.groups))
            self.assertLess(max(ctx.seq, ctx.run, ctx.conn), 2**64)
        self.assertIn(200, {len(c.identity) for c in K.BOUNDS})
        self.assertIn(64, {len(c.groups) for c in K.BOUNDS})
        self.assertIn(2**64 - 1, {c.seq for c in K.BOUNDS})

    def test_every_refusal_is_written_for(self) -> None:
        answered = {want.split()[1] for _, _, want in K.targeted() if want and want.startswith("refused")}
        self.assertEqual(answered, set(K.REASONS))


class Names(unittest.TestCase):
    """The lane names what the specification has, so that none of it goes untried."""

    @staticmethod
    def quoted_in(path: str, start: str) -> list[str]:
        text = (ROOT / path).read_text()
        block = text[text.index(start):]
        block = block[:block.index("\n\n")]
        return re.findall(r'\("([a-z-]+)",', block)

    def test_the_lane_tries_every_version_of_the_rules(self) -> None:
        self.assertEqual(self.quoted_in("lean/DN/News/ArticleSpec.lean", "def names :"), K.MUTANTS)

    def test_the_lane_knows_every_reason(self) -> None:
        self.assertEqual(self.quoted_in("lean/DN/News/ArticleModel.lean", "def reason :"), K.REASONS)


class Corpus(unittest.TestCase):
    """INN's test articles as a POST gets them."""

    def test_wire_articles_lose_their_terminator_and_stuffed_dots(self) -> None:
        wire = b"A: b\r\n\r\n..x\r\n.\r\n"
        self.assertEqual(K.as_posted("wire-x", wire), b"A: b\r\n\r\n.x\r\n")
        self.assertEqual(K.as_posted("native", b"A: b\n\nx\n"), b"A: b\r\n\r\nx\r\n")

    def test_a_proto_article_drops_what_an_injecting_agent_adds(self) -> None:
        posted = (b"Path: a!b\r\n c\r\nNewsgroups: example.test,example.config\r\nXref: s g:1\r\n"
                  b"Subject: s\r\n t\r\n\r\nPath: body\r\n")
        self.assertEqual(K.as_proto(posted), b"Newsgroups: local.test,local.other\r\nSubject: s\r\n t\r\n"
                                             b"\r\nPath: body\r\n")

    def test_the_corpus_is_the_recorded_one_and_fully_answered(self) -> None:
        files = K.corpus_files()
        self.assertEqual(set(files), set(K.CORPUS_EXPECTED))
        self.assertIn(b"OR IN CONNECTION WITH THE USE OR PERFORMANCE OF THIS SOFTWARE.",
                      (K.CORPUS / "LICENSE").read_bytes())
        with tempfile.TemporaryDirectory() as temp:
            copy = Path(temp)
            for name, data in files.items():
                (copy / name).write_bytes(data)
            (copy / "LICENSE").write_bytes((K.CORPUS / "LICENSE").read_bytes())
            (copy / "1").write_bytes(files["1"] + b"changed")
            with mock.patch.object(K, "CORPUS", copy), self.assertRaises(K.LaneError) as refused:
                K.corpus_files()
            self.assertIn("inn-articles/1", str(refused.exception))
            (copy / "1").write_bytes(files["1"])
            (copy / "extra").write_bytes(b"x")
            with mock.patch.object(K, "CORPUS", copy), self.assertRaises(K.LaneError) as refused:
                K.corpus_files()
            self.assertIn("extra", str(refused.exception))

    def test_an_article_is_dated_by_its_own_date(self) -> None:
        self.assertEqual(K.date_of(b"Date: Sat, 06 Mar 2004 21:39:44 -0800\r\n"), 1078637984)
        self.assertIsNone(K.date_of(b"Subject: none\r\n"))


if __name__ == "__main__":
    unittest.main()
