# SPDX-License-Identifier: AGPL-3.0-or-later
"""The tools that take the grammar of header fields from the RFCs and hold it to them, on grammars
and texts made to fail them: the reading and printing of ABNF, the generator's refusals and its
count of depth, and what the lane takes for the RFCs' examples and holds to the library's own
transcriptions of an RFC."""
from __future__ import annotations

import re
from typing import Any
import unittest
from unittest import mock

from gatekit import ROOT, script

A = script("abnf_text")
gen_abnf = script("gen_abnf")
abnf_check = script("abnf_check")


def seq(*items: Any) -> Any:
    return A.Seq(tuple(items))


def alt(*items: Any) -> Any:
    return A.Alt(tuple(items))


class Reading(unittest.TestCase):
    """`abnf_text`: a rule found where an RFC prints it, and printed so that it reads back."""

    def test_a_rule_is_found_across_a_page_break(self) -> None:
        # A rule the page's footer, form feed and running header cut in two.
        text = (
            '   rule-a   =  "x" /\n'
            "\n"
            "Author                      Standards Track                     [Page 3]\n"
            "\f\n"
            "RFC 9999                          Title                      January 2000\n"
            "\n"
            '                "y"\n'
            "\n"
            "   Prose that follows.\n"
        )
        self.assertEqual(A.parse(A.extract(text, "rule-a")),
                         ("rule-a", False, alt(A.Text(b"x"), A.Text(b"y"))))
        with self.assertRaises(A.RuleMissing):
            A.extract(text, "rule-b")

    def test_every_term_reads_back_as_it_is_printed(self) -> None:
        terms = {
            "*(4x)": A.Rep(0, None, A.Rep(4, 4, A.Ref("x"))),
            "[a b]": A.Rep(0, 1, seq(A.Ref("a"), A.Ref("b"))),
            "1*2(a / b)": A.Rep(1, 2, alt(A.Ref("a"), A.Ref("b"))),
            'a (b / "c") %x41-5A %x0D.0A': seq(A.Ref("a"), alt(A.Ref("b"), A.Text(b"c")),
                                                A.Range(0x41, 0x5A), A.Exact(b"\r\n")),
        }
        for printed, term in terms.items():
            with self.subTest(printed=printed):
                self.assertEqual(A.show(term), printed)
                self.assertEqual(A.parse(f"r = {printed}"), ("r", False, term))


class Generator(unittest.TestCase):
    """`gen_abnf`: what it refuses, the space it adds, and the depth it counts."""

    def test_a_left_recursive_grammar_is_refused(self) -> None:
        grammars = {
            "directly": {"a": seq(A.Ref("a"), A.Text(b"x"))},
            "behind what may match nothing": {
                "a": seq(A.Ref("n"), A.Ref("b")), "b": alt(A.Text(b"y"), A.Ref("a")),
                "n": A.Rep(0, 1, A.Text(b"z"))},
        }
        for how, grammar in grammars.items():
            with self.subTest(how=how), self.assertRaises(SystemExit) as refused:
                gen_abnf.depth(grammar)
            self.assertIn("left-recursive", str(refused.exception))

    def test_depth_counts_the_levels_at_one_position(self) -> None:
        # A rule nested in itself after a byte is not left recursion: a repetition that starts
        # after "(" goes down 4 levels, to the "(" of the next comment.
        nested = {"c": seq(A.Text(b"("), A.Rep(0, None, A.Ref("c")), A.Text(b")"))}
        self.assertEqual(gen_abnf.depth(nested), 4)
        # What follows a part that may match nothing starts where the part does, and counts;
        # a run's reference to "a" is 1 level, its sequence 1, and "d" behind "n" 5 more.
        nothing = {"a": seq(A.Ref("n"), A.Ref("d")), "n": A.Rep(0, 1, A.Text(b"z")),
                   "d": alt(alt(alt(A.Text(b"q"))))}
        self.assertEqual(gen_abnf.depth(nothing), 7)
        something = {**nothing, "n": A.Rep(1, 1, A.Text(b"z"))}
        self.assertEqual(gen_abnf.depth(something), 5)

    def test_the_space_after_a_fields_colon_is_added_once(self) -> None:
        to = seq(A.Text(b"To:"), A.Ref("address-list"), A.Ref("crlf"))
        spaced = gen_abnf.spaced("to", to)
        self.assertEqual(spaced, seq(A.Text(b"To:"), A.Ref("sp"), A.Ref("address-list"), A.Ref("crlf")))
        self.assertIs(gen_abnf.spaced("to", spaced), spaced)
        optional = seq(A.Ref("field-name"), A.Text(b":"), A.Ref("unstructured"), A.Ref("crlf"))
        self.assertEqual(gen_abnf.spaced("optional-field", optional).items[2], A.Ref("sp"))
        for rule in (seq(A.Ref("a"), A.Ref("crlf")), A.Ref("a")):
            with self.subTest(rule=A.show(rule)), self.assertRaises(SystemExit) as refused:
                gen_abnf.spaced("x", rule)
            self.assertIn("no colon", str(refused.exception))

    def test_a_rule_printed_otherwise_than_it_reads_is_refused(self) -> None:
        rules = {"r": A.Rep(0, None, A.Rep(4, 4, A.Ref("x")))}
        self.assertIn("\nr = *(4x)\n", gen_abnf.abnf_file(rules, {"r": "RFC 0"}))
        with mock.patch.object(gen_abnf.A, "show", lambda _: "*4x"), \
                self.assertRaises(SystemExit) as refused:
            gen_abnf.abnf_file(rules, {"r": "RFC 0"})
        self.assertIn("reads back otherwise", str(refused.exception))

    def test_the_transcriptions_are_held_to_the_rfcs_text(self) -> None:
        gen_abnf.check_transcriptions()
        self.assertEqual(gen_abnf.quoted('a := "(" / <"> "/"'), {"(", '"', "/"})
        wide = {"token": ("RFC 2045 §5.1", "token = 1*%d33-126")}
        with mock.patch.dict(gen_abnf.TRANSCRIBED, wide), self.assertRaises(SystemExit) as refused:
            gen_abnf.check_transcriptions()
        self.assertIn("token: the ranges allow", str(refused.exception))
        with mock.patch.object(gen_abnf, "notation", lambda *_: "token := 1*<any CHAR>"), \
                self.assertRaises(SystemExit) as refused:
            gen_abnf.check_transcriptions()
        self.assertIn("the RFC defines token as", str(refused.exception))
        with mock.patch.object(gen_abnf, "rfc", lambda _: "   other := x\n"), \
                self.assertRaises(SystemExit) as refused:
            gen_abnf.notation(2045, "token")
        self.assertIn("does not define token", str(refused.exception))

    def test_the_notice_carries_rfc_2231s_own(self) -> None:
        paragraphs = gen_abnf.notice()
        self.assertIn("RFC 2231: Copyright (C) The Internet Society (1997). All Rights Reserved.",
                      paragraphs)
        self.assertTrue(paragraphs[-1].startswith("This document and translations of it"))
        self.assertTrue(paragraphs[-1].endswith("languages other than English."))
        moved = {"no statement": "RFC 2231 text without it\n",
                 "another paragraph": "12.  Full Copyright Statement\n\n"
                                      "   Copyright (C) The Internet Society (1997).\n\n"
                                      "   Something else.\n"}
        for how, text in moved.items():
            with self.subTest(how=how), mock.patch.object(gen_abnf, "rfc", lambda _, t=text: t), \
                    self.assertRaises(SystemExit):
                gen_abnf.rfc2231_notice()


class Lane(unittest.TestCase):
    """`abnf_check`: what it takes for an example and what it holds to the library."""

    def test_prose_that_names_a_field_is_not_an_example(self) -> None:
        text = (
            "   The text goes on to the\n"
            "   Subject: line, which is prose.\n"
            "\n"
            "      Subject: an example\n"
            "        folded\n"
            "      To: x@y.example\n"
            "   ----\n"
            "   From  : a@b.example\n"
            "   __\n"
            "        <c@d.example>\n"
            "\n"
            "   X-Other: a field the checks do not know\n"
        )
        with mock.patch.object(abnf_check.G, "rfc", lambda _: text):
            found = abnf_check.printed(0)
        self.assertEqual(found, [("subject", b"Subject: an example\r\n folded\r\n"),
                                 ("to", b"To: x@y.example\r\n"),
                                 ("from", b"From  : a@b.example\r\n  \r\n <c@d.example>\r\n")])

    def test_the_lane_tries_every_mutant_of_the_interpreter(self) -> None:
        text = (ROOT / "lean/DN/News/AbnfMutant.lean").read_text()
        block = text[text.index("def names :"):]
        block = block[:block.index("\n\n")]
        self.assertEqual(re.findall(r'\("([a-z-]+)",', block), abnf_check.MUTANTS)

    def test_the_rfcs_examples_expect_what_rfc_5536_allows(self) -> None:
        expected = abnf_check.examples()
        for _, want, why in expected:
            self.assertEqual(want == "0", bool(why))
        refused = {data.split(b"\r\n")[0].decode(): why for (_, data), want, why in expected if want == "0"}
        self.assertEqual(len(refused), 9)
        self.assertLessEqual(set(abnf_check.OBSOLETE), set(refused))
        self.assertEqual(refused["To:A Group(Some people)"], "no space after the colon (RFC 5536 §2.2)")
        self.assertEqual(refused["Subject     : Saying Hello"],
                         "white space before the colon (RFC 5322 §4.5)")
        accepted = {data for (_, data), want, _ in expected if want == "1"}
        # The obsolete phrase, which RFC 5536 §2.1 keeps.
        self.assertIn(b"From: Joe Q. Public <john.q.public@example.com>\r\n", accepted)
        with mock.patch.dict(abnf_check.OBSOLETE, {"Never: printed": "a line no RFC has"}), \
                self.assertRaises(abnf_check.LaneError):
            abnf_check.examples()

    def test_only_rules_taken_unchanged_are_held_to_the_library(self) -> None:
        names = ["to", "address-list", "comment", "orig-date", "return", "date-time",
                 "optional-field", "parameter", "ipv6address"]
        cases = [(name, b"x") for name in names]
        held = abnf_check.library_cases(cases, ["1"] * len(names))
        self.assertEqual({rule for rule, _ in held["rfc5322"]}, {"to", "address-list", "comment"})
        self.assertEqual({rule for rule, _ in held["rfc3986"]}, {"ipv6address"})
        refused = abnf_check.library_cases(cases, ["0"] * len(names))
        self.assertEqual(refused, {"rfc5322": [], "rfc3986": []})


if __name__ == "__main__":
    unittest.main()
