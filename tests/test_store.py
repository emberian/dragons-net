# SPDX-License-Identifier: AGPL-3.0-or-later
"""The store lane's own tools, on inputs made to test them: the directories it makes are the ones
it says, its table covers what decision 0005 lists, it fails where a second recovery, the two
answers or the documents do not hold, and what it tries and knows is what Lean has."""
from __future__ import annotations

import random
import re
import unittest

from gatekit import ROOT, script

S = script("store_check")
L = script("lanes")
J = script("journal_check")
START = J.START_RECORD


class Directories(unittest.TestCase):
    """The directories the lane makes."""

    def test_a_store_holds_its_journal_and_a_file_per_number(self) -> None:
        items = [START, S.commit(1, 1, size=3), S.commit(1, 2, size=5), START, S.commit(2, 3)]
        j, files = S.store(items)
        self.assertEqual(j, J.journal(S.KEY, items))
        self.assertEqual(files, [(b"journal", j), (S.named("a", 1), bytes(3)), (S.named("a", 2), bytes(1))])

    def test_names_are_the_letter_and_sixteen_hex_digits(self) -> None:
        self.assertEqual(S.named("q", 255), b"q00000000000000ff")
        self.assertEqual(S.named("a", 2**64 - 1), b"a" + b"f" * 16)

    def test_a_tail_kept_starts_with_where_it_was_cut(self) -> None:
        self.assertEqual(S.kept(b"abcdef", 4), (4).to_bytes(8, "little").hex() + b"ef".hex())
        self.assertEqual(S.keep_and_cut(b"abcdef", 4, 9)[1:], ["sync-dir", "cut:4"])

    def test_a_line_lists_the_directory_in_order(self) -> None:
        line = S.recover_line([(b"journal", b""), (b"x", b"\x01")], key=b"\x02", groups=[])
        self.assertEqual(line, "recover 02 - 6a6f75726e616c=-;78=01")
        self.assertEqual(S.recover_line([]).split(" ")[2:], [",".join(g.hex() for g in S.GROUPS), "-"])

    def test_starts_go_among_the_commits_in_their_order(self) -> None:
        rng = random.Random(1)  # noqa: S311 -- a fixed seed, so that every run draws the same cases
        cs = [S.commit(s) for s in range(1, 8)]
        drawn = [S.with_starts(rng, cs) for _ in range(50)]
        self.assertTrue(all(S.commits_of(items) == cs for items in drawn))
        self.assertTrue(any(START in items for items in drawn))
        self.assertTrue(any(items[-1] == START for items in drawn))

    def test_some_drawn_commits_break_each_rule_across_records(self) -> None:
        rng = random.Random(1)  # noqa: S311 -- a fixed seed, so that every run draws the same cases
        broken = set()
        for _ in range(400):
            cs = S.random_commits(rng, [b"local.test", b"local.more"])
            seqs = [c[0] for c in cs]
            if len(set(seqs)) != len(seqs):
                broken.add("seq")
            if any(name == b"local.zzz" for c in cs for name, _ in c[2]):
                broken.add("group")
            highest: dict[bytes, int] = {}
            for c in cs:
                if any(n <= highest.get(g, 0) for g, n in c[2]):
                    broken.add("number")
                highest.update({g: max(n, highest.get(g, 0)) for g, n in c[2]})
        self.assertEqual(broken, {"seq", "group", "number"})

    def test_drawn_directories_are_ones_a_listing_gives(self) -> None:
        rng = random.Random(1)  # noqa: S311 -- a fixed seed, so that every run draws the same cases
        for _ in range(300):
            key, _, files = S.random_store(rng)
            names = [n for n, _ in files]
            self.assertEqual(len(set(names)), len(names))
            self.assertEqual(len(key), 16)
            self.assertIn(b"journal", names)

    def test_every_way_of_damage_changes_the_directory(self) -> None:
        rng = random.Random(1)  # noqa: S311 -- a fixed seed, so that every run draws the same cases
        for _ in range(300):
            _, _, files = S.random_store(rng)
            self.assertNotEqual(S.damaged(rng, files), files)

    def test_drawn_actions_are_of_every_kind(self) -> None:
        rng = random.Random(1)  # noqa: S311 -- a fixed seed, so that every run draws the same cases
        lines = [c.line for c in S.actions_drawn(rng)]
        self.assertTrue(all(ln.startswith("apply ") and len(ln.split(" ")) == 3 for ln in lines))
        done = {a.split(":")[0] for ln in lines for a in ln.split(" ")[2].split(";")}
        self.assertEqual(done, {"keep", "rename", "remove", "sync-dir", "cut", "create", "-"})


class Table(unittest.TestCase):
    """The table holds what decision 0005 lists."""

    def test_every_case_of_the_table_has_its_answer(self) -> None:
        self.assertTrue(all(c.want is not None for c in S.table()))

    def test_the_table_finds_every_fault(self) -> None:
        self.assertEqual(S.unseen([c.want for c in S.table()]), [])

    def test_the_table_recovers_with_every_action(self) -> None:
        actions = {a.split(":")[0] for c in S.table() if c.want.startswith("ok ")
                   for a in c.want.split(" ")[6].split(";")}
        self.assertEqual(actions, {"keep", "rename", "remove", "sync-dir", "cut", "create", "-"})

    def test_the_table_holds_starts_whole_and_torn(self) -> None:
        lines = [c.line for c in S.table()]
        whole = J.journal(S.KEY, [START]).hex()
        torn = S.torn_after(S.KEY, J.format_frame(S.KEY), START, 5).hex()
        self.assertTrue(any(f"={whole};" in ln or ln.endswith(f"={whole}") for ln in lines))
        self.assertTrue(any(f"={torn}" in ln for ln in lines))

    def test_no_directory_is_listed_twice(self) -> None:
        lines = [c.line for c in S.table()]
        self.assertEqual(len(set(lines)), len(lines))


class Holding(unittest.TestCase):
    """What the lane refuses: answers that differ, a fault never seen, a second recovery that does
    not hold, documents stating other numbers."""

    FIRST = "ok 00 5 100 C:1 3,2 keep:6a:00;sync-dir;cut:100"

    def again(self, *changed: tuple[int, str]) -> str:
        words = self.FIRST.split(" ")
        words[6] = "-"
        for k, value in changed:
            words[k] = value
        return " ".join(words)

    def test_a_second_recovery_holds_only_as_the_first(self) -> None:
        self.assertIsNone(S.again_problem(self.FIRST, self.again()))
        self.assertIsNone(S.again_problem(self.FIRST, self.again((2, "4"), (5, "2,3"))))
        for changed, problem in (((1, "01"), "its key changed"), ((3, "99"), "its end of the journal changed"),
                                 ((4, "C:2"), "its articles changed"), ((2, "6"), "its next number is higher"),
                                 ((5, "2"), "other files are set aside"), ((6, "sync-dir"), "actions are left")):
            with self.subTest(changed=changed):
                self.assertEqual(S.again_problem(self.FIRST, self.again(changed)), problem)
        self.assertEqual(S.again_problem(self.FIRST, "corrupt bad-key"), "it does not recover")

    def test_the_first_answer_that_differs_is_told(self) -> None:
        self.assertIsNone(L.differing(["a", "b"], ["1", "2"], ["1", "2"]))
        said = L.differing(["a", "b", "c"], ["1", "2", "3"], ["1", "x", "y"])
        self.assertEqual(said, "b: the model answers 2, the reference x")

    def test_a_fault_no_answer_shows_is_told(self) -> None:
        answers = [f"corrupt {f} 1" for f in S.FAULTS if f != "exhausted"] + ["ok 00 1 50 - - -"]
        self.assertEqual(S.unseen(answers), ["exhausted"])

    def test_a_number_stated_otherwise_anywhere_is_told(self) -> None:
        measured = {"cases": "1,587", "that recover": "776"}
        self.assertEqual(L.misstated("on 1,587 cases and 776 that recover; 1,587 cases", measured), [])
        self.assertEqual(L.misstated("on 1,587 cases and 1,500 cases, 776 that recover", measured),
                         ["'cases': 1,587, 1,500, not 1,587"])
        self.assertEqual(L.misstated("on 1,587 cases", measured), ["'that recover': none, not 776"])

    def test_a_section_runs_to_the_next_heading(self) -> None:
        text = "a\n### Store\nbody\n### Next\nmore"
        self.assertEqual(L.section(text, "\n### Store\n", "\n### "), "\n### Store\nbody")


class Names(unittest.TestCase):
    """The lane names what the specification has, so that none of it goes untried."""

    @staticmethod
    def block(path: str, start: str) -> str:
        text = (ROOT / path).read_text()
        found = text[text.index(start):]
        return found[:found.index("\n\n")]

    def test_the_lane_tries_every_version_of_recovery(self) -> None:
        names = re.findall(r'\("([a-z-]+)",', self.block("lean/DN/News/RecoveryMutant.lean", "def names :"))
        self.assertEqual(names, S.MUTANTS)

    def test_the_lane_knows_every_fault(self) -> None:
        faults = re.findall(r'=> (?:s!)?"([a-z-]+)', self.block("lean/DN/News/RecoveryModel.lean", "def faultText"))
        self.assertEqual(faults, S.FAULTS)


if __name__ == "__main__":
    unittest.main()
