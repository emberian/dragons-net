# SPDX-License-Identifier: AGPL-3.0-or-later
"""What the compiler prints and what the native lanes make of it, without a Pancake compiler: the
golden sources, the reply reference, the entry decision, the parser's tree, the generated-programs
lane on stand-ins for the compiled code, and the corpus of stopping states."""
from __future__ import annotations

from collections.abc import Callable
import contextlib
import hashlib
import io
import json
import os
from pathlib import Path
import re
import subprocess
import tempfile
from typing import Any
import unittest
from unittest import mock

from gatekit import DN_COMPILER, ROOT, run, script

entry_bench = script("entry_bench")
fuzz_interp = script("fuzz_interp")
fuzz_reduce = script("fuzz_reduce")
gen_keywords = script("gen_keywords")
lanes = script("lanes")
native_baseline = script("native_baseline")
native_fuzz = script("native_fuzz")
parse_check = script("parse_check")
parser_contract = script("parser_contract")
state_check = script("state_check")

STUB_LEXER = """Definition get_keyword_def:
  get_keyword s =
  if s = "skip" then (KeywordT SkipK) else
  if s = "if" then (KeywordT IfK) else
  if s = "else" then (KeywordT ElseK) else
  if s = "while" then (KeywordT WhileK) else
  if s = "var" then (KeywordT VarK) else
  if s = "return" then (KeywordT RetK) else
  if s = "@base" then (KeywordT BaseK) else
  if s = "" then LexErrorT $ empty
  else IdentT s
End
"""



class Emitted(unittest.TestCase):
    """What `dn-compiler` prints, and the gate it prints through."""

    def test_the_session_passes_the_safety_analysis(self) -> None:
        """The analysis the kernel runs for the session's theorem, compiled: when a change to the
        program makes the theorem fail, this names the first alarm."""
        done = subprocess.run([str(DN_COMPILER), "analyze-session"], text=True, capture_output=True,
                              check=False, timeout=600)
        self.assertEqual((done.returncode, done.stdout), (0, "safe\n"), done.stderr)

    def test_recovery_passes_the_safety_analysis(self) -> None:
        """The analysis of decision 0004 on recovery's step in a loop, its area at the heap's start:
        recovery is to be embedded in the session's program, whose theorem then needs it."""
        done = subprocess.run([str(DN_COMPILER), "analyze-recover"], text=True, capture_output=True,
                              check=False, timeout=600)
        self.assertEqual((done.returncode, done.stdout), (0, "safe\n"), done.stderr)

    def test_grammar_passes_the_safety_analysis(self) -> None:
        """The analysis of decision 0004 on the grammar's program, its area above the heap's header:
        the grammar is to be embedded in the session's program, whose theorem then needs it."""
        done = subprocess.run([str(DN_COMPILER), "analyze-grammar"], text=True, capture_output=True,
                              check=False, timeout=600)
        self.assertEqual((done.returncode, done.stdout), (0, "safe\n"), done.stderr)

    def test_the_lean_parser_reads_each_printed_program_as_lowered(self) -> None:
        """DN.Compiler.Parse, the Lean copy of CakeML's parser, reads every printed program as its
        lowering in the canonical form, and each cell of the precedence table as the table says.
        scripts/check_parse.sh holds the same trees and refusals to HOL4's own parser."""
        programs = json.loads(run([str(DN_COMPILER), "emit-trees"]).stdout)
        trees = json.loads(run([str(DN_COMPILER), "parse-trees"]).stdout)
        self.assertEqual(len(trees), len(programs))
        for program, tree in zip(programs, trees, strict=True):
            with self.subTest(program=program["name"]):
                self.assertIsNotNone(tree)
                parse_check.compared(program, tree)
        cells = json.loads(run([str(DN_COMPILER), "emit-cells"]).stdout)
        readings = json.loads(run([str(DN_COMPILER), "parse-cells"]).stdout)
        self.assertEqual(parse_check.cells_read(cells, readings), len(cells))

    def test_the_lean_parser_refuses_forms_never_printed(self) -> None:
        """A form the gate never prints is refused, though its like is read; white space is HOL's."""
        def reading(text: str) -> Any:
            return json.loads(subprocess.run([str(DN_COMPILER), "parse-text"], input=text, text=True,
                                             capture_output=True, check=True, timeout=60).stdout)

        def body(*lines: str) -> str:
            return "fun f(1 a) {\n" + "".join(f"  {line}\n" for line in lines) + "  return a;\n}\n"

        plain = body("var r = g(a);", "@dn_x(a, a, a, a);")
        self.assertIsNotNone(reading(plain))
        # HOL's isSpace: the codes 9 to 13 as well as the space.
        for c in "\t\v\f\r":
            with self.subTest(space=ord(c)):
                self.assertEqual(reading(plain.replace(" ", c)), reading(plain))
        refused = {"the primitive AddCarry": body("var r = __add_with_carry__(a);"),
                   "@top, a keyword": body("@top(a, a, a, a);"), "@ alone": body("@(a, a, a, a);")}
        for name, text in refused.items():
            with self.subTest(name):
                self.assertIsNone(reading(text))

    def test_certificates_of_the_analysis_are_current(self) -> None:
        """The modules whose claims the kernel checks a declaration each are what the generator
        prints for the programs as they are."""
        for what, module in (("session", "lean/DN/Server/SessionCert.lean"),
                             ("recover", "lean/DN/News/RecoverCert.lean")):
            done = subprocess.run([str(DN_COMPILER), "analysis-cert", what], text=True, capture_output=True,
                                  check=False, timeout=600)
            self.assertEqual(done.returncode, 0, done.stderr)
            self.assertEqual(done.stdout, (ROOT / module).read_text(), f"{module} is stale: regenerate it")

    def test_emitted_sources_match_the_golden_files(self) -> None:
        def emit(target: str) -> str:
            return subprocess.run([str(DN_COMPILER), f"emit-{target}"], text=True, capture_output=True,
                                  check=True, timeout=600).stdout

        for name in ("region", "echo", "render", "crc", "sip", "scan", "reply", "skeleton",
                     "frame-line", "frame-line-4", "frame-block-64", "frame-block-4"):
            with self.subTest(target=name):
                self.assertEqual(emit(name), (ROOT / "tests/golden" / f"{name}.pnk").read_text())
        # The whole programs, the differential fixture and the reply cases are too long to read in a
        # diff; their digests catch a change just as well.
        self.assertEqual(hashlib.sha256(emit("session").encode()).hexdigest(),
                         "2d243e08c9215ae871124455a4890c590d73bbf809a6d7bad5b9e59a028d3b91")
        self.assertEqual(hashlib.sha256(emit("recover").encode()).hexdigest(),
                         "8f562e94aa1ba27b2c0c00f99fed5732470d27594079e46a8778fbf369b24472")
        self.assertEqual(hashlib.sha256(emit("baseline").encode()).hexdigest(),
                         "1a845eaaa7ab24f9bb87bc80e5e0720642e1a60692168376695f931a659be89a")
        self.assertEqual(hashlib.sha256(emit("reply-cases").encode()).hexdigest(),
                         "e35a50cc0aaff19efdafb7138c2da756c14a3037ce4438abc42b86584e9dd40e")

    def test_emitter_has_no_build_side_effects(self) -> None:
        with tempfile.TemporaryDirectory() as temp:
            first = subprocess.run([str(DN_COMPILER), "emit-region"], cwd=temp, check=True,
                                   text=True, capture_output=True).stdout
            second = subprocess.run([str(DN_COMPILER), "emit-region"], cwd=temp, check=True,
                                    text=True, capture_output=True).stdout
            self.assertEqual(first, second)
            self.assertEqual(list(Path(temp).iterdir()), [])
            self.assertTrue(first.startswith("export fun dn_region("))
            result = subprocess.run([str(DN_COMPILER), "unknown"], capture_output=True, check=False)
            self.assertEqual(result.returncode, 2)

    def compiled(self, text: str | bytes) -> subprocess.CompletedProcess[str]:
        with tempfile.TemporaryDirectory() as temp:
            path = Path(temp, "input.json")
            path.write_bytes(text if isinstance(text, bytes) else text.encode())
            return subprocess.run([str(DN_COMPILER), "compile", str(path)], text=True, capture_output=True,
                                  check=False, timeout=60)

    def test_compile_prints_the_examples_as_the_built_in_programs(self) -> None:
        for name in ("region", "echo"):
            done = subprocess.run([str(DN_COMPILER), "compile", str(ROOT / f"examples/{name}.json")], text=True,
                                  capture_output=True, check=True, timeout=60)
            self.assertEqual(done.stdout, run([str(DN_COMPILER), f"emit-{name}"]).stdout, name)

    def test_compile_refuses_with_stable_codes(self) -> None:
        def program(body: list[Any], params: list[str] | None = None, name: str = "dn_x", **more: Any) -> str:
            function = {"name": name, "params": ["a"] if params is None else params, "body": body}
            return json.dumps({"dn_input": 1, "function": function, **more})

        def nested(levels: int) -> Any:
            e: Any = "a"
            for _ in range(levels):
                e = ["+", e, 1]
            return e

        deep = nested(300)
        small = program([["return", "a"]])
        cases: list[tuple[str | bytes, str, int]] = [
            ("{", "DN0001", 3),
            (b"\xff\xfe", "DN0001", 3),
            (json.dumps({"dn_input": 2, "function": {}}), "DN0002", 3),
            ('{"dn_input": 1.0, "function": {}}', "DN0006", 3),
            ('{"dn_input": 1e1000000, "function": {}}', "DN0006", 3),
            ('{"dn_input": 1e10000000000, "function": {}}', "DN0006", 3),
            ('{"dn_input": 1E9, "function": {}}', "DN0006", 3),
            ('{"dn_input": 1, "function": {}, "x": ' + "1" * 21 + "}", "DN0006", 3),
            (program([["return", ["+", "a", "1" * 20]]], name="dn_e1e9.5"), "DN0100", 1),
            (program([["return", "a"]], name='dn_"1e9'), "DN0100", 1),
            (program([["return", -1]]), "DN0006", 3),
            (" " * (1 << 20) + "{}", "DN0003", 3),
            (small + " " * ((1 << 18) + 1 - len(small)), "DN0003", 3),
            # The file, the function, its body and the statement are four levels around the expression.
            (program([["return", nested(253)]]), "DN0004", 3),
            (program([["return", deep]]), "DN0004", 3),
            (program([["return", "a"]], colour="blue"), "DN0005", 3),
            (json.dumps({"dn_input": 1, "function": {"name": "dn_x", "params": [], "body": [], "spare": 1}}),
             "DN0005", 3),
            (program([["jump", "a"]]), "DN0006", 3),
            (json.dumps({"function": {}}), "DN0006", 3),
            (program([["return", "a"]], name="x"), "DN0101", 1),
            (program([["return", "a"]], params=["a", "a"]), "DN0105", 1),
            (program([["return", "b"]]), "DN0107", 1),
            (program([["set", "a", 1]]), "DN0122", 1),
            (program([["call", "r", "f", ["a"]], ["return", "r"]],
                     calls=[{"name": "f", "params": ["x"], "body": [["call", "y", "f", ["x"]], ["return", "y"]]}]),
             "DN0123", 1),
        ]
        for text, code, status in cases:
            done = self.compiled(text)
            self.assertEqual((done.returncode, done.stdout), (status, ""), (code, done.stderr))
            self.assertTrue(done.stderr.startswith(f"error[{code}]: "), (code, done.stderr))
        # At the bounds, 256 KiB and 256 levels, an input is taken.
        for text in (small + " " * ((1 << 18) - len(small)), program([["return", nested(252)]])):
            self.assertEqual(self.compiled(text).returncode, 0)
        # A message that quotes the input escapes its control characters, and is cut at 300 of them.
        def with_field(name: str) -> str:
            return json.dumps({"dn_input": 1, "function": json.loads(small)["function"], name: 1})

        done = self.compiled(with_field("\u001b[2J\u007f"))
        self.assertEqual(done.stderr, "error[DN0005]: a field the format does not have: \\u001b[2J\\u007f\n")
        message = "a field the format does not have: " + "x" * 400
        done = self.compiled(with_field("x" * 400))
        self.assertEqual(done.stderr, f"error[DN0005]: {message[:300]}...\n")
        self.assertIn("statement 1: a literal", self.compiled(program([["var", "b", 1], ["return", -1]])).stderr)

    def test_keyword_table_is_generated_from_the_pinned_lexers(self) -> None:
        lock = json.loads((ROOT / "backend/lock.json").read_text())
        recorded = {source["revision"] for source in lock["lexer_sources"]}
        self.assertEqual(recorded, {lock["cakeml"]["revision"],
                                    json.loads((ROOT / "tools.lock.json").read_text())
                                    ["cake"]["source_revision"]})
        table = (ROOT / "lean/DN/Compiler/Keywords.lean").read_text()
        self.assertIn("Generated by scripts/gen_keywords.py", table)
        self.assertEqual(set(re.findall(r'\("([0-9a-f]{40})"', table)), recorded)
        # A word dropped from every list is invisible to the native check, which only
        # compares the words that are there.
        self.assertLessEqual(gen_keywords.EXPECTED, set(re.findall(r'"([a-z0-9]+)"', table)))
        # The namespace the validator enforces is the one the native lane looks for.
        prefix = re.search(r'def exportPrefix : String := "([^"]+)"',
                           (ROOT / "lean/DN/Compiler/Checked.lean").read_text())
        assert prefix is not None
        self.assertEqual(prefix.group(1), lanes.EXPORT_PREFIX)

    def test_generated_table_refuses_a_lexer_that_changed_shape(self) -> None:
        source = {"component": "cakeml", "path": "pancake/parser/panLexerScript.sml",
                  "revision": "a" * 40, "sha256": ""}
        rendered = gen_keywords.render([source], lambda _: STUB_LEXER.encode())
        self.assertIn('"skip", "if", "else", "while", "var", "return"', rendered)
        self.assertNotIn("@base", rendered)
        broken = {
            "changed shape": STUB_LEXER.replace('  if s = "while" then (KeywordT WhileK) else\n', ""),
            "not plain names": STUB_LEXER.replace('"skip"', '"sk ip"'),
            "lexer moved": STUB_LEXER.replace("Definition get_keyword_def:", "Definition other:"),
        }
        for reason, lexer in broken.items():
            with self.subTest(reason=reason):
                with self.assertRaises(SystemExit) as refused:
                    gen_keywords.render([source], lambda _, text=lexer: text.encode())
                self.assertIn(reason, str(refused.exception))
        with self.assertRaises(SystemExit):
            gen_keywords.render([], lambda _: STUB_LEXER.encode())

    def test_pancake_warnings_are_never_silenced(self) -> None:
        # A Pancake warning keeps the exit status at zero, so the scripts read stderr;
        # the compiler flag that hides those warnings must not appear anywhere.
        here = Path(__file__).name
        for source in [*sorted((ROOT / "scripts").glob("*.py")),
                       *sorted((ROOT / "tests").glob("*.py"))]:
            if source.name == here:  # this file names the flag in order to forbid it
                continue
            with self.subTest(script=source.name):
                self.assertNotIn("no_warn", source.read_text())


class StateCorpus(unittest.TestCase):
    """The corpus of stopping states and its independent check."""

    def test_state_check_reads_the_whole_state(self) -> None:
        """The lane compares every printed field, not only the value a run computes."""
        lines = ["CASE ok", "PROG (seq (assign x (const 1)) (ret (var x)))", "CODE ()", "LOCALS x=5",
                 "MEM 0=0", "DOM 0", "BE 0", "CLOCK 4", "BASE 0", "ANSWERS", "NAMES x",
                 "RESULT return:1", "FLOCALS x=", "FMEM 0=0", "FCALLS 0", "FTRACE",
                 "FCLOCK 4", "FBASE 0", "END"]
        agreeing = "\n".join(lines)
        with tempfile.TemporaryDirectory() as temp:
            dump = Path(temp) / "dump"

            def check(text: str) -> subprocess.CompletedProcess[str]:
                dump.write_text(text)
                return subprocess.run(
                    ["python3", "-P", str(ROOT / "scripts/state_check.py"), "--dump", str(dump),
                     "--out", str(Path(temp) / "out")],
                    capture_output=True, text=True, check=False)

            first = check(agreeing)
            self.assertEqual(first.returncode, 0, first.stderr)
            # Each field carries something no value comparison would see: a return
            # empties the locals, a clock is spent, an external call is recorded.
            # Every field the lane compares is perturbed here, and the list of
            # them is pinned: dropping one from `FIELDS` would go unnoticed.
            self.assertEqual(set(state_check.FIELDS),
                             {"RESULT", "FLOCALS", "FMEM", "FCALLS", "FTRACE", "FCLOCK", "FBASE"})
            wrong = {"RESULT return:1": "RESULT return:2",
                     "FLOCALS x=": "FLOCALS x=5",
                     "FCLOCK 4": "FCLOCK 3",
                     "FCALLS 0": "FCALLS 1",
                     "FMEM 0=0": "FMEM 0=7",
                     "FTRACE": "FTRACE read:-:00",
                     "FBASE 0": "FBASE 8"}
            for field, replacement in wrong.items():
                with self.subTest(field=field):
                    result = check(agreeing.replace(field, replacement))
                    self.assertEqual(result.returncode, 1, result.stdout)
                    self.assertIn("ok disagrees", result.stderr)
                    self.assertIn(field.split(" ")[0], result.stderr)

    def test_state_corpus_reaches_the_stopping_branches(self) -> None:
        """A corpus of successful runs would prove nothing about the other half."""
        dump = run([str(DN_COMPILER), "dump-states"]).stdout
        results = [line.partition(" ")[2] for line in dump.splitlines()
                   if line.startswith("RESULT ")]
        self.assertGreaterEqual(len(results), 40)
        for expected in ("error", "timeout"):
            self.assertGreaterEqual(results.count(expected), 2, expected)
        self.assertGreaterEqual(sum(1 for r in results if r.startswith("return:")), 5)
        self.assertGreaterEqual(sum(1 for r in results if r.startswith("final:")), 2)
        # Every construct of the subset is exercised, so a clause cannot drift
        # unseen for want of a case.
        programs = [line for line in dump.splitlines() if line.startswith("PROG ")]
        for construct in ("(skip)", "(dec ", "(assign ", "(store ", "(storeb ", "(extcall ",
                          "(seq ", "(if ", "(while ", "(ret ", "(mul ", "(and ", "(shr ", "(shl ", "(xor ", "(or ",
                          "(loadb ", "(loadw ", "(base)", "(less ", "(equal ", "(notless ", "(deccall ",
                          "(sub "):
            with self.subTest(construct=construct):
                self.assertTrue(any(construct in p for p in programs), construct)
        # The write-back clause an external call cannot reach has its own cases.
        self.assertGreaterEqual(sum(1 for line in dump.splitlines() if line.startswith("WRITE ")), 3)
        # What the documents claim about the corpus is what the corpus is.
        stopping = sum(1 for r in results if r != "none")
        for name in ("docs/assurance.md", "docs/baseline.md"):
            with self.subTest(document=name):
                text = (ROOT / name).read_text()
                self.assertIn(f"{len(results)} cases", text)
        self.assertIn(f"{len(results)} cases, {stopping} of which stop",
                      (ROOT / "docs/baseline.md").read_text())
        writes = sum(1 for line in dump.splitlines() if line.startswith("WRITE "))
        for name in ("docs/assurance.md", "docs/pancake-semantics.md"):
            with self.subTest(document=name):
                self.assertIn(f"{writes} write-backs", (ROOT / name).read_text())


class Replies(unittest.TestCase):
    """The reply table's reference."""

    def test_reply_reference_refuses_a_fixture_it_should(self) -> None:
        emitted = subprocess.run([str(DN_COMPILER), "emit-reply-cases"], text=True, capture_output=True,
                                 check=True, timeout=600).stdout
        fixture = json.loads(emitted)
        native_baseline.reply_cases(fixture)
        short = list(b"MODE READE")
        quit_ = list(b"QUIT")
        broken: dict[str, tuple[str, Callable[[dict[str, Any]], None]]] = {
            "a reply the reference disagrees with": ("Lean/Python disagreement",
                                                     lambda f: f["cases"][0]["output"].append(0)),
            "a buffer the longest reply does not need": ("longest reply",
                                                         lambda f: f.update(max_len=f["max_len"] + 1)),
            "a keyword boundary the inputs lost": ("no longer reach", lambda f: f.update(
                cases=[case for case in f["cases"] if case["input"] != short])),
            "the keyword itself lost": ("no longer reach", lambda f: f.update(
                cases=[case for case in f["cases"] if case["input"] != quit_])),
            "every change to the last byte of a keyword lost": ("no longer reach", lambda f: f.update(
                cases=[case for case in f["cases"] if len(case["input"]) < 4 or
                       case["input"][:3] != quit_[:3] or case["input"][3] == quit_[3]])),
            "another function's cases": ("unexpected reply function",
                                         lambda f: f.update(function="dn_other")),
        }
        for name, (message, change) in broken.items():
            with self.subTest(fixture=name):
                copy = json.loads(emitted)
                change(copy)
                with self.assertRaisesRegex(lanes.LaneError, message):
                    native_baseline.reply_cases(copy)


class EntryDecision(unittest.TestCase):
    """The entry benchmark and the decision it measured."""

    def test_entry_decision_quotes_its_measurements(self) -> None:
        """The table in decision 0002 is the kept run, not numbers typed in."""
        report = json.loads((ROOT / "docs/decisions/0002-measurements.json").read_text())
        text = " ".join((ROOT / "docs/decisions/0002-entry-and-memory.md").read_text().split())
        self.assertEqual(report["status"], "measured")
        micro = {key: value["median"] for key, value in report["micro"].items()}
        rate = {key: f"{round(value['median'], -2):,.0f}" for key, value in report["network"].items()}
        batches = " / ".join(f"{micro[f'loop_reply_batch{k}_ns']:.1f}" for k in (1, 8, 16, 64))
        quoted = [
            f"| an empty crossing of the boundary | {micro['export_nop_ns']:.1f} ns | {micro['loop_nop_ns']:.1f} ns |",
            (f"| one reply, with the host's bookkeeping | {micro['export_reply_ns']:.1f} ns | {batches} ns "
             "for batches of 1 / 8 / 16 / 64 |"),
            *(f"| {label} | {rate[f'export_{n}_rps']} | {rate[f'loop_batch64_{n}_rps']} (batch 64), "
              f"{rate[f'loop_batch1_{n}_rps']} (batch 1) |"
              for label, n in (("requests per second over loopback, 1 connection", 1), ("32 connections", 32),
                               ("128 connections", 128))),
            f"ran at {rate['loop_batch1_repoll_32_rps']} and {rate['loop_batch1_repoll_128_rps']} requests per second",
            f"a load average of {report['load_average_before'][0]:.2f} at the start",
        ]
        for phrase in quoted:
            with self.subTest(phrase=phrase):
                self.assertIn(phrase, text)

    def test_entry_header_is_read_off_the_assembly(self) -> None:
        text = ("x:\n\t.quad 1\ncake_bitmaps:\n\t.quad 4,128\n     .globl y\ny:\ncake_main:\n\n"
                "/* Generated machine code follows */\n\t.byte 0x01,0x02\n\t.byte 0x03\n     .globl z\n")
        self.assertEqual(entry_bench.listed_values(text, "cake_bitmaps:", ".quad"), 2)
        self.assertEqual(entry_bench.listed_values(text, "cake_main:", ".byte"), 3)
        with self.assertRaisesRegex(lanes.LaneError, "exactly one"):
            entry_bench.listed_values(text + "cake_main:\n", "cake_main:", ".byte")


class ParserContract(unittest.TestCase):
    """Reading the parser's tree."""

    def test_parser_contract_reads_the_explore_tree(self) -> None:
        """The parser's tree, brought to the canonical form: chains nested to the right, a shift
        distance in either pinned form, statements as a list, and an unknown form refused."""
        section = """
(func 1 main () (return (Const 0x0)))
(func 1 dn_f ((a : 1) (b : 1))
   (seq (annot "location" "(1:2 1:9)")
      (dec (local 1 x := (Add (Var local a) (Add (Var local b) (Const 0x2)) (Const 0x3)))
         (seq (seq (annot "location" "x") (local x := (Mul (Mul (Var local a) (Var local b)) (Var local x))))
              (seq (annot "location" "y") (mem (Var local a) := byte (Lsr (Var local x) 5)))
              (seq (annot "location" "w") (mem (Var local b) := (Lsr (Var local x) (Const 0x5))))
              (if (NotLess (Var local b) (Var local a)) (seq (annot "location" "z") skip)
                  (return (MemLoadByte (Var local a))))))))
"""
        trees = dict(parser_contract.function(form) for form in parser_contract.forms(section))
        add = ["Add", ["Var", "a"], ["Add", ["Var", "b"], ["Add", ["Const", 2], ["Const", 3]]]]
        mul = ["Mul", ["Var", "a"], ["Mul", ["Var", "b"], ["Var", "x"]]]
        self.assertEqual(trees["dn_f"], {"params": ["a", "b"], "body": [["dec", "x", add, [
            ["assign", "x", mul],
            ["storebyte", ["Var", "a"], ["Lsr", ["Var", "x"], ["Const", 5]]],
            ["store", ["Var", "b"], ["Lsr", ["Var", "x"], ["Const", 5]]],
            ["if", ["NotLess", ["Var", "b"], ["Var", "a"]], [], [["return", ["MemLoadByte", ["Var", "a"]]]]],
        ]]]})
        for unknown in ("(func 1 g () (return (Asr (Var local a) (Const 1))))",
                        "(func 1 g () (return (Var global a)))",
                        "(func 1 g () (tail_call h ()))",
                        "(func 1 g () (return (Mul (Var local a) (Var local b) (Var local c))))"):
            with self.subTest(form=unknown), self.assertRaises(parser_contract.ContractError):
                [parser_contract.function(form) for form in parser_contract.forms(unknown)]

    def test_parser_contract_batches_keep_names_apart(self) -> None:
        """Programs that share a name go to different compilations, and every program to one."""
        programs = [{"name": name, "source": str(i)} for i, name in enumerate("abacab")]
        groups = parser_contract.batches(programs)
        self.assertEqual(sorted(p["source"] for g in groups for p in g), [str(i) for i in range(6)])
        for group in groups:
            names = [p["name"] for p in group]
            self.assertEqual(len(names), len(set(names)))
        self.assertEqual(len(groups), 3)

    def test_parser_contract_batches_keep_within_their_bytes(self) -> None:
        """A group's sources are at most `BATCH_BYTES` together, unless it is one program larger."""
        half = parser_contract.BATCH_BYTES // 2
        programs = [{"name": name, "source": "x" * size}
                    for name, size in (("a", half), ("b", half), ("c", 1), ("d", 3 * half), ("e", half))]
        groups = parser_contract.batches(programs)
        self.assertEqual([[p["name"] for p in g] for g in groups], [["a", "b"], ["c", "e"], ["d"]])


class Generated(unittest.TestCase):
    """The generated-programs lane: its interpreter, types, reducer and planted defects."""

    def test_fuzz_splitmix_is_one_function(self) -> None:
        """The model and the interpreter fill the buffers from the same SplitMix64, and it is the
        published one: its first output from seed 0."""
        samples = json.loads(subprocess.run([str(DN_COMPILER), "fuzz-samples"],
                                            check=True, text=True, capture_output=True).stdout)
        seeds = [0, 1, (1 << 64) - 1]
        self.assertEqual(samples["splitmix"], [[fuzz_interp.splitmix(s, i) for i in range(4)] for s in seeds])
        masks = [(1 << 64) - 1, 0x0707070707070707, 0xFF, 0x8080808080808080, 0]
        self.assertEqual(samples["fill"], [[fuzz_interp.fill_word(7, m, 0, 0), fuzz_interp.fill_word(7, m, 2, 511)]
                                           for m in masks])
        self.assertEqual(fuzz_interp.splitmix(0, 0), 0xE220A8397B1DCDAF)

    def test_fuzz_interpreter_reads_the_source(self) -> None:
        """Signed comparisons, `<=` itself rather than a rewriting of it, little-endian bytes, and
        a fault wherever the semantics has no value."""
        plan: dict[str, Any] = {"params": [{"name": "p", "kind": "pointer", "buffer": 0, "offset": 0},
                                           {"name": "t", "kind": "table"}, {"name": "a", "kind": "data"}],
                                "entries": [[1, 16]]}

        def run(body: list[Any], a: int = 5) -> int:
            program = {"name": "dn_t", "params": ["p", "t", "a"], "body": body}
            result: int = fuzz_interp.run(program, plan, {"data": {"a": a}, "fill": [3, 0]})[0]
            return result

        self.assertEqual(run([["return", ["<=", "a", "a"]]]), 1)
        self.assertEqual(run([["return", ["<", ["-", 0, 1], 0]]]), 1)
        self.assertEqual(run([["return", ["<=", 0, ["-", 0, 1]]]]), 0)
        self.assertEqual(run([["st", "p", 0x0807060504030201], ["return", ["ld8", ["+", "p", 1]]]]), 2)
        self.assertEqual(run([["return", ["lds", 1, "t"]]]), fuzz_interp.buffer_base(1) + 16)
        self.assertEqual(run([["return", [">>>", "a", 1]]]), 2)
        self.assertEqual(run([["return", ["<<", "a", 63]]]), 1 << 63)
        self.assertEqual(run([["return", ["^", "a", 3]]]), 6)
        self.assertEqual(run([["return", ["|", "a", 3]]]), 7)
        # A call binds its arguments to the function's parameters and runs it on locals of its own.
        functions = [{"name": "h0", "params": ["p", "a"], "body": [["st8", "p", "a"], ["return", ["+", "a", 1]]]}]
        called = {**plan, "functions": [{"name": "h0", "params": [plan["params"][0], {"name": "a", "kind": "data"}]}]}
        result, changed, reached = fuzz_interp.run(
            {"name": "dn_t", "params": ["p", "t", "a"],
             "body": [["var", "x0", 7], ["call", "x1", "h0", ["p", "x0"]], ["return", ["+", "x1", "a"]]]},
            called, {"data": {"a": 5}, "fill": [0, 0]}, functions)
        self.assertEqual((result, changed), (13, [[0, 0, 7]]))
        self.assertEqual((reached["call"], reached["pointer passed to a function"]), (1, 1))
        # Its locals are its own: what it declares leaves the caller's alone, and it sees none of them.
        own = [{"name": "h0", "params": ["p", "a"], "body": [["var", "x0", 9], ["set", "a", 2], ["return", "x0"]]}]
        result, _, _ = fuzz_interp.run(
            {"name": "dn_t", "params": ["p", "t", "a"],
             "body": [["var", "x0", 1], ["call", "x1", "h0", ["p", "x0"]], ["return", ["+", ["+", "x0", "x1"], "a"]]]},
            called, {"data": {"a": 5}, "fill": [0, 0]}, own)
        self.assertEqual(result, 1 + 9 + 5)
        twice = {**called, "functions": [{"name": "h0", "params": [{"name": "a", "kind": "data"}] * 2}]}
        wrong: list[tuple[list[Any], dict[str, Any], list[Any]]] = [
            ([["call", "x", "h1", ["p", 1]], ["return", 0]], called, functions),
            ([["call", "x", "h0", ["p"]], ["return", 0]], called, functions),
            ([["call", "x", "h0", ["p", 1]], ["return", 0]], called, [{**functions[0], "body": [["st8", "p", "a"]]}]),
            ([["var", "x0", 1], ["call", "x", "h0", ["p", 1]], ["return", 0]], called,
             [{**functions[0], "body": [["return", "x0"]]}]),
            ([["call", "x", "h0", [1, 2]], ["return", 0]], twice, [{"name": "h0", "params": ["a", "a"],
                                                                   "body": [["return", "a"]]}]),
            ([["return", 0]], called, [{**functions[0], "name": "h1"}]),
        ]
        for body, given_plan, given in wrong:
            with self.subTest(body=body), self.assertRaises(fuzz_interp.Fault):
                fuzz_interp.run({"name": "dn_t", "params": ["p", "t", "a"], "body": body}, given_plan,
                                {"data": {"a": 5}, "fill": [0, 0]}, given)
        for body in ([["return", [">>>", "a", 64]]], [["return", ["<<", "a", 64]]],
                     [["return", ["lds", 1, ["+", "p", 1]]]],
                     [["return", ["ld8", ["+", "p", 4096]]]], [["return", ["ld8", ["-", "p", 1]]]],
                     [["while", 1, []], ["return", 0]], [["st", "t", 0], ["return", 0]]):
            with self.subTest(body=body), self.assertRaises(fuzz_interp.Fault):
                run(body)

    def test_fuzz_a_call_spends_the_clock_in_the_model_and_the_interpreter(self) -> None:
        """A loop iteration and a call each spend one step of the clock: 5,000 iterations, each with
        a call, spend all of it, one more runs out of it."""
        plan = {"params": [], "entries": [], "functions": [{"name": "h0", "params": []}]}
        functions = [{"name": "h0", "params": [], "body": [["return", 0]]}]

        def program(n: int) -> dict[str, Any]:
            return {"name": "dn_t", "params": [], "body": [
                ["var", "i", 0], ["while", ["<", "i", n], [["call", "x", "h0", []], ["set", "i", ["+", "i", 1]]]],
                ["return", "i"]]}

        cases = [{"program": program(n), "functions": functions, "plan": plan,
                  "vectors": [{"data": {}, "fill": [0, 0]}]} for n in (5000, 5001)]
        answers = json.loads(subprocess.run([str(DN_COMPILER), "run-fuzz"], input=json.dumps(cases), check=True,
                                            text=True, capture_output=True).stdout)
        self.assertEqual(answers[0]["vectors"][0]["result"], 5000)
        self.assertIn("does not return", answers[1]["error"])
        self.assertEqual(fuzz_interp.run(program(5000), plan, {"data": {}, "fill": [0, 0]}, functions)[0], 5000)
        with self.assertRaisesRegex(fuzz_interp.Fault, "clock"):
            fuzz_interp.run(program(5001), plan, {"data": {}, "fill": [0, 0]}, functions)

    def test_fuzz_types_refuse_pointer_leaks(self) -> None:
        """A pointer used as a value would make the model's addresses and the host's meet."""
        plan: dict[str, Any] = {"params": [{"name": "p", "kind": "pointer", "buffer": 0, "offset": 0},
                                           {"name": "t", "kind": "table"}, {"name": "a", "kind": "data"}],
                                "entries": [[1, 0]]}

        def check(body: list[Any]) -> Any:
            return fuzz_interp.check_types({"name": "dn_t", "params": ["p", "t", "a"], "body": body}, plan)

        body = [["var", "r", ["+", "p", ["*", ["&", "a", 7], 8]]], ["st8", "r", "a"], ["st8", "p", 1],
                ["return", ["lds", 1, ["lds", 1, "t"]]]]
        check(body)
        # What the calls reach is counted as they run: the pointer local, the offset computed from
        # data, and the first byte of the buffer, which `r`, derived from `p`, reaches when `a & 7`
        # is 0. A local derived from a pointer is that pointer, not a second one.
        for a, first in ((8, 2), (9, 1)):
            _, _, reached = fuzz_interp.run({"name": "dn_t", "params": ["p", "t", "a"], "body": body}, plan,
                                            {"data": {"a": a}, "fill": [0, 0]})
            self.assertEqual((reached["pointer local"], reached["computed address"], reached["pointer from the table"],
                              reached["one byte through two pointers, stored to"], reached["first byte of buffer 0"]),
                             (1, 1, 1, 0, first))
        # Two pointers into one buffer reach the same byte, and one of them stores to it.
        both = {"params": [{"name": "p", "kind": "pointer", "buffer": 0, "offset": 0},
                           {"name": "q", "kind": "pointer", "buffer": 0, "offset": 8}], "entries": []}
        for load, aliased in ((["+", "p", 8], 1), ("p", 0)):
            _, _, reached = fuzz_interp.run({"name": "dn_t", "params": ["p", "q"],
                                             "body": [["st8", "q", 1], ["return", ["ld8", load]]]},
                                            both, {"data": {}, "fill": [0, 0]})
            self.assertEqual(reached["one byte through two pointers, stored to"], aliased)
        leaks: list[list[Any]] = [
            [["return", "p"]], [["st", "p", "p"]], [["return", ["lds", 1, "t"]]], [["return", ["ld8", "t"]]],
            [["set", "a", "p"]], [["return", ["<", "p", "a"]]], [["var", "r", "t"]],
            [["return", ["ld8", ["+", "a", 1]]]]]
        for leak in leaks:
            with self.subTest(body=leak), self.assertRaises(fuzz_interp.TypeViolation):
                check(leak)
        # A call passes a pointer only where the function takes one, and the function is checked too.
        called = {**plan, "functions": [{"name": "h0", "params": [plan["params"][0], {"name": "a", "kind": "data"}]}]}

        def check_call(args: list[Any], body: list[Any]) -> Any:
            return fuzz_interp.check_types(
                {"name": "dn_t", "params": ["p", "t", "a"], "body": [["call", "x", "h0", args], ["return", "x"]]},
                called, [{"name": "h0", "params": ["p", "a"], "body": body}])

        check_call(["p", "a"], [["st8", "p", "a"], ["return", "a"]])
        refused: list[tuple[list[Any], list[Any]]] = [
            (["a", "a"], [["return", "a"]]), (["p", "p"], [["return", "a"]]), (["p", "a"], [["return", "p"]]),
            (["p"], [["return", "a"]])]
        for args, body in refused:
            with self.subTest(args=args, body=body), self.assertRaises(fuzz_interp.TypeViolation):
                check_call(args, body)
        with self.assertRaisesRegex(fuzz_interp.TypeViolation, "different functions"):
            fuzz_interp.check_types({"name": "dn_t", "params": ["p", "t", "a"], "body": [["return", 0]]}, called, [])

    def test_fuzz_the_clock_a_program_may_spend_is_counted_from_its_loops_and_calls(self) -> None:
        """A loop spends its most iterations, each one step and its body's; a call one step and what
        the function spends; a branch the more of its two blocks."""
        functions = [{"name": "h0", "params": [], "body": [
            ["var", "i0", 0], ["while", ["<", "i0", 3], [["set", "i0", ["+", "i0", 1]]]], ["return", 0]]}]
        program = {"name": "dn_t", "params": ["a"], "body": [
            ["var", "i0", 0],
            ["while", ["<", "i0", ["&", "a", 7]], [["call", "x", "h0", []], ["set", "i0", ["+", "i0", 1]]]],
            ["if", "a", [["call", "y", "h0", []]], []], ["return", 0]]}
        self.assertEqual(fuzz_interp.worst_case(program, functions), {"program": 7 * (4 + 1) + 4, "functions": [3]})
        with self.assertRaisesRegex(fuzz_interp.Fault, "does not build"):
            fuzz_interp.worst_case({**program, "body": [["while", "a", []], ["return", 0]]}, [])

    def test_fuzz_replay_refuses_addresses_the_checker_distrusts(self) -> None:
        """A candidate the reducer makes can leave a local in different states on the two sides of a
        branch; CakeML then warns about an address computed from it, so the model's side refuses the
        candidate before it reaches the compiler."""
        plan = {"params": [{"name": "p", "kind": "pointer", "buffer": 0, "offset": 0},
                           {"name": "a", "kind": "data"}], "entries": []}
        body: list[Any] = [
            ["var", "x0", 0],
            ["if", ["<", "a", 5], [["set", "x0", ["lds", 1, "p"]]], [["set", "x0", ["lds", 1, ["+", "p", 8]]]]],
            ["st8", ["+", "p", ["&", "x0", 7]], 1], ["return", 0]]
        one_side = [body[0], ["if", body[1][1], [], body[1][3]], *body[2:]]
        cases = [{"program": {"name": "dn_t", "params": ["p", "a"], "body": b}, "plan": plan,
                  "vectors": [{"data": {"a": 3}, "fill": [1, 255]}]} for b in (body, one_side)]
        answers = json.loads(subprocess.run([str(DN_COMPILER), "run-fuzz"],
                                            input=json.dumps(cases), check=True, text=True,
                                            capture_output=True).stdout)
        self.assertNotIn("error", answers[0])
        self.assertIn("static checker does not trust", answers[1]["error"])

    def test_fuzz_reducer_is_deterministic(self) -> None:
        """The reduction ends at a small case that still fails, the same one every time, and
        never asks about a case that breaks the pointer discipline."""
        plan = {"params": [{"name": "p", "kind": "pointer", "buffer": 0, "offset": 0},
                           {"name": "a", "kind": "data"}, {"name": "b", "kind": "data"}], "entries": []}
        body = [["var", "x", ["+", "a", 7]], ["st8", ["+", "p", 3], "x"],
                ["if", ["<", "x", 9], [["set", "x", ["<=", ["ld8", "p"], "b"]]], [["return", 4]]],
                ["while", ["<", "a", 2], [["set", "a", ["+", "a", 1]]]], ["return", ["*", "x", "b"]]]
        case = {"program": {"name": "dn_t", "params": ["p", "a", "b"], "body": body}, "plan": plan,
                "vector": {"data": {"a": 3, "b": 12345}, "fill": [99, 255]}}
        asked: list[Any] = []

        def fails(cases: list[Any]) -> list[bool]:
            asked.extend(cases)
            return ["<=" in json.dumps(c["program"]["body"]) for c in cases]

        first, stats = fuzz_reduce.reduce(case, fails)
        # The count the corpus records is the count of what was asked, as seen from outside.
        self.assertEqual(stats["asked"], len(asked))
        again, _ = fuzz_reduce.reduce(case, fails)
        self.assertEqual(first, again)
        self.assertEqual(first["program"]["body"], [["var", "x", 0], ["set", "x", ["<=", 0, 0]]])
        self.assertEqual(first["program"]["params"], [])
        self.assertEqual(first["vector"], {"data": {}, "fill": [0, 0]})
        self.assertTrue(all(fuzz_reduce.well_typed(c) for c in asked))

    def test_fuzz_reducer_drops_and_shrinks_what_a_program_calls(self) -> None:
        """A function nothing calls goes, a parameter its body does not use goes with the argument of
        every call, and a call is replaced by a literal or one of its arguments."""
        plan = {"params": [{"name": "a", "kind": "data"}], "entries": [],
                "functions": [{"name": "h0", "params": [{"name": "a", "kind": "data"}, {"name": "b", "kind": "data"}]},
                              {"name": "h1", "params": []}]}
        case = {"program": {"name": "dn_t", "params": ["a"],
                            "body": [["call", "x", "h0", ["a", 5]], ["return", ["<=", "x", 3]]]},
                "functions": [{"name": "h0", "params": ["a", "b"], "body": [["return", ["-", "a", 1]]]},
                              {"name": "h1", "params": [], "body": [["return", 0]]}],
                "plan": plan, "vector": {"data": {"a": 2}, "fill": [0, 0]}}

        def fails(cases: list[Any]) -> list[bool]:
            # The failure lies in the function: it has to be called and subtract from its parameter.
            return [any(s[0] == "call" for s in c["program"]["body"]) and '["-", "a",' in json.dumps(c["functions"])
                    for c in cases]

        small, _ = fuzz_reduce.reduce(case, fails)
        self.assertEqual(small["functions"], [{"name": "h0", "params": ["a"], "body": [["return", ["-", "a", 0]]]}])
        self.assertEqual([p["name"] for p in small["plan"]["functions"][0]["params"]], ["a"])
        self.assertEqual(small["program"]["body"][0], ["call", "x", "h0", [0]])
        self.assertEqual(small["program"]["params"], [])
        self.assertTrue(fuzz_reduce.well_typed(small))
        gone, _ = fuzz_reduce.reduce(case, lambda cases: ["<=" in json.dumps(c["program"]) for c in cases])
        self.assertEqual((gone["functions"], gone["plan"]["functions"]), ([], []))
        self.assertEqual(gone["program"]["body"], [["return", ["<=", 0, 0]]])

    def test_fuzz_programs_read_back_as_they_were_emitted(self) -> None:
        """A program the reducer hands back as data is checked, printed and run exactly as the
        generator's own: the reading of the data is the inverse of its writing."""
        emitted = json.loads(subprocess.run([str(DN_COMPILER), "emit-fuzz", "7", "25", "2"], check=True, text=True,
                                            capture_output=True).stdout)
        self.assertTrue(any(r["functions"] for r in emitted))
        for r in emitted:
            # What the generator counts of the clock is what the program can spend, and no program it
            # draws without calls has a function or a call.
            self.assertEqual(fuzz_interp.worst_case(r["program"], r["functions"]), r["cost"])
            if not r["config"]["calls"]:
                self.assertEqual(r["functions"], [])
                self.assertNotIn('"call"', json.dumps(r["program"]))
        given = [{"program": r["program"], "functions": r["functions"], "plan": r["plan"],
                  "vectors": [{"data": v["data"], "fill": v["fill"]} for v in r["vectors"]]} for r in emitted]
        back = json.loads(subprocess.run([str(DN_COMPILER), "run-fuzz"], input=json.dumps(given), check=True, text=True,
                                         capture_output=True).stdout)
        for before, after in zip(emitted, back, strict=True):
            with self.subTest(program=before["name"]):
                for key in ("name", "plan", "program", "functions", "source", "tree", "vectors"):
                    self.assertEqual(before[key], after[key])
        refused = json.loads(subprocess.run([str(DN_COMPILER), "run-fuzz"], input=json.dumps(
            [{**given[0], "program": {**given[0]["program"], "body": [["return", "nowhere"]]}}]),
            check=True, text=True, capture_output=True).stdout)
        self.assertIn("variable not in scope", refused[0]["error"])

    def test_fuzz_planted_defects_change_what_they_name(self) -> None:
        source = ("export fun dn_t(1 p, 1 a, 1 dn_result) {\n  if a <= 3 {\n    st8 p, ld8 (p + 1);\n"
                  "    st dn_result, (a) >>> 63;\n    return 0;\n  } else {\n    st dn_result, (a) >>> 5;\n"
                  "    st dn_result, (a ^ 1) << 2;\n    return 0;\n  }\n}\n")
        mutants = native_fuzz.MUTANTS
        self.assertIn("if a < 3 {", mutants["le-as-lt"](source))
        self.assertIn("    st p, ld8", mutants["st8-as-st"](source))
        self.assertIn("st8 p, lds 1 (p + 1)", mutants["ld8-as-lds"](source))
        self.assertIn("if (a <= 3) == 0 {", mutants["if-negated"](source))
        self.assertIn(">>> 62;", mutants["shift-off-by-one"](source))
        self.assertIn(">>> 6;", mutants["shift-off-by-one"](source))
        self.assertIn("(a | 1) << 2;", mutants["xor-as-or"](source))
        self.assertIn("(a ^ 1) >>> 2;", mutants["shl-as-shr"](source))
        called = "fun dn_t_h0(1 p, 1 a, 1 b) {\n  return a;\n}\n\n" + source.replace(
            "  if a <= 3 {\n", "  var x0 = dn_t_h0(p, a, 3);\n  var x1 = dn_t_h1(p, a);\n  if a <= 3 {\n")
        swapped = mutants["call-args-swapped"](called + "  var x2 = dn_t_h2();\n")
        self.assertIn("var x0 = dn_t_h0(p, 3, a);", swapped)
        self.assertIn("var x1 = dn_t_h1(p, a);", swapped)
        self.assertIn("var x2 = dn_t_h2();", swapped)
        source = called
        for name, mutant in mutants.items():
            with self.subTest(mutant=name):
                changed = [a != b for a, b in zip(source.splitlines(), mutant(source).splitlines(), strict=True)]
                self.assertTrue(any(changed))

    def test_fuzz_the_corpus_is_recorded_for_the_defects_named(self) -> None:
        parsed = [native_fuzz.arguments().parse_args(given).write_corpus
                  for given in ([], ["--write-corpus"], ["--write-corpus", "le-as-lt", "call-args-swapped"])]
        self.assertEqual([native_fuzz.to_write(p) for p in parsed],
                         [set(), set(native_fuzz.MUTANTS), {"le-as-lt", "call-args-swapped"}])
        with contextlib.redirect_stderr(io.StringIO()), self.assertRaises(SystemExit):
            native_fuzz.arguments().parse_args(["--write-corpus", "no-such-defect"])


class StandIn:
    """A `native_fuzz.Native` that compiles nothing: each function answers as `answers` says, and a
    batch holding a function named in `warns` draws a diagnostic."""

    def __init__(self, answers: dict[str, Any], warns: frozenset[str] = frozenset()) -> None:
        self.answers, self.warns = answers, warns
        self.built: list[list[str]] = []
        self.sources: list[tuple[str, str, int]] = []

    def build(self, name: str, sources: list[tuple[str, str, int]], *, symbols: bool = False) -> Path:
        del symbols
        self.built.append([fn for _, fn, _ in sources])
        if any(fn in self.warns for _, fn, _ in sources):
            raise lanes.Diagnostics(f"{name}.pnk compiled with diagnostics")
        self.sources = sources
        return Path(name)

    def run(self, binary: Path, lines: list[str]) -> list[Any]:
        del binary
        return [self.answers[self.sources[int(line.split()[0])][1]] for line in lines]


def record(name: str, result: int, program: dict[str, Any] | None = None) -> dict[str, Any]:
    source = f"export fun {name}() {{}}\n"
    return {"name": name, "source": source, "tree": {"name": name, "source": source},
            "program": program or {"name": name, "params": [], "body": [["return", result]]}, "functions": [],
            "plan": {"params": [], "entries": []},
            "vectors": [{"data": {}, "fill": [0, 0], "result": result, "changed": []}]}


class GeneratedOnStandIns(unittest.TestCase):
    """The branches of the generated-programs lane a run on the standard seed never takes."""

    def test_a_batch_the_compiler_warns_about_is_judged_one_by_one(self) -> None:
        records = [record("dn_a", 5), record("dn_b", 5), record("dn_c", 5)]
        native = StandIn({"dn_a": (0, 6, []), "dn_b": (0, 6, []), "dn_c": (0, 5, [])}, frozenset({"dn_b"}))
        together = native_fuzz.native_verdicts(native, records, None)
        self.assertEqual(native.built[0], ["dn_a", "dn_b", "dn_c"])
        alone = [native_fuzz.native_verdicts(native, [r], None)[0] for r in records]
        # The warned-about candidate does not count as failing; the others keep their verdicts.
        self.assertEqual(together, [True, False, False])
        self.assertEqual(together, alone)

    def test_a_found_case_that_disagrees_again_is_refused(self) -> None:
        kept = record("dn_min", 7)
        case = {"name": "kept", "program": kept["program"], "functions": [], "plan": kept["plan"],
                "input": {"data": {}, "fill": [0, 0]}, "model": {"result": 7, "changed": []}}
        with tempfile.TemporaryDirectory() as temp:
            mutants, found = Path(temp) / "mutants", Path(temp) / "found"
            mutants.mkdir()
            found.mkdir()
            (found / "kept.json").write_text(json.dumps(case))
            held = {"mutants": [], "found": [case]}
            with mock.patch.multiple(native_fuzz, MUTANT_CASES=mutants, FOUND_CASES=found, MUTANTS={},
                                     dn=lambda *_, **__: held, replay=lambda _: [kept]):
                self.assertEqual(native_fuzz.check_corpus(StandIn({"dn_min": (0, 7, [])})),
                                 {"mutants": 0, "found": 1})
                with self.assertRaisesRegex(lanes.LaneError, "disagrees again on the found case dn_min"):
                    native_fuzz.check_corpus(StandIn({"dn_min": (0, 8, [])}))

    def test_a_disagreement_is_kept_as_the_kind_it_is(self) -> None:
        program = {"name": "dn_t", "params": ["a"],
                   "body": [["var", "x", ["+", "a", 1]], ["return", ["<=", "x", 3]]]}
        case = {"program": program, "plan": {"params": [{"name": "a", "kind": "data"}], "entries": []},
                "vector": {"data": {"a": 2}, "fill": [0, 0]}}

        def replay(cases: list[dict[str, Any]]) -> list[dict[str, Any]]:
            # A model that answers one more than the interpreter.
            out = []
            for c in cases:
                vector = c["vectors"][0]
                result, changed, _ = fuzz_interp.run(c["program"], c["plan"], vector)
                out.append({**record(c["program"]["name"], result + 1, c["program"]), "plan": c["plan"],
                            "vectors": [{**vector, "result": result + 1, "changed": changed}]})
            return out

        def runs(cases: list[dict[str, Any]]) -> list[bool]:
            # The reducer's question here: does the candidate still run to a return.
            verdicts = []
            for c in cases:
                try:
                    fuzz_interp.run(c["program"], c["plan"], c["vector"])
                    verdicts.append(True)
                except fuzz_interp.Fault:
                    verdicts.append(False)
            return verdicts

        def misread(*_: Any, **__: Any) -> int:
            raise parser_contract.ContractError("dn_min: the parser's tree is not the lowered one")

        sides: dict[str, tuple[dict[str, Any], str, Any]] = {
            "native": ({"native": StandIn({"dn_min": "fault"})}, "native", "fault"),
            "model": ({}, "interpreter", "the model and the interpreter disagree"),
            "parser": ({"cake": "cake"}, "parser", "is not the lowered one"),
        }
        with (tempfile.TemporaryDirectory() as temp, mock.patch.multiple(native_fuzz, OUT=Path(temp), replay=replay),
              mock.patch.object(native_fuzz.contract, "compare", misread)):
            for kind, (side, field, said) in sides.items():
                with self.subTest(kind=kind):
                    told = native_fuzz.minimized(kind, case, runs, {"seed": 1}, **side)
                    self.assertIn(f"build/fuzz/minimized/{kind}.json", told)
                    kept = json.loads((Path(temp) / "minimized" / f"{kind}.json").read_text())
                    self.assertEqual((kept["kind"], kept["name"], kept["origin"]), (kind, "disagreement", {"seed": 1}))
                    self.assertIn(said, str(kept[field]))

    def test_the_contract_takes_runs_within_its_bytes(self) -> None:
        """Every record goes to one run, in order; a run stays within the limit unless it is one
        record alone, and is cut only where the next record would take it past."""
        records = [{"tree": {"source": "x" * n}} for n in (3, 4, 2, 9, 1, 1, 5)]
        runs = native_fuzz.runs_within(records, 7)
        self.assertEqual([(k, [len(r["tree"]["source"]) for r in run]) for k, run in runs],
                         [(0, [3, 4]), (2, [2]), (3, [9]), (4, [1, 1, 5])])
        first = native_fuzz.runs_within([{"tree": {"source": "x" * n}} for n in (9, 1)], 7)
        self.assertEqual([(k, len(run)) for k, run in first], [(0, 1), (1, 1)])
        self.assertEqual(native_fuzz.runs_within([], 7), [])

    def test_a_batch_the_parser_refuses_but_no_program_alone_is_reported(self) -> None:
        """The run that fails is named by the programs in it, past the runs before it."""
        records = [record(f"dn_{i}", 1 + i % 2) for i in range(4)]
        tags: list[str] = []

        def compare(cake: str, trees: list[dict[str, Any]], tag: str, **_: Any) -> int:
            del cake
            tags.append(tag)
            if len(trees) > 1 and trees[0]["name"] == "dn_2":
                raise parser_contract.ContractError("dn_2: the parser's tree is not the lowered one")
            return len(trees)

        def replay(cases: list[dict[str, Any]]) -> list[dict[str, Any]]:
            return [record(c["program"]["name"], 1) for c in cases]

        two = 2 * len(records[0]["tree"]["source"])
        with (mock.patch.object(native_fuzz.contract, "compare", compare),
              mock.patch.multiple(native_fuzz, replay=replay, CONTRACT_BYTES=two),
              self.assertRaisesRegex(lanes.LaneError, "programs 2-3 together and on none alone")):
            native_fuzz.parsed_as_lowered("cake", records, {})
        self.assertEqual(tags[:2], ["fuzz-0", "fuzz-2"])

    def test_the_contract_is_held_in_the_lanes_own_directory(self) -> None:
        """The nightly run starts this lane on an empty build/, with no other lane before it: what
        the parser compiles, for the run, for the reducer and for a kept case, goes under the lane's
        own directory, made when missing, and the parser lane's directory is not touched."""
        tree = {"name": "dn_0", "source": "export fun dn_0() {\n  return 1;\n}\n", "params": [],
                "body": [["return", ["Const", 1]]]}
        case = {"program": {"name": "dn_0", "params": [], "body": [["return", 1]]},
                "plan": {"params": [], "entries": []}, "vector": {"data": {}, "fill": [0, 0]}}

        def replay(cases: list[dict[str, Any]]) -> list[dict[str, Any]]:
            # The stand-in parser below reads only dn_0, so these renamed programs disagree with it.
            return [{"name": c["program"]["name"], "source": tree["source"],
                     "tree": {**tree, "name": c["program"]["name"]}, "program": c["program"], "functions": [],
                     "plan": c["plan"],
                     "vectors": [{**c["vectors"][0], "result": 1, "changed": []}]} for c in cases]

        with tempfile.TemporaryDirectory() as temp:
            cake = Path(temp) / "cake"
            cake.write_text("#!/bin/sh\ncat > /dev/null\nprintf '%s\\n' '# initial pancake program' "
                            "'(func 1 main () (return (Const 0x0)))' '(func 1 dn_0 () (return (Const 0x1)))'\n")
            cake.chmod(0o755)
            fuzz, parser = Path(temp) / "fuzz", Path(temp) / "parser"
            with (mock.patch.multiple(native_fuzz, OUT=fuzz, replay=replay),
                  mock.patch.object(native_fuzz.contract, "OUT", parser)):
                self.assertEqual(native_fuzz.parsed_as_lowered(str(cake), [{"name": "dn_0", "tree": tree}], {}), 1)
                self.assertEqual(native_fuzz.parser_failure(str(cake))([case]), [True])
                kept = native_fuzz.fixture("parser", "p", case, case, {}, {"asked": 1}, cake=str(cake))
            self.assertIn("nobody printed", kept["parser"])
            self.assertEqual(sorted(p.name for p in (fuzz / "parser").iterdir()),
                             ["fixture-0.pnk", "fuzz-0-0.pnk", "reduce-0.pnk"])
            self.assertFalse(parser.exists())


class Lanes(unittest.TestCase):
    """What every native lane shares: how it ends and what its report says."""

    def test_a_lane_ends_with_its_reason_or_its_report(self) -> None:
        with tempfile.TemporaryDirectory() as temp:
            out, cake = Path(temp), Path(temp) / "cake"
            cake.write_text("compiler")
            (out / "report.json").write_text("{}")

            def refuse() -> Any:
                raise lanes.LaneError("the check refused")

            with self.assertRaises(SystemExit) as ended:
                lanes.lane_main("PROBE", out, refuse)
            self.assertEqual(str(ended.exception.code), "DN PROBE: the check refused")
            # One line, not a traceback with the refusal as its cause.
            self.assertTrue(ended.exception.__suppress_context__)
            self.assertFalse((out / "report.json").exists())
            # A defect of the lane itself keeps its traceback.
            with self.assertRaises(ValueError):
                lanes.lane_main("PROBE", out, lambda: int("x"))
            printed = io.StringIO()
            host = ROOT / "native/host.h"
            with contextlib.redirect_stdout(printed):
                lanes.lane_main("PROBE", out, lambda: lanes.Report("matched", str(cake), [host], {"count": 3},
                                                                   printed_by_dn_compiler=False))
            report = json.loads((out / "report.json").read_text())
            self.assertEqual(json.loads(printed.getvalue()), report)
            self.assertEqual({k: report[k] for k in ("status", "cake_sha256", "dn_compiler_sha256", "count")},
                             {"status": "matched", "cake_sha256": lanes.digest(cake), "dn_compiler_sha256": None,
                              "count": 3})
            self.assertEqual(report["host_sha256"], {"native/host.h": lanes.digest(host)})
            self.assertIn("seconds", report)
            self.assertIn("platform", report)

    def test_documents_have_to_say_what_the_run_measured(self) -> None:
        """Run alone, a lane holds the documents to what it measured; under `scripts/once.py` it
        leaves the requirement for `scripts/check_documents.py`, which holds them to it."""
        with mock.patch.dict(os.environ):
            os.environ.pop("DN_DOCUMENTED", None)
            lanes.require_quoted({"README.md": ("dn-compiler",)})
            with self.assertRaisesRegex(lanes.LaneError, "README.md does not say 'no such phrase'"):
                lanes.require_quoted({"README.md": ("no such phrase",)})
            with self.assertRaisesRegex(lanes.LaneError, "states otherwise than measured: 'cases': none, not 3"):
                lanes.require_stated([("README.md", [("# dn", "## ")], {"cases": "3"})])
        with tempfile.TemporaryDirectory() as temp:
            later = Path(temp) / "documented"
            with mock.patch.dict(os.environ, {"DN_DOCUMENTED": str(later)}):
                lanes.require_quoted({"README.md": ("no such phrase",)})
            [requirement] = [json.loads(line) for line in later.read_text().splitlines()]
            self.assertEqual(lanes.unheld(requirement), ["README.md does not say 'no such phrase'"])
