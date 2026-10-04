# SPDX-License-Identifier: AGPL-3.0-or-later
"""The proof audit, the independent kernel and the Lean source gate, on probe modules compiled into
a disposable copy of the built library; the working tree is never modified."""
from __future__ import annotations

import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import tempfile
import unittest

from gatekit import ROOT, regressions, run, script, sha256, source_tree, tool

structure = script("check_structure")

AUDIT_PROBES = {
    "Foreign": "axiom Foreign.bad : False\naxiom Foreign.p : Prop\n",
    "DN.Probe.Transitive": (
        "import Foreign\nnamespace DN.Probe\ntheorem transitive : False := Foreign.bad\n"
        "noncomputable def isolated : Nat := False.elim Foreign.bad\n"
        "inductive Wrap | mk : Foreign.p → Wrap\ndef viaCtor (_ : Wrap) : Nat := 0\nend DN.Probe\n"),
    "DN.Probe.PrivateAxiom": (
        "namespace DN.Probe\nprivate axiom hidden : False\n"
        "theorem viaPrivate : (1 : Nat) = 2 := hidden.elim\nend DN.Probe\n"),
    "DN.Probe.TopLevel": "axiom topBad : False\ndef topUse : Nat := topBad.elim\n",
    "DN.Probe.Sorry": "theorem DN.Probe.gap : (1 : Nat) = 2 := sorry\n",
    "DN.Probe.Native": "theorem DN.Probe.native : 10 + 10 = 20 := by native_decide\n",
    "DN.Probe.ImplementedBy": (
        "def DN.Probe.fast (n : Nat) : Nat := n + 1\n"
        "@[implemented_by DN.Probe.fast] def DN.Probe.slow (n : Nat) : Nat := n\n"),
    "DN.Probe.Extern": '@[extern "dn_probe_ext"] opaque DN.Probe.ext : Nat → Nat\n',
    "DN.Probe.Partial": "partial def DN.Probe.spin (n : Nat) : Nat := DN.Probe.spin n\n",
    "DN.Probe.Unsafe": "unsafe def DN.Probe.raw : Nat := 0\n",
    # A condition of one's own making, assumed by a theorem and satisfied by
    # nothing: the theorem may be true only because its premise is empty.
    "DN.Probe.NoWitness": (
        "namespace DN.Probe\ndef Impossible (n : Nat) : Prop := n < n\n"
        "theorem fromImpossible (n : Nat) (h : Impossible n) : n = n := rfl\nend DN.Probe\n"),
    "DN.Probe.Initializers": "initialize DN.Probe.counter : Nat ← pure 1\ninitialize pure ()\n",
    "DN.Probe.CompilerHooks": (
        "namespace DN.Probe\ndef slowId (n : Nat) : Nat := n\ndef fastId (n : Nat) : Nat := n\n"
        "@[csimp] theorem slowId_eq : @slowId = @fastId := rfl\n"
        "@[export dn_probe_exported] def exported (n : Nat) : Nat := n\nend DN.Probe\n"),
    "DN.Probe.Helper": (
        "namespace DN.Probe\nunsafe def spoof._unsafe_rec : Nat := 42\ndef spoof : Nat := 0\n"
        "def plain._unsafe_rec : Nat := 42\ndef plain : Nat := 0\nend DN.Probe\n"),
    "DN.Probe.MetaImport": "import Lean.Elab\n",
    "DN.Probe.Mistyped": (
        "def DN.Probe.regression_9002 : Nat := 1\ndef DN.Probe.regression_9004 : Bool := false\n"
        "def DN.Probe.regression_9008 : Nat → Bool := fun _ => true\n"
        "def DN.Probe.regression_9009 : Unit → Nat := fun _ => 0\n"),
    "DN.Probe.Regressions": (
        "namespace DN.Probe\ndef count : Nat → Nat\n  | 0 => 0\n  | n + 1 => count n + 1\n"
        "def le_succ : (n : Nat) → n ≤ n + 1\n  | 0 => Nat.le_succ 0\n"
        "  | n + 1 => Nat.succ_le_succ (le_succ n)\n"
        "def regression_9001 : Bool := false\nprivate def regression_9003 : Bool := count 3 == 3\n"
        "noncomputable def regression_9005 : Bool := Classical.choice ⟨true⟩\n"
        "def regression_9006 (_ : Unit) : Bool := count 2 == 2\ndef regression_9007 (_ : Unit) : Bool := false\n"
        "end DN.Probe\n"),
    "DN.Probe.NoTheorems": "def DN.Probe.value : Nat := 1\n",
    "DN.Probe.PartialDef": (
        "import Lean\nopen Lean\nrun_cmd Elab.Command.liftCoreM do\n  addDecl <| .defnDecl\n"
        "    { name := `DN.Probe.loop, levelParams := [], type := mkConst ``Nat,\n"
        "      value := mkNatLit 0, hints := .opaque, safety := .partial }\n"),
    "DN.Probe.CopyA": "theorem DN.Probe.copied : 2 + 2 = 4 := rfl\n",
    "DN.Probe.CopyB": "theorem DN.Probe.copied : 2 + 2 = 4 := sorry\n",
    "DN.Probe.SkipKernel": (
        "import Lean\nopen Lean Elab Command\n"
        'elab "add_unchecked" : command => do\n'
        "  let decl := Declaration.thmDecl\n"
        "    { name := `DN.Probe.bad, levelParams := [], type := mkConst ``False,\n"
        "      value := mkConst ``True.intro }\n"
        "  liftCoreM (addDecl decl)\n"
        "set_option debug.skipKernelTC true in\nadd_unchecked\n"),
}
# Probes for the export to the independent kernel.
KERNEL_PROBES = {
    "DN.Probe.Kernel": (
        "namespace DN.Probe\ninductive Token | a | b (n : Nat) | c | d | e | f | g | h | i | j | k | l\n"
        "  deriving DecidableEq\n"
        "private theorem hidden : Token.a ≠ Token.b 0 := by decide\n"
        "def halve (n : Nat) : Nat := if h : n = 0 then 0 else halve (n / 2)\n"
        "termination_by n\ndecreasing_by omega\n"
        "theorem halve_zero : halve 0 = 0 := by rw [halve]; simp\nend DN.Probe\n"),
    "DN.Probe.Unwritable": (
        "import Lean\nopen Lean\nrun_cmd Elab.Command.liftCoreM do\n  addDecl <| .defnDecl\n"
        '    { name := .str `DN.Probe "a»b", levelParams := [], type := mkConst ``Nat,\n'
        "      value := mkNatLit 0, hints := .abbrev, safety := .safe }\n"),
    "DN.Probe.NulName": (
        "import Lean\nopen Lean\nrun_cmd Elab.Command.liftCoreM do\n  addDecl <| .defnDecl\n"
        '    { name := .str `DN.Probe "a\\x00--export-unsafe\\x00b", levelParams := [], type := mkConst ``Nat,\n'
        "      value := mkNatLit 0, hints := .abbrev, safety := .safe }\n"),
    "DN.Compiler.Main": "import DN.Probe.Extra\ndef DN.Compiler.Main.value : Nat := DN.Probe.Extra.x\n",
    "DN.Probe.Extra": "def DN.Probe.Extra.x : Nat := 1\n",
    "DN.Probe.Lookalike": (
        "axiom «Quot.sound» : False\ntheorem DN.Probe.lookalike : (1 : Nat) = 2 := «Quot.sound».elim\n"),
    "DN.Probe.EmptyPrefix": (
        "import Lean\nopen Lean\nrun_cmd Elab.Command.liftCoreM do\n  addDecl <| .axiomDecl\n"
        '    { name := .str (.str .anonymous "") "propext", levelParams := [], type := mkConst ``False,\n'
        "      isUnsafe := false }\n"),
}
PROBES = AUDIT_PROBES | KERNEL_PROBES
UNSOUND = [
    "DN.Probe.transitive depends on Foreign.bad",
    "DN.Probe.isolated depends on Foreign.bad",
    "DN.Probe.viaCtor depends on Foreign.p",
    "axiom declared: _private.DN.Probe.PrivateAxiom",
    "DN.Probe.viaPrivate depends on",
    "axiom declared: topBad",
    "topUse depends on topBad",
    "DN.Probe.gap depends on sorryAx",
    "DN.Probe.native depends on DN.Probe.native._native.native_decide",
    "implemented_by DN.Probe.fast: DN.Probe.slow",
    "extern declaration: DN.Probe.ext",
    "partial definition: DN.Probe.spin",
    "premise without a witness: DN.Probe.Impossible",
    "unsafe declaration: DN.Probe.raw",
    "csimp theorem: DN.Probe.slowId_eq",
    "initializer: DN.Probe.counter",
    "initializer: initFn._@.DN.Probe.Initializers",
    "export dn_probe_exported: DN.Probe.exported",
    "hand-written recursion helper: DN.Probe.spoof._unsafe_rec",
    "hand-written recursion helper: DN.Probe.plain._unsafe_rec",
    "DN.Probe.MetaImport imports Lean.Elab",
    "regression is not a Bool or Unit → Bool definition: DN.Probe.regression_9002",
    "regression is not a Bool or Unit → Bool definition: DN.Probe.regression_9008",
    "regression is not a Bool or Unit → Bool definition: DN.Probe.regression_9009",
    "partial definition: DN.Probe.loop",
    "stores another version of DN.Probe.copied",
]

ALLOWED = """\
/-! Module doc mentioning #eval, run_cmd and @[init]. -/
namespace DN.Probe.Allowed
-- #eval 1
/- /- #eval 1 -/ initialize -/
/-- Docstring with `#eval` and `unsafe`. -/
def two : Nat := 2
def s : String := "#eval \\" run_cmd"
def r : String := r#"#eval "quoted""#
def c : Char := '#'
def q : Char := '"'
def i : String := s!"{two} and {"nested"}"
theorem h' : True := trivial
@[simp] theorem u : two = 2 := rfl
@[inline] def inl (n : Nat) : Nat := n
@[reducible] def red : Nat := 1
@[irreducible] def irr : Nat := 1
attribute [local simp] red
set_option maxHeartbeats 400000 in
theorem v : True := trivial
set_option maxRecDepth 1000 in
theorem w : True := trivial
section
variable (n : Nat)
universe v
def idn : Nat := n
end
mutual
def even : Nat → Bool
  | 0 => true
  | n + 1 => odd n
def odd : Nat → Bool
  | 0 => false
  | n + 1 => even n
end
open Nat in
theorem z : succ 0 = 1 := rfl
section
variable [DecidableEq Nat]
omit [DecidableEq Nat] in
theorem om : True := trivial
end
example : two + 0 = 2 := by simp +arith [two]
end DN.Probe.Allowed
"""
PINNED = """\
namespace DN.Probe.Pinned
macro "probe_tac" : tactic => `(tactic| trivial)
syntax "probe_term" : term
macro_rules | `(probe_term) => `(1)
notation "probe_one" => 1
infixl:65 " +++ " => Nat.add
theorem uses : probe_one +++ probe_term = 2 := rfl
end DN.Probe.Pinned
"""
EVAL = "command `Lean.Parser.Command.eval` is not allowed"
# Module name -> (source, expected message); `None` means the module must pass.
GATE_PROBES: dict[str, tuple[str, str | None]] = {
    "Eval": ('#eval IO.FS.writeFile "{marker}" ""\n', EVAL),
    "ConfigTerm": (('example : True := by\n  simp (maxSteps := if (unsafeIO (IO.FS.writeFile '
                    '"{marker}" "")).isOk then 1000 else 999) <;> trivial\n'),
                   "`Lean.Parser.Tactic.valConfigItem` runs code"),
    "RunCmd": ("run_cmd pure ()\n", "command `Lean.runCmd` is not allowed"),
    "Initialize": ("initialize pure ()\n", "command `Lean.Parser.Command.initialize` is not allowed"),
    "NestedEval": ("open Nat in\n#eval 1\n", EVAL),
    "Macro": ('macro "m" : term => `(1)\n',
              "syntax definition `Lean.Parser.Command.macro` outside the reviewed syntax files"),
    "ByElab": ("def f : Nat := by_elab return Lean.mkNatLit 1\n", "`Lean.byElab` runs code"),
    "RunTac": ("example : True := by run_tac pure ()\n", "`Lean.Parser.Tactic.runTac` runs code"),
    "IncludeStr": ('def s : String := include_str "x.txt"\n', "`Lean.includeStr` runs code"),
    "Idbg": ("def f (n : Nat) : Nat := idbg n; n\n", "`Lean.Parser.Term.idbg` runs code"),
    "UnsafeDef": ("unsafe def f : Nat := 0\n", "unsafe code is not allowed"),
    "UnsafeTerm": ("def f : Nat := unsafe 0\n", "unsafe code is not allowed"),
    "InitAttr": ("@[init] def f : IO Unit := pure ()\n", "attribute `init` is not allowed"),
    "ExternAttr": ('@[extern "c_f"] opaque f : Nat → Nat\n', "attribute `extern` is not allowed"),
    "ImplementedBy": ("def g : Nat := 1\n@[implemented_by g] def f : Nat := 0\n",
                      "attribute `implemented_by` is not allowed"),
    "AttributeCmd": ("def f : Nat := 0\nattribute [local instance] f\n",
                     "attribute `instance` is not allowed"),
    "Option": ("set_option debug.skipKernelTC true in\ntheorem t : True := trivial\n",
               "option `debug.skipKernelTC` is not allowed"),
    "TermOption": ("def x : Nat := set_option pp.all true in 1\n", "option `pp.all` is not allowed"),
    "TacticOption": ("example : True := by set_option trace.Meta.synthInstance true in trivial\n",
                     "option `trace.Meta.synthInstance` is not allowed"),
    "Import": ("import Lean\n", "import of Lean is not allowed"),
    "EscapedImport": ("import «Lean».«Elab»\n", "import of Lean.Elab is not allowed"),
    "ParseError": ("def := 1\n", "unexpected token"),
    "ElabError": ('def f : Nat := "x"\n', "error"),
    "QuoteIdent": ('def «q"» : Nat := 1\n#eval 1\n-- "\n', EVAL),
    "CommentIdent": ("def «/-» : Nat := 1\n#eval 1\n-- -/\n", EVAL),
    "Interpolation": ('def s : String := s!"{\'"\'}"\n#eval 1\n-- "\n', EVAL),
    "ImportsFailed": ("import DN.Probe.Eval\n", "not checked, it imports a module that failed"),
    "PinnedElab": ('elab "e" : term => return Lean.mkNatLit 1\n',
                   "command `Lean.Parser.Command.elab` is not allowed"),
    "Allowed": (ALLOWED, None),
    "UsesAllowed": ("import «DN».Probe.«Allowed»\nexample : DN.Probe.Allowed.two = 2 := rfl\n", None),
    "Pinned": (PINNED, None),
    "ModuleA": ("module\n\npublic def DN.Probe.ModuleA.a : Nat := 1\n", None),
    "ModuleB": (("module\n\npublic import DN.Probe.ModuleA\n\npublic def DN.Probe.ModuleB.b : Nat := "
                 "DN.Probe.ModuleA.a\n"), None),
    "UsesPinned": (("import DN.Probe.Pinned\nexample : True := by probe_tac\n"
                    "example : probe_term = probe_one := rfl\n"), None),
}




class Probes:
    """Compile probe modules into a disposable copy of the built library."""

    def __init__(self, directory: Path, modules: list[str]) -> None:
        self.src, self.lib = directory / "src", directory / "lib"
        shutil.copytree(ROOT / ".lake/build/lib/lean", self.lib)
        self.env = {**os.environ, "LEAN_PATH": str(self.lib)}
        for module in modules:
            relative = Path(*module.split("."))
            source = (self.src / relative).with_suffix(".lean")
            source.parent.mkdir(parents=True, exist_ok=True)
            source.write_text(PROBES[module])
            olean = (self.lib / relative).with_suffix(".olean")
            olean.parent.mkdir(parents=True, exist_ok=True)
            result = run(["lean", f"--root={self.src}", "-o", str(olean), str(source)], env=self.env)
            if result.returncode != 0:
                raise AssertionError(f"probe {module} failed to compile:\n{result.stdout}{result.stderr}")

    def audit(self, roots: tuple[str, ...] = ("lean",)) -> subprocess.CompletedProcess[str]:
        flags = [arg for root in (*roots, str(self.src)) for arg in ("--root", root)]
        return run(["lean", "--run", "scripts/Audit.lean", "--regressions", regressions(), *flags],
                   env=self.env)




class Audit(unittest.TestCase):
    """The proof audit: what it rejects, what it counts, and what it pins."""

    def test_rejects_every_escape(self) -> None:
        with tempfile.TemporaryDirectory() as temp:
            unsound = [m for m in AUDIT_PROBES
                       if m not in ("DN.Probe.SkipKernel", "DN.Probe.Regressions", "DN.Probe.NoTheorems")]
            result = Probes(Path(temp), unsound).audit()
            self.assertEqual(result.returncode, 1, result.stderr)
            for expected in UNSOUND:
                self.assertIn(expected, result.stderr)
            self.assertNotIn("regression failed", result.stderr)
            self.assertNotIn("regressions passed", result.stdout)

    def test_runs_and_counts_regressions(self) -> None:
        with tempfile.TemporaryDirectory() as temp:
            result = Probes(Path(temp), ["DN.Probe.Regressions"]).audit()
            self.assertEqual(result.returncode, 1, result.stderr)
            self.assertIn("regression failed: DN.Probe.regression_9001", result.stderr)
            self.assertIn("regression could not run: DN.Probe.regression_9005", result.stderr)
            self.assertIn("regression failed: DN.Probe.regression_9007", result.stderr)
            self.assertIn(f"expected {regressions()} passing regressions, found {int(regressions()) + 2}",
                          result.stderr)

    def test_documented_counts_match_the_audit(self) -> None:
        prefix = run(["lean", "--print-prefix"]).stdout.strip()
        env = {**os.environ, "LEAN_PATH": f"{prefix}/lib/lean:{ROOT}/.lake/build/lib/lean"}
        result = run(["lean", "--run", "scripts/Audit.lean", "--regressions", regressions()], env=env)
        self.assertEqual(result.returncode, 0, result.stderr)
        counts = re.search(r"(\d+) modules, (\d+) declarations, (\d+) theorems checked, "
                           r"(\d+) recursion helpers", result.stdout)
        assert counts is not None, result.stdout
        declarations, theorems, helpers = (f"{int(counts.group(index)):,}" for index in (2, 3, 4))
        documented = {
            "docs/assurance.md": (f"audit covers {declarations} declarations, including {theorems} theorems",
                                  f"| {regressions()} executable examples |"),
            "docs/baseline.md": (f"{declarations} declarations, including {theorems} theorems",
                                 f"the kernels skip the {helpers} `_unsafe_rec` helpers",
                                 f"| {regressions()} executable cases |"),
        }
        for name, expected in documented.items():
            with self.subTest(document=name):
                text = (ROOT / name).read_text()
                for phrase in expected:
                    self.assertIn(phrase, text)

    def test_requires_theorems(self) -> None:
        with tempfile.TemporaryDirectory() as temp:
            result = Probes(Path(temp), ["DN.Probe.NoTheorems"]).audit(roots=())
            self.assertEqual(result.returncode, 1, result.stderr)
            self.assertIn("no theorems found", result.stderr)

    def test_requires_regression_count(self) -> None:
        for args in ([], ["--regressions", "1", "--export-list"]):
            with self.subTest(args=args):
                result = run(["lean", "--run", "scripts/Audit.lean", *args])
                self.assertEqual(result.returncode, 2, result.stderr)
                self.assertIn("usage", result.stderr)

    def test_compiler_imports_are_pinned(self) -> None:
        with tempfile.TemporaryDirectory() as temp:
            result = Probes(Path(temp), ["DN.Probe.Extra", "DN.Compiler.Main"]).audit(roots=())
            self.assertEqual(result.returncode, 1, result.stderr)
            self.assertIn("dn-compiler now also needs DN.Probe.Extra; review that and update "
                          "compilerModules", result.stderr)

    def test_rejects_build_output_without_a_source(self) -> None:
        with tempfile.TemporaryDirectory() as temp:
            root = source_tree(Path(temp))
            built = root / ".lake/build/lib/lean/DN/Compiler"
            built.mkdir(parents=True)
            (root / "lean/DN/Compiler").mkdir(parents=True)
            (root / "lean/DN/Compiler/Kept.lean").write_text("def x : Nat := 1\n")
            for name in ("Kept.olean", "Kept.olean.private"):
                (built / name).write_text("")
            self.assertEqual(structure.stale_build_errors(root), [])
            (built / "Gone.olean").write_text("")
            (built / "Gone.olean.private").write_text("")
            stale = "build output of a module that no longer exists; run lake clean"
            self.assertEqual(structure.stale_build_errors(root),
                             [f".lake/build/lib/lean/DN/Compiler/Gone.olean: {stale}",
                              f".lake/build/lib/lean/DN/Compiler/Gone.olean.private: {stale}"])

    def test_kernel_recheck_rejects_skipped_kernel(self) -> None:
        with tempfile.TemporaryDirectory() as temp:
            probes = Probes(Path(temp), ["DN.Probe.SkipKernel"])
            result = run(["leanchecker", "DN.Probe.SkipKernel"], env=probes.env)
            self.assertNotEqual(result.returncode, 0)
            self.assertIn("DN.Probe.bad", result.stdout + result.stderr)


class IndependentKernel(unittest.TestCase):
    """Probe modules exported as check.sh exports the library, then checked by nanoda with its configuration."""

    @staticmethod
    def export_list(probes: Probes) -> subprocess.CompletedProcess[str]:
        return run(["lean", "--run", "scripts/Audit.lean", "--export-list", "--root", str(probes.src)],
                   env=probes.env)

    def kernel(self, modules: list[str]) -> subprocess.CompletedProcess[str]:
        with tempfile.TemporaryDirectory() as temp:
            probes = Probes(Path(temp), modules)
            listing = self.export_list(probes)
            self.assertEqual(listing.returncode, 0, listing.stderr)
            env = {**probes.env, "LEAN_SYSROOT": run(["lean", "--print-prefix"]).stdout.strip(),
                   "LEAN_ABORT_ON_PANIC": "1"}
            export = subprocess.run([tool("lean4export"), *listing.stdout.split("\0")[:-1]], env=env, text=True,
                                    capture_output=True, check=True, timeout=600).stdout
            return subprocess.run([tool("nanoda"), "scripts/nanoda.json"], cwd=ROOT, input=export, text=True,
                                  capture_output=True, check=False, timeout=600)

    def test_export_list_names_every_checked_declaration(self) -> None:
        with tempfile.TemporaryDirectory() as temp:
            listing = self.export_list(Probes(Path(temp), ["DN.Probe.Kernel"]))
            self.assertEqual(listing.returncode, 0, listing.stderr)
            args = listing.stdout.split("\0")
            self.assertEqual(args[:2], ["DN.Probe.Kernel", "--"])
            self.assertEqual(args[-1], "")
            names = args[2:-1]
            self.assertIn("DN.Probe.halve", names)
            self.assertIn("_private.DN.Probe.Kernel.0.DN.Probe.hidden", names)
            self.assertTrue(any(".«_@»." in name for name in names), names)
            self.assertNotIn("DN.Probe.halve._unsafe_rec", names)
        refusals = {"DN.Probe.Unwritable": "cannot write the name", "DN.Probe.NulName": "cannot write the name",
                    "DN.Probe.Lookalike": "«Quot.sound» reads to nanoda as the axiom Quot.sound",
                    "DN.Probe.EmptyPrefix": "reads to nanoda as the axiom propext"}
        for module, message in refusals.items():
            with self.subTest(module=module), tempfile.TemporaryDirectory() as temp:
                listing = self.export_list(Probes(Path(temp), [module]))
                self.assertEqual(listing.returncode, 1, listing.stderr)
                self.assertIn(message, listing.stderr)

    def test_configuration_admits_only_the_audited_axioms(self) -> None:
        audited = re.search(r"^def allowedAxioms .*$", (ROOT / "scripts/Audit.lean").read_text(), re.MULTILINE)
        assert audited is not None
        config = json.loads((ROOT / "scripts/nanoda.json").read_text())
        self.assertEqual(config["permitted_axioms"], re.findall(r"``([\w.]+)", audited.group(0)))
        self.assertIs(config["unpermitted_axiom_hard_error"], True)
        self.assertNotIn("unsafe_permit_all_axioms", config)

    def test_accepts_sound_declarations(self) -> None:
        result = self.kernel(["DN.Probe.Kernel"])
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertRegex(result.stdout, r"Checked \d+ declarations with no errors")
        admitted = re.findall(r"^axiom ([\w.]+?)\.?[ {]", result.stdout, re.MULTILINE)
        self.assertTrue(admitted)
        self.assertLessEqual(set(admitted), {"propext", "Classical.choice", "Quot.sound"})

    def test_rejects_what_the_kernel_never_checked(self) -> None:
        result = self.kernel(["DN.Probe.SkipKernel"])
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("assertion failed: self.def_eq", result.stderr)
        self.assertNotIn("with no errors", result.stdout)

    def test_rejects_unpermitted_axioms(self) -> None:
        cases = {"DN.Probe.Transitive": "Foreign.", "DN.Probe.PrivateAxiom": "hidden", "DN.Probe.Sorry": "sorryAx",
                 "DN.Probe.Native": "native_decide"}
        for module, axiom in cases.items():
            with self.subTest(module=module):
                result = self.kernel(["Foreign", module] if module == "DN.Probe.Transitive" else [module])
                self.assertNotEqual(result.returncode, 0)
                self.assertRegex(result.stderr, f"unpermitted axiom \"[^\"]*{re.escape(axiom)}")


class SourceGate(unittest.TestCase):
    def test_rules(self) -> None:
        with tempfile.TemporaryDirectory() as temp:
            root = source_tree(Path(temp))
            marker = root / "marker"
            for module, (source, _) in GATE_PROBES.items():
                path = root / f"lean/DN/Probe/{module}.lean"
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_text(source.replace("{marker}", str(marker)))
            pins = {f"lean/DN/Probe/{m}.lean": sha256(root / f"lean/DN/Probe/{m}.lean")
                    for m in ("Pinned", "PinnedElab")}
            self.assertEqual(structure.static_errors(root, pins), [])
            errors = structure.gate_errors(root, pins)
            for module, (_, message) in GATE_PROBES.items():
                with self.subTest(module=module):
                    found = [e for e in errors if f"DN/Probe/{module}.lean" in e]
                    if message is None:
                        self.assertEqual(found, [])
                    else:
                        self.assertTrue(any(message in e for e in found), found or errors)
            self.assertFalse(marker.exists())
            self.assertFalse((root / ".lake").exists())

    def test_uses_lakefile_options(self) -> None:
        with tempfile.TemporaryDirectory() as temp:
            root = source_tree(Path(temp))
            (root / "lakefile.lean").write_text("package dn where\n  leanOptions := #[⟨`maxRecDepth, 8⟩]\n")
            (root / "lean/DN/Deep.lean").write_text("theorem t : [1, 2, 3].length = 3 := by decide\n")
            errors = structure.gate_errors(root, {})
            self.assertTrue(any("maximum recursion depth" in e for e in errors), errors)

    def test_documented_loom_count_matches_the_recorded_tests(self) -> None:
        recorded = (ROOT / "models/expected-tests.txt").read_text().splitlines()
        loom = sum(1 for line in recorded if line.startswith("loom "))
        for name in ("docs/baseline.md", "docs/assurance.md", "README.md"):
            with self.subTest(document=name):
                self.assertIn(f"{loom} Loom tests", (ROOT / name).read_text())

    def test_auto_implicit_is_off(self) -> None:
        self.assertIn("⟨`autoImplicit, false⟩", (ROOT / "lakefile.lean").read_text())
        with tempfile.TemporaryDirectory() as temp:
            root = source_tree(Path(temp))
            (root / "lean/DN/Deep.lean").write_text("theorem t (x : Unbound) : x = x := rfl\n")
            errors = structure.gate_errors(root, {})
            self.assertTrue(any("Unknown identifier" in e for e in errors), errors)

    def test_static_checks(self) -> None:
        with tempfile.TemporaryDirectory() as temp:
            root = source_tree(Path(temp))
            pinned = root / "lean/DN/Pinned.lean"
            pinned.write_text("namespace DN\n")
            pins = {"lean/DN/Pinned.lean": sha256(pinned)}
            self.assertEqual(structure.static_errors(root, pins), [])
            pinned.write_text("namespace DN\nend DN\n")
            (root / "lean/DN/notes.txt").write_text("")
            for name in ("lean/DN/Probe.X.lean", "lean/DN/.Hidden.lean", "lean/DN/Bad-Name.lean", "lean/Other.lean"):
                (root / name).write_text("")
            (root / "lean/DN/Link").symlink_to(root / "rfcs")
            (root / "lean-toolchain").write_text("leanprover/lean4:v4.31.0\n")
            stored = list(json.loads((root / "rfcs/manifest.json").read_text())["documents"])
            rfc = root / "rfcs" / stored[0]
            rfc.write_text(rfc.read_text() + "\n")
            (root / "rfcs" / stored[1]).unlink()
            (root / "rfcs/rfc9999.txt").write_text("a document nobody recorded\n")
            patch = root / "backend" / json.loads((root / "backend/lock.json").read_text())["patches"][0]["path"]
            patch.write_text(patch.read_text() + "\n")
            (root / "migration/kept.rs").write_text("fn main() { }\n")
            errors = "\n".join(structure.static_errors(root, pins))
            for expected in ("update its pin", "unexpected file under lean/", "source gate rules were reviewed",
                             "lean/DN/Probe.X.lean: name is not a plain identifier", "lean/DN/Link: symlink",
                             "lean/DN/.Hidden.lean: name is not", "lean/DN/Bad-Name.lean: name is not",
                             "lean/Other.lean: unexpected file",
                             f"RFC digest mismatch: {rfc.name}", f"RFC missing: {stored[1]}",
                             "the RFC collection carries a document the manifest does not record: rfc9999.txt",
                             "backend patch digest mismatch",
                             "preserved reference changed: migration/kept.rs"):
                self.assertIn(expected, errors)

    def test_check_reports_static_and_gate_errors(self) -> None:
        with tempfile.TemporaryDirectory() as temp:
            root = source_tree(Path(temp))
            (root / "lean/DN/notes.txt").write_text("")
            (root / "lean/DN/Eval.lean").write_text("#eval 1\n")
            errors = "\n".join(structure.check(root, {}))
            self.assertIn("unexpected file under lean/", errors)
            self.assertIn(EVAL, errors)

    def test_gate_reads_the_file_lake_builds(self) -> None:
        with tempfile.TemporaryDirectory() as temp:
            root = source_tree(Path(temp))
            (root / "lean/DN/Probe.X.lean").write_text("#eval 1\n")
            errors = structure.gate_errors(root, {})
            self.assertTrue(any("Probe.X.lean" in e and EVAL in e for e in errors), errors)
            (root / "lean/DN/Probe").mkdir()
            (root / "lean/DN/Probe/X.lean").write_text("theorem t : True := trivial\n")
            (root / "lean/DN/D.lean").mkdir()
            errors = structure.gate_errors(root, {})
            self.assertTrue(any("cannot be checked as module" in e for e in errors), errors)

    def test_import_forms(self) -> None:
        source = "module\n\npublic meta import all «DN».A\nprivate import DN.«B»\nimport DN.C\n-- import DN.D\n"
        self.assertEqual(structure.imports(source), {"DN.A", "DN.B", "DN.C"})

    def test_import_cycle(self) -> None:
        with tempfile.TemporaryDirectory() as temp:
            root = source_tree(Path(temp))
            (root / "lean/DN/A.lean").write_text("import DN.B\n")
            (root / "lean/DN/B.lean").write_text("import DN.A\n")
            self.assertTrue(structure.gate_errors(root, {})[0].startswith("import cycle"))
