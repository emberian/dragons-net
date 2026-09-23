"""Gate tests on disposable copies and probe modules; the working tree is never modified, and only
pinned tools are added to .deps."""
from __future__ import annotations

import functools
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tarfile
import tempfile
from typing import Any
import unittest

ROOT = Path(__file__).resolve().parents[1]


def script(name: str) -> Any:
    """Load a script as a module under its own name, which dataclasses in it need."""
    spec = importlib.util.spec_from_file_location(name, ROOT / f"scripts/{name}.py")
    assert spec is not None and spec.loader is not None
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module


structure = script("check_structure")
build_archive = script("build_archive")
native_baseline = script("native_baseline")
gen_keywords = script("gen_keywords")
upstream_sources = script("check_upstream_sources")
bootstrap_tool = script("bootstrap_tool")
verify_run = script("verify_run")
state_check = script("state_check")
check_holmake = script("check_holmake")
CHECK = (ROOT / "scripts/check.sh").read_text()
AUDIT = re.search(r"--run scripts/Audit\.lean --regressions (\d+)", CHECK)

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
        "def DN.Probe.regression_9002 : Nat := 1\ndef DN.Probe.regression_9004 : Bool := false\n"),
    "DN.Probe.Regressions": (
        "namespace DN.Probe\ndef count : Nat → Nat\n  | 0 => 0\n  | n + 1 => count n + 1\n"
        "def le_succ : (n : Nat) → n ≤ n + 1\n  | 0 => Nat.le_succ 0\n"
        "  | n + 1 => Nat.succ_le_succ (le_succ n)\n"
        "def regression_9001 : Bool := false\nprivate def regression_9003 : Bool := count 3 == 3\n"
        "noncomputable def regression_9005 : Bool := Classical.choice ⟨true⟩\nend DN.Probe\n"),
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
    "regression is not a Bool definition: DN.Probe.regression_9002",
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


def run(args: list[str], env: dict[str, str] | None = None) -> subprocess.CompletedProcess[str]:
    return subprocess.run(args, cwd=ROOT, env=env, text=True, capture_output=True, timeout=600,
                          check=False)


def regressions() -> str:
    assert AUDIT is not None, "scripts/check.sh does not run the audit with --regressions"
    return AUDIT.group(1)


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


@functools.cache
def tool(name: str) -> str:
    result = subprocess.run(["python3", "scripts/bootstrap_tool.py", name], cwd=ROOT, text=True,
                            capture_output=True, check=False, timeout=1800)
    if result.returncode != 0:
        raise AssertionError(f"cannot obtain {name}:\n{result.stderr}")
    return result.stdout.strip()


def source_tree(directory: Path) -> Path:
    for name in ("rfcs", "backend"):
        shutil.copytree(ROOT / name, directory / name)
    for name in ("lean-toolchain", "lakefile.lean"):
        shutil.copy(ROOT / name, directory / name)
    (directory / "lean/DN").mkdir(parents=True)
    return directory


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


class Audit(unittest.TestCase):
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
            self.assertIn(f"expected {regressions()} passing regressions, found {int(regressions()) + 1}",
                          result.stderr)

    def test_documented_counts_match_the_audit(self) -> None:
        prefix = run(["lean", "--print-prefix"]).stdout.strip()
        env = {**os.environ, "LEAN_PATH": f"{prefix}/lib/lean:{ROOT}/.lake/build/lib/lean"}
        result = run(["lean", "--run", "scripts/Audit.lean", "--regressions", regressions()], env=env)
        self.assertEqual(result.returncode, 0, result.stderr)
        counts = re.search(r"(\d+) modules, (\d+) declarations, (\d+) theorems", result.stdout)
        assert counts is not None, result.stdout
        declarations, theorems = (f"{int(counts.group(index)):,}" for index in (2, 3))
        documented = {
            "docs/assurance.md": (f"audit covers {declarations} declarations, including {theorems} theorems",
                                  f"| {regressions()} executable examples |"),
            "docs/baseline.md": (f"{declarations} declarations, including {theorems} theorems",
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
            rfc = root / "rfcs" / next(iter(json.loads((root / "rfcs/manifest.json").read_text())["documents"]))
            rfc.write_text(rfc.read_text() + "\n")
            patch = root / "backend" / json.loads((root / "backend/lock.json").read_text())["patches"][0]["path"]
            patch.write_text(patch.read_text() + "\n")
            errors = "\n".join(structure.static_errors(root, pins))
            for expected in ("update its pin", "unexpected file under lean/", "source gate rules were reviewed",
                             "lean/DN/Probe.X.lean: name is not a plain identifier", "lean/DN/Link: symlink",
                             "lean/DN/.Hidden.lean: name is not", "lean/DN/Bad-Name.lean: name is not",
                             "lean/Other.lean: unexpected file",
                             f"RFC digest mismatch: {rfc.name}", "backend patch digest mismatch"):
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


class Pipeline(unittest.TestCase):
    def test_check_script_runs_every_gate_in_order(self) -> None:
        steps = ["LAKE_ARTIFACT_CACHE=false", "tracked=$(tracked_outputs)", "before=$(snapshot)",
                 "python3 scripts/check_structure.py", "lake build --wfail DN dn-compiler",
                 '"$(snapshot)" != "$before"', "LEAN_ABORT_ON_PANIC=1", "check_structure.py outputs",
                 '"$leanchecker" DN', "--export-list",
                 '"$nanoda" scripts/nanoda.json', f"--regressions {regressions()}"]
        positions = [CHECK.find(step) for step in steps]
        self.assertNotIn(-1, positions, dict(zip(steps, positions, strict=True)))
        self.assertEqual(positions, sorted(positions))
        self.assertIn("all) build; proofs; tests ;;", CHECK)
        self.assertNotIn("lake env", CHECK)

    def test_build_archive_accepts_only_the_build_directory(self) -> None:
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            (root / "src/.lake/build/lib/lean/DN").mkdir(parents=True)
            (root / "src/.lake/build/lib/lean/DN/M.olean").write_text("olean")
            (root / "evil").write_text("x")
            good = root / "good.tar"
            with tarfile.open(good, "w") as tar:
                tar.add(root / "src/.lake/build", arcname=".lake/build")
            build_archive.unpack(good, root / "out")
            self.assertEqual((root / "out/.lake/build/lib/lean/DN/M.olean").read_text(), "olean")
            outside = {"escape": "../evil", "elsewhere": "scripts/check.sh", "absolute": "/tmp/evil",
                       "inner escape": ".lake/build/bin/../../../scripts/check.sh",
                       "toolchain module": ".lake/build/lib/lean/Init.olean", "file for a directory": ".lake/build/lib"}
            for case, name in outside.items():
                with self.subTest(case=case):
                    bad = root / f"{case}.tar"
                    with tarfile.open(bad, "w") as tar:
                        tar.add(root / "evil", arcname=name)
                    with self.assertRaises(SystemExit):
                        build_archive.unpack(bad, root / "out")
            link = root / "link.tar"
            with tarfile.open(link, "w") as tar:
                info = tarfile.TarInfo(".lake/build/bin/link")
                info.type, info.linkname = tarfile.SYMTYPE, "/etc/passwd"
                tar.addfile(info)
            with self.assertRaises(SystemExit):
                build_archive.unpack(link, root / "out")
            self.assertFalse((root / "out/scripts").exists())

    def test_snapshot_covers_everything_but_vcs_and_outputs(self) -> None:
        function = re.search(r"^snapshot\(\) \{.*?^\}", CHECK, re.MULTILINE | re.DOTALL)
        assert function is not None
        with tempfile.TemporaryDirectory() as temp:
            tree = Path(temp)
            ignored = (".git/config", ".lake/build/lib", "build/evidence/check.log")
            watched = ("scripts/check.sh", "lean/DN/X.lean", "target/debug/app", ".deps/tool",
                       "tests/__pycache__/t.pyc")
            for name in ignored + watched:
                (tree / name).parent.mkdir(parents=True, exist_ok=True)
                (tree / name).write_text("0")

            def snapshot() -> str:
                script = f"set -euo pipefail\n{function.group(0)}\nsnapshot"
                return subprocess.run(["bash", "-c", script], cwd=tree, text=True, capture_output=True,
                                      check=True).stdout

            (tree / "tests/scripts").symlink_to(tree / "scripts")
            before = snapshot()
            for name in ignored:
                (tree / name).write_text("1")
            self.assertEqual(snapshot(), before)
            for name in watched:
                with self.subTest(changed=name):
                    (tree / name).write_text("1")
                    self.assertNotEqual(snapshot(), before)
                    (tree / name).write_text("0")
            (tree / "tests/test_extra.py").symlink_to(tree / "scripts/check.sh")
            self.assertNotEqual(snapshot(), before)
            (tree / "tests/test_extra.py").unlink()
            (tree / "tests/scripts").unlink()
            (tree / "tests/scripts").symlink_to(tree / "lean")
            self.assertNotEqual(snapshot(), before)

    def test_check_stops_before_the_gate(self) -> None:
        with tempfile.TemporaryDirectory() as temp:
            parent = Path(temp)
            tree = parent / "dn"
            (tree / "scripts").mkdir(parents=True)
            shutil.copy(ROOT / "scripts/check.sh", tree / "scripts/check.sh")

            def refused(message: str) -> None:
                result = subprocess.run(["bash", "scripts/check.sh"], cwd=tree, text=True, capture_output=True,
                                        check=False)
                self.assertNotEqual(result.returncode, 0)
                self.assertIn(message, result.stderr)
                self.assertNotIn("check_structure", result.stderr)

            refused("not a git repository")
            subprocess.run(["git", "init", "-q"], cwd=parent, check=True)
            refused("run from the root of its own git checkout")
            shutil.rmtree(parent / ".git")
            subprocess.run(["git", "init", "-q"], cwd=tree, check=True)
            (tree / ".lake").mkdir()
            (tree / ".lake/x.olean").write_text("")
            subprocess.run(["git", "add", "-f", "."], cwd=tree, check=True)
            refused("build outputs are tracked by git")

    def test_check_stages_run_only_their_steps(self) -> None:
        with tempfile.TemporaryDirectory() as temp:
            tree, stubs, toolchain = (Path(temp) / name for name in ("repo", "bin", "toolchain"))
            (tree / "scripts").mkdir(parents=True)
            shutil.copy(ROOT / "scripts/check.sh", tree / "scripts/check.sh")
            subprocess.run(["git", "init", "-q"], cwd=tree, check=True)
            log = Path(temp) / "log"

            def stub(directory: Path, name: str, body: str) -> None:
                directory.mkdir(exist_ok=True)
                (directory / name).write_text(f"#!/bin/sh\n{body}\n")
                (directory / name).chmod(0o755)

            for name in ("lake", "cargo", "leanchecker", "lean"):
                stub(stubs, name, f'echo "{name} $*" >> {log}')
            stub(stubs, "python3", f'echo "python3 $*" >> {log}\n'
                 f'case "$2" in lean4export | nanoda) echo "{stubs}/$2" ;; esac')
            checker_env = "[$LEAN_PATH $LEAN_ABORT_ON_PANIC]"
            stub(stubs, "lean4export", f'echo "lean4export $* $LEAN_SYSROOT {checker_env}" >> {log}\n'
                 'echo export\nexit "${FAIL_EXPORT:-0}"')
            stub(stubs, "nanoda", f'echo "nanoda $* $(cat)" >> {log}\nexit "${{FAIL_NANODA:-0}}"')
            stub(toolchain, "leanchecker", f'echo "toolchain leanchecker $* {checker_env}" >> {log}')
            stub(toolchain, "lean", f'echo "toolchain lean $* {checker_env}" >> {log}\ncase "$*" in\n'
                 "  --print-prefix) echo /sysroot ;;\n  *--export-list*) printf 'M\\0--\\0N\\0' ;;\nesac")
            stub(stubs, "elan", f"echo {toolchain}/$2")
            env = {key: value for key, value in os.environ.items() if key not in ("LEAN_PATH", "LEAN_ABORT_ON_PANIC")}
            env["PATH"] = f"{stubs}:{os.environ['PATH']}"
            checked = "[/sysroot/lib/lean:.lake/build/lib/lean 1]"
            expected = {
                "build": ["python3 scripts/check_structure.py",
                          "lake build --wfail DN dn-compiler"],
                "proofs": ["toolchain lean --print-prefix [ ]", "python3 scripts/bootstrap_tool.py lean4export",
                           "python3 scripts/bootstrap_tool.py nanoda",
                           "python3 scripts/check_structure.py outputs",
                           f"toolchain leanchecker DN {checked}",
                           f"toolchain lean --run scripts/Audit.lean --export-list {checked}",
                           f"lean4export M -- N /sysroot {checked}", "nanoda scripts/nanoda.json export",
                           f"toolchain lean --run scripts/Audit.lean --regressions {regressions()} {checked}"],
                "tests": ["python3 -m unittest", "cargo clippy", "cargo clippy", "cargo clippy",
                          "cargo clippy", "cargo test", "python3 scripts/check_models.py",
                          "python3 scripts/state_check.py"],
            }
            for stage, steps in expected.items():
                with self.subTest(stage=stage):
                    log.write_text("")
                    subprocess.run(["bash", "scripts/check.sh", stage], cwd=tree, env=env, check=True,
                                   capture_output=True)
                    calls = log.read_text().splitlines()
                    self.assertEqual(len(calls), len(steps), calls)
                    for call, step in zip(calls, steps, strict=True):
                        self.assertTrue(call == step if stage == "proofs" else call.startswith(step), (call, step))
            for failing in ("FAIL_EXPORT", "FAIL_NANODA"):
                with self.subTest(failing=failing):
                    log.write_text("")
                    result = subprocess.run(["bash", "scripts/check.sh", "proofs"], cwd=tree,
                                            env={**env, failing: "1"}, capture_output=True, check=False)
                    self.assertNotEqual(result.returncode, 0)
                    self.assertNotIn("--regressions", log.read_text())

    def test_ci_runs_the_stages_in_one_chain(self) -> None:
        workflow = (ROOT / ".github/workflows/ci.yml").read_text().partition("\njobs:\n")[2]
        jobs: dict[str, str] = {}
        for block in re.split(r"^  (?=[a-z]+:\n)", workflow, flags=re.MULTILINE)[1:]:
            name, _, body = block.partition(":\n")
            jobs[name] = body
        self.assertEqual(list(jobs), ["lint", "build", "proofs", "test"])
        for job, previous in zip(list(jobs)[1:], list(jobs), strict=False):
            self.assertIn(f"needs: {previous}\n", jobs[job])
        self.assertIn("bash scripts/lint.sh", jobs["lint"])
        for job, stage in (("build", "build"), ("proofs", "proofs"), ("test", "tests")):
            self.assertEqual(re.findall(r"scripts/check\.sh (\w+)", jobs[job]), [stage])
        # A job added or renamed here is a job the verify lane stops requiring.
        self.assertEqual(verify_run.REQUIRED_JOBS, tuple(jobs))

    def test_verify_judges_a_run_from_outside_the_change(self) -> None:
        green: list[dict[str, object]] = [{"name": name, "status": "completed", "conclusion": "success"}
                                          for name in verify_run.REQUIRED_JOBS]
        base = {"scripts/check.sh": "a", ".github/workflows/ci.yml": "b", "tools.lock.json": "c",
                "lean/DN/A.lean": "d", "docs/x.md": "e", "README.md": "f",
                "models/expected-tests.txt": "g", "models/Cargo.lock": "h",
                "crates/dn-runtime/Cargo.toml": "i"}
        ok = verify_run.Run(url="https://example.invalid/run", conclusion="success",
                            default_branch="main", base_refs=("main",))

        def tree(paths: dict[str, str], truncated: bool = False,
                 mode: str = "100644", extra: list[dict[str, str]] | None = None) -> dict[str, object]:
            entries: list[dict[str, str]] = [{"path": "scripts", "type": "tree", "sha": "t"}]
            entries += [{"path": p, "type": "blob", "mode": mode, "sha": s} for p, s in paths.items()]
            return {"truncated": truncated, "tree": entries + (extra or [])}

        def verdict(head: dict[str, str], truncated: bool = False,
                    jobs: list[dict[str, object]] | None = None,
                    run: Any = ok, extra: list[dict[str, str]] | None = None) -> Any:
            return verify_run.judge(green if jobs is None else jobs, tree(base),
                                    tree(head, truncated, extra=extra), run)

        self.assertEqual(verdict(base).conclusion, "success")
        for subject in ("lean/DN/A.lean", "docs/x.md", "README.md"):
            with self.subTest(subject=subject):
                # What the checks read is the change under review; it may differ.
                self.assertEqual(verdict({**base, subject: "x"}).conclusion, "success")
        critical = {"edited": {**base, "scripts/check.sh": "x"},
                    "workflow edited": {**base, ".github/workflows/ci.yml": "x"},
                    "pin moved": {**base, "tools.lock.json": "x"},
                    # Inside the subject directories, but not subjects: the list the
                    # model gate requires the tests to match, and dependency pins.
                    "test list shortened": {**base, "models/expected-tests.txt": "x"},
                    "model pin moved": {**base, "models/Cargo.lock": "x"},
                    "manifest edited": {**base, "crates/dn-runtime/Cargo.toml": "x"},
                    "added": {**base, "scripts/graphlib.py": "x"},
                    "removed": {k: v for k, v in base.items() if k != "scripts/check.sh"}}
        for case, head in critical.items():
            with self.subTest(case=case):
                answer = verdict(head)
                self.assertEqual(answer.conclusion, "neutral")
                self.assertNotIn("lean/DN/A.lean", answer.summary)
        self.assertIn("scripts/graphlib.py", verdict(critical["added"]).summary)
        # Without the whole listing there is nothing to conclude.
        self.assertEqual(verdict(base, truncated=True).conclusion, "neutral")
        # A check that stops being executable is a change to the checks as well.
        mode = verify_run.judge(green, tree(base), tree(base, mode="100755"), ok)
        self.assertEqual(mode.conclusion, "neutral")
        self.assertIn("scripts/check.sh", mode.summary)
        # A submodule carries content the comparison would otherwise not see.
        link = [{"path": "vendor", "type": "commit", "mode": "160000", "sha": "s"}]
        self.assertEqual(verdict(base, extra=link).conclusion, "neutral")
        missing = [job for job in green if job["name"] != "proofs"]
        skipped = [{**job, "conclusion": "skipped"} if job["name"] == "proofs" else job for job in green]
        twice: list[dict[str, object]] = [
            *green, {"name": "proofs", "status": "completed", "conclusion": "success"}]
        for case, jobs in (("job removed", missing), ("job skipped", skipped), ("job twice", twice)):
            with self.subTest(case=case):
                # A run may conclude successfully with a job missing, allowed to
                # fail, or answered for by a second job of the same name.
                answer = verdict(base, jobs=jobs)
                self.assertEqual(answer.conclusion, "failure")
                self.assertIn("proofs", answer.summary)
        # Nothing to certify: the run itself is red, and its own jobs say why.
        for conclusion in ("failure", "skipped", "cancelled"):
            with self.subTest(conclusion=conclusion):
                ended = verify_run.Run(url="u", conclusion=conclusion, default_branch="main")
                answer = verdict(base, run=ended)
                self.assertEqual(answer.conclusion, "neutral")
                self.assertIn(conclusion, answer.summary)
        # The summary has a size limit, so neither list may grow without one.
        many: list[dict[str, object]] = [*green] + [
            {"name": f"extra-{n}", "status": "completed", "conclusion": "success"}
            for n in range(verify_run.LISTED)]
        crowded = verdict(base, jobs=many)
        self.assertEqual(crowded.conclusion, "success")
        self.assertIn(f"and {len(many) - verify_run.LISTED} more", crowded.summary)
        # The checks that ran are the base branch's, and this speaks for one branch.
        other = verify_run.Run(url="u", conclusion="success", default_branch="main",
                               base_refs=("release",))
        answer = verdict(base, run=other)
        self.assertEqual(answer.conclusion, "neutral")
        self.assertIn("release", answer.summary)

    def test_verify_never_runs_the_change_it_judges(self) -> None:
        workflow = (ROOT / ".github/workflows/verify.yml").read_text()
        self.assertIn("workflows: [checks]", workflow)
        # The default branch's copy, by name: `github.sha` would be one more thing to trust.
        self.assertIn("ref: ${{ github.event.repository.default_branch }}", workflow)
        self.assertIn("python3 -P scripts/verify_run.py", workflow)
        # And it proves that is what it got before running anything from the checkout.
        self.assertIn('compare/$DEFAULT_BRANCH...$head', workflow)
        # The write permission is safe only while nothing from the change runs in this job.
        self.assertIn("checks: write", workflow)
        # Comments name what the lane is about; the steps are what it does.
        steps = "\n".join(line for line in workflow.splitlines() if not line.lstrip().startswith("#"))
        checkout = steps.partition("- name: Read the finished run")[0]
        for forbidden in ("head_sha", "head_branch", "head_repository"):
            self.assertNotIn(forbidden, checkout)
        for forbidden in ("pull_request_target", "scripts/check.sh", "lake ", "cargo "):
            self.assertNotIn(forbidden, steps)
        # The trigger matches the other workflow by name, so the two must agree.
        self.assertTrue((ROOT / ".github/workflows/ci.yml").read_text().startswith("name: checks\n"))
        # Only one thing from the checkout runs, and only the check run is written.
        self.assertEqual(steps.count("python3 "), 1)
        self.assertEqual(re.findall(r"^\s+\w+: write$", steps, re.MULTILINE), ["      checks: write"])
        # What makes the job itself red when the verdict is a failure.
        self.assertIn('[[ "$conclusion" != failure ]]', steps)
        # A pull request from a fork whose commit this repository cannot read.
        self.assertIn('repos/$HEAD_REPO/git/trees/$HEAD_SHA', steps)
        # The branch the run was merged into decides which checks ran.
        self.assertIn("commits/$HEAD_SHA/pulls", steps)
        self.assertIn("--base-refs", steps)
        self.assertIn("--conclusion", steps)

    def test_verify_publishes_what_it_judged(self) -> None:
        """The published body is the verdict, and a hostile path cannot forge a line in it."""
        with tempfile.TemporaryDirectory() as temp:
            work = Path(temp)
            jobs = [{"name": name, "status": "completed", "conclusion": "success"}
                    for name in verify_run.REQUIRED_JOBS]
            (work / "jobs.json").write_text(json.dumps({"jobs": jobs}))
            forged = "scripts/x`\n- every required job succeeded | success"
            entries = [{"path": "scripts/check.sh", "type": "blob", "mode": "100755", "sha": "a"}]
            base = {"truncated": False, "tree": entries}
            head = {"truncated": False, "tree": [
                *entries, {"path": forged, "type": "blob", "mode": "100644", "sha": "b"}]}
            (work / "base.json").write_text(json.dumps(base))
            (work / "head.json").write_text(json.dumps(head))
            sha = "0" * 40

            def run_verify(*extra: str) -> subprocess.CompletedProcess[str]:
                return subprocess.run(
                    ["python3", "-P", str(ROOT / "scripts/verify_run.py"),
                     "--jobs", str(work / "jobs.json"), "--base-tree", str(work / "base.json"),
                     "--head-tree", str(work / "head.json"), "--head-sha", sha,
                     "--conclusion", "success", "--default-branch", "main",
                     "--run-url", "https://example.invalid/run", *extra],
                    capture_output=True, text=True, check=False)

            result = run_verify("--details-url", "https://example.invalid/verify")
            self.assertEqual(result.returncode, 0, result.stderr)
            body = json.loads(result.stdout)
            self.assertEqual(body["name"], "verify")
            self.assertEqual(body["head_sha"], sha)
            self.assertEqual(body["status"], "completed")
            self.assertEqual(body["conclusion"], "neutral")
            self.assertEqual(body["details_url"], "https://example.invalid/verify")
            summary = body["output"]["summary"]
            self.assertIn("This change edits its own checks", body["output"]["title"])
            # One bullet per path, and the forged cell and line break are gone.
            bullets = [line for line in summary.splitlines() if line.startswith("- ")]
            self.assertEqual(len(bullets), 1, bullets)
            self.assertNotIn("|", bullets[0])
            self.assertEqual(bullets[0].count("`"), 2, "a path closed its own quoting")
            self.assertLess(len(summary), 65536)
            # A reference is not a commit, and the body is published against one.
            refused = subprocess.run(
                ["python3", "-P", str(ROOT / "scripts/verify_run.py"),
                 "--jobs", str(work / "jobs.json"), "--base-tree", str(work / "base.json"),
                 "--head-tree", str(work / "head.json"), "--head-sha", "refs/heads/main",
                 "--conclusion", "success", "--default-branch", "main",
                 "--run-url", "https://example.invalid/run"],
                capture_output=True, text=True, check=False)
            self.assertNotEqual(refused.returncode, 0)
            self.assertIn("not a commit", refused.stderr)

    def test_holmake_gate_reads_the_job_logs_as_well(self) -> None:
        """A parallel Holmake prints a status word and writes the details to a log file.

        Reading only the captured standard output would therefore see nothing, so
        each way of recording a cheat, an oracle tag or a cache hit is checked here.
        """
        with tempfile.TemporaryDirectory() as temp:
            work = Path(temp)
            tree = work / "cakeml"
            (tree / "pancake/proofs/.hol/logs").mkdir(parents=True)
            built = tree / "pancake/proofs/pan_to_targetProofTheory.uo"
            built.write_text("theory")
            output = work / "holmake.log"

            def found(stdout: str, log: str, jobs: int = 2, target: Path | None = built,
                      since: float = 0.0) -> Any:
                output.write_text(stdout)
                (tree / "pancake/proofs/.hol/logs/job").write_text(log)
                return check_holmake.problems(output, tree, jobs, target, since)

            self.assertEqual(found("Finished pan_to_targetProofTheory OK", "no complaints"), [])
            for pattern in check_holmake.RECORDED:
                with self.subTest(recorded=pattern):
                    # A single-job build prints these; a parallel one writes them.
                    self.assertTrue(found(f"...{pattern}...", "clean"))
                    self.assertTrue(found("everything OK", f"...{pattern}..."))
            for word in check_holmake.STATUS:
                with self.subTest(status=word):
                    self.assertTrue(found(f"pan_to_targetProofTheory {word} (1m)", "clean"))
            # `OK` is printed for a clean job and for one whose theorems are oracle
            # tagged, so the word alone must not clear the run.
            self.assertTrue(found("pan_to_targetProofTheory OK", "Saved ORACLE thm _"))
            self.assertEqual(found("OK", "clean", jobs=1), [])
            shutil.rmtree(tree / "pancake/proofs/.hol")
            self.assertTrue(check_holmake.problems(output, tree, 2, built, 0.0),
                            "a parallel build with no job logs was accepted")
            self.assertEqual(check_holmake.problems(output, tree, 1, built, 0.0), [])
            self.assertTrue(check_holmake.problems(output, tree, 1, built, built.stat().st_mtime + 60),
                            "a target older than the run was accepted")
            self.assertTrue(check_holmake.problems(output, tree, 1, tree / "missing.uo", 0.0))

    def test_checkers_cover_what_decides_the_checks(self) -> None:
        """The tests stage runs code from the change; what it may not change is this."""
        function = re.search(r"^checkers\(\) \{.*?^\}", CHECK, re.MULTILINE | re.DOTALL)
        assert function is not None
        with tempfile.TemporaryDirectory() as temp:
            tree = Path(temp)
            for name in ("scripts/check.sh", "tests/test_gates.py", ".github/workflows/ci.yml",
                         "lakefile.lean", "lean-toolchain", "tools.lock.json", "ruff.toml",
                         "lean/DN/A.lean", "docs/x.md", "crates/dn-runtime/src/lib.rs"):
                (tree / name).parent.mkdir(parents=True, exist_ok=True)
                (tree / name).write_text("0")
            subprocess.run(["git", "init", "-q"], cwd=tree, check=True)
            (tree / ".gitignore").write_text("__pycache__/\n")
            subprocess.run(["git", "add", "-A"], cwd=tree, check=True)

            def checkers() -> str:
                script = f"set -euo pipefail\n{function.group(0)}\ncheckers"
                return subprocess.run(["bash", "-c", script], cwd=tree, text=True,
                                      capture_output=True, check=True).stdout

            before = checkers()
            for name in ("lean/DN/A.lean", "docs/x.md", "crates/dn-runtime/src/lib.rs"):
                with self.subTest(subject=name):
                    # The subject of the checks changes with the change under review.
                    (tree / name).write_text("1")
                    self.assertEqual(checkers(), before)
            for name in ("scripts/check.sh", "tests/test_gates.py", ".github/workflows/ci.yml",
                         "lakefile.lean", "lean-toolchain", "tools.lock.json", "ruff.toml"):
                with self.subTest(changed=name):
                    (tree / name).write_text("1")
                    self.assertNotEqual(checkers(), before)
                    (tree / name).write_text("0")
            self.assertEqual(checkers(), before)
            # A module dropped in during the run counts; bytecode the run writes does not.
            (tree / "tests/graphlib.py").write_text("x")
            self.assertNotEqual(checkers(), before)
            (tree / "tests/graphlib.py").unlink()
            (tree / "scripts/__pycache__").mkdir()
            (tree / "scripts/__pycache__/check.pyc").write_text("x")
            self.assertEqual(checkers(), before)

    def test_backend_refuses_a_target_that_is_an_option(self) -> None:
        """`DN_BACKEND_TARGET` reaches Holmake as an argument; `--fast` cheats every tactic."""
        with tempfile.TemporaryDirectory() as temp:
            tree = Path(temp) / "dn"
            (tree / "scripts").mkdir(parents=True)
            shutil.copy(ROOT / "scripts/check_backend.sh", tree / "scripts")
            for target, ok in (("--fast", False), ("-j4", False), ("../evil", False),
                               ("loop_liveProofTheory.uo", True)):
                with self.subTest(target=target):
                    result = subprocess.run(["bash", "scripts/check_backend.sh"], cwd=tree,
                                            env={**os.environ, "DN_BACKEND_TARGET": target},
                                            capture_output=True, text=True, check=False)
                    refused = "must name a theory object" in result.stderr
                    self.assertEqual(refused, not ok, result.stderr)
                    if not ok:
                        self.assertEqual(result.returncode, 2)

    def test_state_check_reads_the_whole_state(self) -> None:
        """The lane compares every printed field, not only the value a run computes."""
        lines = ["CASE ok", "PROG (seq (assign x (const 1)) (ret (var x)))", "LOCALS x=5",
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
        dump = run([str(ROOT / ".lake/build/bin/dn-compiler"), "dump-states"]).stdout
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
                          "(seq ", "(if ", "(while ", "(ret ", "(mul ", "(and ", "(shr ",
                          "(loadb ", "(loadw ", "(base)", "(less ", "(equal ", "(notless "):
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

    def test_no_script_shadows_a_standard_library_module(self) -> None:
        """`unittest discover` puts tests/ first on the path, which PYTHONSAFEPATH does not undo."""
        for directory in ("scripts", "tests"):
            for path in sorted((ROOT / directory).rglob("*.py")):
                with self.subTest(module=str(path.relative_to(ROOT))):
                    self.assertNotIn(path.stem, sys.stdlib_module_names)

    def test_tree_digest_sees_more_than_file_contents(self) -> None:
        with tempfile.TemporaryDirectory() as temp:
            tool = Path(temp) / "tool"
            (tool / "inner").mkdir(parents=True)
            (tool / "tool.bin").write_text("binary")
            (tool / "link").symlink_to("tool.bin")

            def digest() -> Any:
                # The walk is cached within a run, which no caller defeats by
                # rewriting a tool it has already checked; a test does.
                bootstrap_tool.tree_digest.cache_clear()
                return bootstrap_tool.tree_digest(tool)

            before = digest()
            (tool / "tool.bin").chmod(0o755)
            self.assertNotEqual(digest(), before, "the executable bit is not in the manifest")
            (tool / "tool.bin").chmod(0o644)
            self.assertEqual(digest(), before)
            (tool / "extra").mkdir()
            self.assertNotEqual(digest(), before, "an added directory is not in the manifest")
            (tool / "extra").rmdir()
            (tool / "link").unlink()
            (tool / "link").symlink_to("elsewhere")
            self.assertNotEqual(digest(), before, "a symlink's target is not in the manifest")

    def test_bootstrap_verifies_stored_tools(self) -> None:
        with tempfile.TemporaryDirectory() as temp:
            tree = Path(temp)
            (tree / "scripts").mkdir()
            shutil.copy(ROOT / "scripts/bootstrap_tool.py", tree / "scripts")
            shutil.copy(ROOT / "tools.lock.json", tree)
            subprocess.run(["git", "init", "-q"], cwd=tree, check=True)
            pin = json.loads((ROOT / "tools.lock.json").read_text())["typos"]

            def bootstrap() -> str:
                return subprocess.run(["python3", "scripts/bootstrap_tool.py", "typos"], cwd=tree, text=True,
                                      capture_output=True, check=False).stderr

            archive = tree / ".deps/archives" / pin["sha256"]
            archive.parent.mkdir(parents=True)
            archive.write_text("not the pinned archive")
            self.assertIn("digest mismatch", bootstrap())
            self.assertFalse(archive.exists())
            unpacked = tree / ".deps/tools" / f"typos-{pin['version']}"
            unpacked.mkdir(parents=True)
            (unpacked / "archive.sha256").write_text("0" * 64 + "\n")
            self.assertIn("does not match the lock", bootstrap())
            # The archive is verified once, when it is downloaded; a stored tool is
            # verified on every use against a manifest over its whole content.
            (unpacked / "archive.sha256").write_text(pin["sha256"] + "\n")
            (unpacked / pin["binary"]).write_text("the tool")
            (unpacked / "tree.sha256").write_text(bootstrap_tool.tree_digest(unpacked) + "\n")
            self.assertEqual(bootstrap(), "")
            (unpacked / pin["binary"]).write_text("something else")
            self.assertIn("has changed since it was installed", bootstrap())
            (unpacked / pin["binary"]).write_text("the tool")
            (unpacked / "extra").write_text("smuggled in")
            self.assertIn("has changed since it was installed", bootstrap())

    def test_tools_come_only_from_their_archives(self) -> None:
        lint = (ROOT / "scripts/lint.sh").read_text()
        self.assertLess(lint.index("bash scripts/check.sh guard"), lint.index("bootstrap_tool.py"))
        with tempfile.TemporaryDirectory() as temp:
            tree = Path(temp)
            (tree / "scripts").mkdir()
            shutil.copy(ROOT / "scripts/bootstrap_tool.py", tree / "scripts")
            shutil.copy(ROOT / "tools.lock.json", tree)
            subprocess.run(["git", "init", "-q"], cwd=tree, check=True)
            (tree / ".deps/tools/typos-v1.50.1").mkdir(parents=True)
            (tree / ".deps/tools/typos-v1.50.1/typos").write_text("")
            subprocess.run(["git", "add", "-f", ".deps"], cwd=tree, check=True)
            result = subprocess.run(["python3", "scripts/bootstrap_tool.py", "typos"], cwd=tree, text=True,
                                    capture_output=True, check=False)
            self.assertNotEqual(result.returncode, 0)
            self.assertIn(".deps is tracked by git", result.stderr)

    def test_bootstrap_builds_tools_outside_the_repository(self) -> None:
        with tempfile.TemporaryDirectory() as temp:
            work = Path(temp)
            tree, stubs, cache, log = work / "repo", work / "bin", work / "cache", work / "log"
            (tree / "scripts").mkdir(parents=True)
            shutil.copy(ROOT / "scripts/bootstrap_tool.py", tree / "scripts")
            for name in ("lean-toolchain", "rust-toolchain.toml"):
                shutil.copy(ROOT / name, tree)
            subprocess.run(["git", "init", "-q"], cwd=tree, check=True)
            lock = json.loads((ROOT / "tools.lock.json").read_text())
            archives = tree / ".deps/archives"
            archives.mkdir(parents=True)

            def source_archive(name: str, toolchain: str) -> None:
                source = work / name / "source"
                source.mkdir(parents=True, exist_ok=True)
                (source / "lean-toolchain").write_text(toolchain + "\n")
                with tarfile.open(work / name / "source.tar.gz", "w:gz") as tar:
                    tar.add(source, arcname="source")
                lock[name]["sha256"] = sha256(work / name / "source.tar.gz")
                shutil.copy(work / name / "source.tar.gz", archives / lock[name]["sha256"])
                (tree / "tools.lock.json").write_text(json.dumps(lock))

            # A verified Lean release, as bootstrap records one, with a stand-in for its lake.
            lean = tree / ".deps/tools" / f"lean-{lock['lean']['version']}"
            (lean / "home/bin").mkdir(parents=True)
            (lean / "archive.sha256").write_text(lock["lean"]["sha256"] + "\n")
            lake = (f'echo "lake $* | $PWD | $LAKE_ARTIFACT_CACHE" >> {log}\n'
                    "mkdir -p .lake/build/bin && touch .lake/build/bin/lean4export")
            cargo = (f'echo "cargo $* | $PWD | ${{RUSTUP_TOOLCHAIN-unset}} | $(tr -d "\\n" < rust-toolchain.toml)" '
                     f'>> {log}\nmkdir -p "$CARGO_TARGET_DIR/release" && touch "$CARGO_TARGET_DIR/release/nanoda_bin"')
            for path, body in ((lean / "home/bin/lake", lake), (stubs / "cargo", cargo)):
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_text(f"#!/bin/sh\n{body}\n")
                path.chmod(0o755)
            (lean / "tree.sha256").write_text(bootstrap_tool.tree_digest(lean) + "\n")
            toolchain = (ROOT / "lean-toolchain").read_text().strip()
            source_archive("lean4export", toolchain)
            source_archive("nanoda", toolchain)
            env = {**os.environ, "PATH": f"{stubs}:{os.environ['PATH']}", "XDG_CACHE_HOME": str(cache),
                   "RUSTUP_TOOLCHAIN": "stable"}

            def bootstrap(name: str, **extra: str) -> subprocess.CompletedProcess[str]:
                return subprocess.run(["python3", "scripts/bootstrap_tool.py", name], cwd=tree, text=True,
                                      env=env | extra, capture_output=True, check=False)

            for name, binary in (("lean4export", "lean4export"), ("nanoda", "nanoda_bin")):
                result = bootstrap(name)
                self.assertEqual(result.returncode, 0, result.stderr)
                self.assertEqual(Path(result.stdout.strip()),
                                 tree / ".deps/tools" / f"{name}-{lock[name]['version']}" / binary)
            lake_call, cargo_call = log.read_text().splitlines()
            rust = (ROOT / "rust-toolchain.toml").read_text().replace("\n", "")
            source = rf"{re.escape(str(cache.resolve()))}/dn-tool-\w+/source/source"
            self.assertRegex(lake_call, rf"^lake build lean4export \| {source} \| false$")
            self.assertRegex(cargo_call, rf"^cargo build --release --locked \| {source} \| unset \| {re.escape(rust)}$")
            self.assertEqual(list(cache.iterdir()), [])
            shutil.rmtree(tree / ".deps/tools" / f"nanoda-{lock['nanoda']['version']}")
            inside = bootstrap("nanoda", XDG_CACHE_HOME=str(tree / ".cache"))
            self.assertNotEqual(inside.returncode, 0)
            self.assertIn("is inside the repository", inside.stderr)
            shutil.rmtree(tree / ".deps/tools" / f"lean4export-{lock['lean4export']['version']}")
            source_archive("lean4export", "leanprover/lean4:v4.31.0")
            other = bootstrap("lean4export")
            self.assertNotEqual(other.returncode, 0)
            self.assertIn("is not pinned to", other.stderr)

    def test_refuses_tracked_build_outputs(self) -> None:
        function = re.search(r"^tracked_outputs\(\) \{.*?^\}", CHECK, re.MULTILINE | re.DOTALL)
        assert function is not None
        with tempfile.TemporaryDirectory() as temp:
            tree = Path(temp)
            subprocess.run(["git", "init", "-q"], cwd=tree, check=True)
            (tree / "README").write_text("")

            def tracked() -> str:
                script = f"set -euo pipefail\n{function.group(0)}\ntracked_outputs"
                return subprocess.run(["bash", "-c", script], cwd=tree, text=True, capture_output=True,
                                      check=True).stdout

            subprocess.run(["git", "add", "README"], cwd=tree, check=True)
            self.assertEqual(tracked(), "")
            for name in (".lake/build/lib/lean/DN.olean", ".deps/tools/cake", "build/x", "target/x",
                         "models/target/x", "tests/__pycache__/t.pyc", "vendor/lake/lib/lean/DN.olean",
                         "vendor/lake/lib/lean/DN.olean.private", "vendor/lake/lib/lean/DN.ilean",
                         "vendor/lake/lib/lean/DN.trace", "vendor/lake/ir/DN.c.hash", ".LAKE/X.OLEAN"):
                with self.subTest(tracked=name):
                    (tree / name).parent.mkdir(parents=True, exist_ok=True)
                    (tree / name).write_text("")
                    subprocess.run(["git", "add", "-f", name], cwd=tree, check=True)
                    self.assertIn(name, tracked())
                    subprocess.run(["git", "rm", "-q", "--cached", name], cwd=tree, check=True)
            subprocess.run(["rm", "-rf", ".git"], cwd=tree, check=True)
            script = f"set -euo pipefail\n{function.group(0)}\ntracked_outputs"
            outside = subprocess.run(["bash", "-c", script], cwd=tree, capture_output=True, check=False)
            self.assertNotEqual(outside.returncode, 0)

    def test_backend_verify_rejects_stale_build_outputs(self) -> None:
        """A pinned proof tree carrying build outputs cannot be verified.

        Upstream ignores its own `*.uo` and `*Theory.sml` files, so a stale or
        substituted theory object would otherwise pass the check and let Holmake
        treat the target as already built.
        """
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            (root / "scripts").mkdir()
            shutil.copy(ROOT / "scripts/backend.py", root / "scripts/backend.py")
            tree = root / ".deps/cakeml"
            tree.mkdir(parents=True)
            subprocess.run(["git", "init", "-q", "-b", "main", str(tree)], check=True)
            (tree / ".gitignore").write_text("*.uo\n")
            (tree / "pancake.sml").write_text("val x = 1;\n")
            env = {**os.environ, "GIT_AUTHOR_NAME": "t", "GIT_AUTHOR_EMAIL": "t@example.com",
                   "GIT_COMMITTER_NAME": "t", "GIT_COMMITTER_EMAIL": "t@example.com"}
            subprocess.run(["git", "-C", str(tree), "add", "."], check=True, env=env)
            subprocess.run(["git", "-C", str(tree), "-c", "commit.gpgsign=false",
                            "commit", "-qm", "pinned"], check=True, env=env)
            revision = subprocess.check_output(["git", "-C", str(tree), "rev-parse", "HEAD"],
                                               text=True).strip()
            (root / "backend").mkdir()
            (root / "backend/lock.json").write_text(json.dumps({
                "format": 1,
                "cakeml": {"url": "file:///none", "revision": revision},
                "patches": [],
                "semantics_sources": [{"component": "cakeml", "revision": revision,
                                       "path": "pancake.sml",
                                       "sha256": sha256(tree / "pancake.sml")}],
            }))
            verify = ["python3", str(root / "scripts/backend.py"), "verify", "cakeml"]
            clean = subprocess.run(verify, capture_output=True, text=True, check=False)
            self.assertEqual(clean.returncode, 0, clean.stderr)
            self.assertIn("no build outputs present", clean.stdout)
            # The kind of file upstream ignores: invisible to a check that only
            # looks at non-ignored files.
            (tree / "loop_liveProofTheory.uo").write_text("stale")
            stale = subprocess.run(verify, capture_output=True, text=True, check=False)
            self.assertNotEqual(stale.returncode, 0, stale.stdout)
            self.assertIn("build outputs present in the pinned tree", stale.stderr)
            self.assertIn("loop_liveProofTheory.uo", stale.stderr)
            # A whole ignored directory is one entry, and a file upstream does not
            # ignore is refused by the older check for a different reason.
            (tree / "outputs").mkdir()
            (tree / "outputs/a.uo").write_text("stale")
            (tree / "loop_liveProofTheory.uo").unlink()
            directory = subprocess.run(verify, capture_output=True, text=True, check=False)
            self.assertNotEqual(directory.returncode, 0, directory.stdout)
            self.assertIn("outputs/", directory.stderr)
            shutil.rmtree(tree / "outputs")
            (tree / "left-over.txt").write_text("not ignored")
            untracked = subprocess.run(verify, capture_output=True, text=True, check=False)
            self.assertNotEqual(untracked.returncode, 0, untracked.stdout)
            self.assertIn("untracked files outside upstream ignores", untracked.stderr)

    def test_semantics_sources_cover_the_pinned_revisions(self) -> None:
        lock = json.loads((ROOT / "backend/lock.json").read_text())
        for component in ("cakeml", "hol"):
            with self.subTest(component=component):
                recorded = {source["revision"] for source in lock["semantics_sources"]
                            if source["component"] == component}
                self.assertIn(lock[component]["revision"], recorded,
                              "the pin moved: redo the comparison and record the digests")
        # Every file the comparison cites must be recorded, and nothing else.
        table = (ROOT / "docs/pancake-semantics.md").read_text().partition("## The modelled subset")[0]
        cited = set(re.findall(r"`([\w./-]+\.sml)`", table))
        self.assertEqual(cited, {source["path"] for source in lock["semantics_sources"]})

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
        self.assertEqual(prefix.group(1), native_baseline.EXPORT_PREFIX)

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
        for script in [*sorted((ROOT / "scripts").glob("*.py")),
                       *sorted((ROOT / "tests").glob("*.py"))]:
            if script.name == here:  # this file names the flag in order to forbid it
                continue
            with self.subTest(script=script.name):
                self.assertNotIn("no_warn", script.read_text())

    def test_upstream_comparison_reports_a_changed_or_empty_record(self) -> None:
        recorded = [{"component": "hol", "path": "src/n-bit/byteScript.sml", "revision": "a" * 40,
                     "sha256": hashlib.sha256(b"upstream").hexdigest()}]
        self.assertEqual(upstream_sources.compare(recorded, lambda _: b"upstream"), [])
        self.assertEqual(upstream_sources.compare([], lambda _: b"upstream"),
                         ["no upstream source is recorded"])
        changed = upstream_sources.compare(recorded, lambda _: b"edited upstream")
        self.assertEqual(len(changed), 1)
        self.assertIn("byteScript.sml", changed[0])
        asked: list[str] = []

        def record(url: str) -> bytes:
            asked.append(url)
            return b"upstream"

        upstream_sources.compare(recorded, record)
        raw = "https://raw.githubusercontent.com/HOL-Theorem-Prover/HOL"
        self.assertEqual(asked, [f"{raw}/{'a' * 40}/src/n-bit/byteScript.sml"])

    def test_emitted_sources_match_the_golden_files(self) -> None:
        binary = ROOT / ".lake/build/bin/dn-compiler"

        def emit(target: str) -> str:
            return subprocess.run([str(binary), f"emit-{target}"], text=True, capture_output=True,
                                  check=True, timeout=600).stdout

        for name in ("region", "echo", "render"):
            with self.subTest(target=name):
                self.assertEqual(emit(name), (ROOT / "tests/golden" / f"{name}.pnk").read_text())
        # The differential fixture is 200 KB of cases; its digest catches a change just as well.
        self.assertEqual(hashlib.sha256(emit("baseline").encode()).hexdigest(),
                         "51082f8e08484077f5ad9bc2cd59f060e23a0e9381a4353353fe569dfee6113a")

    def test_emitter_has_no_build_side_effects(self) -> None:
        binary = ROOT / ".lake/build/bin/dn-compiler"
        with tempfile.TemporaryDirectory() as temp:
            first = subprocess.run([str(binary), "emit-region"], cwd=temp, check=True,
                                   text=True, capture_output=True).stdout
            second = subprocess.run([str(binary), "emit-region"], cwd=temp, check=True,
                                    text=True, capture_output=True).stdout
            self.assertEqual(first, second)
            self.assertEqual(list(Path(temp).iterdir()), [])
            self.assertTrue(first.startswith("export fun dn_region("))
            result = subprocess.run([str(binary), "unknown"], capture_output=True, check=False)
            self.assertEqual(result.returncode, 2)
