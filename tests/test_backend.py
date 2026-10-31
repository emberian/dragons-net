# SPDX-License-Identifier: AGPL-3.0-or-later
"""The backend lanes on disposable trees with stand-ins for the prover; nothing here builds a proof."""
from __future__ import annotations

import contextlib
import io
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import tempfile
from typing import Any, ClassVar
import unittest

from gatekit import ROOT, script, sha256

backend = script("backend")
# Stand-ins that write down how they were called. The one for Holmake prints what the scripts in
# its directory print, as the prover does when it builds them, unless it is to stay silent.
RECORDER = """import os
import sys
from pathlib import Path
with open(os.environ["DN_TEST_CALLS"], "a") as calls:
    print(Path(sys.argv[0]).stem, *sys.argv[1:], file=calls)
    if sys.argv[1:] == ["verify", "cakeml"]:
        print("stale output", Path(os.environ["CAKEMLDIR"], "pancake/proofs/stale.uo").exists(), file=calls)
"""
PROVER = r"""#!/usr/bin/env python3
import os
import re
import sys
from pathlib import Path
with open(os.environ["DN_TEST_CALLS"], "a") as calls:
    print("Holmake", *sys.argv[1:], "|", Path.cwd(), "|", os.environ.get("POLY_CLINE_OPTIONS", ""), file=calls)
if not os.environ.get("DN_TEST_SILENT_PROVER"):
    for source in Path.cwd().glob("*Script.sml"):
        print(*re.findall(r'print "([^"]*)\\n"', source.read_text()), sep="\n")
"""
bootstrap_tool = script("bootstrap_tool")
check_holmake = script("check_holmake")
semantics_check = script("semantics_check")
parse_check = script("parse_check")


class Backend(unittest.TestCase):
    """The backend lanes: the proof chain, the bootstrap, and the gates around Holmake."""

    def test_holmake_gate_reads_the_job_logs_as_well(self) -> None:
        """A parallel Holmake prints a status word and writes the details to a log file.

        Reading only the captured standard output would therefore see nothing, so
        each way of recording a cheat, an oracle tag or a cache hit is checked here.
        """
        with tempfile.TemporaryDirectory() as temp:
            work = Path(temp)
            tree = work / "cakeml"
            proofs = tree / "pancake/proofs"
            (proofs / ".hol/logs").mkdir(parents=True)
            (proofs / ".hol/objs").mkdir(parents=True)
            # Holmake writes its objects to `.hol/objs`, not beside the sources, and the lane
            # names the target as the source directory plus its name.
            built = proofs / "pan_to_targetProofTheory.uo"
            obj = proofs / ".hol/objs" / built.name
            obj.write_text("theory")
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
            self.assertTrue(check_holmake.problems(output, tree, 1, built, obj.stat().st_mtime + 60),
                            "a target older than the run was accepted")
            shutil.rmtree(proofs / ".hol")
            self.assertTrue(check_holmake.problems(output, tree, 2, built, 0.0),
                            "a parallel build with no job logs was accepted")
            # Nothing was built at all: the name alone must not clear the run.
            self.assertTrue(check_holmake.problems(output, tree, 1, built, 0.0),
                            "a target that exists nowhere was accepted")
            # An older Holmake left the object beside the source, which is still accepted.
            built.write_text("theory")
            self.assertEqual(check_holmake.problems(output, tree, 1, built, 0.0), [])
            self.assertTrue(check_holmake.problems(output, tree, 1, tree / "missing.uo", 0.0))

    def test_backend_refuses_a_target_that_is_an_option(self) -> None:
        """`DN_BACKEND_TARGET` reaches Holmake as an argument; `--fast` cheats every tactic."""
        with tempfile.TemporaryDirectory() as temp:
            tree = Path(temp) / "dn"
            (tree / "scripts").mkdir(parents=True)
            for name in ("check_backend.sh", "backend_lane.sh"):
                shutil.copy(ROOT / "scripts" / name, tree / "scripts")
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

    def test_backend_refuses_a_prover_built_by_another_compiler(self) -> None:
        """The prover records what built it; a prover built by anything else is refused."""
        poly, holdir = Path("/tools/polyml-v5.9.2/bin/poly"), Path("/deps/hol")
        record = f'val HOLDIR = "{holdir}"\nval MOSMLDIR = ""\nval POLY = "{poly}"\n'
        self.assertIn("built with the pinned", backend.check_record(record, poly, holdir))
        for broken in (None, record.replace(str(poly), "/usr/bin/poly"),
                       record.replace(str(holdir), "/somewhere/else/hol"),
                       "val MOSMLDIR = \"\"\n"):
            with self.subTest(record=broken), self.assertRaises(SystemExit) as refusal:
                backend.check_record(broken, poly, holdir)
            self.assertRegex(str(refusal.exception), "rebuild|build it")
        pin = json.loads((ROOT / "tools.lock.json").read_text())["polyml"]
        self.assertTrue(pin["url"].startswith("https://github.com/polyml/polyml/archive/"))
        self.assertIn(pin["revision"], pin["url"])
        self.assertRegex(pin["sha256"], r"\A[0-9a-f]{64}\Z")
        # Poly/ML detects GMP unless it is told: the same source would otherwise give a
        # different arbitrary-precision backend on a machine that has its headers.
        source = (ROOT / "scripts/bootstrap_tool.py").read_text()
        self.assertIn("--without-gmp", source)
        self.assertIn("--enable-intinf-as-int", source)

    def test_tag_checks_ask_the_prover_itself(self) -> None:
        """Each tag check reads its theorem's own tag, from a theory built outside both pinned
        trees; what the lanes do with it, `test_backend_lanes_run_their_steps_in_order` runs."""
        checks = {"tagcheck/dnTagCheckScript.sml": ("pan_to_targetProofTheory", "pan_to_target_compile_semantics",
                                                    "INCLUDES = $(CAKEMLDIR)/pancake/proofs"),
                  "bootstrap-tagcheck/dnBootstrapTagCheckScript.sml": (
                      "x64BootstrapTheory", "Thm.tag compiler64_compiled",
                      "INCLUDES = $(CAKEMLDIR)/compiler/bootstrap/compilation/x64/64")}
        for path, (theory, theorem, includes) in checks.items():
            with self.subTest(check=path):
                source = (ROOT / "backend" / path).read_text()
                self.assertIn(f"open HolKernel boolLib {theory};", source)
                self.assertIn(theorem, source)
                # Upstream's own criterion: a theorem read from disk carries DISK_THM and nothing else.
                self.assertIn("Tag.isDisk tag", source)
                self.assertIn("raise Fail", source)
                self.assertIn(includes, (ROOT / "backend" / path).with_name("Holmakefile").read_text())

    def test_backend_lanes_refuse_options_from_the_environment(self) -> None:
        """A job count, a heap size or Holmake's option variables are read before anything runs.

        Each reaches Holmake or the prover's command line, where anything else is an option:
        `--fast` turns tactics into oracles, and a word naming an object file is loaded and run.
        """
        base = {key: value for key, value in os.environ.items()
                if key not in ("CLINE_OPTIONS", "POLY_CLINE_OPTIONS", "DN_BUILD_JOBS",
                               "DN_POLY_MINHEAP", "DN_BACKEND_TARGET")}
        lanes = {
            "check_backend.sh": ("DN BACKEND:", [
                {"DN_BUILD_JOBS": "0"}, {"DN_BUILD_JOBS": "--fast"}, {"DN_BUILD_JOBS": "2 --fast"},
                {"CLINE_OPTIONS": "--fast"}, {"POLY_CLINE_OPTIONS": "--minheap 1G"}]),
            "check_semantics.sh": ("DN SEMANTICS:", [
                {"DN_BUILD_JOBS": "0"}, {"DN_BUILD_JOBS": "--fast"}, {"CLINE_OPTIONS": "--fast"},
                {"POLY_CLINE_OPTIONS": "--minheap 1G"}]),
            "bootstrap_cake.sh": ("DN BOOTSTRAP:", [
                {"DN_BUILD_JOBS": "0"}, {"DN_BUILD_JOBS": "--fast"},
                {"DN_POLY_MINHEAP": "8G /tmp/evil.uo"}, {"DN_POLY_MINHEAP": "--fast"},
                {"DN_POLY_MINHEAP": "8T"}, {"CLINE_OPTIONS": "--fast"}]),
        }
        with tempfile.TemporaryDirectory() as temp:
            tree = Path(temp) / "dn"
            (tree / "scripts").mkdir(parents=True)
            shutil.copy(ROOT / "scripts/backend_lane.sh", tree / "scripts")
            for lane, (prefix, refused) in lanes.items():
                shutil.copy(ROOT / "scripts" / lane, tree / "scripts")
                for extra, ok in [(env, False) for env in refused] + [({"DN_BUILD_JOBS": "3"}, True)]:
                    with self.subTest(lane=lane, env=extra):
                        result = subprocess.run(["bash", f"scripts/{lane}"], cwd=tree,
                                                env={**base, **extra}, capture_output=True,
                                                text=True, check=False, timeout=60)
                        # The accepted run stops later, at the missing checkout, not here.
                        self.assertEqual(result.returncode == 2 and prefix in result.stderr,
                                         not ok, result.stderr)

    def test_stack_permissions_are_read_from_the_file(self) -> None:
        """The stack check reads the program headers, so it cannot be satisfied by a flag."""
        with tempfile.TemporaryDirectory() as temp:
            source = Path(temp) / "main.c"
            source.write_text("int main(void) { return 0; }\n")
            for flag, expected in (("noexecstack", "RW"), ("execstack", "RWE")):
                binary = Path(temp) / flag
                subprocess.run(["cc", str(source), "-o", str(binary), f"-Wl,-z,{flag}"],
                               check=True, capture_output=True, timeout=60)
                self.assertEqual(backend.stack_permissions(binary), expected)
            with self.assertRaises(SystemExit):
                backend.stack_permissions(source)

    def test_bootstrap_packaging_refuses_what_it_would_record_wrongly(self) -> None:
        """An executable stack or a wrong hello world stops the record; a good build is copied."""
        makefile = ("cake:\n\t$(CC) main.c -o cake $(LDFLAGS) $(STACK)\n"
                    "test-hello.cake:\n\t$(CC) hello.c -o test-hello.cake $(LDFLAGS)\n")
        cases = (("", 'puts("Hello!");', None),
                 ("STACK = -Wl,-z,execstack\n", 'puts("Hello!");', "stack is RWE"),
                 ("", 'puts("Hello, world");', "hello world printed"))
        for stack, hello, refusal in cases:
            with self.subTest(refusal=refusal), tempfile.TemporaryDirectory() as temp:
                target, out = Path(temp) / "x64", Path(temp) / "out"
                target.mkdir()
                out.mkdir()
                (target / "Makefile").write_text(stack + makefile)
                (target / "main.c").write_text("int main(void) { return 0; }\n")
                (target / "hello.c").write_text(f"#include <stdio.h>\nint main(void) {{ {hello} }}\n")
                (target / "cake.S").write_text("generated\n")
                (target / "basis_ffi.c").write_text("ffi\n")
                (out / "holmake.log").write_text("log\n")
                if refusal is None:
                    report = backend.package_bootstrap(12, 3, target, out)
                    self.assertEqual((report["stack"], report["hello_world"], report["jobs"]),
                                     ("RW", "Hello!", 3))
                    self.assertEqual(report["cake_sha256"], backend.digest(target / "cake"))
                    self.assertEqual((out / "cake.S").read_text(), "generated\n")
                    self.assertEqual(json.loads((out / "report.json").read_text()), report)
                else:
                    with self.assertRaises(SystemExit) as stopped:
                        backend.package_bootstrap(12, 3, target, out)
                    self.assertIn(refusal, str(stopped.exception))
                    self.assertFalse((out / "report.json").exists())

    def test_bootstrap_record_names_the_pinned_inputs(self) -> None:
        """The recorded bootstrap was made from what is pinned now, so a pin cannot move alone.

        The compiler takes hours to build and runs outside CI, so the evidence is a record of one
        run; a CakeML, HOL, patch or Poly/ML pin that moves without a new run would leave it
        describing a compiler that nothing here builds any more.
        """
        record = json.loads((ROOT / "backend/bootstrap-record.json").read_text())
        rerun = "run scripts/bootstrap_cake.sh again and copy build/bootstrap/report.json here"
        self.assertEqual(record["cakeml_revision"], backend.LOCK["cakeml"]["revision"], rerun)
        self.assertEqual(record["hol_revision"], backend.LOCK["hol"]["revision"], rerun)
        self.assertEqual(record["patches"],
                         [{"path": p["path"], "sha256": p["sha256"]} for p in backend.LOCK["patches"]],
                         rerun)
        polyml = json.loads((ROOT / "tools.lock.json").read_text())["polyml"]
        self.assertEqual(record["polyml"],
                         {key: polyml[key] for key in ("version", "revision", "sha256")}, rerun)
        self.assertEqual((record["stack"], record["hello_world"], record["link_flags"]),
                         ("RW", "Hello!", backend.LINK_FLAGS))
        for field in ("holmake_log_sha256", "cake_S_sha256", "basis_ffi_sha256", "cake_sha256"):
            self.assertRegex(record[field], r"\A[0-9a-f]{64}\Z")

    def test_backend_lanes_run_their_steps_in_order(self) -> None:
        """Both lanes, on a tree whose prover, pin checks and log gate write down how they were
        called: the tree is cleaned before its pin is checked and the prover is asked what built it
        before it runs; every Holmake run goes through the gate; the tag check builds its theory
        outside the pinned trees and needs the sentence its script prints; and the bootstrap
        packages nothing before that. A prover that prints nothing fails both lanes."""
        with tempfile.TemporaryDirectory() as temp:
            tree = Path(temp).resolve() / "dn"
            (tree / "scripts").mkdir(parents=True)
            for name in ("check_backend.sh", "bootstrap_cake.sh", "check_semantics.sh", "backend_lane.sh"):
                shutil.copy(ROOT / "scripts" / name, tree / "scripts")
            for name in ("tagcheck", "bootstrap-tagcheck", "semantics"):
                shutil.copytree(ROOT / "backend" / name, tree / "backend" / name)
            for name in ("backend", "check_holmake", "semantics_check"):
                (tree / f"scripts/{name}.py").write_text(RECORDER)
            prover = tree / ".deps/hol/bin/Holmake"
            prover.parent.mkdir(parents=True)
            prover.write_text(PROVER)
            prover.chmod(0o755)
            cakeml = tree / ".deps/cakeml"
            subprocess.run(["git", "init", "-q", str(cakeml)], check=True)
            (cakeml / ".gitignore").write_text("*.uo\n")
            # Directories of the checkout are tracked; its build outputs are not.
            for directory in ("pancake/proofs", "pancake/semantics", "compiler/bootstrap/compilation/x64/64"):
                (cakeml / directory).mkdir(parents=True)
                (cakeml / directory / "Holmakefile").write_text("")
            subprocess.run(["git", "-C", str(cakeml), "add", "-A"], check=True)
            calls = Path(temp) / "calls"
            base = {key: value for key, value in os.environ.items()
                    if key not in ("CLINE_OPTIONS", "POLY_CLINE_OPTIONS", "DN_BACKEND_TARGET")}
            base |= {"DN_BUILD_JOBS": "3", "DN_POLY_MINHEAP": "4G", "DN_TEST_CALLS": str(calls)}
            proofs, x64 = cakeml / "pancake/proofs", cakeml / "compiler/bootstrap/compilation/x64/64"
            semantics, states = cakeml / "pancake/semantics", tree / "backend/semantics/states.txt"
            evaluated = ("dnShowTheory.uo dnModelTheory.uo dnModelShowTheory.uo dnStatesTheory.uo "
                         "dnModelStatesTheory.uo")
            build = tree / "build"
            expected = {
                "check_backend.sh": [
                    "backend verify hol", "backend built-with hol", "backend verify cakeml",
                    "stale output False",
                    f"Holmake -j 3 pan_to_targetProofTheory.uo | {proofs} | ",
                    (f"check_holmake --output {build}/backend-holmake.log --tree {cakeml} --jobs 3 "
                     f"--built {proofs}/pan_to_targetProofTheory.uo --since T"),
                    f"Holmake -j 1 --no_prereqs dnTagCheckTheory.uo | {build}/tagcheck | ",
                    (f"check_holmake --output {build}/backend-tagcheck.log --tree {build}/tagcheck --jobs 1 "
                     f"--built {build}/tagcheck/dnTagCheckTheory.uo --since T")],
                "bootstrap_cake.sh": [
                    "backend verify hol", "backend built-with hol", "backend verify cakeml",
                    "stale output False",
                    (f"Holmake --minheap 2G -j 3 --no-cache --qof cake.S x64BootstrapTheory.uo | {x64} | "
                     "--minheap 4G"),
                    (f"check_holmake --output {build}/bootstrap/holmake.log --tree {cakeml} --jobs 3 "
                     f"--built {x64}/cake.S --since T"),
                    (f"Holmake --minheap 2G -j 1 --no_prereqs dnBootstrapTagCheckTheory.uo | "
                     f"{build}/bootstrap/tagcheck | --minheap 4G"),
                    (f"check_holmake --output {build}/bootstrap/tagcheck.log --tree {build}/bootstrap/tagcheck "
                     f"--jobs 1 --built {build}/bootstrap/tagcheck/dnBootstrapTagCheckTheory.uo --since T"),
                    "backend package-bootstrap --seconds T --jobs 3"],
                "check_semantics.sh": [
                    "backend verify hol", "backend built-with hol", "backend verify cakeml",
                    "stale output False",
                    f"Holmake -j 3 panSemTheory.uo | {semantics} | ",
                    (f"check_holmake --output {build}/semantics-holmake.log --tree {cakeml} --jobs 3 "
                     f"--built {semantics}/panSemTheory.uo --since T"),
                    f"semantics_check write {states} {build}/semantics",
                    f"Holmake -j 1 --no_prereqs dnModelProofTheory.uo {evaluated} | {build}/semantics | ",
                    (f"check_holmake --output {build}/semantics-eval.log --tree {build}/semantics --jobs 1 "
                     f"--built {build}/semantics/dnModelStatesTheory.uo --since T"),
                    f"semantics_check compare {states} {build}/semantics-eval.log",
                    f"semantics_check write {states} {build}/semantics-defect --defect",
                    f"Holmake -j 1 --no_prereqs {evaluated} | {build}/semantics-defect | ",
                    (f"check_holmake --output {build}/semantics-defect.log --tree {build}/semantics-defect "
                     f"--jobs 1 --built {build}/semantics-defect/dnModelStatesTheory.uo --since T"),
                    f"semantics_check compare {states} {build}/semantics-defect.log --expect-differences"],
            }
            for lane, steps in expected.items():
                for silent in (False, True):
                    with self.subTest(lane=lane, silent=silent):
                        (proofs / "stale.uo").write_text("")
                        calls.write_text("")
                        env = base | ({"DN_TEST_SILENT_PROVER": "1"} if silent else {})
                        result = subprocess.run(["bash", f"scripts/{lane}"], cwd=tree, env=env, text=True,
                                                capture_output=True, check=False, timeout=60)
                        made = re.sub(r"--(since|seconds) \d+", r"--\1 T", calls.read_text()).splitlines()
                        if silent and lane == "check_semantics.sh":
                            # The proof's theory reports on its own tags, and the lane needs that.
                            self.assertEqual(result.returncode, 2, result.stderr)
                            self.assertIn("did not report on its tags", result.stderr)
                            self.assertEqual(made, steps[:len(made)])
                        elif silent:
                            self.assertEqual(result.returncode, 1, result.stderr)
                            self.assertIn("the tag check did not report on the theorem", result.stderr)
                            self.assertEqual(made, steps[:len(made)])
                            self.assertNotIn("package-bootstrap", "".join(made))
                        else:
                            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
                            self.assertEqual(made, steps)

    def test_backend_workflow_runs_the_lane_it_names(self) -> None:
        """Every path that triggers the lane exists, and the job runs the lane's own script."""
        workflow = (ROOT / ".github/workflows/backend.yml").read_text()
        blocks = re.findall(r"^  (push|pull_request):\n(?:.*\n)*?    paths:\n((?:      - \S+\n)+)",
                            workflow, re.MULTILINE)
        self.assertEqual(len(blocks), 2, workflow)
        listed = [sorted(block.split()[1::2]) for _, block in blocks]
        # One of the two lists alone would leave half the lane's triggers behind.
        self.assertEqual(listed[0], listed[1])
        self.assertIn("backend/**", listed[0])
        for path in listed[0]:
            with self.subTest(path=path):
                self.assertTrue(list(ROOT.glob(path)), f"{path} matches nothing in the tree")
        self.assertIn("bash scripts/check_backend.sh", workflow)
        self.assertIn("bash scripts/check_semantics.sh", workflow)
        self.assertIn("bash scripts/check_parse.sh", workflow)
        self.assertIn("scripts/backend.py build hol", workflow)
        # A target that passed on the same inputs is not built again: the proof's key reads what the
        # paths name, and the parser's what its lane reads, the Lean tree that prints the programs too.
        # The Lean files among the paths trigger the parser's job alone, whose key holds the Lean tree.
        proof, parser = workflow.split("\n  parser:\n", 1)
        keyed = re.findall(r"HEAD:(\S+)", proof)
        self.assertEqual(sorted(keyed), sorted(p.removesuffix("/**") for p in listed[0] if not p.startswith("lean/")))
        self.assertLessEqual({"lean/DN/Compiler/Parse.lean", "lean/DN/Compiler/Checked.lean",
                              "lean/DN/Compiler/Syntax.lean"}, set(listed[0]))
        self.assertLessEqual({"backend", "lean", "scripts/check_parse.sh", "scripts/parse_check.py",
                              "scripts/parser_contract.py", "scripts/lanes.py"}, set(re.findall(r"HEAD:(\S+)", parser)))
        # The compiler is verified against its pin on every run, not restored with the prover.
        self.assertNotIn(".deps/tools", workflow)
        cached = re.search(r"path: (\S+)\n\s+key: \$\{\{ steps\.pins\.outputs\.key \}\}", workflow)
        self.assertIsNotNone(cached)

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


class Semantics(unittest.TestCase):
    """The HOL lane's terms and comparison, without the prover: what the theory evaluates is
    built from the corpus's inputs alone, and the comparison refuses each way of disagreeing."""

    corpus = semantics_check.corpus(ROOT / "backend/semantics/states.txt")

    @staticmethod
    def log(cases: list[dict[str, str]]) -> str:
        """What both theories print when panSem and dnModel agree with the model on every case."""
        out = []
        for mark in (semantics_check.PANSEM, semantics_check.MODEL):
            for case in cases:
                if "WRITE" in case:
                    out += [f"{mark} WRITE {case['WRITE']}", f"WRESULT {case['WRESULT']}"]
                else:
                    out += [f"{mark} CASE {case['CASE']}", *(f"{f} {case[f]}" for f in semantics_check.FIELDS)]
                out.append("DNEND")
        return "<<HOL message>>\n" + "\n".join(out) + "\nExporting theory\n"

    @staticmethod
    def moved(case: dict[str, str], field: str) -> str:
        """Another value of an input field, in the field's own form."""
        value = case[field]
        others = {"BE": "0" if value == "1" else "1",
                  "PROG": "(skip)" if value != "(skip)" else "(ret (const 0))",
                  "CODE": "((f () (skip)))" if value == "()" else "()",
                  "WBYTES": "00" if value == "-" else value + "00"}
        if field in ("CLOCK", "BASE", "WADDR"):
            return str(int(value) + 1)
        if field in others or field == "WBE":
            return others["BE" if field == "WBE" else field]
        extra = {"LOCALS": "zz=1", "MEM": "4096=1", "WMEM": "4096=1", "DOM": "4096", "WDOM": "4096",
                 "ANSWERS": "ret:00", "NAMES": "zz"}
        if field in extra:
            return f"{value}{';' if field == 'ANSWERS' else ','}{extra[field]}" if value else extra[field]
        return value + "-moved"

    def test_terms_read_only_the_inputs(self) -> None:
        """The model's answer is not in the term HOL evaluates, so HOL cannot copy it; every input is."""
        answers = (*semantics_check.FIELDS, "WRESULT")
        for case in self.corpus:
            inputs = semantics_check.WRITE_INPUTS if "WRITE" in case else semantics_check.INPUTS
            for convert, ops in ((semantics_check.case_term, semantics_check.BINOPS),
                                 (semantics_check.model_case_term, semantics_check.MODEL_BINOPS)):
                term = convert(case, ops)
                blanked = {k: ("" if k in answers else v) for k, v in case.items()}
                self.assertEqual(convert(blanked, ops), term)
                for field in inputs:
                    with self.subTest(case=case.get("CASE") or case.get("WRITE"), field=field, by=convert.__name__):
                        moved = {**case, field: self.moved(case, field)}
                        self.assertNotEqual(convert(moved, ops), term)

    def test_every_case_is_evaluated_once(self) -> None:
        for model, ops, defect_ops, forms, add, sub in (
                (False, semantics_check.BINOPS, semantics_check.DEFECT,
                 ("DecCall", "ExtCall", "While", "StoreByte", "write_bytearray", "Oracle_final"), "asm$Add", "asm$Sub"),
                (True, semantics_check.MODEL_BINOPS, semantics_check.MODEL_DEFECT,
                 ("PDecCall", "PExtCall", "PWhile", "PStoreByte", "dn_write_byte_array", "OFinal"), "BAdd", "BSub")):
            with self.subTest(model=model):
                script = semantics_check.script(self.corpus, ops, model=model)
                keys = re.findall(r'^val _ = answer \("([^"]*)"', script, re.MULTILINE)
                self.assertEqual(len(keys), len(self.corpus))
                self.assertEqual(len(set(keys)), len(keys))
                # The corpus reaches every statement and both kinds of case, calls among them.
                for form in forms:
                    self.assertIn(form, script)
                # The defect changes what is evaluated, and only where subtraction is.
                defect = semantics_check.script(self.corpus, defect_ops, model=model)
                self.assertNotEqual(defect, script)
                self.assertEqual(defect.replace(add, sub).count(sub), script.replace(add, sub).count(sub))

    def test_comparison_refuses_each_disagreement(self) -> None:
        agreeing = self.log(self.corpus)
        self.assertEqual(semantics_check.differences(self.corpus, agreeing), [])
        first = next(c for c in self.corpus if "CASE" in c)
        key = f"DNCASE CASE {first['CASE']}\n"
        block = agreeing[agreeing.index(key):agreeing.index("DNEND\n", agreeing.index(key)) + 6]
        wrong = {
            "a field": agreeing.replace(key + f"RESULT {first['RESULT']}", key + "RESULT unreachable", 1),
            "a case missing": agreeing.replace(block, ""),
            "a case not in the corpus": agreeing + "DNCASE CASE extra\nRESULT none\nDNEND\n",
            "an unreduced term": agreeing.replace(block, key + "UNREDUCED\nDNEND\n"),
        }
        for what, log in wrong.items():
            with self.subTest(what=what):
                self.assertNotEqual(semantics_check.differences(self.corpus, log), [])
        with self.assertRaises(SystemExit):
            semantics_check.differences(self.corpus, agreeing + block)

    def test_compare_reads_both_theories(self) -> None:
        """A case wrong in either theory's answers fails the comparison, and names that theory."""
        agreeing = self.log(self.corpus)
        first = next(c for c in self.corpus if "CASE" in c)
        with tempfile.TemporaryDirectory() as temp:
            corpus, log = Path(temp) / "states.txt", Path(temp) / "log"
            corpus.write_text((ROOT / "backend/semantics/states.txt").read_text())

            def compare(text: str) -> subprocess.CompletedProcess[str]:
                log.write_text(text)
                return subprocess.run(["python3", "-P", str(ROOT / "scripts/semantics_check.py"), "compare",
                                       str(corpus), str(log)], capture_output=True, text=True, check=False)

            self.assertEqual(compare(agreeing).returncode, 0)
            for mark, who in ((semantics_check.PANSEM, "panSem's evaluate"),
                              (semantics_check.MODEL, "dnModel's dn_sem")):
                key = f"{mark} CASE {first['CASE']}\n"
                start = agreeing.index(key)
                block = agreeing[start:agreeing.index("DNEND\n", start) + 6]
                wrong = agreeing.replace(key + f"RESULT {first['RESULT']}", key + "RESULT unreachable", 1)
                for what, text in {"wrong": wrong, "missing": agreeing.replace(block, ""),
                                   "twice": agreeing + block}.items():
                    with self.subTest(mark=mark, what=what):
                        result = compare(text)
                        self.assertEqual(result.returncode, 1, result.stdout)
                        if what != "twice":
                            self.assertIn(who, result.stderr)

    def test_defect_has_to_show_where_subtraction_is(self) -> None:
        agreeing = self.log(self.corpus)

        def changed(case: dict[str, str]) -> str:
            key = f"DNCASE CASE {case['CASE']}\n"
            return agreeing.replace(key + f"RESULT {case['RESULT']}", key + "RESULT unreachable", 1)

        def dropped(case: dict[str, str]) -> str:
            key = f"DNCASE CASE {case['CASE']}\n"
            start = agreeing.index(key)
            return agreeing[:start] + agreeing[agreeing.index("DNEND\n", start) + 6:]

        states = [c for c in self.corpus if "CASE" in c]
        subtracting = next(c for c in states if "(sub " in c["PROG"])
        other = next(c for c in states if "(sub " not in c["PROG"] + c["CODE"])
        self.assertIsNone(semantics_check.defect_unseen(self.corpus, changed(subtracting)))
        # The changes above are to the panSem theory's answers; dnModel's are untouched.
        self.assertIsNotNone(semantics_check.defect_unseen(self.corpus, changed(subtracting), semantics_check.MODEL))
        for what, log in {"no difference": agreeing, "a difference without subtraction": changed(other),
                          "a case unanswered": dropped(subtracting)}.items():
            with self.subTest(what=what):
                self.assertIsNotNone(semantics_check.defect_unseen(self.corpus, log))


class ParseCheck(unittest.TestCase):
    """What scripts/parse_check.py makes of the trees the parser's theorems give, with no prover."""

    P = "panLang$"
    program: ClassVar[dict[str, Any]] = {"name": "dn_f", "params": ["a"], "body": [["return", ["Var", "a"]]],
                                         "functions": [], "source": "export fun dn_f(1 a) {\n  return a;\n}\n"}

    def function(self, body: list[Any], export: bool = True) -> list[Any]:
        return [self.P + "Function", {"name": "dn_f", "inline": False, "export": export,
                                       "params": [["pair$,", "a", [self.P + "One"]]], "body": body,
                                       "return": [self.P + "One"]}]

    def var(self, kind: str = "Local") -> list[Any]:
        return [self.P + "Var", [self.P + kind], "a"]

    def test_the_lowered_tree_is_taken(self) -> None:
        self.assertEqual(parse_check.compared(self.program, [self.function([self.P + "Return", self.var()])]), 1)

    def test_other_trees_are_refused(self) -> None:
        returned = {
            "a global": self.var("Global"),
            "one operand": [self.P + "Op", ["asm$Add"], [self.var()]],
            "an operator of another theory": [self.P + "Op", ["other$Add"], [self.var(), self.var()]],
            "a sum": [self.P + "Op", ["asm$Add"], [self.var(), self.var()]],
            "a load of two words": [self.P + "Load", [self.P + "Comb", []], self.var()],
        }
        for name, e in returned.items():
            with self.subTest(name), self.assertRaises(parse_check.LaneError):
                parse_check.compared(self.program, [self.function([self.P + "Return", e])])

    def test_export_follows_the_text(self) -> None:
        with self.assertRaisesRegex(parse_check.LaneError, "which its text does not say"):
            parse_check.compared(self.program, [self.function([self.P + "Return", self.var()], export=False)])

    def test_a_record_of_another_shape_is_refused(self) -> None:
        returned = [self.P + "Return", self.var()]
        for name, field in {"inlined": ("inline", True), "export not a boolean": ("export", 1)}.items():
            decl = self.function(returned)
            decl[1][field[0]] = field[1]
            with self.subTest(name), self.assertRaisesRegex(parse_check.LaneError, "inlined or returning"):
                parse_check.compared(self.program, [decl])

    def test_a_shift_by_other_than_a_number_is_refused(self) -> None:
        shifted = {**self.program, "body": [["return", ["Lsl", ["Var", "a"], ["Const", 1]]]]}
        tree = [self.P + "Shift", ["ast$Lsl"], self.var(), 1]
        self.assertEqual(parse_check.compared(shifted, [self.function([self.P + "Return", tree])]), 1)
        with self.assertRaises(parse_check.LaneError):
            parse_check.compared(shifted, [self.function([self.P + "Return", [*tree[:3], 1.0]])])

    def test_a_field_twice_is_refused(self) -> None:
        with tempfile.TemporaryDirectory() as temp:
            path = Path(temp, "t.json")
            path.write_text('[{"name": "a", "name": "b"}]')
            with self.assertRaisesRegex(parse_check.LaneError, "a key twice"):
                parse_check.tree(path)

    def test_the_text_is_read_as_octets(self) -> None:
        self.assertIn('BinIO.openIn "dnParse3.pnk"', parse_check.script(3, "x"))

    def test_only_places_are_left_out(self) -> None:
        place = [self.P + "Annot", "location", "(1:1 1:2)"]
        comment = [self.P + "Annot", "@", "a comment"]
        skip = [self.P + "Skip"]
        self.assertEqual(parse_check.unplaced([self.P + "Seq", place, skip]), skip)
        kept = [self.P + "Seq", comment, skip]
        self.assertEqual(parse_check.unplaced(kept), kept)

    def compare(self, hol: list[Any], copy: list[Any], cells: list[dict[str, Any]], readings: list[Any],
                held: list[Any]) -> str:
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            files = {"trees.json": [self.program], "lean.json": [copy], "cells.json": cells,
                     "readings.json": readings, "dnParse0.json": hol, "dnParseCells.json": held}
            for name, value in files.items():
                (root / name).write_text(json.dumps(value))
            (root / "targets").write_text("dnParse0Theory.uo\ndnParseCellsTheory.uo\n")
            with contextlib.redirect_stdout(io.StringIO()) as out:
                parse_check.compare(root / "trees.json", root, False, root / "cells.json",
                                    (root / "lean.json", root / "readings.json"))
            return out.getvalue()

    def test_a_program_without_its_theory_is_refused(self) -> None:
        returned = [self.P + "Return", self.var()]
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            (root / "trees.json").write_text(json.dumps([self.program, self.program]))
            (root / "dnParse0.json").write_text(json.dumps([self.function(returned)]))
            (root / "targets").write_text("dnParse0Theory.uo\n")
            with contextlib.redirect_stdout(io.StringIO()), \
                    self.assertRaisesRegex(parse_check.LaneError, "1 theories for 2 printed programs"):
                parse_check.compare(root / "trees.json", root, False)

    def test_the_lean_parser_is_held_to_each_tree_and_refusal(self) -> None:
        place = [self.P + "Annot", "location", "(2:3 2:11)"]
        returned = [self.P + "Return", self.var()]
        hol = [self.function([self.P + "Seq", place, returned])]
        copy = [self.function(returned)]
        cell = {"tree": self.program, "reads": True, "cell": "top/left: a"}
        self.assertIn("1 cells", self.compare(hol, copy, [cell], [copy], [hol]))
        other = [self.function([self.P + "Return", self.var("Global")])]
        cases: dict[str, tuple[list[Any], list[Any]]] = {
            "a program": (other, [copy]), "a cell": (copy, [other]), "a refusal": (copy, [None])}
        for name, (program, readings) in cases.items():
            with self.subTest(name), self.assertRaisesRegex(parse_check.LaneError, "Lean parser reads it otherwise"):
                self.compare(hol, program, [cell], readings, [hol])

    def test_cells_are_read_as_the_table_says(self) -> None:
        read = [self.function([self.P + "Return", self.var()])]
        misread = [self.function([self.P + "Return", [self.P + "Const", 0]])]
        cell = {"tree": self.program, "cell": "top/left: a"}
        self.assertEqual(parse_check.cells_read([{**cell, "reads": False}, {**cell, "reads": False}],
                                                [None, misread]), 2)
        with self.assertRaisesRegex(parse_check.LaneError, "refused, which the table says is read"):
            parse_check.cells_read([{**cell, "reads": True}], [None])
        with self.assertRaisesRegex(parse_check.LaneError, "which the table says it is not"):
            parse_check.cells_read([{**cell, "reads": False}], [read])
        with self.assertRaisesRegex(parse_check.LaneError, "the parser's tree is not the lowered one"):
            parse_check.cells_read([{**cell, "reads": True}], [misread])
