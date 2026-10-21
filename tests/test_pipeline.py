# SPDX-License-Identifier: AGPL-3.0-or-later
"""The checks around the code: `check.sh` and CI, the `verify` workflow, what the repository keeps
from elsewhere, and the pinned tools; on disposable copies, never on the working tree."""
from __future__ import annotations

import hashlib
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

from gatekit import CHECK, ROOT, regressions, run, script, sha256, source_tree

bootstrap_tool = script("bootstrap_tool")
build_archive = script("build_archive")
prior_pass = script("prior_pass")
check_prose = script("check_prose")
structure = script("check_structure")
upstream_sources = script("check_upstream_sources")
verify_run = script("verify_run")


class CheckScript(unittest.TestCase):
    """`check.sh`, its stages and the chain CI runs them in."""

    def test_check_script_runs_every_gate_in_order(self) -> None:
        steps = ["LAKE_ARTIFACT_CACHE=false", "tracked=$(tracked_outputs)", "before=$(snapshot)",
                 "once check-gate", "lake build --wfail DN dn-compiler",
                 '"$(snapshot)" != "$before"', "LEAN_ABORT_ON_PANIC=1", "check_structure.py outputs",
                 '"$leanchecker" DN', "--export-list",
                 '"$nanoda" scripts/nanoda.json', f"--regressions {regressions()}"]
        positions = [CHECK.find(step) for step in steps]
        self.assertNotIn(-1, positions, dict(zip(steps, positions, strict=True)))
        self.assertEqual(positions, sorted(positions))
        self.assertIn("all) build; once check-proofs bash scripts/check.sh proofs-now; bash scripts/check_tests.sh ;;",
                      CHECK)
        self.assertIn("once check-gate python3 scripts/check_structure.py", CHECK)
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
            for script in ("check.sh", "check_tests.sh"):
                shutil.copy(ROOT / "scripts" / script, tree / "scripts" / script)

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
            for script in ("check.sh", "check_tests.sh"):
                shutil.copy(ROOT / "scripts" / script, tree / "scripts" / script)
            (tree / "tests").mkdir()
            for module in ("test_a.py", "test_once.py"):
                (tree / "tests" / module).write_text("")
            subprocess.run(["git", "init", "-q"], cwd=tree, check=True)
            subprocess.run(["git", "add", "tests"], cwd=tree, check=True)
            log = Path(temp) / "log"

            def stub(directory: Path, name: str, body: str) -> None:
                directory.mkdir(exist_ok=True)
                (directory / name).write_text(f"#!/bin/sh\n{body}\n")
                (directory / name).chmod(0o755)

            for name in ("lake", "cargo", "leanchecker", "lean"):
                stub(stubs, name, f'echo "{name} $*" >> {log}')
            stub(stubs, "python3", 'case "$1" in scripts/once.py) exit 1 ;; esac\n'
                 f'echo "python3 $*" >> {log}\n'
                 'case "$1" in scripts/measured.py) shift; exec "$@" ;; esac\n'
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
            env["DN_ONCE"] = "none"
            # One group after another, in their order.
            env["DN_PARALLEL"] = "1"
            checked = "[/sysroot/lib/lean:.lake/build/lib/lean 1]"
            expected = {
                "build": ["python3 scripts/check_structure.py",
                          "python3 scripts/measured.py lake build --wfail DN dn-compiler",
                          "lake build --wfail DN dn-compiler"],
                "proofs": ["toolchain lean --print-prefix [ ]", "python3 scripts/bootstrap_tool.py lean4export",
                           "python3 scripts/bootstrap_tool.py nanoda",
                           "python3 scripts/check_structure.py outputs",
                           f"python3 scripts/measured.py {toolchain}/leanchecker DN",
                           f"toolchain leanchecker DN {checked}",
                           f"toolchain lean --run scripts/Audit.lean --export-list {checked}",
                           f"lean4export M -- N /sysroot {checked}", "nanoda scripts/nanoda.json export",
                           f"toolchain lean --run scripts/Audit.lean --regressions {regressions()} {checked}"],
                "tests": ["python3 -m unittest discover -s tests -p test_a.py",
                          "python3 -m unittest discover -s tests -p test_once.py",
                          "cargo clippy", "cargo clippy", "cargo clippy",
                          "cargo clippy", "cargo test", "python3 scripts/check_models.py",
                          "python3 scripts/state_check.py", "python3 scripts/session_check.py",
                          "python3 scripts/abnf_check.py", "python3 scripts/article_check.py",
                          "python3 scripts/journal_check.py", "python3 scripts/fs_check.py",
                          "python3 scripts/store_check.py", "python3 scripts/runs_check.py",
                          "python3 scripts/compile_sources.py", "python3 scripts/fiu_check.py",
                          "python3 scripts/host_check.py"],
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
        self.assertEqual(list(jobs), ["lint", "build", "proofs", "tests", "test", "lanes", "native", "documents",
                                      "lazyfs"])
        chain = ["lint", "build", "proofs", "tests", "test"]
        for job, previous in zip(chain[1:], chain, strict=False):
            self.assertIn(f"needs: {previous}\n", jobs[job])
        # The native lanes run beside the tests, each in shards, all of them; a job gathers each one's
        # shards, and fails unless every shard passed. The documents are held to the stamps of both.
        self.assertIn("needs: proofs\n", jobs["lanes"])
        self.assertIn("needs: lanes\n", jobs["native"])
        lanes = (ROOT / "scripts/native_lanes.sh").read_text()
        [listed] = re.findall(r"^lanes=\(([a-z ]+)\)$", lanes, re.MULTILINE)
        sharded = " ".join(re.findall(r"^          - \{name: [a-z]+, lanes: ([a-z ]+)\}$", jobs["lanes"], re.MULTILINE))
        self.assertEqual(sorted(sharded.split()), sorted(listed.split()))
        groups = (ROOT / "scripts/check_tests.sh").read_text()
        [named] = re.findall(r"^TEST_GROUPS=\(([a-z ]+)\)$", groups, re.MULTILINE)
        sharded = " ".join(re.findall(r"^          - \{name: [a-z]+, groups: ([a-z ]+)\}$", jobs["tests"],
                                      re.MULTILINE))
        self.assertEqual(sorted(sharded.split()), sorted(named.split()))
        self.assertIn("bash scripts/native_lanes.sh $LANES\n", jobs["lanes"])
        for job in ("tests", "test"):
            self.assertNotIn("native_lanes.sh", jobs[job])
        for job, shards in (("test", "tests"), ("native", "lanes")):
            self.assertIn("    if: ${{ !cancelled() }}\n", jobs[job])
            self.assertIn(f"SHARDS: ${{{{ needs.{shards}.result }}}}\n        run: test \"$SHARDS\" = success\n",
                          jobs[job])
        self.assertIn("needs: [test, native]\n", jobs["documents"])
        self.assertIn("run: python3 scripts/check_documents.py\n", jobs["documents"])
        # Each job's record of a pass carries its own stamps, the native lanes' or all the others, and
        # names the run that holds it; the documents job takes both records by them.
        self.assertEqual(jobs["test"].count("!build/stamps/lane-*.json\n"), 2)
        self.assertEqual(jobs["native"].count(" build/stamps/lane-*.json\n"), 2)
        self.assertNotIn("build/stamps/*.json", jobs["native"])
        for job in ("test", "native"):
            self.assertIn("      record: passed-${{ steps.tree.outputs.key }}\n"
                          "      run: ${{ steps.passed.outputs.run-id || github.run_id }}\n", jobs[job])
            self.assertIn(f"name: ${{{{ needs.{job}.outputs.record }}}}\n          path: build/stamps\n"
                          f"          run-id: ${{{{ needs.{job}.outputs.run }}}}\n", jobs["documents"])
        # The LazyFS lane mounts FUSE, and the power lane on it needs the build: they run beside the
        # rest of the chain once the build has passed.
        self.assertIn("needs: build\n", jobs["lazyfs"])
        self.assertIn("python3 scripts/lazyfs_check.py", jobs["lazyfs"])
        self.assertIn("run: bash scripts/native_lanes.sh power\n", jobs["lazyfs"])
        self.assertIn("bash scripts/lint.sh", jobs["lint"])
        for job, stage in (("build", "build"), ("proofs", "proofs"), ("tests", "tests")):
            self.assertEqual(re.findall(r"scripts/check\.sh (\w+)", jobs[job]), [stage])
        # A job added or renamed here is a job the verify lane stops requiring; the shards of a matrix
        # have names of their own, and answer through the job that gathers them.
        self.assertEqual(verify_run.REQUIRED_JOBS, tuple(j for j in jobs if "    strategy:\n" not in jobs[j]))

    def test_native_lanes_run_all_or_the_named_ones(self) -> None:
        """Without names every lane runs in its order, but those that mount FUSE; with names only
        those, in the order named; a lane that fails stops the run with its status; a misspelt name is
        refused before any lane runs, or it would run nothing and pass. A lane that mounts FUSE is not
        run again on a tree it passed on."""
        scripts = {"native_check.py": "native", "native_baseline.py": "baseline", "entry_bench.py": "entry",
                   "server_check.py": "server", "framing_check.py": "framing", "grammar_check.py": "grammar",
                   "accept_check.py": "accept",
                   "session_native.py": "session",
                   "nntp_check.py": "nntp", "crash_check.py": "crash", "faults_check.py": "faults",
                   "parser_contract.py": "parser",
                   "native_fuzz.py": "fuzz", "power_check.py": "power"}
        with tempfile.TemporaryDirectory() as temp:
            tree, ran = Path(temp), Path(temp) / "ran"
            (tree / "scripts").mkdir()
            shutil.copy(ROOT / "scripts/native_lanes.sh", tree / "scripts")
            shutil.copy(ROOT / "scripts/once.py", tree / "scripts")
            subprocess.run(["git", "init", "-q", str(tree)], check=True)
            (tree / ".gitignore").write_text("build/\nran\n")
            for name, lane in scripts.items():
                (tree / "scripts" / name).write_text(
                    f"import os, sys\nwith open({str(ran)!r}, 'a') as f:\n    print({lane!r}, *sys.argv[1:], file=f)\n"
                    f"print({lane!r})\nsys.exit(3 if os.environ.get('FAILING') == {lane!r} else 0)\n")

            def lanes(*names: str, failing: str = "", once: str = "none",
                      parallel: str = "1") -> tuple[int, str, list[str]]:
                ran.unlink(missing_ok=True)
                done = subprocess.run(["bash", str(tree / "scripts/native_lanes.sh"), *names], text=True,
                                      env={**os.environ, "CAKE": "/pinned/cake", "FAILING": failing,
                                           "DN_ONCE": once, "DN_STAMPS": str(tree / "build/stamps"),
                                           "DN_PARALLEL": parallel},
                                      capture_output=True, check=False, timeout=60)
                return done.returncode, done.stderr, ran.read_text().splitlines() if ran.exists() else []

            self.assertEqual(lanes(), (0, "", ["native --cake /pinned/cake", "baseline --cake /pinned/cake",
                                              "entry check --cake /pinned/cake", "server --cake /pinned/cake",
                                              "framing --cake /pinned/cake", "grammar --cake /pinned/cake",
                                              "accept --cake /pinned/cake",
                                              "session --cake /pinned/cake",
                                              "nntp --cake /pinned/cake", "crash --cake /pinned/cake",
                                              "faults --cake /pinned/cake",
                                              "parser --cake /pinned/cake",
                                              "fuzz --cake /pinned/cake"]))
            # Each lane's output is also kept, under its own name.
            for lane in scripts.values():
                if lane != "power":
                    self.assertEqual((tree / f"build/evidence/{lane}.log").read_text(), f"{lane}\n")
            self.assertEqual(lanes("power", once=""), (0, "", ["power --cake /pinned/cake"]))
            self.assertEqual((tree / "build/evidence/power.log").read_text(), "power\n")
            status, said, run_lanes = lanes("power", once="")
            self.assertEqual((status, run_lanes), (0, []))
            self.assertIn("DN SKIP lane-power: passed on this tree", said)
            self.assertEqual(lanes("parser", "native"), (0, "", ["parser --cake /pinned/cake",
                                                                 "native --cake /pinned/cake"]))
            self.assertEqual(lanes(failing="baseline"), (3, "", ["native --cake /pinned/cake",
                                                                 "baseline --cake /pinned/cake"]))
            status, said, run_lanes = lanes("native", "parsre")
            self.assertEqual((status, run_lanes), (2, []))
            self.assertIn("no lane named 'parsre'", said)
            # Several at a time, every lane runs, a failing one among them, which fails the run.
            every = sorted(f"{lane} --cake /pinned/cake" for lane in scripts.values() if lane != "power")
            status, said, run_lanes = lanes(parallel="3")
            self.assertEqual((status, sorted(r.replace("entry check", "entry") for r in run_lanes)), (0, every))
            status, said, run_lanes = lanes(failing="baseline", parallel="3")
            self.assertEqual((status, len(run_lanes)), (1, len(every)))
            self.assertIn("the lane baseline failed", said)

    def test_a_prior_pass_is_taken_only_from_this_repository(self) -> None:
        """CI skips a job whose pass an earlier run recorded: the newest such run of this repository's
        own branches, never one of a fork, whose workflow is its own, nor an expired record."""
        def artifact(run: int, repository: int = 7, head: int = 7, expired: bool = False) -> dict[str, Any]:
            return {"expired": expired, "workflow_run": {"id": run, "repository_id": repository,
                                                         "head_repository_id": head}}

        self.assertIsNone(prior_pass.choose({"artifacts": []}, 7))
        self.assertEqual(prior_pass.choose({"artifacts": [artifact(3), artifact(5), artifact(4)]}, 7), 5)
        self.assertIsNone(prior_pass.choose({"artifacts": [artifact(5, head=9)]}, 7))
        self.assertIsNone(prior_pass.choose({"artifacts": [artifact(5, repository=9, head=9)]}, 7))
        self.assertIsNone(prior_pass.choose({"artifacts": [artifact(5, expired=True)]}, 7))
        self.assertEqual(prior_pass.choose({"artifacts": [artifact(5, head=9), artifact(2)]}, 7), 2)
        self.assertIsNone(prior_pass.choose({"artifacts": [{"expired": False}]}, 7))

    def test_ci_records_a_pass_only_after_its_steps(self) -> None:
        """Every job looks for a recorded pass first, and records its own last, so a job that
        failed half way records none."""
        workflow = (ROOT / ".github/workflows/ci.yml").read_text().split("\njobs:\n", 1)[1]
        jobs = dict(re.findall(r"^  ([a-z]+):\n(.*?)(?=\n\n  [#a-z]|\Z)", workflow, re.MULTILINE | re.DOTALL))
        shards = {name for name, job in jobs.items() if "    strategy:\n" in job}
        self.assertEqual(set(jobs) - shards, set(verify_run.REQUIRED_JOBS))
        for name, job in jobs.items():
            with self.subTest(job=name):
                steps = re.split(r"(?m)^      - ", job)[1:]
                found = [i for i, s in enumerate(steps) if 'run: python3 scripts/prior_pass.py "passed-' in s]
                recorded = [i for i, s in enumerate(steps) if "name: passed-${{" in s]
                self.assertEqual(len(found), 1)
                if name in shards:
                    # A shard records no pass: the job that gathers the shards does, once all passed.
                    self.assertEqual(recorded, [])
                    self.assertTrue(all("if:" in s for s in steps[found[0] + 1:]))
                    continue
                self.assertEqual(len(recorded), 1)
                # Only the build's archive goes up either way: a later job of the run needs it.
                self.assertTrue(all("if:" in s or "name: lean-build" in s for s in steps[found[0] + 1:recorded[0] + 1]))
                self.assertTrue(all("upload-artifact" in s or "lean-build" in s
                                    for s in steps[recorded[0] + 1:]))

    def test_prose_is_held_to_its_limits(self) -> None:
        """A paragraph, a list item, a sentence and a table cell each over its limit are refused, each at
        its line; a code span counts as one word, code blocks and headings not at all, and short text
        passes."""
        def text(n: int) -> str:
            return " ".join(["Word"] + ["word"] * (n - 1))

        self.assertEqual(check_prose.problems(f"# {text(99)}\n\n{text(40)}.\n\n| {text(40)} | b |\n| --- | - |\n"), [])
        self.assertEqual(check_prose.problems(f"```\n{text(99)}\n```\n`{text(99)}` {text(44)}.\n"), [])
        long = check_prose.problems(f"{text(30)}. {text(31)}.\n\n- {text(40)}.\n- {text(46)}.\n\n| {text(41)} |\n"
                                    f"\n`a` `b` {text(44)}.\n")
        self.assertEqual([p.split(":")[0] for p in long], ["line 1", "line 4", "line 6", "line 8"])
        self.assertIn("a paragraph of 61 words", long[0])
        self.assertIn("a sentence of 46 words", long[1])
        self.assertIn("a cell of 41 words", long[2])
        self.assertIn("a sentence of 46 words", long[3])
        # A sentence ends where a capital, a digit or code follows its full stop, not elsewhere.
        self.assertEqual(check_prose.sentences("One. Two e.g. three. 4 x. `y` z."), ["One.", "Two e.g. three.", "4 x.",
                                                                              "`y` z."])
        # Lint holds every Markdown file to them but the records and the files listed as not yet brought.
        lint = (ROOT / "scripts/lint.sh").read_text()
        self.assertIn("| xargs -0 python3 -P scripts/check_prose.py", lint)
        self.assertIn("git ls-files -z '*.md' ':!:migration/' ':!:docs/decisions/' ':!:docs/reviews/'", lint)

    def test_every_native_lane_also_runs_alone(self) -> None:
        """CI runs the native lanes one after another in one checkout, where a lane can lean on what
        an earlier one left in build/; the nightly run starts each on a fresh machine, always."""
        [listed] = re.findall(r"^lanes=\(([a-z ]+)\)$", (ROOT / "scripts/native_lanes.sh").read_text(),
                              re.MULTILINE)
        nightly = (ROOT / ".github/workflows/scheduled.yml").read_text()
        [job] = re.findall(r"^  lanes-alone:\n(.*?)\n\n", nightly, re.MULTILINE | re.DOTALL)
        [alone] = re.findall(r"^        lane: \[([a-z, ]+)\]$", job, re.MULTILINE)
        self.assertEqual(alone.split(", "), listed.split())
        self.assertIn('run: bash scripts/native_lanes.sh "${LANE}"', job)
        self.assertNotIn("if:", job)

    def test_checkers_cover_what_decides_the_checks(self) -> None:
        """The tests stage runs code from the change; what it may not change is this."""
        function = re.search(r"^checkers\(\) \{.*?^\}", (ROOT / "scripts/check_tests.sh").read_text(),
                             re.MULTILINE | re.DOTALL)
        assert function is not None
        with tempfile.TemporaryDirectory() as temp:
            tree = Path(temp)
            for name in ("scripts/check.sh", "tests/test_pipeline.py", ".github/workflows/ci.yml",
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
            for name in ("scripts/check.sh", "tests/test_pipeline.py", ".github/workflows/ci.yml",
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


class Verify(unittest.TestCase):
    """The `verify` workflow, which judges a run from outside the change."""

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


class Sources(unittest.TestCase):
    """What the repository keeps from elsewhere: the snapshot, the RFCs, licences and provenance."""

    def test_preserved_snapshot_is_unchanged(self) -> None:
        """The manifest calls part of the tree a preserved reference; that has to be true."""
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            (root / "docs").mkdir(parents=True)
            (root / "migration").mkdir()
            kept = root / "migration/kept.rs"
            kept.write_text("fn main() {}\n")
            entry = {"destination": "migration/kept.rs", "source_sha256": sha256(kept),
                     "changes": "Unmodified migration reference; not an active dn build target."}
            manifest = root / "docs/provenance.json"
            manifest.write_text(json.dumps({"files": [entry]}))
            self.assertEqual(structure.snapshot_errors(root), [])
            kept.write_text("fn main() { }\n")
            self.assertIn("preserved reference changed", " ".join(structure.snapshot_errors(root)))
            kept.unlink()
            self.assertIn("preserved reference is missing", " ".join(structure.snapshot_errors(root)))
            # A manifest that records nothing must not pass as a check that found nothing.
            manifest.write_text(json.dumps({"files": []}))
            self.assertIn("covers nothing", " ".join(structure.snapshot_errors(root)))
            # An edited file is not a preserved reference and is not checked here.
            kept.write_text("fn main() {}\n")
            edited = {"destination": "migration/edited.rs", "source_sha256": "0" * 64,
                      "changes": "Namespace renamed; audits removed."}
            (root / "migration/edited.rs").write_text("whatever\n")
            manifest.write_text(json.dumps({"files": [entry, edited]}))
            self.assertEqual(structure.snapshot_errors(root), [])
            # A file nobody recorded could change without anyone noticing, so it is refused.
            (root / "migration/stray.rs").write_text("fn stray() {}\n")
            self.assertIn("does not record: migration/stray.rs",
                          " ".join(structure.snapshot_errors(root)))
            (root / "migration/stray.rs").unlink()
            # A symlink is not bytes taken from anywhere, on either side of the record.
            (root / "migration/link.rs").symlink_to(root / "migration/kept.rs")
            self.assertIn("carries a symlink", " ".join(structure.snapshot_errors(root)))
            (root / "migration/link.rs").unlink()
            outside = {"destination": "../outside.rs", "source_sha256": "0" * 64,
                       "changes": entry["changes"]}
            manifest.write_text(json.dumps({"files": [entry, outside]}))
            self.assertIn("outside the tree", " ".join(structure.snapshot_errors(root)))
            # A manifest that cannot be read is an error with a message, not a traceback.
            manifest.write_text("{ not json")
            self.assertIn("not a manifest", " ".join(structure.snapshot_errors(root)))
            manifest.write_text(json.dumps({"files": [{"destination": "migration/kept.rs"}]}))
            self.assertIn("not a manifest", " ".join(structure.snapshot_errors(root)))
            manifest.unlink()
            self.assertIn("provenance.json is missing", " ".join(structure.snapshot_errors(root)))

    def test_a_broken_manifest_is_reported_not_raised(self) -> None:
        """Every manifest a gate reads is a file someone can break; none may kill the gate."""
        with tempfile.TemporaryDirectory() as temp:
            root = source_tree(Path(temp))
            for name, key in (("backend/lock.json", "patches"), ("rfcs/manifest.json", "documents"),
                              ("docs/provenance.json", "files")):
                # The last two are the right container holding the wrong thing, which is what
                # an outer shape check alone does not catch.
                for broken in ("{ not json", '{"other": 1}', f'{{"{key}": "not a list"}}',
                               f'{{"{key}": [1, 2]}}', f'{{"{key}": {{"a": 1}}}}'):
                    with self.subTest(manifest=name, content=broken):
                        kept = (root / name).read_text()
                        (root / name).write_text(broken)
                        try:
                            errors = structure.static_errors(root, {})
                        finally:
                            (root / name).write_text(kept)
                        self.assertTrue(any(name in error for error in errors),
                                        f"{name} broken as {broken!r} was not reported: {errors}")

    def test_snapshot_check_covers_the_whole_snapshot(self) -> None:
        """On the real tree: every file of the snapshot is recorded, and the record is used."""
        recorded = [item for item in json.loads((ROOT / "docs/provenance.json").read_text())["files"]
                    if item["changes"].startswith(structure.UNMODIFIED)]
        files = [path for path in (ROOT / structure.SNAPSHOT).rglob("*") if path.is_file()]
        self.assertGreater(len(recorded), 50)
        self.assertEqual(len(files) - len(structure.SNAPSHOT_OWN), len(recorded))
        self.assertEqual(structure.snapshot_errors(ROOT), [])

    def test_rfc_collection_is_what_the_manifest_records(self) -> None:
        """On the real tree: the stored documents are exactly the recorded ones, byte for byte."""
        documents = json.loads((ROOT / "rfcs/manifest.json").read_text())["documents"]
        stored = {path.name for path in (ROOT / "rfcs").iterdir()
                  if path.is_file() and path.name != "manifest.json"}
        self.assertEqual(stored, set(documents))
        self.assertEqual(structure.rfc_errors(ROOT), [])

    def test_every_source_file_declares_its_licence(self) -> None:
        """`NOTICE` says the sources carry an SPDX identifier; this is what makes that true."""
        # The preserved snapshot and the corpora keep the headers they were taken with.
        kept = ("migration/", "tests/corpus/")
        suffixes = (".lean", ".rs", ".py", ".sh", ".c", ".h", ".sml")
        listed = run(["git", "ls-files", *(f"*{suffix}" for suffix in suffixes)]).stdout.split()
        ours = [name for name in listed if not name.startswith(kept)]
        self.assertGreater(len(ours), 50)
        for name in ours:
            with self.subTest(source=name):
                head = "".join((ROOT / name).read_text().splitlines(keepends=True)[:2])
                self.assertIn("SPDX-License-Identifier: AGPL-3.0-or-later", head)

    def test_no_script_shadows_a_standard_library_module(self) -> None:
        """`unittest discover` puts tests/ first on the path, which PYTHONSAFEPATH does not undo."""
        for directory in ("scripts", "tests"):
            for path in sorted((ROOT / directory).rglob("*.py")):
                with self.subTest(module=str(path.relative_to(ROOT))):
                    self.assertNotIn(path.stem, sys.stdlib_module_names)

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

    def test_upstream_comparison_covers_where_the_code_came_from(self) -> None:
        """Every recorded source with a public repository is fetched, not only the first one."""
        manifest = json.loads((ROOT / "docs/provenance.json").read_text())
        entries = manifest["files"] + manifest["removed"]
        public = [entry for entry in entries
                  if "url" in manifest["sources"][entry["source_repository"]]]
        asked: list[str] = []

        def get(url: str) -> bytes:
            asked.append(url)
            return b"not what was recorded"

        errors, checked = upstream_sources.compare_provenance(manifest["sources"], entries, get)
        # A check that stops early, or counts a skipped entry as checked, fails here.
        self.assertEqual((checked, len(asked)), (len(public), len(public)))
        self.assertGreater(checked, 150)
        self.assertEqual(len(errors), checked, "every wrong digest must be reported")

    def test_upstream_comparison_reports_what_it_cannot_check(self) -> None:
        """A source it cannot fetch, or cannot read, is a message rather than a silent pass."""
        taken = b"fn main() {}\n"
        entry = {"source_repository": "breadstuffs", "source_revision": "a" * 40,
                 "source_path": "orb/src/lib.rs", "source_sha256": hashlib.sha256(taken).hexdigest(),
                 "destination": "crates/dn-runtime/src/lib.rs", "changes": "Crate renamed."}
        other = {**entry, "source_path": "orb/src/ring.rs", "destination": "crates/x.rs"}
        private = {**entry, "source_repository": "drorb", "destination": "native/x.c"}
        sources = {"breadstuffs": {"url": "https://github.com/emberian/dregg"},
                   "drorb": {"note": "Private; not publicly verifiable."}}
        asked: list[str] = []

        def get(url: str) -> bytes:
            asked.append(url)
            return taken

        errors, checked = upstream_sources.compare_provenance(sources, [entry, other, private], get)
        self.assertEqual((errors, checked), ([], 2))
        raw = "https://raw.githubusercontent.com/emberian/dregg/" + "a" * 40
        self.assertEqual(asked, [f"{raw}/orb/src/lib.rs", f"{raw}/orb/src/ring.rs"])

        def refused(*entries: Any, get: Any = get, **changed: Any) -> str:
            found, _ = upstream_sources.compare_provenance({**sources, **changed},
                                                           list(entries), get)
            self.assertTrue(found, "accepted what it cannot check")
            return " ".join(found)

        def missing(_: str) -> bytes:
            raise subprocess.CalledProcessError(22, "curl")

        self.assertIn("no longer serves it", refused(entry, get=missing))
        self.assertIn("is not described", refused({**entry, "source_repository": "elsewhere"}))
        self.assertIn("no url to check against and no note",
                      refused(entry, drorb={"changes": "moved"}))
        self.assertIn("is not a commit", refused({**entry, "source_revision": "main"}))
        self.assertIn("does not name a file", refused({**entry, "source_path": "../secrets"}))
        self.assertIn("this check can read",
                      refused(entry, breadstuffs={"url": "https://gitlab.com/x/y"}))
        self.assertIn("has no", refused({key: value for key, value in entry.items()
                                         if key != "source_sha256"}))
        self.assertIn("no recorded source could be checked", refused(private))

    def test_upstream_comparison_keeps_the_grammar_errata_verified(self) -> None:
        """An erratum the grammar follows has to be verified still, with the text it carries."""
        listed = [{"doc-id": "RFC0000", "errata_id": "1", "errata_status_code": "Verified",
                   "correct_text": "a  =  b\n   / c"},
                  {"doc-id": "RFC0000", "errata_id": "2", "errata_status_code": "Rejected",
                   "correct_text": ""}]
        served = json.dumps(listed).encode()
        compare = upstream_sources.compare_errata
        self.assertEqual(compare([("RFC0000", 1)], {1: "a = b / c"}, lambda _: served), [])
        self.assertIn("otherwise", compare([("RFC0000", 1)], {1: "a = d"}, lambda _: served)[0])
        self.assertIn("not Verified", compare([("RFC0000", 2)], {}, lambda _: served)[0])
        self.assertIn("not in the errata", compare([("RFC0000", 3)], {}, lambda _: served)[0])
        applied, corrected = upstream_sources.grammar_errata()
        self.assertTrue(applied and set(corrected) <= {number for _, number in applied})

    def test_upstream_comparison_covers_the_stored_documents(self) -> None:
        """A stored RFC is compared against its url, with the recorded normalization applied."""
        served = b"page one\f\npage two\n"
        stored = {"rfc0000.txt": {"url": "https://example.invalid/rfc0000.txt",
                                  "sha256": hashlib.sha256(served.replace(b"\f", b"")).hexdigest(),
                                  "normalized": "form-feeds-removed"}}
        self.assertEqual(upstream_sources.compare_documents(stored, lambda _: served), [])
        # Without the normalization the same bytes no longer match: it is applied, not assumed.
        plain = {"rfc0000.txt": {k: v for k, v in stored["rfc0000.txt"].items() if k != "normalized"}}
        self.assertIn("rfc0000.txt", upstream_sources.compare_documents(plain, lambda _: served)[0])
        unknown = {"rfc0000.txt": {**stored["rfc0000.txt"], "normalized": "reflowed"}}
        self.assertIn("not one this check knows",
                      upstream_sources.compare_documents(unknown, lambda _: served)[0])
        self.assertEqual(upstream_sources.compare_documents({}, lambda _: served),
                         ["no RFC is recorded"])


class Tools(unittest.TestCase):
    """The pinned tools: stored, verified and built outside the repository."""

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

    def test_bootstrap_installs_a_tool_once_when_asked_side_by_side(self) -> None:
        with tempfile.TemporaryDirectory() as temp:
            work = Path(temp)
            tree, stubs, log = work / "repo", work / "bin", work / "log"
            (tree / "scripts").mkdir(parents=True)
            shutil.copy(ROOT / "scripts/bootstrap_tool.py", tree / "scripts")
            shutil.copy(ROOT / "rust-toolchain.toml", tree)
            subprocess.run(["git", "init", "-q"], cwd=tree, check=True)
            (work / "source").mkdir()
            with tarfile.open(work / "source.tar.gz", "w:gz") as tar:
                tar.add(work / "source", arcname="source")
            lock = json.loads((ROOT / "tools.lock.json").read_text())
            lock["nanoda"]["sha256"] = sha256(work / "source.tar.gz")
            (tree / "tools.lock.json").write_text(json.dumps(lock))
            (tree / ".deps/archives").mkdir(parents=True)
            shutil.copy(work / "source.tar.gz", tree / ".deps/archives" / lock["nanoda"]["sha256"])
            # Installed before stored trees were sealed: redone under the lock.
            tool = tree / ".deps/tools" / f"nanoda-{lock['nanoda']['version']}"
            tool.mkdir(parents=True)
            (tool / "archive.sha256").write_text(lock["nanoda"]["sha256"] + "\n")
            # The build waits until the other two bootstraps wait on the lock, ten seconds at most.
            stubs.mkdir()
            (stubs / "cargo").write_text(
                f"#!/bin/sh\nwaiting=0\nfor _ in $(seq 200); do\n"
                f"  inode=$(stat -c %i {tool}.lock) && waiting=$(grep -c -- \"-> FLOCK .*:$inode \" /proc/locks)\n"
                f'  [ "$waiting" -ge 2 ] && break\n  sleep 0.05\ndone\necho "built, $waiting waiting" >> {log}\n'
                'mkdir -p "$CARGO_TARGET_DIR/release" && touch "$CARGO_TARGET_DIR/release/nanoda_bin"\n')
            (stubs / "cargo").chmod(0o755)
            env = {**os.environ, "PATH": f"{stubs}:{os.environ['PATH']}", "XDG_CACHE_HOME": str(work / "cache")}
            runs = [subprocess.Popen(["python3", "scripts/bootstrap_tool.py", "nanoda"], cwd=tree, env=env, text=True,
                                     stdout=subprocess.PIPE, stderr=subprocess.PIPE) for _ in range(3)]
            paths = set()
            for each in runs:
                out, err = each.communicate()
                self.assertEqual(each.returncode, 0, err)
                paths.add(out.strip())
            self.assertEqual(paths, {str(tool / "nanoda_bin")})
            self.assertEqual(log.read_text(), "built, 2 waiting\n")
