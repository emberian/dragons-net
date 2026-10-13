# SPDX-License-Identifier: AGPL-3.0-or-later
"""`scripts/once.py`: a check is not run again on the inputs it read. Run untraced, since a traced
process cannot trace another."""
from __future__ import annotations

import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tempfile
from typing import Any
import unittest

from gatekit import ROOT, script

once = script("once")


def parsed(log: str, cwd: str = "/r") -> Any:
    return once.Trace(cwd).parse(log)


class Trace(unittest.TestCase):
    """What a run read, wrote, listed and looked for, from strace's log."""

    def test_reads_writes_lookups_and_listings(self) -> None:
        log = """\
7 execve("/r/s.py", ["python3", "s.py"], 0x1 /* 3 vars */) = 0
7 openat(AT_FDCWD</r>, "a.txt", O_RDONLY|O_CLOEXEC) = 3</r/a.txt>
7 openat(AT_FDCWD</r>, "out", O_WRONLY|O_CREAT|O_TRUNC, 0666) = 4</r/out>
7 newfstatat(AT_FDCWD</r>, "/r/missing", 0x7f, 0) = -1 ENOENT (No such file or directory)
7 openat(AT_FDCWD</r>, "/r/d", O_RDONLY|O_NONBLOCK|O_CLOEXEC|O_DIRECTORY) = 5</r/d>
7 renameat2(AT_FDCWD</r>, "out", AT_FDCWD</r>, "final", RENAME_NOREPLACE) = 0
7 openat(AT_FDCWD</r>, "b.txt", O_RDONLY <unfinished ...>
8 getcwd("/r/sub", 4096) = 7
7 <... openat resumed>) = 6</r/b.txt>
"""
        t = parsed(log)
        self.assertEqual(t.read, {"/r/s.py", "/r/a.txt", "/r/b.txt"})
        self.assertEqual(t.written, {"/r/out", "/r/final"})
        self.assertEqual(t.absent, {"/r/missing"})
        self.assertEqual(t.listed, {"/r/d"})
        self.assertEqual(t.ran, [("/r/s.py", ["python3", "s.py"])])
        self.assertEqual(t.unresolved, [])

    def test_what_is_read_and_written_and_failed_changes(self) -> None:
        """A file opened to read and write is both, and noted as such; a change that failed is none,
        and one that failed for want of the path is a path looked for."""
        log = """\
7 openat(AT_FDCWD</r>, "log", O_RDWR|O_APPEND) = 3</r/log>
7 openat(AT_FDCWD</r>, "lnk", O_RDONLY) = 4</r/target>
7 mkdir("/r/nodir/x", 0777) = -1 ENOENT (No such file or directory)
7 unlink("/r/locked") = -1 EACCES (Permission denied)
7 newfstatat(AT_FDCWD</r>, "/r/d", {st_mode=S_IFDIR|0755, st_size=4096, ...}, 0) = 0
"""
        t = parsed(log)
        self.assertEqual(t.read, {"/r/log", "/r/target", "/r/d"})
        self.assertEqual(t.updated, {"/r/log"})
        self.assertEqual(t.written, {"/r/log"})
        self.assertEqual(t.named, {"/r/log", "/r/lnk"})
        self.assertEqual(t.absent, {"/r/nodir/x"})

    def test_a_relative_path_is_resolved_where_its_process_runs(self) -> None:
        """A path without a directory is resolved by the process's own directory: as its last
        call with one showed, as it changed to, or as its parent's when it forked."""
        log = """\
5 chdir("/r/x") = 0
5 clone(child_stack=NULL, flags=CLONE_CHILD_CLEARTID|SIGCHLD) = 9
9 readlink("link", 0x7f, 4096) = 4
5 readlink("other", 0x7f, 4096) = 4
6 readlink("orphan", 0x7f, 4096) = 4
"""
        t = parsed(log, cwd="/r")
        self.assertEqual(t.read, {"/r/x/link", "/r/x/other"})
        self.assertEqual(len(t.unresolved), 1)
        self.assertIn("orphan", t.unresolved[0])

    def test_a_padded_or_split_call_counts(self) -> None:
        """strace pads before a short call's result and a resumed call's, to align them."""
        log = """\
7 chdir("/r/x")                           = 0
7 unlink("old.o" <unfinished ...>
8 readlink("/r/lnk", "t", 4096)           = 1
7 <... unlink resumed>)             = 0
7 openat(AT_FDCWD</r/x>, "y.o", O_RDWR|O_CREAT|O_TRUNC, 0666 <unfinished ...>
8 access("/r/f", R_OK)                    = 0
7 <... openat resumed>)             = 3</r/x/y.o>
"""
        t = parsed(log)
        self.assertEqual(t.read, {"/r/lnk", "/r/f"})
        self.assertEqual(t.written, {"/r/x/old.o", "/r/x/y.o"})
        self.assertEqual(t.unresolved, [])


class Hashes(unittest.TestCase):
    def test_a_file_changed_within_a_step_of_the_clock_is_read_again(self) -> None:
        with tempfile.TemporaryDirectory() as temp:
            file = Path(temp) / "f"
            file.write_text("one")
            mtime = file.stat().st_mtime_ns
            hashes = once.Hashes(Path(temp) / "hashes.json")
            first = hashes.of(str(file))
            file.write_text("two")
            os.utime(file, ns=(mtime, mtime))
            self.assertNotEqual(hashes.of(str(file)), first)
            os.utime(file, ns=(mtime - 2 * once.Hashes.RACY, mtime - 2 * once.Hashes.RACY))
            kept = hashes.of(str(file))
            self.assertEqual(hashes.known[str(file)][3], kept)


class Live(unittest.TestCase):
    """A real run under strace, in a repository of its own."""

    def setUp(self) -> None:
        self.tree = Path(tempfile.mkdtemp())
        self.addCleanup(shutil.rmtree, self.tree)
        (self.tree / "scripts").mkdir()
        shutil.copy(ROOT / "scripts/once.py", self.tree / "scripts")
        (self.tree / ".gitignore").write_text("build/\n")
        (self.tree / "input.txt").write_text("one\n")
        (self.tree / "unrelated.txt").write_text("x\n")
        (self.tree / "check.py").write_text(
            "import os, json\n"
            "print(open('input.txt').read().strip())\n"
            "open('build-output.txt', 'w').write('made')\n"
            "print(os.path.exists('maybe.txt'))\n"
            "if os.environ.get('DN_DOCUMENTED'):\n"
            "    open(os.environ['DN_DOCUMENTED'], 'a').write(json.dumps({'quoted': {'a': ['b']}}) + '\\n')\n")
        subprocess.run(["git", "init", "-q", str(self.tree)], check=True)

    def run_check(self, *log: str) -> str:
        done = subprocess.run([sys.executable, "scripts/once.py", "run", "probe", *log, "--", sys.executable,
                               "check.py"], cwd=self.tree, capture_output=True, text=True, check=True, timeout=120)
        return done.stdout + done.stderr

    def check(self, body: str) -> None:
        (self.tree / "check.py").write_text(body)

    def test_a_check_runs_again_only_when_what_it_read_changes(self) -> None:
        self.assertIn("one", self.run_check())
        stamp = json.loads((self.tree / "build/stamps/probe.json").read_text())
        self.assertIn("input.txt", stamp["inputs"]["files"])
        self.assertIn("check.py", stamp["inputs"]["files"])
        self.assertNotIn("build-output.txt", stamp["inputs"]["files"])
        self.assertIn("maybe.txt", stamp["inputs"]["absent"])
        self.assertEqual(stamp["documented"], [{"quoted": {"a": ["b"]}}])
        self.assertIn("DN SKIP probe", self.run_check())
        # What it writes, and a file it never reads, change nothing; a new name where it looked for
        # modules would.
        (self.tree / "build-output.txt").write_text("other")
        (self.tree / "unrelated.txt").write_text("y\n")
        self.assertIn("DN SKIP probe", self.run_check())
        (self.tree / "input.txt").write_text("two\n")
        self.assertIn("two", self.run_check())
        self.assertIn("DN SKIP probe", self.run_check())
        # A path it looked for and did not find, appearing, runs it again.
        (self.tree / "maybe.txt").write_text("")
        self.assertIn("True", self.run_check())

    def test_a_link_retargeted_or_a_directory_removed_runs_it_again(self) -> None:
        (self.tree / "other.txt").write_text("other\n")
        (self.tree / "via").symlink_to("input.txt")
        (self.tree / "d").mkdir()
        self.check("import os\nprint(open('via').read().strip(), os.path.isdir('d'))\n")
        self.assertIn("one True", self.run_check())
        self.assertIn("DN SKIP", self.run_check())
        (self.tree / "via").unlink()
        (self.tree / "via").symlink_to("other.txt")
        self.assertIn("other True", self.run_check())
        self.assertIn("DN SKIP", self.run_check())
        (self.tree / "d").rmdir()
        self.assertIn("other False", self.run_check())

    def test_what_a_short_call_reads_or_writes_counts(self) -> None:
        (self.tree / "via").symlink_to("input.txt")
        self.check("import os\nos.chdir('build')\nopen('tmp', 'w').write('x')\nos.rename('tmp', 'out')\n"
                   "open('out').read()\nprint(os.readlink('../via'))\n")
        self.assertIn("input.txt", self.run_check())
        self.assertIn("DN SKIP", self.run_check())
        (self.tree / "via").unlink()
        (self.tree / "via").symlink_to("unrelated.txt")
        self.assertIn("unrelated.txt", self.run_check())

    def test_a_check_that_rewrites_a_source_or_sees_one_change_runs_every_time(self) -> None:
        subprocess.run(["git", "add", "-A"], cwd=self.tree, check=True)
        self.check("f = open('input.txt', 'r+')\nf.read()\nf.write('x')\n")
        self.assertIn("runs every time, it read and wrote input.txt", self.run_check())
        self.assertNotIn("DN SKIP", self.run_check())
        # A change the trace cannot see as the check's own, made under another name of the file.
        os.link(self.tree / "unrelated.txt", self.tree / "alias")
        self.check("open('unrelated.txt').read()\nopen('alias', 'a').write('more')\n")
        self.assertIn("runs every time, unrelated.txt changed while it ran", self.run_check())
        self.assertNotIn("DN SKIP", self.run_check())

    def test_its_input_is_empty_and_its_output_kept_only_when_it_runs(self) -> None:
        self.check("import sys\nprint('read', repr(sys.stdin.read()))\n")
        log = self.tree / "build/evidence/probe.log"
        self.assertIn("read ''", self.run_check("--log", str(log)))
        self.assertIn("read ''", log.read_text())
        self.assertIn("DN SKIP", self.run_check("--log", str(log)))
        self.assertIn("read ''", log.read_text())

    def test_a_failing_check_records_nothing(self) -> None:
        (self.tree / "check.py").write_text("raise SystemExit(3)\n")
        done = subprocess.run([sys.executable, "scripts/once.py", "run", "probe", "--", sys.executable, "check.py"],
                              cwd=self.tree, capture_output=True, text=True, check=False, timeout=120)
        self.assertEqual(done.returncode, 3)
        self.assertFalse((self.tree / "build/stamps/probe.json").exists())


class Stages(unittest.TestCase):
    """`check.sh tests` as it runs: each of its checks recorded, and on a second run each skipped."""

    def test_the_tests_stage_runs_each_check_once(self) -> None:
        with tempfile.TemporaryDirectory() as temp:
            tree, stubs = Path(temp) / "repo", Path(temp) / "bin"
            (tree / "scripts").mkdir(parents=True)
            (tree / "tests").mkdir()
            stubs.mkdir()
            for name in ("check.sh", "once.py"):
                shutil.copy(ROOT / "scripts" / name, tree / "scripts" / name)
            body = (ROOT / "scripts/check.sh").read_text().partition("\ntests() {")[2].partition("\n}\n")[0]
            ran = re.findall(r"^\s*once [\w-]+ python3 (scripts/\w+\.py)", body, re.MULTILINE)
            for name in ran:
                (tree / name).write_text("print('checked')\n")
            for module in ("test_a.py", "test_once.py"):
                (tree / "tests" / module).write_text("import unittest\n\n\nclass A(unittest.TestCase):\n"
                                                     "    def test_a(self) -> None:\n        pass\n")
            (stubs / "cargo").write_text("#!/bin/sh\necho cargo \"$@\"\n")
            (stubs / "cargo").chmod(0o755)
            (tree / ".gitignore").write_text("build/\n")
            subprocess.run(["git", "init", "-q", str(tree)], check=True)
            subprocess.run(["git", "add", "-A"], cwd=tree, check=True)
            env = {**os.environ, "PATH": f"{stubs}:{os.environ['PATH']}"}
            env.pop("DN_ONCE", None)

            def stage() -> str:
                done = subprocess.run(["bash", "scripts/check.sh", "tests"], cwd=tree, env=env, text=True,
                                      capture_output=True, check=True, timeout=300)
                return done.stdout + done.stderr

            first = stage()
            self.assertNotIn("DN SKIP", first)
            self.assertEqual(first.count("checked"), len(ran))
            second = stage()
            # The unit module, the five runs of cargo and the scripts; the tracer's own test runs always.
            self.assertEqual(second.count("DN SKIP"), 1 + 5 + len(ran))
            self.assertNotIn("checked", second)
            (tree / ran[0]).write_text("print('checked again')\n")
            self.assertEqual(stage().count("DN SKIP"), 5 + len(ran))


class Documents(unittest.TestCase):
    """What the checks require of the documents, held after their last passes."""

    def test_the_documents_are_held_to_each_stamp_s_requirements(self) -> None:
        with tempfile.TemporaryDirectory() as temp:
            stamps = Path(temp)
            (stamps / "hashes.json").write_text("{}")

            def held(phrase: str) -> subprocess.CompletedProcess[str]:
                (stamps / "lane-x.json").write_text(json.dumps({"documented": [{"quoted": {"README.md": [phrase]}}]}))
                return subprocess.run([sys.executable, "scripts/check_documents.py"], cwd=ROOT, text=True,
                                      env={**os.environ, "DN_STAMPS": temp}, capture_output=True, check=False)

            for name in script("check_documents").CHECKS.values():
                (stamps / f"{name}.json").write_text("{}")
            passed = held("dn-compiler")
            self.assertEqual(passed.returncode, 0, passed.stderr)
            self.assertIn("1 requirements", passed.stdout)
            failed = held("no such phrase")
            self.assertEqual(failed.returncode, 1)
            self.assertIn("lane-x: README.md does not say 'no such phrase'", failed.stderr)

    def test_every_check_that_holds_the_documents_is_named_and_stamped(self) -> None:
        """A script that leaves requirements on the documents is listed, and a run without its stamp
        does not pass, for its requirements would go unheld."""
        documents = script("check_documents")
        calling = {p.name for p in (ROOT / "scripts").glob("*.py")
                   if p.name not in {"lanes.py", "check_documents.py", "once.py"}
                   and re.search(r"lanes\.require(_quoted|_stated)?\(", p.read_text())}
        self.assertEqual(calling, set(documents.CHECKS))
        with tempfile.TemporaryDirectory() as temp:
            done = subprocess.run([sys.executable, "scripts/check_documents.py"], cwd=ROOT, text=True,
                                  env={**os.environ, "DN_STAMPS": temp}, capture_output=True, check=False)
            self.assertEqual(done.returncode, 1)
            self.assertIn("no stamp of lane-nntp", done.stderr)


class Fingerprint(unittest.TestCase):
    """The modules of the library a command of `dn-compiler` runs."""

    def test_a_command_rests_on_the_modules_it_reaches(self) -> None:
        prefix = subprocess.run(["lean", "--print-prefix"], cwd=ROOT, capture_output=True, text=True,
                                check=True).stdout.strip()
        env = {**os.environ, "LEAN_PATH": f"{prefix}/lib/lean:{ROOT}/.lake/build/lib/lean"}
        done = subprocess.run(["lean", "--run", "scripts/Fingerprint.lean", "frame-model", "emit-crc", "nope"],
                              cwd=ROOT, env=env, capture_output=True, text=True, check=False, timeout=600)
        self.assertEqual(done.returncode, 1)
        self.assertIn("no command nope", done.stderr)
        lines = {line.split()[0]: line.split()[1:] for line in done.stdout.splitlines()}
        self.assertIn("DN.News.FrameModel", lines["frame-model"])
        self.assertIn("DN.Compiler.Main", lines["frame-model"])
        self.assertNotIn("DN.Compiler.Analyzer", lines["frame-model"])
        self.assertIn("DN.News.CrcProg", lines["emit-crc"])
        self.assertNotIn("DN.News.SipProg", lines["emit-crc"])


class TreeKey(unittest.TestCase):
    """A check that cannot be traced, keyed by every file of the tree."""

    def test_a_check_keyed_by_the_tree_runs_once_per_tree(self) -> None:
        """A check that passed is not run again on a tree whose every file is as it was, and is on
        one with a file changed, added, or of another content under the same name, or with another
        command or compiler."""
        with tempfile.TemporaryDirectory() as temp:
            tree = Path(temp)
            (tree / "scripts").mkdir()
            shutil.copy(ROOT / "scripts/once.py", tree / "scripts")
            (tree / ".gitignore").write_text("build/\n")
            (tree / "a.txt").write_text("one\n")
            subprocess.run(["git", "init", "-q", str(tree)], check=True)

            def run(*args: str, cake: str = "") -> subprocess.CompletedProcess[str]:
                return subprocess.run([sys.executable, str(tree / "scripts/once.py"), *args], cwd=tree, text=True,
                                      env={**os.environ, "CAKE": cake}, capture_output=True, check=False,
                                      timeout=60)

            def once(action: str, *command: str, cake: str = "") -> int:
                return run(action, "lane", "--", *(command or ("run",)), cake=cake).returncode

            missed = run("check", "lane", "--", "run")
            self.assertEqual(missed.returncode, 1)
            # The key is taken before the check runs: a file changed meanwhile leaves the tree unstamped.
            (tree / "a.txt").write_text("changed while it ran\n")
            self.assertEqual(run("stamp", "lane", missed.stdout.strip()).returncode, 0)
            self.assertEqual(once("check"), 1)
            (tree / "a.txt").write_text("one\n")
            self.assertEqual(once("check"), 0)
            self.assertEqual(run("stamp", "lane", "").returncode, 1)
            self.assertEqual(run("stamp", "../lane", missed.stdout.strip()).returncode, 1)
            self.assertEqual(once("check", "other"), 1)
            self.assertEqual(once("check", cake="/other/cake"), 1)
            (tree / "build/ignored").write_text("left by a run\n")
            self.assertEqual(once("check"), 0)
            (tree / "a.txt").write_text("two\n")
            self.assertEqual(once("check"), 1)
            (tree / "a.txt").write_text("one\n")
            self.assertEqual(once("check"), 0)
            (tree / "b.txt").write_text("")
            self.assertEqual(once("check"), 1)



if __name__ == "__main__":
    unittest.main()
