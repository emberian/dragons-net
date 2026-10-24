# SPDX-License-Identifier: AGPL-3.0-or-later
"""`scripts/once.py`: a check is not run again on the inputs it read. Run untraced, since a traced
process cannot trace another."""
from __future__ import annotations

import hashlib
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
from unittest import mock

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

    def test_the_empty_path_names_only_a_descriptor(self) -> None:
        """A lookup of the empty path names the descriptor it is given, with AT_EMPTY_PATH, and nothing
        without: Python asks for it of a path entry that does not exist."""
        log = """\
7 newfstatat(3</r/f>, "", {st_mode=S_IFREG|0644, st_size=1, ...}, AT_EMPTY_PATH) = 0
7 newfstatat(AT_FDCWD</r>, "", 0x7f, 0) = -1 ENOENT (No such file or directory)
"""
        t = parsed(log)
        self.assertEqual((t.read, t.absent), ({"/r/f"}, set()))

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


class Git(unittest.TestCase):
    """Runs of git in a check, kept apart from it and run again."""

    def test_a_run_of_git_is_kept_apart_with_its_arguments_and_environment(self) -> None:
        """What git and its children touch is the run of git's; the rest the check's."""
        log = """\
5 execve("/usr/bin/git", ["git", "ls-files", "--", "a\\"b"], ["GIT_X=1", "HOME=/h"]) = 0
5 openat(AT_FDCWD</r>, "/r/.git/index", O_RDONLY) = 3</r/.git/index>
5 clone(child_stack=NULL, flags=SIGCHLD) = 6
6 openat(AT_FDCWD</r>, "child", O_RDONLY) = 3</r/child>
7 openat(AT_FDCWD</r>, "own", O_RDONLY) = 3</r/own>
"""
        t = parsed(log)
        [call] = t.git
        self.assertEqual((call.cwd, call.argv, call.env),
                         ("/r", ["git", "ls-files", "--", 'a"b'], {"GIT_X": "1", "HOME": "/h"}))
        self.assertEqual(call.read, {"/usr/bin/git", "/r/.git/index", "/r/child"})
        self.assertEqual(t.read, {"/r/own"})

    def test_only_a_run_of_git_that_reads_here_is_run_again(self) -> None:
        def replayable(argv: list[str], env: dict[str, str] | None = None, cwd: str = str(ROOT),
                       wrote: str | None = None) -> bool:
            call = once.GitCall(cwd, argv, once.checked_env() if env is None else env)
            if wrote:
                call.written.add(wrote)
            return bool(once.replayable(call))

        for argv in (["git", "ls-files"], ["git", "--icase-pathspecs", "ls-files", "--", "x"],
                     ["git", "-c", "core.quotePath=false", "rev-parse", "HEAD"], ["git", "-C", "scripts", "log"],
                     ["git", "ls-remote", "--quiet", "--get-url"]):
            with self.subTest(argv=argv):
                self.assertTrue(replayable(argv))
        for argv in (["git", "status"], ["git", "-C", "..", "ls-files"], ["git", "-C"], ["git", "--git-dir=x", "log"],
                     ["git", "cat-file", "--batch"], ["git", "check-ignore", "--stdin"], ["git"],
                     ["git", "ls-remote"], ["git", "ls-remote", "--", "--get-url"]):
            with self.subTest(argv=argv):
                self.assertFalse(replayable(argv))
        for argv in (["git", "describe", "--dirty"], ["git", "-c", "http.extraheader=Authorization: x", "log"]):
            with self.subTest(argv=argv):
                self.assertFalse(replayable(argv))
        self.assertFalse(replayable(["git", "ls-files"], env={**os.environ, "GIT_INDEX_FILE": "other"}))
        self.assertFalse(replayable(["git", "ls-files"], env={**os.environ, "LEAN_PATH": "other"}))
        self.assertFalse(replayable(["git", "ls-files"], cwd="/elsewhere"))
        self.assertFalse(replayable(["git", "ls-files"], wrote=str(ROOT / ".git/index")))

    def test_a_run_of_git_strace_did_not_print_whole_is_not_run_again(self) -> None:
        """A string or an array cut short, or a variable given twice, leaves the run unknown."""
        whole = 'execve("/usr/bin/git", ["git", "ls-files"], ["A=1", "B=2"]) = 0'
        for args in (whole, whole.replace('"ls-files"', '"ls-fi"...'), whole.replace('"B=2"', '"B=2", ...'),
                     whole.replace('"B=2"', '"A=2"'), whole.replace(', ["A=1", "B=2"]', ", 0x1 /* 2 vars */")):
            with self.subTest(args=args):
                [call] = parsed(f"5 {args}\n").git
                self.assertEqual(call.whole, args == whole)

    def test_an_answer_git_cannot_give_counts_as_changed(self) -> None:
        self.assertIsNone(once.answer("no/such/directory", ["git", "ls-files"]))
        deps: dict[str, Any] = {"git": None, "compiler": None, "links": {}, "files": {}, "dirs": {}, "absent": {},
                "commands": [["no/such/directory", ["git", "ls-files"], "0" * 64]]}
        self.assertFalse(once.current(deps, once.Hashes(Path(tempfile.mkdtemp()) / "hashes.json")))
        self.assertIsNone(once.key_of("/etc/hosts"))
        self.assertEqual(once.key_of("/etc/passwd"), "/etc/passwd")


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

    def run_check(self, *log: str, env: dict[str, str] | None = None) -> str:
        done = subprocess.run([sys.executable, "scripts/once.py", "run", "probe", *log, "--", sys.executable,
                               "check.py"], cwd=self.tree, env=env, capture_output=True, text=True, check=True,
                              timeout=120)
        return done.stdout + done.stderr

    def check(self, body: str) -> None:
        (self.tree / "check.py").write_text(body)

    def git(self, *args: str) -> None:
        subprocess.run(["git", "-c", "user.name=t", "-c", "user.email=t@t.example", "-c", "commit.gpgsign=false",
                        *args], cwd=self.tree, check=True, capture_output=True, timeout=60)

    def test_a_module_beside_those_imported_is_no_input(self) -> None:
        """Imports look up the names they search for: a module put beside the one imported leaves
        the stamp standing; one found first runs the check again."""
        shutil.copytree(ROOT / "scripts/once_site", self.tree / "scripts/once_site")
        for name in ("first", "second"):
            (self.tree / name).mkdir()
        (self.tree / "second/helper.py").write_text("VALUE = 1\n")
        self.check("import sys\nsys.path[:0] = ['first', 'second']\nimport helper\nprint(helper.VALUE)\n")
        self.assertIn("1", self.run_check())
        (self.tree / "second/other.py").write_text("")
        (self.tree / "first/unrelated.py").write_text("")
        self.assertIn("DN SKIP", self.run_check())
        (self.tree / "first/helper.py").write_text("VALUE = 2\n")
        self.assertIn("2", self.run_check())
        (self.tree / "first/helper.py").unlink()
        (self.tree / "first/helper").mkdir()
        (self.tree / "first/helper/__init__.py").write_text("VALUE = 3\n")
        self.assertIn("3", self.run_check())

    def test_a_directory_listed_whole_is_an_input_still(self) -> None:
        """A check that lists a directory itself, or a Python that ignores the environment and so
        lists the directories it imports from, runs again when a name is added there."""
        shutil.copytree(ROOT / "scripts/once_site", self.tree / "scripts/once_site")
        (self.tree / "second").mkdir()
        (self.tree / "second/helper.py").write_text("VALUE = 1\n")
        bodies = ["import os\nprint(sorted(os.listdir('second')))\n",
                  ("import subprocess, sys\nsubprocess.run([sys.executable, '-I', '-c', "
                   "\"import sys; sys.path[:0] = ['second']; import helper\"], check=True)\n")]
        for k, body in enumerate(bodies):
            with self.subTest(body=body):
                self.check(body)
                self.run_check()
                self.assertIn("DN SKIP", self.run_check())
                (self.tree / f"second/new{k}.py").write_text("")
                self.assertNotIn("DN SKIP", self.run_check())

    def test_a_check_on_what_git_answers_runs_again_only_when_the_answer_changes(self) -> None:
        self.check("import subprocess\nprint(subprocess.run(['git', 'ls-files', '--cached', '--others', "
                   "'--exclude-standard'], capture_output=True, text=True, check=True).stdout.split())\n")
        self.git("add", "-A")
        self.assertIn("check.py", self.run_check())
        inputs = once.passes(json.loads((self.tree / "build/stamps/probe.json").read_text()))[0]["inputs"]
        self.assertIsNone(inputs["git"])
        self.assertEqual([c[1] for c in inputs["commands"]],
                         [["git", "ls-files", "--cached", "--others", "--exclude-standard"]])
        # A commit moves HEAD, not what git answers; a file git now lists changes the answer.
        self.git("commit", "-qm", "first")
        self.assertIn("DN SKIP", self.run_check())
        (self.tree / "new.txt").write_text("")
        self.assertIn("new.txt", self.run_check())
        self.assertIn("DN SKIP", self.run_check())

    def test_a_check_on_git_s_own_state_runs_again_on_a_commit(self) -> None:
        """A run of git that writes, one in an environment of its own or pointed elsewhere, and git's
        files read without git, stand for git's whole state."""
        for body in ("import subprocess\nsubprocess.run(['git', 'status', '--porcelain'], check=True)\n",
                     "print(open('.git/HEAD').read())\n",
                     ("import os, subprocess\nsubprocess.run(['git', 'ls-files'], check=True, "
                      "env={**os.environ, 'GIT_INDEX_FILE': '.git/index'})\n"),
                     "import subprocess\nsubprocess.run(['git', '--git-dir=.git', 'ls-files'], check=True)\n"):
            with self.subTest(body=body):
                self.check(body)
                self.git("add", "-A")
                self.git("commit", "-qm", "c", "--allow-empty")
                self.run_check()
                self.assertIn("DN SKIP", self.run_check())
                self.git("commit", "-qm", "next", "--allow-empty")
                self.assertNotIn("DN SKIP", self.run_check())

    def test_a_check_that_looks_for_git_s_directory_runs_again_only_on_what_it_excludes(self) -> None:
        """A tool that honours .gitignore looks up git's directory and reads the patterns it excludes,
        which a commit leaves as they were."""
        self.check("import os\nos.stat('.git')\nprint(open('.git/info/exclude').read())\n")
        (self.tree / ".git/info").mkdir(exist_ok=True)
        (self.tree / ".git/info/exclude").write_text("")
        self.git("add", "-A")
        self.git("commit", "-qm", "c")
        self.run_check()
        [made] = once.passes(json.loads((self.tree / "build/stamps/probe.json").read_text()))
        self.assertIsNone(made["inputs"]["git"])
        self.git("commit", "-qm", "next", "--allow-empty")
        self.assertIn("DN SKIP", self.run_check())
        (self.tree / ".git/info/exclude").write_text("*.tmp\n")
        self.assertIn("*.tmp", self.run_check())

    def test_a_check_whose_git_files_change_while_it_runs_runs_every_time(self) -> None:
        self.git("add", "-A")
        self.git("commit", "-qm", "c")
        self.check("import os, subprocess\nsubprocess.run(['git', 'ls-files'], check=True)\n"
                   "os.utime('.git/index')\n")
        self.assertIn("runs every time, .git/index changed while it ran", self.run_check())

    def test_a_check_that_changes_what_git_lists_runs_every_time(self) -> None:
        self.check("import subprocess\nopen('made.txt', 'a').close()\n"
                   "subprocess.run(['git', 'ls-files', '--others', '--exclude-standard'], check=True)\n")
        self.assertIn("runs every time, the files git lists, HEAD or the refs changed while it ran", self.run_check())

    def test_a_check_runs_again_only_when_what_it_read_changes(self) -> None:
        self.assertIn("one", self.run_check())
        stamp = once.passes(json.loads((self.tree / "build/stamps/probe.json").read_text()))[0]
        self.assertIn("input.txt", stamp["inputs"]["files"])
        self.assertIn("check.py", stamp["inputs"]["files"])
        self.assertNotIn("build-output.txt", stamp["inputs"]["files"])
        self.assertIn("maybe.txt", stamp["inputs"]["absent"])
        self.assertEqual(stamp["documented"], [{"quoted": {"a": ["b"]}}])
        self.assertIn("DN SKIP probe", self.run_check())
        # A variable naming only the service it runs under changes nothing.
        other = os.environ.get("SYSTEMD_EXEC_PID", "") + "1"
        self.assertIn("DN SKIP probe", self.run_check(env={**os.environ, "SYSTEMD_EXEC_PID": other}))
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

    def test_a_stamp_keeps_a_pass_in_each_environment(self) -> None:
        """A pass in one environment leaves the passes in others standing, the newest `PASSES` of them;
        a run that fails drops its own environment's alone, and a stamp of one pass, as stamps were
        made before, is that pass."""
        def env(name: str) -> dict[str, str]:
            return {**os.environ, "DN_PROBE_RUNNER": name}

        def kept() -> list[str]:
            stamp = json.loads((self.tree / "build/stamps/probe.json").read_text())
            return [p["environment"]["DN_PROBE_RUNNER"] for p in once.passes(stamp)]

        self.assertIn("one", self.run_check(env=env("a")))
        self.assertIn("one", self.run_check(env=env("b")))
        self.assertIn("DN SKIP probe", self.run_check(env=env("a")))
        self.assertEqual(kept(), ["b", "a"])
        for name in ("c", "d"):
            self.run_check(env=env(name))
        self.assertEqual(kept(), ["d", "c", "b"])
        self.check("raise SystemExit(3)\n")
        failed = subprocess.run([sys.executable, "scripts/once.py", "run", "probe", "--", sys.executable, "check.py"],
                                cwd=self.tree, env=env("c"), capture_output=True, text=True, check=False, timeout=120)
        self.assertEqual(failed.returncode, 3)
        self.assertEqual(kept(), ["d", "b"])
        stamp = self.tree / "build/stamps/probe.json"
        stamp.write_text(json.dumps(once.passes(json.loads(stamp.read_text()))[0]))
        self.assertEqual(kept(), ["d"])
        # A stamp that does not read as one records nothing: the check runs.
        self.check("print('ran')\n")
        for broken in ('{"passes": 5}', "[1]", "not json"):
            stamp.write_text(broken)
            self.assertIn("ran", self.run_check(env=env("d")))

    def test_stamps_made_elsewhere_are_merged_pass_by_pass(self) -> None:
        """Merging lays each stamp's passes over those of the same name, the newest in each
        environment kept, and leaves the lanes' stamps and the hashes alone."""
        def stamp(*passes: tuple[str, str]) -> str:
            return json.dumps({"passes": [{"command": ["c"], "environment": {"E": e}, "tracer": "t", "inputs": None,
                                           "passed": at} for e, at in passes]})

        dest, made = self.tree / "dest", self.tree / "made"
        for d in (dest, made):
            d.mkdir()
        (dest / "x.json").write_text(stamp(("a", "2026-01-01T00:00:00Z"), ("b", "2026-01-01T00:00:00Z")))
        (made / "x.json").write_text(stamp(("b", "2026-02-01T00:00:00Z"), ("c", "2026-02-01T00:00:00Z")))
        (made / "y.json").write_text(stamp(("a", "2026-02-01T00:00:00Z")))
        for name in ("lane-z.json", "hashes.json"):
            (made / name).write_text("{}")
        subprocess.run([sys.executable, "scripts/once.py", "merge", str(dest), str(made)], cwd=self.tree, check=True)
        x = once.passes(json.loads((dest / "x.json").read_text()))
        self.assertEqual([(p["environment"]["E"], p["passed"][5:7]) for p in x],
                         [("b", "02"), ("c", "02"), ("a", "01")])
        self.assertTrue((dest / "y.json").is_file())
        self.assertEqual(sorted(p.name for p in dest.iterdir()), ["x.json", "y.json"])

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
            for name in ("check.sh", "check_tests.sh", "once.py", "unit.py"):
                shutil.copy(ROOT / "scripts" / name, tree / "scripts" / name)
            text = (ROOT / "scripts/check_tests.sh").read_text()
            body = text.partition("\ngroup() {")[2].partition("\n}\n")[0]
            ran = re.findall(r"^\s*once [\w-]+ python3 (scripts/(?!unit\.py)\w+\.py)", body, re.MULTILINE)
            # Modules of tests a group of their own runs.
            apart = re.findall(r"^\s*once [\w-]+ python3 scripts/unit\.py (\w+)$", body, re.MULTILINE)
            for name in ran:
                (tree / name).write_text("print('checked')\n")
            # What puts a group's tools in place, which here puts none.
            tools = text.partition("\ntools() {")[2].partition("\n}\n")[0]
            for name in set(re.findall(r"python3 (scripts/\w+\.py)", tools)):
                (tree / name).write_text("")
            for module in ("test_a", "test_once", *apart):
                (tree / "tests" / f"{module}.py").write_text("import unittest\n\n\nclass A(unittest.TestCase):\n"
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
            # The modules of tests, the five runs of cargo and the scripts; the tracer's own test runs
            # always.
            skipped = 1 + len(apart) + 5 + len(ran)
            self.assertEqual(second.count("DN SKIP"), skipped)
            self.assertNotIn("checked", second)
            (tree / ran[0]).write_text("print('checked again')\n")
            self.assertEqual(stage().count("DN SKIP"), skipped - 1)


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
        does not pass, for its requirements would go unheld; or it is a FUSE lane, run again on any
        change of the tree, which holds them as it runs."""
        documents = script("check_documents")
        calling = {p.name for p in (ROOT / "scripts").glob("*.py")
                   if p.name not in {"lanes.py", "check_documents.py", "once.py"}
                   and re.search(r"lanes\.require(_quoted|_stated)?\(", p.read_text())}
        self.assertEqual(calling, set(documents.CHECKS) | documents.AS_THEY_RUN)
        lanes = (ROOT / "scripts/native_lanes.sh").read_text()
        [fuse] = re.findall(r"^fuse=\(([a-z ]+)\)$", lanes, re.MULTILINE)
        self.assertEqual({f"{name}_check.py" for name in fuse.split()}, documents.AS_THEY_RUN)
        for name in fuse.split():
            self.assertIn(f"    {name}) script=(scripts/{name}_check.py) ;;\n", lanes)
        with tempfile.TemporaryDirectory() as temp:
            done = subprocess.run([sys.executable, "scripts/check_documents.py"], cwd=ROOT, text=True,
                                  env={**os.environ, "DN_STAMPS": temp}, capture_output=True, check=False)
            self.assertEqual(done.returncode, 1)
            self.assertIn("no stamp of lane-nntp", done.stderr)


class Fingerprint(unittest.TestCase):
    """What a command of `dn-compiler` runs, on a library of its own: `DN.Compiler.Main` picks a
    handler from its table, which reaches the rest."""

    # `f` carries a proof of `t`, which the code erases.
    LIB = ("def g (x : Nat) : Nat := x + 1\n"
           "theorem t : g 0 = 1 := rfl\n"
           "def f (x : Nat) : Nat := have _ : g 0 = 1 := t; g x * 2\n"
           "def h : Nat := 7\n")
    MAIN = ("import DN.Lib\nimport DN.Printed\n"
            "def DN.Compiler.Cli.table : List (Prod String (List String → IO UInt32)) :=\n"
            "  [(\"a\", fun _ => pure (f 1).toUInt32), (\"b\", fun _ => pure h.toUInt32),\n"
            "   (\"emit-p\", fun _ => pure 5)]\n"
            "def main (args : List String) : IO UInt32 :=\n"
            "  match (DN.Compiler.Cli.table.find? (args.head? == some ·.1)), DN.Printed.named with\n"
            "  | some (_, run), _ => run args\n"
            "  | none, _ => pure 2\n")

    PRINTED = "def DN.Printed.named : List (Prod String String) := [(\"p\", \"q\")]\n"

    def digests(self, lib: str = LIB, main: str = MAIN, printed: str = PRINTED) -> dict[str, str]:
        with tempfile.TemporaryDirectory() as temp:
            tree, built = Path(temp) / "src", Path(temp) / "lib"
            sources = {"DN/Lib.lean": lib,
                       "DN/Printed.lean": printed,
                       "DN/Compiler/Main.lean": main}
            prefix = subprocess.run(["lean", "--print-prefix"], cwd=ROOT, capture_output=True, text=True,
                                    check=True).stdout.strip()
            env = {**os.environ, "LEAN_PATH": f"{prefix}/lib/lean:{built}"}
            for name, text in sources.items():
                (tree / name).parent.mkdir(parents=True, exist_ok=True)
                (tree / name).write_text(text)
                (built / name).parent.mkdir(parents=True, exist_ok=True)
                subprocess.run(["lean", f"--root={tree}", "-o", str(built / name.replace(".lean", ".olean")),
                                str(tree / name)], cwd=ROOT, env=env, check=True, capture_output=True, timeout=300)
            done = subprocess.run(["lean", "--run", str(ROOT / "scripts/Fingerprint.lean"), "a", "b", "emit-p", "nope"],
                                  cwd=ROOT, env=env, capture_output=True, text=True, check=False, timeout=300)
            self.assertEqual(done.returncode, 1)
            self.assertIn("no command nope", done.stderr)
            out: dict[str, str] = once.digests(done.stdout)
            return out

    def test_a_command_rests_on_the_code_it_reaches(self) -> None:
        base = self.digests()
        self.assertEqual(sorted(base), ["a", "b", "emit-p"])
        unrelated = [self.LIB.replace(":= 7", ":= 8"), self.LIB.replace(":= rfl", ":= by decide"),
                     "-- a comment\n" + self.LIB.replace("(x : Nat) : Nat := x + 1", "(y : Nat) : Nat := y + 1")]
        for lib in unrelated:
            with self.subTest(lib=lib):
                self.assertEqual(self.digests(lib)["a"], base["a"])
        for lib in (self.LIB.replace("x + 1", "x + 1 + 0"), "@[inline] " + self.LIB):
            with self.subTest(lib=lib):
                self.assertNotEqual(self.digests(lib)["a"], base["a"])
        changed = self.digests(main=self.MAIN.replace("(f 1)", "(f 2)"))
        self.assertNotEqual(changed["a"], base["a"])
        self.assertEqual(changed["b"], base["b"])
        self.assertNotEqual(self.digests(main=self.MAIN.replace("pure 2", "pure 3"))["b"], base["b"])
        # `emit-NAME` is a printed program's before it is the table's, as `main` looks it up.
        self.assertNotEqual(self.digests(printed=self.PRINTED.replace('"q"', '"r"'))["emit-p"], base["emit-p"])
        self.assertEqual(self.digests(main=self.MAIN.replace("pure 5", "pure 6"))["emit-p"], base["emit-p"])


class Compiled(unittest.TestCase):
    """`dn-compiler` counted by what its commands run, in a tree of its own: an executable that says
    what it ran, and a fingerprint that prints what `fp.txt` holds."""

    def setUp(self) -> None:
        self.tree = Path(tempfile.mkdtemp())
        self.addCleanup(shutil.rmtree, self.tree)
        (self.tree / "scripts").mkdir()
        shutil.copy(ROOT / "scripts/once.py", self.tree / "scripts")
        shutil.copy(ROOT / "lean-toolchain", self.tree)
        (self.tree / "scripts/Fingerprint.lean").write_text(
            "def main (_ : List String) : IO UInt32 := do\n  IO.print (← IO.FS.readFile \"fp.txt\")\n  return 0\n")
        (self.tree / ".gitignore").write_text("build/\n")
        (self.tree / "lakefile.lean").write_text("-- one\n")
        (self.tree / "lake-manifest.json").write_text("{}\n")
        self.binary = self.tree / ".lake/build/bin/dn-compiler"
        self.binary.parent.mkdir(parents=True)
        self.binary.write_text('#!/bin/sh\nif [ "$1" = --help ]; then cat help.txt; exit 0; fi\necho "ran $1"\n')
        self.binary.chmod(0o755)
        (self.tree / "help.txt").write_text("usage\n")
        self.olean = self.tree / ".lake/build/lib/lean/DN/A.olean"
        self.olean.parent.mkdir(parents=True)
        (self.tree / "check.py").write_text("import subprocess\nprint(subprocess.run(['.lake/build/bin/dn-compiler', "
                                            "'a'], capture_output=True, text=True, check=True).stdout)\n")
        subprocess.run(["git", "init", "-q", str(self.tree)], check=True)
        self.rebuild(b"one", "one")

    def rebuild(self, olean: bytes, code: str) -> None:
        """The library compiled anew to `olean`, its command's code `code`, and the executable after it."""
        (self.tree / "fp.txt").write_text(f'["Q",["{code}"],[]]\n["c",["a"],[0]]\n')
        self.olean.write_bytes(olean)
        later = self.olean.stat().st_mtime_ns + 10**9
        os.utime(self.binary, ns=(later, later))

    def run_check(self) -> str:
        done = subprocess.run([sys.executable, "scripts/once.py", "run", "probe", "--", sys.executable, "check.py"],
                              cwd=self.tree, capture_output=True, text=True, check=True, timeout=300)
        return done.stdout + done.stderr

    def test_dn_compiler_counts_by_what_its_commands_run_and_how_it_starts(self) -> None:
        self.assertIn("ran a", self.run_check())
        inputs = once.passes(json.loads((self.tree / "build/stamps/probe.json").read_text()))[0]["inputs"]
        self.assertEqual(list(inputs["compiler"]), ["a"])
        self.assertNotIn(".lake/build/bin/dn-compiler", inputs["files"])
        self.assertIn("lakefile.lean", inputs["files"])
        self.assertIn("DN SKIP", self.run_check())
        # The library built anew to the same code runs nothing again.
        self.rebuild(b"two", "one")
        self.assertIn("DN SKIP", self.run_check())
        # Other code for the command, or another start of the executable, does.
        self.rebuild(b"three", "two")
        self.assertIn("ran a", self.run_check())
        self.assertIn("DN SKIP", self.run_check())
        (self.tree / "help.txt").write_text("other usage\n")
        self.rebuild(b"four", "two")
        self.assertIn("ran a", self.run_check())
        # An executable older than the library may not be what it compiles to.
        later = self.binary.stat().st_mtime_ns + 10**9
        os.utime(self.olean, ns=(later, later))
        self.assertIn("ran a", self.run_check())
        self.rebuild(b"four", "two")
        (self.tree / "lakefile.lean").write_text("-- two\n")
        self.assertIn("ran a", self.run_check())


class Schema(unittest.TestCase):
    """What a stamp records and how a trace is read are pinned to `SCHEMA`: a change of either fails
    here until `SCHEMA` is raised with the pin, and the stamps made before it then count for nothing."""

    LOG = """\
7 execve("/r/s.py", ["python3", "s.py"], 0x1 /* 3 vars */) = 0
7 openat(AT_FDCWD</r>, "a.txt", O_RDONLY|O_CLOEXEC) = 3</r/a.txt>
7 openat(AT_FDCWD</r>, "out", O_WRONLY|O_CREAT|O_TRUNC, 0666) = 4</r/out>
7 openat(AT_FDCWD</r>, "log", O_RDWR|O_APPEND) = 5</r/log>
7 newfstatat(AT_FDCWD</r>, "/r/missing", 0x7f, 0) = -1 ENOENT (No such file or directory)
7 newfstatat(AT_FDCWD</r>, "lnk", {st_mode=S_IFLNK|0777, st_size=3, ...}, AT_SYMLINK_NOFOLLOW) = 0
7 newfstatat(3</r/a.txt>, "", {st_mode=S_IFREG|0644, st_size=1, ...}, AT_EMPTY_PATH) = 0
7 newfstatat(AT_FDCWD</r>, "", 0x7f, 0) = -1 ENOENT (No such file or directory)
7 openat(AT_FDCWD</r>, "/r/d", O_RDONLY|O_NONBLOCK|O_CLOEXEC|O_DIRECTORY) = 6</r/d>
7 renameat2(AT_FDCWD</r>, "out", AT_FDCWD</r>, "final", RENAME_NOREPLACE) = 0
7 unlink("/r/locked") = -1 EACCES (Permission denied)
7 readlink("/r/lnk", "a.txt", 4096) = 5
"""

    def test_what_a_stamp_records_is_pinned_to_its_schema(self) -> None:
        rules = [sorted(once.ASIDE), sorted(once.WHERE), sorted(once.OPENS), sorted(once.WRITES), sorted(once.LOOKUPS),
                 sorted(once.WITH_DIRFD), sorted(once.READING), sorted(once.VALUED), sorted(once.ELSEWHERE),
                 sorted(once.GIT_AS_FILES),
                 once.VOLATILE.pattern, once.SECRET.pattern, once.SECRET_ARG.pattern]
        t = parsed(self.LOG)
        seen = [sorted(getattr(t, n)) for n in ("read", "named", "listed", "absent", "written", "updated")]
        pin = hashlib.sha256(json.dumps([rules, seen]).encode()).hexdigest()[:16]
        self.assertEqual((once.SCHEMA, pin), (2, "68f3f56e892b2b4d"))

    def test_the_schema_is_in_every_key(self) -> None:
        keys = once.tracer(), once.tree_key("lane", ["run"])
        with mock.patch.object(once, "SCHEMA", once.SCHEMA + 1):
            self.assertNotEqual((once.tracer(), once.tree_key("lane", ["run"])), keys)


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
