#!/usr/bin/env python3
# SPDX-License-Identifier: AGPL-3.0-or-later
"""Run a check once per inputs.

`once.py run NAME [--log FILE] -- COMMAND...` runs COMMAND under strace, its standard input empty,
and when it passes records what it read: each file by content, each directory it listed by its
names, each path it looked for and did not find, each symbolic link on the way by its target, in
the repository and outside it (`/proc`, `/sys`, `/dev`, `/run` and temporary files aside). Next
time, if the command, the environment, this script and every one of those are the same, it says
`DN SKIP` instead of running, and leaves FILE as it was; otherwise it runs, a copy of its output
going to FILE. A path the check writes and does not read is its output. A file of the sources the
check both read and wrote, an input that changed while the check ran, or a path the trace leaves
unresolved leaves the run unrecorded, so it runs every time. Git's own files stand for the list
of files git tracks, `HEAD` and the refs. `dn-compiler` stands for the compiled library modules
its commands reach (`scripts/Fingerprint.lean`), the toolchain and the build's options, when the
executable is newer than them. What the run requires of the documents (`lanes.require`) is kept
with its stamp, for `scripts/check_documents.py`. The stamps lie in `build/stamps`, or where
`DN_STAMPS` says; `DN_ONCE=off` runs everything again and records it.

`once.py check NAME -- COMMAND...` and `once.py stamp NAME KEY` do the same by every file of the
tree, for a check that cannot be traced; `once.py key NAME` prints the key of NAME's inputs alone,
for CI, whose jobs record what they passed on as an artifact named by that key
(`scripts/prior_pass.py`)."""
from __future__ import annotations

import codecs
import functools
import hashlib
import json
import os
from pathlib import Path
import platform
import re
import subprocess
import sys
import tempfile
import time
from typing import Any

ROOT = Path(__file__).resolve().parent.parent
# What the source gate and the build of the Lean library read, and the proofs over what it built.
BUILD = ["lean", "lakefile.lean", "lake-manifest.json", "lean-toolchain", "tools.lock.json", "backend/lock.json",
         "backend/patches", "rfcs", "migration", "docs/provenance.json", "scripts/check.sh",
         "scripts/check_structure.py", "scripts/SourceGate.lean", "scripts/measured.py", "scripts/build_archive.py",
         "scripts/bootstrap_tool.py", "scripts/once.py"]
INPUTS = {"check-gate": BUILD, "check-build": BUILD,
          "check-proofs": [*BUILD, "scripts/Audit.lean", "scripts/nanoda.json"]}
NAME = re.compile(r"[a-z0-9-]+")
# Variables a check is keyed by: all but those that change from run to run without changing what a
# check does, and secrets, of which only the presence counts.
VOLATILE = re.compile(r"(HOSTNAME|PWD|OLDPWD|SHLVL|_|TERM|COLUMNS|LINES|INVOCATION_ID|JOURNAL_STREAM|DISPLAY"
                      r"|SSH_[A-Z_]+|XDG_[A-Z_]+|GITHUB_[A-Z_]+|RUNNER_[A-Z_]+|ACTIONS_[A-Z_]+"
                      r"|DN_ONCE|DN_STAMPS|DN_DOCUMENTED)")
SECRET = re.compile(r"[A-Z_]*(TOKEN|SECRET|PASSWORD|KEY)[A-Z_]*")
# What no check's outcome rests on.
ASIDE = ("/proc/", "/sys/", "/dev/", "/run/", "/tmp/", "/var/tmp/")  # noqa: S108 # left out, not used
OPENS = {"openat", "open", "openat2", "creat"}
# Syscalls that change the path they name.
WRITES = {"mkdir", "mkdirat", "unlink", "unlinkat", "rename", "renameat", "renameat2", "rmdir", "symlink",
          "symlinkat", "link", "linkat", "chmod", "fchmodat", "fchmodat2", "chown", "lchown", "fchownat",
          "utime", "utimes", "utimensat", "futimesat", "truncate", "mknod", "mknodat"}
LOOKUPS = {"newfstatat", "fstatat64", "statx", "stat", "lstat", "access", "faccessat", "faccessat2",
           "readlink", "readlinkat"}
WITH_DIRFD = {"openat", "openat2", "newfstatat", "fstatat64", "statx", "faccessat", "faccessat2", "readlinkat",
              "mkdirat", "unlinkat", "renameat", "renameat2", "symlinkat", "linkat", "fchmodat", "fchmodat2",
              "fchownat", "utimensat", "futimesat", "mknodat", "execveat"}
STRING = re.compile(r'"((?:[^"\\]|\\.)*)"')
FD = re.compile(r"(?:AT_FDCWD|-?\d+)<((?:[^>\\]|\\.)*)>")
# A call, its arguments and its result; strace pads before the result to align it.
CALL = re.compile(r"(\w+)\((.*)\)\s+= (.*)", re.DOTALL)
COMPILER = ".lake/build/bin/dn-compiler"
# What the compiled library rests on besides its modules: the toolchain and the build's options.
BUILT_BY = ["lean-toolchain", "lakefile.lean", "lake-manifest.json"]


def environment() -> dict[str, str]:
    """What a check reads besides its files: the platform, the interpreter and the variables."""
    env = {k: ("set" if SECRET.fullmatch(k) else v) for k, v in os.environ.items() if not VOLATILE.fullmatch(k)}
    env["platform"] = platform.platform()
    env["python"] = sys.version
    return env


def tracer() -> str:
    """This script and the one that names what `dn-compiler` runs: a stamp another made counts for
    nothing."""
    whole = hashlib.sha256()
    for name in ("scripts/once.py", "scripts/Fingerprint.lean"):
        file = ROOT / name
        whole.update(file.read_bytes() if file.is_file() else b"none")
    return whole.hexdigest()


def unescape(text: str) -> str:
    """A string as strace prints it, its C escapes undone."""
    raw: bytes = codecs.escape_decode(text.encode())[0]
    return raw.decode("utf-8", "surrogateescape")


class Trace:
    """What a traced run did to paths, from strace's log."""

    def __init__(self, cwd: str) -> None:
        # The first process starts in `cwd`; a child starts in its parent's.
        self.start = cwd
        self.cwd: dict[str, str] = {}
        self.parent: dict[str, str] = {}
        self.read: set[str] = set()
        self.named: set[str] = set()
        self.listed: set[str] = set()
        self.absent: set[str] = set()
        self.written: set[str] = set()
        self.updated: set[str] = set()
        self.ran: list[tuple[str, list[str]]] = []
        self.unresolved: list[str] = []

    def where(self, pid: str) -> str | None:
        """Where `pid` runs, as far as the log has shown."""
        seen: set[str] = set()
        while pid not in self.cwd and pid in self.parent and pid not in seen:
            seen.add(pid)
            pid = self.parent[pid]
        return self.cwd.get(pid)

    def resolve(self, pid: str, call: str, args: str) -> list[str]:
        """The paths a call names, made absolute; one that cannot be is noted as unresolved."""
        strings = [unescape(s) for s in STRING.findall(args)]
        if call in WITH_DIRFD:
            fd = FD.match(args)
            base = unescape(fd.group(1)) if fd else None
            count = 2 if call in {"renameat", "renameat2", "linkat"} else 1
        else:
            base = self.where(pid)
            count = 2 if call in {"rename", "link", "symlink"} else 1
        out = []
        for s in strings[:count]:
            if s.startswith("/"):
                out.append(os.path.normpath(s))
            elif base is not None and base.startswith("/"):
                out.append(os.path.normpath(Path(base) / s) if s else base)
            else:
                self.unresolved.append(f"{call}({args[:120]})")
        return out

    def opened(self, pid: str, call: str, args: str, result: str, failed: bool, missing: bool) -> None:
        paths = self.resolve(pid, call, args)
        writes = call == "creat" or any(f in args for f in ("O_WRONLY", "O_RDWR", "O_CREAT", "O_TRUNC",
                                                            "O_APPEND"))
        reads = call != "creat" and "O_WRONLY" not in args and "O_TRUNC" not in args
        if missing:
            self.absent.update(paths)
            return
        if failed:
            self.named.update(paths)
            return
        fd = FD.search(result)
        real = os.path.normpath(unescape(fd.group(1))) if fd else (paths[0] if paths else None)
        if real is None:
            return
        self.named.update(paths)
        if "O_DIRECTORY" in args or Path(real).is_dir():
            self.listed.add(real)
            return
        if reads:
            self.read.add(real)
        if writes:
            self.written.add(real)
            if reads:
                self.updated.add(real)

    def call(self, pid: str, call: str, args: str, result: str) -> None:
        failed = result.startswith("-1")
        missing = failed and ("ENOENT" in result or "ENOTDIR" in result)
        cwd = re.match(r"AT_FDCWD<((?:[^>\\]|\\.)*)>", args)
        if cwd:
            self.cwd[pid] = unescape(cwd.group(1))
        if call == "getcwd" and not failed:
            self.cwd[pid] = unescape(STRING.findall(args)[0])
        elif call in {"chdir", "fchdir"}:
            if not failed:
                fd = FD.match(args)
                paths = [unescape(fd.group(1))] if fd else self.resolve(pid, call, args)
                if paths:
                    self.cwd[pid] = paths[0]
        elif call in OPENS:
            self.opened(pid, call, args, result, failed, missing)
        elif call in LOOKUPS:
            paths = self.resolve(pid, call, args)
            (self.absent if missing else self.read).update(paths)
        elif call in {"execve", "execveat"}:
            paths = self.resolve(pid, call, args)
            if missing:
                self.absent.update(paths)
            elif not failed:
                argv = [unescape(s) for s in STRING.findall(args)[1:]]
                self.read.update(paths)
                self.ran.extend((p, argv) for p in paths)
        elif call in WRITES:
            paths = self.resolve(pid, call, args)
            if missing:
                self.absent.update(paths)
            elif not failed:
                self.written.update(paths)

    def parse(self, log: str) -> Trace:
        lines = log.splitlines()
        for line in lines:
            child = re.match(r"(\d+)\s+(?:<\.\.\. )?(?:clone|clone3|fork|vfork)\b.*= (\d+)$", line.strip())
            if child:
                self.parent[child.group(2)] = child.group(1)
        if lines:
            self.cwd[lines[0].strip().partition(" ")[0]] = self.start
        pending: dict[str, str] = {}
        for line in lines:
            pid, _, body = line.strip().partition(" ")
            body = body.strip()
            if body.endswith("<unfinished ...>"):
                pending[pid] = body[: -len("<unfinished ...>")].rstrip()
                continue
            resumed = re.match(r"<\.\.\. (\w+) resumed>(.*)", body)
            if resumed:
                body = pending.pop(pid, resumed.group(1) + "(") + resumed.group(2)
            call = CALL.fullmatch(body)
            if call:
                self.call(pid, *call.groups())
        return self


def key_of(path: str) -> str | None:
    """How a path is recorded: relative to the repository if it lies in it, absolute otherwise,
    nothing if no check's outcome rests on it."""
    root = str(ROOT)
    if path == root or path.startswith(root + "/"):
        rel = os.path.relpath(path, root)
        return None if rel.startswith("build/stamps") or "/__pycache__/" in f"/{rel}/" else rel
    if path.startswith(ASIDE) or f"{path}/" in ASIDE:
        return None
    return path


def where(key: str) -> Path:
    return Path(key) if key.startswith("/") else ROOT / key


class Hashes:
    """Content digests, kept by size, time and inode so that an unchanged file is not read again. A
    file's time moves in steps of the kernel's clock, so one changed again within a step keeps it;
    the digest of a file changed less than `RACY` before it was read is not kept."""

    RACY = 2_000_000_000

    def __init__(self, path: Path) -> None:
        self.path = path
        try:
            self.known: dict[str, list[object]] = json.loads(path.read_text())
        except (OSError, ValueError):
            self.known = {}

    def of(self, key: str) -> str | None:
        file = where(key)
        try:
            st = file.stat()
        except OSError:
            return None
        if not file.is_file():
            return "dir" if file.is_dir() else "other"
        mark: list[object] = [st.st_size, st.st_mtime_ns, st.st_ino]
        known = self.known.get(key)
        if known is not None and known[:3] == mark:
            return str(known[3])
        try:
            digest = hashlib.sha256(file.read_bytes()).hexdigest()
        except OSError:
            return "unreadable"
        if time.time_ns() - st.st_mtime_ns > self.RACY:
            self.known[key] = [*mark, digest]
        return digest

    def save(self) -> None:
        self.path.parent.mkdir(parents=True, exist_ok=True)
        self.path.write_text(json.dumps(self.known))


@functools.cache
def files() -> frozenset[str]:
    """Every file git tracks or would track."""
    listed = subprocess.run(["git", "ls-files", "-z", "--cached", "--others", "--exclude-standard"], cwd=ROOT,
                            capture_output=True, check=True).stdout
    return frozenset(p for p in listed.decode().split("\0") if p)


def git_state() -> str:
    """What a check that reads git's own files rests on: the files git tracks, `HEAD` and the refs."""
    head = subprocess.run(["git", "rev-parse", "HEAD"], cwd=ROOT, capture_output=True, check=False).stdout
    refs = subprocess.run(["git", "for-each-ref"], cwd=ROOT, capture_output=True, check=False).stdout
    return hashlib.sha256("\0".join(sorted(files())).encode() + b"\0" + head + b"\0" + refs).hexdigest()


def listing(key: str, outputs: list[str]) -> str | None:
    """The names in a directory but the run's own outputs."""
    try:
        names = {p.name for p in where(key).iterdir()} - set(outputs) - {"__pycache__"}
    except OSError:
        return None
    return hashlib.sha256("\0".join(sorted(names)).encode()).hexdigest()


def link(key: str) -> str | None:
    try:
        return str(where(key).readlink())
    except OSError:
        return None


@functools.cache
def is_link(path: Path) -> bool:
    return path.is_symlink()


def links_on_the_way(key: str) -> list[str]:
    """The symbolic links a path goes through, itself included."""
    path = where(key)
    return [key_of(str(part)) or str(part) for part in [*reversed(path.parents), path] if is_link(part)]


def git_path(key: str) -> bool:
    return key == ".git" or key.startswith(".git/")


def compiled_modules(commands: set[str]) -> list[str] | None:
    """The compiled files of the library modules the commands of `dn-compiler` run, or nothing if
    one of them is no command `scripts/Fingerprint.lean` knows, or the executable is older than one
    of them, so that it may not be what they compile to."""
    try:
        prefix = subprocess.run(["lean", "--print-prefix"], cwd=ROOT, capture_output=True, text=True,
                                check=True).stdout.strip()
        done = subprocess.run(["lean", "--run", "scripts/Fingerprint.lean", *sorted(commands)], cwd=ROOT,
                              env={**os.environ, "LEAN_PATH": f"{prefix}/lib/lean:{ROOT}/.lake/build/lib/lean"},
                              capture_output=True, text=True, check=False)
    except (OSError, subprocess.SubprocessError):
        return None
    if done.returncode != 0:
        return None
    modules = {m for line in done.stdout.splitlines() for m in line.split()[1:]}
    oleans = sorted(".lake/build/lib/lean/" + m.replace(".", "/") + ".olean" for m in modules)
    try:
        newest = max((ROOT / o).stat().st_mtime_ns for o in oleans)
        if (ROOT / COMPILER).stat().st_mtime_ns < newest:
            return None
    except (OSError, ValueError):
        return None
    return oleans


def inputs(trace: Trace, hashes: Hashes, started: int) -> tuple[dict[str, Any] | None, str]:
    """What the run's outcome rests on, as it is now, or nothing and why it cannot be recorded."""
    if trace.unresolved:
        return None, f"a path the trace leaves unresolved: {trace.unresolved[0]}"

    def keys(paths: set[str]) -> set[str]:
        return {k for k in (key_of(p) for p in paths) if k is not None}

    written = keys(trace.written)
    sources = [k for k in sorted(keys(trace.updated) | (keys(trace.read) & written)) if k in files()]
    if sources:
        return None, f"it read and wrote {sources[0]}"
    commands = {argv[1] if len(argv) > 1 else "" for path, argv in trace.ran if key_of(path) == COMPILER}
    library = compiled_modules(commands) if commands and "" not in commands else None
    read = keys(trace.read) - written
    if library is not None:
        read = (read - {COMPILER}) | set(library) | set(BUILT_BY)
    deps: dict[str, Any] = {"files": {}, "dirs": {}, "absent": {}, "links": {}, "git": None}
    if any(git_path(k) for k in keys(trace.read | trace.listed | trace.absent)):
        deps["git"] = git_state()
    for key in sorted(read):
        if not git_path(key):
            deps["files"][key] = hashes.of(key)
            try:
                if deps["files"][key] != "dir" and where(key).stat().st_mtime_ns >= started:
                    return None, f"{key} changed while it ran"
            except OSError:
                pass
    for key in sorted(keys(trace.listed)):
        if not git_path(key):
            outputs = sorted(Path(w).name for w in written if str(Path(w).parent) == key or
                             (key == "." and "/" not in w))
            deps["dirs"][key] = [listing(key, outputs), outputs]
    for key in sorted(keys(trace.absent) - written):
        if not git_path(key):
            deps["absent"][key] = None
    for key in sorted(keys(trace.read | trace.named | trace.listed | trace.absent)):
        for on in links_on_the_way(key):
            deps["links"][on] = link(on)
    return deps, ""


def current(deps: dict[str, Any], hashes: Hashes) -> bool:
    """Whether every input is as recorded."""
    if deps["git"] is not None and deps["git"] != git_state():
        return False
    if any(link(k) != target for k, target in deps["links"].items()):
        return False
    if any(hashes.of(k) != digest for k, digest in deps["files"].items()):
        return False
    if any(listing(k, outputs) != names for k, (names, outputs) in deps["dirs"].items()):
        return False
    return not any(where(k).exists() for k in deps["absent"])


def traced(command: list[str], log: Path, documented: Path, copy: Path | None) -> int:
    """The command's status, run under strace, its output also copied to `copy`."""
    strace = ["strace", "-f", "-y", "-qq", "--seccomp-bpf", "-s", "65535", "-e", "trace=%file,%process",
              "-e", "signal=none", "-o", str(log), *command]
    env = {**os.environ, "DN_DOCUMENTED": str(documented)}
    if copy is None:
        return subprocess.run(strace, env=env, stdin=subprocess.DEVNULL, check=False).returncode
    copy.parent.mkdir(parents=True, exist_ok=True)
    with copy.open("wb") as out, subprocess.Popen(strace, env=env, stdin=subprocess.DEVNULL,
                                                  stdout=subprocess.PIPE, stderr=subprocess.STDOUT) as proc:
        stream = proc.stdout
        while stream is not None and (chunk := os.read(stream.fileno(), 65536)):
            sys.stdout.buffer.write(chunk)
            sys.stdout.buffer.flush()
            out.write(chunk)
        return proc.wait()


def run(name: str, command: list[str], copy: Path | None) -> int:
    stamps = Path(os.environ.get("DN_STAMPS", ROOT / "build/stamps"))
    stamp = stamps / f"{name}.json"
    hashes = Hashes(stamps / "hashes.json")
    want = {"command": command, "environment": environment(), "tracer": tracer()}
    if os.environ.get("DN_ONCE") != "off" and stamp.is_file():
        old: dict[str, Any] = {}
        try:
            old = json.loads(stamp.read_text())
            fresh = all(old.get(k) == v for k, v in want.items()) and old["inputs"] is not None and \
                current(old["inputs"], hashes)
        except (ValueError, KeyError, TypeError):
            fresh = False
        if fresh:
            hashes.save()
            print(f"DN SKIP {name}: passed on these inputs at {old['passed']}", file=sys.stderr, flush=True)
            return 0
    stamp.unlink(missing_ok=True)
    # Made before the check runs, so that a listing it takes holds the stamps' directory, as later.
    stamps.mkdir(parents=True, exist_ok=True)
    started = time.time_ns()
    with tempfile.TemporaryDirectory() as temp:
        log, documented = Path(temp) / "trace", Path(temp) / "documented"
        status = traced(command, log, documented, copy)
        if status != 0:
            return status
        trace = Trace(str(Path.cwd())).parse(log.read_text(errors="surrogateescape"))
        required = [json.loads(line) for line in documented.read_text().splitlines()] if documented.exists() else []
    files.cache_clear()
    is_link.cache_clear()
    deps, why = inputs(trace, hashes, started)
    if deps is None:
        print(f"DN ONCE {name}: runs every time, {why}", file=sys.stderr)
    record = {**want, "inputs": deps, "documented": required,
              "passed": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())}
    stamps.mkdir(parents=True, exist_ok=True)
    stamp.write_text(json.dumps(record, indent=1))
    hashes.save()
    return 0


def tree_key(name: str, command: list[str], pathspecs: list[str] | None = None) -> str:
    """What the check depends on: its name and command, the compiler named, and every file, or the
    files under `pathspecs`."""
    listed = subprocess.run(["git", "ls-files", "-z", "--cached", "--others", "--exclude-standard", "--",
                             *(pathspecs or [])], cwd=ROOT, capture_output=True, check=True).stdout
    whole = hashlib.sha256()
    for part in (name, "\0".join(command), os.environ.get("CAKE", "")):
        whole.update(part.encode() + b"\0")
    for path in sorted(p for p in listed.decode().split("\0") if p):
        file = ROOT / path
        if file.is_file():
            whole.update(path.encode() + b"\0" + hashlib.sha256(file.read_bytes()).digest())
    return whole.hexdigest()


def main() -> None:
    usage = ("usage: once.py run NAME [--log FILE] -- COMMAND... | check NAME -- COMMAND... | stamp NAME KEY"
             " | key NAME")
    args = sys.argv[1:]
    stamps = Path(os.environ.get("DN_STAMPS", ROOT / "build/stamps"))
    if len(args) >= 4 and args[0] == "run" and NAME.fullmatch(args[1]):
        copy = None
        rest = args[2:]
        if rest[:1] == ["--log"] and len(rest) >= 2:
            copy, rest = Path(rest[1]), rest[2:]
        if rest[:1] == ["--"] and len(rest) >= 2:
            raise SystemExit(run(args[1], rest[1:], copy))
    if len(args) == 3 and args[0] == "stamp" and NAME.fullmatch(args[1]) and re.fullmatch(r"[0-9a-f]{64}", args[2]):
        stamps.mkdir(parents=True, exist_ok=True)
        (stamps / f"{args[1]}-{args[2]}").write_text(time.strftime("%Y-%m-%dT%H:%M:%SZ\n", time.gmtime()))
        return
    if len(args) == 2 and args[0] == "key" and args[1] in INPUTS:
        print(f"{args[1]}-{tree_key(args[1], [], INPUTS[args[1]])}")
        return
    if len(args) < 4 or args[0] != "check" or not NAME.fullmatch(args[1]) or args[2] != "--":
        raise SystemExit(usage)
    name, command = args[1], args[3:]
    key = tree_key(name, command, INPUTS.get(name))
    stamp = stamps / f"{name}-{key}"
    if os.environ.get("DN_ONCE") != "off" and stamp.is_file():
        print(f"DN SKIP {name}: passed on this tree ({key[:12]}) at {stamp.read_text().strip()}", file=sys.stderr)
        return
    print(key)
    raise SystemExit(1)


if __name__ == "__main__":
    main()
