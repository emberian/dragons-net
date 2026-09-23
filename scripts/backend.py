#!/usr/bin/env python3
# SPDX-License-Identifier: AGPL-3.0-or-later
"""Fetch exact upstream sources, apply the curated patch, and build the prover.

Everything lives in .deps, outside the checkout that is being proved about: the
sources are pinned by revision, the patch by digest, and the prover by the ML
compiler that built it.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import tempfile
from typing import Any

ROOT = Path(__file__).resolve().parents[1]
LOCK = json.loads((ROOT / "backend/lock.json").read_text())
# What the prover records about its own build. `smart-configure` writes the compiler it was
# given and the directory it was built for into this file, which HOL's own ignores cover, so
# `verify` tolerates it. Asking the prover beats a note kept beside it: a note records an
# intention, this records what the build used.
RECORD = ROOT / ".deps/hol/tools/Holmake/Systeml.sml"
CONFIGURED = re.compile(r'^val (POLY|HOLDIR) = "(.*)"\s*;?$', re.MULTILINE)


def sml_string(value: str) -> str:
    """An SML string literal: a path with a quote or a backslash must not end the literal."""
    return '"' + value.replace("\\", "\\\\").replace('"', '\\"') + '"'


def jobs() -> int:
    """How many build jobs: `DN_BUILD_JOBS`, or the cores this process may use. The machine's
    core count is not the same thing inside a container or under a taskset."""
    requested = os.environ.get("DN_BUILD_JOBS")
    if requested and requested.isdigit() and int(requested) > 0:
        return int(requested)
    return len(os.sched_getaffinity(0))


def run(*args: str, cwd: Path | None = None, **kwargs: Any) -> None:
    subprocess.run(args, cwd=cwd, check=True, **kwargs)


def fetch(name: str) -> None:
    spec = LOCK[name]
    destination = ROOT / ".deps" / name
    if destination.exists():
        raise SystemExit(f"Refusing to overwrite {destination}; use verify or choose a fresh checkout.")
    destination.parent.mkdir(exist_ok=True)
    with tempfile.TemporaryDirectory(prefix=f"{name}-", dir=destination.parent) as temp:
        run("git", "init", "-q", temp)
        run("git", "-C", temp, "fetch", "--depth=1", spec["url"], spec["revision"])
        run("git", "-C", temp, "checkout", "--detach", "FETCH_HEAD")
        if name == "cakeml":
            for patch in LOCK["patches"]:
                path = ROOT / "backend" / patch["path"]
                if hashlib.sha256(path.read_bytes()).hexdigest() != patch["sha256"]:
                    raise SystemExit("patch checksum mismatch")
                run("git", "-C", temp, "apply", "--check", str(path))
                run("git", "-C", temp, "apply", str(path))
        os.rename(temp, destination)
    print(destination)


def verify(name: str) -> None:
    path = ROOT / ".deps" / name
    actual = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=path, text=True).strip()
    if actual != LOCK[name]["revision"]:
        raise SystemExit(f"{name}: revision mismatch")
    # Compare source against a temporary index initialized to the pinned tree
    # plus our patches. Neither the checkout nor its index is modified.
    with tempfile.TemporaryDirectory() as temp:
        env = dict(os.environ, GIT_INDEX_FILE=str(Path(temp) / "index"))
        run("git", "read-tree", "HEAD", cwd=path, env=env)
        if name == "cakeml":
            for patch in LOCK["patches"]:
                patch_path = ROOT / "backend" / patch["path"]
                if hashlib.sha256(patch_path.read_bytes()).hexdigest() != patch["sha256"]:
                    raise SystemExit("patch checksum mismatch")
                run("git", "apply", "--cached", str(patch_path), cwd=path, env=env)
        run("git", "diff", "--exit-code", cwd=path, env=env)
        # The files the Lean transcription of the semantics was compared against. A pin that
        # no recorded source matches means the comparison was never made against this revision.
        sources = [source for source in LOCK["semantics_sources"]
                   if source["component"] == name and source["revision"] == actual]
        if not sources:
            raise SystemExit(f"{name}: no semantics source recorded for {actual}; redo the comparison "
                             "in docs/pancake-semantics.md and record the digests")
        for source in sources:
            digest = hashlib.sha256((path / source["path"]).read_bytes()).hexdigest()
            if digest != source["sha256"]:
                raise SystemExit(f"{source['path']}: content differs from the recorded semantics source")
        untracked = subprocess.check_output(["git", "ls-files", "--others", "--exclude-standard"],
                                            cwd=path, text=True, env=env)
        if untracked.strip():
            raise SystemExit(f"{name}: untracked files outside upstream ignores: {untracked}")
        # -z: a path may contain a space, and the count below is reported as a fact.
        ignored = subprocess.check_output(["git", "ls-files", "-z", "--others", "--ignored",
                                           "--exclude-standard", "--directory"],
                                          cwd=path, text=True, env=env).split("\0")
        ignored = [name for name in ignored if name]
    if name == "cakeml":
        # Upstream ignores its own build outputs (`*.uo`, `*Theory.sml`, `.HOLMK`, ...),
        # so this check would otherwise pass on a tree where a stale or substituted
        # theory object makes Holmake believe the target is already built.
        if ignored:
            listing = " ".join(ignored[:10]) + (" ..." if len(ignored) > 10 else "")
            raise SystemExit(
                f"{name}: build outputs present in the pinned tree: {listing}\n"
                "Remove them (git clean -fdX) so the proof is rebuilt from source."
            )
        print(f"{name}: pinned source and patch content verified, no build outputs present")
        return
    # The prover is built inside its own checkout, so its build outputs are expected
    # here and are not certified by this check; what is certified is the source they
    # were built from.
    print(f"{name}: pinned source verified; {len(ignored)} build outputs present, not certified")


def polyml() -> Path:
    """The pinned ML compiler, built from its pinned source and verified by the bootstrap.

    Only its standard output is captured: on a fresh checkout this builds the compiler, and a
    build that fails silently for minutes is worse than one that says what went wrong.
    """
    path = subprocess.run(["python3", "-P", str(ROOT / "scripts/bootstrap_tool.py"), "polyml"],
                          cwd=ROOT, text=True, stdout=subprocess.PIPE, check=True).stdout.strip()
    return Path(path)


def configured(record: str) -> dict[str, str]:
    """The values `smart-configure` wrote, by name."""
    return {name: value for name, value in CONFIGURED.findall(record)}


def build(name: str) -> None:
    """Build the pinned prover with the pinned ML compiler.

    `smart-configure` works out where poly and its library are from the command line it was
    invoked with, so the override file states both instead: a poly found on PATH would build a
    prover nobody pinned. What the build then used is recorded by the prover itself.
    """
    if name != "hol":
        raise SystemExit("only the prover is built here; Holmake builds the proofs themselves")
    path = ROOT / ".deps/hol"
    if not path.is_dir():
        raise SystemExit(f"{path} does not exist; fetch it first")
    verify(name)
    poly = polyml()
    if RECORD.is_file() and configured(RECORD.read_text()).get("POLY") != str(poly):
        raise SystemExit(f"{path} was configured for another compiler; building over it would "
                         "leave that one's objects behind. Remove the checkout and fetch it again.")
    # The override is kept, not deleted: it is what a later `smart-configure` in this tree would
    # read, and HOL's own ignores cover it, so `verify` tolerates it either way.
    override = path / "tools-poly/poly-includes.ML"
    override.write_text(f'val poly = {sml_string(str(poly))};\n'
                        f'val polymllibdir = {sml_string(str(poly.parents[1] / "lib"))};\n'
                        "val MLTON = NONE;\n")
    # --script, not the script on standard input: `poly < file` prints a compile error and exits
    # successfully, so a configuration that did not happen would look like one that did.
    run(str(poly), "--script", "tools/smart-configure.sml", cwd=path)
    run(str(path / "bin/build"), "--stdknl", f"-j{jobs()}", cwd=path)
    print(f"hol: {built_with_pinned_polyml()}")


def check_record(record: str | None, poly: Path, holdir: Path) -> str:
    """Refuse a prover that was not configured here, or was configured for another compiler.

    `HOLDIR` matters as much as `POLY`: both are absolute paths compiled into the prover, so a
    checkout that moved carries a prover that cannot run, and says so now rather than hours in.
    """
    if record is None:
        raise SystemExit("the prover is not configured; build it with scripts/backend.py build hol")
    values = configured(record)
    for name, expected in (("POLY", str(poly)), ("HOLDIR", str(holdir))):
        if values.get(name) != expected:
            raise SystemExit(f"the prover records {name} as {values.get(name)!r}, not {expected!r}; "
                             "remove .deps/hol, fetch it again and rebuild it")
    return f"built with the pinned compiler at {poly}"


def built_with_pinned_polyml() -> str:
    # Asking for the compiler here is what verifies its installed tree against its manifest.
    return check_record(RECORD.read_text() if RECORD.is_file() else None, polyml(), ROOT / ".deps/hol")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("action", choices=["fetch", "verify", "build", "built-with"])
    parser.add_argument("component", choices=["cakeml", "hol"])
    args = parser.parse_args()
    if args.action == "built-with":
        if args.component != "hol":
            raise SystemExit("only the prover records what built it")
        print(built_with_pinned_polyml())
    else:
        {"fetch": fetch, "verify": verify, "build": build}[args.action](args.component)
