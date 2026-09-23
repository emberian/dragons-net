#!/usr/bin/env python3
# SPDX-License-Identifier: AGPL-3.0-or-later
"""Source gates run before the build: Lean modules, the offline RFC collection and the
backend patch.

Every module under `lean/DN` is checked by scripts/SourceGate.lean, in import order and with
the lakefile's Lean options, before any of its commands is elaborated. Files that may
define syntax are pinned by SHA-256 below. The gate rules were reviewed for one Lean
release; a toolchain change needs a new review.
"""
from __future__ import annotations

from collections.abc import Callable
from concurrent.futures import FIRST_COMPLETED, Future, ThreadPoolExecutor, wait
import graphlib
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[1]
GATE = ROOT / "scripts" / "SourceGate.lean"
LEAN_TOOLCHAIN = "leanprover/lean4:v4.30.0"
# How the extraction manifest marks a file kept as it was, byte for byte.
UNMODIFIED = "Unmodified migration reference"
# The snapshot, and the one file in it this project wrote rather than took.
SNAPSHOT = "migration"
SNAPSHOT_OWN = ("migration/dataplane/README.md",)
# Reviewed files allowed to define syntax, pinned by SHA-256. No module defines syntax today.
SYNTAX_FILES: dict[str, str] = {}
IMPORT = re.compile(r"^(?:public\s+|private\s+)?(?:meta\s+)?import\s+(?:all\s+)?(\S+)", re.MULTILINE)
NAME = re.compile(r"[A-Za-z_][A-Za-z0-9_]*")
LEAN_OPTIONS = re.compile(r"leanOptions\s*:=\s*#\[(.*?)\]", re.DOTALL)
OPTION = re.compile(r"⟨`([\w.]+),\s*(\w+)⟩")


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def tree_errors(root: Path) -> list[str]:
    """Lake and the gate must agree on the modules: plain names only, no links, no other files."""
    errors = []
    for path in sorted((root / "lean").rglob("*")):
        rel = path.relative_to(root)
        if path.is_symlink():
            errors.append(f"{rel}: symlink under lean/")
        elif path.is_file() and (path.suffix != ".lean" or not path.is_relative_to(root / "lean/DN")):
            errors.append(f"{rel}: unexpected file under lean/")
        elif not NAME.fullmatch(path.stem if path.is_file() else path.name):
            errors.append(f"{rel}: name is not a plain identifier")
    return errors


def modules(root: Path) -> dict[str, Path]:
    lean = root / "lean"
    return {".".join(path.relative_to(lean).with_suffix("").parts): path
            for path in sorted((lean / "DN").rglob("*.lean")) if path.is_file()}


def stale_build_errors(root: Path) -> list[str]:
    """Lake leaves the compiled module of a deleted source behind, and `leanchecker` then
    re-checks a module that is no longer part of the library."""
    built = root / ".lake/build/lib/lean/DN"
    if not built.is_dir():
        return []
    known = modules(root)
    errors = []
    for directory, _, names in os.walk(built, followlinks=False):
        for name in sorted(names):
            path = Path(directory) / name
            if path.suffix != ".olean" and not name.endswith(".olean.private"):
                continue
            stem = name.removesuffix(".olean.private").removesuffix(".olean")
            module = "DN." + ".".join((*Path(directory).relative_to(built).parts, stem))
            if module not in known:
                errors.append(f"{path.relative_to(root)}: build output of a module that no longer "
                              "exists; run lake clean")
    return errors


def static_errors(root: Path, pins: dict[str, str]) -> list[str]:
    """Checks that need no Lean: toolchain, source tree, pins, digests and build outputs."""
    errors = tree_errors(root) + stale_build_errors(root)
    toolchain = (root / "lean-toolchain").read_text().strip()
    if toolchain != LEAN_TOOLCHAIN:
        errors.append(f"lean-toolchain is {toolchain}; the source gate rules were reviewed for "
                      f"{LEAN_TOOLCHAIN}, review scripts/SourceGate.lean for the new release")
    for name, pinned in pins.items():
        path = root / name
        if not path.is_file() or digest(path) != pinned:
            errors.append(f"{name}: changed file with syntax definitions; review it and update its pin")
    errors += rfc_errors(root)
    for item in json.loads((root / "backend/lock.json").read_text())["patches"]:
        if digest(root / "backend" / item["path"]) != item["sha256"]:
            errors.append(f"backend patch digest mismatch: {item['path']}")
    errors += snapshot_errors(root)
    return errors


def rfc_errors(root: Path) -> list[str]:
    """The stored RFCs are the ones the manifest names, with the bytes it records.

    The digests answer "did a stored document change"; the walk answers "is a document here that
    nobody recorded", which the digests cannot see and which would make the collection quietly
    larger than what has been read.
    """
    documents = json.loads((root / "rfcs/manifest.json").read_text())["documents"]
    errors = []
    for name, item in documents.items():
        path = root / "rfcs" / name
        if not path.is_file():
            errors.append(f"RFC missing: {name}")
        elif digest(path) != item["sha256"]:
            errors.append(f"RFC digest mismatch: {name}")
    for path in sorted((root / "rfcs").iterdir()):
        name = path.name
        if path.is_symlink():
            errors.append(f"the RFC collection carries a symlink: {name}")
        elif path.is_file() and name != "manifest.json" and name not in documents:
            errors.append(f"the RFC collection carries a document the manifest does not record: {name}")
    return errors


def snapshot_errors(root: Path) -> list[str]:
    """Files the manifest records as preserved references must still be their source bytes.

    The snapshot is a reference for extraction, not a build target: what makes it useful is that
    it is unchanged, and what makes that claim checkable is the digest the manifest already
    carries. The digests say the recorded files did not change; the walk below says the record is
    all of them, because a file nobody recorded could change without anyone noticing.
    """
    manifest = root / "docs/provenance.json"
    if not manifest.is_file():
        return ["docs/provenance.json is missing; it records where the preserved files came from"]
    try:
        entries = json.loads(manifest.read_text())["files"]
        recorded = [(str(item["destination"]), str(item["changes"]), str(item["source_sha256"]))
                    for item in entries]
    except (ValueError, TypeError, KeyError) as error:
        return [f"docs/provenance.json is not a manifest this check can read: {error}"]

    errors = []
    preserved: set[str] = set()
    listed = {destination for destination, _, _ in recorded}
    for destination, changes, recorded_digest in recorded:
        if not changes.startswith(UNMODIFIED):
            continue
        candidate = Path(destination)
        if candidate.is_absolute() or ".." in candidate.parts:
            errors.append(f"preserved reference is outside the tree: {destination}")
            continue
        preserved.add(destination)
        path = root / candidate
        if path.is_symlink():
            errors.append(f"preserved reference is a symlink: {destination}")
        elif not path.is_file():
            errors.append(f"preserved reference is missing: {destination}")
        elif digest(path) != recorded_digest:
            errors.append(f"preserved reference changed: {destination}")
    if not preserved:
        errors.append("the manifest records no preserved reference; the snapshot check covers nothing")
    snapshot = root / SNAPSHOT
    for path in sorted(snapshot.rglob("*")) if snapshot.is_dir() else []:
        name = path.relative_to(root).as_posix()
        if path.is_symlink():
            errors.append(f"the snapshot carries a symlink: {name}")
        elif path.is_file() and name not in listed and name not in SNAPSHOT_OWN:
            errors.append(f"the snapshot carries a file the manifest does not record: {name}")
    return errors


def imports(source: str) -> set[str]:
    """Imported module names, for scheduling only: the gate itself checks the real header."""
    return {raw.replace("«", "").replace("»", "") for raw in IMPORT.findall(source)}


def lean_options(root: Path) -> list[str]:
    block = LEAN_OPTIONS.search((root / "lakefile.lean").read_text())
    if block is None:
        raise ValueError("lakefile.lean: leanOptions not found")
    return [arg for name, value in OPTION.findall(block.group(1))
            for arg in ("--option", f"{name}={value}")]


def run_in_order(graph: dict[str, set[str]], check: Callable[[str], str]) -> dict[str, str | None]:
    """Run `check` on every module after the modules it imports, in parallel.

    The result maps each module to its failure output, `""` when it passed, or `None` when it
    was skipped because an import failed.
    """
    sorter = graphlib.TopologicalSorter(graph)
    sorter.prepare()
    results: dict[str, str | None] = {}
    with ThreadPoolExecutor(os.cpu_count() or 1) as pool:
        running: dict[Future[str], str] = {}
        while sorter.is_active():
            for module in sorter.get_ready():
                if any(results[dep] != "" for dep in graph[module]):
                    results[module] = None
                    sorter.done(module)
                else:
                    running[pool.submit(check, module)] = module
            if running:
                finished, _ = wait(running, return_when=FIRST_COMPLETED)
                for future in finished:
                    module = running.pop(future)
                    results[module] = future.result()
                    sorter.done(module)
    return results


def gate_errors(root: Path, pins: dict[str, str]) -> list[str]:
    """Run the Lean source gate over every module, dependencies first."""
    lean = root / "lean"
    files: dict[str, Path] = {}
    for path in sorted((lean / "DN").rglob("*.lean")):
        module = ".".join(path.relative_to(lean).with_suffix("").parts)
        if module in files or not path.is_file():
            return [f"{path.relative_to(root)}: cannot be checked as module {module}"]
        files[module] = path
    graph = {module: imports(path.read_text()) & files.keys() for module, path in files.items()}
    try:
        options = lean_options(root)
    except ValueError as error:
        return [str(error)]
    pinned = {name for name, value in pins.items()
              if (root / name).is_file() and digest(root / name) == value}
    env = {k: v for k, v in os.environ.items() if k != "LEAN_PATH"}

    def run(module: str, out: str) -> str:
        rel = files[module].relative_to(root)
        args = ["lean", "--run", str(GATE), "--out", out, *options,
                *(["--syntax"] if str(rel) in pinned else []), str(files[module]), module]
        try:
            result = subprocess.run(args, cwd=ROOT, env=env, text=True, capture_output=True,
                                    check=False, timeout=1800)
        except subprocess.TimeoutExpired:
            return f"{rel}: source gate timed out"
        if result.returncode == 0:
            return ""
        return (result.stdout + result.stderr).strip() or f"{rel}: source gate failed"

    try:
        with tempfile.TemporaryDirectory() as out:
            results = run_in_order(graph, lambda module: run(module, out))
    except graphlib.CycleError as error:
        return [f"import cycle: {' -> '.join(error.args[1])}"]
    return [f"{files[module].relative_to(root)}: not checked, it imports a module that failed "
            "the source gate" if output is None else output
            for module, output in sorted(results.items()) if output != ""]


def check(root: Path = ROOT, pins: dict[str, str] = SYNTAX_FILES) -> list[str]:
    return static_errors(root, pins) + gate_errors(root, pins)


if __name__ == "__main__":
    # The proofs stage re-checks the build outputs alone: the kernel re-check reads them.
    outputs_only = sys.argv[1:] == ["outputs"]
    errors = stale_build_errors(ROOT) if outputs_only else check()
    if errors:
        sys.exit("\n".join(errors))
    print("structure: build outputs OK" if outputs_only
          else "structure: Lean source gate, build outputs, preserved snapshot, RFC and backend digests OK")
