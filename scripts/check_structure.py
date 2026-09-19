#!/usr/bin/env python3
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
# Reviewed files allowed to define syntax, pinned by SHA-256.
SYNTAX_FILES = {
    "lean/DN/Compiler/ProofProducing.lean": "668a1b79c1d75804bbe6bf8fb200c275130b490b2f96527d655b4ab7515b580d",
}
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


def static_errors(root: Path, pins: dict[str, str]) -> list[str]:
    """Checks that need no Lean: toolchain, source tree, pins and digests."""
    errors = tree_errors(root)
    toolchain = (root / "lean-toolchain").read_text().strip()
    if toolchain != LEAN_TOOLCHAIN:
        errors.append(f"lean-toolchain is {toolchain}; the source gate rules were reviewed for "
                      f"{LEAN_TOOLCHAIN}, review scripts/SourceGate.lean for the new release")
    for name, pinned in pins.items():
        path = root / name
        if not path.is_file() or digest(path) != pinned:
            errors.append(f"{name}: changed file with syntax definitions; review it and update its pin")
    for name, item in json.loads((root / "rfcs/manifest.json").read_text())["documents"].items():
        if digest(root / "rfcs" / name) != item["sha256"]:
            errors.append(f"RFC digest mismatch: {name}")
    for item in json.loads((root / "backend/lock.json").read_text())["patches"]:
        if digest(root / "backend" / item["path"]) != item["sha256"]:
            errors.append(f"backend patch digest mismatch: {item['path']}")
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
    errors = check()
    if errors:
        sys.exit("\n".join(errors))
    print("structure: Lean source gate, RFC digests and backend patch digest OK")
