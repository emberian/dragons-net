#!/usr/bin/env python3
# SPDX-License-Identifier: AGPL-3.0-or-later
"""Lean's checker on the library's modules that changed: `leanchecker` replays each module's
declarations into the environment its imports make, so a module whose `.olean` files and whose
imports' are those it last passed with is not replayed again. A module's key is the digest of the
checker, the toolchain's name, its `.olean` files and the keys of the library's modules its header
imports, read from the `.olean` as the checker reads it (`scripts/ModuleImports.lean`); the keys
of a pass are kept in `build/proofs/leanchecked.json`, written only once the checker passed.

`leanchecked.py LEAN CHECKER` runs from the repository's root, the build in `.lake/build/lib/lean`."""
from __future__ import annotations

import hashlib
import json
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
BUILT = ROOT / ".lake/build/lib/lean"
KEPT = ROOT / "build/proofs/leanchecked.json"


def modules(lean: Path) -> dict[str, list[str]]:
    """Each module of the build with the library's modules it imports."""
    files = sorted(BUILT.glob("DN/**/*.olean"))
    said = subprocess.run([str(lean), "--run", str(ROOT / "scripts/ModuleImports.lean"), *map(str, files)],
                          cwd=ROOT, capture_output=True, text=True, check=True).stdout
    found = {}
    for line in said.splitlines():
        file, _, imported = line.partition("\t")
        name = ".".join(Path(file).relative_to(BUILT).with_suffix("").parts)
        found[name] = [m for m in imported.split() if m == "DN" or m.startswith("DN.")]
    if len(found) != len(files):
        sys.exit(f"leanchecked.py: the imports of {len(files)} modules read as {len(found)}")
    return found


def keys(graph: dict[str, list[str]], checker: Path) -> dict[str, str]:
    base = hashlib.sha256(checker.read_bytes() + (ROOT / "lean-toolchain").read_bytes()).hexdigest()
    done: dict[str, str] = {}

    def key(name: str) -> str:
        if name not in done:
            olean = BUILT / Path(*name.split(".")).with_suffix(".olean")
            # The parts of a module's data beside its `.olean`, which the checker reads too.
            files = [olean, *(f for f in (olean.with_suffix(".olean.server"), olean.with_suffix(".olean.private"))
                              if f.exists())]
            parts = [base, *(hashlib.sha256(f.read_bytes()).hexdigest() for f in files),
                     *(key(m) for m in sorted(graph[name]))]
            done[name] = hashlib.sha256("\n".join(parts).encode()).hexdigest()
        return done[name]

    for name in graph:
        key(name)
    return done


def main() -> None:
    if len(sys.argv) != 3:
        sys.exit("usage: leanchecked.py LEAN CHECKER")
    lean, checker = Path(sys.argv[1]), Path(sys.argv[2])
    graph = modules(lean)
    now = keys(graph, checker)
    try:
        kept = json.loads(KEPT.read_text())
    except (OSError, ValueError):
        kept = {}
    changed = [name for name in graph if kept.get(name) != now[name]]
    print(f"DN leanchecker: {len(changed)} of {len(graph)} modules changed since their last pass", flush=True)
    if changed:
        done = subprocess.run([str(checker), *changed], cwd=ROOT, check=False)
        if done.returncode != 0:
            sys.exit(done.returncode)
    KEPT.parent.mkdir(parents=True, exist_ok=True)
    temp = KEPT.with_suffix(".json.part")
    temp.write_text(json.dumps(now, indent=1, sort_keys=True) + "\n")
    temp.replace(KEPT)


if __name__ == "__main__":
    main()
