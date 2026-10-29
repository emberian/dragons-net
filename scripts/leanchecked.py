#!/usr/bin/env python3
# SPDX-License-Identifier: AGPL-3.0-or-later
"""Lean's checker on the library's modules that changed: `leanchecker` replays each module's
declarations into the environment its imports make, so a module whose `.olean` and whose imports'
are those it last passed with is not replayed again. A module's key is the digest of the checker,
the toolchain's name, its `.olean` and its imports' keys; the keys of a pass are kept in
`build/proofs/leanchecked.json`, written only once the checker passed.

`leanchecked.py CHECKER` runs from the repository's root, the build in `.lake/build/lib/lean`."""
from __future__ import annotations

import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
SOURCES = ROOT / "lean"
BUILT = ROOT / ".lake/build/lib/lean"
KEPT = ROOT / "build/proofs/leanchecked.json"


def modules() -> dict[str, list[str]]:
    """Each module of the library with the library's modules it imports."""
    found = {}
    for source in sorted(SOURCES.glob("DN/**/*.lean")):
        name = ".".join(source.relative_to(SOURCES).with_suffix("").parts)
        found[name] = re.findall(r"^import\s+(DN(?:\.\w+)+)\s*$", source.read_text(), re.MULTILINE)
    return found


def keys(graph: dict[str, list[str]], checker: Path) -> dict[str, str]:
    base = hashlib.sha256(checker.read_bytes() + (ROOT / "lean-toolchain").read_bytes()).hexdigest()
    done: dict[str, str] = {}

    def key(name: str) -> str:
        if name not in done:
            olean = BUILT / Path(*name.split(".")).with_suffix(".olean")
            parts = [base, hashlib.sha256(olean.read_bytes()).hexdigest(), *(key(m) for m in sorted(graph[name]))]
            done[name] = hashlib.sha256("\n".join(parts).encode()).hexdigest()
        return done[name]

    for name in graph:
        key(name)
    return done


def main() -> None:
    if len(sys.argv) != 2:
        sys.exit("usage: leanchecked.py CHECKER")
    checker = Path(sys.argv[1])
    graph = modules()
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
