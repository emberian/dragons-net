# SPDX-License-Identifier: AGPL-3.0-or-later
"""What the gate tests share: the repository, its scripts loaded as modules, a command run from the
root, the pinned tools, and a disposable source tree."""
from __future__ import annotations

import functools
import hashlib
import importlib.util
import json
from pathlib import Path
import re
import shutil
import subprocess
import sys
from typing import Any

ROOT = Path(__file__).resolve().parents[1]
DN_COMPILER = ROOT / ".lake/build/bin/dn-compiler"
CHECK = (ROOT / "scripts/check.sh").read_text()
AUDIT = re.search(r"--run scripts/Audit\.lean --regressions (\d+)", CHECK)


@functools.cache
def script(name: str) -> Any:
    """Load a script as a module under its own name, which dataclasses in it need. A script another
    one has already imported is that module, so both see the same classes."""
    path = ROOT / f"scripts/{name}.py"
    loaded = sys.modules.get(name)
    if loaded is not None and Path(getattr(loaded, "__file__", "") or "").resolve() == path:
        return loaded
    spec = importlib.util.spec_from_file_location(name, path)
    assert spec is not None and spec.loader is not None
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module


def run(args: list[str], env: dict[str, str] | None = None) -> subprocess.CompletedProcess[str]:
    return subprocess.run(args, cwd=ROOT, env=env, text=True, capture_output=True, timeout=600,
                          check=False)


def regressions() -> str:
    assert AUDIT is not None, "scripts/check.sh does not run the audit with --regressions"
    return AUDIT.group(1)


@functools.cache
def tool(name: str) -> str:
    result = subprocess.run(["python3", "scripts/bootstrap_tool.py", name], cwd=ROOT, text=True,
                            capture_output=True, check=False, timeout=1800)
    if result.returncode != 0:
        raise AssertionError(f"cannot obtain {name}:\n{result.stderr}")
    return result.stdout.strip()


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def source_tree(directory: Path) -> Path:
    for name in ("rfcs", "backend"):
        shutil.copytree(ROOT / name, directory / name)
    for name in ("lean-toolchain", "lakefile.lean"):
        shutil.copy(ROOT / name, directory / name)
    (directory / "lean/DN").mkdir(parents=True)
    # The snapshot check reads the extraction manifest, so a tree without one is
    # not the tree the gate runs on.
    (directory / "docs").mkdir()
    (directory / "migration").mkdir()
    kept = directory / "migration/kept.rs"
    kept.write_text("fn main() {}\n")
    (directory / "docs/provenance.json").write_text(json.dumps({"files": [
        {"destination": "migration/kept.rs", "source_sha256": sha256(kept),
         "changes": "Unmodified migration reference; not an active dn build target."}]}))
    return directory
