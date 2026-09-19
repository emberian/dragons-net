#!/usr/bin/env python3
"""Fetch exact upstream sources and apply the curated patch in an isolated directory."""
from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess
import tempfile
from typing import Any

ROOT = Path(__file__).resolve().parents[1]
LOCK = json.loads((ROOT / "backend/lock.json").read_text())


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
        untracked = subprocess.check_output(["git", "ls-files", "--others", "--exclude-standard"],
                                            cwd=path, text=True, env=env)
        if untracked.strip():
            raise SystemExit(f"{name}: untracked files outside upstream ignores: {untracked}")
    print(f"{name}: pinned source and patch content verified")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("action", choices=["fetch", "verify"])
    parser.add_argument("component", choices=["cakeml", "hol"])
    args = parser.parse_args()
    {"fetch": fetch, "verify": verify}[args.action](args.component)
