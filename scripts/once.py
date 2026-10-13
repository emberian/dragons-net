#!/usr/bin/env python3
# SPDX-License-Identifier: AGPL-3.0-or-later
"""Run a check once per tree: `once.py check NAME -- COMMAND...` succeeds if the check NAME, with
this command, passed on a tree whose every file is as it is now, and says so; otherwise it prints
the tree's key, and `once.py stamp NAME KEY` records that the check passed on that tree. The key is
taken before the check runs, so a file changed while it runs is checked again. The tree is every
file git tracks or would track, by content, so nothing a check can read is left out, or for the
checks `INPUTS` names, the files under its paths; the compiler `CAKE` names counts too. The stamps
lie in `build/stamps`, or where `DN_STAMPS` says; `DN_ONCE=off` runs everything again and stamps it.

`once.py key NAME` prints the key of NAME's inputs alone, for CI, whose jobs record what they
passed on as an artifact named by that key (`scripts/prior_pass.py`)."""
from __future__ import annotations

import hashlib
import os
from pathlib import Path
import re
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parent.parent
# What the source gate and the build of the Lean library read, and the proofs over what it built.
BUILD = ["lean", "lakefile.lean", "lake-manifest.json", "lean-toolchain", "tools.lock.json", "backend/lock.json",
         "backend/patches", "rfcs", "migration", "docs/provenance.json", "scripts/check.sh",
         "scripts/check_structure.py", "scripts/SourceGate.lean", "scripts/measured.py", "scripts/build_archive.py",
         "scripts/bootstrap_tool.py", "scripts/once.py"]
INPUTS = {"check-gate": BUILD, "check-build": BUILD,
          "check-proofs": [*BUILD, "scripts/Audit.lean", "scripts/nanoda.json"]}


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
    usage = "usage: once.py check NAME -- COMMAND... | stamp NAME KEY | key NAME"
    stamps = Path(os.environ.get("DN_STAMPS", ROOT / "build/stamps"))
    if len(sys.argv) == 4 and sys.argv[1] == "stamp" and re.fullmatch(r"[a-z0-9-]+", sys.argv[2]) and \
            re.fullmatch(r"[0-9a-f]{64}", sys.argv[3]):
        stamps.mkdir(parents=True, exist_ok=True)
        (stamps / f"{sys.argv[2]}-{sys.argv[3]}").write_text(time.strftime("%Y-%m-%dT%H:%M:%SZ\n", time.gmtime()))
        return
    if len(sys.argv) == 3 and sys.argv[1] == "key" and sys.argv[2] in INPUTS:
        print(f"{sys.argv[2]}-{tree_key(sys.argv[2], [], INPUTS[sys.argv[2]])}")
        return
    if len(sys.argv) < 5 or sys.argv[1] != "check" or not re.fullmatch(r"[a-z0-9-]+", sys.argv[2]) or \
            sys.argv[3] != "--":
        raise SystemExit(usage)
    name, command = sys.argv[2], sys.argv[4:]
    key = tree_key(name, command, INPUTS.get(name))
    stamp = stamps / f"{name}-{key}"
    if os.environ.get("DN_ONCE") != "off" and stamp.is_file():
        print(f"DN SKIP {name}: passed on this tree ({key[:12]}) at {stamp.read_text().strip()}", file=sys.stderr)
        return
    print(key)
    raise SystemExit(1)


if __name__ == "__main__":
    main()
