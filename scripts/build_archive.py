#!/usr/bin/env python3
"""Pack the Lean build output for the next CI job, or unpack it there.

The build job runs code from the change under test, so unpacking accepts only regular files
and directories under the parts of .lake/build that later jobs read.
"""
from __future__ import annotations

import argparse
from pathlib import Path, PurePosixPath
import tarfile

ROOT = Path(__file__).resolve().parents[1]
BUILD = ".lake/build"
CONTENT = (("lib", "lean", "DN"), ("ir", "DN"), ("bin",))


def allowed(member: tarfile.TarInfo) -> bool:
    parts = PurePosixPath(member.name).parts
    if parts[:2] != (".lake", "build") or ".." in parts:
        return False
    rest = parts[2:]
    if any(rest[: len(prefix)] == prefix for prefix in CONTENT):
        return member.isfile() or member.isdir()
    return member.isdir() and any(prefix[: len(rest)] == rest for prefix in CONTENT)


def unpack(archive: Path, root: Path) -> None:
    with tarfile.open(archive) as tar:
        members = tar.getmembers()
        for member in members:
            if not allowed(member):
                raise SystemExit(f"unexpected member in the build archive: {member.name}")
        tar.extractall(root, members=members, filter="data")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("action", choices=["pack", "unpack"])
    parser.add_argument("archive", type=Path)
    args = parser.parse_args()
    if args.action == "pack":
        with tarfile.open(args.archive, "w") as tar:
            tar.add(ROOT / BUILD, arcname=BUILD)
    else:
        unpack(args.archive, ROOT)


if __name__ == "__main__":
    main()
