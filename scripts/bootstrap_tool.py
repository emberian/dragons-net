#!/usr/bin/env python3
"""Obtain digest-pinned Linux x86-64 tools for the reproducible CI/native lane."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import platform
import subprocess
import sys
import tarfile
import tempfile

ROOT = Path(__file__).resolve().parents[1]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("tool", choices=["cake", "elan"])
    args = parser.parse_args()
    if platform.system() != "Linux" or platform.machine() != "x86_64":
        parser.error("these bootstrap artifacts target Linux x86-64")
    if sys.version_info < (3, 12):
        parser.error("Python 3.12+ is required for safe archive extraction")
    pin = json.loads((ROOT / "tools.lock.json").read_text())[args.tool]
    directory = ROOT / ".deps/tools"
    directory.mkdir(parents=True, exist_ok=True)
    target = directory / (args.tool + "-" + pin["version"])
    if not target.exists():
        with tempfile.TemporaryDirectory(dir=directory) as temp:
            temp = Path(temp)
            archive = temp / "download.tar.gz"
            subprocess.run(["curl", "--fail", "--location", "--retry", "3", pin["url"],
                            "--output", str(archive)], check=True, stdout=sys.stderr)
            if hashlib.sha256(archive.read_bytes()).hexdigest() != pin["sha256"]:
                raise SystemExit("tool archive digest mismatch")
            content = temp / "content"
            content.mkdir()
            with tarfile.open(archive) as tar:
                tar.extractall(content, filter="data")
            (content / "archive.sha256").write_text(pin["sha256"] + "\n")
            os.rename(content, target)
    if (target / "archive.sha256").read_text().strip() != pin["sha256"]:
        raise SystemExit("existing bootstrap directory does not match the lock; use a clean .deps/tools")
    if args.tool == "cake":
        source = target / "cake-x64-64"
        subprocess.run(["make", "-C", str(source), "cake", "LDFLAGS=-Wl,-z,noexecstack"],
                       check=True, stdout=sys.stderr)
        print(source / "cake")
    else:
        subprocess.run([str(target / "elan-init"), "-y", "--no-modify-path", "--default-toolchain", "none"],
                       check=True, stdout=sys.stderr)


if __name__ == "__main__":
    main()
