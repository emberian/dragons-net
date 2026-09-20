#!/usr/bin/env python3
"""Check the recorded semantics sources against the upstream repositories.

The Lean transcription was compared against exact files; `backend/lock.json` records each
one with its revision and digest. This fetches them by revision and compares, so a wrong
digest cannot sit in the lock until someone happens to fetch a checkout. It needs network.
"""
from __future__ import annotations

from collections.abc import Callable
import hashlib
import json
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
REPOSITORIES = {"cakeml": "CakeML/cakeml", "hol": "HOL-Theorem-Prover/HOL"}


def url_of(source: dict[str, str]) -> str:
    repository = REPOSITORIES[source["component"]]
    return f"https://raw.githubusercontent.com/{repository}/{source['revision']}/{source['path']}"


def fetch(url: str) -> bytes:
    return subprocess.run(["curl", "--proto", "=https", "--tlsv1.2", "--fail", "--location",
                           "--retry", "3", "--silent", "--show-error", url],
                          capture_output=True, check=True).stdout


def compare(sources: list[dict[str, str]], get: Callable[[str], bytes] = fetch) -> list[str]:
    """One message per source whose upstream bytes do not hash to the recorded digest."""
    if not sources:
        return ["no semantics source is recorded"]
    errors = []
    for source in sources:
        digest = hashlib.sha256(get(url_of(source))).hexdigest()
        if digest != source["sha256"]:
            errors.append(f"{source['path']} at {source['revision'][:7]}: "
                          f"{digest} recorded as {source['sha256']}")
    return errors


def main() -> None:
    sources = json.loads((ROOT / "backend/lock.json").read_text())["semantics_sources"]
    errors = compare(sources)
    if errors:
        sys.exit("\n".join(errors))
    print(f"semantics sources: {len(sources)} files match their recorded digests")


if __name__ == "__main__":
    main()
