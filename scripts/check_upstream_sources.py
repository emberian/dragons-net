#!/usr/bin/env python3
"""Check the recorded upstream sources against the repositories they came from.

The Lean transcription of the semantics and the generated keyword table were both taken
from exact files; `backend/lock.json` records each one with its revision and digest. This
fetches them by revision and compares, so a wrong digest cannot sit in the lock until
someone happens to fetch a checkout. It needs network.
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
                           "--retry", "3", "--connect-timeout", "20", "--max-time", "120",
                              "--silent", "--show-error", url],
                          capture_output=True, check=True).stdout


def compare(sources: list[dict[str, str]], get: Callable[[str], bytes] = fetch) -> list[str]:
    """One message per source whose upstream bytes do not hash to the recorded digest."""
    if not sources:
        return ["no upstream source is recorded"]
    errors = []
    for source in sources:
        digest = hashlib.sha256(get(url_of(source))).hexdigest()
        if digest != source["sha256"]:
            errors.append(f"{source['path']} at {source['revision'][:7]}: "
                          f"{digest} recorded as {source['sha256']}")
    return errors


def main() -> None:
    lock = json.loads((ROOT / "backend/lock.json").read_text())
    sources = lock["semantics_sources"] + lock["lexer_sources"]
    errors = compare(sources)
    if errors:
        sys.exit("\n".join(errors))
    print(f"upstream sources: {len(sources)} files match their recorded digests")


if __name__ == "__main__":
    main()
