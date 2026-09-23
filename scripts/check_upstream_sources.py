#!/usr/bin/env python3
# SPDX-License-Identifier: AGPL-3.0-or-later
"""Check the recorded upstream sources against the repositories they came from.

The Lean transcription of the semantics and the generated keyword table were both taken
from exact files; `backend/lock.json` records each one with its revision and digest. This
fetches them by revision and compares, so a wrong digest cannot sit in the lock until
someone happens to fetch a checkout. The stored RFCs are checked the same way, against the
url each one records. It needs network.
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
# What an RFC entry's `normalized` may name, and what it does to the fetched bytes.
NORMALIZERS = {"form-feeds-removed": lambda content: content.replace(b"\f", b"")}


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


def compare_documents(documents: dict[str, dict[str, str]],
                      get: Callable[[str], bytes] = fetch) -> list[str]:
    """One message per stored RFC whose url no longer serves the bytes that were stored.

    The digest in the manifest says the stored file did not change here; this says the file is
    still what the url gives, which is the part a reader checks the manifest for.
    """
    if not documents:
        return ["no RFC is recorded"]
    errors = []
    for name, item in documents.items():
        normalized = item.get("normalized")
        if normalized is not None and normalized not in NORMALIZERS:
            errors.append(f"{name}: recorded normalization {normalized!r} is not one this check knows")
            continue
        content = get(item["url"])
        if normalized is not None:
            content = NORMALIZERS[normalized](content)
        digest = hashlib.sha256(content).hexdigest()
        if digest != item["sha256"]:
            errors.append(f"{name} from {item['url']}: {digest} recorded as {item['sha256']}")
    return errors


def main() -> None:
    lock = json.loads((ROOT / "backend/lock.json").read_text())
    sources = lock["semantics_sources"] + lock["lexer_sources"]
    documents = json.loads((ROOT / "rfcs/manifest.json").read_text())["documents"]
    errors = compare(sources) + compare_documents(documents)
    if errors:
        sys.exit("\n".join(errors))
    print(f"upstream sources: {len(sources)} files and {len(documents)} RFCs match their "
          "recorded digests")


if __name__ == "__main__":
    main()
