#!/usr/bin/env python3
# SPDX-License-Identifier: AGPL-3.0-or-later
"""Check the recorded upstream sources against the repositories they came from.

The Lean transcription of the semantics and the generated keyword table were both taken
from exact files; `backend/lock.json` records each one with its revision and digest. This
fetches them by revision and compares, so a wrong digest cannot sit in the lock until
someone happens to fetch a checkout. The stored RFCs are checked the same way, against the
url each one records, and the files the extraction manifest records are checked against the
repository they were taken from. It needs network.
"""
from __future__ import annotations

from collections.abc import Callable
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
REPOSITORIES = {"cakeml": "CakeML/cakeml", "hol": "HOL-Theorem-Prover/HOL"}
GITHUB = "https://github.com/"
RAW = "https://raw.githubusercontent.com/"
# A recorded source has to be a commit: a branch or a tag would turn "these bytes" into
# "whatever that name points at today", which pins nothing.
REVISION = re.compile(r"[0-9a-f]{40}")
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


def raw_url(repository: str, revision: str, path: str) -> str:
    """Where a GitHub repository's url serves file contents."""
    return f"{RAW}{repository.removeprefix(GITHUB).rstrip('/')}/{revision}/{path}"


def describes(sources: dict[str, dict[str, str]]) -> list[str]:
    """A source that cannot be checked has to say why, or a private source and a forgotten url
    look the same from here."""
    return [f"{name}: the manifest gives no url to check against and no note saying why"
            for name, source in sorted(sources.items())
            if "url" not in source and not source.get("note")]


def compare_provenance(sources: dict[str, dict[str, str]], entries: list[dict[str, str]],
                       get: Callable[[str], bytes] = fetch) -> tuple[list[str], int]:
    """Check each recorded source against the repository it came from, and say how many.

    The extraction manifest says what a file was when it was taken. Until now that was a
    statement nobody rechecked: the digests were compared once, by hand. A file whose source
    cannot be fetched is reported as that, not as a mismatch and not as a traceback, so one
    file that moved upstream does not hide the other hundred and seventy-seven.
    """
    errors, checked = describes(sources), 0
    for entry in entries:
        try:
            repository, destination = entry["source_repository"], entry["destination"]
            revision, path, recorded = (entry["source_revision"], entry["source_path"],
                                        entry["source_sha256"])
        except KeyError as missing:
            errors.append(f"an entry of the extraction manifest has no {missing}")
            continue
        source = sources.get(repository)
        if source is None:
            errors.append(f"{destination}: source repository {repository!r} is not described "
                          "in the manifest")
            continue
        url = source.get("url")
        if url is None:
            continue  # Recorded as not publicly verifiable, with the note `describes` requires.
        if not url.startswith(GITHUB):
            errors.append(f"{repository}: {url} is not a repository this check can read")
            continue
        if not REVISION.fullmatch(revision):
            errors.append(f"{destination}: {revision!r} is not a commit, so it pins no content")
            continue
        if path.startswith("/") or ".." in path.split("/"):
            errors.append(f"{destination}: source path {path!r} does not name a file in a tree")
            continue
        try:
            content = get(raw_url(url, revision, path))
        except subprocess.CalledProcessError:
            errors.append(f"{path} at {revision[:7]}: {repository} no longer serves it")
            continue
        checked += 1
        digest = hashlib.sha256(content).hexdigest()
        if digest != recorded:
            errors.append(f"{path} at {revision[:7]}: {digest} recorded as {recorded}")
    if not checked and not errors:
        errors.append("no recorded source could be checked against a repository")
    return errors, checked


def main() -> None:
    lock = json.loads((ROOT / "backend/lock.json").read_text())
    sources = lock["semantics_sources"] + lock["lexer_sources"]
    documents = json.loads((ROOT / "rfcs/manifest.json").read_text())["documents"]
    manifest = json.loads((ROOT / "docs/provenance.json").read_text())
    # Both lists: a module that was deleted still carries the digest of what it was taken from.
    entries = manifest["files"] + manifest["removed"]
    provenance, checked = compare_provenance(manifest["sources"], entries)
    errors = compare(sources) + compare_documents(documents) + provenance
    if errors:
        sys.exit("\n".join(errors))
    print(f"upstream sources: {len(sources)} files and {len(documents)} RFCs match their recorded "
          f"digests, and so do {checked} extracted files; the other {len(entries) - checked} "
          "record no public source")


if __name__ == "__main__":
    main()
