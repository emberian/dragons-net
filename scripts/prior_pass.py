#!/usr/bin/env python3
# SPDX-License-Identifier: AGPL-3.0-or-later
"""Find a pass that an earlier CI run recorded: `prior_pass.py NAME` prints `run-id=ID` for the
newest run that uploaded an unexpired artifact NAME, or `run-id=` when there is none. A job records
a pass as an artifact named by its inputs (scripts/once.py), and artifacts, unlike the Actions
cache, are seen across branches: the run on main after a merge finds what the pull request's run
passed on the same tree. Only runs of this repository's own branches count; a pull request from a
fork runs a workflow of its own, which could record anything. A run of this repository's branches
is trusted as its writers are. When the API does not answer, the checks run."""
from __future__ import annotations

import json
import os
import sys
from typing import Any
import urllib.parse
import urllib.request


def choose(listing: dict[str, Any], repository: int) -> int | None:
    """The newest run of this repository's branches that holds the artifact, if it has not expired."""
    runs = [a.get("workflow_run") or {} for a in listing.get("artifacts", []) if not a.get("expired")]
    found = [r["id"] for r in runs if r.get("repository_id") == repository == r.get("head_repository_id")
             and isinstance(r.get("id"), int)]
    return max(found, default=None)


def main() -> None:
    if len(sys.argv) != 2:
        raise SystemExit("usage: prior_pass.py NAME")
    api, repo = os.environ["GITHUB_API_URL"], os.environ["GITHUB_REPOSITORY"]
    query = urllib.parse.urlencode({"name": sys.argv[1], "per_page": 100})
    if not api.startswith("https://"):
        raise SystemExit(f"prior_pass.py: the API is not at an https URL: {api}")
    request = urllib.request.Request(f"{api}/repos/{repo}/actions/artifacts?{query}", headers={  # noqa: S310
        "Accept": "application/vnd.github+json", "Authorization": f"Bearer {os.environ['GH_TOKEN']}"})
    try:
        with urllib.request.urlopen(request, timeout=30) as response:  # noqa: S310 # https, checked above
            run = choose(json.load(response), int(os.environ["GITHUB_REPOSITORY_ID"]))
    except (OSError, ValueError) as error:
        print(f"prior_pass.py: no answer from the API, so the checks run: {error}", file=sys.stderr)
        run = None
    print(f"run-id={run or ''}")


if __name__ == "__main__":
    main()
