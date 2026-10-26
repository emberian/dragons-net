#!/usr/bin/env python3
# SPDX-License-Identifier: AGPL-3.0-or-later
"""Find a pass that an earlier CI run recorded: `prior_pass.py NAME` prints `run-id=ID` and `found=ID`
for the newest run that uploaded an unexpired artifact NAME, or `run-id=` and `found=` when there is
none. `--noted TREE`, the tree a writer checked before the push (the job `checked` of ci.yml), is a
pass too: it prints `run-id=` and `found=noted` without asking. A job records
a pass as an artifact named by its inputs (scripts/once.py), and artifacts, unlike the Actions
cache, are seen across branches: the run on main after a merge finds what the pull request's run
passed on the same tree. Only runs of this repository's own branches count; a pull request from a
fork runs a workflow of its own, which could record anything. A run of this repository's branches
is trusted as its writers are, who choose its workflow. But any code a job runs can upload an
artifact of any name, the change's tests among it, so a run counts only where GitHub says the step
`Record NAME` of one of its jobs passed, and the run asking never does. `--branch B`, given
for the stamps of the checks, counts only runs of the branches named: those stamps are made by the
code the checks run, so one branch's are never taken up by another, but from the default branch.
When the API does not answer, the checks run."""
from __future__ import annotations

import argparse
import json
import os
import sys
from typing import Any
import urllib.parse
import urllib.request

# The newest runs holding the artifact whose steps are asked about, before the checks run instead.
ASKED = 5


def candidates(listing: dict[str, Any], repository: int, asking: int, branches: list[str] | None = None) -> list[int]:
    """The runs of this repository's branches, or of `branches`, that hold the artifact unexpired,
    newest first, but the run asking."""
    runs = [a.get("workflow_run") or {} for a in listing.get("artifacts", []) if not a.get("expired")]
    found = {r["id"] for r in runs if r.get("repository_id") == repository == r.get("head_repository_id")
             and isinstance(r.get("id"), int) and r["id"] != asking
             and (branches is None or r.get("head_branch") in branches)}
    return sorted(found, reverse=True)


def recorded(jobs: dict[str, Any], name: str) -> bool:
    """Whether a job of the run passed the step that records `name`."""
    return any(step.get("name") == f"Record {name}" and step.get("conclusion") == "success"
               for job in jobs.get("jobs", []) for step in job.get("steps") or [])


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("name")
    parser.add_argument("--branch", action="append", dest="branches")
    parser.add_argument("--noted", default="")
    args = parser.parse_args()
    if args.noted:
        print("run-id=\nfound=noted")
        return
    name = args.name
    api, repo = os.environ["GITHUB_API_URL"], os.environ["GITHUB_REPOSITORY"]
    if not api.startswith("https://"):
        raise SystemExit(f"prior_pass.py: the API is not at an https URL: {api}")

    def get(path: str, query: dict[str, str | int]) -> Any:
        url = f"{api}/repos/{repo}/{path}?{urllib.parse.urlencode(query)}"
        request = urllib.request.Request(url, headers={  # noqa: S310
            "Accept": "application/vnd.github+json", "Authorization": f"Bearer {os.environ['GH_TOKEN']}"})
        with urllib.request.urlopen(request, timeout=30) as response:  # noqa: S310 # https, checked above
            return json.load(response)

    run = None
    try:
        listing = get("actions/artifacts", {"name": name, "per_page": 100})
        held = candidates(listing, int(os.environ["GITHUB_REPOSITORY_ID"]), int(os.environ["GITHUB_RUN_ID"]),
                          args.branches)
        for each in held[:ASKED]:
            if recorded(get(f"actions/runs/{each}/jobs", {"filter": "all", "per_page": 100}), name):
                run = each
                break
    except (OSError, ValueError) as error:
        print(f"prior_pass.py: no answer from the API, so the checks run: {error}", file=sys.stderr)
        run = None
    print(f"run-id={run or ''}\nfound={run or ''}")


if __name__ == "__main__":
    main()
