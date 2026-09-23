#!/usr/bin/env python3
# SPDX-License-Identifier: AGPL-3.0-or-later
"""Judge a finished `checks` run from outside the change it ran on.

For a pull request GitHub takes the workflow file, and everything it starts, from
the pull request's own merge commit: `scripts/check.sh`, the proof audit and the
gate tests are all supplied by the change they are meant to certify. A green run
therefore says "these checks passed", not "the project's checks passed".

Running the default branch's checks over the change instead does not settle it.
The expected regression count, the module list of the audit and the pinned
syntax files change together with the code they describe, so the default
branch's checks report an honest structural change as a failure, and a lane that
is red on honest changes is a lane nobody reads.

What can be decided from outside, and is decided here, is narrower and true: did
every required job of that run finish successfully, and are the files in that
commit that decide what the checks do identical to the ones on the default
branch? Everything is critical by default -- a new script, a new workflow, a
moved pin -- and only the directories the checks read as their subject are
exempt. The input is the run's job list and the two commit trees as the API
returns them; nothing from the change is executed, and no claim rests on a file
the change could write.

Three limits are part of the answer, not defects in it. The comparison is of
committed files: a test in the subject directories runs before other scripts of
the same job and could rewrite them on disk, which is why `scripts/check.sh`
refuses a tree that changed while the tests ran. A branch behind the default
branch is reported as different even when the merge commit that ran already had
the current checks; updating the branch clears it. And a change that renames the
`checks` workflow, or narrows its triggers, gets no report at all rather than a
red one, because the run this reads would not exist: a missing report is not a
passing one, and only a branch rule that requires this check can say so.
"""
from __future__ import annotations

import argparse
from dataclasses import dataclass
import json
from pathlib import Path
import re
import sys
from typing import Any

# The jobs of `.github/workflows/ci.yml`. A run that is missing one, or that let
# one fail, checked less than the name `checks` claims.
REQUIRED_JOBS = ("lint", "build", "proofs", "test")

# What the checks read as their subject: the code under review and the tests that
# ship with it, which a reviewer reads together with the code. Everything else is
# critical by default -- the scripts, workflows and gate tests that decide which
# checks run and how, the toolchain and dependency pins, the backend source pin.
SUBJECT_DIRECTORIES = ("lean/", "crates/", "models/", "native/", "migration/", "rfcs/", "docs/")
SUBJECT_FILES = ("README.md", "AGENTS.md", "CONTRIBUTING.md", "LICENSE", "NOTICE")

# The exceptions inside those directories: a manifest pins dependencies and names
# the workspace members that are built at all, and `models/expected-tests.txt` is
# the list `scripts/check_models.py` requires the discovered tests to match.
CRITICAL_NAMES = ("Cargo.toml", "Cargo.lock")
CRITICAL_FILES = ("models/expected-tests.txt",)

# Paths and job names come from the commit under review. They reach a markdown
# summary, where a newline, a backtick or a cell separator could forge a line, so
# they are quoted and truncated, and the summary as a whole stays well under the
# 65536 characters the Checks API accepts.
PATH_LIMIT = 120
LISTED = 40


@dataclass(frozen=True)
class Run:
    """What GitHub says about the finished run, none of it written by the change."""

    url: str
    conclusion: str
    default_branch: str
    base_refs: tuple[str, ...] = ()


@dataclass(frozen=True)
class Verdict:
    conclusion: str
    title: str
    summary: str


def quote(text: str) -> str:
    kept = "".join(c for c in text if c.isprintable() and c not in "`|")
    return f"`{kept[:PATH_LIMIT]}`"


def job_problems(jobs: list[dict[str, Any]]) -> list[str]:
    """Required jobs that did not run, did not succeed, or ran more than once.

    Two jobs of one name would let the second answer for the first, so a name
    that is not there exactly once is itself the problem.
    """
    problems = []
    for name in REQUIRED_JOBS:
        matching = [job for job in jobs if str(job.get("name")) == name]
        if not matching:
            problems.append(f"{quote(name)}: did not run")
        elif len(matching) > 1:
            problems.append(f"{quote(name)}: ran {len(matching)} times")
        elif matching[0].get("conclusion") != "success":
            state = matching[0].get("conclusion") or matching[0].get("status")
            problems.append(f"{quote(name)}: {quote(str(state))}")
    return problems


def is_subject(path: str) -> bool:
    if path in CRITICAL_FILES or path.rsplit("/", 1)[-1] in CRITICAL_NAMES:
        return False
    return path.startswith(SUBJECT_DIRECTORIES) or path in SUBJECT_FILES


def contents(tree: dict[str, Any]) -> dict[str, str]:
    """Path to kind, mode and content hash, for everything that carries content.

    Directories carry only what is under them, which is compared on its own.
    Files and submodule links do carry content, and so does the mode: a script
    that stops being executable is a change too.
    """
    return {str(e["path"]): f'{e.get("type")} {e.get("mode", "")} {e["sha"]}'
            for e in tree.get("tree", []) if e.get("type") != "tree"}


def differences(base: dict[str, str], head: dict[str, str]) -> list[str]:
    paths = set(base) | set(head)
    return sorted(p for p in paths if not is_subject(p) and base.get(p) != head.get(p))


def table(jobs: list[dict[str, Any]]) -> str:
    rows = "\n".join(
        f"| {quote(str(job.get('name')))} | {quote(str(job.get('conclusion') or job.get('status')))} |"
        for job in jobs[:LISTED]
    )
    if len(jobs) > LISTED:
        rows += f"\n| and {len(jobs) - LISTED} more | |"
    return f"| job | result |\n| --- | --- |\n{rows}\n"


def listing(items: list[str]) -> str:
    """Bullets, already quoted by the caller, with a bound on how many are shown."""
    shown = "\n".join(f"- {item}" for item in items[:LISTED])
    if len(items) > LISTED:
        shown += f"\n- and {len(items) - LISTED} more"
    return shown


def judge(jobs: list[dict[str, Any]], base: dict[str, Any], head: dict[str, Any],
          run: Run) -> Verdict:
    ran = f"\nThe run: {run.url}\n"
    if run.conclusion != "success":
        return Verdict("neutral", "The checks did not succeed",
                       f"The `checks` run ended as {quote(run.conclusion)}, so there is nothing "
                       "here to certify; its own jobs say what failed." + ran)
    if base.get("truncated") or head.get("truncated"):
        return Verdict("neutral", "The commit could not be compared",
                       "The tree listing was truncated, so the files that decide what the "
                       "checks do were not all compared." + ran)
    elsewhere = sorted({ref for ref in run.base_refs if ref != run.default_branch})
    if elsewhere:
        return Verdict("neutral", "The change is not based on the default branch",
                       "The run checked this commit merged into "
                       + ", ".join(quote(ref) for ref in elsewhere)
                       + f", and the checks there are whatever that branch carries. This "
                       f"compares against {quote(run.default_branch)} only." + ran)
    problems = job_problems(jobs)
    changed = differences(contents(base), contents(head))
    edited = "" if not changed else (
        "\nThese files decide what the checks do, and this commit does not have the default "
        "branch's version of them:\n\n" + listing([quote(path) for path in changed]) + "\n")
    tail = f"\n{table(jobs)}{ran}"
    if problems:
        return Verdict("failure", "The run checked less than it claims",
                       "The `checks` run concluded successfully, but:\n\n"
                       + listing(problems) + "\n" + edited + tail)
    if changed:
        return Verdict("neutral", "This change edits its own checks",
                       "Every required job succeeded. A green `checks` run is then the change "
                       "certifying itself, and the difference has to be read by hand.\n"
                       + edited + tail)
    return Verdict("success", "Checked by the default branch's checks",
                   "Every required job succeeded, and the scripts, workflows, gate tests and "
                   "pins in this commit are the default branch's.\n" + tail)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--jobs", type=Path, required=True, help="the run's jobs, as the API returns them")
    parser.add_argument("--base-tree", type=Path, required=True, help="recursive tree of the default branch")
    parser.add_argument("--head-tree", type=Path, required=True, help="recursive tree of the checked commit")
    parser.add_argument("--head-sha", required=True, help="the commit the check run is published on")
    parser.add_argument("--conclusion", required=True, help="how the checked run ended")
    parser.add_argument("--default-branch", required=True, help="the branch this compares against")
    parser.add_argument("--base-refs", default="", help="the branches the run's pull requests target")
    parser.add_argument("--run-url", required=True, help="the finished run, for the summary")
    parser.add_argument("--details-url", help="this run, which the check run links to")
    parser.add_argument("--summary", type=Path, help="append the summary here as well")
    args = parser.parse_args()
    if not re.fullmatch("[0-9a-f]{40}", args.head_sha):
        raise SystemExit(f"--head-sha is not a commit: {args.head_sha!r}")

    run = Run(url=args.run_url, conclusion=args.conclusion, default_branch=args.default_branch,
              base_refs=tuple(args.base_refs.split()))
    jobs = json.loads(args.jobs.read_text()).get("jobs", [])
    verdict = judge(jobs, json.loads(args.base_tree.read_text()),
                    json.loads(args.head_tree.read_text()), run)
    if args.summary is not None:
        with args.summary.open("a") as out:
            out.write(f"## verify: {verdict.title}\n\n{verdict.summary}\n")
    body: dict[str, Any] = {"name": "verify", "head_sha": args.head_sha, "status": "completed",
                            "conclusion": verdict.conclusion,
                            "output": {"title": verdict.title, "summary": verdict.summary}}
    if args.details_url is not None:
        body["details_url"] = args.details_url
    json.dump(body, sys.stdout)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
