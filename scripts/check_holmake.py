#!/usr/bin/env python3
# SPDX-License-Identifier: AGPL-3.0-or-later
"""Decide whether a finished Holmake run rebuilt the proof, and rebuilt it honestly.

Holmake does not fail on a theorem proved by `cheat` or carrying an oracle tag,
and it does not fail when it takes a theory from its cache: it records what
happened and exits 0. What it records, and where, depends on the job count.

With one job the build output goes to standard output (`graphbuildj1` in
`tools/Holmake/poly/BuildCommand.sml`). With more, each job's output goes to a
file under `.hol/logs` (`LOGDIR` in `tools/Holmake/unix-systeml.sml`) and
standard output carries one status word per finished job; an oracle tag changes
nothing there but the colour (`monitor` in `tools/Holmake/poly/MB_Monitor.sml`).
A lane that reads only the standard output of a parallel build therefore reads
nothing at all, which is why this reads both.

It also refuses a parallel run that left no job logs, and a target that is not
newer than the run: a scan with nothing to scan, or a target Holmake decided was
already up to date, proves as little as a scan that was never written.
"""
from __future__ import annotations

import argparse
from pathlib import Path
import re

# What Holmake's monitor looks for in a job's output, spelled as in
# `MB_Monitor.sml` (`cheat_string`, `fastcheat_string`, `oracle_string`,
# `used_cheat_string`, `cachehit_string`). A single-job build prints these.
RECORDED = ("Saved CHEAT", "Saved FAST-CHEAT", "Saved ORACLE thm", "(used CHEAT)", "Cache hit!")

# What it prints instead for a finished job of a parallel build, from the same
# function. `OK` covers both a clean job and one whose theorems carry an oracle
# tag, so the word alone never clears a run: the job logs do.
STATUS = ("CHEATED", "F-CHEAT", "CACHED")


def hits(text: str, log: str) -> list[str]:
    return [f"{log} reports {pattern!r}" for pattern in RECORDED if pattern in text]


def read(path: Path) -> str:
    return path.read_text(errors="replace")


def located(built: Path) -> Path | None:
    """Where Holmake left the target. It writes objects to `.hol/objs` beside the sources it
    built, and older layouts write them into the source directory itself."""
    return next((path for path in (built.parent / ".hol/objs" / built.name, built)
                 if path.exists()), None)


def problems(output: Path, tree: Path, jobs: int, built: Path | None, since: float) -> list[str]:
    found = hits(read(output), output.name)
    words = [word for word in STATUS if re.search(rf"(?<![A-Z-]){word}(?![A-Z-])", read(output))]
    found += [f"a job of this run finished as {word}" for word in words]
    logs = sorted(path for path in tree.glob("**/.hol/logs/*") if path.is_file())
    if jobs > 1 and not logs:
        found.append("the parallel build left no job logs, so this check read no build output")
    for log in logs:
        found += hits(read(log), str(log.relative_to(tree)))
    if built is not None:
        target = located(built)
        if target is None:
            found.append(f"{built.name} is neither in {built.parent}/.hol/objs nor in "
                         f"{built.parent}, so it was not built")
        elif target.stat().st_mtime < since:
            found.append(f"{target} is older than this run; nothing was rebuilt")
    return found


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True, help="the captured standard output")
    parser.add_argument("--tree", type=Path, required=True, help="the source tree that was built")
    parser.add_argument("--jobs", type=int, required=True, help="the job count Holmake was given")
    parser.add_argument("--built", type=Path, help="the target that must exist and be newer")
    parser.add_argument("--since", type=float, default=0.0, help="when the run started, in seconds")
    args = parser.parse_args()
    found = problems(args.output, args.tree, args.jobs, args.built, args.since)
    for problem in found:
        print(f"DN BACKEND: {problem}")
    if found:
        print("DN BACKEND: the build establishes nothing; see the messages above")
        return 1
    print(f"DN BACKEND: no cheat, oracle tag or cache hit in the output or in the job logs of {args.tree}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
