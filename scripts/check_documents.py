#!/usr/bin/env python3
# SPDX-License-Identifier: AGPL-3.0-or-later
"""Hold the documents to what the checks measured: each requirement a check recorded with its stamp
(`scripts/once.py`, `lanes.require`) has to hold of the documents as they are now, and every check
that makes requirements (`CHECKS`) has to have a stamp. A change to the documents alone is checked
here, in a moment, instead of by running the checks again."""
from __future__ import annotations

import json
import os
from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parent))
import lanes

ROOT = Path(__file__).resolve().parent.parent
# The stamp of each script that holds the documents to what it measured, as check.sh and
# native_lanes.sh name it.
CHECKS = {"abnf_check.py": "abnf", "article_check.py": "article", "journal_check.py": "journal",
          "fs_check.py": "fs", "store_check.py": "store", "runs_check.py": "runs",
          "session_check.py": "session-model", "framing_check.py": "lane-framing",
          "grammar_check.py": "lane-grammar", "accept_check.py": "lane-accept",
          "native_baseline.py": "lane-baseline", "native_fuzz.py": "lane-fuzz", "nntp_check.py": "lane-nntp",
          "crash_check.py": "lane-crash", "faults_check.py": "lane-faults",
          "parser_contract.py": "lane-parser", "session_native.py": "lane-session"}
# Checks run again on any change of the tree, scripts/native_lanes.sh's FUSE lanes, which hold the
# documents as they run.
AS_THEY_RUN = {"power_check.py"}


def main() -> int:
    stamps = Path(os.environ.get("DN_STAMPS", ROOT / "build/stamps"))
    wrong, held = [], 0
    wrong += [f"no stamp of {name}, whose requirements are unheld" for name in sorted(CHECKS.values())
              if not (stamps / f"{name}.json").is_file()]
    for stamp in sorted(stamps.glob("*.json")):
        if stamp.name == "hashes.json":
            continue
        for requirement in json.loads(stamp.read_text()).get("documented", []):
            held += 1
            wrong += [f"{stamp.stem}: {w}" for w in lanes.unheld(requirement)]
    for w in wrong:
        print(w, file=sys.stderr)
    if wrong:
        return 1
    print(f"DN DOCUMENTS: PASS ({held} requirements of the checks' last passes)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
