#!/usr/bin/env python3
# SPDX-License-Identifier: AGPL-3.0-or-later
"""Build the NNTP server (docs/runbook.md): the session's program as `dn-compiler` prints it,
compiled by the CakeML compiler `--cake` names and linked with its host, into `OUT/dragons-nntpd`.
"""
from __future__ import annotations

import argparse
import os
from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parent))
import lanes  # the path above is what makes it importable
from lanes import NATIVE, ROOT


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--cake", default=os.environ.get("CAKE"), help="the CakeML compiler (or CAKE)")
    parser.add_argument("--out", type=Path, default=ROOT / "build/server", help="where the server goes")
    args = parser.parse_args()
    cake = lanes.given_cake(parser, args.cake)
    out: Path = args.out
    out.mkdir(parents=True, exist_ok=True)
    (out / "dn_session_layout.h").write_text(lanes.emit("emit-session-layout"))
    built = lanes.whole_program(cake, "dragons-nntpd", lanes.emit("emit-session"), out, NATIVE / "nntp_host.c",
                                [NATIVE / "store.c", NATIVE / "jobs.c"])
    print(built)


if __name__ == "__main__":
    main()
