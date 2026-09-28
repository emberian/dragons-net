#!/usr/bin/env python3
# SPDX-License-Identifier: AGPL-3.0-or-later
"""Compile emitted Pancake and run the real exported kernel on Linux x86-64.

CAKE must name an existing compiler executable. Its digest is recorded, not
silently treated as the verified build of backend/lock.json.
"""
from __future__ import annotations

import argparse
import json
import os
from pathlib import Path
import platform
import subprocess
import sys

sys.path.insert(0, str(Path(__file__).resolve().parent))
import lanes  # the path above is what makes it importable
from lanes import NATIVE, ROOT, LaneError, Report

OUT = ROOT / "build/native"
DRIVER = NATIVE / "region_driver.c"


def run(cake: str, supplied: Path | None) -> Report:
    source = OUT / "region.pnk"
    source.write_bytes(supplied.read_bytes() if supplied else lanes.emit("emit-region").encode())
    assembly = lanes.assemble(cake, source)
    executable = lanes.link(OUT / "region-check", [DRIVER, NATIVE / "cake_runtime.c", assembly])
    result = subprocess.run([str(executable)], text=True, capture_output=True, check=False,
                            timeout=60)
    if result.returncode:
        raise LaneError(f"the region check failed with status {result.returncode}:\n"
                        f"{result.stdout}{result.stderr}")
    measured = json.loads(result.stdout)
    if measured["vectors"] != 99240 or measured["checksum"] == 0 or measured["elapsed_ns"] <= 0:
        raise LaneError("native region coverage or execution evidence is incomplete")
    measured["MiB_per_second"] = measured["bytes"] * 1e9 / measured["elapsed_ns"] / 1048576
    return Report("native-tested", cake, [DRIVER, *lanes.RUNTIME], {
        "assurance": "not an end-to-end compiler proof", "cpu": platform.processor(),
        "source_sha256": lanes.digest(source), "assembly_sha256": lanes.digest(assembly),
        "executable_sha256": lanes.digest(executable), "measurements": measured},
        printed_by_dn_compiler=supplied is None)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--cake", default=os.environ.get("CAKE"))
    parser.add_argument("--source", type=Path, help="Previously emitted .pnk; defaults to running dn-compiler")
    args = parser.parse_args()
    lanes.require_platform(parser)
    cake = lanes.given_cake(parser, args.cake)
    lanes.lane_main("NATIVE", OUT, lambda: run(cake, args.source))


if __name__ == "__main__":
    main()
