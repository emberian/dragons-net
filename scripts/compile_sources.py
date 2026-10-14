#!/usr/bin/env python3
# SPDX-License-Identifier: AGPL-3.0-or-later
"""Compile each C source of native/ on its own, as the nightly CodeQL job builds its database: with
the flags the native lane builds with, less those of linking, the system's headers and the layouts
`dn-compiler` prints. The nightly workflow runs only from the default branch; here a source that
needs anything else fails on every commit instead. native/entry/, the entry benchmark's hosts, is
its lane's.

With `--print-to DIR` it only prints the layouts there; with `--layouts DIR` it compiles with those
already printed, so the CodeQL job runs `dn-compiler` before its tracer starts."""
from __future__ import annotations

import argparse
from collections.abc import Mapping
from pathlib import Path
import re
import sys
import tempfile

sys.path.insert(0, str(Path(__file__).resolve().parent))
import lanes  # the path above is what makes it importable

COMPILE = [flag for flag in lanes.HARDENING if flag != "-pie" and not flag.startswith("-Wl,")]
# The headers the sources include that dn-compiler prints, with the command that prints each.
GENERATED = {"dn_layout.h": "emit-layout", "dn_recover_layout.h": "emit-recover-layout",
             "dn_scan_layout.h": "emit-scan-layout", "dn_session_layout.h": "emit-session-layout"}
INCLUDE = re.compile(r'^[ \t]*#[ \t]*include[ \t]*"([^"]+)"', re.MULTILINE)


def unaccounted(native: Path, generated: Mapping[str, str]) -> list[str]:
    """What is wrong with the headers the files of `native` include: one neither among those files
    nor printed, or one printed that no file includes."""
    named = {name for path in [*native.glob("*.c"), *native.glob("*.h")] for name in INCLUDE.findall(path.read_text())}
    return ([f"included, but neither in native/ nor printed: {name}"
             for name in sorted(named - generated.keys()) if not (native / name).is_file()] +
            [f"printed, but included by no source: {name}" for name in sorted(generated.keys() - named)])


def print_layouts(out: Path) -> None:
    out.mkdir(parents=True, exist_ok=True)
    for header, command in GENERATED.items():
        (out / header).write_text(lanes.emit(command))


def compile_each(layouts: Path, out: Path) -> int:
    sources = sorted(lanes.NATIVE.glob("*.c"))
    for source in sources:
        lanes.loud([lanes.cc(), *COMPILE, f"-I{lanes.NATIVE}", f"-I{layouts}", "-c", str(source),
                    "-o", str(out / f"{source.name}.o")], timeout=300, what=f"compiling {source.name}")
    return len(sources)


def check(args: argparse.Namespace) -> str:
    if wrong := unaccounted(lanes.NATIVE, GENERATED):
        raise lanes.LaneError("; ".join(wrong))
    if args.print_to:
        print_layouts(args.print_to)
        return f"{len(GENERATED)} layouts printed"
    with tempfile.TemporaryDirectory(prefix="dn-sources-") as temp:
        layouts = args.layouts or Path(temp)
        if not args.layouts:
            print_layouts(layouts)
        return f"{compile_each(layouts, Path(temp))} sources of native/, each on its own"


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    given = parser.add_mutually_exclusive_group()
    given.add_argument("--print-to", type=Path, help="only print the layouts into this directory")
    given.add_argument("--layouts", type=Path, help="compile with the layouts printed in this directory")
    try:
        said = check(parser.parse_args())
    except lanes.LaneError as error:
        raise SystemExit(f"DN SOURCES: {error}") from None
    print(f"DN SOURCES: PASS ({said})")


if __name__ == "__main__":
    main()
