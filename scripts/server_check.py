#!/usr/bin/env python3
# SPDX-License-Identifier: AGPL-3.0-or-later
"""The server loop (`DN.Server.Skeleton`) as the host runs it: a whole program, built without
`--main_return`, whose `main` fetches batches of events and hands back batches of actions through
two external calls.

`native/skeleton_check.c` plays the host. It requires every received payload back, in order, as a
send to the same connection, stops the run inside a call as a server host does, and checks on every
call that the heap header is intact, that each array is exactly its area of the layout and that the
program wrote nothing outside the layout. Four hostile batches — a count of events or a length just
below zero or just above its bound — have to end the run. Each of the checks, the program's and the
host's, is shown to work: a program wrong in one way, for each of them, has to be refused with that
check's own message. The layout comes from `dn-compiler emit-layout`, so the program and the host
cannot disagree about it.
"""
from __future__ import annotations

import argparse
import json
import os
from pathlib import Path
import subprocess
import sys

sys.path.insert(0, str(Path(__file__).resolve().parent))
import lanes  # the path above is what makes it importable
from lanes import NATIVE, ROOT, LaneError, Report

OUT = ROOT / "build/server"
HOST = NATIVE / "skeleton_check.c"
HOSTS = [HOST, NATIVE / "server.h", NATIVE / "cake_header.c", *lanes.RUNTIME]
HOSTILE = ("count-negative", "count-over", "length-negative", "length-over")
# Each check of the loop as the gate prints it.
CHECKS = {"count-negative": "    if k < 0 {\n      return 1;\n    } else {\n    }\n",
          "count-over": "    if 16 < k {\n      return 1;\n    } else {\n    }\n",
          "length-negative": "        if len < 0 {\n          return 2;\n        } else {\n        }\n",
          "length-over": "        if 512 < len {\n          return 2;\n        } else {\n        }\n"}
FETCH = "    @dn_next(@base + 64, 8, @base + 128, 8720);\n"
HAND = "    @dn_emit(@base + 64, 8, @base + 8848, 8976);\n"
END = HAND + "  }\n  return 0;\n}\n"
# A recursion far deeper than the stack the host provisions.
DEEP = ("fun dn_deep(1 n) {\n  if n == 0 {\n    return 0;\n  } else {\n  }\n"
        "  var r = dn_deep(n - 1);\n  return r + 1;\n}\n")
# Programs that are wrong in one way: (name, what to replace, with what, the host mode that shows it,
# what the host has to say). The first six stand against the hostile batches, one at each check
# taken out and two at a bound one too far; the rest each break one thing the host checks.
VARIANTS = [
    ("without the negative count check", CHECKS["count-negative"], "", "count-negative", "went on"),
    ("without the count bound", CHECKS["count-over"], "", "count-over", "went on"),
    ("with the count bound one too far", "if 16 < k {", "if 17 < k {", "count-over", "went on"),
    ("without the negative length check", CHECKS["length-negative"], "", "length-negative", "went on"),
    ("without the length bound", CHECKS["length-over"], "", "length-over", "outside its layout"),
    ("with the length bound one too far", "if 512 < len {", "if 513 < len {", "length-over", "outside its layout"),
    ("another layout version", "  st @base + 64, 1;", "  st @base + 64, 2;", "echo", "speaks layout 2"),
    ("another configuration array", FETCH, FETCH.replace("@base + 64, 8,", "@base + 72, 8,"), "echo",
     "configuration array is not the layout's"),
    ("another configuration length", FETCH, FETCH.replace("@base + 64, 8,", "@base + 64, 16,"), "echo",
     "configuration array is not the layout's"),
    ("another area", FETCH, FETCH.replace("@base + 128,", "@base + 136,"), "echo",
     "array is not the layout's area"),
    ("another area length", FETCH, FETCH.replace("8720);", "8712);"), "echo", "array is not the layout's area"),
    ("an end without a cause", "if k < 0 {", "if k < 1 {", "echo", "without a cause"),
    ("a write into the heap header at the end", CHECKS["count-negative"],
     CHECKS["count-negative"].replace("      return 1;", "      st @base + 8, 0;\n      return 1;"), "count-negative",
     "end of run: the heap header"),
    ("a write outside the layout at the end", CHECKS["count-negative"],
     CHECKS["count-negative"].replace("      return 1;", "      st @base + 20000, 7;\n      return 1;"),
     "count-negative", "end of run: the program wrote outside its layout"),
    ("an end for want of stack", END, END.replace(HAND, HAND + "    var x = dn_deep(1000000);\n") + "\n" + DEEP,
     "echo", "for want of stack or heap"),
    ("a write outside the layout", "    st @base + 8856, 0;\n", "    st @base + 8856, 0;\n    st @base + 20000, 7;\n",
     "echo", "wrote outside its layout"),
    ("a write into the heap header", "  st @base + 64, 1;", "  st @base + 64, 1;\n  st @base + 8, 0;", "echo",
     "heap header"),
    ("a deadline", "    st @base + 8856, 0;\n", "    st @base + 8856, 5;\n", "echo", "a deadline"),
    ("one action too many", "    st @base + 8848, m;", "    st @base + 8848, m + 1;", "echo", "actions for"),
    ("fetching twice", FETCH, FETCH + FETCH, "echo", "fetched again"),
    ("answering first", FETCH, HAND + FETCH, "echo", "answered without fetching"),
    ("another action", "        st ac, 1;", "        st ac, 3;", "echo", "is not a send"),
    ("another connection", "st ac + 8, lds 1 (ev + 8);", "st ac + 8, lds 1 (ev + 16);", "echo",
     "another connection"),
    ("another generation", "st ac + 16, lds 1 (ev + 16);", "st ac + 16, lds 1 (ev + 8);", "echo",
     "another generation"),
    ("another length", "st ac + 24, len;", "st ac + 24, len + 1;", "echo", "another length"),
    ("no more reading", "st ac + 32, 1;", "st ac + 32, 0;", "echo", "does not read on"),
    ("bytes claimed taken", "st ac + 40, 0;", "st ac + 40, 1;", "echo", "claims bytes"),
    ("no bytes copied", "st8 ac + 48 + j, ld8 (ev + 32 + j);", "st8 ac + 48 + j, 0;", "echo",
     "differs from its payload"),
]


def build(cake: str, name: str, source: str) -> Path:
    """Compile a variant of the loop without `--main_return`, make its bitmaps label global for the
    heap header (native/cake_header.c), and link it with the checking host."""
    pnk = OUT / f"{name}.pnk"
    pnk.write_text(source)
    asm = lanes.assemble(cake, pnk, main_return=False)
    text = asm.read_text()
    if text.count("\ncake_bitmaps:\n") != 1:
        raise LaneError(f"{asm.name}: the bitmaps label is not where the host expects it")
    asm.write_text(text.replace("\ncake_bitmaps:\n", "\n     .globl cake_bitmaps\ncake_bitmaps:\n"))
    return lanes.link(OUT / name, [HOST, NATIVE / "cake_header.c", NATIVE / "cake_runtime.c", asm],
                      includes=[OUT])


def run(binary: Path, mode: str) -> subprocess.CompletedProcess[str]:
    try:
        return subprocess.run([str(binary), mode], text=True, capture_output=True, check=False, timeout=60)
    except subprocess.TimeoutExpired as error:
        raise LaneError(f"{binary.name} {mode} ran past its time") from error


def report(done: subprocess.CompletedProcess[str], what: str) -> dict[str, object]:
    try:
        result: dict[str, object] = json.loads(done.stdout)
    except json.JSONDecodeError as error:
        raise LaneError(f"{what} printed no report:\n{done.stdout}{done.stderr}") from error
    return result


def check(cake: str) -> Report:
    OUT.mkdir(parents=True, exist_ok=True)
    (OUT / "dn_layout.h").write_text(lanes.emit("emit-layout"))
    source = lanes.emit("emit-skeleton")
    binary = build(cake, "skeleton", source)
    echo = run(binary, "echo")
    if echo.returncode:
        raise LaneError(f"the echo run failed with status {echo.returncode}:\n{echo.stdout}{echo.stderr}")
    measured = report(echo, "the echo run")
    if measured["batches"] != 4 or measured["echoed"] != 1 + 2 + 16:
        raise LaneError(f"the echo run did not go through the whole script: {measured}")
    unwritten = run(binary, "no-header")
    if unwritten.returncode != 1 or "heap header" not in unwritten.stderr:
        raise LaneError(f"a run without the heap header was not refused:\n{unwritten.stdout}{unwritten.stderr}")
    for mode in HOSTILE:
        done = run(binary, mode)
        if done.returncode or report(done, f"the {mode} run").get("ended") is not True:
            raise LaneError(f"the loop did not end its run on a {mode} batch:\n{done.stdout}{done.stderr}")
    refused = {}
    for index, (name, right, wrong, mode, said) in enumerate(VARIANTS):
        if source.count(right) != 1:
            raise LaneError(f"the printed loop does not hold {right!r} once, for the variant {name}")
        done = run(build(cake, f"variant-{index}", source.replace(right, wrong)), mode)
        if done.returncode != 1 or said not in done.stderr:
            raise LaneError(f"the loop {name} was not refused for it:\n{done.stdout}{done.stderr}")
        refused[name] = done.stderr.strip()
    return Report("checked", cake, HOSTS, {
        "source_sha256": lanes.digest(OUT / "skeleton.pnk"), "layout_sha256": lanes.digest(OUT / "dn_layout.h"),
        "executable_sha256": lanes.digest(binary), "batches": measured["batches"], "echoed": measured["echoed"],
        "hostile_batches_ended": list(HOSTILE), "refused_variants": refused,
        "stack_depth_bytes": measured["stack_depth"], "startup_store_bytes": measured["store_bytes"],
        "stack_provisioned_bytes": 1024 * 1024})


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--cake", default=os.environ.get("CAKE"))
    args = parser.parse_args()
    lanes.require_platform(parser)
    cake = lanes.given_cake(parser, args.cake)
    lanes.lane_main("SERVER", OUT, lambda: check(cake))


if __name__ == "__main__":
    main()
