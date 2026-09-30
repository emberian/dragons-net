#!/usr/bin/env python3
# SPDX-License-Identifier: AGPL-3.0-or-later
"""The independent reference of the grammar lane: the `abnf` library, with its own reading of
ABNF, loads the grammar text scripts/gen_abnf.py writes and answers the cases `dn-compiler
abnf-model` answers, in the same form — a line naming a rule and giving bytes in hex, `-` for
none, answered `1` if the rule matches all of them and `0` if not. Run by the Python of
scripts/requirements-tests.txt, which pins the library.

The library reads recursively and stops at a depth of nesting, reporting it as a failure to
match caused by a RecursionError; its Rust backend stops near 180 rules deep, whatever the
thread's stack, as its documentation of `parse_all` says. Such a case is decided again by its
pure-Python backend, in a process of its own (the Rust backend, once loaded, stands in for it) on
a thread with a stack and a recursion limit large enough for any case the lane gives; one that
still goes too deep fails the run.

With `--library`, the rules are instead the library's own transcription of RFC 5322 or RFC 3986,
which the lane holds the grammar to.
"""
from __future__ import annotations

import argparse
import os
from pathlib import Path
import subprocess
import sys
import threading

from abnf import ParseError, Rule
from abnf.grammars import rfc3986, rfc5322

STACK = 1 << 30
RECURSION = 10_000_000
LIBRARY: dict[str, type[Rule]] = {"rfc5322": rfc5322.Rule, "rfc3986": rfc3986.Rule}


class Netnews(Rule):
    """The rules of scripts/netnews.abnf."""


class TooDeep(Exception):
    pass


def answer(rules: type[Rule], rule: str, data: bytes) -> str:
    try:
        rules(rule).parse_all(data.decode("latin-1"))
    except ParseError as e:
        if isinstance(e.__cause__, RecursionError):
            raise TooDeep from e
        return "0"
    return "1"


def deep(lines: list[str], argv: list[str]) -> list[str]:
    """The answers of the pure-Python backend to `lines`, from a process of its own."""
    done = subprocess.run([sys.executable, __file__, *argv, "--deep"], input="".join(lines),
                          capture_output=True, text=True, check=False,
                          env={**os.environ, "ABNF_NO_RUST": "1"})
    said = done.stdout.split()
    if done.returncode or len(said) != len(lines):
        sys.exit(f"the pure-Python backend failed: {done.stderr[-500:]}")
    return said


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    parser.add_argument("--grammar", type=Path, default=Path(__file__).with_name("netnews.abnf"),
                        help="another grammar text, as the lane's planted defects give it")
    parser.add_argument("--library", choices=sorted(LIBRARY),
                        help="the library's own rules of an RFC in place of the grammar text")
    parser.add_argument("--deep", action="store_true",
                        help="the pure-Python backend on a large stack, for cases nested too deep")
    args = parser.parse_args()
    rules: type[Rule] = Netnews
    if args.library:
        rules = LIBRARY[args.library]
    else:
        Netnews.load_grammar(args.grammar.read_text(encoding="ascii"))
    lines = sys.stdin.readlines()
    answers: list[str | None] = []
    if args.deep:
        sys.setrecursionlimit(RECURSION)
    for line in lines:
        rule, hexed = line.split()
        try:
            answers.append(answer(rules, rule, b"" if hexed == "-" else bytes.fromhex(hexed)))
        except TooDeep:
            if args.deep:
                sys.exit(f"{rule} {hexed[:120]} is nested too deep even for the pure-Python backend")
            answers.append(None)
    retried = [k for k, a in enumerate(answers) if a is None]
    if retried:
        argv = ["--grammar", str(args.grammar)] + (["--library", args.library] if args.library else [])
        for k, said in zip(retried, deep([lines[k] for k in retried], argv), strict=True):
            answers[k] = said
    sys.stdout.write("".join(f"{a}\n" for a in answers))


def run_deep() -> None:
    """`main`, on a thread whose stack is large enough for the recursion limit it sets."""
    threading.stack_size(STACK)
    failed: list[BaseException] = []

    def body() -> None:
        try:
            main()
        except BaseException as e:  # noqa: BLE001 -- re-raised on the main thread
            failed.append(e)

    worker = threading.Thread(target=body)
    worker.start()
    worker.join()
    if failed:
        raise failed[0]


if __name__ == "__main__":
    if "--deep" in sys.argv:
        run_deep()
    else:
        main()
