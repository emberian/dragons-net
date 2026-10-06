#!/usr/bin/env python3
# SPDX-License-Identifier: AGPL-3.0-or-later
"""Differential compiler baseline and a real generated-code TCP echo smoke test."""
from __future__ import annotations

import argparse
import json
import os
from pathlib import Path
import re
import signal
import subprocess
import sys
from typing import Any

sys.path.insert(0, str(Path(__file__).resolve().parent))
# The path above is what makes these importable.
import lanes
from lanes import NATIVE, ROOT, LaneError, Report
from words import MASK, signed, word_op

OUT = ROOT / "build/baseline"
FIXTURES = [("baseline.json", "emit-baseline"), ("echo.pnk", "emit-echo"), ("render.pnk", "emit-render"),
            ("reply.pnk", "emit-reply"), ("reply-cases.json", "emit-reply-cases")]
HOSTS = [NATIVE / "echo_check.c", NATIVE / "render_check.c", NATIVE / "reply_check.c",
         NATIVE / "echo_server.c", NATIVE / "accept_policy.h", *lanes.RUNTIME]


def reference(expr: Any, a: int, b: int) -> int:
    if isinstance(expr, int):
        return expr & MASK
    if isinstance(expr, str):
        return {"a": a, "b": b}[expr]
    op, lhs, rhs = expr
    value = word_op(op, reference(lhs, a, b), reference(rhs, a, b))
    if value is None:
        raise ValueError("the model gives a shift of a whole word or more no value")
    return value


def control(a: int, b: int) -> int:
    acc = b
    for i in range(min(a & 31, 7)):
        acc = (acc + i if signed(acc) < 0 else acc * 3 + 1) & MASK
    return acc


def control2(a: int, b: int) -> int:
    """Returns from an else branch, at the top level and inside a loop."""
    acc = b
    if a & 1:
        return acc
    acc = (acc + 1) & MASK
    i = 0
    while signed(i) < signed(a & 7):
        if signed(i) < 3:
            acc = (acc + 1) & MASK
        else:
            return (acc * 2) & MASK
        i += 1
    return acc


# What `dn_reply` answers, written from its description rather than from the Lean program.
BINARY_KEYWORD = bytes([0xC8, 0x80, 0xFF, 0x00])
REPLY_KEYWORDS = (b"QUIT", b"MODE READER", BINARY_KEYWORD, b"HELP")


def reply(data: bytes) -> bytes:
    if data.startswith(b"QUIT"):
        return b"205 closing connection\r\n"
    if data.startswith(b"MODE READER"):
        return b"201 reader mode, posting prohibited\r\n"
    if data.startswith(BINARY_KEYWORD):
        return b"501 not text\r\n"
    if data.startswith(b"HELP"):
        return b"100 help text follows\r\n.\r\n"
    return b"500 unknown command\r\n"


def reply_cases(fixture: dict[str, Any]) -> list[tuple[bytes, bytes]]:
    """The Lean program's replies, checked against `reply`, and the inputs checked for the
    boundary cases a generator can lose without anyone noticing."""
    if fixture["function"] != "dn_reply":
        raise LaneError(f"unexpected reply function {fixture['function']}")
    cases = [(bytes(case["input"]), bytes(case["output"])) for case in fixture["cases"]]
    for data, answer in cases:
        if reply(data) != answer:
            raise LaneError(f"Lean/Python disagreement on the reply to {data!r}")
    if fixture["max_len"] != max(len(reply(keyword)) for keyword in (*REPLY_KEYWORDS, b"")):
        raise LaneError("the reply buffer the program asks for is not its longest reply")
    inputs = {data for data, _ in cases}
    wanted = ({keyword[:i] for keyword in REPLY_KEYWORDS for i in range(len(keyword) + 1)} |
              {keyword + b"\r\n" for keyword in REPLY_KEYWORDS} | {bytes([b]) for b in range(256)})
    # A kernel that skips one byte of a keyword shows only on an input that differs from the
    # keyword in that byte alone and is answered differently.
    changed = all(any(len(data) >= len(keyword) and reply(data) != reply(keyword) and
                      [j for j in range(len(keyword)) if data[j] != keyword[j]] == [i]
                      for data in inputs)
                  for keyword in REPLY_KEYWORDS for i in range(len(keyword)))
    if (not wanted <= inputs or not changed or
            len({answer for _, answer in cases}) != len(REPLY_KEYWORDS) + 1):
        raise LaneError("the reply inputs no longer reach every keyword boundary and reply")
    return cases


def compiler_revision(cake: str) -> str:
    """The revision the compiler reports for itself, not the one a lock file claims."""
    printed = subprocess.run([cake, "--version"], capture_output=True, text=True, timeout=60,
                             check=True).stdout
    found = re.search(r"CakeML:\s*([0-9a-f]{40})", printed)
    if not found:
        raise LaneError(f"the compiler does not report a revision:\n{printed}")
    return found.group(1)


def lexer_keywords(cake: str, out: Path, table: list[dict[str, Any]]) -> int:
    """The compiler itself decides what a keyword is; the table has to agree with it.

    Words the table calls keywords of the running compiler's revision must be refused as
    names, and words it records only for another pinned revision must be accepted.
    """
    revision = compiler_revision(cake)
    listed = {entry["revision"]: entry["keywords"] for entry in table}
    if revision not in listed:
        raise LaneError(f"the fixture carries no keyword list for {revision[:7]}")
    here = listed[revision]
    # With one pinned revision, or two that agree, a word no lexer reserves keeps the check
    # two-sided: the compiler has to accept it.
    elsewhere = sorted({word for words in listed.values() for word in words} - set(here)) or ["base"]
    if not here:
        raise LaneError("the keyword table has no words for the running compiler")
    source = out / "keyword.pnk"
    for word, is_keyword in [(w, True) for w in here] + [(w, False) for w in elsewhere]:
        source.write_text(f"export fun dn_word(1 a) {{ var {word} = a; return {word}; }}\n")
        with source.open("rb") as inp:
            probe = subprocess.run([cake, "--pancake", "--main_return=true"], stdin=inp,
                                   capture_output=True, timeout=60, check=False)
        if is_keyword and probe.returncode == 0:
            raise LaneError(f"the compiler accepts {word} as a name; the table calls it a keyword")
        if not is_keyword and probe.returncode != 0:
            raise LaneError(f"the compiler refuses {word} as a name; the table does not list it")
    return len(here) + len(elsewhere)


def documented(measured: dict[str, Any]) -> None:
    """The counts the documents quote must be the ones this run measured."""
    quoted = {"differential_cases": ("README.md", "docs/assurance.md", "docs/baseline.md"),
              "copy_cases": ("README.md", "docs/baseline.md"),
              "render_cases": ("docs/baseline.md",),
              "reply_cases": ("README.md", "docs/assurance.md", "docs/baseline.md",
                              "docs/decisions/0001-embedding.md"),
              "reply_inputs": ("docs/baseline.md",)}
    for key, files in quoted.items():
        try:
            lanes.require_quoted({name: (f"{measured[key]:,}",) for name in files})
        except LaneError as error:
            raise LaneError(f"{error}, the {key.replace('_', ' ')} this run measured") from None
    lanes.require_quoted({"docs/baseline.md": (f"all {measured['fixture_functions']} fixture functions",)})


def build(cake: str, name: str, host: Path, binary: str | None = None) -> Path:
    """Compile `name`.pnk and link it with `host`."""
    assembly = lanes.assemble(cake, OUT / f"{name}.pnk", timeout=180)
    return lanes.link(OUT / (binary or f"{name}-check"), [host, NATIVE / "cake_runtime.c", assembly],
                      timeout=60)


def run(binary: Path, *args: str, stdin: str | None = None) -> subprocess.CompletedProcess[str]:
    return subprocess.run([str(binary), *args], input=stdin, text=True, capture_output=True, timeout=120,
                          check=False)


def measured_by(binary: Path, *args: str, stdin: str | None = None) -> dict[str, Any]:
    done = run(binary, *args, stdin=stdin)
    if done.returncode:
        raise LaneError(f"{binary.name} failed with status {done.returncode}:\n{done.stdout}{done.stderr}")
    result: dict[str, Any] = json.loads(done.stdout)
    return result


def refuses(cake: str, name: str, source: str, host: Path, status: int, message: str | None,
            *args: str, stdin: str | None = None) -> None:
    """A kernel that breaks one property the host checks has to be refused, for that reason."""
    (OUT / f"{name}.pnk").write_text(source)
    done = run(build(cake, name, host), *args, stdin=stdin)
    if done.returncode != status or (message is not None and message not in done.stderr):
        raise LaneError(f"{host.name} did not refuse {name} (status {done.returncode}):\n{done.stderr}")


def differential(cake: str) -> dict[str, Any]:
    """Every expression and control fixture, run natively on every value pair, against the model's
    values and against `reference`."""
    fixture = json.loads((OUT / "baseline.json").read_text())
    cases, values = fixture["cases"], fixture["values"]
    if len(cases) != 183 or len(values) != 192:
        raise LaneError("unexpected differential fixture coverage")
    expected = [[reference(case["expression"], a, b) for a, b in values] for case in cases]
    for i, row in enumerate(expected):
        if row != cases[i]["expected"]:
            raise LaneError(f"Lean/Python disagreement in expression {i}: {cases[i]['expression']}")
    for name, model in (("control", control), ("control2", control2)):
        expected.append([model(a, b) for a, b in values])
        if expected[-1] != fixture[name]:
            raise LaneError(f"Lean/Python disagreement in {name}")
    (OUT / "probes.pnk").write_text(fixture["source"])
    names = [f"dn_probe_{i}" for i in range(len(cases))] + ["dn_control", "dn_control2"]
    nested = fixture["nested_load_expected"]
    if nested != [0xef, 0xef, 0x0123456789abcdef, 0x0123456789abcdef]:
        raise LaneError("nested-load model disagrees with independent memory fixture")
    driver = '#include "cake_runtime.h"\n#include "host.h"\n#include <inttypes.h>\n'
    driver += "\n".join(f"extern uint32_t {name}(uint64_t,uint64_t,uint64_t);" for name in names)
    driver += "\nstatic uint32_t (*functions[])(uint64_t,uint64_t,uint64_t) = {" + ",".join(names) + "};\n"
    driver += "extern uint32_t dn_nested_1(uint64_t,uint64_t), dn_nested_3(uint64_t,uint64_t);\n"
    driver += r'''
int main(void) {
    dn_runtime_init();
    size_t index, cases = 0;
    uint64_t a, b, expected;
    int read;
    while ((read = scanf("%zu %" SCNu64 " %" SCNu64 " %" SCNu64, &index, &a, &b, &expected)) == 4) {
        if (index >= sizeof(functions)/sizeof(functions[0])) dn_harness("bad input: no case %zu", index);
        uint64_t output[3] = {0xcafebabefeedfaceULL, 0, 0x0123456789abcdefULL};
        uint32_t status = functions[index](a,b,(uintptr_t)&output[1]);
        if (status || output[0] != 0xcafebabefeedfaceULL || output[2] != 0x0123456789abcdefULL)
            dn_violation("case %zu returned %u or wrote beside its output word", index, status);
        uint64_t actual = output[1];
        if (actual != expected)
            dn_violation("native mismatch case=%zu a=%" PRIu64 " b=%" PRIu64 " expected=%" PRIu64
                         " actual=%" PRIu64, index, a, b, expected, actual);
        ++cases;
    }
    if (read != EOF) dn_harness("bad input: unreadable");
    uint64_t cell = 0x0123456789abcdefULL, pointer = (uintptr_t)&cell;
    uint64_t output[3] = {0xcafebabefeedfaceULL, 0, 0x0123456789abcdefULL};
    uint32_t (*nested[])(uint64_t,uint64_t) = {dn_nested_1, dn_nested_3};
    for (size_t i = 0; i < 2; ++i) {
        uint32_t status = nested[i]((uintptr_t)&pointer, (uintptr_t)&output[1]);
        uint64_t expected = i == 0 ? cell & 255 : cell;
        if (status || output[1] != expected || output[0] != 0xcafebabefeedfaceULL ||
            output[2] != 0x0123456789abcdefULL)
            dn_violation("native nested-load mismatch");
    }
    printf("{\"differential_cases\":%zu,\"nested_load_native_cases\":2}\n",cases);
    return 0;
}
'''
    (OUT / "probe_driver.c").write_text(driver)
    vectors = "".join(f"{i} {a} {b} {expected[i][j]}\n"
                      for i in range(len(expected)) for j, (a, b) in enumerate(values))
    measured = measured_by(build(cake, "probes", OUT / "probe_driver.c", "probes"), stdin=vectors)
    if (measured["differential_cases"] != len(expected) * len(values) or
            measured["nested_load_native_cases"] != 2):
        raise LaneError("incomplete native probe execution")
    measured["nested_load_parser_cases"] = len(nested)
    measured["fixture_functions"] = fixture["source"].count("export fun ")
    for index, source in enumerate(fixture["accepted_examples"]):
        (OUT / "accepted.pnk").write_text(source)
        try:
            lanes.pancake(cake, OUT / "accepted.pnk", timeout=60)
        except lanes.Diagnostics as refused:
            raise LaneError(f"the gate accepts example {index}, the compiler does not:\n{source}{refused}") from None
    measured["accepted_example_cases"] = len(fixture["accepted_examples"])
    measured["lexer_keyword_cases"] = lexer_keywords(cake, OUT, fixture["lexer_keywords"])
    return measured


def replies(cake: str) -> dict[str, Any]:
    """The reply table on every input the Lean program answers, and each property the check claims
    broken by a kernel of its own, which the check has to refuse."""
    reply_fixture = json.loads((OUT / "reply-cases.json").read_text())
    cases = reply_cases(reply_fixture)
    stdin = "".join(f"{data.hex() or '-'} {answer.hex() or '-'}\n" for data, answer in cases)
    # The room the program asks for, which the kernel compares against; not the longest reply seen.
    max_len: int = reply_fixture["max_len"]
    host = NATIVE / "reply_check.c"
    measured = measured_by(build(cake, "reply", host), str(max_len), stdin=stdin)
    measured["reply_inputs"] = len(cases)
    if measured["reply_cases"] != 10 * len(cases):
        raise LaneError("incomplete native reply execution")
    text = (OUT / "reply.pnk").read_text()
    lines = text.splitlines(keepends=True)
    store = next(i for i, line in enumerate(lines) if line.lstrip().startswith("st8 "))
    advance = next(i for i, line in enumerate(lines) if re.fullmatch(r"\s*pos = pos \+ \d+;\n", line))
    step = lines[advance].split("+")[-1].strip().rstrip(";")
    guard = f"if {len(REPLY_KEYWORDS[0])} <= inlen {{"
    room = f"if cap < {max_len} {{"
    if guard not in text or text.count(room) != 1:
        raise LaneError("the reply mutations no longer find the lines they change")
    before, after = lines[:advance + 1], lines[advance + 1:]
    lengthened = lines[advance].replace(f"+ {step};", f"+ {int(step) + 1};")
    mutants = {
        # a byte of the reply not written
        "reply-short": ("".join(lines[:store] + lines[store + 1:]), 1),
        # the reply's bytes with the wrong length
        "reply-length": ("".join([*lines[:advance], lengthened, *after]), 1),
        # a byte written past the reply, inside the buffer
        "reply-past": ("".join([*before, "st8 out + pos, 0;\n", *after]), 1),
        # a byte written into the input, which the host may hold read-only
        "reply-input": ("".join([*before, "st8 inp, 0;\n", *after]), -signal.SIGSEGV),
        # a buffer one byte too small accepted
        "reply-room": (text.replace(room, f"if cap < {max_len - 1} {{"), 1),
        # a keyword compared without the length guard reads past the input
        "reply-unguarded": (text.replace(guard, "if 0 <= inlen {", 1), -signal.SIGSEGV),
    }
    for name, (source, status) in mutants.items():
        refuses(cake, name, source, host, status, "reply mismatch" if status == 1 else None, str(max_len),
                stdin=stdin)
    measured["reply_mutants_rejected"] = len(mutants)
    return measured


def echo(cake: str) -> dict[str, Any]:
    """The copy kernel against its contract, and kernels that break the contract, each refused for
    the reason it breaks."""
    host = NATIVE / "echo_check.c"
    measured = measured_by(build(cake, "echo", host))
    text = (OUT / "echo.pnk").read_text()
    lines = text.splitlines(keepends=True)
    if sum(line.lstrip().startswith("st8 ") for line in lines) != 1:
        raise LaneError("echo mutation no longer targets exactly one store")
    bound = "if 4096 < cap {"
    loop = "while i < len {"
    if text.count(bound) != 1 or text.count(loop) != 1:
        raise LaneError("the capacity mutations no longer find the lines they change")
    mutants = {
        # the store removed
        "broken": ("".join(line for line in lines if not line.lstrip().startswith("st8 ")),
                   "copy/frame mismatch"),
        # no upper bound on the capacity
        "echo-unbounded": (text.replace(bound, "if 0 {"), "rejection mismatch"),
        # the bound one too high
        "echo-bound": (text.replace(bound, "if 4097 < cap {"), "rejection mismatch"),
        # the whole capacity copied, the length returned
        "echo-capacity": (text.replace(loop, "while i < cap {"), "copy/frame mismatch"),
    }
    for name, (source, message) in mutants.items():
        refuses(cake, name, source, host, 1, message)
    measured["missing_store_mutant_rejected"] = True
    measured["capacity_mutants_rejected"] = len(mutants) - 1
    return measured


def gates(cake: str) -> int:
    """The two gates every lane compiles through, seen refusing: a warning fails the build, and an
    export outside the project namespace is refused."""
    cases = [("warned", "export fun dn_warned(1 a) { var x = a; var x = a; return x; }\n", "is redeclared"),
             ("stray", "export fun atoi(1 a) { return a; }\n", "outside the project namespace")]
    for name, source, message in cases:
        (OUT / f"{name}.pnk").write_text(source)
        try:
            lanes.assemble(cake, OUT / f"{name}.pnk", timeout=180)
        except LaneError as refused:
            if message not in str(refused):
                raise LaneError(f"the {name} gate failed for another reason: {refused}") from refused
        else:
            raise LaneError(f"the gates no longer refuse {name}")
    return len(cases)


def network() -> Any:
    """The echo server, built on the generated copy, over TCP."""
    server = lanes.link(OUT / "dn-echo", [NATIVE / "echo_server.c", NATIVE / "cake_runtime.c", OUT / "echo.S"],
                        timeout=60)
    done = subprocess.run([sys.executable, str(ROOT / "tests/echo_integration.py"), str(server)],
                          capture_output=True, text=True, timeout=90, check=False)
    if done.returncode:
        raise LaneError(f"TCP integration failed:\n{done.stdout}\n{done.stderr}")
    return json.loads(done.stdout)


def baseline(cake: str, supplied: Path | None) -> Report:
    for name, command in FIXTURES:
        data = (supplied / name).read_bytes() if supplied else lanes.emit(command, timeout=60).encode()
        (OUT / name).write_bytes(data)
    measured = differential(cake)
    render = build(cake, "render", NATIVE / "render_check.c")
    measured.update(measured_by(render))
    measured.update(replies(cake))
    measured.update(echo(cake))
    measured["gate_sensitivity_cases"] = gates(cake)
    measured["network"] = network()
    documented(measured)
    return Report("native-tested", cake, HOSTS, {
        "sources": "supplied" if supplied else "emitted by dn-compiler",
        "assurance": "bounded differential and integration tests, not a whole compiler proof",
        "fixture_sha256": lanes.digest(OUT / "baseline.json"),
        "probe_driver_sha256": lanes.digest(OUT / "probe_driver.c"),
        "echo_source_sha256": lanes.digest(OUT / "echo.pnk"),
        "echo_assembly_sha256": lanes.digest(OUT / "echo.S"),
        "render_source_sha256": lanes.digest(OUT / "render.pnk"),
        "render_assembly_sha256": lanes.digest(OUT / "render.S"),
        "reply_source_sha256": lanes.digest(OUT / "reply.pnk"),
        "reply_cases_sha256": lanes.digest(OUT / "reply-cases.json"),
        "reply_assembly_sha256": lanes.digest(OUT / "reply.S"),
        "reply_executable_sha256": lanes.digest(OUT / "reply-check"),
        "echo_executable_sha256": lanes.digest(OUT / "dn-echo"),
        "measurements": measured}, printed_by_dn_compiler=supplied is None)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--cake", default=os.environ.get("CAKE"))
    parser.add_argument("--fixtures", type=Path,
                        help="directory of previously emitted baseline.json, echo.pnk, render.pnk, "
                             "reply.pnk and reply-cases.json")
    args = parser.parse_args()
    lanes.require_platform(parser)
    cake = lanes.given_cake(parser, args.cake)
    lanes.lane_main("NATIVE BASELINE", OUT, lambda: baseline(cake, args.fixtures))


if __name__ == "__main__":
    main()
