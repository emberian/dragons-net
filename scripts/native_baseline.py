#!/usr/bin/env python3
# SPDX-License-Identifier: AGPL-3.0-or-later
"""Differential compiler baseline and a real generated-code TCP echo smoke test."""
from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import platform
import re
import shutil
import signal
import subprocess
import sys
from typing import Any

ROOT = Path(__file__).resolve().parents[1]
MASK = (1 << 64) - 1
# Hardening the linked binaries: position-independent with full RELRO, fortified library
# calls, stack protection and control-flow protection. The generated assembly is
# position-independent, so nothing here needs a fixed load address.
HARDENING = ["-O2", "-Wall", "-Wextra", "-Werror", "-fPIE", "-pie",
             "-Wl,-z,relro,-z,now", "-Wl,-z,noexecstack",
             "-D_FORTIFY_SOURCE=3", "-fstack-protector-strong", "-fstack-clash-protection",
             "-fcf-protection=full", "-Wformat=2"]
# Global symbols the Cake runtime defines in every generated assembly file.
RUNTIME_SYMBOLS = {"cake_bitmaps_buffer_begin", "cake_bitmaps_buffer_end",
                   "cake_codebuffer_begin", "cake_codebuffer_end", "cake_text_begin",
                   "cml_heap", "cml_main", "cml_stack", "cml_stackend"}
# Must stay equal to Checked.exportPrefix; a test holds the two together.
EXPORT_PREFIX = "dn_"


def signed(n: int) -> int:
    return n if n < 1 << 63 else n - (1 << 64)


def reference(expr: Any, a: int, b: int) -> int:
    if isinstance(expr, int):
        return expr & MASK
    if isinstance(expr, str):
        return {"a": a, "b": b}[expr]
    op, lhs, rhs = expr
    x, y = reference(lhs, a, b), reference(rhs, a, b)
    if op == ">>>" and y >= 64:
        raise ValueError("the model gives a shift of a whole word or more no value")
    results = {"+": (x + y) & MASK, "-": (x - y) & MASK, "*": (x * y) & MASK, "&": x & y,
               "<": int(signed(x) < signed(y)), "<=": int(signed(x) <= signed(y)), "==": int(x == y),
               ">>>": (x >> y) & MASK}
    if op not in results:
        raise ValueError(op)
    return results[op]


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
        raise RuntimeError(f"unexpected reply function {fixture['function']}")
    cases = [(bytes(case["input"]), bytes(case["output"])) for case in fixture["cases"]]
    for data, answer in cases:
        if reply(data) != answer:
            raise RuntimeError(f"Lean/Python disagreement on the reply to {data!r}")
    if fixture["max_len"] != max(len(reply(keyword)) for keyword in (*REPLY_KEYWORDS, b"")):
        raise RuntimeError("the reply buffer the program asks for is not its longest reply")
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
        raise RuntimeError("the reply inputs no longer reach every keyword boundary and reply")
    return cases


def digest(p: Path | str) -> str:
    return hashlib.sha256(Path(p).read_bytes()).hexdigest()


def loud(command: list[str], *, timeout: int, what: str, stdin: Any = None) -> str:
    """Run a step and, when it fails, say what it printed rather than only its status."""
    done = subprocess.run(command, stdin=stdin, capture_output=True, text=True,
                          timeout=timeout, check=False)
    if done.returncode:
        raise RuntimeError(f"{what} failed with status {done.returncode}:\n"
                           f"{done.stdout}{done.stderr}")
    return done.stdout


def check_symbols(assembly: Path, obj: Path) -> None:
    """An exported name becomes a global C symbol.

    Anything outside the runtime's own set has to stay in this project's namespace, or it can
    displace a libc function of the host it is linked into.
    """
    subprocess.run([os.environ.get("CC", "cc"), "-c", str(assembly), "-o", str(obj)],
                   check=True, timeout=60)
    listing = subprocess.run(["nm", "--defined-only", "--extern-only", str(obj)],
                             capture_output=True, text=True, check=True, timeout=60)
    symbols = {line.split()[-1] for line in listing.stdout.splitlines() if line.strip()}
    if not symbols & RUNTIME_SYMBOLS:
        raise RuntimeError(f"{obj.name} carries no runtime symbol; the check is looking at nothing")
    stray = sorted(s for s in symbols - RUNTIME_SYMBOLS if not s.startswith(EXPORT_PREFIX))
    if stray:
        raise RuntimeError(f"{assembly.name} exports symbols outside the project namespace: {stray}")


def compiler_revision(cake: str) -> str:
    """The revision the compiler reports for itself, not the one a lock file claims."""
    printed = subprocess.run([cake, "--version"], capture_output=True, text=True, timeout=60,
                             check=True).stdout
    found = re.search(r"CakeML:\s*([0-9a-f]{40})", printed)
    if not found:
        raise RuntimeError(f"the compiler does not report a revision:\n{printed}")
    return found.group(1)


def hardened(binary: Path) -> None:
    """The linked binary must carry the protections it was built with, read off the file."""
    name = binary.name
    header = loud(["readelf", "-hdl", str(binary)], timeout=60, what=f"reading {name}")
    symbols = loud(["nm", "-u", str(binary)], timeout=60, what=f"reading symbols of {name}")
    if "DYN (" not in header:
        raise RuntimeError(f"{name} is not position-independent")
    if "BIND_NOW" not in header:
        raise RuntimeError(f"{name} was linked without BIND_NOW")
    if "GNU_RELRO" not in header:
        raise RuntimeError(f"{name} has no read-only-after-relocation segment")
    if "TEXTREL" in header:
        raise RuntimeError(f"{name} needs text relocations")
    stack = [line for line in header.splitlines() if "GNU_STACK" in line]
    if not stack or "RWE" in stack[0]:
        raise RuntimeError(f"{name} does not declare a non-executable stack")
    if "__stack_chk_fail" not in symbols:
        raise RuntimeError(f"{name} was built without stack protection")
    if not any(check in symbols for check in ("_chk@", "_chk")):
        raise RuntimeError(f"{name} was built without fortified library calls")


def lexer_keywords(cake: str, out: Path, table: list[dict[str, Any]]) -> int:
    """The compiler itself decides what a keyword is; the table has to agree with it.

    Words the table calls keywords of the running compiler's revision must be refused as
    names, and words it records only for another pinned revision must be accepted.
    """
    revision = compiler_revision(cake)
    listed = {entry["revision"]: entry["keywords"] for entry in table}
    if revision not in listed:
        raise RuntimeError(f"the fixture carries no keyword list for {revision[:7]}")
    here = listed[revision]
    # With one pinned revision, or two that agree, a word no lexer reserves keeps the check
    # two-sided: the compiler has to accept it.
    elsewhere = sorted({word for words in listed.values() for word in words} - set(here)) or ["base"]
    if not here:
        raise RuntimeError("the keyword table has no words for the running compiler")
    source = out / "keyword.pnk"
    for word, is_keyword in [(w, True) for w in here] + [(w, False) for w in elsewhere]:
        source.write_text(f"export fun dn_word(1 a) {{ var {word} = a; return {word}; }}\n")
        with source.open("rb") as inp:
            probe = subprocess.run([cake, "--pancake", "--main_return=true"], stdin=inp,
                                   capture_output=True, timeout=60, check=False)
        if is_keyword and probe.returncode == 0:
            raise RuntimeError(f"the compiler accepts {word} as a name; the table calls it a keyword")
        if not is_keyword and probe.returncode != 0:
            raise RuntimeError(f"the compiler refuses {word} as a name; the table does not list it")
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
        printed = f"{measured[key]:,}"
        for name in files:
            if printed not in (ROOT / name).read_text():
                raise RuntimeError(f"{name} does not quote {key} as {printed}")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--cake", default=os.environ.get("CAKE"))
    parser.add_argument("--fixtures", type=Path,
                        help="directory of previously emitted baseline.json, echo.pnk, render.pnk, "
                             "reply.pnk and reply-cases.json")
    args = parser.parse_args()
    if platform.system() != "Linux" or platform.machine() != "x86_64":
        parser.error("native baseline requires Linux x86-64")
    cake = shutil.which(args.cake or "")
    if not cake:
        parser.error("provide --cake or CAKE; no interpreted fallback")
    out = ROOT / "build/baseline"
    out.mkdir(parents=True, exist_ok=True)
    report_file = out / "report.json"
    report_file.unlink(missing_ok=True)
    compiler = ROOT / ".lake/build/bin/dn-compiler"
    for name, command in [("baseline.json", "emit-baseline"), ("echo.pnk", "emit-echo"),
                          ("render.pnk", "emit-render"), ("reply.pnk", "emit-reply"),
                          ("reply-cases.json", "emit-reply-cases")]:
        data = ((args.fixtures / name).read_bytes() if args.fixtures else
                loud([str(compiler), command], timeout=60, what=f"emitting {name}").encode())
        (out / name).write_bytes(data)
    fixture = json.loads((out / "baseline.json").read_text())
    cases, values = fixture["cases"], fixture["values"]
    if len(cases) != 113 or len(values) != 192:
        raise RuntimeError("unexpected differential fixture coverage")
    expected = [[reference(case["expression"], a, b) for a, b in values] for case in cases]
    for i, row in enumerate(expected):
        if row != cases[i]["expected"]:
            raise RuntimeError(f"Lean/Python disagreement in expression {i}: {cases[i]['expression']}")
    for name, model in (("control", control), ("control2", control2)):
        expected.append([model(a, b) for a, b in values])
        if expected[-1] != fixture[name]:
            raise RuntimeError(f"Lean/Python disagreement in {name}")
    (out / "probes.pnk").write_text(fixture["source"])
    names = [f"dn_probe_{i}" for i in range(len(cases))] + ["dn_control", "dn_control2"]
    nested = fixture["nested_load_expected"]
    if nested != [0xef, 0xef, 0x0123456789abcdef, 0x0123456789abcdef]:
        raise RuntimeError("nested-load model disagrees with independent memory fixture")
    driver = '#include "cake_runtime.h"\n#include <inttypes.h>\n'
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
        if (index >= sizeof(functions)/sizeof(functions[0])) return 2;
        uint64_t output[3] = {0xcafebabefeedfaceULL, 0, 0x0123456789abcdefULL};
        uint32_t status = functions[index](a,b,(uintptr_t)&output[1]);
        if (status || output[0] != 0xcafebabefeedfaceULL || output[2] != 0x0123456789abcdefULL) return 3;
        uint64_t actual = output[1];
        if (actual != expected) {
            fprintf(stderr,"native mismatch case=%zu a=%" PRIu64 " b=%" PRIu64
                    " expected=%" PRIu64 " actual=%" PRIu64 "\n", index,a,b,expected,actual);
            return 1;
        }
        ++cases;
    }
    if (read != EOF) return 2;
    uint64_t cell = 0x0123456789abcdefULL, pointer = (uintptr_t)&cell;
    uint64_t output[3] = {0xcafebabefeedfaceULL, 0, 0x0123456789abcdefULL};
    uint32_t (*nested[])(uint64_t,uint64_t) = {dn_nested_1, dn_nested_3};
    for (size_t i = 0; i < 2; ++i) {
        uint32_t status = nested[i]((uintptr_t)&pointer, (uintptr_t)&output[1]);
        uint64_t expected = i == 0 ? cell & 255 : cell;
        if (status || output[1] != expected || output[0] != 0xcafebabefeedfaceULL ||
            output[2] != 0x0123456789abcdefULL) {
            fputs("native nested-load mismatch\n", stderr); return 1;
        }
    }
    printf("{\"differential_cases\":%zu,\"nested_load_native_cases\":2}\n",cases);
    return 0;
}
'''
    (out / "probe_driver.c").write_text(driver)

    def compile_source(name: str) -> None:
        # A Pancake warning (a redeclared variable, say) leaves the exit status at zero,
        # so anything on stderr fails the build.
        with (out / f"{name}.pnk").open("rb") as inp, (out / f"{name}.S").open("wb") as asm:
            compiled = subprocess.run([cake, "--pancake", "--main_return=true"], stdin=inp,
                                      stdout=asm, stderr=subprocess.PIPE, timeout=180, check=False)
        if compiled.returncode or compiled.stderr:
            raise RuntimeError(f"{name}.pnk compiled with diagnostics:\n"
                               f"{compiled.stderr.decode(errors='replace')}")
        check_symbols(out / f"{name}.S", out / f"{name}.o")


    def link(name: str, source: Path, assembly: Path) -> None:
        loud([os.environ.get("CC", "cc"), *HARDENING, "-g", "-I", str(ROOT / "native"),
              str(source), str(ROOT / "native/cake_runtime.c"), str(assembly),
              "-o", str(out / name)], timeout=60, what=f"linking {name}")
        hardened(out / name)

    compile_source("probes")
    link("probes", out / "probe_driver.c", out / "probes.S")
    vectors = "".join(f"{i} {a} {b} {expected[i][j]}\n"
                      for i in range(len(expected)) for j, (a, b) in enumerate(values))
    probed = subprocess.run([str(out / "probes")], input=vectors, text=True,
                            capture_output=True, timeout=60, check=False)
    if probed.returncode:
        raise RuntimeError(f"the differential probes failed with status {probed.returncode}:\n"
                           f"{probed.stdout}{probed.stderr}")
    measured = json.loads(probed.stdout)
    if measured["differential_cases"] != len(expected) * len(values) or measured["nested_load_native_cases"] != 2:
        raise RuntimeError("incomplete native probe execution")
    measured["nested_load_parser_cases"] = len(nested)
    for index, source in enumerate(fixture["accepted_examples"]):
        (out / "accepted.pnk").write_text(source)
        with (out / "accepted.pnk").open("rb") as inp:
            accepted = subprocess.run([cake, "--pancake", "--main_return=true"], stdin=inp,
                                      capture_output=True, timeout=60, check=False)
        if accepted.returncode or accepted.stderr:
            raise RuntimeError(f"the gate accepts example {index}, the compiler does not:\n"
                               f"{source}{accepted.stderr.decode(errors='replace')}")
    measured["accepted_example_cases"] = len(fixture["accepted_examples"])
    measured["lexer_keyword_cases"] = lexer_keywords(cake, out, fixture["lexer_keywords"])
    compile_source("render")
    link("render-check", ROOT / "native/render_check.c", out / "render.S")
    measured.update(json.loads(loud([str(out / "render-check")], timeout=60,
                                    what="the decimal render check")))
    reply_fixture = json.loads((out / "reply-cases.json").read_text())
    replies = reply_cases(reply_fixture)
    reply_input = "".join(f"{data.hex() or '-'} {answer.hex() or '-'}\n" for data, answer in replies)
    # The room the program asks for, which the kernel compares against; not the longest reply seen.
    max_len: int = reply_fixture["max_len"]

    def run_reply(name: str) -> subprocess.CompletedProcess[str]:
        compile_source(name)
        link(f"{name}-check", ROOT / "native/reply_check.c", out / f"{name}.S")
        return subprocess.run([str(out / f"{name}-check"), str(max_len)], input=reply_input,
                              text=True, capture_output=True, timeout=120, check=False)

    checked = run_reply("reply")
    if checked.returncode:
        raise RuntimeError(f"the reply check failed with status {checked.returncode}:\n"
                           f"{checked.stdout}{checked.stderr}")
    measured.update(json.loads(checked.stdout))
    measured["reply_inputs"] = len(replies)
    if measured["reply_cases"] != 10 * len(replies):
        raise RuntimeError("incomplete native reply execution")
    # Sensitivity: each property the check claims has a kernel that breaks that property alone,
    # and the check has to refuse every one of them.
    text = (out / "reply.pnk").read_text()
    lines = text.splitlines(keepends=True)
    store = next(i for i, line in enumerate(lines) if line.lstrip().startswith("st8 "))
    advance = next(i for i, line in enumerate(lines) if re.fullmatch(r"\s*pos = pos \+ \d+;\n", line))
    step = lines[advance].split("+")[-1].strip().rstrip(";")
    guard = f"if {len(REPLY_KEYWORDS[0])} <= inlen {{"
    room = f"if cap < {max_len} {{"
    if guard not in text or text.count(room) != 1:
        raise RuntimeError("the reply mutations no longer find the lines they change")
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
        (out / f"{name}.pnk").write_text(source)
        broken = run_reply(name)
        if broken.returncode != status or (status == 1 and "reply mismatch" not in broken.stderr):
            raise RuntimeError(f"the reply check did not refuse {name} (status {broken.returncode}):\n"
                               f"{broken.stderr}")
    measured["reply_mutants_rejected"] = len(mutants)
    compile_source("echo")
    link("echo-check", ROOT / "native/echo_check.c", out / "echo.S")
    measured.update(json.loads(loud([str(out / "echo-check")], timeout=30,
                                    what="the copy and frame check")))
    # Sensitivity check: compiling a kernel without its store must fail the same
    # native contract test. No checked-in source or backend checkout is mutated.
    text = (out / "echo.pnk").read_text()
    lines = text.splitlines(keepends=True)
    if sum(line.lstrip().startswith("st8 ") for line in lines) != 1:
        raise RuntimeError("echo mutation no longer targets exactly one store")
    (out / "broken.pnk").write_text("".join(line for line in lines if not line.lstrip().startswith("st8 ")))
    compile_source("broken")
    link("broken-check", ROOT / "native/echo_check.c", out / "broken.S")
    broken = subprocess.run([str(out / "broken-check")], capture_output=True, text=True, timeout=30,
                            check=False)
    if broken.returncode != 1 or "copy/frame mismatch" not in broken.stderr:
        raise RuntimeError("copy test did not detect the deliberately removed store")
    measured["missing_store_mutant_rejected"] = True
    # Sensitivity of the two gates around the compiler: a warning must fail the build, and
    # an export outside the project namespace must be refused.
    (out / "warned.pnk").write_text(
        "export fun dn_warned(1 a) { var x = a; var x = a; return x; }\n")
    try:
        compile_source("warned")
    except RuntimeError as refused:
        if "is redeclared" not in str(refused):
            raise RuntimeError(f"the warning gate failed for another reason: {refused}") from refused
    else:
        raise RuntimeError("a redeclaration warning no longer fails the build")
    (out / "stray.pnk").write_text("export fun atoi(1 a) { return a; }\n")
    with (out / "stray.pnk").open("rb") as inp, (out / "stray.S").open("wb") as asm:
        subprocess.run([cake, "--pancake", "--main_return=true"], stdin=inp, stdout=asm,
                       check=True, timeout=180)
    try:
        check_symbols(out / "stray.S", out / "stray.o")
    except RuntimeError as refused:
        if "outside the project namespace" not in str(refused):
            raise RuntimeError(f"the symbol gate failed for another reason: {refused}") from refused
    else:
        raise RuntimeError("an export outside the project namespace is no longer refused")
    measured["gate_sensitivity_cases"] = 2
    link("dn-echo", ROOT / "native/echo_server.c", out / "echo.S")
    network = subprocess.run([sys.executable, str(ROOT / "tests/echo_integration.py"),
                              str(out / "dn-echo")], capture_output=True, text=True, timeout=90, check=False)
    if network.returncode:
        raise RuntimeError(f"TCP integration failed:\n{network.stdout}\n{network.stderr}")
    measured["network"] = json.loads(network.stdout)
    report = {"status": "native-tested",
              "sources": "supplied" if args.fixtures else "emitted by dn-compiler",
              "compiler_digest": digest(compiler) if not args.fixtures else None,
              "assurance": "bounded differential and integration tests, not a whole compiler proof",
              "platform": platform.platform(), "compiler_sha256": digest(cake),
              "fixture_sha256": digest(out / "baseline.json"), "echo_source_sha256": digest(out / "echo.pnk"),
              "echo_assembly_sha256": digest(out / "echo.S"),
              "render_source_sha256": digest(out / "render.pnk"),
              "render_assembly_sha256": digest(out / "render.S"),
              "reply_source_sha256": digest(out / "reply.pnk"),
              "reply_cases_sha256": digest(out / "reply-cases.json"),
              "reply_assembly_sha256": digest(out / "reply.S"),
              "reply_check_sha256": digest(ROOT / "native/reply_check.c"),
              "reply_executable_sha256": digest(out / "reply-check"),
              "render_check_sha256": digest(ROOT / "native/render_check.c"),
              "echo_check_sha256": digest(ROOT / "native/echo_check.c"),
              "echo_executable_sha256": digest(out / "dn-echo"),
              "host_sha256": digest(ROOT / "native/echo_server.c"),
              "runtime_sha256": digest(ROOT / "native/cake_runtime.c"),
              "runtime_header_sha256": digest(ROOT / "native/cake_runtime.h"),
              "measurements": measured}
    documented(measured)
    report_file.write_text(json.dumps(report, indent=2) + "\n")
    print(report_file.read_text(), end="")


if __name__ == "__main__":
    main()
