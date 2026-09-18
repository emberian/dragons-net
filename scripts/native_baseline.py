#!/usr/bin/env python3
"""Differential compiler baseline and a real generated-code TCP echo smoke test."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import platform
import shutil
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
MASK = (1 << 64) - 1


def signed(n):
    return n if n < 1 << 63 else n - (1 << 64)


def reference(expr, a, b):
    if isinstance(expr, int):
        return expr & MASK
    if isinstance(expr, str):
        return {"a": a, "b": b}[expr]
    op, lhs, rhs = expr
    l, r = reference(lhs, a, b), reference(rhs, a, b)
    if op == "+": return (l + r) & MASK
    if op == "-": return (l - r) & MASK
    if op == "*": return (l * r) & MASK
    if op == "&": return l & r
    if op == "<": return int(signed(l) < signed(r))
    if op == "<=": return int(signed(l) <= signed(r))
    if op == "==": return int(l == r)
    raise ValueError(op)


def control(a, b):
    acc = b
    for i in range(min(a & 31, 7)):
        acc = (acc + i if signed(acc) < 0 else acc * 3 + 1) & MASK
    return acc


def digest(p):
    return hashlib.sha256(Path(p).read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--cake", default=os.environ.get("CAKE"))
    parser.add_argument("--fixtures", type=Path, help="directory of previously emitted baseline.json and echo.pnk")
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
    for name, command in [("baseline.json", "emit-baseline"), ("echo.pnk", "emit-echo")]:
        data = ((args.fixtures / name).read_bytes() if args.fixtures else
                subprocess.check_output([str(compiler), command], timeout=60))
        (out / name).write_bytes(data)
    fixture = json.loads((out / "baseline.json").read_text())
    cases, values = fixture["cases"], fixture["values"]
    if len(cases) != 108 or len(values) != 192:
        raise RuntimeError("unexpected differential fixture coverage")
    expected = [[reference(case["expression"], a, b) for a, b in values] for case in cases]
    for i, row in enumerate(expected):
        if row != cases[i]["expected"]:
            raise RuntimeError(f"Lean/Python disagreement in expression {i}: {cases[i]['expression']}")
    expected.append([control(a, b) for a, b in values])
    if expected[-1] != fixture["control"]:
        raise RuntimeError("Lean/Python control-flow disagreement")
    (out / "probes.pnk").write_text(fixture["source"])
    names = [f"dn_probe_{i}" for i in range(len(cases))] + ["dn_control"]
    driver = '#include "cake_runtime.h"\n#include <inttypes.h>\n'
    driver += "\n".join(f"extern uint32_t {name}(uint64_t,uint64_t,uint64_t);" for name in names)
    driver += "\nstatic uint32_t (*functions[])(uint64_t,uint64_t,uint64_t) = {" + ",".join(names) + "};\n"
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
            fprintf(stderr,"native mismatch case=%zu a=%" PRIu64 " b=%" PRIu64 " expected=%" PRIu64 " actual=%" PRIu64 "\n",
                    index,a,b,expected,actual); return 1;
        }
        ++cases;
    }
    if (read != EOF) return 2;
    printf("{\"differential_cases\":%zu}\n",cases);
    return 0;
}
'''
    (out / "probe_driver.c").write_text(driver)

    def compile_source(name):
        with (out / f"{name}.pnk").open("rb") as inp, (out / f"{name}.S").open("wb") as asm:
            subprocess.run([cake, "--pancake", "--main_return=true"], stdin=inp, stdout=asm,
                           check=True, timeout=180)

    def link(name, source, assembly):
        subprocess.run([os.environ.get("CC", "cc"), "-O2", "-g", "-Wall", "-Wextra", "-Werror",
                        "-no-pie", "-Wl,-z,noexecstack", "-I", str(ROOT / "native"),
                        str(source), str(assembly), "-o", str(out / name)], check=True, timeout=60)

    compile_source("probes")
    link("probes", out / "probe_driver.c", out / "probes.S")
    vectors = "".join(f"{i} {a} {b} {expected[i][j]}\n"
                      for i in range(len(expected)) for j, (a, b) in enumerate(values))
    result = subprocess.run([str(out / "probes")], input=vectors, text=True,
                            capture_output=True, timeout=60)
    if result.returncode:
        raise RuntimeError(result.stderr)
    measured = json.loads(result.stdout)
    if measured["differential_cases"] != len(expected) * len(values):
        raise RuntimeError("incomplete native probe execution")
    compile_source("echo")
    link("echo-check", ROOT / "native/echo_check.c", out / "echo.S")
    measured.update(json.loads(subprocess.check_output([str(out / "echo-check")], timeout=30)))
    # Sensitivity check: compiling a kernel without its store must fail the same
    # native contract test. No checked-in source or backend checkout is mutated.
    text = (out / "echo.pnk").read_text()
    lines = text.splitlines(keepends=True)
    if sum(line.lstrip().startswith("st8 ") for line in lines) != 1:
        raise RuntimeError("echo mutation no longer targets exactly one store")
    (out / "broken.pnk").write_text("".join(line for line in lines if not line.lstrip().startswith("st8 ")))
    compile_source("broken")
    link("broken-check", ROOT / "native/echo_check.c", out / "broken.S")
    broken = subprocess.run([str(out / "broken-check")], capture_output=True, text=True, timeout=30)
    if broken.returncode != 1 or "copy/frame mismatch" not in broken.stderr:
        raise RuntimeError("copy test did not detect the deliberately removed store")
    link("dn-echo", ROOT / "native/echo_server.c", out / "echo.S")
    network = subprocess.run([sys.executable, str(ROOT / "tests/echo_integration.py"),
                              str(out / "dn-echo")], check=True, capture_output=True, text=True, timeout=90)
    measured["network"] = json.loads(network.stdout)
    report = {"status": "native-tested", "assurance": "bounded differential and integration tests, not a whole compiler proof",
              "platform": platform.platform(), "compiler_sha256": digest(cake),
              "fixture_sha256": digest(out / "baseline.json"), "echo_source_sha256": digest(out / "echo.pnk"),
              "echo_assembly_sha256": digest(out / "echo.S"), "echo_executable_sha256": digest(out / "dn-echo"),
              "host_sha256": digest(ROOT / "native/echo_server.c"),
              "runtime_sha256": digest(ROOT / "native/cake_runtime.h"),
              "missing_store_mutant_rejected": True, "measurements": measured}
    report_file.write_text(json.dumps(report, indent=2) + "\n")
    print(report_file.read_text(), end="")


if __name__ == "__main__":
    main()
