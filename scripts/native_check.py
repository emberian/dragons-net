#!/usr/bin/env python3
"""Compile emitted Pancake and run the real exported kernel on Linux x86-64.

CAKE must name an existing compiler executable. Its digest is recorded, not
silently treated as the verified build of backend/lock.json.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import platform
import shutil
import subprocess

ROOT = Path(__file__).resolve().parents[1]


def digest(path: Path | str) -> str:
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--cake", default=os.environ.get("CAKE"))
    parser.add_argument("--source", type=Path, help="Previously emitted .pnk; defaults to running dn-compiler")
    args = parser.parse_args()
    if platform.system() != "Linux" or platform.machine() not in ("x86_64", "AMD64"):
        parser.error("the initial native adapter targets Linux x86-64; model/host checks are portable")
    cake = shutil.which(args.cake or "")
    if not cake:
        parser.error("set CAKE or --cake to a Pancake-capable compiler; no native fallback exists")
    out = ROOT / "build/native"
    out.mkdir(parents=True, exist_ok=True)
    report_path = out / "report.json"
    report_path.unlink(missing_ok=True)  # A failed rerun must not leave a stale PASS.
    source = out / "region.pnk"
    if args.source:
        source.write_bytes(args.source.read_bytes())
    else:
        source.write_bytes(subprocess.check_output([str(ROOT / ".lake/build/bin/dn-compiler"), "emit-region"]))
    assembly = out / "region.S"
    with source.open("rb") as inp, assembly.open("wb") as output:
        subprocess.run([cake, "--pancake", "--main_return=true"], stdin=inp, stdout=output,
                       check=True, timeout=120)
    cc = os.environ.get("CC", "cc")
    driver = ROOT / "native/region_driver.c"
    executable = out / "region-check"
    subprocess.run([cc, "-O2", "-Wall", "-Wextra", "-Werror", "-no-pie", "-Wl,-z,noexecstack",
                    str(driver), str(assembly), "-o", str(executable)], check=True, timeout=60)
    result = subprocess.run([str(executable)], text=True, capture_output=True, check=True, timeout=60)
    measured = json.loads(result.stdout)
    if measured["vectors"] != 99240 or measured["checksum"] == 0 or measured["elapsed_ns"] <= 0:
        raise RuntimeError("native region coverage or execution evidence is incomplete")
    measured["MiB_per_second"] = measured["bytes"] * 1e9 / measured["elapsed_ns"] / 1048576
    report = {"status": "native-tested", "assurance": "not an end-to-end compiler proof",
              "platform": platform.platform(), "cpu": platform.processor(),
              "compiler_sha256": digest(cake), "source_sha256": digest(source),
              "assembly_sha256": digest(assembly), "executable_sha256": digest(executable),
              "adapter_sha256": digest(driver), "measurements": measured}
    report_path.write_text(json.dumps(report, indent=2) + "\n")
    print(report_path.read_text(), end="")


if __name__ == "__main__":
    main()
