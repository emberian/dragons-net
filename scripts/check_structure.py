#!/usr/bin/env python3
"""Cheap repository invariants, including proof coverage and offline RFC integrity."""
import hashlib
import json
from pathlib import Path
import re
import sys

ROOT = Path(__file__).resolve().parents[1]


def check(root=ROOT):
    errors = []
    audit = root / "lean/DN/Audit.lean"
    expected = {".".join(p.relative_to(root / "lean").with_suffix("").parts)
                for p in (root / "lean/DN").rglob("*.lean") if p != audit}
    actual = set(re.findall(r"^import (DN\.[\w.]+)$", audit.read_text(), re.M))
    if actual != expected:
        errors.append(f"audit import inventory mismatch: missing={expected-actual}, extra={actual-expected}")
    for p in (root / "lean").rglob("*.lean"):
        # This is a hygiene tripwire, NOT the axiom audit or a Lean parser.
        if re.search(r"^\s*#(?:eval|guard)\b", p.read_text(), re.M):
            errors.append(f"evaluation-only assertion in {p.relative_to(root)}; use a named theorem or executable test")
    for name, item in json.loads((root / "rfcs/manifest.json").read_text())["documents"].items():
        if hashlib.sha256((root / "rfcs" / name).read_bytes()).hexdigest() != item["sha256"]:
            errors.append(f"RFC digest mismatch: {name}")
    lock = json.loads((root / "backend/lock.json").read_text())
    for item in lock["patches"]:
        p = root / "backend" / item["path"]
        if hashlib.sha256(p.read_bytes()).hexdigest() != item["sha256"]:
            errors.append(f"backend patch digest mismatch: {item['path']}")
    return errors


if __name__ == "__main__":
    errors = check()
    if errors:
        sys.exit("\n".join(errors))
    print("structure: proof inventory, RFC digests and backend patch digests OK")
