#!/usr/bin/env python3
"""Run the inherited closed compiler examples as executable regressions.

These are named Boolean test cases, deliberately separate from kernel proofs.
"""
from pathlib import Path
import re
import subprocess

ROOT = Path(__file__).resolve().parents[1]


def main():
    checks, imports = [], []
    for path in sorted((ROOT / "lean/DN").rglob("*.lean")):
        namespaces = []
        found = False
        for line in path.read_text().splitlines():
            if match := re.match(r"^namespace ([\w.]+)\s*$", line):
                namespaces.append(match[1])
            elif match := re.match(r"^end ([\w.]+)\s*$", line):
                if namespaces and namespaces[-1] == match[1]:
                    namespaces.pop()
            elif match := re.match(r"^def (regression_\d+) : Bool", line):
                checks.append(".".join(namespaces + [match[1]]))
                found = True
        if found:
            imports.append("import " + ".".join(path.relative_to(ROOT / "lean").with_suffix("").parts))
    if not checks:
        raise SystemExit("no compiler regression cases discovered")
    target = ROOT / "build/CompilerChecks.lean"
    target.parent.mkdir(exist_ok=True)
    body = ["def main : IO Unit := do"]
    for name in checks:
        body.append(f'  unless {name} do throw (IO.userError "failed: {name}")')
    body.append(f'  IO.println "Compiler/dataplane examples: {len(checks)} executable cases passed (not proofs)"')
    target.write_text("\n".join(imports + [""] + body) + "\n")
    subprocess.run(["lake", "env", "lean", "--run", str(target)], cwd=ROOT, check=True, timeout=120)


if __name__ == "__main__":
    main()
