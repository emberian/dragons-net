#!/usr/bin/env python3
# SPDX-License-Identifier: AGPL-3.0-or-later
"""The modules of a certificate of the safety analysis, as `dn-compiler analysis-cert` prints them,
written to lean/, and those of it no longer printed removed: `python3 scripts/analysis_cert.py session`.
A test holds the files to what it prints."""
from __future__ import annotations

import argparse
import json
from pathlib import Path
import subprocess

ROOT = Path(__file__).resolve().parent.parent
DN_COMPILER = ROOT / ".lake/build/bin/dn-compiler"
MODULES = {"session": "DN.Server.SessionCert", "recover": "DN.News.RecoverCert"}


def path_of(module: str) -> Path:
    return ROOT / "lean" / f"{module.replace('.', '/')}.lean"


def printed(what: str) -> dict[Path, str]:
    """Each module's text by its file."""
    done = subprocess.run([str(DN_COMPILER), "analysis-cert", what], text=True, capture_output=True,
                          check=False, timeout=600)
    if done.returncode != 0:
        raise SystemExit(f"dn-compiler analysis-cert {what}: {done.stderr.strip()}")
    modules: dict[str, str] = json.loads(done.stdout)
    return {path_of(module): text for module, text in modules.items()}


def present(what: str) -> list[Path]:
    """The files there are of the certificate's module and of the modules under it."""
    top = path_of(MODULES[what])
    return sorted(path for path in [top, *top.with_suffix("").rglob("*.lean")] if path.exists())


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("what", choices=sorted(MODULES))
    what = parser.parse_args().what
    files = printed(what)
    for path in present(what):
        if path not in files:
            path.unlink()
    for path, text in files.items():
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(text)


if __name__ == "__main__":
    main()
