#!/usr/bin/env python3
# SPDX-License-Identifier: AGPL-3.0-or-later
"""Run the tests of the modules of tests/ named, verbosely, with tests/ put first on the path once the
interpreter has started: a file a module does not import is then no input of its run (scripts/once.py),
where discovery would look at every file in tests/."""
from pathlib import Path
import sys
import unittest

if len(sys.argv) < 2:
    raise SystemExit("usage: unit.py MODULE...")
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "tests"))
unittest.main(module=None, argv=[sys.argv[0], "-v", *sys.argv[1:]])
