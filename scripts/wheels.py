#!/usr/bin/env python3
# SPDX-License-Identifier: AGPL-3.0-or-later
"""Put in place the environment of wheels a requirements file pins (scripts/lanes.py) and print its
Python, for checks that take it to find it there."""
from __future__ import annotations

import argparse
from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parent))
import lanes  # the path above is what makes it importable


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("requirements", type=Path)
    print(lanes.pinned_python(parser.parse_args().requirements.resolve()))


if __name__ == "__main__":
    main()
