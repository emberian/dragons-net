#!/usr/bin/env python3
# SPDX-License-Identifier: AGPL-3.0-or-later
"""Run a command and say how long it took and how much memory its largest process held, so that
the cost of a step shows in the log as the code grows."""
import resource
import subprocess
import sys
import time


def main() -> None:
    start = time.monotonic()
    status = subprocess.run(sys.argv[1:], check=False).returncode
    largest = resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss // 1024
    print(f"DN MEASURED {' '.join(sys.argv[1:3])}: {time.monotonic() - start:.0f} s, largest process {largest} MB",
          flush=True)
    sys.exit(status)


if __name__ == "__main__":
    main()
