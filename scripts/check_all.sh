#!/usr/bin/env bash
# SPDX-License-Identifier: AGPL-3.0-or-later
# Complete maintained baseline, including real native execution. No skipped lane
# may make this command report success.
set -euo pipefail
cd "$(dirname "$0")/.."
# A module in scripts/ with the name of a standard-library one would otherwise
# shadow it: Python puts the script's directory first on the path. It does the
# same for tests/, which this flag does not cover, so a gate test forbids the
# names there instead.
export PYTHONSAFEPATH=1
# shellcheck disable=SC2312 # a failed uname compares unequal, which refuses to run
if [[ "$(uname -s)" != Linux || "$(uname -m)" != x86_64 ]]; then
  echo 'The checks require Linux x86-64; elsewhere, scripts/check.sh build runs the source gate and the build.' >&2
  exit 1
fi
bash scripts/lint.sh
bash scripts/check.sh
python3 scripts/check_models.py --loom
bash scripts/native_lanes.sh
echo 'DN BASELINE: PASS (models, differential native code, generated programs, both entry designs, the server loop, the framers, the session program, the NNTP server over sockets, the printed source against the parser, concurrency, and TCP echo; see docs/baseline.md for scope)'
