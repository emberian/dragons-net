#!/usr/bin/env bash
# Complete maintained baseline, including real native execution. No skipped lane
# may make this command report success.
set -euo pipefail
cd "$(dirname "$0")/.."
# A module in scripts/ with the name of a standard-library one would otherwise
# shadow it: Python puts the script's directory first on the path. It does the
# same for tests/, which this flag does not cover, so a gate test forbids the
# names there instead.
export PYTHONSAFEPATH=1
if [[ "$(uname -s)" != Linux || "$(uname -m)" != x86_64 ]]; then
  echo 'The checks require Linux x86-64; elsewhere, scripts/check.sh build runs the source gate and the build.' >&2
  exit 1
fi
bash scripts/lint.sh
bash scripts/check.sh
python3 scripts/check_models.py --loom
cake="${CAKE:-}"
if [[ -z "$cake" ]]; then cake=$(python3 scripts/bootstrap_tool.py cake); fi
python3 scripts/native_check.py --cake "$cake"
python3 scripts/native_baseline.py --cake "$cake"
echo 'DN BASELINE: PASS (models, differential native code, concurrency, and TCP echo; see docs/baseline.md for scope)'
