#!/usr/bin/env bash
# SPDX-License-Identifier: AGPL-3.0-or-later
# The native lanes, in order, each with its log in build/evidence/. check_all.sh and CI both run
# them from this one list. The compiler is the one CAKE names, or else the pinned release.
set -euo pipefail
cd "$(dirname "$0")/.."
export PYTHONSAFEPATH=1
cake="${CAKE:-}"
if [[ -z "$cake" ]]; then cake=$(python3 scripts/bootstrap_tool.py cake); fi
mkdir -p build/evidence
lane() {
  local log=$1
  shift
  python3 "$@" --cake "$cake" 2>&1 | tee "build/evidence/$log.log"
}
lane native scripts/native_check.py
lane baseline scripts/native_baseline.py
lane entry scripts/entry_bench.py check
lane parser scripts/parser_contract.py
lane fuzz scripts/native_fuzz.py
