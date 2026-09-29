#!/usr/bin/env bash
# SPDX-License-Identifier: AGPL-3.0-or-later
# The native lanes, in order, each with its log in build/evidence/. check_all.sh and CI both run
# all of them from this one list. Named lanes run alone; the nightly run uses this to start each
# on a fresh machine. The compiler is the one CAKE names, or else the pinned release.
set -euo pipefail
cd "$(dirname "$0")/.."
export PYTHONSAFEPATH=1
lanes=(native baseline entry server framing session nntp parser fuzz)
script_of() {
  case $1 in
    native) script=(scripts/native_check.py) ;;
    baseline) script=(scripts/native_baseline.py) ;;
    entry) script=(scripts/entry_bench.py check) ;;
    server) script=(scripts/server_check.py) ;;
    framing) script=(scripts/framing_check.py) ;;
    session) script=(scripts/session_native.py) ;;
    nntp) script=(scripts/nntp_check.py) ;;
    parser) script=(scripts/parser_contract.py) ;;
    fuzz) script=(scripts/native_fuzz.py) ;;
    *)
      echo "native_lanes.sh: no lane named '$1'; the lanes are ${lanes[*]}" >&2
      exit 2
      ;;
  esac
}
if (($#)); then chosen=("$@"); else chosen=("${lanes[@]}"); fi
# A misspelt name would otherwise run nothing and pass.
for name in "${chosen[@]}"; do script_of "$name"; done
cake="${CAKE:-}"
if [[ -z "$cake" ]]; then cake=$(python3 scripts/bootstrap_tool.py cake); fi
mkdir -p build/evidence
for name in "${chosen[@]}"; do
  script_of "$name"
  python3 "${script[@]}" --cake "$cake" 2>&1 | tee "build/evidence/$name.log"
done
