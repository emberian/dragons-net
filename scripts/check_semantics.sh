#!/usr/bin/env bash
# SPDX-License-Identifier: AGPL-3.0-or-later
# The Lean model of Pancake against HOL4's own semantics: every case of the state corpus,
# backend/semantics/states.txt, which the state lane holds equal to what the model prints, is run
# by panSem's evaluate under EVAL in the pinned CakeML tree, and every field it ends in is compared
# with the model's (scripts/semantics_check.py). Then once more with subtraction read as addition,
# which has to be seen. A corpus is not a proof: this shows the two agree on these cases.
set -euo pipefail
cd "$(dirname "$0")/.."
# A module in scripts/ with the name of a standard-library one would otherwise shadow it.
export PYTHONSAFEPATH=1
root="$(pwd)"
# shellcheck source=/dev/null
source scripts/backend_lane.sh
begin_lane SEMANTICS
build_jobs=$(checked_jobs)
[[ -z "${CLINE_OPTIONS:-}${POLY_CLINE_OPTIONS:-}" ]] || refuse "unset CLINE_OPTIONS and POLY_CLINE_OPTIONS"
HOLDIR="$root/.deps/hol"
CAKEMLDIR="$root/.deps/cakeml"
export HOLDIR CAKEMLDIR
prepare_trees
use_holmake

mkdir -p build
holmake_gated "$CAKEMLDIR/pancake/semantics" "$root/build/semantics-holmake.log" "$CAKEMLDIR" "$build_jobs" \
  "$CAKEMLDIR/pancake/semantics/panSemTheory.uo" panSemTheory.uo

corpus="$root/backend/semantics/states.txt"
# evaluate DIR LOG [--defect]: the cases' theory, built outside both pinned trees with one job, so
# that what the theory prints is in LOG.
evaluate() {
  local dir=$1 log=$2
  shift 2
  rm -rf "$dir"
  mkdir -p "$dir"
  cp backend/semantics/Holmakefile backend/semantics/dnShowScript.sml "$dir"
  python3 scripts/semantics_check.py write "$corpus" "$dir/dnStatesScript.sml" "$@"
  holmake_gated "$dir" "$log" "$dir" 1 "$dir/dnStatesTheory.uo" --no_prereqs dnStatesTheory.uo
}
evaluate "$root/build/semantics" "$root/build/semantics-eval.log"
python3 scripts/semantics_check.py compare "$corpus" "$root/build/semantics-eval.log"
evaluate "$root/build/semantics-defect" "$root/build/semantics-defect.log" --defect
python3 scripts/semantics_check.py compare "$corpus" "$root/build/semantics-defect.log" --expect-differences
