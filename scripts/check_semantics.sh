#!/usr/bin/env bash
# SPDX-License-Identifier: AGPL-3.0-or-later
# The Lean model of Pancake against HOL4's own semantics. backend/semantics/dnModelScript.sml is
# the model written again in HOL, and dnModelProofScript.sml proves it equal to panSem's evaluate
# on the subset; the prover is asked that the proof rests on no oracle. Every case of the state
# corpus, backend/semantics/states.txt, which the state lane holds equal to what the Lean model
# prints, is then run by panSem's evaluate and by the HOL model under EVAL, and every field each
# ends in is compared with the Lean model's (scripts/semantics_check.py): the second run is what
# ties the HOL model to the Lean one. Then once more with subtraction read as addition, which both
# have to show.
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
evaluated=(dnShowTheory.uo dnModelTheory.uo dnModelShowTheory.uo dnStatesTheory.uo dnModelStatesTheory.uo)
# evaluate DIR LOG OPTION TARGET...: the theories, built outside both pinned trees with one job, so
# that what they print is in LOG; OPTION is --defect or nothing.
evaluate() {
  local dir=$1 log=$2 option=$3
  shift 3
  rm -rf "$dir"
  mkdir -p "$dir"
  cp backend/semantics/Holmakefile backend/semantics/*Script.sml "$dir"
  python3 scripts/semantics_check.py write "$corpus" "$dir" ${option:+"$option"}
  holmake_gated "$dir" "$log" "$dir" 1 "$dir/dnModelStatesTheory.uo" --no_prereqs "$@"
}
evaluate "$root/build/semantics" "$root/build/semantics-eval.log" "" dnModelProofTheory.uo "${evaluated[@]}"
grep -qF "DN SEMANTICS: dn_sem_thm and dn_eval_thm carry no oracle" "$root/build/semantics-eval.log" ||
  refuse "the proof of dnModelProof did not report on its tags"
python3 scripts/semantics_check.py compare "$corpus" "$root/build/semantics-eval.log"
evaluate "$root/build/semantics-defect" "$root/build/semantics-defect.log" --defect "${evaluated[@]}"
python3 scripts/semantics_check.py compare "$corpus" "$root/build/semantics-defect.log" --expect-differences
