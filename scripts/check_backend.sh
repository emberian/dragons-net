#!/usr/bin/env bash
# SPDX-License-Identifier: AGPL-3.0-or-later
# Rebuild the Pancake proof chain against the locked source and the curated patch.
#
# The patch changes `shrink_def`, which the proofs below it use: `crep_to_loopProof`
# has `loop_liveProof` as an ancestor, `pan_to_wordProof` unfolds the clauses of
# `shrink_def`, and the compiler's correctness statement is `pan_to_targetProof`.
# Building only the optimization's own theory would leave a break further down
# invisible, so the default target is the end of that chain: from a clean tree
# that took 46 minutes on twelve jobs of a machine with 16 hardware threads.
#
# `DN_BACKEND_TARGET` selects a narrower target for a smoke run; the final line
# then says which target was built, because only the full chain re-establishes
# the compiler theorem, and only it produces the theorem the tag check reads.
set -euo pipefail
cd "$(dirname "$0")/.."
# A module in scripts/ with the name of a standard-library one would otherwise
# shadow it: Python puts the script's directory first on the path.
export PYTHONSAFEPATH=1
root="$(pwd)"
# The library is checked on its own; this script uses only its functions.
# shellcheck source=/dev/null
source scripts/backend_lane.sh
begin_lane BACKEND

target="${DN_BACKEND_TARGET:-pan_to_targetProofTheory.uo}"
# The target is passed to Holmake as an argument, so an option here would be read
# as one: `DN_BACKEND_TARGET=--fast` must not turn every tactic into an oracle.
[[ "$target" =~ ^[A-Za-z0-9_]+Theory\.uo$ ]] || refuse "DN_BACKEND_TARGET must name a theory object, not $target"
build_jobs=$(checked_jobs)
# Holmake adds CLINE_OPTIONS to its own options and passes POLY_CLINE_OPTIONS to every theory's
# prover process, so either could change what is built or run code the checks never see.
[[ -z "${CLINE_OPTIONS:-}${POLY_CLINE_OPTIONS:-}" ]] || refuse "unset CLINE_OPTIONS and POLY_CLINE_OPTIONS"
HOLDIR="$root/.deps/hol"
CAKEMLDIR="$root/.deps/cakeml"
export HOLDIR CAKEMLDIR
prepare_trees
use_holmake

mkdir -p build
# No --fast (every tactic becomes an oracle) and no --noqof (a failed proof stops
# being fatal): either would produce a "built" theory that establishes nothing.
holmake_gated "$CAKEMLDIR/pancake/proofs" "$root/build/backend-holmake.log" "$CAKEMLDIR" "$build_jobs" \
  "$CAKEMLDIR/pancake/proofs/$target" "$target"
if [[ "$target" == "pan_to_targetProofTheory.uo" ]]; then
  tag_check "$root/backend/tagcheck" "$root/build/tagcheck" "$root/build/backend-tagcheck.log" dnTagCheck
  echo 'DN BACKEND: the Pancake proof chain was rebuilt up to the compiler correctness theorem'
  echo 'DN BACKEND: this is not a compiler bootstrap; no executable was produced from this source'
else
  echo "DN BACKEND: $target built; this is a smoke run, not the compiler theorem"
fi
