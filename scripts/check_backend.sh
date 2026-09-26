#!/usr/bin/env bash
# SPDX-License-Identifier: AGPL-3.0-or-later
# Rebuild the Pancake proof chain against the locked source and the curated patch.
#
# The patch changes `shrink_def`, which the proofs below it use: `crep_to_loopProof`
# has `loop_liveProof` as an ancestor, `pan_to_wordProof` unfolds the clauses of
# `shrink_def`, and the compiler's correctness statement is `pan_to_targetProof`.
# Building only the optimization's own theory would leave a break further down
# invisible, so the default target is the end of that chain: from a clean tree
# that took 46 minutes on twelve jobs of a 16-core machine.
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

target="${DN_BACKEND_TARGET:-pan_to_targetProofTheory.uo}"
# The target is passed to Holmake as an argument, so an option here would be read
# as one: `DN_BACKEND_TARGET=--fast` must not turn every tactic into an oracle.
if [[ ! "$target" =~ ^[A-Za-z0-9_]+Theory\.uo$ ]]; then
  echo "DN BACKEND: DN_BACKEND_TARGET must name a theory object, not $target" >&2
  exit 2
fi
build_jobs="${DN_BUILD_JOBS:-2}"
if [[ ! "$build_jobs" =~ ^[1-9][0-9]*$ ]]; then
  echo "DN BACKEND: DN_BUILD_JOBS must be a positive number, not $build_jobs" >&2
  exit 2
fi
# Holmake adds CLINE_OPTIONS to its own options and passes POLY_CLINE_OPTIONS to every theory's
# prover process, so either could change what is built or run code the checks never see.
if [[ -n "${CLINE_OPTIONS:-}${POLY_CLINE_OPTIONS:-}" ]]; then
  echo "DN BACKEND: unset CLINE_OPTIONS and POLY_CLINE_OPTIONS" >&2
  exit 2
fi
python3 scripts/backend.py verify hol
HOLDIR="$(pwd)/.deps/hol"
CAKEMLDIR="$(pwd)/.deps/cakeml"
export HOLDIR CAKEMLDIR
if [[ ! -x "$HOLDIR/bin/Holmake" ]]; then
  echo 'Build the pinned HOL tree first; see backend/README.md.' >&2
  exit 1
fi
# The ML compiler is part of what the rebuilt proof rests on, so a prover built by an
# unrecorded one is refused rather than used.
python3 scripts/backend.py built-with hol
# Build outputs left from an earlier run would let Holmake decide the target is
# already up to date, so the proof would not be rebuilt against the patch. The
# tree is verified after the clean, because that check refuses a tree that still
# carries them.
git -C "$CAKEMLDIR" clean -fdXq
python3 scripts/backend.py verify cakeml

log="$root/build/backend-holmake.log"
mkdir -p "$(dirname "$log")"
cd "$CAKEMLDIR/pancake/proofs"
started=$(date +%s)
# No --fast (every tactic becomes an oracle) and no --noqof (a failed proof stops
# being fatal): either would produce a "built" theory that establishes nothing.
"$HOLDIR/bin/Holmake" -j "$build_jobs" "$target" 2>&1 | tee "$log"

# Holmake records a cheat, an oracle tag or a cache hit and exits successfully.
# Where it records them depends on the job count, so both places are read.
python3 "$root/scripts/check_holmake.py" --output "$log" --tree "$CAKEMLDIR" \
  --jobs "$build_jobs" --built "$CAKEMLDIR/pancake/proofs/$target" --since "$started"
if [[ "$target" == "pan_to_targetProofTheory.uo" ]]; then
  # What the log says about cheats is what Holmake chose to print. This asks the prover
  # instead, from a theory built outside both pinned trees against the one just produced.
  check="$root/build/tagcheck"
  rm -rf "$check"
  mkdir -p "$check"
  cp "$root/backend/tagcheck/Holmakefile" "$root/backend/tagcheck/dnTagCheckScript.sml" "$check"
  tag_log="$root/build/backend-tagcheck.log"
  started=$(date +%s)
  # One job: with more, Holmake writes each job's output to its own log and prints a status
  # word, and what this reads is what the script itself printed. --no_prereqs: the included
  # directory's own default target is a dozen proofs this run did not come for.
  (cd "$check" && "$HOLDIR/bin/Holmake" -j1 --no_prereqs dnTagCheckTheory.uo) 2>&1 | tee "$tag_log"
  python3 "$root/scripts/check_holmake.py" --output "$tag_log" --tree "$check" \
    --jobs 1 --built "$check/dnTagCheckTheory.uo" --since "$started"
  grep -q 'DN BACKEND: pan_to_target_compile_semantics carries no oracle' "$tag_log" ||
    { echo 'DN BACKEND: the tag check did not report on the theorem' >&2; exit 1; }
  echo 'DN BACKEND: the Pancake proof chain was rebuilt up to the compiler correctness theorem'
  echo 'DN BACKEND: this is not a compiler bootstrap; no executable was produced from this source'
else
  echo "DN BACKEND: $target built; this is a smoke run, not the compiler theorem"
fi
