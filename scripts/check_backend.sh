#!/usr/bin/env bash
# Rebuild the curated optimization proof against locked source.
set -euo pipefail
cd "$(dirname "$0")/.."
python3 scripts/backend.py verify cakeml
python3 scripts/backend.py verify hol
export HOLDIR="$(pwd)/.deps/hol"
export CAKEMLDIR="$(pwd)/.deps/cakeml"
if [[ ! -x "$HOLDIR/bin/Holmake" ]]; then
  echo 'Build the pinned HOL tree first; see backend/README.md.' >&2
  exit 1
fi
cd "$CAKEMLDIR/pancake/proofs"
"$HOLDIR/bin/Holmake" -j "${DN_BUILD_JOBS:-2}" loop_liveProofTheory.uo
echo 'DN BACKEND: proof target built (not a compiler bootstrap or whole-program theorem)'
