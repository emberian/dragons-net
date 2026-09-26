#!/usr/bin/env bash
# SPDX-License-Identifier: AGPL-3.0-or-later
# Build the CakeML compiler from the pinned, patched source, and record what it is.
#
# Every native lane here runs a digest-pinned release binary built from a different revision,
# so nothing they show says the curated patch is in the compiler that ran. This builds `cake`
# from the revision in backend/lock.json plus that patch, which is the only way to say it.
#
# What it produces is the binary and a record of how it was made, not a theorem about the
# binary. It takes hours and tens of gigabytes, which does not fit a hosted runner; see
# backend/README.md for what one run took and what the result does and does not establish.
set -euo pipefail
cd "$(dirname "$0")/.."
export PYTHONSAFEPATH=1
root="$(pwd)"
out="$root/build/bootstrap"
# First, so that a run which stops early leaves no record from an earlier one behind.
rm -rf "$out"
mkdir -p "$out"

refuse() {
  echo "DN BOOTSTRAP: $*" >&2
  exit 2
}
build_jobs="${DN_BUILD_JOBS:-2}"
minheap="${DN_POLY_MINHEAP:-8G}"
# Both end up on the prover's command line, where anything else would be read as an option.
[[ "$build_jobs" =~ ^[1-9][0-9]*$ ]] || refuse "DN_BUILD_JOBS must be a positive number, not '$build_jobs'"
[[ "$minheap" =~ ^[1-9][0-9]*[KMGkmg]?$ ]] || refuse "DN_POLY_MINHEAP must be a size such as 8G, not '$minheap'"
# Holmake adds CLINE_OPTIONS to its own options; nothing this script did not set may reach it.
[[ -z "${CLINE_OPTIONS:-}" ]] || refuse "CLINE_OPTIONS is set; unset it"
platform=$(uname -sm)
[[ "$platform" == "Linux x86_64" ]] || refuse "the compiler is built on Linux x86-64 only"

python3 scripts/backend.py verify hol
# The compiler is built by the prover, so the prover has to be the pinned one.
python3 scripts/backend.py built-with hol
HOLDIR="$root/.deps/hol"
CAKEMLDIR="$root/.deps/cakeml"
export HOLDIR CAKEMLDIR
# Anything left from an earlier build could let Holmake reuse a theory derived from the
# unpatched source. The saved Poly/ML heap under cv_translator is the one that would do it
# without a word, so the tree is cleaned before the pins are checked.
git -C "$CAKEMLDIR" clean -fdXq
python3 scripts/backend.py verify cakeml

# Poly/ML sizes its heap from GC timing. While a process grows fast the new limit can land on the
# space already in use, and an object larger than one heap segment then ends the build with "Run out
# of store" although most of the heap is free. A floor keeps the limit above the space in use.
export POLY_CLINE_OPTIONS="--minheap $minheap"
# Holmake runs on Poly/ML too and has hit the same limit, so it gets a floor of its own; the
# runtime takes the option from its command line before Holmake sees the arguments.
holmake=("$HOLDIR/bin/Holmake" --minheap 2G)
target="$CAKEMLDIR/compiler/bootstrap/compilation/x64/64"
log="$out/holmake.log"
started=$(date +%s)
# `cake.S` is the compiler's machine code, written by the proof of `compiler64_compiled`; the
# theory object is what the tag check below loads. No --fast (it replaces tactics with cheats)
# and no --noqof (it carries on past a failure); --no-cache and --qof are the pinned Holmake's
# defaults, spelled out all the same.
(cd "$target" && "${holmake[@]}" -j "$build_jobs" --no-cache --qof cake.S x64BootstrapTheory.uo) \
  2>&1 | tee "$log"
python3 "$root/scripts/check_holmake.py" --output "$log" --tree "$CAKEMLDIR" \
  --jobs "$build_jobs" --built "$target/cake.S" --since "$started"

# What the log says about cheats is what Holmake chose to print. This asks the prover instead,
# from a theory built outside both pinned trees, as the proof lane does for its theorem.
check="$out/tagcheck"
mkdir -p "$check"
cp "$root/backend/bootstrap-tagcheck/Holmakefile" \
  "$root/backend/bootstrap-tagcheck/dnBootstrapTagCheckScript.sml" "$check"
tag_log="$out/tagcheck.log"
tag_started=$(date +%s)
# One job and --no_prereqs, for the reasons given in scripts/check_backend.sh.
(cd "$check" && "${holmake[@]}" -j1 --no_prereqs dnBootstrapTagCheckTheory.uo) 2>&1 | tee "$tag_log"
python3 "$root/scripts/check_holmake.py" --output "$tag_log" --tree "$check" \
  --jobs 1 --built "$check/dnBootstrapTagCheckTheory.uo" --since "$tag_started"
grep -q 'DN BOOTSTRAP: compiler64_compiled carries no oracle' "$tag_log" || {
  echo 'DN BOOTSTRAP: the tag check did not report on the theorem' >&2
  exit 1
}

# Linking is an ordinary C toolchain run, covered by no theorem; the result is checked instead.
finished=$(date +%s)
python3 scripts/backend.py package-bootstrap --seconds "$(( finished - started ))" --jobs "$build_jobs"
echo "DN BOOTSTRAP: built $out/cake from the patched source"
echo 'DN BOOTSTRAP: the binary carries the patch; no theorem here says the binary is correct'
