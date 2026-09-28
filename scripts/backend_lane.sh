# shellcheck shell=bash
# SPDX-License-Identifier: AGPL-3.0-or-later
# What the two backend lanes share, sourced by check_backend.sh and bootstrap_cake.sh. A lane
# names itself with `begin_lane`, sets `root` to the repository and HOLDIR and CAKEMLDIR to the
# pinned trees, and says how Holmake is run with `use_holmake` once the trees are prepared.
# shellcheck disable=SC2154 # root, HOLDIR and CAKEMLDIR are the sourcing lane's
# The lanes run under these options, and what follows relies on them.
set -euo pipefail

# The word the lane's messages start with.
begin_lane() {
  lane=$1
}

refuse() {
  echo "DN $lane: $*" >&2
  exit 2
}

# The job count from DN_BUILD_JOBS. It ends up on the prover's command line, where anything else
# would be read as an option.
checked_jobs() {
  local jobs="${DN_BUILD_JOBS:-2}"
  [[ "$jobs" =~ ^[1-9][0-9]*$ ]] || refuse "DN_BUILD_JOBS must be a positive number, not '$jobs'"
  echo "$jobs"
}

# The pinned prover, built by the pinned Poly/ML, and the CakeML tree with every build output
# removed and then checked against its pin.
prepare_trees() {
  python3 "$root/scripts/backend.py" verify hol
  [[ -x "$HOLDIR/bin/Holmake" ]] || refuse 'build the pinned HOL tree first; see backend/README.md'
  # The ML compiler is part of what the rebuilt proof rests on, so a prover built by an
  # unrecorded one is refused rather than used.
  python3 "$root/scripts/backend.py" built-with hol
  # Anything left from an earlier build could let Holmake decide a target is already built, or
  # reuse a theory derived from the unpatched source; the saved Poly/ML heap under
  # cv_translator would do it without a word. The tree is checked after the clean, because the
  # check refuses a tree that still carries them.
  git -C "$CAKEMLDIR" clean -fdXq
  python3 "$root/scripts/backend.py" verify cakeml
}

# Holmake with OPTIONS before the arguments each run adds.
use_holmake() {
  holmake=("$HOLDIR/bin/Holmake" "$@")
}

# holmake_gated DIR LOG TREE JOBS BUILT ARGS...: run Holmake in DIR with its output in LOG, then
# hold the run to what a real build leaves. Holmake records a cheat, an oracle tag or a cache hit
# and exits successfully, and where it records them depends on the job count, so check_holmake.py
# reads both the log and TREE, and requires BUILT to be newer than the start.
holmake_gated() {
  local dir=$1 log=$2 tree=$3 jobs=$4 built=$5 started
  shift 5
  started=$(date +%s)
  (cd "$dir" && "${holmake[@]}" -j "$jobs" "$@") 2>&1 | tee "$log"
  python3 "$root/scripts/check_holmake.py" --output "$log" --tree "$tree" --jobs "$jobs" \
    --built "$built" --since "$started"
}

# tag_check SOURCES DIR LOG THEORY: build THEORY from SOURCES in a fresh DIR outside both pinned
# trees, against what was just built, and require the sentence its script prints. What the log
# of the build says about cheats is what Holmake chose to print; this asks the prover. One job:
# with more, Holmake writes each job's output to its own log and prints a status word, and what
# this reads is what the script itself printed. --no_prereqs: the included directory's own
# default target is a dozen proofs the run did not come for.
tag_check() {
  local sources=$1 dir=$2 log=$3 theory=$4 wanted
  wanted=$(sed -n 's/.*print "\([^"]*\)\\n".*/\1/p' "$sources/${theory}Script.sml")
  [[ -n "$wanted" ]] || refuse "$sources/${theory}Script.sml prints no sentence to check for"
  rm -rf "$dir"
  mkdir -p "$dir"
  cp "$sources/Holmakefile" "$sources/${theory}Script.sml" "$dir"
  holmake_gated "$dir" "$log" "$dir" 1 "$dir/${theory}Theory.uo" --no_prereqs "${theory}Theory.uo"
  grep -qF "$wanted" "$log" || {
    echo "DN $lane: the tag check did not report on the theorem" >&2
    exit 1
  }
}
