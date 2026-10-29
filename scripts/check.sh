#!/usr/bin/env bash
# SPDX-License-Identifier: AGPL-3.0-or-later
set -euo pipefail
# A module in scripts/ with the name of a standard-library one would otherwise
# shadow it: Python puts the script's directory first on the path. It does the
# same for tests/, which this flag does not cover, so a gate test forbids the
# names there instead.
export PYTHONSAFEPATH=1

# The whole script is parsed before it runs, and the build must not change any
# repository file, so it cannot alter the checks that follow it.
snapshot() {
  local skip=(\( -path ./.git -o -path ./.lake -o -path ./build \) -prune -o)
  find . "${skip[@]}" -type f -print0 | sort -z | xargs -0 sha256sum
  find . "${skip[@]}" -type l -printf '%p -> %l\n' | sort
}

# Lake and Python reuse build outputs that match the sources, so the checks may use only
# outputs of this run: none may be committed, and Lake may not fetch them from its cache.
tracked_outputs() {
  local prefix
  prefix=$(git rev-parse --show-prefix)
  if [[ -n "$prefix" ]]; then
    echo 'check: run from the root of its own git checkout' >&2
    return 1
  fi
  git --icase-pathspecs ls-files -- .lake .deps build target models/target \
    '*.olean' '*.olean.*' '*.ilean' '*.trace' '*.hash' '*.pyc'
}

main() {
  local stage=${1:-all}
  cd "$(dirname "$0")/.."
  export LEAN_NUM_THREADS="${LEAN_NUM_THREADS:-4}" LAKE_ARTIFACT_CACHE=false
  local tracked
  tracked=$(tracked_outputs)
  if [[ -n "$tracked" ]]; then
    echo 'check: build outputs are tracked by git' >&2
    exit 1
  fi
  case "${1:-all}" in
    guard) ;;
    build) build ;;
    proofs) once check-proofs bash scripts/check.sh proofs-now ;;
    proofs-now) shift; proofs "$@" ;;
    tests) shift; bash scripts/check_tests.sh "$@" ;;
    all) build; once check-proofs bash scripts/check.sh proofs-now; bash scripts/check_tests.sh ;;
    *)
      echo 'usage: check.sh [guard | build | proofs | tests [group...]]' >&2
      exit 2
      ;;
  esac
  if [[ $stage == all ]]; then
    echo 'DN CHECK: PASS (Lean/model + host primitives; native/backend checks are separate)'
  else
    echo "DN CHECK $stage: PASS"
  fi
}

# A check that passed on the inputs it read is not run again (scripts/once.py); DN_ONCE=none runs it
# untraced, as CI does where a job's inputs decide instead. The build always runs: Lake rebuilds only
# what changed, and the outputs must match the sources.
once() {
  local name=$1
  shift
  if [[ ${DN_ONCE:-} == none ]]; then "$@"; else python3 scripts/once.py run "$name" -- "$@"; fi
}

# Source gate and build.
build() {
  local before
  before=$(snapshot)
  once check-gate python3 scripts/check_structure.py
  # --wfail: a warning fails the build. Lake replays a module's stored log, so
  # this holds on a warm cache as well as on a fresh checkout. The kernel's runs of the
  # safety analyses make most of its cost, which the log shows as it grows.
  python3 scripts/measured.py lake build --wfail DN dn-compiler
  # shellcheck disable=SC2310,SC2312 # a failed snapshot compares unequal, which refuses
  if [[ "$(snapshot)" != "$before" ]]; then
    echo 'check: repository files changed during the source gate or the build' >&2
    exit 1
  fi
}

# Kernel re-checks and proof audit; no built code runs before the audit's static checks pass.
# The checkers come from the toolchain and the lock, never from PATH, which Lake prefixes with
# .lake/build/bin. Given a part, only that one runs: Lean's own checker, or the independent kernel
# and the audit, which CI runs beside each other.
proofs() {
  local part=${1:-} leanchecker lean prefix exporter nanoda args
  if [[ ! $part =~ ^(|leanchecker|nanoda)$ ]]; then
    echo "check.sh: no part of the proofs named '$part'; the parts are leanchecker and nanoda" >&2
    exit 2
  fi
  leanchecker=$(elan which leanchecker)
  lean=$(elan which lean)
  prefix=$("$lean" --print-prefix)
  if [[ $part != leanchecker ]]; then
    exporter=$(python3 scripts/bootstrap_tool.py lean4export)
    nanoda=$(python3 scripts/bootstrap_tool.py nanoda)
  fi
  # Toolchain modules come first, and a panic stops a checker instead of returning a default.
  local -x LEAN_PATH="$prefix/lib/lean:.lake/build/lib/lean" LEAN_ABORT_ON_PANIC=1
  python3 scripts/check_structure.py outputs
  if [[ $part != nanoda ]]; then
    python3 scripts/measured.py python3 scripts/leanchecked.py "$leanchecker"
  fi
  if [[ $part != leanchecker ]]; then
    # The independent kernel checks the library's declarations and everything they use.
    mkdir -p build/proofs
    "$lean" --run scripts/Audit.lean --export-list >build/proofs/export-list
    mapfile -d '' -t args <build/proofs/export-list
    LEAN_SYSROOT=$prefix "$exporter" "${args[@]}" | "$nanoda" scripts/nanoda.json
    "$lean" --run scripts/Audit.lean --regressions 264
  fi
}

main "$@"
