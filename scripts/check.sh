#!/usr/bin/env bash
set -euo pipefail

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
    build | proofs | tests) "$1" ;;
    all) build; proofs; tests ;;
    *)
      echo 'usage: check.sh [guard | build | proofs | tests]' >&2
      exit 2
      ;;
  esac
  if [[ ${1:-all} == all ]]; then
    echo 'DN CHECK: PASS (Lean/model + host primitives; native/backend checks are separate)'
  else
    echo "DN CHECK $1: PASS"
  fi
}

# Source gate and build.
build() {
  local before
  before=$(snapshot)
  python3 scripts/check_structure.py
  lake build DN dn-compiler
  if [[ "$(snapshot)" != "$before" ]]; then
    echo 'check: repository files changed during the source gate or the build' >&2
    exit 1
  fi
}

# Kernel re-check and proof audit; no built code runs before the audit's static checks pass.
# The checkers come from the toolchain, never from PATH, which Lake prefixes with .lake/build/bin.
proofs() {
  local leanchecker lean path
  leanchecker=$(elan which leanchecker)
  lean=$(elan which lean)
  path="$("$lean" --print-prefix)/lib/lean:.lake/build/lib/lean"
  LEAN_PATH=$path "$leanchecker" DN
  LEAN_PATH=$path "$lean" --run scripts/Audit.lean --regressions 434
}

# Tests that run the built code, and the Rust crates.
tests() {
  python3 -m unittest discover -s tests -v
  cargo clippy --locked --workspace --all-targets -- -D warnings
  cargo test --locked --workspace
  python3 scripts/check_models.py
}

main "$@"
