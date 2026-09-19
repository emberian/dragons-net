#!/usr/bin/env bash
set -euo pipefail

# The whole script is parsed before it runs, and the build must not change any
# repository file, so it cannot alter the checks that follow it.
snapshot() {
  find . \( -path ./.git -o -path ./.lake -o -path ./build \) -prune -o ! -type d -print0 |
    sort -z | xargs -0 sha256sum
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
  local tracked before
  tracked=$(tracked_outputs)
  if [[ -n "$tracked" ]]; then
    echo 'check: build outputs are tracked by git' >&2
    exit 1
  fi
  before=$(snapshot)
  python3 scripts/check_structure.py
  lake build DN dn-compiler
  if [[ "$(snapshot)" != "$before" ]]; then
    echo 'check: repository files changed during the source gate or the build' >&2
    exit 1
  fi
  lake env leanchecker DN
  lake env lean --run scripts/Audit.lean --regressions 434
  python3 -m unittest discover -s tests -v
  cargo fmt --all -- --check
  cargo clippy --locked --workspace --all-targets -- -D warnings
  cargo test --locked --workspace
  python3 scripts/check_models.py
  echo 'DN CHECK: PASS (Lean/model + host primitives; native/backend checks are separate)'
}

main "$@"
