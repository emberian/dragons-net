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
  # --wfail: a warning fails the build. Lake replays a module's stored log, so
  # this holds on a warm cache as well as on a fresh checkout.
  lake build --wfail DN dn-compiler
  if [[ "$(snapshot)" != "$before" ]]; then
    echo 'check: repository files changed during the source gate or the build' >&2
    exit 1
  fi
}

# Kernel re-checks and proof audit; no built code runs before the audit's static checks pass.
# The checkers come from the toolchain and the lock, never from PATH, which Lake prefixes with
# .lake/build/bin.
proofs() {
  local leanchecker lean prefix exporter nanoda args
  leanchecker=$(elan which leanchecker)
  lean=$(elan which lean)
  prefix=$("$lean" --print-prefix)
  exporter=$(python3 scripts/bootstrap_tool.py lean4export)
  nanoda=$(python3 scripts/bootstrap_tool.py nanoda)
  # Toolchain modules come first, and a panic stops a checker instead of returning a default.
  local -x LEAN_PATH="$prefix/lib/lean:.lake/build/lib/lean" LEAN_ABORT_ON_PANIC=1
  python3 scripts/check_structure.py outputs
  "$leanchecker" DN
  # The independent kernel checks the library's declarations and everything they use.
  mkdir -p build/proofs
  "$lean" --run scripts/Audit.lean --export-list >build/proofs/export-list
  mapfile -d '' -t args <build/proofs/export-list
  LEAN_SYSROOT=$prefix "$exporter" "${args[@]}" | "$nanoda" scripts/nanoda.json
  "$lean" --run scripts/Audit.lean --regressions 79
}

# Tests that run the built code, and the Rust crates.
tests() {
  python3 -m unittest discover -s tests -v
  cargo clippy --locked --workspace --all-targets -- -D warnings
  # The models are a second workspace, and both configurations have to lint:
  # the loom code paths are compiled only under the cfg.
  cargo clippy --locked --manifest-path models/Cargo.toml --workspace --all-targets \
    -- -D warnings
  RUSTFLAGS='--cfg loom' cargo clippy --locked --manifest-path models/Cargo.toml \
    --workspace --all-targets -- -D warnings
  RUSTFLAGS='--cfg loom' cargo clippy --locked --workspace --all-targets -- -D warnings
  cargo test --locked --workspace
  python3 scripts/check_models.py
}

main "$@"
