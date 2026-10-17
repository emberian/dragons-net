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

# The files that decide what the checks do. The tests run code from the change in
# the same checkout as the scripts that run after them, so a test that rewrote one
# of those on disk would be checked by what it wrote; the tests stage compares this
# before and after. Bytecode caches are written by the tests themselves.
checkers() {
  git ls-files -z --cached --others --exclude-standard -- \
    scripts tests .github lakefile.lean lean-toolchain '*.toml' '*.json' ':!:*__pycache__*' \
    | xargs -0 -r sha256sum
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
    build) build ;;
    proofs) once check-proofs bash scripts/check.sh proofs-now ;;
    proofs-now) proofs ;;
    tests) tests ;;
    all) build; once check-proofs bash scripts/check.sh proofs-now; tests ;;
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
  python3 scripts/measured.py "$leanchecker" DN
  # The independent kernel checks the library's declarations and everything they use.
  mkdir -p build/proofs
  "$lean" --run scripts/Audit.lean --export-list >build/proofs/export-list
  mapfile -d '' -t args <build/proofs/export-list
  LEAN_SYSROOT=$prefix "$exporter" "${args[@]}" | "$nanoda" scripts/nanoda.json
  "$lean" --run scripts/Audit.lean --regressions 259
}

# Tests that run the built code, and the Rust crates.
tests() {
  local before module name
  before=$(checkers)
  # Each module of tests on its own, so that a change reruns only the modules that read it. The
  # tracer's own test runs untraced, since a traced process cannot trace another.
  for module in $(git ls-files --cached --others --exclude-standard 'tests/test_*.py'); do
    module=$(basename "$module")
    if [[ $module == test_once.py ]]; then
      python3 -m unittest discover -s tests -p "$module" -v
    else
      name=${module%.py}
      once "unit-${name//_/-}" python3 -m unittest discover -s tests -p "$module" -v
    fi
  done
  once clippy cargo clippy --locked --workspace --all-targets -- -D warnings
  # The models are a second workspace, and both configurations have to lint:
  # the loom code paths are compiled only under the cfg.
  once clippy-models cargo clippy --locked --manifest-path models/Cargo.toml --workspace --all-targets \
    -- -D warnings
  once clippy-models-loom env RUSTFLAGS='--cfg loom' cargo clippy --locked --manifest-path models/Cargo.toml \
    --workspace --all-targets -- -D warnings
  once clippy-loom env RUSTFLAGS='--cfg loom' cargo clippy --locked --workspace --all-targets -- -D warnings
  once cargo-test cargo test --locked --workspace
  once models python3 scripts/check_models.py
  # The states a run stops in, against an independent implementation of the same
  # clauses: the differential lanes compare computed values and never reach them.
  once states python3 scripts/state_check.py
  # The session model driven by a simulated host and judged by an independent reference.
  once session-model python3 scripts/session_check.py
  # The grammar of header fields, taken from the RFCs, against an independent ABNF library.
  once abnf python3 scripts/abnf_check.py
  # Which proto-articles a POST accepts and what it adds, against an independent reference.
  once article python3 scripts/article_check.py
  # The store's journal and the names of its files, against an independent reference.
  once journal python3 scripts/journal_check.py
  # The file system and what a crash may leave of it, against an independent reference.
  once fs python3 scripts/fs_check.py
  # How the store recovers when it starts, against an independent reference.
  once store python3 scripts/store_check.py
  # The store's program, every point of its runs held to what a crash may leave there.
  once runs python3 scripts/runs_check.py
  # Each source of native/ on its own, as the nightly CodeQL job builds it.
  once sources python3 scripts/compile_sources.py
  # The points of failure the host's test build carries, held to what its tests take of libfiu.
  once fiu python3 scripts/fiu_check.py
  # The host's side of the store, with a stand-in for the program.
  once host python3 scripts/host_check.py
  # shellcheck disable=SC2310,SC2312 # a failed snapshot compares unequal, which refuses
  if [[ "$(checkers)" != "$before" ]]; then
    echo 'check: the scripts, workflows or gate tests changed while the tests ran' >&2
    exit 1
  fi
}

main "$@"
