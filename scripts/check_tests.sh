#!/usr/bin/env bash
# SPDX-License-Identifier: AGPL-3.0-or-later
# The tests stage of scripts/check.sh, apart from the build and the proofs, whose inputs it is not.
set -euo pipefail
export PYTHONSAFEPATH=1

# A check that passed on the inputs it read is not run again (scripts/once.py); DN_ONCE=none runs it
# untraced.
once() {
  local name=$1
  shift
  if [[ ${DN_ONCE:-} == none ]]; then "$@"; else python3 scripts/once.py run "$name" -- "$@"; fi
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

# Tests that run the built code, and the Rust crates, in groups that need nothing of each other.
# CI runs each group as a job of its own; given no group, they run here DN_PARALLEL at a time, each
# group's output kept in build/evidence and shown whole once it is done.
TEST_GROUPS=(unit rust session models host runs)
group() {
  local module name
  tools "$1"
  case $1 in
    unit)
      # Each module of tests on its own, so that a change reruns only the modules that read it. The
      # tracer's own test runs untraced, since a traced process cannot trace another.
      for module in $(git ls-files --cached --others --exclude-standard 'tests/test_*.py'); do
        name=$(basename "$module" .py)
        if [[ $name == test_once ]]; then
          python3 scripts/unit.py "$name"
        else
          once "unit-${name//_/-}" python3 scripts/unit.py "$name"
        fi
      done
      ;;
    rust)
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
      ;;
    session)
      # The session model driven by a simulated host and judged by an independent reference.
      once session-model python3 scripts/session_check.py
      ;;
    models)
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
      ;;
    runs)
      # The store's program, every point of its runs held to what a crash may leave there.
      once runs python3 scripts/runs_check.py
      ;;
    host)
      # Each source of native/ on its own, as the nightly CodeQL job builds it.
      once sources python3 scripts/compile_sources.py
      # The points of failure the host's test build carries, held to what its tests take of libfiu.
      once fiu python3 scripts/fiu_check.py
      # The host's side of the store, with a stand-in for the program.
      once host python3 scripts/host_check.py
      ;;
    *)
      echo "check.sh: no group of tests named '$1'; the groups are ${TEST_GROUPS[*]}" >&2
      exit 2
      ;;
  esac
}

# The pinned tools and wheels a group's checks take, put in place first and untraced: a check that
# installed one would read what it wrote, and so would run every time.
tools() {
  case $1 in
    unit) python3 scripts/bootstrap_tool.py lean4export && python3 scripts/bootstrap_tool.py nanoda ;;
    session) python3 scripts/wheels.py scripts/requirements-tests.txt ;;
    models) python3 scripts/bootstrap_tool.py abnfgen && python3 scripts/wheels.py scripts/requirements-tests.txt ;;
    host) python3 scripts/bootstrap_tool.py libfiu ;;
  esac >/dev/null
}

main() {
  local before g failed=0 started=0
  cd "$(dirname "$0")/.."
  before=$(checkers)
  if (($#)); then
    for g; do group "$g"; done
  elif ((${DN_PARALLEL:-1} < 2)); then
    for g in "${TEST_GROUPS[@]}"; do group "$g"; done
  else
    # An interrupt ends every group running.
    trap 'trap - INT TERM; kill 0' INT TERM
    mkdir -p build/evidence
    for g in "${TEST_GROUPS[@]}"; do
      # Once as many run as may, each next one waits for one of them to end.
      if ((started >= ${DN_PARALLEL:-1})); then wait -n || true; fi
      started=$((started + 1))
      (
        set +e
        (set -e; group "$g") >"build/evidence/tests-$g.log" 2>&1
        echo $? >"build/evidence/tests-$g.status"
      ) &
    done
    wait
    for g in "${TEST_GROUPS[@]}"; do
      cat "build/evidence/tests-$g.log"
      if [[ $(<"build/evidence/tests-$g.status") != 0 ]]; then
        echo "check: the group of tests $g failed" >&2
        failed=1
      fi
    done
    ((failed == 0)) || exit 1
  fi
  # shellcheck disable=SC2310,SC2312 # a failed snapshot compares unequal, which refuses
  if [[ "$(checkers)" != "$before" ]]; then
    echo 'check: the scripts, workflows or gate tests changed while the tests ran' >&2
    exit 1
  fi
}

main "$@"
