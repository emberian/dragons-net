#!/usr/bin/env bash
# SPDX-License-Identifier: AGPL-3.0-or-later
set -euo pipefail
# A module in scripts/ with the name of a standard-library one would otherwise
# shadow it: Python puts the script's directory first on the path. It does the
# same for tests/, which this flag does not cover, so a gate test forbids the
# names there instead.
export PYTHONSAFEPATH=1

# A check that passed on the inputs it read is not run again (scripts/once.py); DN_ONCE=none runs it
# untraced. Each linter is a check of its own, so that a change runs again only those that read it.
once() {
  local name=$1
  shift
  if [[ ${DN_ONCE:-} == none ]]; then "$@"; else python3 scripts/once.py run "$name" -- "$@"; fi
}

# The files git tracks that the pathspecs after the first word name, into the array it names.
tracked() {
  local -n into=$1
  shift
  mkdir -p build
  git ls-files -z "$@" >build/lint-files
  # shellcheck disable=SC2034 # the caller's array
  mapfile -d '' -t into <build/lint-files
}

# Checks that need no build: workflows, shell, Python, Rust formatting, secrets, and the
# spelling and whitespace of documentation. Every tool is pinned by digest in
# tools.lock.json or scripts/requirements-lint.txt.
main() {
  cd "$(dirname "$0")/.."
  bash scripts/check.sh guard
  local venv=.deps/lint pins
  # The venv is made again when the pins or the Python it is made from change.
  pins=$(sha256sum scripts/requirements-lint.txt && python3 --version)
  # shellcheck disable=SC2312 # a failed read compares unequal, which rebuilds the venv
  if [[ ! -f $venv/pins || "$(cat "$venv/pins")" != "$pins" ]]; then
    rm -rf "$venv"
    python3 -m venv "$venv"
    "$venv/bin/pip" install --quiet --disable-pip-version-check --require-hashes --no-deps \
      --only-binary=:all: -r scripts/requirements-lint.txt
    echo "$pins" >"$venv/pins"
  fi
  local actionlint zizmor shellcheck gitleaks typos editorconfig deny machete
  actionlint=$(python3 -P scripts/bootstrap_tool.py actionlint)
  zizmor=$(python3 -P scripts/bootstrap_tool.py zizmor)
  shellcheck=$(python3 -P scripts/bootstrap_tool.py shellcheck)
  gitleaks=$(python3 -P scripts/bootstrap_tool.py gitleaks)
  typos=$(python3 -P scripts/bootstrap_tool.py typos)
  editorconfig=$(python3 -P scripts/bootstrap_tool.py editorconfig-checker)
  deny=$(python3 -P scripts/bootstrap_tool.py cargo-deny)
  machete=$(python3 -P scripts/bootstrap_tool.py cargo-machete)
  # The preserved snapshot, the RFCs, INN's test articles and SipHash's vectors are kept as their
  # sources have them.
  local sources=(':!:migration/**' ':!:rfcs/**' ':!:tests/corpus/inn-articles/**'
    ':!:tests/corpus/siphash/**')

  local shells docs files prose commit
  tracked shells '*.sh' "${sources[@]}"
  tracked docs '*.md' "${sources[@]}"
  tracked files "${sources[@]}"
  # Prose stays short. Decisions and reviews are records, kept as written; the files after them have
  # not been brought to the limits yet, and leave this list once they are.
  tracked prose '*.md' ':!:migration/' ':!:docs/decisions/' ':!:docs/reviews/' ':!:AGENTS.md' \
    ':!:CONTRIBUTING.md' ':!:SECURITY.md' ':!:backend/README.md' ':!:docs/architecture.md' ':!:docs/echo.md' \
    ':!:docs/handoff.md' ':!:docs/nntp.md' ':!:docs/pancake-semantics.md' ':!:docs/porting-risks.md' \
    ':!:docs/project.md' ':!:models/README.md'

  once lint-actionlint "$actionlint" -shellcheck "$shellcheck"
  # Online audits, such as impostor commits, need a token; offline ones always run. The answers of
  # the network change with nothing here changed: the nightly run asks them again.
  local online=(--offline)
  [[ -z ${GH_TOKEN:-} ]] || online=()
  once lint-zizmor "$zizmor" "${online[@]}" .github/workflows
  # The optional checks are the ones that matter for scripts whose correctness rests on
  # `set -euo pipefail`: a command whose failure is masked, or an exit status swallowed by the
  # assignment it is written into, turns a failed check into a passing one.
  once lint-shellcheck "$shellcheck" \
    --enable=check-set-e-suppressed,check-extra-masked-returns,quote-safe-variables \
    --enable=avoid-nullary-conditions,check-unassigned-uppercase "${shells[@]}"
  # Without caches: a check that read what it wrote would run every time (scripts/once.py).
  once lint-ruff "$venv/bin/ruff" check --no-cache scripts tests
  # A checker that cannot fire, a comparison that is always false and a name that may be unbound
  # all read as "this passed" from the outside, so they are errors here.
  once lint-mypy "$venv/bin/mypy" --strict --python-version 3.12 --warn-unreachable --strict-equality \
    --enable-error-code redundant-expr --enable-error-code possibly-undefined \
    --enable-error-code truthy-bool --enable-error-code ignore-without-code \
    --cache-dir=/dev/null scripts tests
  # Each commit once: those the default branch has were read before they reached it, a push to it
  # names those it brings, and `all` is every one (DN_COMMITS_FROM), as is a push whose commit before
  # is gone, forced. A merge is read against its first parent, its resolutions among what it changes.
  local default=origin/${DN_DEFAULT_BRANCH:-main} from=${DN_COMMITS_FROM:-} range commits
  git rev-parse -q --verify "$default^{commit}" >/dev/null || default=${default#origin/}
  if [[ $from == all ]] || { [[ -n $from ]] && ! git cat-file -e "$from^{commit}" 2>/dev/null; }; then
    range=HEAD
  else
    [[ -n $from ]] || from=$(git merge-base HEAD "$default")
    range=$from..HEAD
  fi
  commits=$(git rev-list "$range")
  for commit in $commits; do
    once "lint-gitleaks-$commit" "$gitleaks" git --no-banner --redact --log-level warn \
      --log-opts="-m --first-parent $commit^!" .
  done
  once lint-typos "$typos" "${docs[@]}"
  once lint-editorconfig "$editorconfig" "${files[@]}"
  once lint-prose python3 -P scripts/check_prose.py "${prose[@]}"
  # Cargo here keeps a cache of its own: the build rewrites the shared one under other flags, which
  # would change what this read and run it again (scripts/once.py).
  local -x CARGO_TARGET_DIR=build/lint-target
  once lint-fmt cargo fmt --all -- --check
  once lint-fmt-models cargo fmt --manifest-path models/Cargo.toml --all -- --check
  # The advisories are fetched first, untraced: a check that wrote what it read would run every time.
  # New ones make it run again.
  "$deny" --locked fetch
  "$deny" --locked --manifest-path models/Cargo.toml fetch
  once lint-deny "$deny" --locked --offline check
  once lint-deny-models "$deny" --locked --offline --manifest-path models/Cargo.toml check
  # A dependency nobody uses is a dependency nobody reads, and it still ships its advisories.
  # It reports `[dependencies]` only — dev and target-scoped entries are invisible to it, and
  # every dependency here is one of those today, so this guards what gets added next. Our
  # crates only: the preserved snapshot carries manifests of its own and is not built here.
  once lint-machete "$machete" crates models
  echo 'DN LINT: PASS'
}

main "$@"
