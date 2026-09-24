#!/usr/bin/env bash
# SPDX-License-Identifier: AGPL-3.0-or-later
set -euo pipefail
# A module in scripts/ with the name of a standard-library one would otherwise
# shadow it: Python puts the script's directory first on the path. It does the
# same for tests/, which this flag does not cover, so a gate test forbids the
# names there instead.
export PYTHONSAFEPATH=1

# Checks that need no build: workflows, shell, Python, Rust formatting, secrets, and the
# spelling and whitespace of documentation. Every tool is pinned by digest in
# tools.lock.json or scripts/requirements-lint.txt.
main() {
  cd "$(dirname "$0")/.."
  bash scripts/check.sh guard
  local venv=.deps/lint pins
  pins=$(sha256sum scripts/requirements-lint.txt)
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
  local sources=(':!:migration/**' ':!:rfcs/**')

  "$actionlint" -shellcheck "$shellcheck"
  # Online audits, such as impostor commits, need a token; offline ones always run.
  local online=(--offline)
  [[ -z ${GH_TOKEN:-} ]] || online=()
  "$zizmor" "${online[@]}" .github/workflows
  # The optional checks are the ones that matter for scripts whose correctness rests on
  # `set -euo pipefail`: a command whose failure is masked, or an exit status swallowed by the
  # assignment it is written into, turns a failed check into a passing one.
  git ls-files -z '*.sh' "${sources[@]}" | xargs -0 "$shellcheck" \
    --enable=check-set-e-suppressed,check-extra-masked-returns,quote-safe-variables \
    --enable=avoid-nullary-conditions,check-unassigned-uppercase
  "$venv/bin/ruff" check scripts tests
  # A checker that cannot fire, a comparison that is always false and a name that may be unbound
  # all read as "this passed" from the outside, so they are errors here.
  "$venv/bin/mypy" --strict --python-version 3.12 --warn-unreachable --strict-equality \
    --enable-error-code redundant-expr --enable-error-code possibly-undefined \
    --enable-error-code truthy-bool --enable-error-code ignore-without-code \
    scripts tests
  "$gitleaks" git --no-banner --redact --log-level warn .
  git ls-files -z '*.md' "${sources[@]}" | xargs -0 "$typos"
  git ls-files -z "${sources[@]}" | xargs -0 "$editorconfig"
  cargo fmt --all -- --check
  cargo fmt --manifest-path models/Cargo.toml --all -- --check
  "$deny" --locked check
  "$deny" --locked --manifest-path models/Cargo.toml check
  # A dependency nobody uses is a dependency nobody reads, and it still ships its advisories.
  # It reports `[dependencies]` only — dev and target-scoped entries are invisible to it, and
  # every dependency here is one of those today, so this guards what gets added next. Our
  # crates only: the preserved snapshot carries manifests of its own and is not built here.
  "$machete" crates models
  echo 'DN LINT: PASS'
}

main "$@"
