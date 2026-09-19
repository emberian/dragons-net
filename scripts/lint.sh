#!/usr/bin/env bash
set -euo pipefail

# Checks that need no build: workflows, shell, Python, Rust formatting, secrets, and the
# spelling and whitespace of documentation. Every tool is pinned by digest in
# tools.lock.json or scripts/requirements-lint.txt.
main() {
  cd "$(dirname "$0")/.."
  bash scripts/check.sh guard
  local venv=.deps/lint pins
  pins=$(sha256sum scripts/requirements-lint.txt)
  if [[ ! -f $venv/pins || "$(cat "$venv/pins")" != "$pins" ]]; then
    rm -rf "$venv"
    python3 -m venv "$venv"
    "$venv/bin/pip" install --quiet --disable-pip-version-check --require-hashes --no-deps \
      --only-binary=:all: -r scripts/requirements-lint.txt
    echo "$pins" >"$venv/pins"
  fi
  local actionlint zizmor shellcheck gitleaks typos editorconfig deny
  actionlint=$(python3 -P scripts/bootstrap_tool.py actionlint)
  zizmor=$(python3 -P scripts/bootstrap_tool.py zizmor)
  shellcheck=$(python3 -P scripts/bootstrap_tool.py shellcheck)
  gitleaks=$(python3 -P scripts/bootstrap_tool.py gitleaks)
  typos=$(python3 -P scripts/bootstrap_tool.py typos)
  editorconfig=$(python3 -P scripts/bootstrap_tool.py editorconfig-checker)
  deny=$(python3 -P scripts/bootstrap_tool.py cargo-deny)
  local sources=(':!:migration/**' ':!:rfcs/**')

  "$actionlint" -shellcheck "$shellcheck"
  # Online audits, such as impostor commits, need a token; offline ones always run.
  local online=(--offline)
  [[ -z ${GH_TOKEN:-} ]] || online=()
  "$zizmor" "${online[@]}" .github/workflows
  git ls-files -z '*.sh' "${sources[@]}" | xargs -0 "$shellcheck"
  "$venv/bin/ruff" check scripts tests
  "$venv/bin/mypy" --strict --python-version 3.12 scripts tests
  "$gitleaks" git --no-banner --redact --log-level warn .
  git ls-files -z '*.md' "${sources[@]}" | xargs -0 "$typos"
  git ls-files -z "${sources[@]}" | xargs -0 "$editorconfig"
  cargo fmt --all -- --check
  cargo fmt --manifest-path models/Cargo.toml --all -- --check
  "$deny" --locked check
  "$deny" --locked --manifest-path models/Cargo.toml check
  echo 'DN LINT: PASS'
}

main "$@"
