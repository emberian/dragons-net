#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
export LEAN_NUM_THREADS="${LEAN_NUM_THREADS:-4}"
python3 scripts/check_structure.py
lake build DN dn-compiler
python3 scripts/compiler_checks.py
python3 -m unittest discover -s tests -v
cargo fmt --all -- --check
cargo clippy --locked --workspace --all-targets -- -D warnings
cargo test --locked --workspace
python3 scripts/check_models.py
echo 'DN CHECK: PASS (Lean/model + host primitives; native/backend checks are separate)'
