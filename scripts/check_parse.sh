#!/usr/bin/env bash
# SPDX-License-Identifier: AGPL-3.0-or-later
# Every program dn-compiler prints, read by the parser of the pinned CakeML source inside HOL4:
# `parse_topdecs_to_ast`, which compile_pancake reads its input with, evaluated by EVAL on each
# program's text in a theory of its own, the equation saved as a theorem resting on no oracle, and
# the tree it gives held to the lowering in the canonical form of scripts/parser_contract.py
# (scripts/parse_check.py); so is each cell of the precedence table, to what the table says. The
# Lean copy of the parser, DN.Compiler.Parse, has to read each text to the same tree, places aside,
# or refuse it alike. Then once more with a subtraction regrouped, which the comparison has to see.
# DN_BUILD_JOBS theories are evaluated at a time.
set -euo pipefail
cd "$(dirname "$0")/.."
# A module in scripts/ with the name of a standard-library one would otherwise shadow it.
export PYTHONSAFEPATH=1
root="$(pwd)"
# shellcheck source=/dev/null
source scripts/backend_lane.sh
begin_lane PARSE
build_jobs=$(checked_jobs)
[[ -z "${CLINE_OPTIONS:-}${POLY_CLINE_OPTIONS:-}" ]] || refuse "unset CLINE_OPTIONS and POLY_CLINE_OPTIONS"
HOLDIR="$root/.deps/hol"
CAKEMLDIR="$root/.deps/cakeml"
export HOLDIR CAKEMLDIR
compiler="${DN_COMPILER:-$root/.lake/build/bin/dn-compiler}"
[[ -x "$compiler" ]] || refuse "build dn-compiler first (lake build dn-compiler)"
prepare_trees
use_holmake

mkdir -p build
holmake_gated "$CAKEMLDIR/pancake/parser" "$root/build/parse-holmake.log" "$CAKEMLDIR" "$build_jobs" \
  "$CAKEMLDIR/pancake/parser/panPtreeConversionTheory.uo" panPtreeConversionTheory.uo
trees="$root/build/parse-trees.json"
"$compiler" emit-trees > "$trees"
cells="$root/build/parse-cells.json"
"$compiler" emit-cells > "$cells"
copies="$root/build/parse-lean.json"
"$compiler" parse-trees > "$copies"
readings="$root/build/parse-lean-cells.json"
"$compiler" parse-cells > "$readings"

# evaluate DIR LOG [--defect]: the theories of the printed programs in DIR, outside both pinned
# trees, with LOG the build's output.
evaluate() {
  local dir=$1 log=$2
  shift 2
  rm -rf "$dir"
  mkdir -p "$dir"
  cp backend/parser/Holmakefile backend/parser/dnParseShowLib.sml "$dir"
  python3 scripts/parse_check.py write "$trees" "$dir" "$@"
  local targets
  mapfile -t targets < "$dir/targets"
  holmake_gated "$dir" "$log" "$dir" "$build_jobs" "$dir/${targets[-1]}" --no_prereqs "${targets[@]}"
}
evaluate "$root/build/parse" "$root/build/parse-eval.log" --cells "$cells"
python3 scripts/parse_check.py compare "$trees" "$root/build/parse" --cells "$cells" --lean "$copies" "$readings"
evaluate "$root/build/parse-defect" "$root/build/parse-defect.log" --defect
python3 scripts/parse_check.py compare "$trees" "$root/build/parse-defect" --expect-differences
