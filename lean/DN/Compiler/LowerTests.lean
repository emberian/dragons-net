-- SPDX-License-Identifier: AGPL-3.0-or-later
import DN.Compiler.Lower

namespace DN.Compiler.LowerTests
open DN.Compiler.Syntax DN.Compiler.Lower

/-- A call lowers to `DecCall`, scoping what follows; one whose argument does not lower does not. -/
theorem call_lowers :
    lowerStmtsFold [.call "r" "f" [.var "a"], .ret (.var "r")] =
      some (.decCall "r" "f" [.var "a"] (.ret (.var "r"))) := rfl

theorem call_of_unlowerable_argument_is_rejected :
    lowerStmt1 (.call "r" "f" [.loadw 2 (.var "p")]) = none := rfl

theorem scalar_load_is_supported :
    lowerExp (.loadw 1 (.var "p")) = some (.loadWord (.var "p")) := rfl

theorem nonscalar_load_is_rejected :
    lowerExp (.loadw 2 (.var "p")) = none := rfl

theorem less_equal_swaps_operands :
    lowerExp (eLe (v "a") (v "b")) = some (.cmp .notLess (.var "b") (.var "a")) := rfl

theorem region_lowers :
    (lower (emitExportFun { regionC0 with name := "dn_region" })).isSome = true := rfl

theorem short_ffi_is_rejected : lowerStmt1 (.ffi "read" [.base]) = none := rfl

theorem long_ffi_is_rejected :
    lowerStmt1 (.ffi "read" [.base, .base, .base, .base, .base]) = none := rfl

end DN.Compiler.LowerTests
