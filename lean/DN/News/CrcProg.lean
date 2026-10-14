-- SPDX-License-Identifier: AGPL-3.0-or-later
import DN.Compiler.Checked

/-!
# DN.News.CrcProg

The CRC-32C as the gate prints it: the table of 256 words built from `t`, and the CRC of the `n`
octets from `p` read through it. `DN.News.CrcCode` proves that they lower to the programs it shows
to compute `DN.News.Journal`'s table and CRC.
-/

namespace DN.News.CrcProg

open DN.Compiler DN.Compiler.Syntax

/-- One shift of the remainder in `c`, without a branch. -/
def shiftS : PExpr :=
  eXor (.shr (v "c") (n 1)) (eAnd (n 0x82F63B78) (eSub (n 0) (eAnd (v "c") (n 1))))

/-- The table from `t`, with the locals `i` and `c`. -/
def fillSrc : List PStmt :=
  [.assign "i" (n 0),
   .while (eLt (v "i") (n 256))
     ([.assign "c" (v "i")] ++ List.replicate 8 (.assign "c" shiftS) ++
      [.store (eAdd (v "t") (eMul (v "i") (n 8))) (v "c"), .assign "i" (eAdd (v "i") (n 1))])]

/-- The CRC-32C of the buffer from `p` into `r`, with the locals `i` and `acc`. -/
def crcSrc : List PStmt :=
  [.assign "i" (n 0), .assign "acc" (n 0xFFFFFFFF),
   .while (eLt (v "i") (v "n"))
     [.assign "acc" (eXor (.loadw 1 (eAdd (v "t") (eMul (eAnd (eXor (v "acc")
        (.loadb (eAdd (v "p") (v "i")))) (n 255)) (n 8)))) (.shr (v "acc") (n 8))),
      .assign "i" (eAdd (v "i") (n 1))],
   .assign "r" (eXor (v "acc") (n 0xFFFFFFFF))]

/-- The table built at `t`, then the CRC-32C of the `n` octets from `p`, returned: the two
fragments between their locals' declarations and the return. -/
def crcKernel : PFun :=
  { name := "dn_crc32c", exported := true, params := [(1, "t"), (1, "p"), (1, "n")],
    body := [.dec "r" (n 0), .dec "i" (n 0), .dec "c" (n 0), .dec "acc" (n 0)] ++ fillSrc ++
      crcSrc ++ [.ret (v "r")] }

def regression_936 : Bool := (Checked.emit crcKernel).isOk

end DN.News.CrcProg
