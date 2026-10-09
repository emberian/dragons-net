-- SPDX-License-Identifier: AGPL-3.0-or-later
import DN.Compiler.Checked

/-!
# DN.News.SipProg

SipHash-2-4 as the gate prints it: the tag of the `n` octets from `p` under the key of sixteen at
`k`, into `r`. `DN.News.SipHashCode` proves that it lowers to the program it shows to compute
`DN.News.SipHash.tag`.
-/

namespace DN.News.SipProg

open DN.Compiler DN.Compiler.Syntax

/-- `x` rotated left by `b` bits: two shifts and an or. -/
def rotlS (x : String) (b : Nat) : PExpr := eOr (.shl (v x) (n b)) (.shr (v x) (n (64 - b)))

/-- One SipRound over the locals `v0` to `v3`. -/
def roundS : List PStmt :=
  [.assign "v0" (eAdd (v "v0") (v "v1")), .assign "v1" (eXor (rotlS "v1" 13) (v "v0")),
   .assign "v0" (rotlS "v0" 32), .assign "v2" (eAdd (v "v2") (v "v3")),
   .assign "v3" (eXor (rotlS "v3" 16) (v "v2")), .assign "v0" (eAdd (v "v0") (v "v3")),
   .assign "v3" (eXor (rotlS "v3" 21) (v "v0")), .assign "v2" (eAdd (v "v2") (v "v1")),
   .assign "v1" (eXor (rotlS "v1" 17) (v "v2")), .assign "v2" (rotlS "v2" 32)]

/-- The octets at `q + i - 1` down to `q`, each below the last, into `m`. -/
def bytesS (q : PExpr) : Nat → List PStmt
  | 0 => []
  | i + 1 => .assign "m" (eOr (.shl (v "m") (n 8)) (.loadb (eAdd q (n i)))) :: bytesS q i

/-- The tag into `r`, with the locals `m`, `v0` to `v3`, `off` and `j`. -/
def sipSrc : List PStmt :=
  [.assign "m" (n 0)] ++ bytesS (v "k") 8 ++
  [.assign "v0" (eXor (v "m") (n 0x736f6d6570736575)),
   .assign "v2" (eXor (v "m") (n 0x6c7967656e657261)),
   .assign "m" (n 0)] ++ bytesS (eAdd (v "k") (n 8)) 8 ++
  [.assign "v1" (eXor (v "m") (n 0x646f72616e646f6d)),
   .assign "v3" (eXor (v "m") (n 0x7465646279746573)),
   .assign "off" (n 0),
   .while (eLe (eAdd (v "off") (n 8)) (v "n"))
     ([.assign "m" (n 0)] ++ bytesS (eAdd (v "p") (v "off")) 8 ++
      [.assign "v3" (eXor (v "v3") (v "m"))] ++ roundS ++ roundS ++
      [.assign "v0" (eXor (v "v0") (v "m")), .assign "off" (eAdd (v "off") (n 8))]),
   .assign "j" (eSub (v "n") (v "off")), .assign "m" (n 0),
   .while (eLt (n 0) (v "j"))
     [.assign "j" (eSub (v "j") (n 1)),
      .assign "m" (eOr (.shl (v "m") (n 8)) (.loadb (eAdd (eAdd (v "p") (v "off")) (v "j"))))],
   .assign "m" (eOr (.shl (v "n") (n 56)) (v "m")), .assign "v3" (eXor (v "v3") (v "m"))] ++
  roundS ++ roundS ++
  [.assign "v0" (eXor (v "v0") (v "m")), .assign "v2" (eXor (v "v2") (n 255))] ++
  roundS ++ roundS ++ roundS ++ roundS ++
  [.assign "r" (eXor (eXor (eXor (v "v0") (v "v1")) (v "v2")) (v "v3"))]

/-- The tag of the `n` octets from `p` under the key at `k`, stored at `out`: the fragment between
its locals' declarations and the store. -/
def sipKernel : PFun :=
  { name := "dn_siphash", exported := true, params := [(1, "k"), (1, "p"), (1, "n"), (1, "out")],
    body := ["r", "m", "v0", "v1", "v2", "v3", "off", "j"].map (.dec · (n 0)) ++ sipSrc ++
      [.store (v "out") (v "r"), .ret (n 0)] }

def regression_937 : Bool := (Checked.emit sipKernel).isOk

end DN.News.SipProg
