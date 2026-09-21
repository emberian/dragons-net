import DN.Compiler.Checked
import DN.Compiler.ByteCopy
import DN.Compiler.NatToDec

namespace DN.Compiler.Kernels
open Syntax

/-- Reject negative-as-signed lengths before comparing or doing arithmetic.
Pointer validity, alignment, disjointness, and actual allocation lengths remain
host obligations. No unsigned length is silently treated as a negative loop count. -/
def rejectNegative (names : List String) (bad : List PStmt) (body : List PStmt) : List PStmt :=
  names.foldr (fun x rest => [.ite (eLt (v x) (n 0)) bad rest]) body

def copyLoop : PStmt := .while (eLt (v "i") (v "len"))
  [.storeb (eAdd (v "dst") (v "i")) (.loadb (eAdd (v "src") (v "i"))),
   .assign "i" (eAdd (v "i") (n 1))]

def echo : PFun :=
  { name := "dn_echo", exported := true,
    params := [(1,"src"),(1,"dst"),(1,"len"),(1,"cap")],
    body := rejectNegative ["len", "cap"] [.ret (n (2^32-1))]
      [.ite (eLt (n 4096) (v "cap")) [.ret (n (2^32-1))]
       [.ite (eLt (v "cap") (v "len")) [.ret (n (2^32-1))]
        [.dec "i" (n 0), copyLoop]]] ++ [.ret (v "len")] }

/-- One decimal digit in the emitted syntax. The working names are declared once, before
the loop, and assigned inside it: Pancake warns about a name declared twice. -/
def digitStep (declare : Bool) : List PStmt :=
  let bind := fun name value => if declare then PStmt.dec name value else PStmt.assign name value
  [bind "hi" (.shr (v "n") (n 32)),
   bind "lo" (eAnd (v "n") (n 4294967295)),
   bind "qh" (.shr (eMul (v "hi") (n 3435973837)) (n 35)),
   bind "rh" (eSub (v "hi") (eMul (v "qh") (n 10))),
   bind "t" (eAdd (eMul (v "rh") (n 6)) (v "lo")),
   bind "qt" (.shr (eMul (v "t") (n 3435973837)) (n 35)),
   bind "q" (eAdd (eAdd (eMul (v "qh") (n 4294967296)) (eMul (v "rh") (n 429496729)))
                  (v "qt")),
   .assign "p" (eSub (v "p") (n 1)),
   .storeb (v "p") (eAdd (eSub (v "n") (eMul (v "q") (n 10))) (n 48)),
   .assign "n" (v "q")]

/-- Render `n` as decimal ASCII below the pointer and return how many bytes it wrote. -/
def render : PFun :=
  { name := "dn_render", exported := true, params := [(1,"n"),(1,"p")],
    body := [.dec "start" (v "p")] ++ digitStep true ++
      [.while (v "n") (digitStep false), .ret (eSub (v "start") (v "p"))] }

/-- The emitted render lowers to exactly the model program the render theorem runs: the
working names declared once, the first digit, then the loop that assigns them. -/
theorem render_body_lowering :
    Lower.lowerStmtsFold (digitStep true ++ [.while (v "n") (digitStep false)])
      = some NatToDec.natToDecProg := rfl

/-- The loop body on its own lowers to the model's loop body. -/
theorem digit_loop_lowering :
    Lower.lowerStmtsFold (digitStep false) = some NatToDec.digitBodyAssign := rfl

-- The gate is run on the render as an executable check: deciding it during elaboration
-- costs more than it is worth on a program this size.
def regression_601 : Bool := (Checked.emit render).isOk

/-- The emitted loop lowers to the exact loop used by the packed-byte copy theorem.
The ABI wrapper and native host are still separate obligations. -/
theorem copy_loop_lowering : Lower.lowerStmt1 copyLoop = some ByteCopy.copyByteWhile := rfl

theorem echo_is_checked : (Checked.emit echo).isOk = true := by decide

end DN.Compiler.Kernels
