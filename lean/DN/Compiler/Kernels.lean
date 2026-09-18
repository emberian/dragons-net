import DN.Compiler.Checked
import DN.Compiler.ByteCopy

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

/-- The emitted loop lowers to the exact loop used by the inherited packed-byte
copy theorem. The ABI wrapper and native host are still separate obligations. -/
theorem copy_loop_lowering : Lower.lowerStmt1 copyLoop = some ByteCopy.copyByteWhile := rfl

theorem echo_is_checked : (Checked.emit echo).isOk = true := by decide

end DN.Compiler.Kernels
