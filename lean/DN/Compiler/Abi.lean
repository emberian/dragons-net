import DN.Compiler.Checked

/-! The pinned x86-64 Cake export trampoline returns a 32-bit C result
(`mov %edi, %eax`). Carry a full machine word through a caller-owned output
slot instead. The caller must provide an aligned, writable, disjoint slot. -/
namespace DN.Compiler.Abi
open Syntax

mutual
def returnWordStmt : PStmt → List PStmt
  | .ret e => [.store (.var "dn_result") e, .ret (.const 0)]
  | .ite e t f => [.ite e (returnWordStmts t) (returnWordStmts f)]
  | .while e b => [.while e (returnWordStmts b)]
  | s => [s]
def returnWordStmts : List PStmt → List PStmt
  | [] => []
  | s :: rest => returnWordStmt s ++ returnWordStmts rest
end

/-- Internal syntax transformation. Validate both before and after transforming
via `emitWord`; otherwise introducing the parameter could capture a free name. -/
def wordResult (f : PFun) : PFun :=
  { f with params := f.params ++ [(1, "dn_result")], body := returnWordStmts f.body }

def emitWord (f : PFun) : Except String String := do
  let _ ← Checked.emit f
  Checked.emit (wordResult f)

theorem free_output_name_is_rejected :
    (emitWord { name := "probe", exported := true, body := [.ret (.var "dn_result")] }).isOk = false := by decide

theorem return_uses_output_slot (e : PExpr) :
    returnWordStmt (.ret e) = [.store (.var "dn_result") e, .ret (.const 0)] := rfl

end DN.Compiler.Abi
