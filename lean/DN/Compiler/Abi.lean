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

def emitWord (f : PFun) : Except Checked.Reason String := do
  let _ ← Checked.emit f
  Checked.emit (wordResult f)

/-- The output slot is introduced by the transformation, so a function that already reads
that name is refused before the parameter can capture it. -/
theorem free_output_name_is_rejected :
    (emitWord { name := "dn_probe", exported := true,
                body := [.ret (.var "dn_result")] }).isOk = false := by decide

/-! ## Completeness of the rewrite

Counting, rather than a fixture, is what makes a missed branch visible: a branch the
rewrite fails to walk keeps its return and gains no store. -/

mutual
/-- Returns that hand a value straight back to the caller, at any depth. -/
def valueReturns : PStmt → Nat
  | .ret (.const 0) => 0
  | .ret _ => 1
  | .ite _ t f => valueReturnsL t + valueReturnsL f
  | .while _ b => valueReturnsL b
  | _ => 0
def valueReturnsL : List PStmt → Nat
  | [] => 0
  | s :: rest => valueReturns s + valueReturnsL rest
end

mutual
/-- Returns of any kind, at any depth. -/
def returns : PStmt → Nat
  | .ret _ => 1
  | .ite _ t f => returnsL t + returnsL f
  | .while _ b => returnsL b
  | _ => 0
def returnsL : List PStmt → Nat
  | [] => 0
  | s :: rest => returns s + returnsL rest
end

mutual
/-- Writes to the caller's output slot, at any depth. -/
def slotStores : PStmt → Nat
  | .store (.var "dn_result") _ => 1
  | .ite _ t f => slotStoresL t + slotStoresL f
  | .while _ b => slotStoresL b
  | _ => 0
def slotStoresL : List PStmt → Nat
  | [] => 0
  | s :: rest => slotStores s + slotStoresL rest
end

theorem append_counts (a b : List PStmt) :
    slotStoresL (a ++ b) = slotStoresL a + slotStoresL b ∧
    valueReturnsL (a ++ b) = valueReturnsL a + valueReturnsL b := by
  induction a with
  | nil => simp [slotStoresL, valueReturnsL]
  | cons s rest ih => simp [slotStoresL, valueReturnsL, ih.1, ih.2]; omega

/-- The rewrite turns every return into a slot write, at every depth: a branch it fails
to walk shows up as a missing store. -/
theorem rewrite_stores_every_return :
    (∀ s : PStmt, slotStoresL (returnWordStmt s) = slotStores s + returns s) ∧
    (∀ ss : List PStmt, slotStoresL (returnWordStmts ss) = slotStoresL ss + returnsL ss) := by
  apply returnWordStmt.mutual_induct
  all_goals intros
  all_goals simp_all [returnWordStmt, returnWordStmts, slotStores, slotStoresL, returns, returnsL,
    (append_counts _ _).1]
  all_goals omega

/-- …and leaves no return that hands a value back directly. -/
theorem rewrite_leaves_no_value_return :
    (∀ s : PStmt, valueReturnsL (returnWordStmt s) = 0) ∧
    (∀ ss : List PStmt, valueReturnsL (returnWordStmts ss) = 0) := by
  apply returnWordStmt.mutual_induct
  all_goals intros
  all_goals simp_all [returnWordStmt, returnWordStmts, valueReturns, valueReturnsL,
    (append_counts _ _).2]

/-- The rewrite is pointwise: it walks the list in order and replaces each statement by
its own image, so it can neither reorder nor drop a statement. -/
theorem rewrite_is_pointwise (ss : List PStmt) :
    returnWordStmts ss = ss.flatMap returnWordStmt := by
  induction ss with
  | nil => rfl
  | cons s rest ih => simp [returnWordStmts, ih]

/-- Statements that cannot carry a return are handed through untouched. -/
theorem rewrite_keeps_plain_statements (x fname rname : String) (e a b : PExpr)
    (args : List PExpr) :
    returnWordStmt (.dec x e) = [.dec x e] ∧ returnWordStmt (.assign x e) = [.assign x e] ∧
      returnWordStmt (.store a b) = [.store a b] ∧ returnWordStmt (.storeb a b) = [.storeb a b] ∧
      returnWordStmt (.ffi fname args) = [.ffi fname args] ∧
      returnWordStmt (.call rname fname args) = [.call rname fname args] :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem return_uses_output_slot (e : PExpr) :
    returnWordStmt (.ret e) = [.store (.var "dn_result") e, .ret (.const 0)] := rfl

/-- The rewrite reaches a return nested in control flow, not only a top-level one. -/
theorem nested_return_uses_output_slot (c e : PExpr) :
    returnWordStmts [.ite c [.ret e] [.while c [.ret e]]]
      = [.ite c [.store (.var "dn_result") e, .ret (.const 0)]
                [.while c [.store (.var "dn_result") e, .ret (.const 0)]]] := rfl

end DN.Compiler.Abi
