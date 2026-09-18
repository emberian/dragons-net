import DN.Compiler.Clock

/-! Certificates require an inhabited precondition. This avoids packaging a
proof of an impossible caller contract as a useful compiled component.
The certificate concerns model execution, not printed source or native code. -/

namespace DN.Compiler
open Clock Region

structure Certificate (o : Oracle σ) (P : PancakeState σ → Prop)
    (Q : PancakeState σ → PancakeState σ → Prop) where
  code : PancakeProg
  correct : RefinesClk o code P Q
  witness : ∃ s, P s

def Certificate.then (first : Certificate o P Q) (second : Certificate o R S)
    (link : ∀ s t, P s → Q s t → R t) :
    Certificate o P (fun s u => ∃ t, Q s t ∧ S t u) :=
  ⟨.seq first.code second.code,
   refinesClk_seq o first.correct second.correct link, first.witness⟩

/-- Increment reads a bound local; it is not required to work on unbound states. -/
def increment (o : Oracle Unit) (value : Word) :
    Certificate o (fun s => s.locals "x" = some value)
      (fun s t => t = { s with locals := setLocal s.locals "x" (value + 1) }) where
  code := .assign "x" (.op .add (.var "x") (.const 1))
  correct := refinesClk_assign o "x" _ _ (fun _ => value + 1) (by
    intro s h
    simp [eval, h])
  witness := ⟨{ locals := fun _ => some value, memory := fun _ => 0,
                memaddrs := fun _ => false, be := false, clock := 0,
                ffi := (), baseAddr := 0 }, rfl⟩

theorem increment_result (o : Oracle Unit) (value : Word) (s : PancakeState Unit)
    (h : s.locals "x" = some value) :
    ∃ t, PancakeSem o (increment o value).code s = (none, t) ∧
      t.locals "x" = some (value + 1) := by
  obtain ⟨t, he, ht, _⟩ := (increment o value).correct s h
  refine ⟨t, he, ?_⟩
  rw [ht]
  simp [setLocal]

end DN.Compiler
