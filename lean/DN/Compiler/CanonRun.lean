-- SPDX-License-Identifier: AGPL-3.0-or-later
import DN.Compiler.ParseCorrect
import DN.Compiler.Entry

/-!
# DN.Compiler.CanonRun

**A program runs as its canonical form does.** `canonProg` rewrites expressions only, each into
the form `Canon.canon_eval` shows evaluates alike. A run of the canonical program, from a state
whose code holds the canonical bodies, ends as the program's run ends, in its state but for the
code (`canon_run`). Programs of one canonical form, entered from states equal but for code of one
canonical form, therefore fail alike (`fails_same`): the program `Parse`, the Lean copy of CakeML's parser,
reads from a printed program fails exactly where the program it was printed from does.
-/

namespace DN.Compiler.CanonRun

open DN.Compiler DN.Compiler.Canon DN.Compiler.ParseCorrect

variable {σ : Type}

/-- Code with each body in canonical form. -/
def canonCode (c : String → Option (List String × PancakeProg)) :
    String → Option (List String × PancakeProg) :=
  fun f => (c f).map fun b => (b.1, canonProg b.2)

/-- A state with its code in canonical form. -/
def canonState (s : PancakeState σ) : PancakeState σ := { s with code := canonCode s.code }

/-- An expression reads no code. -/
theorem eval_code (s : PancakeState σ) (c : String → Option (List String × PancakeProg)) :
    ∀ e, eval { s with code := c } e = eval s e
  | .const _ | .var _ | .base => rfl
  | .op _ l r | .mul l r | .shiftR l r | .shiftL l r => by
    simp only [eval, eval_code s c l, eval_code s c r]
  | .cmp k l r => by cases k <;> simp only [eval, eval_code s c l, eval_code s c r]
  | .loadByte a | .loadWord a => by simp only [eval, eval_code s c a]

theorem eval_canon (s : PancakeState σ) (e : PancakeExp) : eval (canonState s) (canon e) = eval s e :=
  (canon_eval _ e).trans (eval_code s _ e)

theorem evalArgs_canon (s : PancakeState σ) :
    ∀ es, evalArgs (canonState s) (es.map canon) = evalArgs s es
  | [] => rfl
  | e :: es => by simp only [List.map_cons, evalArgs, eval_canon, evalArgs_canon s es]

theorem lookupCode_canon (c : String → Option (List String × PancakeProg)) (f : String)
    (vs : List Value) :
    lookupCode (canonCode c) f vs = (lookupCode c f vs).map fun r => (canonProg r.1, r.2) := by
  unfold lookupCode canonCode
  cases c f with
  | none => rfl
  | some b =>
    obtain ⟨ps, body⟩ := b
    simp only [Option.map_some]
    split <;> rfl

/-! The canonical state is the state but for its code, field by field. -/

theorem cs_locals (s : PancakeState σ) : (canonState s).locals = s.locals := rfl
theorem cs_memory (s : PancakeState σ) : (canonState s).memory = s.memory := rfl
theorem cs_memaddrs (s : PancakeState σ) : (canonState s).memaddrs = s.memaddrs := rfl
theorem cs_be (s : PancakeState σ) : (canonState s).be = s.be := rfl
theorem cs_clock (s : PancakeState σ) : (canonState s).clock = s.clock := rfl
theorem cs_ffi (s : PancakeState σ) : (canonState s).ffi = s.ffi := rfl
theorem cs_code (s : PancakeState σ) : (canonState s).code = canonCode s.code := rfl

/-- **A run of the canonical program, from the canonical code, is the program's run.** -/
theorem canon_run (o : Oracle σ) :
    ∀ (n : Nat) (p : PancakeProg) (s : PancakeState σ), s.clock ≤ n →
      PancakeSem o (canonProg p) (canonState s) =
        ((PancakeSem o p s).1, canonState (PancakeSem o p s).2) := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ihn =>
  intro p
  induction p with
  | skip => intro s _; rw [canonProg, PancakeSem.eq_1, PancakeSem.eq_1]
  | dec v e c ih =>
    intro s hc
    rw [canonProg, PancakeSem.eq_2, PancakeSem.eq_2, eval_canon]
    cases eval s e with
    | none => rfl
    | some val =>
      have h := ih { s with locals := setLocal s.locals v val } hc
      simp only [cs_locals]
      exact congrArg (fun r => (r.1, { r.2 with locals := resVar r.2.locals v (s.locals v) })) h
  | assign v e =>
    intro s _
    rw [canonProg, PancakeSem.eq_3, PancakeSem.eq_3, eval_canon]
    simp only [cs_locals]
    cases eval s e <;> cases s.locals v <;> rfl
  | store d e =>
    intro s _
    rw [canonProg, PancakeSem.eq_4, PancakeSem.eq_4, eval_canon, eval_canon]
    simp only [cs_memory, cs_memaddrs]
    cases eval s d <;> cases eval s e <;> try rfl
    rename_i a w
    dsimp only
    cases memStoreWord s.memory s.memaddrs a w <;> rfl
  | storeByte d e =>
    intro s _
    rw [canonProg, PancakeSem.eq_10, PancakeSem.eq_10, eval_canon, eval_canon]
    simp only [cs_memory, cs_memaddrs, cs_be]
    cases eval s d <;> cases eval s e <;> try rfl
    rename_i a w
    dsimp only
    cases memStoreByte s.memory s.memaddrs s.be a (w.setWidth 8) <;> rfl
  | extCall name a b c d =>
    intro s _
    rw [canonProg, PancakeSem.eq_5, PancakeSem.eq_5, eval_canon, eval_canon, eval_canon, eval_canon]
    simp only [cs_memory, cs_memaddrs, cs_be, cs_ffi]
    cases eval s a <;> cases eval s b <;> cases eval s c <;> cases eval s d <;> try rfl
    rename_i cp cl ap al
    dsimp only
    cases readByteArray s.memory s.memaddrs s.be cp cl.toNat <;>
      cases readByteArray s.memory s.memaddrs s.be ap al.toNat <;> try rfl
    rename_i conf arr
    dsimp only
    cases callFFI o s.ffi name conf arr <;> rfl
  | seq c1 c2 ih1 ih2 =>
    intro s hc
    rw [canonProg, PancakeSem.eq_6, PancakeSem.eq_6, ih1 s hc, cs_clock]
    have hcl : (clampClock s.clock (PancakeSem o c1 s)).2.clock ≤ n := by
      simp only [clampClock]; omega
    revert hcl
    generalize PancakeSem o c1 s = R
    obtain ⟨x, s1⟩ := R
    intro hcl
    simp only [clampClock] at hcl ⊢
    cases x with
    | none => exact ih2 { s1 with clock := min s.clock s1.clock } hcl
    | some r => rfl
  | cond e c1 c2 ih1 ih2 =>
    intro s hc
    rw [canonProg, PancakeSem.eq_7, PancakeSem.eq_7, eval_canon]
    cases eval s e with
    | none => rfl
    | some w =>
      by_cases hz : w = 0
      · simp only [hz, ne_eq, not_true_eq_false, if_false]
        exact ih2 s hc
      · simp only [hz, ne_eq, not_false_eq_true, if_true]
        exact ih1 s hc
  | while_ e c _ =>
    intro s hc
    rw [canonProg, PancakeSem.eq_8, PancakeSem.eq_8, eval_canon]
    cases eval s e with
    | none => rfl
    | some w =>
      by_cases hz : w = 0
      · simp only [hz, ne_eq, not_true_eq_false, if_false]
      · simp only [hz, ne_eq, not_false_eq_true, if_true, cs_clock]
        by_cases h0 : s.clock = 0
        · simp only [h0, if_true]; rfl
        · simp only [h0, if_false]
          have hb := ihn (s.clock - 1) (by omega) c (decClock s) (by simp [decClock])
          rw [show decClock (canonState s) = canonState (decClock s) from rfl, hb]
          have hcl : (clampClock (s.clock - 1) (PancakeSem o c (decClock s))).2.clock < n := by
            simp only [clampClock]; omega
          revert hcl
          generalize PancakeSem o c (decClock s) = R
          obtain ⟨x, s1⟩ := R
          intro hcl
          simp only [clampClock] at hcl ⊢
          have hloop := ihn _ hcl (.while_ e c) { s1 with clock := min (s.clock - 1) s1.clock }
            (Nat.le_refl _)
          rw [canonProg] at hloop
          cases x with
          | none => exact hloop
          | some res =>
            cases res with
            | continue_ => exact hloop
            | _ => rfl
  | ret e =>
    intro s _
    rw [canonProg, PancakeSem.eq_9, PancakeSem.eq_9, eval_canon]
    cases eval s e <;> rfl
  | decCall rt f args c _ =>
    intro s hc
    rw [canonProg, PancakeSem.eq_11, PancakeSem.eq_11, evalArgs_canon]
    cases evalArgs s args with
    | none => rfl
    | some vs =>
      simp only [cs_code, lookupCode_canon, cs_clock]
      cases lookupCode s.code f vs with
      | none => rfl
      | some bp =>
        obtain ⟨body, params⟩ := bp
        simp only [Option.map_some]
        by_cases h0 : s.clock = 0
        · simp only [h0, if_true]; rfl
        · simp only [h0, if_false]
          have hb := ihn (s.clock - 1) (by omega) body { decClock s with locals := params }
            (by simp [decClock])
          rw [show ({ decClock (canonState s) with locals := params } : PancakeState σ) =
            canonState { decClock s with locals := params } from rfl, hb]
          have hcl : (clampClock (s.clock - 1)
              (PancakeSem o body { decClock s with locals := params })).2.clock < n := by
            simp only [clampClock]; omega
          revert hcl
          generalize PancakeSem o body { decClock s with locals := params } = R
          obtain ⟨x, s1⟩ := R
          intro hcl
          simp only [clampClock] at hcl ⊢
          cases x with
          | none => rfl
          | some res =>
            cases res with
            | return_ v =>
              have h2 := ihn _ hcl c
                { { s1 with clock := min (s.clock - 1) s1.clock } with locals := setLocal s.locals rt v }
                (Nat.le_refl _)
              simp only [cs_locals]
              exact congrArg (fun r => (r.1, { r.2 with locals := resVar r.2.locals rt (s.locals rt) })) h2
            | _ => rfl

/-- The call that enters a program ends as its body's run ends, whatever state that run leaves. -/
theorem enter_fst (o : Oracle σ) (p q : PancakeProg) (s t : PancakeState σ) (hc : s.clock = t.clock)
    (h : (PancakeSem o p { decClock s with locals := fun _ => none }).1 =
      (PancakeSem o q { decClock t with locals := fun _ => none }).1) :
    (Entry.enter o p s).1 = (Entry.enter o q t).1 := by
  unfold Entry.enter
  rw [hc]
  split
  · rfl
  · simp only [clampClock]
    rw [h]
    generalize (PancakeSem o q { decClock t with locals := fun _ => none }).1 = x
    cases x with
    | none => rfl
    | some r => cases r <;> rfl

/-- Entering the canonical program from the canonical state ends as entering the program does. -/
theorem enter_canon (o : Oracle σ) (p : PancakeProg) (s : PancakeState σ) :
    (Entry.enter o (canonProg p) (canonState s)).1 = (Entry.enter o p s).1 := by
  have h := canon_run o _ p { decClock s with locals := fun _ => none } (Nat.le_refl _)
  have h1 := congrArg Prod.fst h
  simp only at h1
  exact enter_fst o _ p (canonState s) s rfl h1

/-- **The canonical program fails exactly where the program does.** -/
theorem fails_canon (o : Oracle σ) (p : PancakeProg) (s : PancakeState σ) :
    Entry.Fails o (canonProg p) (canonState s) ↔ Entry.Fails o p s := by
  unfold Entry.Fails
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨k, ?_⟩
    rw [← enter_canon o p { s with clock := k }]
    exact hk
  · rintro ⟨k, hk⟩
    refine ⟨k, ?_⟩
    have e := enter_canon o p { s with clock := k }
    rw [← hk, ← e]
    rfl

/-- **Programs of one canonical form fail alike** from states equal but for code of one canonical
form. -/
theorem fails_same (o : Oracle σ) {p q : PancakeProg} (hpq : canonProg p = canonProg q)
    {s t : PancakeState σ} (hst : canonState s = canonState t) :
    Entry.Fails o p s ↔ Entry.Fails o q t := by
  rw [← fails_canon o p s, ← fails_canon o q t, hpq, hst]

/-- A state whose code has the canonical form of another's is, canonically, that state. -/
theorem canonState_code (t : PancakeState σ) {c : String → Option (List String × PancakeProg)}
    (h : canonCode c = canonCode t.code) : canonState { t with code := c } = canonState t := by
  show { t with code := canonCode c } = { t with code := canonCode t.code }
  rw [h]

end DN.Compiler.CanonRun
