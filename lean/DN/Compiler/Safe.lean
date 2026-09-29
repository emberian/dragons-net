-- SPDX-License-Identifier: AGPL-3.0-or-later
import DN.Compiler.Entry

/-!
# DN.Compiler.Safe

Rules for showing that a program never errs, whatever the external world answers and however much
clock it is given. `Safe o pre prog post`: from every state satisfying `pre`, the run of `prog`
either ends as a run may end — out of clock, an external call that ends the run, a return — or
finishes normally in a state satisfying `post`; it never ends in `Error`, `Break` or `Continue`.
The rules follow the clauses of the semantics one by one, and `not_fails` turns a body that never
finishes normally into a `main` whose runs do not fail (`Entry.Fails`).

The semantics adjusts the clock between statements, so the rules that run one statement after
another ask that the assertion between them not depend on the clock (`ClockFree`).
-/

namespace DN.Compiler.Safe

open DN.Compiler DN.Compiler.Entry

variable {σ : Type}

/-- What a run may come to: a normal finish in a state satisfying `post`, or an ending that is not
a failure. -/
def Ok (post : PancakeState σ → Prop) : Option Result × PancakeState σ → Prop
  | (none, t) => post t
  | (some r, _) => ends (some r) = true

/-- From every state satisfying `pre`, the run of `prog` comes to `Ok post`. -/
def Safe (o : Oracle σ) (pre : PancakeState σ → Prop) (prog : PancakeProg)
    (post : PancakeState σ → Prop) : Prop :=
  ∀ s, pre s → Ok post (PancakeSem o prog s)

/-- An assertion that does not look at the clock. -/
def ClockFree (p : PancakeState σ → Prop) : Prop :=
  ∀ s k, p s → p { s with clock := k }

/-- Evaluating an expression does not read the clock. -/
theorem eval_clock (s : PancakeState σ) (k : Nat) :
    ∀ e : PancakeExp, eval { s with clock := k } e = eval s e := by
  intro e
  induction e with
  | const w => rfl
  | var name => rfl
  | base => rfl
  | op bop l r ihl ihr => simp only [eval, ihl, ihr]
  | mul l r ihl ihr => simp only [eval, ihl, ihr]
  | cmp c l r ihl ihr => cases c <;> simp only [eval, ihl, ihr]
  | loadByte a ih => simp only [eval, ih]
  | loadWord a ih => simp only [eval, ih]
  | shiftR l r ihl ihr => simp only [eval, ihl, ihr]

theorem skip (o : Oracle σ) (P : PancakeState σ → Prop) : Safe o P .skip P := by
  intro s hs
  rw [PancakeSem]
  exact hs

theorem conseq {o : Oracle σ} {P P' Q Q' : PancakeState σ → Prop} {c : PancakeProg}
    (h : Safe o P c Q) (hpre : ∀ s, P' s → P s) (hpost : ∀ s, Q s → Q' s) : Safe o P' c Q' := by
  intro s hs
  have k := h s (hpre s hs)
  revert k
  cases PancakeSem o c s with
  | mk r t => cases r with
    | none => exact hpost t
    | some res => exact id

theorem seq {o : Oracle σ} {P M Q : PancakeState σ → Prop} {c1 c2 : PancakeProg}
    (h1 : Safe o P c1 M) (h2 : Safe o M c2 Q) (hM : ClockFree M) : Safe o P (.seq c1 c2) Q := by
  intro s hs
  have k1 := h1 s hs
  rw [PancakeSem]
  simp only [clampClock]
  revert k1
  cases PancakeSem o c1 s with
  | mk r t => cases r with
    | none => intro k1; exact h2 _ (hM t _ k1)
    | some res => exact id

theorem ret {o : Oracle σ} {P Q : PancakeState σ → Prop} {e : PancakeExp}
    (h : ∀ s, P s → ∃ w, eval s e = some w) : Safe o P (.ret e) Q := by
  intro s hs
  obtain ⟨w, hw⟩ := h s hs
  rw [PancakeSem]
  simp only [hw]
  rfl

theorem assign {o : Oracle σ} {P Q : PancakeState σ → Prop} {x : String} {e : PancakeExp}
    (h : ∀ s, P s → ∃ val old, eval s e = some val ∧ s.locals x = some old ∧
      Q { s with locals := setLocal s.locals x val }) : Safe o P (.assign x e) Q := by
  intro s hs
  obtain ⟨val, old, hv, hold, hq⟩ := h s hs
  rw [PancakeSem]
  simp only [hv, hold]
  exact hq

theorem store {o : Oracle σ} {P Q : PancakeState σ → Prop} {d e : PancakeExp}
    (h : ∀ s, P s → ∃ addr val m, eval s d = some addr ∧ eval s e = some val ∧
      memStoreWord s.memory s.memaddrs addr val = some m ∧ Q { s with memory := m }) :
    Safe o P (.store d e) Q := by
  intro s hs
  obtain ⟨addr, val, m, hd, he, hm, hq⟩ := h s hs
  rw [PancakeSem]
  simp only [hd, he, hm]
  exact hq

theorem storeByte {o : Oracle σ} {P Q : PancakeState σ → Prop} {d e : PancakeExp}
    (h : ∀ s, P s → ∃ addr val m, eval s d = some addr ∧ eval s e = some val ∧
      memStoreByte s.memory s.memaddrs s.be addr (val.setWidth 8) = some m ∧
      Q { s with memory := m }) : Safe o P (.storeByte d e) Q := by
  intro s hs
  obtain ⟨addr, val, m, hd, he, hm, hq⟩ := h s hs
  rw [PancakeSem]
  simp only [hd, he, hm]
  exact hq

theorem dec {o : Oracle σ} {P Q P' Q' : PancakeState σ → Prop} {v : String} {e : PancakeExp}
    {cont : PancakeProg}
    (hval : ∀ s, P s → ∃ val, eval s e = some val ∧ P' { s with locals := setLocal s.locals v val })
    (hcont : Safe o P' cont Q')
    (hpost : ∀ s t, P s → Q' t → Q { t with locals := resVar t.locals v (s.locals v) }) :
    Safe o P (.dec v e cont) Q := by
  intro s hs
  obtain ⟨val, hv, hp'⟩ := hval s hs
  have k := hcont _ hp'
  rw [PancakeSem]
  simp only [hv]
  revert k
  cases PancakeSem o cont { s with locals := setLocal s.locals v val } with
  | mk r t => cases r with
    | none => exact hpost s t hs
    | some res => exact id

theorem cond {o : Oracle σ} {P Q : PancakeState σ → Prop} {e : PancakeExp} {c1 c2 : PancakeProg}
    (hdef : ∀ s, P s → ∃ w, eval s e = some w)
    (h1 : Safe o (fun s => P s ∧ eval s e ≠ some 0) c1 Q)
    (h2 : Safe o (fun s => P s ∧ eval s e = some 0) c2 Q) : Safe o P (.cond e c1 c2) Q := by
  intro s hs
  obtain ⟨w, hw⟩ := hdef s hs
  rw [PancakeSem]
  simp only [hw]
  by_cases hz : w = 0
  · subst hz
    simp only [ne_eq, not_true_eq_false, if_false]
    exact h2 s ⟨hs, hw⟩
  · simp only [ne_eq, hz, not_false_eq_true, if_true]
    exact h1 s ⟨hs, by rw [hw]; simpa using hz⟩

theorem while_ {o : Oracle σ} {I : PancakeState σ → Prop} {e : PancakeExp} {body : PancakeProg}
    (hdef : ∀ s, I s → ∃ w, eval s e = some w)
    (hbody : Safe o (fun s => I s ∧ eval s e ≠ some 0) body I) (hI : ClockFree I) :
    Safe o I (.while_ e body) (fun s => I s ∧ eval s e = some 0) := by
  suffices h : ∀ n (s : PancakeState σ), s.clock ≤ n → I s →
      Ok (fun s => I s ∧ eval s e = some 0) (PancakeSem o (.while_ e body) s) from
    fun s hs => h s.clock s (Nat.le_refl _) hs
  intro n
  induction n with
  | zero =>
    intro s hc hs
    obtain ⟨w, hw⟩ := hdef s hs
    rw [PancakeSem]
    simp only [hw]
    by_cases hz : w = 0
    · subst hz
      simp only [ne_eq, not_true_eq_false, if_false]
      exact ⟨hs, hw⟩
    · simp only [ne_eq, hz, not_false_eq_true, if_true, Nat.le_zero.mp hc]
      rfl
  | succ n ih =>
    intro s hc hs
    obtain ⟨w, hw⟩ := hdef s hs
    rw [PancakeSem]
    simp only [hw]
    by_cases hz : w = 0
    · subst hz
      simp only [ne_eq, not_true_eq_false, if_false]
      exact ⟨hs, hw⟩
    · simp only [ne_eq, hz, not_false_eq_true, if_true]
      by_cases h0 : s.clock = 0
      · simp only [h0, if_true]
        rfl
      · simp only [h0, if_false, clampClock]
        have hd : I (decClock s) ∧ eval (decClock s) e ≠ some 0 :=
          ⟨hI s _ hs, by
            simp only [decClock, eval_clock, hw]
            simpa using hz⟩
        have k := hbody _ hd
        revert k
        cases PancakeSem o body (decClock s) with
        | mk r t =>
          cases r with
          | none =>
            intro k
            exact ih _ (by simp only; omega) (hI t _ k)
          | some res =>
            cases res with
            | continue_ => intro k; simp [Ok, ends] at k
            | break_ => intro k; simp [Ok, ends] at k
            | error => intro k; simp [Ok, ends] at k
            | timeout => intro _; rfl
            | return_ v => intro _; rfl
            | finalFFI ev => intro _; rfl

/-- A reply to an external call that returns normally has the length of the array it was given. -/
theorem callFFI_ret_length {o : Oracle σ} {ffi ffi' : σ} {name : String}
    {conf arr bytes : List (BitVec 8)} (h : callFFI o ffi name conf arr = .ret ffi' bytes) :
    bytes.length = arr.length := by
  unfold callFFI at h
  split at h
  · cases h; rfl
  · split at h
    · split at h
      · cases h; assumption
      · cases h
    · cases h

theorem extCall {o : Oracle σ} {P Q : PancakeState σ → Prop} {name : String}
    {c cl a al : PancakeExp}
    (h : ∀ s, P s → ∃ cp clv ap alv conf arr,
      eval s c = some cp ∧ eval s cl = some clv ∧ eval s a = some ap ∧ eval s al = some alv ∧
      readByteArray s.memory s.memaddrs s.be cp clv.toNat = some conf ∧
      readByteArray s.memory s.memaddrs s.be ap alv.toNat = some arr ∧
      ∀ ffi' bytes, bytes.length = arr.length →
        Q { s with memory := writeByteArray s.memaddrs s.be ap bytes s.memory, ffi := ffi' }) :
    Safe o P (.extCall name c cl a al) Q := by
  intro s hs
  obtain ⟨cp, clv, ap, alv, conf, arr, hc, hcl, ha, hal, hconf, harr, hq⟩ := h s hs
  rw [PancakeSem]
  simp only [hc, hcl, ha, hal, hconf, harr]
  cases hf : callFFI o s.ffi name conf arr with
  | final ev => rfl
  | ret ffi' bytes => exact hq ffi' bytes (callFFI_ret_length hf)

/-- **A body that never finishes normally makes a `main` whose runs do not fail**, whatever the
clock, provided every run of the body starts in a state satisfying its precondition. -/
theorem not_fails {o : Oracle σ} {P : PancakeState σ → Prop} {body : PancakeProg}
    {s : PancakeState σ} (h : Safe o P body (fun _ => False))
    (hP : ∀ k, P { decClock { s with clock := k } with locals := fun _ => none }) :
    ¬ Fails o body s := by
  apply not_fails_of_ends
  intro k
  unfold enter
  split
  · rfl
  · have hk := h _ (hP k)
    simp only [clampClock]
    revert hk
    cases PancakeSem o body { decClock { s with clock := k } with locals := fun _ => none } with
    | mk r t =>
      cases r with
      | none => intro hk; exact absurd hk id
      | some res =>
        cases res with
        | continue_ => intro hk; simp [Ok, ends] at hk
        | break_ => intro hk; simp [Ok, ends] at hk
        | error => intro hk; simp [Ok, ends] at hk
        | timeout => intro _; rfl
        | return_ v => intro _; rfl
        | finalFFI ev => intro _; rfl

/-- The rules ask for assertions free of the clock, and one about a local is. -/
theorem clockFree_witness : ClockFree (fun s : PancakeState Unit => s.locals "x" = some 1) :=
  fun _ _ h => h

/-- A program that is safe from every state: it returns at once. -/
theorem safe_witness :
    Safe (Oracle.idle (σ := Unit)) (fun _ => True) (.ret (.const 0)) (fun _ => False) :=
  ret fun _ _ => ⟨_, rfl⟩

end DN.Compiler.Safe
