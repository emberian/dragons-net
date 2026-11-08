-- SPDX-License-Identifier: AGPL-3.0-or-later
import DN.Server.SessionCert
import DN.Compiler.WpRet
import DN.Compiler.WpBytes

/-!
# DN.Server.SessionRun

What the session's function proofs share: `keptIn`'s check of a word, as it lowers (`keptIn_lower`). A word in range
passes it, changing nothing (`keptG_pass`, `keptA_wp`). Also where a function sits in the code (`in_code`).
-/

namespace DN.Server.SessionRun

open DN.Compiler DN.Compiler.Wp DN.Compiler.WpRet DN.Server DN.Server.SessionLayout

variable {σ : Type}

/-- `keptIn`'s test of a word: one unless it lies in `[0, hi]`. -/
def keptC (E : PancakeExp) (hi : Nat) : PancakeExp :=
  .cmp .less (.const 0)
    (.op .add (.cmp .less E (.const 0)) (.cmp .less (.const (BitVec.ofNat 64 hi)) E))

/-- `stop brokenState`, as it lowers. -/
def stopG : PancakeProg :=
  .seq (.store (.op .add .base (.const (BitVec.ofNat 64 (ownOff + ownStop))))
      (.const (BitVec.ofNat 64 brokenState)))
    (.ret (.const (BitVec.ofNat 64 brokenState)))

/-- `keptIn`, as it lowers: a stop, with the code of a broken state, unless the word lies in
`[0, hi]`. -/
def keptG (E : PancakeExp) (hi : Nat) : PancakeProg := .cond (keptC E hi) stopG .skip

theorem keptIn_lower {e : Syntax.PExpr} {E : PancakeExp} (he : Lower.lowerExp e = some E) (hi : Nat) :
    Lower.lowerStmt1 (SessionStore.keptIn e hi) = some (keptG E hi) := by
  have hs : Lower.lowerStmtsFold (SessionStore.stop brokenState) = some stopG := rfl
  simp [SessionStore.keptIn, SessionStore.or2, Syntax.eLt, Syntax.eAdd, Syntax.n, Lower.lowerStmt1,
    Lower.lowerExp, Lower.lowerStmtsFold_nil, he, hs, keptG, keptC]

/-- A word in `[0, hi]` passes the test. -/
theorem keptC_zero {s : PancakeState σ} {E : PancakeExp} {hi k : Nat} (hhi : hi < 2 ^ 63)
    (hk : k ≤ hi) (hE : eval s E = some (BitVec.ofNat 64 k)) : eval s (keptC E hi) = some 0 := by
  have h1 : signedLt (BitVec.ofNat 64 k) 0 = false := by
    have := WpBytes.signedLt_small (a := k) (b := 0) (by omega) (by omega)
    simpa using this
  have h2 : signedLt (BitVec.ofNat 64 hi) (BitVec.ofNat 64 k) = false := by
    have := WpBytes.signedLt_small (a := hi) (b := k) hhi (by omega)
    simp only [this, decide_eq_false_iff_not]
    omega
  simp only [keptC, eval, hE, h1, h2]
  rfl

/-- **A word in range passes `keptIn`**, which changes nothing. -/
theorem keptG_pass (o : Oracle σ) (R : Ret) {P : PancakeState σ → Prop} {E : PancakeExp} {hi : Nat}
    (hhi : hi < 2 ^ 63) (h : ∀ s, P s → ∃ k, k ≤ hi ∧ eval s E = some (BitVec.ofNat 64 k)) :
    SafeR o P (keptG E hi) R P := by
  have hz : ∀ s, P s → eval s (keptC E hi) = some 0 := fun s hs => by
    obtain ⟨k, hk, hE⟩ := h s hs
    exact keptC_zero hhi hk hE
  refine cond (fun s hs => ⟨0, hz s hs⟩) (fun s ⟨hs, hne⟩ => absurd (hz s hs) hne) ?_
  exact conseq (skip o _ R) (fun s h => h.1) (fun _ _ h => h) (fun _ h => h)

/-- `keptIn` in a loop's body, as `wpR` reads it. -/
def keptA (E : PancakeExp) (hi : Nat) : AProg σ :=
  .cond (keptC E hi)
    (.seq (.store (.op .add .base (.const (BitVec.ofNat 64 (ownOff + ownStop))))
        (.const (BitVec.ofNat 64 brokenState)))
      (.ret (.const (BitVec.ofNat 64 brokenState))))
    .skip

theorem keptA_vc (E : PancakeExp) (hi : Nat) (R : Ret) (Q : Assn σ) : vcR (keptA E hi) R Q :=
  ⟨⟨trivial, trivial⟩, trivial⟩

/-- …which a word in range passes, on to `Q`. -/
theorem keptA_wp {s : PancakeState σ} {E : PancakeExp} {hi k : Nat} (hhi : hi < 2 ^ 63) (hk : k ≤ hi)
    (hE : eval s E = some (BitVec.ofNat 64 k)) {R : Ret} {Q : Assn σ} (hq : Q s) :
    wpR (keptA E hi) R Q s := by
  simp only [keptA, wpR, keptC_zero hhi hk hE, if_true]
  exact hq

/-- A function of the session's program sits in any code holding its functions, as it lowers. -/
theorem in_code {g : Syntax.PFun} (hg : g ∈ Session.functions) {s : PancakeState σ}
    (hcode : ∀ f ps body k, (f, ps, body, k) ∈ SessionCert.fnsC → s.code f = some (ps, body)) :
    s.code g.name = some (g.params.map (·.2), (Lower.lower g).getD .skip) := by
  have hl : SessionCert.lowerFn g ∈ SessionCert.fnsC.map (fun h => (h.1, h.2.1, h.2.2.1)) := by
    rw [SessionCert.fnsC_lowers]
    exact List.mem_map_of_mem hg
  obtain ⟨⟨f, ps, body, k⟩, hm, he⟩ := List.mem_map.mp hl
  simp only [SessionCert.lowerFn, Prod.mk.injEq] at he
  obtain ⟨rfl, rfl, rfl⟩ := he
  exact hcode _ _ _ k hm

/-- The test can pass: zero lies in `[0, 0]`. -/
theorem keptC_witness : eval (σ := Unit) (bareState ()) (keptC (.const 0) 0) = some 0 :=
  keptC_zero (by decide) (Nat.le_refl 0) rfl

end DN.Server.SessionRun
