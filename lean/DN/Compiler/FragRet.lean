-- SPDX-License-Identifier: AGPL-3.0-or-later
import DN.Compiler.FragRules

/-!
# DN.Compiler.FragRet

Body fragments that may return: `FragR o R xs P P'` is `Frag` with returns giving back as `R`. A `ret` and a branch
whose arms return are fragments (`fragR_ret`, `fragR_ite`). A body closed on its own runs as the function does
(`fragR_close`).
-/

namespace DN.Compiler.Frag

open DN.Compiler DN.Compiler.Wp DN.Compiler.WpRet

variable {σ : Type}

/-- Statements from `P` to `P'` ahead of whatever follows, a return among them giving back what `R` allows. -/
def FragR (o : Oracle σ) (R : Ret) (xs : List Syntax.PStmt) (P P' : Assn σ) : Prop :=
  ∀ (k : PancakeProg) (Q : Assn σ), (∀ u y v, Q u → y ∈ declared xs → Q (restore u y v)) →
    SafeR o P' k R Q → ∃ c, Block.lowerK xs k = some c ∧ SafeR o P c R Q

theorem fragR_of {o : Oracle σ} {R : Ret} {xs : List Syntax.PStmt} {P P' : Assn σ} (h : Frag o xs P P') :
    FragR o R xs P P' := fun k Q hQ hk => h k R Q hQ hk

theorem fragR_append {o : Oracle σ} {R : Ret} {xs ys : List Syntax.PStmt} {P M P' : Assn σ}
    (h1 : FragR o R xs P M) (h2 : FragR o R ys M P') : FragR o R (xs ++ ys) P P' := by
  intro k Q hQ hk
  obtain ⟨c2, h2c, h2s⟩ := h2 k Q (fun u y v hq hy => hQ u y v hq (by
    rw [declared_append]; exact List.mem_append_right _ hy)) hk
  obtain ⟨c1, h1c, h1s⟩ := h1 c2 Q (fun u y v hq hy => hQ u y v hq (by
    rw [declared_append]; exact List.mem_append_left _ hy)) h2s
  exact ⟨c1, by rw [lowerK_append, h2c, Option.bind_some, h1c], h1s⟩

theorem fragR_conseq {o : Oracle σ} {R : Ret} {xs : List Syntax.PStmt} {P P0 P0' P' : Assn σ}
    (h : FragR o R xs P0 P0') (hp : ∀ s, P s → P0 s) (hq : ∀ s, P0' s → P' s) : FragR o R xs P P' := by
  intro k Q hQ hk
  obtain ⟨c, hc, hs⟩ := h k Q hQ (fun s hs => hk s (hq s hs))
  exact ⟨c, hc, fun s hs' => hs s (hp s hs')⟩

/-- **A return**, of what `R` allows. -/
theorem fragR_ret (o : Oracle σ) {R : Ret} {e : Syntax.PExpr} {E : PancakeExp} (he : Lower.lowerExp e = some E)
    {P P' : Assn σ} (h : ∀ s, P s → ∃ w, eval s E = some w ∧ R w s.memory) : FragR o R [.ret e] P P' := by
  intro k Q _ _
  refine ⟨.seq (.ret E) k, lowerK_one (by simp [Lower.lowerStmt1, he]) rfl k, ?_⟩
  exact seq (M := fun _ => False) (WpRet.ret h) (fun _ h => h.elim) (fun _ _ h => h)

/-- **A body closed**: as it lowers on its own, from `P` to `P'`, the locals it declares given back. -/
theorem fragR_close {o : Oracle σ} {R : Ret} {xs : List Syntax.PStmt} {P P' : Assn σ} (h : FragR o R xs P P')
    (hQ : ∀ u y v, P' u → y ∈ declared xs → P' (restore u y v)) :
    ∃ c, Lower.lowerStmtsFold xs = some c ∧ SafeR o P c R P' := by
  obtain ⟨c', hc', hs'⟩ := h .skip P' hQ (WpRet.skip o P' R)
  obtain ⟨c, hc, he⟩ := fold_of_K o xs hc'
  exact ⟨c, hc, fun s hs => by rw [he]; exact hs' s hs⟩

/-- **A branch** whose arms may return. -/
theorem fragR_ite (o : Oracle σ) {R : Ret} {c : Syntax.PExpr} {C : PancakeExp} (hc : Lower.lowerExp c = some C)
    {t e : List Syntax.PStmt} {P P' : Assn σ} (hP' : Safe.ClockFree P') (hdef : ∀ s, P s → ∃ w, eval s C = some w)
    (ht : FragR o R t (fun s => P s ∧ eval s C ≠ some 0) P')
    (htc : ∀ u y v, P' u → y ∈ declared t → P' (restore u y v))
    (he : FragR o R e (fun s => P s ∧ eval s C = some 0) P')
    (hec : ∀ u y v, P' u → y ∈ declared e → P' (restore u y v)) : FragR o R [.ite c t e] P P' := by
  obtain ⟨T, hT, hTs⟩ := fragR_close ht htc
  obtain ⟨E, hE, hEs⟩ := fragR_close he hec
  intro k Q _ hk
  exact ⟨.seq (.cond C T E) k, lowerK_one (by simp [Lower.lowerStmt1, hc, hT, hE]) rfl k,
    seq (WpRet.cond hdef hTs hEs) hk hP'⟩

/-- **A branch on a known flag**, arms that may return: the first if the flag is set, else the second. -/
theorem fragR_if (o : Oracle σ) {R : Ret} {c : Syntax.PExpr} {C : PancakeExp} (hc : Lower.lowerExp c = some C)
    {t e : List Syntax.PStmt} (hlt : LowKK t) (hle : LowKK e) {P Q : Assn σ} (hQ : Safe.ClockFree Q)
    (htc : ∀ u y v, Q u → y ∈ declared t → Q (restore u y v)) (hec : ∀ u y v, Q u → y ∈ declared e → Q (restore u y v))
    {b : Bool} (hv : ∀ u, P u → eval u C = some (if b then 1 else 0))
    (ht : b = true → FragR o R t P Q) (he : b = false → FragR o R e P Q) : FragR o R [.ite c t e] P Q := by
  refine fragR_ite o hc hQ (fun u hu => ⟨_, hv u hu⟩) ?_ htc ?_ hec
  · cases b with
    | true => exact fragR_conseq (ht rfl) (fun u h => h.1) fun _ h => h
    | false => exact fragR_of (frag_unsat hlt fun u ⟨hu, hne⟩ => hne (by rw [hv u hu]; rfl))
  · cases b with
    | true => exact fragR_of (frag_unsat hle fun u ⟨hu, h0⟩ =>
        absurd (Option.some.inj ((hv u hu).symm.trans h0)) (by decide))
    | false => exact fragR_conseq (he rfl) (fun u h => h.1) fun _ h => h

/-- A body from a premise with a witness, shown for each witness. -/
theorem fragR_exists {α : Type} {o : Oracle σ} {R : Ret} {xs : List Syntax.PStmt} (hl : LowKK xs)
    {P : α → Assn σ} {Q : Assn σ} (h : ∀ a, FragR o R xs (P a) Q) : FragR o R xs (fun u => ∃ a, P a u) Q := by
  intro k Q' hQ hk
  obtain ⟨c, hc⟩ := hl k
  refine ⟨c, hc, fun s ⟨a, hs⟩ => ?_⟩
  obtain ⟨c', hc', hs'⟩ := h a k Q' hQ hk
  rw [hc] at hc'; cases hc'
  exact hs' s hs

/-! ## The premises can hold -/

theorem fragR_witness : FragR (σ := Unit) Oracle.idle (fun _ _ => True) [] (fun _ => True) (fun _ => True) :=
  fun k _ _ h => ⟨k, rfl, h⟩

end DN.Compiler.Frag
