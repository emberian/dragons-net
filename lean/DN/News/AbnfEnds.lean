-- SPDX-License-Identifier: AGPL-3.0-or-later
import DN.News.AbnfMatch
-- `endsFrom`'s equation lemmas, made once there.
import DN.News.AbnfMutant

/-!
# DN.News.AbnfEnds

`Abnf.endsFrom`, with its memo, fuel and repetition loop, answers what `AbnfMatch.Matches` says. When a run answers, its
positions are the term's match ends (`ends_ok`). `Abnf.matches?` answers whether the rule matches all the bytes
(`matches?_ok`).
-/

namespace DN.News.AbnfEnds

open DN.News.Abnf DN.News.AbnfMatch

variable {g : Array Term} {input : Array Nat}

/-! ## Sets of positions -/

/-- Ascending, without repeats. -/
def Asc (a : Pos) : Prop := a.Pairwise (· < ·)

theorem mergeUp_mem : ∀ (n : Nat) (a b : Pos) (x : Nat), x ∈ mergeUp n a b ↔ x ∈ a ∨ x ∈ b
  | 0, a, b, x => by simp [mergeUp]
  | _ + 1, [], b, x => by simp [mergeUp]
  | _ + 1, _ :: _, [], x => by simp [mergeUp]
  | n + 1, p :: ps, q :: qs, x => by
    simp only [mergeUp]
    split
    · simp only [List.mem_cons, mergeUp_mem n ps (q :: qs) x]; exact or_assoc.symm
    split
    · simp only [List.mem_cons, mergeUp_mem n (p :: ps) qs x]; exact or_left_comm
    · rename_i h1 h2
      have : p = q := by omega
      subst this
      simp only [List.mem_cons, mergeUp_mem n ps qs x]
      constructor
      · rintro (h | h | h)
        · exact .inl (.inl h)
        · exact .inl (.inr h)
        · exact .inr (.inr h)
      · rintro ((h | h) | h | h)
        · exact .inl h
        · exact .inr (.inl h)
        · exact .inl h
        · exact .inr (.inr h)

theorem mergeUp_asc : ∀ (n : Nat) (a b : Pos), a.length + b.length ≤ n → Asc a → Asc b → Asc (mergeUp n a b)
  | 0, a, b, h, _, _ => by
    have ha : a = [] := List.eq_nil_of_length_eq_zero (by omega)
    have hb : b = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst ha hb; exact List.Pairwise.nil
  | _ + 1, [], b, _, _, hb => by simpa [mergeUp] using hb
  | _ + 1, _ :: _, [], _, ha, _ => by simpa [mergeUp] using ha
  | n + 1, p :: ps, q :: qs, h, ha, hb => by
    simp only [Asc, List.pairwise_cons] at ha hb
    simp only [mergeUp]
    split
    · rename_i hpq
      refine List.pairwise_cons.2 ⟨fun y hy => ?_, mergeUp_asc n ps (q :: qs) (by simp at h ⊢; omega) ha.2
        (List.pairwise_cons.2 hb)⟩
      rcases (mergeUp_mem n ps (q :: qs) y).1 hy with hy | hy
      · exact ha.1 y hy
      · rcases List.mem_cons.1 hy with rfl | hy
        · exact hpq
        · exact Nat.lt_trans hpq (hb.1 y hy)
    split
    · rename_i _ hqp
      refine List.pairwise_cons.2 ⟨fun y hy => ?_, mergeUp_asc n (p :: ps) qs (by simp at h ⊢; omega)
        (List.pairwise_cons.2 ha) hb.2⟩
      rcases (mergeUp_mem n (p :: ps) qs y).1 hy with hy | hy
      · rcases List.mem_cons.1 hy with rfl | hy
        · exact hqp
        · exact Nat.lt_trans hqp (ha.1 y hy)
      · exact hb.1 y hy
    · rename_i h1 h2
      have : p = q := by omega
      subst this
      refine List.pairwise_cons.2 ⟨fun y hy => ?_, mergeUp_asc n ps qs (by simp at h ⊢; omega) ha.2 hb.2⟩
      rcases (mergeUp_mem n ps qs y).1 hy with hy | hy
      · exact ha.1 y hy
      · exact hb.1 y hy

theorem union_mem {a b : Pos} {x : Nat} : x ∈ union a b ↔ x ∈ a ∨ x ∈ b := mergeUp_mem _ _ _ _

theorem union_asc {a b : Pos} (ha : Asc a) (hb : Asc b) : Asc (union a b) := mergeUp_asc _ _ _ (Nat.le_refl _) ha hb

theorem minusUp_sub : ∀ (n : Nat) (a b : Pos), (minusUp n a b).Sublist a
  | 0, a, _ => by simp [minusUp]
  | _ + 1, [], _ => by simp [minusUp]
  | _ + 1, _ :: _, [] => by simp [minusUp]
  | n + 1, p :: ps, q :: qs => by
    simp only [minusUp]
    split
    · exact (minusUp_sub n ps (q :: qs)).cons_cons p
    split
    · exact minusUp_sub n (p :: ps) qs
    · exact (minusUp_sub n ps qs).cons p

theorem minusUp_mem : ∀ (n : Nat) (a b : Pos), a.length + b.length ≤ n → Asc a → Asc b → ∀ x,
    x ∈ minusUp n a b ↔ x ∈ a ∧ x ∉ b
  | 0, a, b, h, _, _, x => by
    have ha : a = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst ha; simp [minusUp]
  | _ + 1, [], _, _, _, _, x => by simp [minusUp]
  | _ + 1, _ :: _, [], _, _, _, x => by simp [minusUp]
  | n + 1, p :: ps, q :: qs, h, ha, hb, x => by
    have ha' := ha
    have hb' := hb
    simp only [Asc, List.pairwise_cons] at ha hb
    simp only [minusUp]
    split
    · rename_i hpq
      rw [List.mem_cons, minusUp_mem n ps (q :: qs) (by simp at h ⊢; omega) ha.2 hb' x]
      constructor
      · rintro (rfl | ⟨h1, h2⟩)
        · refine ⟨List.mem_cons_self .., fun hx => ?_⟩
          rcases List.mem_cons.1 hx with e | hx
          · omega
          · have := hb.1 _ hx; omega
        · exact ⟨List.mem_cons_of_mem _ h1, h2⟩
      · rintro ⟨h1, h2⟩
        rcases List.mem_cons.1 h1 with rfl | h1
        · exact .inl rfl
        · exact .inr ⟨h1, h2⟩
    split
    · rename_i _ hqp
      rw [minusUp_mem n (p :: ps) qs (by simp at h ⊢; omega) ha' hb.2 x]
      constructor
      · rintro ⟨h1, h2⟩
        refine ⟨h1, fun hx => ?_⟩
        rcases List.mem_cons.1 hx with rfl | hx
        · rcases List.mem_cons.1 h1 with e | h1
          · omega
          · have := ha.1 _ h1; omega
        · exact h2 hx
      · rintro ⟨h1, h2⟩
        exact ⟨h1, fun hx => h2 (List.mem_cons_of_mem _ hx)⟩
    · rename_i hn1 hn2
      have : p = q := by omega
      subst this
      rw [minusUp_mem n ps qs (by simp at h ⊢; omega) ha.2 hb.2 x]
      constructor
      · rintro ⟨h1, h2⟩
        refine ⟨List.mem_cons_of_mem _ h1, fun hx => ?_⟩
        rcases List.mem_cons.1 hx with rfl | hx
        · have := ha.1 _ h1; omega
        · exact h2 hx
      · rintro ⟨h1, h2⟩
        rcases List.mem_cons.1 h1 with rfl | h1
        · exact absurd (List.mem_cons_self ..) h2
        · exact ⟨h1, fun hx => h2 (List.mem_cons_of_mem _ hx)⟩

theorem minus_mem {a b : Pos} (ha : Asc a) (hb : Asc b) {x : Nat} : x ∈ minus a b ↔ x ∈ a ∧ x ∉ b :=
  minusUp_mem _ _ _ (Nat.le_refl _) ha hb x

theorem minus_asc {a b : Pos} (ha : Asc a) : Asc (minus a b) := ha.sublist (minusUp_sub _ _ _)

/-! ## Repetitions -/

theorem rep_snoc {u : Term} : ∀ {k p x : Nat},
    Rep g input u (k + 1) p x ↔ ∃ q, Rep g input u k p q ∧ Matches g input u q x
  | 0, p, x => by
    rw [rep_succ_iff]
    constructor
    · rintro ⟨q, h1, h2⟩; rw [rep_zero_iff] at h2; subst h2; exact ⟨p, .zero, h1⟩
    · rintro ⟨q, h1, h2⟩; rw [rep_zero_iff] at h1; subst h1; exact ⟨x, h2, .zero⟩
  | k + 1, p, x => by
    rw [rep_succ_iff]
    constructor
    · rintro ⟨q, h1, h2⟩
      obtain ⟨r, h3, h4⟩ := (rep_snoc (k := k)).1 h2
      exact ⟨r, .succ h1 h3, h4⟩
    · rintro ⟨q, h1, h2⟩
      obtain ⟨r, h3, h4⟩ := rep_succ_iff.1 h1
      exact ⟨r, h3, (rep_snoc (k := k)).2 ⟨q, h4, h2⟩⟩

theorem at_bound {norm : Nat → Nat} : ∀ {p : Nat} {cs : List Nat}, at? input norm p cs = true →
    cs = [] ∨ p + cs.length ≤ input.size
  | _, [], _ => .inl rfl
  | p, c :: cs, h => by
    unfold at? at h
    split at h
    · rename_i b hb
      simp only [Bool.and_eq_true] at h
      have hp : p < input.size := by
        rcases Nat.lt_or_ge p input.size with hp | hp
        · exact hp
        · rw [Array.getElem?_eq_none hp] at hb; cases hb
      rcases at_bound h.2 with e | e
      · subst e; exact .inr (by simp; omega)
      · exact .inr (by simp at e ⊢; omega)
    · cases h

mutual
theorem Matches.bound {t : Term} {p e : Nat} : Matches g input t p e → e ≤ max p input.size
  | @Matches.range _ _ _ _ p b hb _ _ => by
    have : p < input.size := by
      rcases Nat.lt_or_ge p input.size with hp | hp
      · exact hp
      · rw [Array.getElem?_eq_none hp] at hb; cases hb
    omega
  | .text h => by
    rcases at_bound h with e | e
    · rw [e]; simp only [List.length_nil, Nat.add_zero]; exact Nat.le_max_left _ _
    · omega
  | .exact h => by
    rcases at_bound h with e | e
    · rw [e]; simp only [List.length_nil, Nat.add_zero]; exact Nat.le_max_left _ _
    · omega
  | .ref _ h => Matches.bound h
  | .seq h => Seq.bound h
  | .alt _ h => Matches.bound h
  | .rep _ _ h => Rep.bound h
theorem Seq.bound {ts : List Term} {p e : Nat} : Seq g input ts p e → e ≤ max p input.size
  | .nil => Nat.le_max_left _ _
  | .cons h1 h2 => by have := Matches.bound h1; have := Seq.bound h2; omega
theorem Rep.bound {t : Term} {k p e : Nat} : Rep g input t k p e → e ≤ max p input.size
  | .zero => Nat.le_max_left _ _
  | .succ h1 h2 => by have := Matches.bound h1; have := Rep.bound h2; omega
end

/-- An ascending list of numbers from `a` to `b` has at most `b + 1 - a` of them. -/
theorem asc_len_within : ∀ {l : Pos}, Asc l → ∀ {a b : Nat}, (∀ x ∈ l, a ≤ x ∧ x ≤ b) →
    l.length ≤ b + 1 - a
  | [], _, _, _, _ => Nat.zero_le _
  | x :: l, h, a, b, hb => by
    simp only [Asc, List.pairwise_cons] at h
    have h1 := hb x (List.mem_cons_self ..)
    have := asc_len_within h.2 (a := x + 1) (b := b) fun y hy => ⟨h.1 y hy, (hb y (List.mem_cons_of_mem _ hy)).2⟩
    simp only [List.length_cons]; omega

/-- An ascending list within another is no longer. -/
theorem asc_sub_len : ∀ {U A : Pos}, Asc U → Asc A → (∀ x ∈ A, x ∈ U) → A.length ≤ U.length
  | _, [], _, _, _ => Nat.zero_le _
  | [], a :: _, _, _, h => absurd (h a (List.mem_cons_self ..)) (by simp)
  | u :: U, a :: A, hU, hA, h => by
    have hU' := hU
    have hA' := hA
    simp only [Asc, List.pairwise_cons] at hU hA
    have ha := h a (List.mem_cons_self ..)
    by_cases e : a = u
    · subst e
      have := asc_sub_len hU.2 hA.2 fun x hx => by
        rcases List.mem_cons.1 (h x (List.mem_cons_of_mem _ hx)) with e | e
        · have := hA.1 x hx; omega
        · exact e
      simp only [List.length_cons]; omega
    · have hau : a ∈ U := by
        rcases List.mem_cons.1 ha with e' | e'
        · exact absurd e' e
        · exact e'
      have := asc_sub_len hU.2 hA' fun x hx => by
        rcases List.mem_cons.1 hx with rfl | hx
        · exact hau
        · rcases List.mem_cons.1 (h x (List.mem_cons_of_mem _ hx)) with e' | e'
          · have h1 := hA.1 x hx; have h2 := hU.1 a hau; omega
          · exact e'
      simp only [List.length_cons] at this ⊢; omega

/-- …and shorter when it misses one. -/
theorem asc_sub_lt : ∀ {U A : Pos}, Asc U → Asc A → (∀ x ∈ A, x ∈ U) → (∃ y ∈ U, y ∉ A) →
    A.length + 1 ≤ U.length
  | [], _, _, _, _, ⟨_, hy, _⟩ => absurd hy (by simp)
  | u :: U, A, hU, hA, h, ⟨y, hy, hyA⟩ => by
    have hU' := hU
    simp only [Asc, List.pairwise_cons] at hU
    by_cases huA : u ∈ A
    · match A, hA, h, huA, hyA with
      | a :: A, hA, h, huA, hyA =>
        have hA' := hA
        simp only [Asc, List.pairwise_cons] at hA
        have hau : a = u := by
          rcases List.mem_cons.1 (h a (List.mem_cons_self ..)) with e | e
          · exact e
          · rcases List.mem_cons.1 huA with e' | e'
            · exact e'.symm
            · have h1 := hU.1 a e; have h2 := hA.1 u e'; omega
        subst hau
        have hyU : y ∈ U := by
          rcases List.mem_cons.1 hy with e | e
          · exact absurd (e ▸ List.mem_cons_self ..) hyA
          · exact e
        have := asc_sub_lt hU.2 hA.2 (fun x hx => by
          rcases List.mem_cons.1 (h x (List.mem_cons_of_mem _ hx)) with e | e
          · have := hA.1 x hx; omega
          · exact e) ⟨y, hyU, fun hy' => hyA (List.mem_cons_of_mem _ hy')⟩
        simp only [List.length_cons]; omega
    · have := asc_sub_len hU.2 hA fun x hx => by
        rcases List.mem_cons.1 (h x hx) with e | e
        · exact absurd (e ▸ hx) huA
        · exact e
      simp only [List.length_cons]; omega

section rep
variable (g input) (u : Term) (lo p : Nat)

/-- The repetition's loop after `c` rounds: frontier `F`, ends counted `SD`, descending. Before round `lo` the frontier
is all `c` rounds reach; after, `SD` holds what rounds `lo` to `c` reach. `F` is what round `c` reached first; `SD`
grows strictly each round the frontier is nonempty. -/
def RepInv (c : Nat) (F SD : Pos) : Prop :=
  Asc F ∧ Asc SD.reverse ∧
    (c < lo → (∀ x, x ∈ F ↔ Rep g input u c p x) ∧ SD = []) ∧
    (lo ≤ c → (∀ x, x ∈ SD ↔ ∃ k, lo ≤ k ∧ k ≤ c ∧ Rep g input u k p x) ∧
      (∀ x, x ∈ F ↔ Rep g input u c p x ∧ ¬∃ k, lo ≤ k ∧ k < c ∧ Rep g input u k p x) ∧
      (F = [] ∨ c - lo + 1 ≤ SD.length))
end rep

theorem repInv_init {u : Term} {lo p : Nat} : RepInv g input u lo p 0 [p] (if lo = 0 then [p] else []) := by
  have h0 : ∀ x, x ∈ [p] ↔ Rep g input u 0 p x := fun x => by rw [List.mem_singleton, rep_zero_iff]
  refine ⟨List.pairwise_singleton _ _, by split <;> simp [Asc], fun h => ⟨h0, by rw [if_neg (by omega)]⟩,
    fun h => ?_⟩
  have : lo = 0 := by omega
  subst this
  rw [if_pos rfl]
  refine ⟨fun x => ?_, fun x => ?_, .inr (by simp)⟩
  · rw [h0]
    exact ⟨fun e => ⟨0, Nat.le_refl _, Nat.le_refl _, e⟩, fun ⟨k, _, hk, e⟩ => by
      have : k = 0 := by omega
      subst this; exact e⟩
  · rw [h0]
    exact ⟨fun e => ⟨e, fun ⟨k, _, hk, _⟩ => by omega⟩, fun h => h.1⟩

/-- The positions a round reaches past those of the frontier, from the rounds before. -/
theorem round_from {u : Term} {lo p c : Nat} {F SD next : Pos} (hI : RepInv g input u lo p c F SD) (hc : lo ≤ c)
    (hn : ∀ x, x ∈ next ↔ ∃ q, q ∈ F ∧ Matches g input u q x) {x : Nat} :
    Rep g input u (c + 1) p x ↔
      x ∈ next ∨ (Rep g input u (c + 1) p x ∧ ∃ k, lo ≤ k ∧ k ≤ c ∧ Rep g input u k p x) := by
  obtain ⟨-, -, -, h2⟩ := hI
  obtain ⟨-, hF, -⟩ := h2 hc
  constructor
  · intro h
    obtain ⟨q, hq, hm⟩ := rep_snoc.1 h
    by_cases hqF : q ∈ F
    · exact .inl ((hn x).2 ⟨q, hqF, hm⟩)
    · have : ∃ k, lo ≤ k ∧ k < c ∧ Rep g input u k p q :=
        Classical.byContradiction fun hne => hqF ((hF q).2 ⟨hq, hne⟩)
      obtain ⟨k, h1, h2, h3⟩ := this
      exact .inr ⟨h, k + 1, by omega, by omega, rep_snoc.2 ⟨q, h3, hm⟩⟩
  · rintro (h | ⟨h, -⟩)
    · obtain ⟨q, hq, hm⟩ := (hn x).1 h
      exact rep_snoc.2 ⟨q, ((hF q).1 hq).1, hm⟩
    · exact h

theorem rep_closure {u : Term} {lo p c : Nat}
    (h : ∀ x, Rep g input u c p x → ∃ k, lo ≤ k ∧ k < c ∧ Rep g input u k p x) :
    ∀ m x, Rep g input u (c + m) p x → ∃ k, lo ≤ k ∧ k < c ∧ Rep g input u k p x
  | 0, x, hx => h x hx
  | m + 1, x, hx => by
    obtain ⟨q, hq, hm⟩ := rep_snoc.1 hx
    obtain ⟨k, h1, h2, h3⟩ := rep_closure h m q hq
    have hx' : Rep g input u (k + 1) p x := rep_snoc.2 ⟨q, h3, hm⟩
    by_cases hk : k + 1 < c
    · exact ⟨k + 1, by omega, hk, hx'⟩
    · have : k + 1 = c := by omega
      rw [this] at hx'
      exact h x hx'

theorem rep_none {u : Term} {p c : Nat} (h : ∀ x, ¬Rep g input u c p x) : ∀ m x, ¬Rep g input u (c + m) p x
  | 0, x, hx => h x hx
  | m + 1, x, hx => by
    obtain ⟨q, hq, -⟩ := rep_snoc.1 hx
    exact rep_none h m q hq

theorem desc_lt {top : Nat} {rest : Pos} (h : Asc (top :: rest).reverse) : ∀ y ∈ rest, y < top := by
  intro y hy
  simp only [Asc, List.reverse_cons, List.pairwise_append, List.mem_reverse, List.mem_singleton] at h
  exact h.2.2 y hy top rfl

theorem beyond_lt {next SD : Pos} (hn : Asc next) (hs : Asc SD.reverse) (hb : beyond next SD = true) :
    ∀ x ∈ next, ∀ y ∈ SD, y < x := by
  intro x hx y hy
  match next, SD, hn, hs, hb, hx, hy with
  | q :: qs, top :: rest, hn, hs, hb, hx, hy =>
    simp only [beyond, decide_eq_true_eq] at hb
    have hqx : q ≤ x := by
      rcases List.mem_cons.1 hx with rfl | hx
      · exact Nat.le_refl _
      · simp only [Asc, List.pairwise_cons] at hn; exact Nat.le_of_lt (hn.1 x hx)
    have hyt : y ≤ top := by
      rcases List.mem_cons.1 hy with rfl | hy
      · exact Nat.le_refl _
      · exact Nat.le_of_lt (desc_lt hs y hy)
    omega

section
variable {u : Term} {lo p c : Nat} {F SD next : Pos}

theorem repInv_pre (hI : RepInv g input u lo p c F SD) (hc1 : c + 1 < lo)
    (hn : ∀ x, x ∈ next ↔ ∃ q, q ∈ F ∧ Matches g input u q x) (hna : Asc next) :
    RepInv g input u lo p (c + 1) next SD := by
  obtain ⟨-, hSD, h1, -⟩ := hI
  obtain ⟨hFc, e⟩ := h1 (by omega)
  refine ⟨hna, hSD, fun _ => ⟨fun x => ?_, e⟩, fun h => absurd h (by omega)⟩
  rw [hn x, rep_snoc]
  exact ⟨fun ⟨q, hq, hm⟩ => ⟨q, (hFc q).1 hq, hm⟩, fun ⟨q, hq, hm⟩ => ⟨q, (hFc q).2 hq, hm⟩⟩

/-- The round reaching `lo`, from what round `c` reached. -/
theorem first_round (hI : RepInv g input u lo p c F SD) (hc : c < lo)
    (hn : ∀ x, x ∈ next ↔ ∃ q, q ∈ F ∧ Matches g input u q x) (x : Nat) :
    x ∈ next ↔ Rep g input u (c + 1) p x := by
  obtain ⟨hFc, -⟩ := hI.2.2.1 hc
  rw [hn x, rep_snoc]
  exact ⟨fun ⟨q, hq, hm⟩ => ⟨q, (hFc q).1 hq, hm⟩, fun ⟨q, hq, hm⟩ => ⟨q, (hFc q).2 hq, hm⟩⟩

theorem repInv_beyond (hI : RepInv g input u lo p c F SD) (hc1 : ¬c + 1 < lo) (hF0 : F ≠ [])
    (hn : ∀ x, x ∈ next ↔ ∃ q, q ∈ F ∧ Matches g input u q x) (hna : Asc next)
    (hb : beyond next SD = true) :
    RepInv g input u lo p (c + 1) next (next.reverse ++ SD) := by
  have hSD := hI.2.1
  have hd := beyond_lt hna hSD hb
  have hasc : Asc (next.reverse ++ SD).reverse := by
    rw [List.reverse_append, List.reverse_reverse]
    exact List.pairwise_append.2 ⟨hSD, hna, fun a ha b hb => hd b hb a (List.mem_reverse.1 ha)⟩
  refine ⟨hna, hasc, fun h => absurd h hc1, fun _ => ?_⟩
  by_cases hc : lo ≤ c
  · have hr := fun x => round_from hI hc hn (x := x)
    obtain ⟨hS, -, hprog⟩ := hI.2.2.2 hc
    refine ⟨fun x => ?_, fun x => ?_, ?_⟩
    · rw [List.mem_append, List.mem_reverse, hS x]
      constructor
      · rintro (h | ⟨k, h1, h2, h3⟩)
        · exact ⟨c + 1, by omega, Nat.le_refl _, (hr x).2 (.inl h)⟩
        · exact ⟨k, h1, by omega, h3⟩
      · rintro ⟨k, h1, h2, h3⟩
        by_cases hk : k ≤ c
        · exact .inr ⟨k, h1, hk, h3⟩
        · have : k = c + 1 := by omega
          subst this
          rcases (hr x).1 h3 with h | ⟨-, h⟩
          · exact .inl h
          · exact .inr h
    · constructor
      · intro h
        refine ⟨(hr x).2 (.inl h), fun ⟨k, h1, h2, h3⟩ => ?_⟩
        have := hd x h x ((hS x).2 ⟨k, h1, by omega, h3⟩)
        omega
      · rintro ⟨h, hne⟩
        rcases (hr x).1 h with h | ⟨-, k, h1, h2, h3⟩
        · exact h
        · exact absurd ⟨k, h1, by omega, h3⟩ hne
    · by_cases h0 : next = []
      · exact .inl h0
      · refine .inr ?_
        have h1 := List.length_pos_iff.2 h0
        rcases hprog with h | h
        · exact absurd h hF0
        · simp only [List.length_append, List.length_reverse]; omega
  · obtain ⟨-, e⟩ := hI.2.2.1 (by omega)
    subst e
    have hfr := first_round hI (by omega) hn
    refine ⟨fun x => ?_, fun x => ?_, ?_⟩
    · rw [List.append_nil, List.mem_reverse, hfr x]
      exact ⟨fun h => ⟨c + 1, by omega, Nat.le_refl _, h⟩, fun ⟨k, h1, h2, h3⟩ => by
        have : k = c + 1 := by omega
        subst this; exact h3⟩
    · rw [hfr x]
      exact ⟨fun h => ⟨h, fun ⟨k, h1, h2, _⟩ => by omega⟩, fun h => h.1⟩
    · by_cases h0 : next = []
      · exact .inl h0
      · exact .inr (by simp only [List.append_nil, List.length_reverse]; have := List.length_pos_iff.2 h0; omega)

theorem repInv_merge (hI : RepInv g input u lo p c F SD) (hc1 : ¬c + 1 < lo) (hF0 : F ≠ [])
    (hn : ∀ x, x ∈ next ↔ ∃ q, q ∈ F ∧ Matches g input u q x) (hna : Asc next)
    (hb : beyond next SD = false) :
    RepInv g input u lo p (c + 1) (minus next SD.reverse) (union SD.reverse next).reverse := by
  have hSD := hI.2.1
  by_cases hc : lo ≤ c
  · have hr := fun x => round_from hI hc hn (x := x)
    obtain ⟨hS, -, hprog⟩ := hI.2.2.2 hc
    have hm : ∀ x, x ∈ minus next SD.reverse ↔ x ∈ next ∧ x ∉ SD := fun x => by
      rw [minus_mem hna hSD, List.mem_reverse]
    have hu : ∀ x, x ∈ (union SD.reverse next).reverse ↔ x ∈ SD ∨ x ∈ next := fun x => by
      rw [List.mem_reverse, union_mem, List.mem_reverse]
    refine ⟨minus_asc hna, by rw [List.reverse_reverse]; exact union_asc hSD hna, fun h => absurd h hc1,
      fun _ => ⟨fun x => ?_, fun x => ?_, ?_⟩⟩
    · rw [hu x, hS x]
      constructor
      · rintro (⟨k, h1, h2, h3⟩ | h)
        · exact ⟨k, h1, by omega, h3⟩
        · exact ⟨c + 1, by omega, Nat.le_refl _, (hr x).2 (.inl h)⟩
      · rintro ⟨k, h1, h2, h3⟩
        by_cases hk : k ≤ c
        · exact .inl ⟨k, h1, hk, h3⟩
        · have : k = c + 1 := by omega
          subst this
          rcases (hr x).1 h3 with h | ⟨-, h⟩
          · exact .inr h
          · exact .inl h
    · rw [hm x]
      constructor
      · rintro ⟨h, hx⟩
        exact ⟨(hr x).2 (.inl h), fun ⟨k, h1, h2, h3⟩ => hx ((hS x).2 ⟨k, h1, by omega, h3⟩)⟩
      · rintro ⟨h, hne⟩
        rcases (hr x).1 h with h' | ⟨-, k, h1, h2, h3⟩
        · refine ⟨h', fun hx => hne ?_⟩
          obtain ⟨k, h1, h2, h3⟩ := (hS x).1 hx
          exact ⟨k, h1, by omega, h3⟩
        · exact absurd ⟨k, h1, by omega, h3⟩ hne
    · by_cases h0 : minus next SD.reverse = []
      · exact .inl h0
      · refine .inr ?_
        obtain ⟨y, hy⟩ := List.exists_mem_of_ne_nil _ h0
        have hy' := (hm y).1 hy
        have := asc_sub_lt (union_asc hSD hna) hSD (fun x hx => union_mem.2 (.inl hx))
          ⟨y, union_mem.2 (.inr hy'.1), fun h => hy'.2 (List.mem_reverse.1 h)⟩
        rcases hprog with h | h
        · exact absurd h hF0
        · simp only [List.length_reverse] at this ⊢; omega
  · obtain ⟨-, e⟩ := hI.2.2.1 (by omega)
    subst e
    have : beyond next [] = true := by cases next <;> rfl
    rw [this] at hb
    cases hb

theorem repInv_final {hi : Option Nat} (hI : RepInv g input u lo p c F SD) (hhi : ∀ h ∈ hi, c ≤ h)
    (hend : F = [] ∨ ∃ h ∈ hi, h ≤ c) (x : Nat) : x ∈ SD ↔ Matches g input (.rep lo hi u) p x := by
  rw [rep_iff]
  by_cases hc : lo ≤ c
  · obtain ⟨hS, hFc, -⟩ := hI.2.2.2 hc
    rw [hS x]
    rcases hend with h0 | ⟨h, hh, hhc⟩
    · subst h0
      have hc0 : ∀ y, Rep g input u c p y → ∃ k, lo ≤ k ∧ k < c ∧ Rep g input u k p y := fun y hy =>
        Classical.byContradiction fun hne => by simpa using (hFc y).2 ⟨hy, hne⟩
      constructor
      · rintro ⟨k, h1, h2, h3⟩
        exact ⟨k, h1, fun h hh => Nat.le_trans h2 (hhi h hh), h3⟩
      · rintro ⟨k, h1, h2, h3⟩
        by_cases hk : k ≤ c
        · exact ⟨k, h1, hk, h3⟩
        · obtain ⟨j, j1, j2, j3⟩ := rep_closure hc0 (k - c) x (by rwa [show c + (k - c) = k by omega])
          exact ⟨j, j1, by omega, j3⟩
    · have hch : c = h := Nat.le_antisymm (hhi h hh) hhc
      subst hch
      have hi' : hi = some c := Option.mem_def.1 hh
      subst hi'
      constructor
      · rintro ⟨k, h1, h2, h3⟩
        exact ⟨k, h1, fun h' hh' => by cases Option.mem_def.1 hh'; exact h2, h3⟩
      · rintro ⟨k, h1, h2, h3⟩
        exact ⟨k, h1, h2 c rfl, h3⟩
  · obtain ⟨hFc, e⟩ := hI.2.2.1 (by omega)
    subst e
    simp only [List.not_mem_nil, false_iff, not_exists, not_and]
    intro k h1 h2 h3
    rcases hend with h0 | ⟨h, hh, hhc⟩
    · subst h0
      have hnone : ∀ y, ¬Rep g input u c p y := fun y hy => by simpa using (hFc y).2 hy
      exact rep_none hnone (k - c) x (by rwa [show c + (k - c) = k by omega])
    · have := h2 h hh; omega

theorem repInv_full (hI : RepInv g input u lo p c F SD) (hc : lo + input.size + 1 ≤ c) : F = [] := by
  obtain ⟨hS, -, hprog⟩ := hI.2.2.2 (by omega)
  rcases hprog with h | h
  · exact h
  · have hb := asc_len_within hI.2.1 (a := p) (b := max p input.size) fun x hx => by
      obtain ⟨k, -, -, hk⟩ := (hS x).1 (List.mem_reverse.1 hx)
      exact ⟨Rep.le hk, Rep.bound hk⟩
    rw [List.length_reverse] at hb
    omega

end

/-! ## Runs that answer -/

/-- If `m` answers from memo `M`, its answer and memo are as `P` says. -/
def Ok {α : Type} (m : Run α) (M : Memo) (P : α → Memo → Prop) : Prop :=
  ∀ a M', m.run.run M = (.ok a, M') → P a M'

theorem ok_pure {α : Type} {a : α} {M : Memo} {P : α → Memo → Prop} (h : P a M) : Ok (pure a) M P :=
  fun a' M' e => by cases e; exact h

theorem ok_throw {α : Type} {s : Stop} {M : Memo} {P : α → Memo → Prop} : Ok (throw s) M P :=
  fun _ _ e => by cases e

theorem ok_bind {α β : Type} {m : Run α} {k : α → Run β} {M : Memo} {Q : α → Memo → Prop}
    {P : β → Memo → Prop}
    (h1 : Ok m M Q) (h2 : ∀ a M1, Q a M1 → Ok (k a) M1 P) : Ok (m >>= k) M P := by
  intro b M' e
  have : (m >>= k).run.run M = match m.run.run M with
      | (.ok a, M1) => (k a).run.run M1
      | (.error s, M1) => (.error s, M1) := by
    simp only [ExceptT.run_bind, StateT.run_bind]
    rcases m.run.run M with ⟨r, M1⟩
    cases r <;> rfl
  rw [this] at e
  revert e
  rcases hm : m.run.run M with ⟨r, M1⟩
  cases r with
  | error s => intro e; cases e
  | ok a => exact h2 a M1 (h1 a M1 hm) b M'

theorem ok_map {α β : Type} {m : Run α} {f : α → β} {M : Memo} {Q : α → Memo → Prop}
    {P : β → Memo → Prop}
    (h1 : Ok m M Q) (h2 : ∀ a M1, Q a M1 → P (f a) M1) : Ok (f <$> m) M P := by
  rw [map_eq_pure_bind]
  exact ok_bind h1 fun a M1 h => ok_pure (h2 a M1 h)

theorem ok_get {M : Memo} {P : Memo → Memo → Prop} (h : P M M) : Ok get M P :=
  fun a M' e => by cases e; exact h

theorem ok_modify {f : Memo → Memo} {M : Memo} {P : PUnit → Memo → Prop} (h : P ⟨⟩ (f M)) :
    Ok (modify f) M P :=
  fun a M' e => by cases e; exact h

/-! ## `endsFrom` answers the matches' ends -/

section
variable (g : Array Term) (input : Array Nat)

/-- Where the memo has a rule at a position, it holds exactly the ends of its matches there. -/
def MemoOk (M : Memo) : Prop :=
  ∀ p i e, (M[p]?.getD []).lookup i = some e → Asc e ∧ ∀ x, x ∈ e ↔ Matches g input (.ref i) p x

/-- An answer of `endsFrom` for `t` from `p`: the ends of its matches, ascending, the memo kept right. -/
def Ends (t : Term) (p : Nat) (e : Pos) (M : Memo) : Prop :=
  MemoOk g input M ∧ Asc e ∧ ∀ x, x ∈ e ↔ Matches g input t p x
end

theorem ok_unionAll {α : Type} (F : α → Run Pos) (Mt : α → Nat → Prop)
    (hF : ∀ a M, MemoOk g input M →
      Ok (F a) M fun e M' => MemoOk g input M' ∧ Asc e ∧ ∀ x, x ∈ e ↔ Mt a x) :
    ∀ (l : List α) (R : Pos) (M : Memo), MemoOk g input M → Asc R →
      Ok (l.foldlM (fun R a => union R <$> F a) R) M
        fun R' M' => MemoOk g input M' ∧ Asc R' ∧ ∀ x, x ∈ R' ↔ x ∈ R ∨ ∃ a ∈ l, Mt a x
  | [], R, M, hM, hR => ok_pure ⟨hM, hR, fun x => by simp⟩
  | a :: l, R, M, hM, hR => by
    rw [List.foldlM_cons]
    refine ok_bind (Q := fun R1 M1 => MemoOk g input M1 ∧ Asc R1 ∧ ∀ x, x ∈ R1 ↔ x ∈ R ∨ Mt a x)
      (ok_map (hF a M hM) fun e M1 h => ⟨h.1, union_asc hR h.2.1, fun x => by rw [union_mem, h.2.2 x]⟩)
      fun R1 M1 h => ?_
    refine fun R' M' e => ?_
    obtain ⟨h1, h2, h3⟩ := ok_unionAll F Mt hF l R1 M1 h.1 h.2.1 R' M' e
    refine ⟨h1, h2, fun x => ?_⟩
    rw [h3 x, h.2.2 x]
    simp only [List.mem_cons, exists_eq_or_imp]
    constructor
    · rintro ((h | h) | h)
      · exact .inl h
      · exact .inr (.inl h)
      · exact .inr (.inr h)
    · rintro (h | h | h)
      · exact .inl (.inl h)
      · exact .inl (.inr h)
      · exact .inr h

theorem memoOk_empty (n : Nat) : MemoOk g input (Array.replicate n []) := fun p i e h => by
  simp [Array.getElem?_replicate] at h
  split at h <;> simp at h

theorem ok_forIn_range {β : Type} (body : Nat → β → Run (ForInStep β)) (J : Nat → β → Memo → Prop)
    (D : β → Memo → Prop)
    (hstep : ∀ i b M, J i b M → Ok (body i b) M fun r M' => match r with
      | .done b' => D b' M'
      | .yield b' => J (i + 1) b' M') :
    ∀ (n i : Nat) (b : β) (M : Memo), J i b M → (∀ b M, J (i + n) b M → D b M) →
      Ok (forIn (List.range' i n) b body) M D
  | 0, i, b, M, h, hend => by
    simp only [List.range'_zero, List.forIn_nil]
    exact ok_pure (hend b M (by simpa using h))
  | n + 1, i, b, M, h, hend => by
    rw [List.range'_succ, List.forIn_cons]
    refine ok_bind (hstep i b M h) fun r M1 hr => ?_
    cases r with
    | done b' => exact ok_pure hr
    | yield b' =>
      exact ok_forIn_range body J D hstep n (i + 1) b' M1 hr fun b M h =>
        hend b M (by rwa [show i + (n + 1) = i + 1 + n by omega])

theorem memoOk_modify {M : Memo} (hM : MemoOk g input M) {p i : Nat} {e : Pos} (he : Asc e)
    (hx : ∀ x, x ∈ e ↔ Matches g input (.ref i) p x) : MemoOk g input (M.modify p ((i, e) :: ·)) := by
  intro p' i' e' h
  rw [Array.getElem?_modify] at h
  split at h
  · rename_i hp
    subst hp
    rcases hm : M[p]? with _ | l
    · rw [hm] at h; simp at h
    · rw [hm] at h
      simp only [Option.map_some, Option.getD_some, List.lookup_cons] at h
      split at h
      · rename_i hi
        cases h
        have : i' = i := by simpa using hi
        subst this
        exact ⟨he, hx⟩
      · exact hM p i' e' (by rw [hm]; exact h)
  · exact hM p' i' e' h

theorem ends_ok : ∀ (f : Nat) (t : Term) (p : Nat) (M : Memo), MemoOk g input M →
    Ok (endsFrom g input f t p) M (Ends g input t p)
  | 0, _, _, _, _ => by rw [endsFrom.eq_1]; exact ok_throw
  | f + 1, t, p, M, hM => by
    have ih := ends_ok f
    have hall : ∀ (u : Term) (S : Pos) (M : Memo), MemoOk g input M →
        Ok (S.foldlM (fun R q => union R <$> endsFrom g input f u q) []) M
          fun R M' => MemoOk g input M' ∧ Asc R ∧ ∀ x, x ∈ R ↔ ∃ q ∈ S, Matches g input u q x := by
      intro u S M hM R M' e
      obtain ⟨h1, h2, h3⟩ := ok_unionAll (fun q => endsFrom g input f u q) (fun q x => Matches g input u q x)
        (fun q M hM => ih u q M hM) S [] M hM List.Pairwise.nil R M' e
      exact ⟨h1, h2, fun x => by rw [h3 x]; simp⟩
    cases t with
    | range lo hi =>
      rw [endsFrom]
      refine ok_pure ⟨hM, ?_, fun x => ?_⟩
      · split
        · split
          · exact List.pairwise_singleton _ _
          · exact List.Pairwise.nil
        · exact List.Pairwise.nil
      · rw [range_iff]
        split
        · rename_i b hb
          split
          · rename_i hc; simp only [List.mem_singleton]; exact ⟨fun e => ⟨⟨b, hb, hc⟩, e⟩, fun h => h.2⟩
          · rename_i hc; simp only [List.not_mem_nil, false_iff]
            rintro ⟨⟨b', hb', h1, h2⟩, -⟩; rw [hb] at hb'; cases hb'; exact hc ⟨h1, h2⟩
        · rename_i hb; simp only [List.not_mem_nil, false_iff]
          rintro ⟨⟨b', hb', -⟩, -⟩; rw [hb] at hb'; cases hb'
    | text s =>
      rw [endsFrom]
      refine ok_pure ⟨hM, ?_, fun x => ?_⟩
      · split
        · exact List.pairwise_singleton _ _
        · exact List.Pairwise.nil
      · rw [text_iff]
        split
        · rename_i hc; simp only [List.mem_singleton]; exact ⟨fun e => ⟨hc, e⟩, fun h => h.2⟩
        · rename_i hc; simp only [List.not_mem_nil, false_iff]; exact fun h => hc h.1
    | exact s =>
      rw [endsFrom]
      refine ok_pure ⟨hM, ?_, fun x => ?_⟩
      · split
        · exact List.pairwise_singleton _ _
        · exact List.Pairwise.nil
      · rw [exact_iff]
        split
        · rename_i hc; simp only [List.mem_singleton]; exact ⟨fun e => ⟨hc, e⟩, fun h => h.2⟩
        · rename_i hc; simp only [List.not_mem_nil, false_iff]; exact fun h => hc h.1
    | ref i =>
      rw [endsFrom]
      refine ok_bind (Q := fun M0 M1 => M0 = M ∧ M1 = M) (ok_get ⟨rfl, rfl⟩) fun M0 M1 ⟨e1, e2⟩ => ?_
      subst e1 e2
      split
      · rename_i e he
        exact ok_pure ⟨hM, (hM p i e he).1, (hM p i e he).2⟩
      · split
        · exact ok_throw
        · rename_i u hu
          refine ok_bind (ih u p _ hM) fun e M1 h => ?_
          refine ok_bind (ok_modify (P := fun _ M2 => M2 = M1.modify p ((i, e) :: ·)) rfl) fun _ M2 h2 => ?_
          subst h2
          have hx : ∀ x, x ∈ e ↔ Matches g input (.ref i) p x := fun x => (h.2.2 x).trans (ref_iff' hu).symm
          exact ok_pure ⟨memoOk_modify h.1 h.2.1 hx, h.2.1, hx⟩
    | seq ts =>
      rw [endsFrom]
      have hseq : ∀ (ts : List Term) (R : Pos) (M : Memo), MemoOk g input M → Asc R →
          Ok (List.foldlM (fun R u => (fun u S => List.foldlM (fun R q => union R <$> endsFrom g input f u q) [] S)
            u R) R ts) M
            fun R' M' => MemoOk g input M' ∧ Asc R' ∧
              ∀ x, x ∈ R' ↔ ∃ a, a ∈ R ∧ Seq g input ts a x := by
        intro ts
        induction ts with
        | nil => intro R M hM hR; exact ok_pure ⟨hM, hR, fun x => by simp [seq_nil_iff]⟩
        | cons u ts ihs =>
          intro R M hM hR
          rw [List.foldlM_cons]
          refine ok_bind (hall u R M hM) fun R1 M1 h => ?_
          refine fun R' M' e => ?_
          obtain ⟨h1, h2, h3⟩ := ihs R1 M1 h.1 h.2.1 R' M' e
          refine ⟨h1, h2, fun x => ?_⟩
          rw [h3 x]
          simp only [seq_cons_iff]
          constructor
          · rintro ⟨a, ha, hs⟩
            obtain ⟨q, hq, hm⟩ := (h.2.2 a).1 ha
            exact ⟨q, hq, a, hm, hs⟩
          · rintro ⟨q, hq, a, hm, hs⟩
            exact ⟨a, (h.2.2 a).2 ⟨q, hq, hm⟩, hs⟩
      refine fun R M' e => ?_
      obtain ⟨h1, h2, h3⟩ := hseq ts [p] M hM (List.pairwise_singleton _ _) R M' e
      exact ⟨h1, h2, fun x => by rw [h3 x, seq_iff]; simp⟩
    | alt ts =>
      rw [endsFrom]
      refine fun R M' e => ?_
      obtain ⟨h1, h2, h3⟩ := ok_unionAll (fun u => endsFrom g input f u p) (fun u x => Matches g input u p x)
        (fun u M hM => ih u p M hM) ts [] M hM List.Pairwise.nil R M' e
      exact ⟨h1, h2, fun x => by rw [h3 x, alt_iff]; simp⟩
    | rep lo hi u =>
      rw [endsFrom]
      simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size, Nat.sub_zero, Nat.add_sub_cancel,
        Nat.div_one]
      refine ok_bind (Q := fun (r : MProd Nat (MProd Pos (List Nat))) M1 =>
          MemoOk g input M1 ∧ Asc r.snd.snd.reverse ∧ ∀ x, x ∈ r.snd.snd ↔ Matches g input (.rep lo hi u) p x)
        (ok_forIn_range _ (fun i r M1 => r.fst = i ∧ MemoOk g input M1 ∧
          RepInv g input u lo p r.fst r.snd.fst r.snd.snd ∧ ∀ h ∈ hi, r.fst ≤ h) _ ?step
          (lo + input.size + 1) 0 _ M
          ⟨rfl, hM, repInv_init, fun _ _ => Nat.zero_le _⟩ ?fin)
        fun r M1 h => ok_pure ⟨h.1, h.2.1, fun x => by rw [List.mem_reverse]; exact h.2.2 x⟩
      case fin =>
        rintro ⟨c, F, SD⟩ M1 ⟨hc, hM1, hI, hhi⟩
        dsimp only at hc hI hhi ⊢
        exact ⟨hM1, hI.2.1, repInv_final hI hhi (.inl (repInv_full hI (by omega)))⟩
      case step =>
        rintro i ⟨c, F, SD⟩ M1 ⟨hc, hM1, hI, hhi⟩
        simp only at hc hI hhi ⊢
        split
        · rename_i hbrk
          refine ok_pure ⟨hM1, hI.2.1, repInv_final hI hhi ?_⟩
          simp only [Bool.or_eq_true, List.isEmpty_iff, Option.any_eq_true, decide_eq_true_eq] at hbrk
          rcases hbrk with ⟨h, hh, hhc⟩ | h0
          · exact .inr ⟨h, hh, hhc⟩
          · exact .inl h0
        · rename_i hbrk
          simp only [Bool.or_eq_true, List.isEmpty_iff, Option.any_eq_true, decide_eq_true_eq, not_or, not_exists,
            not_and] at hbrk
          obtain ⟨hnhi, hF0⟩ := hbrk
          have hhi' : ∀ h ∈ hi, c + 1 ≤ h := fun h hh => by have := hnhi h hh; omega
          simp only [pure_bind]
          refine ok_bind (hall u F M1 hM1) fun next M2 hn => ?_
          split
          · rename_i hlt
            exact ok_pure ⟨show c + 1 = i + 1 by omega, hn.1, repInv_pre hI hlt hn.2.2 hn.2.1, hhi'⟩
          · rename_i hlt
            split
            · rename_i hb
              exact ok_pure ⟨show c + 1 = i + 1 by omega, hn.1, repInv_beyond hI hlt hF0 hn.2.2 hn.2.1 hb, hhi'⟩
            · rename_i hb
              exact ok_pure ⟨show c + 1 = i + 1 by omega, hn.1,
                repInv_merge hI hlt hF0 hn.2.2 hn.2.1 (Bool.eq_false_iff.2 hb), hhi'⟩

/-- **What `matches?` answers is whether the rule matches all of the bytes**, when it answers. -/
theorem matches?_ok {g : Array Term} {depth i : Nat} {bytes : List Nat} {b : Bool}
    (h : matches? g depth i bytes = .ok b) : b = true ↔ Matches g bytes.toArray (.ref i) 0 bytes.length := by
  have hok := ends_ok (g := g) (input := bytes.toArray) (fuel depth bytes.length) (.ref i) 0 _
    (memoOk_empty (g := g) (input := bytes.toArray) (bytes.length + 1))
  rcases hr : (endsFrom g bytes.toArray (fuel depth bytes.length) (.ref i) 0).run.run
    (Array.replicate (bytes.length + 1) []) with ⟨res, M'⟩
  simp only [matches?, StateT.run', List.size_toArray] at h
  cases res with
  | error s =>
    have : ExceptT.run (endsFrom g bytes.toArray (fuel depth bytes.length) (.ref i) 0)
      (Array.replicate (bytes.length + 1) []) = (Except.error s, M') := hr
    rw [this] at h
    cases h
  | ok e =>
    have : ExceptT.run (endsFrom g bytes.toArray (fuel depth bytes.length) (.ref i) 0)
      (Array.replicate (bytes.length + 1) []) = (Except.ok e, M') := hr
    rw [this] at h
    obtain ⟨-, -, he⟩ := hok e M' hr
    simp only [Except.map, Except.ok.injEq] at h
    rw [← h, List.contains_iff_mem, he]

/-! ## The premises can hold -/

theorem asc_witness : Asc [0, 1] := List.pairwise_pair.2 (by decide)

theorem memoOk_witness : MemoOk #[] #[] (Array.replicate 1 []) := memoOk_empty 1

theorem ok_witness : Ok (pure 0 : Run Nat) #[] (fun a _ => a = 0) := ok_pure rfl

theorem repInv_witness : RepInv #[] #[] (.seq []) 0 0 0 [0] [0] := repInv_init

end DN.News.AbnfEnds
