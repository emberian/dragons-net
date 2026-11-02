-- SPDX-License-Identifier: AGPL-3.0-or-later
import DN.News.RecoverSpec

/-!
# DN.News.RecoverSearch

The specification's searches by index: the first commit a later one repeats the number or Message-ID of
(`seqTwice_first`, `idTwice_first`), the first with a number not above (`notAbove_first`); and phases run in turn
until one asks or gives (`runPhases`), the step's end where `Steps` ends (`steps_end`).
-/

namespace DN.News.RecoverSpec

open DN.News.Journal DN.News.Recovery

/-- Whether a commit after the one at `i` has its `key`. -/
def dupAt {α : Type} [BEq α] (key : Commit → α) (cs : List Commit) (i : Nat) : Bool :=
  match cs.drop i with
  | c :: rest => rest.any (fun d => key d == key c)
  | [] => false

/-- The first of `0, …, k - 1` where `p` holds. -/
def firstIdx (p : Nat → Bool) (k : Nat) : Option Nat := (List.range k).find? p

theorem firstIdx_succ (p : Nat → Bool) (k : Nat) :
    firstIdx p (k + 1) = (firstIdx p k).or (if p k then some k else none) := by
  simp only [firstIdx, List.range_succ, List.find?_append, List.find?_cons, List.find?_nil]
  cases (List.range k).find? p <;> cases p k <;> rfl

theorem firstIdx_lt {p : Nat → Bool} {k i : Nat} (h : firstIdx p k = some i) : i < k ∧ p i = true :=
  ⟨List.mem_range.1 (List.mem_of_find?_eq_some h), List.find?_some h⟩

theorem dupAt_cons_zero {α : Type} [BEq α] (key : Commit → α) (c : Commit) (cs : List Commit) :
    dupAt key (c :: cs) 0 = cs.any (fun d => key d == key c) := rfl

theorem dupAt_cons_succ {α : Type} [BEq α] (key : Commit → α) (c : Commit) (cs : List Commit) (i : Nat) :
    dupAt key (c :: cs) (i + 1) = dupAt key cs i := rfl

/-- The first index of a test shifted by one: at 0, or one past the first of the rest. -/
theorem firstIdx_shift {p q : Nat → Bool} (hs : ∀ i, q (i + 1) = p i) :
    ∀ k, firstIdx q (k + 1) = if q 0 then some 0 else (firstIdx p k).map (· + 1)
  | 0 => by rw [firstIdx_succ]; cases q 0 <;> rfl
  | k + 1 => by
    rw [firstIdx_succ, firstIdx_shift hs k, firstIdx_succ, hs]
    cases q 0 <;> cases firstIdx p k <;> cases p k <;> rfl

/-- **A first repeated key by the index**: what `F` finds, the key of the first commit a later one repeats. -/
theorem twice_first {α : Type} [BEq α] (key : Commit → α) (F : List Commit → Option α) (h0 : F [] = none)
    (h1 : ∀ c cs, F (c :: cs) = if cs.any (fun d => key d == key c) then some (key c) else F cs) :
    ∀ cs : List Commit, F cs = (firstIdx (dupAt key cs) cs.length).bind fun i => cs[i]?.map key
  | [] => h0
  | c :: cs => by
    have ih := twice_first key F h0 h1 cs
    have hshift : ∀ k, firstIdx (dupAt key (c :: cs)) (k + 1) = if cs.any (fun d => key d == key c) then some 0
        else (firstIdx (dupAt key cs) k).map (· + 1) := firstIdx_shift (fun _ => rfl)
    rw [List.length_cons, hshift, h1]
    cases cs.any (fun d => key d == key c)
    · simp only [Bool.false_eq_true, if_false, ih]
      cases firstIdx (dupAt key cs) cs.length <;> rfl
    · simp

/-- Whether a commit after the one at `i` and below `j` has its `key`. -/
def hits {α : Type} [DecidableEq α] (key : Commit → α) (cs : List Commit) (i j : Nat) : Bool :=
  (List.range j).any fun k => decide (i < k) && decide (cs[k]?.map key = cs[i]?.map key)

theorem hits_succ {α : Type} [DecidableEq α] (key : Commit → α) (cs : List Commit) (i j : Nat) :
    hits key cs i (j + 1) = (hits key cs i j || (decide (i < j) && decide (cs[j]?.map key = cs[i]?.map key))) := by
  simp only [hits, List.range_succ, List.any_append, List.any_cons, List.any_nil, Bool.or_false]

theorem hits_le {α : Type} [DecidableEq α] (key : Commit → α) (cs : List Commit) (i j : Nat) (h : j ≤ i + 1) :
    hits key cs i j = false := by
  simp only [hits, List.any_eq_false, List.mem_range, Bool.and_eq_true, decide_eq_true_eq, not_and]
  intro k hk hik; omega

theorem dupAt_hits {α : Type} [BEq α] [LawfulBEq α] [DecidableEq α] (key : Commit → α) {cs : List Commit} {i : Nat}
    (hi : i < cs.length) : dupAt key cs i = hits key cs i cs.length := by
  have hd : cs.drop i = cs[i] :: cs.drop (i + 1) := List.drop_eq_getElem_cons hi
  simp only [dupAt, hd]
  apply Bool.eq_iff_iff.2
  simp only [hits, List.any_eq_true, List.mem_range, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq,
    List.getElem?_eq_getElem hi, Option.map_some]
  constructor
  · rintro ⟨d, hd, he⟩
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hd
    simp only [List.length_drop] at hk
    refine ⟨i + 1 + k, by omega, by omega, ?_⟩
    rw [List.getElem?_eq_getElem (by omega), Option.map_some, ← he, List.getElem_drop]
  · rintro ⟨k, hk, hik, he⟩
    rw [List.getElem?_eq_getElem hk, Option.map_some, Option.some.injEq] at he
    exact ⟨cs[k], List.mem_iff_getElem.2 ⟨k - (i + 1), by simp; omega, by simp [List.getElem_drop]; congr 1; omega⟩, he⟩

theorem seqTwice_first (cs : List Commit) :
    seqTwice? cs = (firstIdx (dupAt (·.seq) cs) cs.length).bind fun i => cs[i]?.map (·.seq) :=
  twice_first (·.seq) seqTwice? rfl (fun _ _ => rfl) cs

theorem idTwice_first (cs : List Commit) :
    idTwice? cs = (firstIdx (dupAt (·.messageId) cs) cs.length).bind fun i => cs[i]?.map (·.messageId) :=
  twice_first (·.messageId) idTwice? rfl (fun _ _ => rfl) cs

theorem firstIdx_some {p : Nat → Bool} : ∀ {n i : Nat}, firstIdx p n = some i →
    i < n ∧ p i = true ∧ firstIdx p i = none
  | 0, _, h => by simp [firstIdx] at h
  | n + 1, i, h => by
    rw [firstIdx_succ] at h
    cases e : firstIdx p n with
    | some j =>
      rw [e] at h; cases h
      obtain ⟨h1, h2, h3⟩ := firstIdx_some e
      exact ⟨by omega, h2, h3⟩
    | none =>
      rw [e] at h
      cases hp : p n with
      | false => simp [hp] at h
      | true =>
        simp only [hp, if_true, Option.none_or, Option.some.injEq] at h
        subst h; exact ⟨by omega, hp, e⟩

/-- A group of the commit at `i` whose number is not above what the commits before it gave. -/
def badGroup (cs : List Commit) (i : Nat) (g : Group) : Bool := decide (g.number ≤ highIn (cs.take i) g.name)

/-- Whether the commit at `i` has such a group. -/
def badAt (cs : List Commit) (i : Nat) : Bool := match cs[i]? with
  | some c => c.groups.any (badGroup cs i)
  | none => false

theorem notAbove_take (cs : List Commit) : ∀ k, k ≤ cs.length → firstIdx (badAt cs) k = none →
    notAbove? [] cs = notAbove? (cs.take k) (cs.drop k)
  | 0, _, _ => rfl
  | k + 1, hk, hf => by
    rw [firstIdx_succ] at hf
    have hk' : firstIdx (badAt cs) k = none := by
      cases e : firstIdx (badAt cs) k with
      | none => rfl
      | some _ => rw [e] at hf; cases hf
    have hb : badAt cs k = false := by
      rw [hk'] at hf
      cases e : badAt cs k with
      | false => rfl
      | true => rw [e] at hf; cases hf
    have hlt : k < cs.length := by omega
    rw [notAbove_take cs k (by omega) hk', List.drop_eq_getElem_cons hlt, notAbove?]
    have hnone : cs[k].groups.find? (fun g => decide (g.number ≤ highIn (cs.take k) g.name)) = none := by
      rw [List.find?_eq_none]
      intro g hg hbad
      have : badAt cs k = true := by
        simp only [badAt, List.getElem?_eq_getElem hlt, List.any_eq_true]
        exact ⟨g, hg, hbad⟩
      rw [hb] at this; cases this
    simp only [hnone]
    rw [List.take_succ_eq_append_getElem hlt]

/-- **`notAbove?` by the index**: the first group not above, of the first commit with one. -/
theorem notAbove_first (cs : List Commit) :
    notAbove? [] cs = (firstIdx (badAt cs) cs.length).bind fun i =>
      (cs[i]?.bind fun c => c.groups.find? (badGroup cs i)).map fun g => (g.name, g.number) := by
  cases e : firstIdx (badAt cs) cs.length with
  | none =>
    rw [notAbove_take cs cs.length (Nat.le_refl _) e, List.drop_length]; rfl
  | some i =>
    obtain ⟨hi, hp, hfi⟩ := firstIdx_some e
    have hlt : i < cs.length := hi
    rw [notAbove_take cs i (by omega) hfi, List.drop_eq_getElem_cons hlt, notAbove?]
    obtain ⟨g, hg, hbg⟩ : ∃ g ∈ cs[i].groups, badGroup cs i g = true := by
      simp only [badAt, List.getElem?_eq_getElem hlt, List.any_eq_true] at hp; exact hp
    cases hf : cs[i].groups.find? (badGroup cs i) with
    | none => exact absurd hbg (by rw [List.find?_eq_none] at hf; simpa using hf g hg)
    | some g' =>
      simp only [Option.bind_some, List.getElem?_eq_getElem hlt]
      show (match cs[i].groups.find? (badGroup cs i) with
        | some g => some (g.name, g.number)
        | none => notAbove? (cs.take i ++ [cs[i]]) (cs.drop (i + 1))) = _
      rw [hf]; rfl

theorem firstIdx_mono {p : Nat → Bool} {k i : Nat} (h : firstIdx p k = some i) :
    ∀ m, k ≤ m → firstIdx p m = some i := by
  intro m hm
  induction m with
  | zero => rw [Nat.le_zero.1 hm] at h; exact h
  | succ m ih =>
    rcases Nat.eq_or_lt_of_le hm with e | lt
    · rw [← e]; exact h
    · rw [firstIdx_succ, ih (by omega)]; rfl

theorem firstIdx_isSome (p : Nat → Bool) (n : Nat) :
    (firstIdx p n).isSome = (List.range n).any p := by
  unfold firstIdx
  apply Bool.eq_iff_iff.2
  rw [List.find?_isSome, List.any_eq_true]

theorem hits_mono {α : Type} [DecidableEq α] (key : Commit → α) (cs : List Commit) (i : Nat) {j j' : Nat}
    (h : hits key cs i j = true) (hj : j ≤ j') : hits key cs i j' = true := by
  simp only [hits, List.any_eq_true, List.mem_range] at h ⊢
  obtain ⟨x, hx, hp⟩ := h
  exact ⟨x, by omega, hp⟩

theorem bytes_take_succ_iff {a b : Bytes} (hab : a.length = b.length) {j : Nat} (hj : j < a.length) :
    (a.take (j + 1) = b.take (j + 1)) ↔ (a.take j = b.take j ∧ a[j] = b[j]'(by omega)) := by
  rw [List.take_succ_eq_append_getElem hj, List.take_succ_eq_append_getElem (by omega : j < b.length)]
  constructor
  · intro e
    have := List.append_inj e (by simp; omega)
    exact ⟨this.1, by simpa using this.2⟩
  · rintro ⟨e1, e2⟩; rw [e1, e2]

/-- The test `p` of the element at `t`, false past the end. -/
def testAt {α : Type} (p : α → Bool) (l : List α) (t : Nat) : Bool :=
  match l[t]? with
  | some a => p a
  | none => false

/-- **`find?` by the index**: the element at the first index where the test holds. -/
theorem find_first {α : Type} (p : α → Bool) : ∀ l : List α,
    l.find? p = (firstIdx (testAt p l) l.length).bind (l[·]?)
  | [] => rfl
  | a :: l => by
    have ih := find_first p l
    have hshift : ∀ k, firstIdx (testAt p (a :: l)) (k + 1) =
        if p a then some 0 else (firstIdx (testAt p l) k).map (· + 1) := firstIdx_shift (fun _ => rfl)
    rw [List.length_cons, hshift, List.find?_cons]
    cases hp : p a
    · simp only [Bool.false_eq_true, if_false, ih]
      cases firstIdx (testAt p l) l.length <;> rfl
    · rfl

/-- Phases from `r`, `i` of them while none asks or gives. -/
def runPhases (cfg : Config) (J : Bytes) : Nat → RSt → RSt × Option ROut
  | 0, r => (r, none)
  | i + 1, r => match runPhases cfg J i r with
    | (q, none) => phase cfg J q
    | p => p

theorem runPhases_succ_none {cfg : Config} {J : Bytes} {i : Nat} {r q : RSt}
    (h : runPhases cfg J i r = (q, none)) : runPhases cfg J (i + 1) r = phase cfg J q := by
  simp only [runPhases, h]

theorem runPhases_succ_some {cfg : Config} {J : Bytes} {i : Nat} {r : RSt} {p : RSt × Option ROut}
    (h : runPhases cfg J i r = p) (hs : p.2.isSome) : runPhases cfg J (i + 1) r = p := by
  obtain ⟨q, o⟩ := p
  cases o with
  | none => simp at hs
  | some o => simp only [runPhases, h]

theorem runPhases_shift {cfg : Config} {J : Bytes} {r r1 : RSt} (h : phase cfg J r = (r1, none)) :
    ∀ j, runPhases cfg J (j + 1) r = runPhases cfg J j r1
  | 0 => by simp only [runPhases, h]
  | j + 1 => by
    have ih := runPhases_shift h j
    simp only [runPhases] at ih ⊢
    rw [ih]

theorem steps_runPhases {cfg : Config} {J : Bytes} {r r' : RSt} {o : ROut} (h : Steps cfg J r r' o) :
    ∃ n, runPhases cfg J (n + 1) r = (r', some o) ∧ ∀ j, j ≤ n → (runPhases cfg J j r).2 = none := by
  induction h with
  | out e => exact ⟨0, by simp only [runPhases, e], fun j hj => by rw [Nat.le_zero.1 hj]; rfl⟩
  | @go r r1 r'' o e _ ih =>
    obtain ⟨n, hn, hb⟩ := ih
    refine ⟨n + 1, by rw [runPhases_shift e]; exact hn, fun j hj => ?_⟩
    cases j with
    | zero => rfl
    | succ j => rw [runPhases_shift e]; exact hb j (by omega)

theorem runPhases_after {cfg : Config} {J : Bytes} {r : RSt} {i : Nat} {p : RSt × Option ROut}
    (h : runPhases cfg J i r = p) (hs : p.2.isSome) : ∀ k, i ≤ k → runPhases cfg J k r = p := by
  intro k hk
  induction k with
  | zero => rw [Nat.le_zero.1 hk] at h; exact h
  | succ k ih =>
    rcases Nat.eq_or_lt_of_le hk with e | lt
    · rw [← e]; exact h
    · exact runPhases_succ_some (ih (by omega)) hs

/-- **The run a step makes**: the first `i` at which a phase asks or gives is the step's. -/
theorem steps_end {cfg : Config} {J : Bytes} {r r' : RSt} {o : ROut} (h : Steps cfg J r r' o)
    {i : Nat} (hi : (runPhases cfg J i r).2.isSome) : runPhases cfg J i r = (r', some o) := by
  obtain ⟨n, hn, hb⟩ := steps_runPhases h
  have : n + 1 ≤ i := by
    refine Nat.lt_of_not_le fun hle => ?_
    rw [hb i hle] at hi; simp at hi
  exact runPhases_after hn rfl i this

end DN.News.RecoverSpec
