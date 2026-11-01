-- SPDX-License-Identifier: AGPL-3.0-or-later
import DN.News.CommandSpec

/-!
# DN.News.WordsRun

A line's words as places: where each starts and how long it is (`spans`), the words `CommandSpec.words` gives being
the octets there (`words_spans`); the places as an octet-by-octet scan finds them (`scanTo`, `spans_end`), each within
the line and none empty (`spans_bound`, `spans_pos`).
-/

namespace DN.News.WordsRun

open DN.News DN.News.FrameSpec

/-- Where the words of `l` from position `q` on lie, as `(start, length)`, `cur` the start of a word not yet
ended. -/
def spansFrom : List Byte → Nat → Option Nat → List (Nat × Nat)
  | [], _, none => []
  | [], q, some st => [(st, q - st)]
  | b :: rest, q, none => if CommandSpec.isWS b then spansFrom rest (q + 1) none else spansFrom rest (q + 1) (some q)
  | b :: rest, q, some st =>
    if CommandSpec.isWS b then (st, q - st) :: spansFrom rest (q + 1) none else spansFrom rest (q + 1) (some st)

/-- The words' places in `l`. -/
def spans (l : List Byte) : List (Nat × Nat) := spansFrom l 0 none

/-- The octets a place names. -/
def cut (L : List Byte) (p : Nat × Nat) : List Byte := (L.drop p.1).take p.2

theorem spansFrom_words (L : List Byte) : ∀ (rest : List Byte) (q : Nat) (cur : List Byte) (st : Nat),
    L.drop q = rest → st + cur.length = q → (L.drop st).take cur.length = cur.reverse →
    CommandSpec.wordsFrom rest cur = (spansFrom rest q (if cur.isEmpty then none else some st)).map (cut L)
  | [], q, cur, st, hr, hq, hc => by
    cases cur with
    | nil => simp [CommandSpec.wordsFrom, spansFrom]
    | cons x xs =>
      simp only [CommandSpec.wordsFrom, List.isEmpty_cons, Bool.false_eq_true, if_false, spansFrom, List.map_cons,
        List.map_nil, cut]
      rw [← hc, show q - st = (x :: xs).length by omega]
  | b :: rest, q, cur, st, hr, hq, hc => by
    have hb : L[q]? = some b := by
      have := congrArg (·[0]?) hr
      simpa [List.getElem?_drop] using this
    have hr' : L.drop (q + 1) = rest := by
      rw [← List.drop_drop, hr]; rfl
    have hsnoc : (L.drop st).take (cur.length + 1) = cur.reverse ++ [b] := by
      rw [List.take_add_one, hc, List.getElem?_drop, show st + cur.length = q by omega, hb]; rfl
    by_cases hw : CommandSpec.isWS b
    · cases cur with
      | nil =>
        simp only [CommandSpec.wordsFrom, hw, if_true, List.isEmpty_nil, spansFrom]
        exact spansFrom_words L rest (q + 1) [] (q + 1) hr' (by simp) (by simp)
      | cons x xs =>
        simp only [CommandSpec.wordsFrom, hw, if_true, List.isEmpty_cons, Bool.false_eq_true, if_false, spansFrom,
          List.map_cons]
        rw [List.cons.injEq]
        refine ⟨?_, spansFrom_words L rest (q + 1) [] (q + 1) hr' (by simp) (by simp)⟩
        rw [cut, ← hc, show q - st = (x :: xs).length by omega]
    · cases cur with
      | nil =>
        obtain rfl : st = q := by simpa using hq
        simp only [CommandSpec.wordsFrom, hw, Bool.false_eq_true, if_false, List.isEmpty_nil, if_true, spansFrom]
        exact spansFrom_words L rest (st + 1) [b] st hr' (by simp) (by simpa using hsnoc)
      | cons x xs =>
        simp only [CommandSpec.wordsFrom, hw, Bool.false_eq_true, if_false, List.isEmpty_cons, spansFrom]
        exact spansFrom_words L rest (q + 1) (b :: x :: xs) st hr' (by simp at hq ⊢; omega)
          (by simpa using hsnoc)

/-- **The words are the octets their places name.** -/
theorem words_spans (l : List Byte) : CommandSpec.words l = (spans l).map (cut l) := by
  simpa using spansFrom_words l l 0 [] 0 rfl rfl rfl

/-- The words ended in the first `q` octets of `L`, and the start of one not yet ended. -/
def scanTo (L : List Byte) : Nat → List (Nat × Nat) × Option Nat
  | 0 => ([], none)
  | q + 1 =>
    let st := scanTo L q
    if CommandSpec.isWS (L.getD q 0) then
      (match st.2 with | none => st.1 | some s => st.1 ++ [(s, q - s)], none)
    else (st.1, some (st.2.getD q))

theorem scanTo_spans (L : List Byte) : ∀ q, q ≤ L.length →
    spans L = (scanTo L q).1 ++ spansFrom (L.drop q) q (scanTo L q).2
  | 0, _ => by simp [spans, scanTo]
  | q + 1, hq => by
    have ih := scanTo_spans L q (by omega)
    have hd : L.drop q = L.getD q 0 :: L.drop (q + 1) := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), Option.getD_some,
        List.drop_eq_getElem_cons (by omega)]
    rw [ih, hd]
    simp only [scanTo]
    generalize L.getD q 0 = b
    cases h2 : (scanTo L q).2 with
    | none => by_cases hw : CommandSpec.isWS b <;> simp [spansFrom, hw]
    | some s => by_cases hw : CommandSpec.isWS b <;> simp [spansFrom, hw]

/-- At the end, the words' places: those ended, and the last if it runs to the end. -/
theorem spans_end (L : List Byte) : spans L =
    (scanTo L L.length).1 ++ ((scanTo L L.length).2.map fun s => (s, L.length - s)).toList := by
  rw [scanTo_spans L L.length (Nat.le_refl _), List.drop_length]
  cases (scanTo L L.length).2 <;> simp [spansFrom]

theorem scanTo_le (L : List Byte) : ∀ q, (∀ p ∈ (scanTo L q).1, p.1 + p.2 ≤ q) ∧
    (∀ st, (scanTo L q).2 = some st → st < q) ∧ (scanTo L q).1.length + (if (scanTo L q).2.isSome then 1 else 0) ≤ q
  | 0 => by simp [scanTo]
  | q + 1 => by
    obtain ⟨h1, h2, h3⟩ := scanTo_le L q
    simp only [scanTo]
    split
    · cases h : (scanTo L q).2 with
      | none => simp only [h] at h3; exact ⟨fun p hp => by have := h1 p hp; omega, by simp, by simp; omega⟩
      | some s =>
        have := h2 s h
        simp only [h, Option.isSome_some, if_true] at h3
        refine ⟨fun p hp => ?_, by simp, by simp; omega⟩
        rcases List.mem_append.mp hp with hp | hp
        · have := h1 p hp; omega
        · simp at hp; subst hp; simp; omega
    · cases h : (scanTo L q).2 with
      | none => simp only [h] at h3; exact ⟨fun p hp => by have := h1 p hp; omega, by simp, by simp; omega⟩
      | some s =>
        have := h2 s h
        simp only [h, Option.isSome_some, if_true] at h3
        exact ⟨fun p hp => by have := h1 p hp; omega, by simp; omega, by simp; omega⟩

theorem spans_bound (L : List Byte) : ∀ p ∈ spans L, p.1 + p.2 ≤ L.length := by
  intro p hp
  rw [spans_end] at hp
  obtain ⟨h1, h2, -⟩ := scanTo_le L L.length
  rcases List.mem_append.mp hp with h | h
  · exact h1 p h
  · cases e : (scanTo L L.length).2 with
    | none => rw [e] at h; simp at h
    | some st => rw [e] at h; simp at h; subst h; have := h2 st e; simp; omega

theorem cut_length {L : List Byte} {p : Nat × Nat} (h : p.1 + p.2 ≤ L.length) : (cut L p).length = p.2 := by
  simp [cut]; omega

theorem cut_get {L : List Byte} {p : Nat × Nat} (h : p.1 + p.2 ≤ L.length) (i : Nat) (hi : i < (cut L p).length) :
    (cut L p)[i] = L[p.1 + i]'(by rw [cut_length h] at hi; omega) := by
  simp [cut]

theorem spans_length (L : List Byte) : (spans L).length ≤ L.length := by
  rw [spans_end]
  obtain ⟨-, -, h⟩ := scanTo_le L L.length
  cases e : (scanTo L L.length).2 <;> simp [e] at h ⊢ <;> omega

theorem scanTo_pos (L : List Byte) : ∀ q, ∀ p ∈ (scanTo L q).1, 1 ≤ p.2
  | 0 => by simp [scanTo]
  | q + 1 => by
    have h1 := scanTo_pos L q
    have h2 := (scanTo_le L q).2.1
    simp only [scanTo]
    split
    · cases h : (scanTo L q).2 with
      | none => exact h1
      | some s =>
        have := h2 s h
        intro p hp
        rcases List.mem_append.mp hp with hp | hp
        · exact h1 p hp
        · simp at hp; subst hp; simp; omega
    · exact h1

/-- The line's words are not empty. -/
theorem spans_pos (L : List Byte) : ∀ p ∈ spans L, 1 ≤ p.2 := by
  intro p hp
  rw [spans_end] at hp
  rcases List.mem_append.mp hp with h | h
  · exact scanTo_pos L L.length p h
  · cases e : (scanTo L L.length).2 with
    | none => rw [e] at h; simp at h
    | some st =>
      rw [e] at h; simp at h; subst h
      have := (scanTo_le L L.length).2.1 st e
      simp; omega

theorem spans_getD_le (L : List Byte) (j : Nat) :
    ((spans L).getD j (0, 0)).1 ≤ L.length ∧ ((spans L).getD j (0, 0)).2 ≤ L.length := by
  rw [List.getD_eq_getElem?_getD]
  cases h : (spans L)[j]? with
  | none => simp
  | some p =>
    have := spans_bound L p (List.mem_of_getElem? h)
    simp only [Option.getD_some]; omega

/-- The place of a word the line has. -/
theorem spans_getD_mem {L : List Byte} {j : Nat} (h : j < (spans L).length) : (spans L).getD j (0, 0) ∈ spans L := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]; simp

end DN.News.WordsRun
