-- SPDX-License-Identifier: AGPL-3.0-or-later
import DN.News.CommandSpec

/-!
# DN.News.CharsRun

Octet checks by characters, as the session makes them, against `CommandSpec`. A check taking each character at its lead
octet, continuations after, is `CommandSpec.chars` (`utf8_run`). So group names and wildmats pass exactly when
`CommandSpec` says (`exactChars_run`, `wildmat_run`).
-/

namespace DN.News.CharsRun

open DN.News DN.News.FrameSpec
open DN.News.CommandSpec (charLength charsFrom chars inRange isTail)

/-! ## UTF-8, octet by octet -/

/-- A lead octet of UTF-8 past US-ASCII: how many continuation octets it needs, the first one's range (RFC 3629 §4). -/
def lead (b : Byte) : Option (Nat × Nat × Nat) :=
  if 194 ≤ b.toNat ∧ b.toNat ≤ 223 then some (1, 128, 191)
  else if b.toNat = 224 then some (2, 160, 191)
  else if (225 ≤ b.toNat ∧ b.toNat ≤ 236) ∨ (238 ≤ b.toNat ∧ b.toNat ≤ 239) then some (2, 128, 191)
  else if b.toNat = 237 then some (2, 128, 159)
  else if b.toNat = 240 then some (3, 144, 191)
  else if 241 ≤ b.toNat ∧ b.toNat ≤ 243 then some (3, 128, 191)
  else if b.toNat = 244 then some (3, 128, 143)
  else none

theorem lead_bounds {b : Byte} {n lo hi : Nat} (h : lead b = some (n, lo, hi)) :
    1 ≤ n ∧ n ≤ 3 ∧ lo < 256 ∧ hi < 256 := by
  simp only [lead] at h
  generalize b.toNat = x at h
  by_cases h1 : 194 ≤ x ∧ x ≤ 223
  · rw [if_pos h1] at h; cases h; decide
  rw [if_neg h1] at h
  by_cases h2 : x = 224
  · rw [if_pos h2] at h; cases h; decide
  rw [if_neg h2] at h
  by_cases h3 : (225 ≤ x ∧ x ≤ 236) ∨ (238 ≤ x ∧ x ≤ 239)
  · rw [if_pos h3] at h; cases h; decide
  rw [if_neg h3] at h
  by_cases h4 : x = 237
  · rw [if_pos h4] at h; cases h; decide
  rw [if_neg h4] at h
  by_cases h5 : x = 240
  · rw [if_pos h5] at h; cases h; decide
  rw [if_neg h5] at h
  by_cases h6 : 241 ≤ x ∧ x ≤ 243
  · rw [if_pos h6] at h; cases h; decide
  rw [if_neg h6] at h
  by_cases h7 : x = 244
  · rw [if_pos h7] at h; cases h; decide
  rw [if_neg h7] at h
  cases h

/-- `n` continuation octets, the first in `[lo, hi]`, the rest in `[128, 191]`: what follows them. -/
def tails : Nat → Nat → Nat → List Byte → Option (List Byte)
  | 0, _, _, bs => some bs
  | _ + 1, _, _, [] => none
  | n + 1, lo, hi, b :: rest => if lo ≤ b.toNat ∧ b.toNat ≤ hi then tails n 128 191 rest else none

theorem tails_drop : ∀ (n lo hi : Nat) (bs r : List Byte), tails n lo hi bs = some r → r = bs.drop n ∧ n ≤ bs.length
  | 0, _, _, bs, r, h => by simp [tails] at h; exact ⟨h.symm, by simp⟩
  | _ + 1, _, _, [], r, h => by simp [tails] at h
  | n + 1, lo, hi, b :: rest, r, h => by
    simp only [tails] at h
    split at h
    · obtain ⟨e, hl⟩ := tails_drop n 128 191 rest r h
      exact ⟨by simpa using e, by simp; omega⟩
    · cases h

theorem ite_and_none {α : Type} {p q : Prop} [Decidable p] [Decidable q] (a : Option α) :
    (if p ∧ q then a else none) = if p then (if q then a else none) else none := by
  by_cases hp : p <;> simp [hp]

/-- **The length of a character is its lead's and its continuation octets'.** -/
theorem charLength_lead (a : Byte) (rest : List Byte) (ha : 128 ≤ a.toNat) :
    charLength (a :: rest) =
      (lead a).bind fun (n, lo, hi) => (tails n lo hi rest).map fun _ => n + 1 := by
  have hlt := a.isLt
  simp only [charLength, lead, inRange, isTail, Nat.not_lt.mpr ha, if_false, Bool.and_eq_true,
    decide_eq_true_eq, beq_iff_eq, Bool.or_eq_true]
  generalize a.toNat = n at *
  rcases rest with _ | ⟨b, _ | ⟨c, _ | ⟨d, r⟩⟩⟩ <;>
  · by_cases h1 : 194 ≤ n ∧ n ≤ 223
    · simp [h1, tails, ite_and_none, apply_ite (Option.map _), Option.map_none]
    by_cases h2 : n = 224
    · subst h2; simp [tails, ite_and_none, apply_ite (Option.map _), Option.map_none]
    by_cases h3 : (225 ≤ n ∧ n ≤ 236) ∨ (238 ≤ n ∧ n ≤ 239)
    · simp [h1, h2, h3, tails, ite_and_none, apply_ite (Option.map _), Option.map_none]
    by_cases h4 : n = 237
    · subst h4; simp [tails, ite_and_none, apply_ite (Option.map _), Option.map_none]
    by_cases h5 : n = 240
    · subst h5; simp [tails, ite_and_none, apply_ite (Option.map _), Option.map_none]
    by_cases h6 : 241 ≤ n ∧ n ≤ 243
    · simp [h1, h2, h3, h4, h5, h6, tails, ite_and_none, apply_ite (Option.map _), Option.map_none]
    by_cases h7 : n = 244
    · subst h7; simp [tails, ite_and_none, apply_ite (Option.map _), Option.map_none]
    simp [h1, h2, h3, h4, h5, h6, h7]

theorem charLength_ascii (a : Byte) (rest : List Byte) (ha : a.toNat < 128) : charLength (a :: rest) = some 1 := by
  simp [charLength, ha]

theorem charLength_pos {bs : List Byte} {k : Nat} (h : charLength bs = some k) : 1 ≤ k := by
  match bs, h with
  | a :: rest, h =>
    by_cases ha : a.toNat < 128
    · rw [charLength_ascii a rest ha] at h
      cases h
      exact Nat.le_refl _
    · rw [charLength_lead a rest (by omega)] at h
      cases hl : lead a with
      | none => simp [hl] at h
      | some x =>
        obtain ⟨n, lo, hi⟩ := x
        simp only [hl, Option.bind_some] at h
        cases ht : tails n lo hi rest with
        | none => simp [ht] at h
        | some r => simp [ht] at h; omega

theorem charsFrom_succ (f : Nat) (a : Byte) (rest : List Byte) :
    charsFrom (f + 1) (a :: rest) = (charLength (a :: rest)).bind fun k =>
      (charsFrom f ((a :: rest).drop k)).map ((a :: rest).take k :: ·) := by
  simp only [charsFrom]
  cases charLength (a :: rest) with
  | none => rfl
  | some k =>
    simp only [Option.bind_some]
    cases h : charsFrom f ((a :: rest).drop k) <;> simp [h]

/-- Fuel of as many as the octets is enough: more changes nothing. -/
theorem charsFrom_eq : ∀ (f g : Nat) (bs : List Byte), bs.length ≤ f → bs.length ≤ g →
    charsFrom f bs = charsFrom g bs
  | 0, g, bs, hf, hg => by
    have : bs = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst this
    cases g <;> rfl
  | f + 1, g, [], _, _ => by cases g <;> rfl
  | f + 1, 0, a :: rest, _, hg => by simp at hg
  | f + 1, g + 1, a :: rest, hf, hg => by
    rw [charsFrom_succ, charsFrom_succ]
    cases hk : charLength (a :: rest) with
    | none => rfl
    | some k =>
      have := charLength_pos hk
      simp only [Option.bind_some]
      rw [charsFrom_eq f g _ (by simp at hf ⊢; omega) (by simp at hg ⊢; omega)]

/-- The characters of octets, the first by its length. -/
theorem chars_cons {a : Byte} {rest : List Byte} {k : Nat} (hk : charLength (a :: rest) = some k) :
    chars (a :: rest) = (chars ((a :: rest).drop k)).map ((a :: rest).take k :: ·) := by
  have := charLength_pos hk
  show charsFrom (rest.length + 1) (a :: rest) = _
  rw [charsFrom_succ, hk, Option.bind_some,
    charsFrom_eq rest.length ((a :: rest).drop k).length _ (by simp; omega) (Nat.le_refl _)]
  rfl

theorem chars_none {a : Byte} {rest : List Byte} (hk : charLength (a :: rest) = none) :
    chars (a :: rest) = none := by
  show charsFrom (rest.length + 1) (a :: rest) = none
  rw [charsFrom_succ, hk]
  rfl

/-- **A check of octets by characters**: `asc` takes a US-ASCII character and `multi` one past it, at its lead octet.
UTF-8's `nd` continuation octets are checked after it, the first from `clo` to `chi`. -/
def bRun {S : Type} (asc : S → Byte → Option S) (multi : S → Option S) :
    S → Nat → Nat → Nat → List Byte → Option S
  | st, nd, _, _, [] => if nd = 0 then some st else none
  | st, nd, clo, chi, b :: rest =>
    if 0 < nd then
      (if b.toNat < clo ∨ chi < b.toNat then none else bRun asc multi st (nd - 1) 128 191 rest)
    else if b.toNat < 128 then (asc st b).bind fun st' => bRun asc multi st' 0 128 191 rest
    else match lead b with
      | some (n, lo, hi) => (multi st).bind fun st' => bRun asc multi st' n lo hi rest
      | none => none

/-- The same, a character at a time. -/
def cStep {S : Type} (asc : S → Byte → Option S) (multi : S → Option S) (st : S) : List Byte → Option S
  | [b] => asc st b
  | _ => multi st

section
variable {S : Type} (asc : S → Byte → Option S) (multi : S → Option S)

theorem bRun_zero (st : S) (lo hi : Nat) (bs : List Byte) :
    bRun asc multi st 0 lo hi bs = bRun asc multi st 0 128 191 bs := by
  cases bs <;> simp [bRun]

theorem bRun_tails : ∀ (n : Nat) (st : S) (lo hi : Nat) (bs : List Byte),
    bRun asc multi st n lo hi bs = (tails n lo hi bs).bind (bRun asc multi st 0 128 191)
  | 0, st, lo, hi, bs => by simp [tails, bRun_zero]
  | n + 1, st, lo, hi, [] => by simp [bRun, tails]
  | n + 1, st, lo, hi, b :: rest => by
    simp only [bRun, tails, Nat.zero_lt_succ, if_true, Nat.add_sub_cancel]
    rw [bRun_tails n st 128 191 rest]
    by_cases h : lo ≤ b.toNat ∧ b.toNat ≤ hi
    · rw [if_neg (by omega), if_pos h]
    · rw [if_pos (by omega), if_neg h]
      rfl

/-- **The check by octets is the check by characters.** -/
theorem utf8_run : ∀ (bs : List Byte) (st : S),
    bRun asc multi st 0 128 191 bs = (chars bs).bind fun cs => cs.foldlM (cStep asc multi) st
  | [], st => by simp [bRun, chars, charsFrom]
  | a :: rest, st => by
    by_cases ha : a.toNat < 128
    · rw [chars_cons (charLength_ascii a rest ha)]
      have e1 : bRun asc multi st 0 128 191 (a :: rest) =
          (asc st a).bind fun st' => bRun asc multi st' 0 128 191 rest := by
        simp [bRun, ha]
      rw [e1]
      show _ = ((chars rest).map ([a] :: ·)).bind _
      cases h : asc st a with
      | none =>
        cases chars rest with
        | none => rfl
        | some cs => simp [List.foldlM_cons, cStep, h]
      | some st' =>
        rw [Option.bind_some, utf8_run rest st']
        cases chars rest with
        | none => rfl
        | some cs => simp [List.foldlM_cons, cStep, h]
    · have hl := charLength_lead a rest (by omega)
      have e1 : bRun asc multi st 0 128 191 (a :: rest) =
          match lead a with
          | some (n, lo, hi) => (multi st).bind fun st' => bRun asc multi st' n lo hi rest
          | none => none := by
        simp [bRun, ha]
      rw [e1]
      cases hld : lead a with
      | none =>
        rw [hld] at hl
        rw [chars_none (by simpa using hl)]
        rfl
      | some x =>
        obtain ⟨n, lo, hi⟩ := x
        simp only [hld, Option.bind_some] at hl ⊢
        cases ht : tails n lo hi rest with
        | none =>
          rw [ht] at hl
          rw [chars_none (by simpa using hl)]
          cases multi st with
          | none => rfl
          | some st' => simp [bRun_tails, ht]
        | some r =>
          obtain ⟨hr, hn⟩ := tails_drop n lo hi rest r ht
          rw [ht] at hl
          rw [chars_cons (by simpa using hl)]
          have hd : (a :: rest).drop (n + 1) = r := by rw [hr]; rfl
          have hpos : 1 ≤ n := (lead_bounds hld).1
          have hstep : cStep asc multi st (a :: rest.take n) = multi st := by
            obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
            cases rest with
            | nil => simp at hn
            | cons b r' => rfl
          rw [hd]
          cases hm : multi st with
          | none =>
            cases chars r with
            | none => rfl
            | some cs => simp [hstep, hm]
          | some st' =>
            have : r.length < (a :: rest).length := by rw [hr]; simp; omega
            rw [Option.bind_some, bRun_tails, ht, Option.bind_some, utf8_run r st']
            cases chars r with
            | none => rfl
            | some cs => simp [hstep, hm]
termination_by bs => bs.length

end

/-! ## A newsgroup's name -/

/-- A character of US-ASCII in a name: `wildmat-exact` or not. -/
def gAsc (_ : Unit) (b : Byte) : Option Unit := if CommandSpec.isExactAscii b then some () else none

/-- A character past US-ASCII in a name. -/
def gMulti (_ : Unit) : Option Unit := some ()

/-- **A name's characters are `wildmat-exact`** exactly when the check by octets passes. -/
theorem exactChars_run (w : List Byte) :
    CommandSpec.exactChars w = (bRun gAsc gMulti () 0 128 191 w).isSome := by
  rw [utf8_run]
  unfold CommandSpec.exactChars
  cases chars w with
  | none => rfl
  | some cs =>
    simp only [Option.any_some, Option.bind_some]
    induction cs with
    | nil => rfl
    | cons c cs ih =>
      rw [List.all_cons, List.foldlM_cons]
      match c with
      | [b] =>
        simp only [cStep, gAsc, List.length_singleton, bne_self_eq_false, Bool.false_or, List.all_cons,
          List.all_nil, Bool.and_true]
        cases CommandSpec.isExactAscii b
        · rfl
        · exact ih
      | [] => simpa [cStep, gMulti] using ih
      | a :: b :: r => simpa [cStep, gMulti] using ih

/-! ## A wildmat -/

/-- A character of US-ASCII in a wildmat, the pattern's items so far and whether a `!` may stand. -/
def wAsc (st : Nat × Bool) (b : Byte) : Option (Nat × Bool) :=
  if b.toNat = 44 then (if st.1 = 0 then none else some (0, true))
  else if b.toNat = 33 then (if st.2 then some (st.1, false) else none)
  else if CommandSpec.isExactAscii b || b.toNat = 42 || b.toNat = 63 then some (st.1 + 1, false) else none

/-- …and one past US-ASCII. -/
def wMulti (st : Nat × Bool) : Option (Nat × Bool) := some (st.1 + 1, false)

/-- Whether a run ended on a pattern of an item or more. -/
def okItems : Option (Nat × Bool) → Bool
  | some (k, _) => k != 0
  | none => false

def itemOK (c : List Byte) : Bool := (CommandSpec.itemOf c).isSome

theorem ascii_comma : CommandSpec.ascii "," = [44#8] := by decide

theorem ascii_bang : CommandSpec.ascii "!" = [33#8] := by decide

theorem mapM_isSome {α β : Type} (f : α → Option β) : ∀ l : List α, (l.mapM f).isSome = l.all fun x => (f x).isSome
  | [] => rfl
  | x :: xs => by
    rw [List.mapM_cons, List.all_cons]
    cases f x with
    | none => rfl
    | some y =>
      simp only [Option.isSome_some, Bool.true_and, ← mapM_isSome f xs]
      cases xs.mapM f <;> rfl

theorem byte_ext {b : Byte} {n : Nat} (hn : n < 256) : b = BitVec.ofNat 8 n ↔ b.toNat = n := by
  constructor
  · rintro rfl; simp [Nat.mod_eq_of_lt hn]
  · intro h; apply BitVec.eq_of_toNat_eq; simp [h, Nat.mod_eq_of_lt hn]

theorem itemOK_single (x : Byte) :
    itemOK [x] = (CommandSpec.isExactAscii x || decide (x.toNat = 42) || decide (x.toNat = 63)) := by
  have h42 : CommandSpec.ascii "*" = [42#8] := by decide
  have h63 : CommandSpec.ascii "?" = [63#8] := by decide
  simp only [itemOK, CommandSpec.itemOf, h42, h63, List.cons.injEq, and_true,
    byte_ext (by decide : 42 < 256), byte_ext (by decide : 63 < 256)]
  by_cases a : x.toNat = 42 <;> by_cases b : x.toNat = 63 <;> simp [a, b]
  split <;> simp_all

theorem itemOK_long (c : List Byte) (h : c.length ≠ 1) : itemOK c = true := by
  have h42 : CommandSpec.ascii "*" = [42#8] := by decide
  have h63 : CommandSpec.ascii "?" = [63#8] := by decide
  have n1 : c ≠ [42#8] := fun e => h (by rw [e]; rfl)
  have n2 : c ≠ [63#8] := fun e => h (by rw [e]; rfl)
  simp [itemOK, CommandSpec.itemOf, h42, h63, n1, n2, h]

/-- **A character, neither a comma nor a `!` where one may stand**: one item more, if it can be one. -/
theorem wStep_item (st : Nat × Bool) (c : List Byte) (h44 : c ≠ [44#8]) (h33 : c ≠ [33#8] ∨ st.2 = false) :
    cStep wAsc wMulti st c = if itemOK c then some (st.1 + 1, false) else none := by
  match c, h44, h33 with
  | [x], h44, h33 =>
    have n44 : x.toNat ≠ 44 := fun e => h44 (by rw [(byte_ext (by decide)).mpr e])
    rw [itemOK_single]
    simp only [cStep, wAsc, n44, if_false]
    by_cases n33 : x.toNat = 33
    · have hb : st.2 = false := h33.resolve_left (fun h => h (by rw [(byte_ext (by decide)).mpr n33]))
      have he : CommandSpec.isExactAscii x = false := by simp [CommandSpec.isExactAscii, n33]
      simp [n33, hb, he]
    · simp [n33]
  | [], _, _ => rw [itemOK_long _ (by simp)]; rfl
  | a :: b :: r, _, _ => rw [itemOK_long _ (by simp)]; rfl

/-- **A pattern's items after the first**: as many more as there are, if each can be one. -/
theorem items_run : ∀ (g : List (List Byte)) (k : Nat), (∀ c ∈ g, c ≠ [44#8]) →
    g.foldlM (cStep wAsc wMulti) (k, false) = if g.all itemOK then some (k + g.length, false) else none
  | [], k, _ => by simp
  | c :: g, k, h => by
    rw [List.foldlM_cons, wStep_item (k, false) c (h c (by simp)) (Or.inr rfl), List.all_cons]
    cases hc : itemOK c with
    | false => rfl
    | true =>
      simp only [if_true, Bool.true_and]
      show List.foldlM (cStep wAsc wMulti) (k + 1, false) g = _
      rw [items_run g (k + 1) fun c' hc' => h c' (by simp [hc'])]
      simp only [List.length_cons]
      rw [show k + 1 + g.length = k + (g.length + 1) by omega]

theorem mapM_itemOf (g : List (List Byte)) : (g.mapM CommandSpec.itemOf).isSome = g.all itemOK :=
  mapM_isSome _ g

theorem patternOf_isSome (neg : Bool) (cs : List (List Byte)) :
    (CommandSpec.patternOf neg cs).isSome =
      (!(if (neg && cs.head? == some [33#8]) = true then cs.tail else cs).isEmpty &&
        (if (neg && cs.head? == some [33#8]) = true then cs.tail else cs).all itemOK) := by
  by_cases hc : (neg && cs.head? == some [33#8]) = true
  · simp only [CommandSpec.patternOf, ascii_bang, hc, if_true]
    cases hr : cs.tail.isEmpty
    · simp only [Bool.false_eq_true, if_false, Bool.not_false, Bool.true_and, ← mapM_itemOf]
      cases cs.tail.mapM CommandSpec.itemOf <;> rfl
    · simp
  · simp only [CommandSpec.patternOf, ascii_bang, hc, if_false, Bool.false_eq_true]
    cases hr : cs.isEmpty
    · simp only [Bool.false_eq_true, if_false, Bool.not_false, Bool.true_and, ← mapM_itemOf]
      cases cs.mapM CommandSpec.itemOf <;> rfl
    · simp

/-- **A pattern**: its items, a `!` before them where one may stand, at least one. -/
theorem group_run (neg : Bool) (g : List (List Byte)) (h : ∀ c ∈ g, c ≠ [44#8]) :
    okItems (g.foldlM (cStep wAsc wMulti) (0, neg)) = (CommandSpec.patternOf neg g).isSome := by
  rw [patternOf_isSome]
  match g, h with
  | [], _ => simp [okItems]
  | c :: g', h =>
    have hg' : ∀ c' ∈ g', c' ≠ [44#8] := fun c' hc' => h c' (by simp [hc'])
    by_cases hb : neg = true ∧ c = [33#8]
    · obtain ⟨rfl, rfl⟩ := hb
      have hs : cStep wAsc wMulti (0, true) [33#8] = some (0, false) := by decide
      rw [List.foldlM_cons, hs]
      show okItems (List.foldlM (cStep wAsc wMulti) (0, false) g') = _
      rw [items_run g' 0 hg']
      simp only [List.head?_cons, beq_self_eq_true, Bool.and_self, if_true, List.tail_cons]
      cases hall : g'.all itemOK
      · simp [okItems]
      · cases g' <;> simp [okItems]
    · have hc : (neg && (c :: g').head? == some [33#8]) = false := by
        simp only [List.head?_cons, Bool.and_eq_false_iff]
        by_cases hn : neg = true
        · right
          simp only [beq_eq_false_iff_ne, ne_eq, Option.some.injEq]
          exact fun e => hb ⟨hn, e⟩
        · left
          simpa using hn
      simp only [hc, Bool.false_eq_true, if_false, List.isEmpty_cons, Bool.not_false, Bool.true_and,
        List.all_cons]
      by_cases h33 : c = [33#8]
      · subst h33
        have hn : neg = false := by simpa [hb] using hb
        subst hn
        have hs : cStep wAsc wMulti (0, false) [33#8] = none := by decide
        have hi : itemOK [33#8] = false := by decide
        rw [List.foldlM_cons, hs, hi]
        rfl
      · rw [List.foldlM_cons, wStep_item (0, neg) c (h c (by simp)) (Or.inl h33)]
        cases hi : itemOK c
        · rfl
        · show okItems (List.foldlM (cStep wAsc wMulti) (0 + 1, false) g') = _
          rw [items_run g' (0 + 1) hg']
          cases g'.all itemOK <;> simp [okItems]

theorem first_sep {α : Type} [DecidableEq α] (sep : α) : ∀ cs : List α,
    sep ∉ cs ∨ ∃ g r, cs = g ++ sep :: r ∧ sep ∉ g
  | [] => Or.inl (by simp)
  | x :: xs => by
    by_cases hx : x = sep
    · exact Or.inr ⟨[], xs, by simp [hx], by simp⟩
    · rcases first_sep sep xs with h | ⟨g, r, h, hn⟩
      · exact Or.inl (by simp [h, Ne.symm hx])
      · exact Or.inr ⟨x :: g, r, by simp [h], by simp [hn, Ne.symm hx]⟩

/-- **A wildmat's characters**: comma-parted patterns, as `CommandSpec.wildmat?` reads them. That is exactly when their
run ends on a pattern of an item or more. -/
theorem wildmat_chars (neg : Bool) (cs : List (List Byte)) :
    okItems (cs.foldlM (cStep wAsc wMulti) (0, neg)) =
      (match cs.splitOn [44#8] with
       | first :: rest =>
         (CommandSpec.patternOf neg first).isSome && rest.all fun g => (CommandSpec.patternOf true g).isSome
       | [] => false) := by
  rcases first_sep [44#8] cs with h | ⟨g, r, rfl, hn⟩
  · rw [List.splitOn_eq_singleton h, group_run neg cs (fun c hc e => h (e ▸ hc))]
    simp
  · have hlen : r.length < (g ++ [44#8] :: r).length := by simp; omega
    have ih := wildmat_chars true r
    have hg := group_run neg g (fun c hc e => hn (e ▸ hc))
    rw [List.splitOn_append_cons_self_of_not_mem hn, List.foldlM_append]
    obtain ⟨first', rest', hfr⟩ := List.exists_cons_of_ne_nil (List.splitOn_ne_nil [44#8] r)
    rw [hfr] at ih ⊢
    dsimp only at ih
    simp only [List.all_cons]
    rw [← hg, ← ih]
    cases hgr : g.foldlM (cStep wAsc wMulti) (0, neg) with
    | none => rfl
    | some st =>
      obtain ⟨k, bg⟩ := st
      show okItems (List.foldlM (cStep wAsc wMulti) (k, bg) ([44#8] :: r)) = _
      rw [List.foldlM_cons]
      by_cases hk : k = 0
      · subst hk
        have : cStep wAsc wMulti (0, bg) [44#8] = none := by simp [cStep, wAsc]
        rw [this]
        rfl
      · have : cStep wAsc wMulti (k, bg) [44#8] = some (0, true) := by simp [cStep, wAsc, hk]
        rw [this]
        simp [okItems, hk]
termination_by cs.length

/-- **The wildmat check by octets is `CommandSpec.wildmat?`**. -/
theorem wildmat_run (w : List Byte) :
    okItems (bRun wAsc wMulti (0, false) 0 128 191 w) = (CommandSpec.wildmat? w).isSome := by
  rw [utf8_run]
  cases hc : chars w with
  | none => simp [CommandSpec.wildmat?, hc, okItems]
  | some cs =>
    simp only [CommandSpec.wildmat?, hc, ascii_comma, Option.bind_eq_bind, Option.bind_some]
    rw [wildmat_chars false cs]
    obtain ⟨first, rest, hfr⟩ := List.exists_cons_of_ne_nil (List.splitOn_ne_nil [44#8] cs)
    rw [hfr]
    dsimp only
    cases CommandSpec.patternOf false first with
    | none => rfl
    | some p =>
      simp only [Option.isSome_some, Bool.true_and, ← mapM_isSome]
      cases rest.mapM (CommandSpec.patternOf true) <;> rfl

end DN.News.CharsRun
