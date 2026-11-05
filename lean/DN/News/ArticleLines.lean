-- SPDX-License-Identifier: AGPL-3.0-or-later
import DN.News.ArticleSpec

/-!
# DN.News.ArticleLines

The header section by places, as the article's program reads it. Lines end where `eolOf` says and lie as `spans`
lists them; fields group them (`groups`, `FieldAt`). `checkWith_shape` gives `ArticleSpec.checkWith`'s first refusals.
-/

namespace DN.News.ArticleLines

open DN.News.FrameSpec (CR LF)
open DN.News.ArticleSpec
open DN.News.CommandSpec (isWS)

/-- Whether a CRLF starts at `e`. -/
def crlfAt (a : Bytes) (e : Nat) : Bool := a[e]? == some CR && a[e + 1]? == some LF

/-- The line's end from `e`, `n` places at most: its CR, or `lim` if no CRLF ends one before it. -/
def eolGo (a : Bytes) (lim : Nat) : Nat → Nat → Nat
  | 0, _ => lim
  | n + 1, e => if e + 1 < lim then (if crlfAt a e then e else eolGo a lim n (e + 1)) else lim

/-- Where the line from `q` ends: its CR, or `lim` if no CRLF ends one before it. -/
def eolOf (a : Bytes) (q lim : Nat) : Nat := eolGo a lim (lim - q) q

theorem eolGo_ge (a : Bytes) (lim : Nat) : ∀ n e, e ≤ lim → e ≤ eolGo a lim n e ∧ eolGo a lim n e ≤ lim
  | 0, _, h => ⟨h, Nat.le_refl _⟩
  | n + 1, e, h => by
    simp only [eolGo]
    split
    · split
      · omega
      · have := eolGo_ge a lim n (e + 1) (by omega); omega
    · omega

theorem eolOf_ge (a : Bytes) {q lim : Nat} (h : q ≤ lim) : q ≤ eolOf a q lim ∧ eolOf a q lim ≤ lim :=
  eolGo_ge a lim _ q h

theorem eolGo_before (a : Bytes) (lim : Nat) : ∀ n e i, lim ≤ e + n → e ≤ i → i < eolGo a lim n e → i + 1 < lim →
    crlfAt a i = false
  | 0, _, _, hn, h1, h2, h3 => by simp only [eolGo] at h2; omega
  | n + 1, e, i, hn, h1, h2, h3 => by
    simp only [eolGo] at h2
    split at h2
    · split at h2
      · omega
      · rename_i hc
        by_cases hi : i = e
        · subst hi; simpa using hc
        · exact eolGo_before a lim n (e + 1) i (by omega) (by omega) h2 h3
    · omega

/-- **Before a line's end, no CRLF.** -/
theorem eolOf_before (a : Bytes) {q lim i : Nat} (h1 : q ≤ i) (h2 : i < eolOf a q lim) (h3 : i + 1 < lim) :
    crlfAt a i = false :=
  eolGo_before a lim _ q i (by omega) h1 h2 h3

theorem eolGo_found (a : Bytes) (lim : Nat) : ∀ n e, eolGo a lim n e < lim →
    crlfAt a (eolGo a lim n e) = true ∧ eolGo a lim n e + 1 < lim
  | 0, _, h => by simp only [eolGo] at h; omega
  | n + 1, e, h => by
    simp only [eolGo] at h ⊢
    split at h
    · rename_i h1
      split at h
      · rename_i h2
        rw [if_pos h1, if_pos h2]; exact ⟨h2, h1⟩
      · rename_i h2
        rw [if_pos h1, if_neg h2]; exact eolGo_found a lim n (e + 1) h
    · omega

/-- A line's end before the bound is past its start. -/
theorem eolOf_low (a : Bytes) {q lim : Nat} (h : eolOf a q lim < lim) : q ≤ eolOf a q lim := by
  by_cases hq : q ≤ lim
  · exact (eolOf_ge a hq).1
  · simp only [eolOf, show lim - q = 0 by omega, eolGo] at h; omega

/-- **A line's end before the bound is a CRLF's.** -/
theorem eolOf_found (a : Bytes) {q lim : Nat} (h : eolOf a q lim < lim) :
    crlfAt a (eolOf a q lim) = true ∧ eolOf a q lim + 1 < lim :=
  eolGo_found a lim _ q h

/-! ## The lines -/

/-- The bytes from `s` to `e`. -/
def seg (a : Bytes) (s e : Nat) : Bytes := (a.drop s).take (e - s)

theorem seg_self (a : Bytes) (s : Nat) : seg a s s = [] := by simp [seg]

theorem seg_length (a : Bytes) {s e : Nat} (hs : s ≤ e) (he : e ≤ a.length) : (seg a s e).length = e - s := by
  simp only [seg, List.length_take, List.length_drop]; omega

theorem seg_succ (a : Bytes) {s i : Nat} (hs : s ≤ i) (hi : i < a.length) :
    seg a s (i + 1) = seg a s i ++ [a[i]] := by
  unfold seg
  rw [show i + 1 - s = (i - s) + 1 by omega, List.take_add_one, List.getElem?_drop,
    show s + (i - s) = i by omega, List.getElem?_eq_getElem hi]
  rfl


/-- Reading a line's bytes before its end: `headerFrom` keeps them in `cur`, a CR last pending in `cr`. -/
theorem headerFrom_scan (a : Bytes) {s e : Nat} (he : e ≤ a.length)
    (hno : ∀ i, s ≤ i → i < e → i + 1 < a.length → crlfAt a i = false) (acc : List Bytes) :
    ∀ k i (cr : Bool) (cur : Bytes), i + k = e → s ≤ i → (cr = true → s < i ∧ a[i - 1]? = some CR) →
      (if cr then CR :: cur else cur).reverse = seg a s i →
      ∃ (cr' : Bool) (cur' : Bytes), (if cr' then CR :: cur' else cur').reverse = seg a s e ∧
        headerFrom (a.drop i) cr cur acc = headerFrom (a.drop e) cr' cur' acc
  | 0, i, cr, cur, hk, _, _, hseg => ⟨cr, cur, by rw [← hk, Nat.add_zero]; exact hseg, by rw [← hk, Nat.add_zero]⟩
  | k + 1, i, cr, cur, hk, hsi, hcr, hseg => by
    have hi : i < a.length := by omega
    rw [List.drop_eq_getElem_cons hi]
    have hlf : (cr && a[i] == LF) = false := by
      cases cr
      · rfl
      · obtain ⟨hs, hp⟩ := hcr rfl
        have hc := hno (i - 1) (by omega) (by omega) (by omega)
        simp only [crlfAt, hp, show i - 1 + 1 = i by omega, List.getElem?_eq_getElem hi, beq_self_eq_true,
          Bool.true_and] at hc
        simpa using hc
    simp only [headerFrom, hlf, Bool.false_eq_true, if_false]
    split
    · rename_i hb
      have hb' : a[i] = CR := by simpa using hb
      refine headerFrom_scan a he hno acc k (i + 1) true (if cr = true then CR :: cur else cur) (by omega) (by omega)
        (fun _ => ⟨by omega, by simp [List.getElem?_eq_getElem hi, hb']⟩) ?_
      simp only [if_true]; rw [List.reverse_cons, hseg, seg_succ a hsi hi, hb']
    · refine headerFrom_scan a he hno acc k (i + 1) false (a[i] :: if cr = true then CR :: cur else cur) (by omega)
        (by omega) (fun h => absurd h (by decide)) ?_
      simp only [Bool.false_eq_true, if_false]; rw [List.reverse_cons, hseg, seg_succ a hsi hi]

/-- The header's lines from place `s`, each by its start and end. Also the empty line's place, if one ends them. -/
def spans (a : Bytes) (s : Nat) : List (Nat × Nat) × Option Nat :=
  if h : eolOf a s a.length < a.length ∧ s ≤ a.length then
    if eolOf a s a.length = s then ([], some s)
    else
      let r := spans a (eolOf a s a.length + 2)
      ((s, eolOf a s a.length) :: r.1, r.2)
  else (if s < a.length then [(s, a.length)] else [], none)
termination_by a.length - s
decreasing_by have := (eolOf_ge a h.2).1; omega

/-- The lines a list of places gives. -/
def segs (a : Bytes) (L : List (Nat × Nat)) : List Bytes := L.map fun p => seg a p.1 p.2

theorem crlf_ne : (CR == LF) = false := by decide

/-- **The header's lines are those of `spans`**, from any place. -/
theorem headerFrom_spans (a : Bytes) : ∀ n s (acc : List Bytes), a.length - s = n → s ≤ a.length →
    headerFrom (a.drop s) false [] acc = (acc.reverse ++ segs a (spans a s).1, (spans a s).2.isSome) := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro s acc hn hs
    have hge := eolOf_ge a hs
    obtain ⟨cr', cur', hseg, hscan⟩ := headerFrom_scan a hge.2
      (fun i h1 h2 h3 => eolOf_before a h1 h2 h3) acc _ s false [] (Nat.add_sub_cancel' hge.1) (Nat.le_refl _)
      (fun h => absurd h (by decide)) (by simp [seg_self])
    rw [hscan]
    by_cases hlt : eolOf a s a.length < a.length
    · obtain ⟨hc, h1⟩ := eolOf_found a hlt
      have hd : a.drop (eolOf a s a.length) = CR :: LF :: a.drop (eolOf a s a.length + 2) := by
        simp only [crlfAt, Bool.and_eq_true, beq_iff_eq] at hc
        rw [List.drop_eq_getElem_cons hlt, List.drop_eq_getElem_cons h1]
        rw [List.getElem?_eq_getElem hlt, Option.some.injEq] at hc
        rw [List.getElem?_eq_getElem h1, Option.some.injEq] at hc
        rw [hc.1, hc.2]
      rw [hd]
      simp only [headerFrom, crlf_ne, Bool.and_false, Bool.false_eq_true, if_false, beq_self_eq_true, if_true,
        Bool.true_and]
      rw [spans, dif_pos ⟨hlt, hs⟩]
      have hlen := seg_length a hge.1 hge.2
      by_cases he : eolOf a s a.length = s
      · rw [if_pos he]
        have : (if cr' = true then CR :: cur' else cur').isEmpty = true := by
          rw [← List.isEmpty_reverse, hseg, List.isEmpty_iff, ← List.length_eq_zero_iff, hlen]; omega
        simp [this, segs]
      · rw [if_neg he]
        have : (if cr' = true then CR :: cur' else cur').isEmpty = false := by
          rw [← List.isEmpty_reverse, hseg, Bool.eq_false_iff, ne_eq, List.isEmpty_iff, ← List.length_eq_zero_iff,
            hlen]; omega
        simp only [this, Bool.false_eq_true, if_false]
        rw [hseg, ih _ (by omega) _ _ rfl (by omega)]
        simp [segs]
    · have he : eolOf a s a.length = a.length := by omega
      rw [he] at hseg
      rw [he, List.drop_length]
      simp only [headerFrom]
      rw [spans, dif_neg (fun h => hlt h.1)]
      have hlen := seg_length a hs (Nat.le_refl _)
      by_cases hsl : s < a.length
      · have : (if cr' = true then CR :: cur' else cur').isEmpty = false := by
          rw [← List.isEmpty_reverse, hseg, Bool.eq_false_iff, ne_eq, List.isEmpty_iff, ← List.length_eq_zero_iff,
            hlen]; omega
        simp only [this, Bool.false_eq_true, if_false, if_pos hsl]
        rw [hseg]; simp [segs]
      · have : (if cr' = true then CR :: cur' else cur').isEmpty = true := by
          rw [← List.isEmpty_reverse, hseg, List.isEmpty_iff, ← List.length_eq_zero_iff, hlen]; omega
        simp [this, if_neg hsl, segs]

/-- **`ArticleSpec.header` by places.** -/
theorem header_spans (a : Bytes) : header a = (segs a (spans a 0).1, (spans a 0).2.isSome) := by
  have := headerFrom_spans a _ 0 [] rfl (Nat.zero_le _)
  simpa [header] using this

/-- **A line's end is the first CRLF**: a CRLF at `e` with none from `q` before it ends the line from `q`. -/
theorem eolGo_eq (a : Bytes) (lim : Nat) {e : Nat} (hc : crlfAt a e = true) (he : e + 1 < lim) :
    ∀ n q, q ≤ e → e < q + n → (∀ i, q ≤ i → i < e → crlfAt a i = false) → eolGo a lim n q = e
  | 0, _, h1, h2, _ => by omega
  | n + 1, q, h1, h2, h3 => by
    simp only [eolGo, if_pos (show q + 1 < lim by omega)]
    by_cases hq : q = e
    · subst hq; rw [if_pos hc]
    · rw [if_neg (by rw [h3 q (Nat.le_refl _) (by omega)]; decide)]
      exact eolGo_eq a lim hc he n (q + 1) (by omega) (by omega) fun i hi1 hi2 => h3 i (by omega) hi2

theorem eolOf_eq (a : Bytes) {q e lim : Nat} (hc : crlfAt a e = true) (he : e + 1 < lim) (hq : q ≤ e)
    (hno : ∀ i, q ≤ i → i < e → crlfAt a i = false) : eolOf a q lim = e :=
  eolGo_eq a lim hc he _ q hq (by omega) hno

/-- A line ending before both bounds ends at the same place under either. -/
theorem eolOf_lim (a : Bytes) {q lim lim' : Nat} (hq : q ≤ lim) (h : eolOf a q lim < lim)
    (h' : eolOf a q lim + 1 < lim') : eolOf a q lim' = eolOf a q lim := by
  have hf := eolOf_found a h
  have hge := eolOf_ge a hq
  exact eolOf_eq a hf.1 h' hge.1 fun i h1 h2 => eolOf_before a h1 h2 (by omega)

/-- The lines from `s` up to the empty one at `p`, by places. -/
inductive Lines (a : Bytes) : Nat → List (Nat × Nat) → Nat → Prop
  | sep {s : Nat} : eolOf a s a.length = s → s < a.length → Lines a s [] s
  | line {s e p : Nat} {L : List (Nat × Nat)} : eolOf a s a.length = e → e < a.length → e ≠ s →
      Lines a (e + 2) L p → Lines a s ((s, e) :: L) p

/-- **Lines the empty one ends are `Lines`.** -/
theorem spans_lines (a : Bytes) : ∀ n s, a.length - s = n → s ≤ a.length → ∀ {L : List (Nat × Nat)} {p : Nat},
    spans a s = (L, some p) → Lines a s L p := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro s hn hs L p h
    rw [spans] at h
    split at h
    · rename_i hc
      split at h
      · rename_i he
        simp only [Prod.mk.injEq, Option.some.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact .sep he (he ▸ hc.1)
      · rename_i he
        simp only [Prod.mk.injEq] at h
        obtain ⟨rfl, h2⟩ := h
        have hf := eolOf_found a hc.1
        have hge := eolOf_ge a hs
        exact .line rfl hc.1 he (ih _ (by omega) _ rfl (by omega) (Prod.ext rfl h2))
    · simp at h

theorem lines_sep {a : Bytes} {s p : Nat} {L : List (Nat × Nat)} (h : Lines a s L p) :
    s ≤ p ∧ eolOf a p a.length = p ∧ p < a.length := by
  induction h with
  | sep he hs => exact ⟨Nat.le_refl _, he, hs⟩
  | line he hlt _ _ ih => exact ⟨by have := eolOf_low a (he ▸ hlt); omega, ih.2⟩

/-- A line of `Lines`: its end is its line's, before the empty line. -/
theorem lines_mem {a : Bytes} {s p : Nat} {L : List (Nat × Nat)} (h : Lines a s L p) :
    ∀ q ∈ L, s ≤ q.1 ∧ q.1 < q.2 ∧ q.2 + 2 ≤ p ∧ eolOf a q.1 a.length = q.2 ∧ q.2 < a.length := by
  induction h with
  | sep => intro q hq; nomatch hq
  | @line s e p L he hlt hne hL ih =>
    have hp := lines_sep hL
    have hge := eolOf_low a (he ▸ hlt)
    intro q hq
    rcases List.mem_cons.1 hq with rfl | hq
    · exact ⟨Nat.le_refl _, by omega, by omega, he, hlt⟩
    · have := ih q hq; omega

/-- **The section's octets, CRLFs counted, up to the empty line.** -/
theorem lines_sum {a : Bytes} {s p : Nat} {L : List (Nat × Nat)} (h : Lines a s L p) :
    ((segs a L).map (·.length + 2)).sum = p - s := by
  induction h with
  | sep => simp [segs]
  | @line s e p L he hlt hne hL ih =>
    have hp := lines_sep hL
    have hge := eolOf_low a (he ▸ hlt)
    simp only [segs, List.map_cons, List.sum_cons] at ih ⊢
    rw [seg_length a (by omega) (by omega)]
    rw [ih]; omega

theorem fits_lines {a : Bytes} {p : Nat} {L : List (Nat × Nat)} (h : Lines a 0 L p) (r : Rules) :
    fits r (segs a L) = decide (p ≤ r.headerMax) := by
  simp only [fits, lines_sum h, Nat.sub_zero]

theorem any_mem_congr {α : Type} {l : List α} {f g : α → Bool} (h : ∀ x ∈ l, f x = g x) : l.any f = l.any g := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    simp only [List.any_cons, h x List.mem_cons_self, ih fun y hy => h y (List.mem_cons_of_mem _ hy)]

/-- **A line past the bound**, by places. -/
theorem long_lines {a : Bytes} {s p : Nat} {L : List (Nat × Nat)} (h : Lines a s L p) (m : Nat) :
    (segs a L).any (·.length > m) = L.any fun q => decide (m < q.2 - q.1) := by
  have hm := lines_mem h
  simp only [segs, List.any_map]
  refine any_mem_congr fun q hq => ?_
  obtain ⟨_, h1, _, _, h2⟩ := hm q hq
  simp only [Function.comp, seg_length a (Nat.le_of_lt h1) (Nat.le_of_lt h2), gt_iff_lt]

/-! ## The fields -/

/-- Where a line's name ends, counted from `k`: its first byte of no name. The flag says no colon ends it there. -/
def nameScan : Bytes → Nat → Nat × Bool
  | [], k => (k, true)
  | b :: rest, k => if b = COLON then (k, false) else if isFtext b then nameScan rest (k + 1) else (k, true)


theorem nameScan_ok : ∀ (l : Bytes) (k : Nat),
    ((nameScan l k).2 = !((l.takeWhile (· != COLON)).all isFtext &&
      decide ((l.takeWhile (· != COLON)).length < l.length))) ∧
    ((nameScan l k).2 = false → (nameScan l k).1 = k + (l.takeWhile (· != COLON)).length)
  | [], k => by simp [nameScan]
  | b :: rest, k => by
    by_cases hb : b = COLON
    · subst hb; simp [nameScan]
    · have hb' : (b != COLON) = true := by simpa using hb
      by_cases hf : isFtext b
      · obtain ⟨h1, h2⟩ := nameScan_ok rest (k + 1)
        simp only [nameScan, if_neg hb, List.takeWhile_cons, hb', if_true, List.all_cons, hf,
          Bool.true_and, List.length_cons]
        refine ⟨by rw [h1]; simp, fun h => by rw [h2 h]; omega⟩
      · simp [nameScan, hb, hf, hb']

theorem takeWhile_take (l : Bytes) (p : FrameSpec.Byte → Bool) : l.takeWhile p = l.take (l.takeWhile p).length := by
  induction l with
  | nil => rfl
  | cons b rest ih => by_cases h : p b <;> simp [h, ← ih]

/-- **A line's name as `nameScan` reads it.** -/
theorem nameOf_scan (l : Bytes) :
    nameOf l = if (nameScan l 0).2 || (nameScan l 0).1 == 0 then none else some (l.take (nameScan l 0).1) := by
  obtain ⟨h1, h2⟩ := nameScan_ok l 0
  have htk := takeWhile_take l (· != COLON)
  simp only [nameOf]
  generalize l.takeWhile (· != COLON) = t at h1 h2 htk
  by_cases ha : t.all isFtext = true <;> by_cases hl : t.length < l.length
  · have hb : (nameScan l 0).2 = false := by rw [h1, ha, decide_eq_true hl]; rfl
    have hj := h2 hb
    rw [Nat.zero_add] at hj
    rw [hb, hj, ← htk]
    by_cases hz : t = []
    · subst hz; simp
    · have : t.length ≠ 0 := fun e => hz (List.length_eq_zero_iff.1 e)
      simp [hl, hz, ha, this]
  · have hb : (nameScan l 0).2 = true := by rw [h1, ha, decide_eq_false hl]; rfl
    rw [hb]; simp [hl]
  · have hb : (nameScan l 0).2 = true := by rw [h1]; simp [ha]
    rw [hb]; simp [ha]
  · have hb : (nameScan l 0).2 = true := by rw [h1]; simp [ha]
    rw [hb]; simp [hl]

/-- Whether line `q` continues a field: it starts with white space. -/
def cont (a : Bytes) (q : Nat × Nat) : Bool := (a[q.1]?).any isWS

/-- Whether line `q`, not a continuation, fails to start a field: no name before a colon. -/
def malName (a : Bytes) (q : Nat × Nat) : Bool := (nameScan (seg a q.1 q.2) 0).2 || (nameScan (seg a q.1 q.2) 0).1 == 0

/-- A field's name, from its first line's place. -/
def nameAt (a : Bytes) (q : Nat × Nat) : Bytes := seg a q.1 (q.1 + (nameScan (seg a q.1 q.2) 0).1)

/-- The field the lines of `g` make. -/
def fieldOf (a : Bytes) (g : List (Nat × Nat)) : Field := ⟨nameAt a (g.headD (0, 0)), segs a g⟩

/-- The fields lines given by places make, as `fieldsFrom` groups them. -/
def groupL (a : Bytes) : List (Nat × Nat) → List (List (Nat × Nat)) → Option (List (Nat × Nat)) →
    Option (List (List (Nat × Nat)))
  | [], acc, cur => some (cur.toList ++ acc).reverse
  | q :: more, acc, cur =>
    if cont a q then
      match cur with
      | some g => groupL a more acc (some (g ++ [q]))
      | none => none
    else if malName a q then none else groupL a more (cur.toList ++ acc) (some [q])

theorem seg_head (a : Bytes) {x e : Nat} (h1 : x < e) : (seg a x e).head? = a[x]? := by
  simp only [seg, List.head?_take, List.head?_drop]
  rw [if_neg (by omega)]

theorem seg_take (a : Bytes) {x e : Nat} (k : Nat) (hk : k ≤ e - x) : (seg a x e).take k = seg a x (x + k) := by
  simp only [seg, List.take_take]; congr 1; omega

/-- **`fieldsFrom` by places**, the lines in order with their places. -/
theorem fields_groupL (a : Bytes) :
    ∀ (L : List (Nat × Nat)) (acc : List (List (Nat × Nat))) (cur : Option (List (Nat × Nat))),
      (∀ q ∈ L, q.1 < q.2 ∧ q.2 ≤ a.length) → (∀ g, cur = some g → g ≠ []) →
      fieldsFrom (segs a L) (acc.map (fieldOf a)) (cur.map (fieldOf a)) = (groupL a L acc cur).map (·.map (fieldOf a))
  | [], acc, cur, _, _ => by
    cases cur <;> simp [fieldsFrom, groupL, segs]
  | q :: more, acc, cur, hL, hcur => by
    obtain ⟨hq1, hq2⟩ := hL q List.mem_cons_self
    have hm : ∀ q' ∈ more, q'.1 < q'.2 ∧ q'.2 ≤ a.length := fun q' h => hL q' (List.mem_cons_of_mem _ h)
    have hhead : (seg a q.1 q.2).head?.any isWS = cont a q := by rw [seg_head a hq1]; rfl
    simp only [segs, List.map_cons, fieldsFrom, groupL]
    rw [hhead]
    split
    · cases cur with
      | none => rfl
      | some g =>
        have := fields_groupL a more acc (some (g ++ [q])) hm (fun g' h => by cases h; simp)
        simp only [segs, Option.map_some] at this ⊢
        rw [← this]
        have hg := hcur g rfl
        congr 2
        simp only [fieldOf, segs, List.map_append, List.map_cons, List.map_nil]
        congr 1
        cases g with
        | nil => exact absurd rfl hg
        | cons _ _ => rfl
    · rw [nameOf_scan]
      by_cases hmal : malName a q = true
      · simp only [malName] at hmal ⊢; simp [hmal]
      · have hmal' : ((nameScan (seg a q.1 q.2) 0).2 || (nameScan (seg a q.1 q.2) 0).1 == 0) = false := by
          simpa [malName] using hmal
        simp only [hmal', Bool.false_eq_true, if_false]
        rw [if_neg (by simpa [malName] using hmal)]
        have := fields_groupL a more (cur.toList ++ acc) (some [q]) hm (fun g h => by cases h; simp)
        simp only [segs, Option.map_some] at this ⊢
        rw [← this]
        congr 1
        · cases cur <;> simp
        · simp only [fieldOf, nameAt, segs, List.headD_cons, List.map_cons, List.map_nil]
          congr 1
          have hb := (nameScan_ok (seg a q.1 q.2) 0)
          rw [seg_take a]
          have hb2 : (nameScan (seg a q.1 q.2) 0).2 = false := by simp at hmal'; exact hmal'.1
          have hj := hb.2 hb2
          have hlt : (List.takeWhile (· != COLON) (seg a q.1 q.2)).length < (seg a q.1 q.2).length := by
            have := hb.1; rw [hb2] at this
            simp only [Bool.false_eq, Bool.not_eq_eq_eq_not, Bool.not_false, Bool.and_eq_true,
              decide_eq_true_eq] at this
            exact this.2
          rw [seg_length a (Nat.le_of_lt hq1) hq2] at hlt
          omega

/-- A line the program finds malformed: a continuation first, or a field's first line without a name. -/
def malLine (a : Bytes) (q : Nat × Nat) : Bool := if cont a q then q.1 == 0 else malName a q

theorem groupL_some_none (a : Bytes) : ∀ (L : List (Nat × Nat)) (acc : List (List (Nat × Nat))) (g : List (Nat × Nat)),
    groupL a L acc (some g) = none ↔ L.any (fun q => !cont a q && malName a q) = true
  | [], _, _ => by simp [groupL]
  | q :: more, acc, g => by
    simp only [groupL, List.any_cons]
    by_cases hc : cont a q = true
    · simp only [hc, if_true, Bool.not_true, Bool.false_and, Bool.false_or]
      exact groupL_some_none a more acc (g ++ [q])
    · have hc' : cont a q = false := by simpa using hc
      simp only [hc', Bool.false_eq_true, if_false, Bool.not_false, Bool.true_and]
      by_cases hm : malName a q = true
      · simp [hm]
      · have hm' : malName a q = false := by simpa using hm
        simp only [hm', Bool.false_eq_true, if_false, Bool.false_or]
        exact groupL_some_none a more _ [q]

/-- **Malformed, as the program finds it**: the lines from the section's start make no fields. -/
theorem groupL_none (a : Bytes) {q : Nat × Nat} {L : List (Nat × Nat)} (h0 : q.1 = 0) (hL : ∀ q' ∈ L, q'.1 ≠ 0) :
    groupL a (q :: L) [] none = none ↔ (q :: L).any (malLine a) = true := by
  have hrest : L.any (malLine a) = L.any (fun q => !cont a q && malName a q) :=
    any_mem_congr fun q' hq' => by
      simp only [malLine]; split
      · rename_i hc; simp [hc, hL q' hq']
      · rename_i hc; simp [hc]
  simp only [groupL, List.any_cons, hrest]
  by_cases hc : cont a q = true
  · simp [hc, malLine, h0]
  · have hc' : cont a q = false := by simpa using hc
    simp only [hc', Bool.false_eq_true, if_false, malLine]
    by_cases hm : malName a q = true
    · simp [hm]
    · have hm' : malName a q = false := by simpa using hm
      simp only [hm', Bool.false_eq_true, if_false, Bool.false_or]
      exact groupL_some_none a L [] [q]

/-- What `checkWith` does once the fields are made. -/
def tailOf (r : Rules) (ctx : Context) (fs : List Field) : Verdict :=
  match fs.findSome? (fieldRefusal r) with
  | some x => .refused x
  | none =>
    match articleRefusal r ctx fs with
    | some x => .refused x
    | none => .accepted (added r ctx fs)

/-- **`checkWith` by places**: the section's shape from `spans`, its fields from `groupL`. -/
theorem checkWith_places (r : Rules) (ctx : Context) (a : Bytes) :
    checkWith r ctx a =
      if (spans a 0).1 = [] then .refused .noHeader
      else match (spans a 0).2 with
        | none => .refused .noSeparator
        | some p =>
          if r.headerMax < p then .refused .headerTooLong
          else if (spans a 0).1.any (fun q => decide (r.lineMax < q.2 - q.1)) then .refused .lineTooLong
          else match groupL a (spans a 0).1 [] none with
            | none => .refused .malformed
            | some gs => tailOf r ctx (gs.map (fieldOf a)) := by
  unfold checkWith
  rw [header_spans]
  simp only
  by_cases he : (spans a 0).1 = []
  · simp [he, segs]
  · have hne : (segs a (spans a 0).1).isEmpty = false := by simp [segs, he]
    rw [hne, if_neg he]
    simp only [Bool.false_eq_true, if_false]
    cases hp : (spans a 0).2 with
    | none => simp
    | some p =>
      have hl := spans_lines a _ 0 rfl (Nat.zero_le _) (show spans a 0 = ((spans a 0).1, some p) by rw [← hp])
      simp only [Option.isSome_some, Bool.not_true, Bool.false_eq_true, if_false]
      rw [fits_lines hl, long_lines hl]
      by_cases h1 : r.headerMax < p
      · simp [h1]
      · simp only [show decide (p ≤ r.headerMax) = true by simpa using h1, Bool.not_true, Bool.false_eq_true,
          if_false, if_neg h1]
        split
        · rfl
        · have hm := lines_mem hl
          have := fields_groupL a (spans a 0).1 [] none (fun q hq => ⟨(hm q hq).2.1, Nat.le_of_lt (hm q hq).2.2.2.2⟩)
            (fun _ h => nomatch h)
          simp only [List.map_nil, Option.map_none, fields] at this ⊢
          rw [this]
          cases groupL a (spans a 0).1 [] none <;> rfl

/-- **No header**: the section empty or its first line. -/
theorem spans_nil (a : Bytes) : (spans a 0).1 = [] ↔ a.length = 0 ∨ eolOf a 0 a.length = 0 := by
  rw [spans]
  split
  · rename_i h
    split
    · rename_i he; simp [he]
    · rename_i he
      simp only [he, or_false, reduceCtorEq, false_iff]
      omega
  · rename_i h
    by_cases hl : 0 < a.length
    · have : eolOf a 0 a.length ≠ 0 := fun e => h ⟨by omega, Nat.zero_le _⟩
      simp [hl, this, Nat.pos_iff_ne_zero.1 hl]
    · simp [show a.length = 0 by omega]

/-- The lines from a line on: a chain of `Lines` from its next line. -/
theorem lines_tail {a : Bytes} {s p : Nat} {q : Nat × Nat} {L : List (Nat × Nat)} (h : Lines a s (q :: L) p) :
    q.1 = s ∧ Lines a (q.2 + 2) L p := by
  cases h with
  | line he hlt hne hL => exact ⟨rfl, hL⟩


theorem dropWhile_len {α : Type} (p : α → Bool) : ∀ l : List α, (l.dropWhile p).length ≤ l.length
  | [] => Nat.le_refl _
  | x :: l => by
    simp only [List.dropWhile_cons]
    split
    · have := dropWhile_len p l; simp only [List.length_cons]; omega
    · exact Nat.le_refl _

/-- The fields of a list of lines: each line not a continuation with the continuations after it. -/
def groups (a : Bytes) : List (Nat × Nat) → List (List (Nat × Nat))
  | [] => []
  | q :: more => (q :: more.takeWhile (cont a)) :: groups a (more.dropWhile (cont a))
termination_by L => L.length
decreasing_by have := dropWhile_len (cont a) more; simp only [List.length_cons]; omega

theorem groupL_cont (a : Bytes) : ∀ (L : List (Nat × Nat)) (acc : List (List (Nat × Nat))) (g : List (Nat × Nat)),
    L.any (fun q => !cont a q && malName a q) = false →
    groupL a L acc (some g) = some (acc.reverse ++ (g ++ L.takeWhile (cont a)) :: groups a (L.dropWhile (cont a)))
  | [], acc, g, _ => by simp [groupL, groups]
  | q :: more, acc, g, h => by
    simp only [List.any_cons, Bool.or_eq_false_iff] at h
    simp only [groupL, List.takeWhile_cons, List.dropWhile_cons]
    by_cases hc : cont a q = true
    · simp only [hc, if_true]
      rw [groupL_cont a more acc (g ++ [q]) h.2]
      simp
    · have hc' : cont a q = false := by simpa using hc
      have hm : malName a q = false := by simpa [hc'] using h.1
      simp only [hc', Bool.false_eq_true, if_false, hm, List.append_nil]
      rw [groupL_cont a more _ [q] h.2]
      simp [groups]

/-- **The fields are the groups**, when no line is malformed. -/
theorem groupL_groups (a : Bytes) {q : Nat × Nat} {L : List (Nat × Nat)} (h0 : q.1 = 0) (hL : ∀ q' ∈ L, q'.1 ≠ 0)
    (hok : (q :: L).any (malLine a) = false) : groupL a (q :: L) [] none = some (groups a (q :: L)) := by
  have hrest : L.any (fun q => !cont a q && malName a q) = false := by
    simp only [List.any_cons, Bool.or_eq_false_iff] at hok
    rw [← hok.2]
    exact (any_mem_congr fun q' hq' => by
      simp only [malLine]; split
      · rename_i hc; simp [hc, hL q' hq']
      · rename_i hc; simp [hc]).symm
  simp only [List.any_cons, Bool.or_eq_false_iff, malLine] at hok
  have hc : cont a q = false := by
    cases hc : cont a q
    · rfl
    · simp [hc, h0] at hok
  have hm : malName a q = false := by simpa [hc] using hok.1
  simp only [groupL, hc, Bool.false_eq_true, if_false, hm]
  show groupL a L [] (some [q]) = _
  rw [groupL_cont a L [] [q] hrest]
  simp [groups]

/-! ## A field by places -/

/-- The colon a field's name ends with, where `nameScan` stops. -/
theorem nameScan_colon : ∀ (l : Bytes) (k0 : Nat), (nameScan l k0).2 = false →
    k0 ≤ (nameScan l k0).1 ∧ l[(nameScan l k0).1 - k0]? = some COLON ∧
      ∀ i, i < (nameScan l k0).1 - k0 → l[i]? ≠ some COLON
  | [], _, h => by simp [nameScan] at h
  | b :: rest, k0, h => by
    by_cases hb : b = COLON
    · subst hb; simp [nameScan]
    · by_cases hf : isFtext b = true
      · have hr : nameScan (b :: rest) k0 = nameScan rest (k0 + 1) := by simp [nameScan, hb, hf]
        rw [hr] at h ⊢
        obtain ⟨h1, h2, h3⟩ := nameScan_colon rest (k0 + 1) h
        refine ⟨by omega, ?_, fun i hi => ?_⟩
        · rw [show (nameScan rest (k0 + 1)).1 - k0 = ((nameScan rest (k0 + 1)).1 - (k0 + 1)) + 1 by omega]
          simpa using h2
        · cases i with
          | zero => simpa using hb
          | succ i => simpa using h3 i (by omega)
      · simp [nameScan, hb, hf] at h

theorem seg_get (a : Bytes) {x e i : Nat} (hi : i < e - x) : (seg a x e)[i]? = a[x + i]? := by
  simp only [seg, List.getElem?_take, if_pos hi, List.getElem?_drop]

/-- A field's start in the section: its first line from `p` to `e`, no continuation and named. `L` follows it. -/
structure FieldAt (a : Bytes) (sep p e : Nat) (L : List (Nat × Nat)) : Prop where
  lines : Lines a p ((p, e) :: L) sep
  first : cont a (p, e) = false
  named : malName a (p, e) = false

/-- The length of the name of a field's first line. -/
def nameLen (a : Bytes) (p e : Nat) : Nat := (nameScan (seg a p e) 0).1

/-- Where the field before lines `L` ends: the next line that is no continuation, else the empty line. -/
def nextOf (a : Bytes) (L : List (Nat × Nat)) (sep : Nat) : Nat := ((L.dropWhile (cont a)).head?.map (·.1)).getD sep

/-- **The field's name**: a colon ends it before its first line's end, none before. -/
theorem fieldAt_colon {a : Bytes} {sep p e : Nat} {L : List (Nat × Nat)} (h : FieldAt a sep p e L) :
    0 < nameLen a p e ∧ p + nameLen a p e < e ∧ a[p + nameLen a p e]? = some COLON ∧
      ∀ j, p ≤ j → j < p + nameLen a p e → a[j]? ≠ some COLON := by
  have hm := lines_mem h.lines (p, e) List.mem_cons_self
  have hn := h.named
  simp only [malName, Bool.or_eq_false_iff, beq_eq_false_iff_ne] at hn
  obtain ⟨h1, h2, h3⟩ := nameScan_colon (seg a p e) 0 hn.1
  have hlen := seg_length a (Nat.le_of_lt hm.2.1) (Nat.le_of_lt hm.2.2.2.2)
  have hk : (nameScan (seg a p e) 0).1 < e - p := by
    rw [← hlen]; exact (List.getElem?_eq_some_iff.1 h2).1 |> fun h => by simpa using h
  refine ⟨Nat.pos_of_ne_zero hn.2, by unfold nameLen; omega, ?_, fun j hj1 hj2 => ?_⟩
  · unfold nameLen; rw [← seg_get a (by simpa using hk)]; simpa using h2
  · have := h3 (j - p) (by unfold nameLen at hj2; omega)
    rwa [seg_get a (by unfold nameLen at hj2; omega), show p + (j - p) = j by omega] at this

/-- **Where the field's first line ends**, from its colon, under the empty line's bound. -/
theorem fieldAt_eol {a : Bytes} {sep p e : Nat} {L : List (Nat × Nat)} (h : FieldAt a sep p e L) :
    eolOf a (p + nameLen a p e) sep = e := by
  have hm := lines_mem h.lines (p, e) List.mem_cons_self
  obtain ⟨_, hpe, hes, heol, hlt⟩ := hm
  have hc := fieldAt_colon h
  have hf := eolOf_found a (show eolOf a p a.length < a.length by rw [heol]; exact hlt)
  rw [heol] at hf
  exact eolOf_eq a hf.1 (by omega) (by omega) fun i h1 h2 =>
    eolOf_before a (q := p) (lim := a.length) (by omega) (by rw [heol]; exact h2) (by omega)

/-- The lines from the empty line's place: none. -/
theorem lines_at_sep {a : Bytes} {q sep : Nat} {L : List (Nat × Nat)} (h : Lines a q L sep) (hq : sep ≤ q) :
    L = [] := by
  cases h with
  | sep => rfl
  | line he hlt hne hL =>
    have := lines_sep hL
    have := eolOf_low a (he ▸ hlt)
    omega

/-- A line from `q` before the empty line, and the lines after it. -/
theorem lines_cons {a : Bytes} {q sep : Nat} {L : List (Nat × Nat)} (h : Lines a q L sep) (hq : q < sep) :
    ∃ e L', L = (q, e) :: L' ∧ eolOf a q sep = e ∧ e + 2 ≤ sep ∧ q < e ∧ e < a.length ∧ Lines a (e + 2) L' sep := by
  cases h with
  | sep => omega
  | @line _ e _ L' he hlt hne hL =>
    have hp := lines_sep hL
    have hge := eolOf_low a (he ▸ hlt)
    refine ⟨e, L', rfl, ?_, by omega, by omega, hlt, hL⟩
    rw [← he]
    exact eolOf_lim a (Nat.le_of_lt (by omega)) (by rw [he]; exact hlt) (by rw [he]; omega)

theorem nextOf_cont {a : Bytes} {q e sep : Nat} {L : List (Nat × Nat)} (h : cont a (q, e) = true) :
    nextOf a ((q, e) :: L) sep = nextOf a L sep := by
  simp [nextOf, h]

theorem nextOf_stop {a : Bytes} {q e sep : Nat} {L : List (Nat × Nat)} (h : cont a (q, e) = false) :
    nextOf a ((q, e) :: L) sep = q := by
  simp [nextOf, h]

theorem nextOf_nil (a : Bytes) (sep : Nat) : nextOf a [] sep = sep := rfl

theorem cont_byte {a : Bytes} {q e : Nat} (hq : q < a.length) : cont a (q, e) = isWS a[q]! := by
  simp [cont, List.getElem?_eq_getElem hq, getElem!_pos a q hq]

/-- **The field's end is past its start**, the empty line's place at most. -/
theorem nextOf_ge {a : Bytes} {q sep : Nat} {L : List (Nat × Nat)} (h : Lines a q L sep) :
    q ≤ nextOf a L sep ∧ nextOf a L sep ≤ sep := by
  induction h with
  | sep => simp [nextOf]
  | @line s e p L he hlt hne hL ih =>
    have hge := eolOf_low a (he ▸ hlt)
    by_cases hc : cont a (s, e) = true
    · rw [nextOf_cont hc]; omega
    · rw [nextOf_stop (by simpa using hc)]; have := lines_sep hL; omega

/-- Whether a continuation line of the field before `L` is white space alone. -/
def blankL (a : Bytes) (L : List (Nat × Nat)) : Bool := (L.takeWhile (cont a)).any fun q => (seg a q.1 q.2).all isWS

theorem blankL_cont {a : Bytes} {q e : Nat} {L : List (Nat × Nat)} (h : cont a (q, e) = true) :
    blankL a ((q, e) :: L) = ((seg a q e).all isWS || blankL a L) := by
  simp [blankL, h]

/-- At the field's end no continuation is left. -/
theorem blankL_stop {a : Bytes} {q sep : Nat} {L : List (Nat × Nat)} (h : Lines a q L sep)
    (hq : nextOf a L sep = q) : blankL a L = false := by
  cases h with
  | sep => rfl
  | @line _ e _ L' he hlt hne hL =>
    by_cases hc : cont a (q, e) = true
    · rw [nextOf_cont hc] at hq
      have := (nextOf_ge hL).1; have := eolOf_low a (he ▸ hlt); omega
    · simp [blankL, show cont a (q, e) = false by simpa using hc]

/-! ## The section's shape -/

/-- The codes of `checkWith`'s first refusals: 1 no header, 2 no empty line, 3 too long, 4 a line too long. 5 is
malformed, 0 none. -/
def shapeOf (r : Rules) (a : Bytes) : Nat :=
  if (spans a 0).1 = [] then 1
  else match (spans a 0).2 with
    | none => 2
    | some p =>
      if r.headerMax < p then 3
      else if (spans a 0).1.any (fun q => decide (r.lineMax < q.2 - q.1)) then 4
      else if (spans a 0).1.any (malLine a) then 5 else 0

/-- The lines after the first start past the section's start. -/
theorem lines_after {a : Bytes} {s p : Nat} {q : Nat × Nat} {L : List (Nat × Nat)} (h : Lines a s (q :: L) p) :
    q.1 = s ∧ ∀ q' ∈ L, q'.1 ≠ 0 := by
  obtain ⟨h1, hL⟩ := lines_tail h
  refine ⟨h1, fun q' hq' => ?_⟩
  have := (lines_mem hL q' hq').1
  omega

/-- **The refusals of the section's shape**: `checkWith` refuses as `shapeOf` says. Else it goes on to the fields the
groups of lines make. -/
theorem checkWith_shape (r : Rules) (ctx : Context) (a : Bytes) :
    checkWith r ctx a = match shapeOf r a with
      | 1 => .refused .noHeader
      | 2 => .refused .noSeparator
      | 3 => .refused .headerTooLong
      | 4 => .refused .lineTooLong
      | 5 => .refused .malformed
      | _ => tailOf r ctx ((groups a (spans a 0).1).map (fieldOf a)) := by
  rw [checkWith_places]
  unfold shapeOf
  by_cases he : (spans a 0).1 = []
  · simp [he]
  · simp only [if_neg he]
    cases hp : (spans a 0).2 with
    | none => rfl
    | some p =>
      simp only
      have hl := spans_lines a _ 0 rfl (Nat.zero_le _) (show spans a 0 = ((spans a 0).1, some p) by rw [← hp])
      obtain ⟨q, L, hqL⟩ : ∃ q L, (spans a 0).1 = q :: L := by
        cases h : (spans a 0).1 with
        | nil => exact absurd h he
        | cons q L => exact ⟨q, L, rfl⟩
      rw [hqL] at hl ⊢
      obtain ⟨h0, hL⟩ := lines_after hl
      by_cases h3 : r.headerMax < p
      · simp [h3]
      · simp only [if_neg h3]
        by_cases h4 : ((q :: L).any fun q => decide (r.lineMax < q.2 - q.1)) = true
        · simp [h4]
        · simp only [h4, Bool.false_eq_true, if_false]
          by_cases h5 : (q :: L).any (malLine a) = true
          · rw [if_pos h5, (groupL_none a h0 hL).2 h5]
          · have h5' : (q :: L).any (malLine a) = false := by simpa using h5
            rw [if_neg h5, groupL_groups a h0 hL h5']

theorem spans_end (a : Bytes) {s : Nat} (h : eolOf a s a.length = a.length) : (spans a s).2 = none := by
  rw [spans, dif_neg (fun h' => by omega)]

theorem spans_sep (a : Bytes) {s : Nat} (hs : s ≤ a.length) (hlt : eolOf a s a.length < a.length)
    (he : eolOf a s a.length = s) : spans a s = ([], some s) := by
  rw [spans, dif_pos ⟨hlt, hs⟩, if_pos he]

theorem spans_line (a : Bytes) {s : Nat} (hs : s ≤ a.length) (hlt : eolOf a s a.length < a.length)
    (he : eolOf a s a.length ≠ s) :
    spans a s = ((s, eolOf a s a.length) :: (spans a (eolOf a s a.length + 2)).1,
      (spans a (eolOf a s a.length + 2)).2) := by
  rw [spans, dif_pos ⟨hlt, hs⟩, if_neg he]

theorem shapeOf_nil {r : Rules} {a : Bytes} (h : (spans a 0).1 = []) : shapeOf r a = 1 := by
  unfold shapeOf; rw [if_pos h]

/-! ## The premises can hold -/

/-- A section of one field, `x:`, and the empty line. -/
def wArt : Bytes := [120#8, 58#8, 13#8, 10#8, 13#8, 10#8]

theorem lines_witness : Lines wArt 0 [(0, 2)] 4 :=
  .line (by decide) (by decide) (by decide) (.sep (by decide) (by decide))

theorem fieldAt_witness : FieldAt wArt 4 0 2 [] := ⟨lines_witness, by decide, by decide⟩

end DN.News.ArticleLines
