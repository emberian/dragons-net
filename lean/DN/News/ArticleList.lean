-- SPDX-License-Identifier: AGPL-3.0-or-later
import DN.News.ArticleDate

/-!
# DN.News.ArticleList

The lists the article's rules read, Newsgroups', Distribution's and Path's, modelled as `artElem` reads them. An
element at a time, white space and line ends left out; reserved group names checked on the way.
-/

namespace DN.News.ArticleList

open DN.News.ArticleSpec (Bytes listed pathElements reserved isPosted named)
open DN.News.FrameSpec (DOT)
open DN.News.CommandSpec (ascii)
open DN.News.ArticleScan (gap)
open DN.News.ArticleLines (seg)
open DN.News.ArticleDate (sp_free sp_sep spp_cons)

/-! ## Reserved names, a byte at a time -/

/-- Whether a component makes a name reserved: `all` or `ctl` anywhere, `example`, `to` or `control` first. -/
def compRes (first : Bool) (c : Bytes) : Bool :=
  c == ascii "all" || c == ascii "ctl" || first && (c == ascii "example" || c == ascii "to" || c == ascii "control")

/-- `artElem`'s check of reserved names: in the first component or not, reserved so far, the component so far. -/
structure RS where
  first : Bool
  res : Bool
  comp : Bytes

/-- One byte of the check. -/
def rsStep (r : RS) (b : BitVec 8) : RS :=
  if b == DOT then ⟨false, r.res || compRes r.first r.comp, []⟩ else { r with comp := r.comp ++ [b] }

/-- The check's verdict at the element's end. -/
def rsEnd (r : RS) : Bool := r.res || compRes r.first r.comp

def rs0 : RS := ⟨true, false, []⟩

/-- The components' verdict, the first told apart. -/
def compsRes (first : Bool) : List Bytes → Bool
  | [] => false
  | c :: cs => compRes first c || compsRes false cs

theorem rs_fold : ∀ (l : Bytes) (r : RS), rsEnd (l.foldl rsStep r) =
    (r.res || compsRes r.first (List.splitOnPPrepend (· == DOT) l r.comp.reverse))
  | [], r => by simp [rsEnd, compsRes]
  | b :: l, r => by
    rw [List.foldl_cons, rs_fold l]
    unfold rsStep
    cases hb : b == DOT
    · simp only [Bool.false_eq_true, if_false, spp_cons, hb, List.reverse_append, List.reverse_cons,
        List.reverse_nil, List.nil_append, List.singleton_append]
    · simp only [if_true, spp_cons, hb, compsRes, List.reverse_reverse, List.reverse_nil, Bool.or_assoc]

theorem sp_cons {p : BitVec 8 → Bool} : ∀ (l acc : Bytes), ∃ c cs, List.splitOnPPrepend p l acc = c :: cs
  | [], acc => ⟨_, _, rfl⟩
  | b :: l, acc => by
    cases hb : p b
    · simp only [spp_cons, hb, Bool.false_eq_true, if_false]; exact sp_cons l _
    · simp only [spp_cons, hb, if_true]; exact ⟨_, _, rfl⟩

theorem compsRes_false : ∀ cs : List Bytes, compsRes false cs = cs.any (fun c => c == ascii "all" || c == ascii "ctl")
  | [] => rfl
  | c :: cs => by simp [compsRes, compRes, compsRes_false cs]

/-- **`reserved` as `artElem` checks it**, a byte at a time. -/
theorem reserved_rs (g : Bytes) :
    reserved g = (rsEnd (g.foldl rsStep rs0) || (g == ascii "poster" || g == ascii "junk")) := by
  rw [rs_fold]
  have e : g.splitOn DOT = List.splitOnPPrepend (· == DOT) g [] := List.splitOnP_eq_splitOnPPrepend
  obtain ⟨c, cs, hc⟩ := sp_cons (p := (· == DOT)) g []
  unfold reserved
  simp only [e, hc, rs0, List.reverse_nil, compsRes, compsRes_false, compRes, List.headD_cons, List.any_cons]
  cases ha : c == ascii "all" <;> cases hb : c == ascii "ctl" <;> cases hx : c == ascii "example" <;>
    cases ht : c == ascii "to" <;> cases hl : c == ascii "control" <;> cases hp : g == ascii "poster" <;>
    cases hj : g == ascii "junk" <;> simp

/-! ## The elements of a list -/

/-- Where the element from `p` ends: at the separator `sep`, or at `e`. -/
def elemEnd (a : Bytes) (p e : Nat) (sep : BitVec 8) : Nat := p + ((seg a p e).takeWhile (· != sep)).length

/-- The element from `p`: its bytes but white space and line ends. -/
def elem (a : Bytes) (p e : Nat) (sep : BitVec 8) : Bytes := (seg a p (elemEnd a p e sep)).filter (!gap ·)

/-- Where the next element starts: past the separator, or at `e`. -/
def elemNext (a : Bytes) (p e : Nat) (sep : BitVec 8) : Nat :=
  if elemEnd a p e sep < e then elemEnd a p e sep + 1 else e

theorem elemEnd_le {a : Bytes} {p e : Nat} {sep : BitVec 8} (hpe : p ≤ e) (he : e ≤ a.length) :
    elemEnd a p e sep ≤ e := by
  unfold elemEnd; have := DN.News.ArticleScan.tw_le (p := (· != sep)) (seg a p e)
  rw [DN.News.ArticleLines.seg_length a hpe he] at this; omega

theorem elemNext_gt {a : Bytes} {p e : Nat} {sep : BitVec 8} (h : p < e) : p < elemNext a p e sep := by
  unfold elemNext; split
  · unfold elemEnd; omega
  · exact h

theorem elemNext_le {a : Bytes} {p e : Nat} {sep : BitVec 8} : elemNext a p e sep ≤ e := by
  unfold elemNext; split <;> omega

/-- The element's bytes hold no separator. -/
theorem elem_free {a : Bytes} {p e : Nat} {sep : BitVec 8} (hpe : p ≤ e) (he : e ≤ a.length) :
    ∀ b ∈ seg a p (elemEnd a p e sep), (b == sep) = false := by
  intro b hb
  have hk : ((seg a p e).takeWhile (· != sep)).length ≤ e - p := by
    have := DN.News.ArticleScan.tw_le (p := (· != sep)) (seg a p e)
    rwa [DN.News.ArticleLines.seg_length a hpe he] at this
  unfold elemEnd at hb
  rw [← DN.News.ArticleLines.seg_take a _ hk, ← DN.News.ArticleLines.takeWhile_take] at hb
  have := List.all_eq_true.1 List.all_takeWhile b hb
  simpa using this

/-- At the element's end before `e` stands the separator. -/
theorem elemEnd_sep {a : Bytes} {p e : Nat} {sep : BitVec 8} (he : e ≤ a.length)
    (h : elemEnd a p e sep < e) : a[elemEnd a p e sep]! = sep := by
  have hd := DN.News.ArticleScan.drop_tw (p := (· != sep)) (seg a p e)
  rw [DN.News.ArticleScan.seg_drop] at hd
  change seg a (elemEnd a p e sep) e = _ at hd
  rw [DN.News.ArticleRun.seg_cons a h he] at hd
  cases hl : (seg a p e).dropWhile (· != sep) with
  | nil => rw [hl] at hd; cases hd
  | cons x l =>
    rw [hl] at hd
    obtain ⟨rfl, -⟩ := List.cons.inj hd
    have := List.head_dropWhile_not (· != sep) (l := seg a p e) (by rw [hl]; simp)
    simp only [hl, List.head_cons] at this
    simpa using this

/-- **The list split at its first separator**, white space and line ends left out. -/
theorem split_elem {a : Bytes} {p e : Nat} {sep : BitVec 8} (hsep : gap sep = false) (hpe : p ≤ e)
    (he : e ≤ a.length) : ((seg a p e).filter (!gap ·)).splitOn sep = elem a p e sep ::
      (if elemEnd a p e sep < e then ((seg a (elemEnd a p e sep + 1) e).filter (!gap ·)).splitOn sep else []) := by
  have hk := elemEnd_le (sep := sep) hpe he
  have hfree := elem_free (sep := sep) hpe he
  have e1 : ∀ l : Bytes, l.splitOn sep = List.splitOnPPrepend (· == sep) l [] := fun _ =>
    List.splitOnP_eq_splitOnPPrepend
  have hfree' : ∀ x ∈ elem a p e sep, (x == sep) = false := fun x hx => hfree x (List.mem_filter.1 hx).1
  split
  · rename_i hlt
    have hsplit : seg a p e =
        seg a p (elemEnd a p e sep) ++ a[elemEnd a p e sep]! :: seg a (elemEnd a p e sep + 1) e := by
      rw [DN.News.ArticleLines.seg_app a (cp := elemEnd a p e sep) (Nat.le_add_right _ _) hk,
        DN.News.ArticleRun.seg_cons a hlt he]
    rw [hsplit, List.filter_append, List.filter_cons, elemEnd_sep he hlt, hsep]
    simp only [Bool.not_false, if_true]
    rw [e1, sp_sep ((seg a p (elemEnd a p e sep)).filter (!gap ·)) sep _ [] hfree' (by simp), e1]
    rfl
  · rename_i hge
    have heq : elemEnd a p e sep = e := by omega
    have hall : ∀ x ∈ (seg a p e).filter (!gap ·), (x == sep) = false := by
      intro x hx; rw [← heq] at hx; exact hfree' x hx
    rw [e1, sp_free _ [] hall]
    simp [elem, heq]

/-- The elements a loop from `p` visits while `p < e`. -/
def elems (a : Bytes) (e : Nat) (sep : BitVec 8) (p : Nat) : List Bytes :=
  if p < e then elem a p e sep :: elems a e sep (elemNext a p e sep) else []
termination_by e - p
decreasing_by
  have h1 := elemNext_gt (a := a) (sep := sep) ‹p < e›
  have h2 := elemNext_le (a := a) (p := p) (e := e) (sep := sep)
  omega

theorem elems_eq (a : Bytes) (e : Nat) (sep : BitVec 8) (p : Nat) :
    elems a e sep p = if p < e then elem a p e sep :: elems a e sep (elemNext a p e sep) else [] := by
  rw [elems]

/-- **A list's elements as the loop visits them**: those of `splitOn`, but an empty one at the end. -/
theorem split_elems {a : Bytes} {sep : BitVec 8} (hsep : gap sep = false) {e : Nat} (he : e ≤ a.length) :
    ∀ k p, e - p = k → p ≤ e → ∃ t, ((seg a p e).filter (!gap ·)).splitOn sep = elems a e sep p ++ t ∧
      (t = [] ∨ t = [[]])
  | k, p, hk, hpe => by
    rw [elems_eq]
    by_cases hp : p < e
    · rw [if_pos hp, split_elem hsep hpe he]
      split
      · rename_i hlt
        have hn : elemNext a p e sep = elemEnd a p e sep + 1 := by unfold elemNext; rw [if_pos hlt]
        obtain ⟨t, ht, h0⟩ := split_elems hsep he (e - (elemEnd a p e sep + 1)) _ rfl (by omega)
        refine ⟨t, ?_, h0⟩
        rw [ht, hn]; rfl
      · rename_i hge
        have hn : elemNext a p e sep = e := by unfold elemNext; rw [if_neg hge]
        refine ⟨[], ?_, .inl rfl⟩
        rw [hn, elems_eq, if_neg (Nat.lt_irrefl _)]; rfl
    · have he' : p = e := by omega
      subst he'
      rw [if_neg hp, DN.News.ArticleLines.seg_self]
      exact ⟨[[]], rfl, .inr rfl⟩
termination_by k => k
decreasing_by
  have := elemNext_gt (a := a) (sep := sep) hp
  omega

/-- **`listed` as the loop reads it**: the elements but the empty ones. -/
theorem listed_elems {a : Bytes} {s e : Nat} (hse : s ≤ e) (he : e ≤ a.length) :
    listed (seg a s e) = (elems a e ArticleSpec.COMMA s).filter (!·.isEmpty) := by
  obtain ⟨t, ht, h0⟩ := split_elems (sep := ArticleSpec.COMMA) (by decide) he _ s rfl hse
  unfold listed
  show (((seg a s e).filter (!gap ·)).splitOn ArticleSpec.COMMA).filter (!·.isEmpty) = _
  rw [ht, List.filter_append]
  rcases h0 with rfl | rfl <;> simp

/-- **Any of a list's names**, as the loop asks, for a test the empty element fails. -/
theorem listed_any {a : Bytes} {s e : Nat} (hse : s ≤ e) (he : e ≤ a.length) {P : Bytes → Bool} (hP : P [] = false) :
    (listed (seg a s e)).any P = (elems a e ArticleSpec.COMMA s).any P := by
  rw [listed_elems hse he]
  generalize elems a e ArticleSpec.COMMA s = l
  induction l with
  | nil => rfl
  | cons x l ih => cases x <;> simp [hP, ih]

/-- **Any of Path's elements**, as the loop asks, for a test the empty element fails. -/
theorem path_any {a : Bytes} {s e : Nat} (hse : s ≤ e) (he : e ≤ a.length) {P : Bytes → Bool} (hP : P [] = false) :
    (pathElements (seg a s e)).any P = (elems a e ArticleSpec.BANG s).any P := by
  obtain ⟨t, ht, h0⟩ := split_elems (sep := ArticleSpec.BANG) (by decide) he _ s rfl hse
  unfold pathElements
  show (((seg a s e).filter (!gap ·)).splitOn ArticleSpec.BANG).any P = _
  rw [ht, List.any_append]
  rcases h0 with rfl | rfl <;> simp [hP]

/-! ## Path's diagnostic `.POSTED` -/

/-- A name spelling `posted` holds six bytes, none of them a dot. -/
theorem posted_dotless {x : Bytes} (h : named x "posted" = true) : x.length = 6 ∧ x.all (· != DOT) = true := by
  unfold named ArticleSpec.sameName at h
  have e := beq_iff_eq.1 h
  refine ⟨by simpa using congrArg List.length e, List.all_eq_true.2 fun b hb => ?_⟩
  have hm : ArticleSpec.lowerB b ∈ (ascii "posted").map ArticleSpec.lowerB := e ▸ List.mem_map_of_mem hb
  rw [bne_iff_ne]; rintro rfl; revert hm; decide +kernel

/-- The byte `takeWhile` stops at fails the test. -/
theorem tw_stop {p : BitVec 8 → Bool} {l : Bytes} (h : (l.takeWhile p).length < l.length) :
    p l[(l.takeWhile p).length]! = false := by
  rw [getElem!_pos l _ h]; exact DN.News.ArticleDate.tw_head (List.drop_eq_getElem_cons h)

/-- **The keyword after the dot**, as the program reads it: six bytes spelling `posted`, then the end or a dot. -/
theorem tw_posted (rest : Bytes) : named (rest.takeWhile (· != DOT)) "posted" =
    (decide (6 ≤ rest.length) && named (rest.take 6) "posted" && (decide (rest.length = 6) || rest[6]! == DOT)) := by
  have htk := DN.News.ArticleLines.takeWhile_take rest (· != DOT)
  apply Bool.eq_iff_iff.2
  simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true, beq_iff_eq]
  constructor
  · intro h
    obtain ⟨h6, -⟩ := posted_dotless h
    have hle := DN.News.ArticleScan.tw_le (p := fun b : DN.News.FrameSpec.Byte => b != DOT) rest
    refine ⟨⟨by omega, by rw [← h6, ← htk]; exact h⟩, ?_⟩
    by_cases hl : rest.length = 6
    · exact .inl hl
    · have hs := tw_stop (p := fun b : DN.News.FrameSpec.Byte => b != DOT) (l := rest) (by omega)
      rw [h6] at hs
      exact .inr (by simpa using hs)
  · rintro ⟨⟨h6, hn⟩, hst⟩
    obtain ⟨-, hall⟩ := posted_dotless hn
    have hlen : (rest.takeWhile (· != DOT)).length = 6 := DN.News.ArticleScan.tw_len rest 6 h6 hall fun h => by
      rcases hst with e | e
      · omega
      · rw [← getElem!_pos rest 6 h, e]; rfl
    rw [htk, hlen]; exact hn

/-- **`isPosted` as the program reads the element**: more than six bytes, a dot, `posted`, then the end or a dot. -/
theorem isPosted_eq (e : Bytes) : isPosted e = (decide (6 < e.length) && e[0]! == DOT &&
    named ((e.drop 1).take 6) "posted" && (decide (e.length = 7) || e[7]! == DOT)) := by
  cases e with
  | nil => rfl
  | cons d rest =>
    have hP : named (rest.takeWhile (· != DOT)) "POSTED" = named (rest.takeWhile (· != DOT)) "posted" := by
      unfold named ArticleSpec.sameName
      rw [show (ascii "POSTED").map ArticleSpec.lowerB = (ascii "posted").map ArticleSpec.lowerB by decide +kernel]
    have e1 : decide (6 < rest.length + 1) = decide (6 ≤ rest.length) := by simp only [decide_eq_decide]; omega
    have e2 : decide (rest.length + 1 = 7) = decide (rest.length = 6) := by simp only [decide_eq_decide]; omega
    simp only [isPosted, hP, tw_posted, List.length_cons, List.drop_succ_cons, List.drop_zero,
      List.getElem!_cons_zero, List.getElem!_cons_succ, e1, e2]
    generalize (d == DOT) = x
    cases x <;> simp

end DN.News.ArticleList
