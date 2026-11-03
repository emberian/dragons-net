-- SPDX-License-Identifier: AGPL-3.0-or-later
import DN.News.AbnfProg

/-!
# DN.News.AbnfMatch

What a grammar matches, as a relation: `Matches g input t p e` when a match of `t` from `p` can end at `e`. This is the
plain meaning `Abnf.endsFrom` works out with memo and fuel. A class or string term matches as its class
(`AbnfProg.classOf`) or string (`AbnfProg.textOf`) says.
-/

namespace DN.News.AbnfMatch

open DN.News.Abnf DN.News.AbnfProg DN.News.AbnfRules

section
variable (g : Array Term) (input : Array Nat)

mutual
/-- A match of `t` from `p` that ends at `e`. -/
inductive Matches : Term → Nat → Nat → Prop
  | range {lo hi p b : Nat} : input[p]? = some b → lo ≤ b → b ≤ hi → Matches (.range lo hi) p (p + 1)
  | text {s : String} {p : Nat} : at? input lower p (codes s) = true → Matches (.text s) p (p + (codes s).length)
  | exact {s : List Nat} {p : Nat} : at? input id p s = true → Matches (.exact s) p (p + s.length)
  | ref {i p e : Nat} {u : Term} : g[i]? = some u → Matches u p e → Matches (.ref i) p e
  | seq {ts : List Term} {p e : Nat} : Seq ts p e → Matches (.seq ts) p e
  | alt {ts : List Term} {t : Term} {p e : Nat} : t ∈ ts → Matches t p e → Matches (.alt ts) p e
  | rep {lo : Nat} {hi : Option Nat} {t : Term} {p e k : Nat} : lo ≤ k → (∀ h ∈ hi, k ≤ h) → Rep t k p e →
      Matches (.rep lo hi t) p e
/-- Matches of the terms in a row. -/
inductive Seq : List Term → Nat → Nat → Prop
  | nil {p : Nat} : Seq [] p p
  | cons {t : Term} {ts : List Term} {p q e : Nat} : Matches t p q → Seq ts q e → Seq (t :: ts) p e
/-- `k` matches of `t` in a row. -/
inductive Rep : Term → Nat → Nat → Nat → Prop
  | zero {t : Term} {p : Nat} : Rep t 0 p p
  | succ {t : Term} {k p q e : Nat} : Matches t p q → Rep t k q e → Rep t (k + 1) p e
end

end

variable {g : Array Term} {input : Array Nat}

/-! ## Each kind of term -/

theorem range_iff {lo hi p e : Nat} :
    Matches g input (.range lo hi) p e ↔ (∃ b, input[p]? = some b ∧ lo ≤ b ∧ b ≤ hi) ∧ e = p + 1 :=
  ⟨fun h => by cases h with | range hb h1 h2 => exact ⟨⟨_, hb, h1, h2⟩, rfl⟩,
    fun ⟨⟨_, hb, h1, h2⟩, he⟩ => he ▸ .range hb h1 h2⟩

theorem text_iff {s : String} {p e : Nat} :
    Matches g input (.text s) p e ↔ at? input lower p (codes s) = true ∧ e = p + (codes s).length :=
  ⟨fun h => by cases h with | text h => exact ⟨h, rfl⟩, fun ⟨h, he⟩ => he ▸ .text h⟩

theorem exact_iff {s : List Nat} {p e : Nat} :
    Matches g input (.exact s) p e ↔ at? input id p s = true ∧ e = p + s.length :=
  ⟨fun h => by cases h with | exact h => exact ⟨h, rfl⟩, fun ⟨h, he⟩ => he ▸ .exact h⟩

theorem ref_iff {i p e : Nat} : Matches g input (.ref i) p e ↔ ∃ u, g[i]? = some u ∧ Matches g input u p e :=
  ⟨fun h => by cases h with | ref hu h => exact ⟨_, hu, h⟩, fun ⟨_, hu, h⟩ => .ref hu h⟩

theorem ref_iff' {i p e : Nat} {u : Term} (hu : g[i]? = some u) :
    Matches g input (.ref i) p e ↔ Matches g input u p e := by
  rw [ref_iff]
  exact ⟨fun ⟨_, h1, h⟩ => by rw [hu] at h1; cases h1; exact h, fun h => ⟨u, hu, h⟩⟩

theorem seq_iff {ts : List Term} {p e : Nat} : Matches g input (.seq ts) p e ↔ Seq g input ts p e :=
  ⟨fun h => by cases h with | seq h => exact h, .seq⟩

theorem alt_iff {ts : List Term} {p e : Nat} : Matches g input (.alt ts) p e ↔ ∃ t ∈ ts, Matches g input t p e :=
  ⟨fun h => by cases h with | alt ht h => exact ⟨_, ht, h⟩, fun ⟨_, ht, h⟩ => .alt ht h⟩

theorem rep_iff {lo : Nat} {hi : Option Nat} {t : Term} {p e : Nat} :
    Matches g input (.rep lo hi t) p e ↔ ∃ k, lo ≤ k ∧ (∀ h ∈ hi, k ≤ h) ∧ Rep g input t k p e :=
  ⟨fun h => by cases h with | rep h1 h2 h => exact ⟨_, h1, h2, h⟩, fun ⟨_, h1, h2, h⟩ => .rep h1 h2 h⟩

theorem seq_nil_iff {p e : Nat} : Seq g input [] p e ↔ e = p :=
  ⟨fun h => by cases h; rfl, fun h => h ▸ .nil⟩

theorem seq_cons_iff {t : Term} {ts : List Term} {p e : Nat} :
    Seq g input (t :: ts) p e ↔ ∃ q, Matches g input t p q ∧ Seq g input ts q e :=
  ⟨fun h => by cases h with | cons h1 h2 => exact ⟨_, h1, h2⟩, fun ⟨_, h1, h2⟩ => .cons h1 h2⟩

theorem rep_zero_iff {t : Term} {p e : Nat} : Rep g input t 0 p e ↔ e = p :=
  ⟨fun h => by cases h; rfl, fun h => h ▸ .zero⟩

theorem rep_succ_iff {t : Term} {k p e : Nat} :
    Rep g input t (k + 1) p e ↔ ∃ q, Matches g input t p q ∧ Rep g input t k q e :=
  ⟨fun h => by cases h with | succ h1 h2 => exact ⟨_, h1, h2⟩, fun ⟨_, h1, h2⟩ => .succ h1 h2⟩

/-- Any number of matches. -/
theorem star_iff {t : Term} {p e : Nat} : Matches g input (.rep 0 none t) p e ↔ ∃ k, Rep g input t k p e := by
  rw [rep_iff]
  exact ⟨fun ⟨k, _, _, h⟩ => ⟨k, h⟩, fun ⟨k, h⟩ => ⟨k, Nat.zero_le _, (fun _ h => nomatch h), h⟩⟩

/-- An optional match. -/
theorem opt_iff {t : Term} {p e : Nat} : Matches g input (.rep 0 (some 1) t) p e ↔ e = p ∨ Matches g input t p e := by
  rw [rep_iff]
  constructor
  · rintro ⟨k, _, hk, h⟩
    have := hk 1 rfl
    match k, h with
    | 0, h => exact .inl (rep_zero_iff.1 h)
    | 1, h =>
      obtain ⟨q, h1, h2⟩ := rep_succ_iff.1 h
      exact .inr (rep_zero_iff.1 h2 ▸ h1)
  · rintro (h | h)
    · exact ⟨0, Nat.zero_le _, fun _ h => by cases h; decide, rep_zero_iff.2 h⟩
    · exact ⟨1, Nat.zero_le _, fun _ h => by cases h; exact Nat.le_refl _, .succ h .zero⟩

/-- At least one match. -/
theorem plus_iff {t : Term} {p e : Nat} :
    Matches g input (.rep 1 none t) p e ↔ ∃ q, Matches g input t p q ∧ ∃ k, Rep g input t k q e := by
  rw [rep_iff]
  constructor
  · rintro ⟨k, hk, _, h⟩
    match k, hk, h with
    | k + 1, _, h =>
      obtain ⟨q, h1, h2⟩ := rep_succ_iff.1 h
      exact ⟨q, h1, k, h2⟩
  · rintro ⟨q, h1, k, h2⟩
    exact ⟨k + 1, Nat.succ_le_succ (Nat.zero_le _), (fun _ h => nomatch h), Rep.succ h1 h2⟩

/-! ## A byte of a class, a string -/

/-- Whether `b` lies in one of the ranges `rs`. -/
def InRanges (rs : List (Nat × Nat)) (b : Nat) : Prop := ∃ r ∈ rs, r.1 ≤ b ∧ b ≤ r.2

theorem lower_lower (b : Nat) : lower (lower b) = lower b := by
  unfold lower
  by_cases h : 65 ≤ b ∧ b ≤ 90
  · rw [if_pos h, if_neg (by omega)]
  · rw [if_neg h, if_neg h]

/-- A letter in either case is what `lower` takes to the same letter. -/
theorem caseRanges_iff (b c : Nat) : InRanges (caseRanges c) b ↔ lower b = lower c := by
  unfold caseRanges InRanges lower
  by_cases h1 : 65 ≤ c ∧ c ≤ 90
  · simp only [if_pos h1, List.mem_cons, List.not_mem_nil, or_false, exists_eq_or_imp, exists_eq_left]
    by_cases hb : 65 ≤ b ∧ b ≤ 90
    · rw [if_pos hb]; constructor <;> intro h <;> omega
    · rw [if_neg hb]; constructor <;> intro h <;> omega
  · by_cases h2 : 97 ≤ c ∧ c ≤ 122
    · simp only [if_neg h1, if_pos h2, List.mem_cons, List.not_mem_nil, or_false, exists_eq_or_imp,
        exists_eq_left]
      by_cases hb : 65 ≤ b ∧ b ≤ 90
      · rw [if_pos hb]; constructor <;> intro h <;> omega
      · rw [if_neg hb]; constructor <;> intro h <;> omega
    · simp only [if_neg h1, if_neg h2, List.mem_cons, List.not_mem_nil, or_false, exists_eq_left]
      by_cases hb : 65 ≤ b ∧ b ≤ 90
      · rw [if_pos hb]; constructor <;> intro h <;> omega
      · rw [if_neg hb]; constructor <;> intro h <;> omega

theorem at_one {norm : Nat → Nat} {p c : Nat} :
    at? input norm p [c] = true ↔ ∃ b, input[p]? = some b ∧ norm b = norm c := by
  unfold at?
  split <;> simp_all [at?]

/-- **A term that is a class** matches one byte, of the class. -/
theorem classOf_iff : ∀ (f : Nat) (t : Term) (rs : List (Nat × Nat)), classOf f t = some rs → ∀ p e,
    Matches grammar input t p e ↔ (∃ b, input[p]? = some b ∧ InRanges rs b) ∧ e = p + 1
  | 0, _, _, h, _, _ => nomatch h
  | f + 1, .range lo hi, rs, h, p, e => by
    simp only [classOf, Option.some.injEq] at h; subst h
    rw [range_iff]; simp only [InRanges, List.mem_cons, List.not_mem_nil, or_false, exists_eq_left]
  | f + 1, .text s, rs, h, p, e => by
    simp only [classOf] at h
    split at h
    · rename_i c hc
      cases h
      rw [text_iff, hc, at_one]
      simp only [List.length_cons, List.length_nil, Nat.zero_add]
      exact ⟨fun ⟨⟨b, hb, hl⟩, he⟩ => ⟨⟨b, hb, (caseRanges_iff b c).2 hl⟩, he⟩,
        fun ⟨⟨b, hb, hl⟩, he⟩ => ⟨⟨b, hb, (caseRanges_iff b c).1 hl⟩, he⟩⟩
    · cases h
  | f + 1, .exact s, rs, h, p, e => by
    match s, h with
    | [c], h =>
      simp only [classOf, Option.some.injEq] at h; subst h
      rw [exact_iff, at_one]
      simp only [InRanges, List.mem_cons, List.not_mem_nil, or_false, exists_eq_left, id, List.length_cons,
        List.length_nil, Nat.zero_add]
      exact ⟨fun ⟨⟨b, hb, hl⟩, he⟩ => ⟨⟨b, hb, by omega, by omega⟩, he⟩,
        fun ⟨⟨b, hb, h1, h2⟩, he⟩ => ⟨⟨b, hb, by omega⟩, he⟩⟩
    | [], h => simp [classOf] at h
    | _ :: _ :: _, h => simp [classOf] at h
  | f + 1, .ref i, rs, h, p, e => by
    simp only [classOf] at h
    split at h
    · cases h
    · cases hu : grammar[i]? with
      | none => rw [hu] at h; cases h
      | some u =>
        rw [hu] at h
        rw [ref_iff' hu]
        exact classOf_iff f u rs h p e
  | f + 1, .alt ts, rs, h, p, e => by
    simp only [classOf] at h
    rw [alt_iff]
    obtain ⟨rss, hm, hr⟩ := Option.map_eq_some_iff.1 h
    subst hr
    clear h
    induction ts generalizing rss with
    | nil =>
      simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at hm; subst hm
      simp [InRanges]
    | cons u us ih =>
      simp only [List.mapM_cons, Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff,
        Option.some.injEq] at hm
      obtain ⟨r, hr, rs', hrs, he⟩ := hm
      subst he
      have h1 := classOf_iff f u r hr p e
      have h2 := ih rs' hrs
      simp only [List.mem_cons, List.flatten_cons, InRanges, List.mem_append] at h1 h2 ⊢
      constructor
      · rintro ⟨t, ht | ht, hm⟩
        · subst ht
          obtain ⟨⟨b, hb, r', hr', hl⟩, he⟩ := h1.1 hm
          exact ⟨⟨b, hb, r', .inl hr', hl⟩, he⟩
        · obtain ⟨⟨b, hb, r', hr', hl⟩, he⟩ := h2.1 ⟨t, ht, hm⟩
          exact ⟨⟨b, hb, r', .inr hr', hl⟩, he⟩
      · rintro ⟨⟨b, hb, r', hr' | hr', hl⟩, he⟩
        · exact ⟨u, .inl rfl, h1.2 ⟨⟨b, hb, r', hr', hl⟩, he⟩⟩
        · obtain ⟨t, ht, hm⟩ := h2.2 ⟨⟨b, hb, r', hr', hl⟩, he⟩
          exact ⟨t, .inr ht, hm⟩
  | f + 1, .seq _, _, h, _, _ => by simp [classOf] at h
  | f + 1, .rep _ _ _, _, h, _, _ => by simp [classOf] at h

theorem at_map_lower {p : Nat} {cs : List Nat} : at? input lower p (cs.map lower) = at? input lower p cs := by
  induction cs generalizing p with
  | nil => rfl
  | cons c cs ih => simp only [List.map_cons, at?, lower_lower, ih]

/-- **A term that is a string** matches it, letters in either case when `cl`. -/
theorem textOf_iff (f : Nat) : ∀ (t : Term) (bs : List Nat) (cl : Bool), textOf f t = some (bs, cl) → ∀ p e,
    Matches grammar input t p e ↔ at? input (if cl then lower else id) p bs = true ∧ e = p + bs.length := by
  induction f with
  | zero => intro _ _ _ h; nomatch h
  | succ f ih =>
    intro t bs cl h p e
    cases t with
    | text s =>
      simp only [textOf, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      rw [text_iff, if_pos rfl, at_map_lower, List.length_map]
    | exact s =>
      simp only [textOf, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      rw [exact_iff]; simp only [Bool.false_eq_true, if_false]
    | ref i =>
      simp only [textOf] at h
      cases hu : grammar[i]? with
      | none => rw [hu] at h; cases h
      | some u =>
        rw [hu] at h
        rw [ref_iff' hu]
        exact ih u bs cl h p e
    | range => simp [textOf] at h
    | seq => simp [textOf] at h
    | alt => simp [textOf] at h
    | rep => simp [textOf] at h

/-! ## Positions go forward -/

mutual
theorem Matches.le {t : Term} {p e : Nat} : Matches g input t p e → p ≤ e
  | .range .. => Nat.le_succ _
  | .text _ => Nat.le_add_right _ _
  | .exact _ => Nat.le_add_right _ _
  | .ref _ h => Matches.le h
  | .seq h => Seq.le h
  | .alt _ h => Matches.le h
  | .rep _ _ h => Rep.le h
theorem Seq.le {ts : List Term} {p e : Nat} : Seq g input ts p e → p ≤ e
  | .nil => Nat.le_refl _
  | .cons h1 h2 => Nat.le_trans (Matches.le h1) (Seq.le h2)
theorem Rep.le {t : Term} {k p e : Nat} : Rep g input t k p e → p ≤ e
  | .zero => Nat.le_refl _
  | .succ h1 h2 => Nat.le_trans (Matches.le h1) (Rep.le h2)
end

/-! ## Terms compared -/

mutual
/-- Whether two terms are the same. -/
def termEq : Term → Term → Bool
  | .range a b, .range c d => a == c && b == d
  | .text s, .text t => s == t
  | .exact s, .exact t => s == t
  | .ref i, .ref j => i == j
  | .seq ts, .seq us => termsEq ts us
  | .alt ts, .alt us => termsEq ts us
  | .rep a b t, .rep c d u => a == c && b == d && termEq t u
  | _, _ => false
def termsEq : List Term → List Term → Bool
  | [], [] => true
  | t :: ts, u :: us => termEq t u && termsEq ts us
  | _, _ => false
end

mutual
theorem termEq_sound : ∀ t u : Term, termEq t u = true → t = u
  | .range a b, .range c d, h => by simp only [termEq, Bool.and_eq_true, beq_iff_eq] at h; rw [h.1, h.2]
  | .text s, .text t, h => by simp only [termEq, beq_iff_eq] at h; rw [h]
  | .exact s, .exact t, h => by simp only [termEq, beq_iff_eq] at h; rw [h]
  | .ref i, .ref j, h => by simp only [termEq, beq_iff_eq] at h; rw [h]
  | .seq ts, .seq us, h => by simp only [termEq] at h; rw [termsEq_sound ts us h]
  | .alt ts, .alt us, h => by simp only [termEq] at h; rw [termsEq_sound ts us h]
  | .rep a b t, .rep c d u, h => by
    simp only [termEq, Bool.and_eq_true, beq_iff_eq] at h; rw [h.1.1, h.1.2, termEq_sound t u h.2]
  | .range .., .text _, h | .range .., .exact _, h | .range .., .ref _, h | .range .., .seq _, h
  | .range .., .alt _, h | .range .., .rep .., h => by simp [termEq] at h
  | .text _, .range .., h | .text _, .exact _, h | .text _, .ref _, h | .text _, .seq _, h
  | .text _, .alt _, h | .text _, .rep .., h => by simp [termEq] at h
  | .exact _, .range .., h | .exact _, .text _, h | .exact _, .ref _, h | .exact _, .seq _, h
  | .exact _, .alt _, h | .exact _, .rep .., h => by simp [termEq] at h
  | .ref _, .range .., h | .ref _, .text _, h | .ref _, .exact _, h | .ref _, .seq _, h
  | .ref _, .alt _, h | .ref _, .rep .., h => by simp [termEq] at h
  | .seq _, .range .., h | .seq _, .text _, h | .seq _, .exact _, h | .seq _, .ref _, h
  | .seq _, .alt _, h | .seq _, .rep .., h => by simp [termEq] at h
  | .alt _, .range .., h | .alt _, .text _, h | .alt _, .exact _, h | .alt _, .ref _, h
  | .alt _, .seq _, h | .alt _, .rep .., h => by simp [termEq] at h
  | .rep .., .range .., h | .rep .., .text _, h | .rep .., .exact _, h | .rep .., .ref _, h
  | .rep .., .seq _, h | .rep .., .alt _, h => by simp [termEq] at h
theorem termsEq_sound : ∀ ts us : List Term, termsEq ts us = true → ts = us
  | [], [], _ => rfl
  | t :: ts, u :: us, h => by
    simp only [termsEq, Bool.and_eq_true] at h; rw [termEq_sound t u h.1, termsEq_sound ts us h.2]
  | [], _ :: _, h | _ :: _, [], h => by simp [termsEq] at h
end

/-- Rule `i` of the grammar is `t`, as the kernel compares them. The elaborator cannot unfold the grammar's array that
deep. -/
theorem rule_eq {i : Nat} {t : Term} (h : (match grammar[i]? with | some u => termEq u t | none => false) = true) :
    grammar[i]? = some t := by
  revert h; cases grammar[i]? with
  | none => intro h; cases h
  | some u => intro h; rw [termEq_sound u t h]

/-! ## The comment's rules -/

theorem comment_eq : commentRule = 31 := by decide +kernel

theorem rule31 : grammar[31]? = some rComment := rule_eq (by decide +kernel)
theorem rule28 : grammar[28]? = some rCcontent := rule_eq (by decide +kernel)
theorem rule72 : grammar[72]? = some rFws := rule_eq (by decide +kernel)
theorem rule37 : grammar[37]? = some rCrlf := rule_eq (by decide +kernel)
theorem rule127 : grammar[127]? = some rQuotedPair := rule_eq (by decide +kernel)

/-- White space: a space or a tab. -/
def isWsp (b : Nat) : Bool := b == 32 || b == 9
/-- A byte of a comment's text. -/
def isCtext (b : Nat) : Bool := (33 ≤ b && b ≤ 39) || (42 ≤ b && b ≤ 91) || (93 ≤ b && b ≤ 126)
/-- A visible byte. -/
def isVchar (b : Nat) : Bool := 33 ≤ b && b ≤ 126

theorem wsp_iff {y z : Nat} :
    Matches grammar input (.ref 166) y z ↔ (∃ b, input[y]? = some b ∧ isWsp b) ∧ z = y + 1 := by
  rw [classOf_iff 4 _ [(32, 32), (9, 9)] (by decide +kernel)]
  simp only [InRanges, List.mem_cons, List.not_mem_nil, or_false, exists_eq_or_imp, exists_eq_left, isWsp,
    Bool.or_eq_true, beq_iff_eq]
  constructor <;> rintro ⟨⟨b, hb, h⟩, he⟩ <;> exact ⟨⟨b, hb, by omega⟩, he⟩

theorem ctext_iff {y z : Nat} :
    Matches grammar input (.ref 38) y z ↔ (∃ b, input[y]? = some b ∧ isCtext b) ∧ z = y + 1 := by
  rw [classOf_iff 4 _ [(33, 39), (42, 91), (93, 126)] (by decide +kernel)]
  simp only [InRanges, List.mem_cons, List.not_mem_nil, or_false, exists_eq_or_imp, exists_eq_left, isCtext,
    Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
  constructor <;> rintro ⟨⟨b, hb, h⟩, he⟩ <;> exact ⟨⟨b, hb, by omega⟩, he⟩

theorem vchar_iff {y z : Nat} :
    Matches grammar input (.ref 163) y z ↔ (∃ b, input[y]? = some b ∧ isVchar b) ∧ z = y + 1 := by
  rw [classOf_iff 4 _ [(33, 126)] (by decide +kernel)]
  simp only [InRanges, List.mem_cons, List.not_mem_nil, or_false, exists_eq_left, isVchar, Bool.and_eq_true,
    decide_eq_true_eq]

/-- A string of one byte that is no letter. -/
theorem textByte_iff {s : String} {c y z : Nat} (hs : codes s = [c]) (hc : ¬(65 ≤ c ∧ c ≤ 90) ∧ ¬(97 ≤ c ∧ c ≤ 122)) :
    Matches grammar input (.text s) y z ↔ input[y]? = some c ∧ z = y + 1 := by
  rw [text_iff, hs, at_one]
  simp only [List.length_cons, List.length_nil, Nat.zero_add]
  have hl : lower c = c := by unfold lower; rw [if_neg hc.1]
  rw [hl]
  constructor
  · rintro ⟨⟨b, hb, h⟩, he⟩
    refine ⟨?_, he⟩
    rw [hb]; unfold lower at h; split at h <;> first | omega | rw [h]
  · rintro ⟨hb, he⟩
    exact ⟨⟨c, hb, hl⟩, he⟩

/-- A line break at `c`. -/
def CrlfAt (input : Array Nat) (c : Nat) : Prop := input[c]? = some 13 ∧ input[c + 1]? = some 10

theorem crlf_iff {y z : Nat} : Matches grammar input (.ref 37) y z ↔ CrlfAt input y ∧ z = y + 2 := by
  rw [ref_iff' rule37, rCrlf, exact_iff]
  simp only [List.length_cons, List.length_nil, CrlfAt]
  unfold at?; unfold at?; unfold at?
  cases h1 : input[y]? <;> cases h2 : input[y + 1]? <;> simp_all

/-- White space, any number of times. -/
def WStar (input : Array Nat) (y z : Nat) : Prop := ∃ k, Rep grammar input (.ref 166) k y z
/-- White space, at least once. -/
def WPlus (input : Array Nat) (y z : Nat) : Prop := ∃ q, Matches grammar input (.ref 166) y q ∧ WStar input q z

/-- Folding white space: `fws = [*wsp crlf] 1*wsp`. -/
theorem fws_iff {y z : Nat} :
    Matches grammar input (.ref 72) y z ↔
      ∃ a, (a = y ∨ ∃ c, WStar input y c ∧ CrlfAt input c ∧ a = c + 2) ∧ WPlus input a z := by
  rw [ref_iff' rule72, rFws, seq_iff, seq_cons_iff]
  simp only [opt_iff, seq_iff, seq_cons_iff, seq_nil_iff, star_iff, crlf_iff, plus_iff, WStar, WPlus]
  constructor
  · rintro ⟨a, ha, q, ⟨q', h1, k, h2⟩, rfl⟩
    refine ⟨a, ?_, q', h1, k, h2⟩
    rcases ha with rfl | ⟨c, ⟨k', hk⟩, c', ⟨hc, rfl⟩, rfl⟩
    · exact .inl rfl
    · exact .inr ⟨c, ⟨k', hk⟩, hc, rfl⟩
  · rintro ⟨a, ha, q', h1, k, h2⟩
    refine ⟨a, ?_, z, ⟨q', h1, k, h2⟩, rfl⟩
    rcases ha with rfl | ⟨c, ⟨k', hk⟩, hc, rfl⟩
    · exact .inl rfl
    · exact .inr ⟨c, ⟨k', hk⟩, c + 2, ⟨hc, rfl⟩, rfl⟩

theorem qp_iff {y z : Nat} : Matches grammar input (.ref 127) y z ↔
    input[y]? = some 92 ∧ (∃ c, input[y + 1]? = some c ∧ (isVchar c || isWsp c)) ∧ z = y + 2 := by
  rw [ref_iff' rule127, rQuotedPair, seq_iff, seq_cons_iff]
  simp only [textByte_iff (show codes "\\" = [92] by decide +kernel) (by omega), seq_cons_iff, seq_nil_iff, alt_iff,
    List.mem_cons, List.not_mem_nil, or_false, exists_eq_or_imp, exists_eq_left, vchar_iff, wsp_iff,
    Bool.or_eq_true]
  constructor
  · rintro ⟨q, ⟨hb, rfl⟩, e, h, rfl⟩
    rcases h with ⟨⟨c, hc, h⟩, rfl⟩ | ⟨⟨c, hc, h⟩, rfl⟩
    · exact ⟨hb, ⟨c, hc, .inl h⟩, rfl⟩
    · exact ⟨hb, ⟨c, hc, .inr h⟩, rfl⟩
  · rintro ⟨hb, ⟨c, hc, h⟩, rfl⟩
    refine ⟨y + 1, ⟨hb, rfl⟩, y + 2, ?_, rfl⟩
    rcases h with h | h
    · exact .inl ⟨⟨c, hc, h⟩, rfl⟩
    · exact .inr ⟨⟨c, hc, h⟩, rfl⟩

theorem ccontent_iff {y z : Nat} : Matches grammar input (.ref 28) y z ↔
    Matches grammar input (.ref 38) y z ∨ Matches grammar input (.ref 127) y z ∨
      Matches grammar input (.ref 31) y z := by
  rw [ref_iff' rule28, rCcontent, alt_iff]
  simp only [List.mem_cons, List.not_mem_nil, or_false, exists_eq_or_imp, exists_eq_left]

/-- The white space between two parts of a comment: `[fws]`. -/
def gapT : Term := .rep 0 (some 1) (.ref 72)
/-- A comment's parts: `*([fws] ccontent)`. -/
def itemsT : Term := .rep 0 none (.seq [gapT, .ref 28])

/-- A comment's parts from `y`, then white space to `z`, where it closes. -/
def Rest0 (input : Array Nat) (y z : Nat) : Prop :=
  ∃ m, Matches grammar input itemsT y m ∧ Matches grammar input gapT m z

theorem comment_iff {y e : Nat} : Matches grammar input (.ref 31) y e ↔
    input[y]? = some 40 ∧ ∃ z, Rest0 input (y + 1) z ∧ input[z]? = some 41 ∧ e = z + 1 := by
  rw [ref_iff' rule31, rComment, seq_iff]
  simp only [seq_cons_iff, seq_nil_iff, textByte_iff (show codes "(" = [40] by decide +kernel) (by omega),
    textByte_iff (show codes ")" = [41] by decide +kernel) (by omega), Rest0]
  constructor
  · rintro ⟨q, ⟨hb, rfl⟩, m, hm, z, hz, e', ⟨hc, rfl⟩, rfl⟩
    exact ⟨hb, z, ⟨m, hm, hz⟩, hc, rfl⟩
  · rintro ⟨hb, z, ⟨m, hm, hz⟩, hc, rfl⟩
    exact ⟨y + 1, ⟨hb, rfl⟩, m, hm, z, hz, z + 1, ⟨hc, rfl⟩, rfl⟩

/-! ## The comment scanned -/

/-- After white space ending at `m`: the close at `m`, or a part and the parts after it. -/
def After (input : Array Nat) (m z : Nat) : Prop :=
  m = z ∨ ∃ c, Matches grammar input (.ref 28) m c ∧ Rest0 input c z

/-- A comment's parts from `y` to the `)` at `z`, white space before `y` in scan state `s`. States: 0 after `(` or a
part, 1 in space, 2 after its line break, 3 in space after it. -/
def Rest (input : Array Nat) : Nat → Nat → Nat → Prop
  | 0, y, z => Rest0 input y z
  | 1, y, z => ∃ m, (WStar input y m ∨ ∃ c, WStar input y c ∧ CrlfAt input c ∧ WPlus input (c + 2) m) ∧ After input m z
  | 2, y, z => ∃ m, WPlus input y m ∧ After input m z
  | 3, y, z => ∃ m, WStar input y m ∧ After input m z
  | _, _, _ => False

/-- `k` comments that close from `y`, the last at `e - 1`. -/
def Tail (input : Array Nat) : Nat → Nat → Nat → Prop
  | 0, y, e => e = y
  | k + 1, y, e => ∃ z, Rest0 input y z ∧ input[z]? = some 41 ∧ Tail input k (z + 1) e

/-- Where the scan goes from `y` with `dep` comments open, in state `sm`. -/
inductive Step where
  | go (y dep sm : Nat)
  | fail
  | done (e : Nat)

/-- One step of the scan, as `AbnfProg.ruleComment` takes it. -/
def step (input : Array Nat) (y dep sm : Nat) : Step :=
  match input[y]? with
  | none => .fail
  | some b =>
    if sm = 2 then (if isWsp b then .go (y + 1) dep 3 else .fail)
    else if isWsp b then .go (y + 1) dep (if sm = 0 then 1 else sm)
    else if b = 13 then
      (if sm = 3 then .fail else if input[y + 1]? = some 10 then .go (y + 2) dep 2 else .fail)
    else if isCtext b then .go (y + 1) dep 0
    else if b = 92 then
      (match input[y + 1]? with
       | some c => if isVchar c || isWsp c then .go (y + 2) dep 0 else .fail
       | none => .fail)
    else if b = 40 then .go (y + 1) (dep + 1) 0
    else if b = 41 then (if dep = 1 then .done (y + 1) else .go (y + 1) (dep - 1) 0)
    else .fail

/-- The scan from `y` with `dep` comments open, in state `sm`, closes the last at `e - 1`. -/
inductive Runs (input : Array Nat) : Nat → Nat → Nat → Nat → Prop
  | done {y dep sm e : Nat} : step input y dep sm = .done e → Runs input y dep sm e
  | go {y dep sm y' dep' sm' e : Nat} : step input y dep sm = .go y' dep' sm' → Runs input y' dep' sm' e →
      Runs input y dep sm e

theorem runs_det {y d s e e' : Nat} (h : Runs input y d s e) (h' : Runs input y d s e') : e = e' := by
  induction h with
  | done hs =>
    cases h' with
    | done hs' => rw [hs] at hs'; cases hs'; rfl
    | go hs' _ => rw [hs] at hs'; cases hs'
  | go hs _ ih =>
    cases h' with
    | done hs' => rw [hs] at hs'; cases hs'
    | go hs' h2 => rw [hs] at hs'; cases hs'; exact ih h2

theorem step_done {y d s e : Nat} (h : step input y d s = .done e) :
    s ≠ 2 ∧ input[y]? = some 41 ∧ d = 1 ∧ e = y + 1 := by
  unfold step at h
  split at h
  · cases h
  · rename_i b hb
    by_cases h2 : s = 2
    · rw [if_pos h2] at h; split at h <;> cases h
    rw [if_neg h2] at h
    by_cases hw : isWsp b = true
    · rw [if_pos hw] at h; cases h
    rw [if_neg hw] at h
    by_cases h13 : b = 13
    · rw [if_pos h13] at h; split at h; · cases h
      split at h <;> cases h
    rw [if_neg h13] at h
    by_cases hc : isCtext b = true
    · rw [if_pos hc] at h; cases h
    rw [if_neg hc] at h
    by_cases h92 : b = 92
    · rw [if_pos h92] at h; split at h; · split at h <;> cases h
      cases h
    rw [if_neg h92] at h
    by_cases h40 : b = 40
    · rw [if_pos h40] at h; cases h
    rw [if_neg h40] at h
    by_cases h41 : b = 41
    · rw [if_pos h41] at h
      split at h
      · cases h; exact ⟨h2, by rw [hb, h41], by assumption, rfl⟩
      · cases h
    · rw [if_neg h41] at h; cases h

theorem step_go {y d s y' d' s' : Nat} (h : step input y d s = .go y' d' s') :
    (s = 2 ∧ (∃ b, input[y]? = some b ∧ isWsp b) ∧ y' = y + 1 ∧ d' = d ∧ s' = 3) ∨
    (s ≠ 2 ∧ (∃ b, input[y]? = some b ∧ isWsp b) ∧ y' = y + 1 ∧ d' = d ∧ s' = (if s = 0 then 1 else s)) ∨
    (s ≠ 2 ∧ s ≠ 3 ∧ CrlfAt input y ∧ y' = y + 2 ∧ d' = d ∧ s' = 2) ∨
    (s ≠ 2 ∧ (∃ b, input[y]? = some b ∧ isCtext b) ∧ y' = y + 1 ∧ d' = d ∧ s' = 0) ∨
    (s ≠ 2 ∧ input[y]? = some 92 ∧ (∃ c, input[y + 1]? = some c ∧ (isVchar c || isWsp c)) ∧ y' = y + 2 ∧ d' = d ∧
      s' = 0) ∨
    (s ≠ 2 ∧ input[y]? = some 40 ∧ y' = y + 1 ∧ d' = d + 1 ∧ s' = 0) ∨
    (s ≠ 2 ∧ input[y]? = some 41 ∧ d ≠ 1 ∧ y' = y + 1 ∧ d' = d - 1 ∧ s' = 0) := by
  unfold step at h
  split at h
  · cases h
  · rename_i b hb
    by_cases h2 : s = 2
    · rw [if_pos h2] at h; split at h
      · cases h; exact .inl ⟨h2, ⟨b, hb, by assumption⟩, rfl, rfl, rfl⟩
      · cases h
    rw [if_neg h2] at h
    by_cases hw : isWsp b = true
    · rw [if_pos hw] at h; cases h; exact .inr (.inl ⟨h2, ⟨b, hb, hw⟩, rfl, rfl, rfl⟩)
    rw [if_neg hw] at h
    by_cases h13 : b = 13
    · rw [if_pos h13] at h; split at h; · cases h
      split at h
      · cases h; subst h13
        exact .inr (.inr (.inl ⟨h2, by assumption, ⟨hb, by assumption⟩, rfl, rfl, rfl⟩))
      · cases h
    rw [if_neg h13] at h
    by_cases hc : isCtext b = true
    · rw [if_pos hc] at h; cases h; exact .inr (.inr (.inr (.inl ⟨h2, ⟨b, hb, hc⟩, rfl, rfl, rfl⟩)))
    rw [if_neg hc] at h
    by_cases h92 : b = 92
    · rw [if_pos h92] at h; split at h
      · rename_i c hc'
        split at h
        · cases h; subst h92
          exact .inr (.inr (.inr (.inr (.inl ⟨h2, hb, ⟨c, hc', by assumption⟩, rfl, rfl, rfl⟩))))
        · cases h
      · cases h
    rw [if_neg h92] at h
    by_cases h40 : b = 40
    · rw [if_pos h40] at h; cases h; subst h40
      exact .inr (.inr (.inr (.inr (.inr (.inl ⟨h2, hb, rfl, rfl, rfl⟩)))))
    rw [if_neg h40] at h
    by_cases h41 : b = 41
    · rw [if_pos h41] at h
      split at h
      · cases h
      · cases h; subst h41
        exact .inr (.inr (.inr (.inr (.inr (.inr ⟨h2, hb, by assumption, rfl, rfl, rfl⟩)))))
    · rw [if_neg h41] at h; cases h

/-! ### What the scan reads is a comment -/

theorem wstar_nil {y : Nat} : WStar input y y := ⟨0, .zero⟩

theorem wsp_at {y b : Nat} (hb : input[y]? = some b) (hw : isWsp b = true) :
    Matches grammar input (.ref 166) y (y + 1) :=
  wsp_iff.2 ⟨⟨b, hb, hw⟩, rfl⟩

theorem wstar_cons {y z : Nat} (h : Matches grammar input (.ref 166) y (y + 1)) (hs : WStar input (y + 1) z) :
    WStar input y z :=
  let ⟨k, hk⟩ := hs; ⟨k + 1, .succ h hk⟩

theorem items_nil {y : Nat} : Matches grammar input itemsT y y := star_iff.2 ⟨0, .zero⟩

theorem gap_nil {y : Nat} : Matches grammar input gapT y y := opt_iff.2 (.inl rfl)

/-- A part after white space, then more parts. -/
theorem items_cons {y m c m' : Nat} (hg : Matches grammar input gapT y m) (hc : Matches grammar input (.ref 28) m c)
    (hi : Matches grammar input itemsT c m') : Matches grammar input itemsT y m' := by
  obtain ⟨k, hk⟩ := star_iff.1 hi
  exact star_iff.2 ⟨k + 1, .succ (seq_iff.2 (.cons hg (.cons hc .nil))) hk⟩

theorem rest0_of {y m z : Nat} (hg : Matches grammar input gapT y m) (ha : After input m z) : Rest0 input y z := by
  rcases ha with rfl | ⟨c, hc, m', hi, hg'⟩
  · exact ⟨y, items_nil, hg⟩
  · exact ⟨m', items_cons hg hc hi, hg'⟩

/-- A part, then the parts up to the close, from any state but just after a line break. -/
theorem rest_part {s y c z : Nat} (hs : s = 0 ∨ s = 1 ∨ s = 3) (hc : Matches grammar input (.ref 28) y c)
    (hr : Rest0 input c z) : Rest input s y z := by
  rcases hs with rfl | rfl | rfl
  · exact rest0_of gap_nil (.inr ⟨c, hc, hr⟩)
  · exact ⟨y, .inl wstar_nil, .inr ⟨c, hc, hr⟩⟩
  · exact ⟨y, wstar_nil, .inr ⟨c, hc, hr⟩⟩

theorem rest_close {s y : Nat} (hs : s = 0 ∨ s = 1 ∨ s = 3) : Rest input s y y := by
  rcases hs with rfl | rfl | rfl
  · exact ⟨y, items_nil, gap_nil⟩
  · exact ⟨y, .inl wstar_nil, .inl rfl⟩
  · exact ⟨y, wstar_nil, .inl rfl⟩

/-- White space at `y`, then the rest of white space with no line break yet. -/
theorem rest_wsp {s y z b : Nat} (hs : s = 0 ∨ s = 1 ∨ s = 3) (hb : input[y]? = some b) (hw : isWsp b = true)
    (hr : Rest input (if s = 0 then 1 else s) (y + 1) z) : Rest input s y z := by
  have h1 := wsp_at hb hw
  rcases hs with rfl | rfl | rfl
  · obtain ⟨m, ht, ha⟩ := hr
    refine rest0_of (opt_iff.2 (.inr (fws_iff.2 ?_))) ha
    rcases ht with ht | ⟨c, hc, hcr, hp⟩
    · exact ⟨y, .inl rfl, y + 1, h1, ht⟩
    · exact ⟨c + 2, .inr ⟨c, wstar_cons h1 hc, hcr, rfl⟩, hp⟩
  · obtain ⟨m, ht, ha⟩ := hr
    refine ⟨m, ?_, ha⟩
    rcases ht with ht | ⟨c, hc, hcr, hp⟩
    · exact .inl (wstar_cons h1 ht)
    · exact .inr ⟨c, wstar_cons h1 hc, hcr, hp⟩
  · obtain ⟨m, ht, ha⟩ := hr
    exact ⟨m, wstar_cons h1 ht, ha⟩

/-- **The scan reads comments**: from `y` in state `s` with `d` open, a run closing the last at `e - 1`. It reads the
parts up to a `)` at `z`, then `d - 1` comments that close. -/
theorem runs_sound {y d s e : Nat} (h : Runs input y d s e) (hd : 1 ≤ d) (hs : s ≤ 3) :
    ∃ z, Rest input s y z ∧ input[z]? = some 41 ∧ Tail input (d - 1) (z + 1) e := by
  induction h with
  | @done y d s e hst =>
    obtain ⟨h2, h41, rfl, rfl⟩ := step_done hst
    exact ⟨y, rest_close (by omega), h41, rfl⟩
  | @go y d s y' d' s' e hst _ ih =>
    rcases step_go hst with ⟨rfl, ⟨b, hb, hw⟩, rfl, rfl, rfl⟩ | ⟨h2, ⟨b, hb, hw⟩, rfl, rfl, rfl⟩ |
      ⟨h2, h3, hcr, rfl, rfl, rfl⟩ | ⟨h2, ⟨b, hb, hc⟩, rfl, rfl, rfl⟩ | ⟨h2, hb, ⟨c, hc, hv⟩, rfl, rfl, rfl⟩ |
      ⟨h2, hb, rfl, rfl, rfl⟩ | ⟨h2, hb, h1, rfl, rfl, rfl⟩
    · obtain ⟨z, ⟨m, hm, ha⟩, hz, ht⟩ := ih hd (by omega)
      exact ⟨z, ⟨m, ⟨y + 1, wsp_at hb hw, hm⟩, ha⟩, hz, ht⟩
    · obtain ⟨z, hr, hz, ht⟩ := ih hd (by split <;> omega)
      exact ⟨z, rest_wsp (by omega) hb hw hr, hz, ht⟩
    · obtain ⟨z, ⟨m, hp, ha⟩, hz, ht⟩ := ih hd (by omega)
      refine ⟨z, ?_, hz, ht⟩
      have hs' : s = 0 ∨ s = 1 := by omega
      rcases hs' with rfl | rfl
      · exact rest0_of (opt_iff.2 (.inr (fws_iff.2 ⟨y + 2, .inr ⟨y, wstar_nil, hcr, rfl⟩, hp⟩))) ha
      · exact ⟨m, .inr ⟨y, wstar_nil, hcr, hp⟩, ha⟩
    · obtain ⟨z, hr, hz, ht⟩ := ih hd (by omega)
      exact ⟨z, rest_part (by omega) (ccontent_iff.2 (.inl (ctext_iff.2 ⟨⟨b, hb, hc⟩, rfl⟩))) hr, hz, ht⟩
    · obtain ⟨z, hr, hz, ht⟩ := ih hd (by omega)
      exact ⟨z, rest_part (by omega) (ccontent_iff.2 (.inr (.inl (qp_iff.2 ⟨hb, ⟨c, hc, hv⟩, rfl⟩)))) hr, hz, ht⟩
    · obtain ⟨z, hr, hz, ht⟩ := ih (by omega) (by omega)
      obtain ⟨z2, hr2, hz2, ht2⟩ :
          ∃ z2, Rest0 input (z + 1) z2 ∧ input[z2]? = some 41 ∧ Tail input (d - 1) (z2 + 1) e := by
        have : d + 1 - 1 = (d - 1) + 1 := by omega
        rw [this] at ht; exact ht
      exact ⟨z2, rest_part (by omega) (ccontent_iff.2 (.inr (.inr (comment_iff.2 ⟨hb, z, hr, hz, rfl⟩)))) hr2, hz2, ht2⟩
    · obtain ⟨z, hr, hz, ht⟩ := ih (by omega) (by omega)
      refine ⟨y, rest_close (by omega), hb, ?_⟩
      have : d - 1 = (d - 1 - 1) + 1 := by omega
      rw [this]; exact ⟨z, hr, hz, ht⟩

/-! ### A comment is what the scan reads -/

/-- The scan goes from one state to another without stopping. -/
inductive Reach (input : Array Nat) : Nat → Nat → Nat → Nat → Nat → Nat → Prop
  | refl {y d s : Nat} : Reach input y d s y d s
  | step {y d s y' d' s' y'' d'' s'' : Nat} : step input y d s = .go y' d' s' → Reach input y' d' s' y'' d'' s'' →
      Reach input y d s y'' d'' s''

theorem Reach.trans {y d s y' d' s' y'' d'' s'' : Nat} (h : Reach input y d s y' d' s')
    (h' : Reach input y' d' s' y'' d'' s'') : Reach input y d s y'' d'' s'' := by
  induction h with
  | refl => exact h'
  | step hs _ ih => exact .step hs (ih h')

theorem runs_of_reach {y d s y' d' s' e : Nat} (h : Reach input y d s y' d' s') (hr : Runs input y' d' s' e) :
    Runs input y d s e := by
  induction h with
  | refl => exact hr
  | step hs _ ih => exact .go hs (ih hr)

theorem step_wsp {y d s b : Nat} (hb : input[y]? = some b) (hw : isWsp b = true) (h2 : s ≠ 2) :
    step input y d s = .go (y + 1) d (if s = 0 then 1 else s) := by
  simp only [step, hb, if_neg h2, hw, if_true]

theorem step_wsp2 {y d b : Nat} (hb : input[y]? = some b) (hw : isWsp b = true) :
    step input y d 2 = .go (y + 1) d 3 := by
  simp only [step, hb, if_true, hw]

theorem step_crlf {y d s : Nat} (hcr : CrlfAt input y) (h2 : s ≠ 2) (h3 : s ≠ 3) :
    step input y d s = .go (y + 2) d 2 := by
  simp [step, hcr.1, hcr.2, h2, h3, isWsp]

theorem step_ctext {y d s b : Nat} (hb : input[y]? = some b) (hc : isCtext b = true) (h2 : s ≠ 2) :
    step input y d s = .go (y + 1) d 0 := by
  have hw : isWsp b = false := by
    simp only [isCtext, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hc
    simp only [isWsp, Bool.or_eq_false_iff, beq_eq_false_iff_ne]; omega
  have h13 : b ≠ 13 := by
    simp only [isCtext, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hc; omega
  simp only [step, hb, if_neg h2, hw, if_neg h13, hc, if_true, Bool.false_eq_true, if_false]

theorem step_qp {y d s c : Nat} (hb : input[y]? = some 92) (hc : input[y + 1]? = some c)
    (hv : (isVchar c || isWsp c) = true) (h2 : s ≠ 2) : step input y d s = .go (y + 2) d 0 := by
  have e1 : isWsp 92 = false := rfl
  have e2 : isCtext 92 = false := rfl
  simp only [step, hb, if_neg h2, e1, e2, hc, hv, Bool.false_eq_true, ↓reduceIte]
  rw [if_neg (by decide)]

theorem step_open {y d s : Nat} (hb : input[y]? = some 40) (h2 : s ≠ 2) :
    step input y d s = .go (y + 1) (d + 1) 0 := by
  simp [step, hb, h2, isWsp, isCtext]

theorem step_close {y d s : Nat} (hb : input[y]? = some 41) (h2 : s ≠ 2) :
    step input y d s = if d = 1 then .done (y + 1) else .go (y + 1) (d - 1) 0 := by
  simp [step, hb, h2, isWsp, isCtext]

theorem wstar_reach {y z d s : Nat} (hs : s = 1 ∨ s = 3) (h : WStar input y z) : Reach input y d s z d s := by
  obtain ⟨k, hk⟩ := h
  induction k generalizing y with
  | zero => rw [rep_zero_iff.1 hk]; exact .refl
  | succ k ih =>
    obtain ⟨q, hq, hr⟩ := rep_succ_iff.1 hk
    obtain ⟨⟨b, hb, hw⟩, rfl⟩ := wsp_iff.1 hq
    have := step_wsp (d := d) (s := s) hb hw (by omega)
    rw [if_neg (by omega)] at this
    exact .step this (ih hr)

theorem wstar_reach0 {y z d : Nat} (h : WStar input y z) : ∃ s', (s' = 0 ∨ s' = 1) ∧ Reach input y d 0 z d s' := by
  obtain ⟨k, hk⟩ := h
  cases k with
  | zero => rw [rep_zero_iff.1 hk]; exact ⟨0, .inl rfl, .refl⟩
  | succ k =>
    obtain ⟨q, hq, hr⟩ := rep_succ_iff.1 hk
    obtain ⟨⟨b, hb, hw⟩, rfl⟩ := wsp_iff.1 hq
    exact ⟨1, .inr rfl, .step (step_wsp (d := d) hb hw (by decide)) (wstar_reach (.inl rfl) ⟨k, hr⟩)⟩

theorem fws_reach {y z d : Nat} (h : Matches grammar input (.ref 72) y z) :
    ∃ s', (s' = 1 ∨ s' = 3) ∧ Reach input y d 0 z d s' := by
  obtain ⟨a, ha, q, hq, hr⟩ := fws_iff.1 h
  obtain ⟨⟨b, hb, hw⟩, rfl⟩ := wsp_iff.1 hq
  rcases ha with rfl | ⟨c, hc, hcr, rfl⟩
  · exact ⟨1, .inl rfl, .step (step_wsp (d := d) hb hw (by decide)) (wstar_reach (.inl rfl) hr)⟩
  · obtain ⟨s', hs', h1⟩ := wstar_reach0 (d := d) hc
    refine ⟨3, .inr rfl, h1.trans (.step (step_crlf hcr (by omega) (by omega)) ?_)⟩
    exact .step (step_wsp2 hb hw) (wstar_reach (.inr rfl) hr)

theorem gap_reach {y z d : Nat} (h : Matches grammar input gapT y z) :
    ∃ s', (s' = 0 ∨ s' = 1 ∨ s' = 3) ∧ Reach input y d 0 z d s' := by
  rcases opt_iff.1 h with rfl | h
  · exact ⟨0, .inl rfl, .refl⟩
  · obtain ⟨s', hs', h1⟩ := fws_reach (d := d) h
    exact ⟨s', .inr hs', h1⟩

/-- **A part of a comment is read** whole, from any state but just after a line break, with comments open. -/
theorem part_reach (n : Nat) : ∀ y c, c ≤ y + n → ∀ d s, 1 ≤ d → (s = 0 ∨ s = 1 ∨ s = 3) →
    Matches grammar input (.ref 28) y c → Reach input y d s c d 0 := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
  intro y c hc d s hd hs h
  rcases ccontent_iff.1 h with h | h | h
  · obtain ⟨⟨b, hb, hct⟩, rfl⟩ := ctext_iff.1 h
    exact .step (step_ctext hb hct (by omega)) .refl
  · obtain ⟨hb, ⟨c', hc', hv⟩, rfl⟩ := qp_iff.1 h
    exact .step (step_qp hb hc' hv (by omega)) .refl
  · obtain ⟨hb, z, ⟨m, hi, hg⟩, hz, rfl⟩ := comment_iff.1 h
    have hmz := Matches.le hg
    obtain ⟨k, hk⟩ := star_iff.1 hi
    have items : ∀ k y', Rep grammar input (.seq [gapT, .ref 28]) k y' m → y + 1 ≤ y' →
        Reach input y' (d + 1) 0 m (d + 1) 0 := by
      intro k
      induction k with
      | zero => intro y' h _; rw [rep_zero_iff.1 h]; exact .refl
      | succ k ihk =>
        intro y' h hy
        obtain ⟨q, hq, hr⟩ := rep_succ_iff.1 h
        obtain ⟨a, hga, hrest⟩ := seq_cons_iff.1 (seq_iff.1 hq)
        obtain ⟨q', hcq, hq'⟩ := seq_cons_iff.1 hrest
        rw [← seq_nil_iff.1 hq'] at hcq
        have hya := Matches.le hga
        have haq := Matches.le hcq
        have hqm := Rep.le hr
        obtain ⟨s', hs', h1⟩ := gap_reach (d := d + 1) hga
        exact h1.trans ((ih (n - 1) (by omega) a q (by omega) (d + 1) s' (by omega) hs' hcq).trans
          (ihk q hr (by omega)))
    obtain ⟨s', hs', h1⟩ := gap_reach (d := d + 1) hg
    have hcl := step_close (y := z) (d := d + 1) (s := s') hz (by omega)
    rw [if_neg (by omega), Nat.add_sub_cancel] at hcl
    exact .step (step_open hb (by omega)) ((items k (y + 1) hk (Nat.le_refl _)).trans (h1.trans (.step hcl .refl)))

/-- **A comment is what the scan reads.** From its `(`, one comment open, the scan closes it where the match ends. -/
theorem runs_of_comment {x e : Nat} (h : Matches grammar input (.ref 31) x e) :
    input[x]? = some 40 ∧ Runs input (x + 1) 1 0 e := by
  obtain ⟨hb, z, ⟨m, hi, hg⟩, hz, rfl⟩ := comment_iff.1 h
  refine ⟨hb, ?_⟩
  obtain ⟨k, hk⟩ := star_iff.1 hi
  have items : ∀ k y', Rep grammar input (.seq [gapT, .ref 28]) k y' m → Reach input y' 1 0 m 1 0 := by
    intro k
    induction k with
    | zero => intro y' h; rw [rep_zero_iff.1 h]; exact .refl
    | succ k ihk =>
      intro y' h
      obtain ⟨q, hq, hr⟩ := rep_succ_iff.1 h
      obtain ⟨a, hga, hrest⟩ := seq_cons_iff.1 (seq_iff.1 hq)
      obtain ⟨q', hcq, hq'⟩ := seq_cons_iff.1 hrest
      rw [← seq_nil_iff.1 hq'] at hcq
      obtain ⟨s', hs', h1⟩ := gap_reach (d := 1) hga
      exact h1.trans ((part_reach q a q (by omega) 1 s' (Nat.le_refl _) hs' hcq).trans (ihk q hr))
  obtain ⟨s', hs', h1⟩ := gap_reach (d := 1) hg
  have hcl := step_close (y := z) (d := 1) (s := s') hz (by omega)
  rw [if_pos rfl] at hcl
  exact runs_of_reach ((items k (x + 1) hk).trans h1) (.done hcl)

/-- **The comment's matches are the scan's.** A `comment` match from `x` ends at `e` exactly when `x` holds `(` and the
scan past it closes there. -/
theorem comment_runs {x e : Nat} :
    Matches grammar input (.ref 31) x e ↔ input[x]? = some 40 ∧ Runs input (x + 1) 1 0 e := by
  refine ⟨runs_of_comment, fun ⟨hb, hr⟩ => ?_⟩
  obtain ⟨z, hz, h41, rfl⟩ := runs_sound hr (Nat.le_refl _) (by decide)
  exact comment_iff.2 ⟨hb, z, hz, h41, rfl⟩

/-! ## A class's bits -/

/-- One byte's bit added when `P` takes it. -/
def bitStep (P : Nat → Bool) (acc b : Nat) : Nat := if P b then acc + 2 ^ b else acc

theorem fold_bits (P : Nat → Bool) : ∀ n, (List.range n).foldl (bitStep P) 0 < 2 ^ n ∧
    ∀ i, ((List.range n).foldl (bitStep P) 0).testBit i = (decide (i < n) && P i)
  | 0 => ⟨by simp, fun i => by simp⟩
  | n + 1 => by
    obtain ⟨h1, h2⟩ := fold_bits P n
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    generalize (List.range n).foldl (bitStep P) 0 = S at h1 h2
    unfold bitStep
    have hp2 : 2 ^ (n + 1) = 2 * 2 ^ n := by rw [Nat.pow_succ, Nat.mul_comm]
    cases hp : P n with
    | false =>
      refine ⟨by rw [if_neg (by simp)]; omega, fun i => ?_⟩
      rw [if_neg (by simp), h2]
      by_cases hi : i = n
      · subst hi; simp [hp]
      · by_cases hi' : i < n
        · simp [hi', show i < n + 1 by omega]
        · simp [hi', show ¬i < n + 1 by omega]
    | true =>
      refine ⟨by rw [if_pos rfl]; omega, fun i => ?_⟩
      rw [if_pos rfl, Nat.add_comm]
      rcases Nat.lt_trichotomy i n with h | rfl | h
      · rw [Nat.testBit_two_pow_add_gt h, h2]; simp [h, show i < n + 1 by omega]
      · rw [Nat.testBit_two_pow_add_eq, h2]; simp [hp]
      · have : 2 ^ n + S < 2 ^ i := by
          have := Nat.pow_le_pow_right (show 0 < 2 by decide) (show n + 1 ≤ i by omega); omega
        rw [Nat.testBit_lt_two_pow this]; simp; omega

/-- **A class's bits**: bit `b % 64` of word `b / 64` is set when a range holds `b`. -/
theorem bitsOf_test (rs : List (Nat × Nat)) {b : Nat} (hb : b < 256) :
    ((bitsOf rs)[b / 64]?.getD 0).testBit (b % 64) = rs.any (fun r => r.1 ≤ b && b ≤ r.2) := by
  have hq : b / 64 < 4 := by omega
  have e : (bitsOf rs)[b / 64]? = some ((List.range 256).foldl (bitStep fun b => rs.any (fun r => r.1 ≤ b && b ≤ r.2))
      0 / 2 ^ (64 * (b / 64)) % 2 ^ 64) := by
    simp only [bitsOf, List.getElem?_map, List.getElem?_range hq, Option.map_some]
    rfl
  rw [e, Option.getD_some, Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow,
    show b % 64 + 64 * (b / 64) = b by omega, (fold_bits _ 256).2 b]
  simp [hb, show b % 64 < 64 by omega]

/-! ## A string compared -/

theorem at_iff {norm : Nat → Nat} : ∀ {x : Nat} {bs : List Nat}, at? input norm x bs = true ↔
    ∀ i (h : i < bs.length), ∃ b, input[x + i]? = some b ∧ norm b = norm bs[i]
  | x, [] => by simp [at?]
  | x, c :: cs => by
    rw [at?]
    have ih := at_iff (norm := norm) (x := x + 1) (bs := cs)
    cases hx : input[x]? with
    | none =>
      simp only [Bool.false_eq_true, false_iff, Classical.not_forall]
      exact ⟨0, by simp, fun ⟨b, hb, _⟩ => by simp [hx] at hb⟩
    | some b =>
      simp only [Bool.and_eq_true, beq_iff_eq, ih]
      constructor
      · rintro ⟨h0, hr⟩ i hi
        cases i with
        | zero => exact ⟨b, by simpa using hx, h0⟩
        | succ i =>
          obtain ⟨b', hb', h'⟩ := hr i (by simp at hi; omega)
          exact ⟨b', by rw [show x + (i + 1) = x + 1 + i by omega]; exact hb', h'⟩
      · intro h
        obtain ⟨b0, hb0, h0⟩ := h 0 (by simp)
        simp only [Nat.add_zero, hx, Option.some.injEq] at hb0
        subst hb0
        refine ⟨h0, fun i hi => ?_⟩
        obtain ⟨b', hb', h'⟩ := h (i + 1) (by simp; omega)
        exact ⟨b', by rw [show x + 1 + i = x + (i + 1) by omega]; exact hb', h'⟩

/-- A byte as `leafText` compares it: an upper case letter made lower case when `cf`. -/
def foldB (cf : Bool) (b : Nat) : Nat := b + 32 * (if cf && (65 ≤ b && b ≤ 90) then 1 else 0)

theorem textOf_lowered (f : Nat) : ∀ (t : Term) (bs : List Nat), textOf f t = some (bs, true) → ∀ b ∈ bs,
    lower b = b := by
  induction f with
  | zero => intro _ _ h; nomatch h
  | succ f ih =>
    intro t bs h
    cases t with
    | text s =>
      simp only [textOf, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, -⟩ := h
      intro b hb
      obtain ⟨c, _, rfl⟩ := List.mem_map.1 hb
      exact lower_lower c
    | ref i =>
      simp only [textOf] at h
      cases hu : grammar[i]? with
      | none => rw [hu] at h; cases h
      | some u => rw [hu] at h; exact ih u bs h
    | exact => simp [textOf] at h
    | range => simp [textOf] at h
    | seq => simp [textOf] at h
    | alt => simp [textOf] at h
    | rep => simp [textOf] at h

/-- **A term that is a string** matches where `leafText` finds it. Each input byte, folded if the string is caseless and
it is a letter, is the string's byte. -/
theorem text_match {f : Nat} {t : Term} {bs : List Nat} {c : Bool} (ht : textOf f t = some (bs, c)) {x e : Nat} :
    Matches grammar input t x e ↔ (∀ i (h : i < bs.length), ∃ b, input[x + i]? = some b ∧
      foldB (c && bs.any fun b => 97 ≤ b && b ≤ 122) b = bs[i]) ∧ e = x + bs.length := by
  rw [textOf_iff f t bs c ht, at_iff]
  refine and_congr_left fun _ => forall_congr' fun i => forall_congr' fun hi => exists_congr fun b =>
    and_congr_right fun _ => ?_
  have hm : bs[i] ∈ bs := List.getElem_mem hi
  cases c with
  | false => simp [foldB]
  | true =>
    have hl := textOf_lowered f t bs ht _ hm
    have hU : ¬(65 ≤ bs[i] ∧ bs[i] ≤ 90) := fun h => by unfold lower at hl; rw [if_pos h] at hl; omega
    simp only [if_true]
    rw [hl, show lower b = if 65 ≤ b ∧ b ≤ 90 then b + 32 else b from rfl]
    cases ha : bs.any fun b => 97 ≤ b && b ≤ 122
    · have hL : ¬(97 ≤ bs[i] ∧ bs[i] ≤ 122) := fun h => by
        have := List.any_eq_false.1 ha _ hm; simp at this; omega
      simp only [foldB, Bool.true_and, Bool.false_and, Bool.false_eq_true, if_false]
      split <;> omega
    · simp only [foldB, Bool.true_and, Bool.and_eq_true, decide_eq_true_eq]
      split <;> (constructor <;> intro <;> omega)

theorem inRanges_any {rs : List (Nat × Nat)} {b : Nat} :
    InRanges rs b ↔ rs.any (fun r => r.1 ≤ b && b ≤ r.2) = true := by
  simp [InRanges, List.any_eq_true]

/-- **A term that is a class** matches a byte where `leafClass` finds its bit set. -/
theorem class_match {f : Nat} {t : Term} {rs : List (Nat × Nat)} (ht : classOf f t = some rs) {x e : Nat}
    (hx : ∀ b, input[x]? = some b → b < 256) : Matches grammar input t x e ↔
      (∃ b, input[x]? = some b ∧ ((bitsOf rs)[b / 64]?.getD 0).testBit (b % 64) = true) ∧ e = x + 1 := by
  rw [classOf_iff f t rs ht]
  refine and_congr_left fun _ => exists_congr fun b => ⟨fun ⟨hb, h⟩ => ⟨hb, ?_⟩, fun ⟨hb, h⟩ => ⟨hb, ?_⟩⟩
  · rw [bitsOf_test rs (hx b hb)]; exact inRanges_any.1 h
  · rw [bitsOf_test rs (hx b hb)] at h; exact inRanges_any.2 h

/-! ## The premises can hold -/

theorem matches_witness : Matches #[] #[65] (.range 65 65) 0 1 := .range rfl (Nat.le_refl _) (Nat.le_refl _)
theorem seq_witness : Seq #[] #[] [] 0 0 := .nil
theorem rep_witness : Rep #[] #[] (.range 0 0) 0 0 0 := .zero
theorem runs_witness : Runs #[41] 0 1 0 1 := .done rfl
theorem reach_witness : Reach #[] 0 0 0 0 0 0 := .refl
theorem crlf_witness : CrlfAt #[13, 10] 0 := ⟨rfl, rfl⟩
theorem wstar_witness : WStar #[] 0 0 := wstar_nil
theorem rest0_witness : Rest0 #[] 0 0 := ⟨0, items_nil, gap_nil⟩
theorem after_witness : After #[] 0 0 := .inl rfl
theorem rest_witness : Rest #[] 0 0 0 := rest0_witness

end DN.News.AbnfMatch
