-- SPDX-License-Identifier: AGPL-3.0-or-later
import DN.News.ArticleCheck

/-!
# DN.News.ArticleContext

`artContext` answers whether the context fits what the server adds (`ArticleSpec.Context.ok`): `artContext_ok`. A
group's name of the grammar holds no comma and no white space, so `artElem` reads it whole.
-/

namespace DN.News.ArticleContext

open DN.News.ArticleSpec (Bytes)
open DN.News.ArticleLines (seg)
open DN.Compiler DN.Compiler.Wp DN.Compiler.WpRet DN.Compiler.Frag DN.News.AbnfProg
open DN.News.AbnfSets DN.News.FunRun DN.News.AbnfLeaves DN.News.ArticleRun
open DN.News.ScanRun (at_ at_add vals_lookup Fresh fresh_cons lookup_cons_ne lookup_head)
open DN.News.ArticleProg (artMax guardL guardS ifs wd)
open DN.News.FramerCode (bw ev_var bw_ne0 bw_eq0)
open DN.News.ArticleListRun (elemScratch)
open DN.News.AbnfGen (AllSets)

variable {σ : Type}

/-! ## A group's name -/

section
open DN.News.Abnf DN.News.AbnfMatch DN.News.AbnfRules

/-- A byte a group name may hold: no comma, no white space, no line end. -/
def NameByte (b : Nat) : Prop := b ≠ 44 ∧ b ≠ 32 ∧ b ≠ 9 ∧ b ≠ 13 ∧ b ≠ 10

theorem rule3 : grammar[3]? = some rAlpha := rule_eq (by decide +kernel)
theorem rule33 : grammar[33]? = some rComponent := rule_eq (by decide +kernel)
theorem rule34 : grammar[34]? = some rComponentChar := rule_eq (by decide +kernel)
theorem rule50 : grammar[50]? = some rDigit := rule_eq (by decide +kernel)
theorem rule104 : grammar[104]? = some rNewsgroupName := rule_eq (by decide +kernel)

theorem text_byte {input : Array Nat} {c p e : Nat} (hc' : c ≠ 44 ∧ c ≠ 32 ∧ c ≠ 9 ∧ c ≠ 13 ∧ c ≠ 10)
    (h : at? input lower p [c] = true) (he : e = p + 1) : e = p + 1 ∧ ∃ b, input[p]? = some b ∧ NameByte b := by
  obtain ⟨b, hb, hl⟩ := (at_one (input := input)).1 h
  refine ⟨he, b, hb, ?_⟩
  unfold lower at hl
  split at hl <;> split at hl <;> unfold NameByte <;> omega

/-- **A component's byte** is one a group name may hold. -/
theorem cc_byte {input : Array Nat} {p e : Nat} (h : Matches grammar input (.ref 34) p e) :
    e = p + 1 ∧ ∃ b, input[p]? = some b ∧ NameByte b := by
  rw [ref_iff' rule34, rComponentChar, alt_iff] at h
  obtain ⟨t, ht, hm⟩ := h
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl
  · rw [ref_iff' rule3, rAlpha, alt_iff] at hm
    obtain ⟨t, ht, hm⟩ := hm
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at ht
    rcases ht with rfl | rfl <;> obtain ⟨⟨b, hb, h1, h2⟩, rfl⟩ := range_iff.1 hm <;>
      exact ⟨rfl, b, hb, by unfold NameByte; omega⟩
  · rw [ref_iff' rule50, rDigit] at hm
    obtain ⟨⟨b, hb, h1, h2⟩, rfl⟩ := range_iff.1 hm
    exact ⟨rfl, b, hb, by unfold NameByte; omega⟩
  all_goals
    obtain ⟨hat, rfl⟩ := text_iff.1 hm
    exact text_byte (by decide) hat rfl

theorem rep_bytes {input : Array Nat} : ∀ {k p e : Nat}, Rep grammar input (.ref 34) k p e →
    ∀ i, p ≤ i → i < e → ∃ b, input[i]? = some b ∧ NameByte b
  | 0, p, e, h => by rw [rep_zero_iff] at h; subst h; intro i h1 h2; omega
  | k + 1, p, e, h => by
    obtain ⟨q, h1, h2⟩ := rep_succ_iff.1 h
    obtain ⟨rfl, b, hb, hn⟩ := cc_byte h1
    intro i hi1 hi2
    by_cases hi : i = p
    · subst hi; exact ⟨b, hb, hn⟩
    · exact rep_bytes h2 i (by omega) hi2

theorem comp_bytes {input : Array Nat} {p e : Nat} (h : Matches grammar input (.ref 33) p e) :
    ∀ i, p ≤ i → i < e → ∃ b, input[i]? = some b ∧ NameByte b := by
  rw [ref_iff' rule33, rComponent, plus_iff] at h
  obtain ⟨q, h1, k, h2⟩ := h
  obtain ⟨rfl, b, hb, hn⟩ := cc_byte h1
  intro i hi1 hi2
  by_cases hi : i = p
  · subst hi; exact ⟨b, hb, hn⟩
  · exact rep_bytes h2 i (by omega) hi2

theorem dots_bytes {input : Array Nat} : ∀ {k p e : Nat},
    Rep grammar input (.seq [.text ".", .ref 33]) k p e → ∀ i, p ≤ i → i < e → ∃ b, input[i]? = some b ∧ NameByte b
  | 0, p, e, h => by rw [rep_zero_iff] at h; subst h; intro i h1 h2; omega
  | k + 1, p, e, h => by
    obtain ⟨q, h1, h2⟩ := rep_succ_iff.1 h
    rw [seq_iff, seq_cons_iff] at h1
    obtain ⟨r, hd, hr⟩ := h1
    rw [seq_cons_iff] at hr
    obtain ⟨r', hc, hnil⟩ := hr
    rw [seq_nil_iff] at hnil; subst hnil
    obtain ⟨hat, rfl⟩ := text_iff.1 hd
    obtain ⟨-, b, hb, hn⟩ := text_byte (c := 46) (by decide) hat rfl
    have hl : (codes ".").length = 1 := by decide
    intro i hi1 hi2
    by_cases hi : i = p
    · subst hi; exact ⟨b, hb, hn⟩
    · by_cases hq : i < q
      · exact comp_bytes hc i (by omega) hq
      · exact dots_bytes h2 i (by omega) hi2

/-- **A group name's bytes**: no comma, no white space, no line end. -/
theorem name_bytes {input : Array Nat} {p e : Nat} (h : Matches grammar input (.ref 104) p e) :
    ∀ i, p ≤ i → i < e → ∃ b, input[i]? = some b ∧ NameByte b := by
  rw [ref_iff' rule104, rNewsgroupName, seq_iff, seq_cons_iff] at h
  obtain ⟨q, h1, h2⟩ := h
  rw [seq_cons_iff] at h2
  obtain ⟨r, h3, h4⟩ := h2
  rw [seq_nil_iff] at h4; subst h4
  obtain ⟨k, h3⟩ := star_iff.1 h3
  intro i hi1 hi2
  by_cases hq : i < q
  · exact comp_bytes h1 i hi1 hq
  · exact dots_bytes h3 i (by omega) hi2

end

theorem says_of {R : Nat} {s : Bytes} {b : Bool}
    (h : DN.News.Abnf.matches? AbnfRules.grammar AbnfRules.depth R (s.map BitVec.toNat) = .ok b) :
    ArticleSpec.grammarSays R s = b := by
  unfold ArticleSpec.grammarSays; rw [h]

theorem nn_eq : ArticleSpec.ruleNamed "newsgroup-name" = 104 := by decide +kernel

/-- **A group's name of the grammar**: none of its bytes a comma, white space or a line end. -/
theorem group_bytes {g : Bytes} {b : Bool}
    (h : DN.News.Abnf.matches? AbnfRules.grammar AbnfRules.depth (ArticleSpec.ruleNamed "newsgroup-name")
      (g.map BitVec.toNat) = .ok b)
    (hs : ArticleSpec.grammarSays (ArticleSpec.ruleNamed "newsgroup-name") g = true) :
    ∀ i (hi : i < g.length), NameByte g[i].toNat := by
  have hsg : seg g 0 g.length = g := by simp [seg]
  have h' : DN.News.Abnf.matches? AbnfRules.grammar AbnfRules.depth (ArticleSpec.ruleNamed "newsgroup-name")
      ((seg g 0 g.length).map BitVec.toNat) = .ok b := by rw [hsg]; exact h
  have hset := DN.News.ArticleGrammar.gram_says (Nat.zero_le _) (Nat.le_refl _) h'
  rw [says_of h] at hs; subst hs
  rw [nn_eq, DN.News.AbnfGen.setOf_iff] at hset
  intro i hi
  obtain ⟨c, hc, hn⟩ := name_bytes hset i (Nat.zero_le _) hi
  rw [List.take_length, inputOf_lt hi, getElem!_pos g i hi] at hc
  cases hc; exact hn

theorem takeWhile_all {α : Type} {p : α → Bool} : ∀ {l : List α}, (∀ a ∈ l, p a = true) → l.takeWhile p = l
  | [], _ => rfl
  | a :: l, h => by
    simp only [List.takeWhile, h a List.mem_cons_self, takeWhile_all fun b hb => h b (List.mem_cons_of_mem _ hb)]

/-- A name with none of those bytes is its own element. -/
theorem elem_whole {g : Bytes} (h : ∀ i (hi : i < g.length), NameByte g[i].toNat) :
    DN.News.ArticleList.elem g 0 g.length ArticleSpec.COMMA = g := by
  have hm : ∀ x ∈ g, NameByte x.toNat := fun x hx => by
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx; exact h i hi
  have hsg : seg g 0 g.length = g := by simp [seg]
  unfold DN.News.ArticleList.elem DN.News.ArticleList.elemEnd
  rw [hsg, takeWhile_all fun x hx => by
    have := (hm x hx).1
    simp only [bne_iff_ne, ne_eq]; intro e; exact this (by rw [e]; rfl), Nat.zero_add, hsg]
  refine List.filter_eq_self.2 fun x hx => ?_
  obtain ⟨-, h2, h3, h4, h5⟩ := hm x hx
  have e1 : (x == 32#8) = false := by simp only [beq_eq_false_iff_ne]; intro e; exact h2 (by rw [e]; rfl)
  have e2 : (x == 9#8) = false := by simp only [beq_eq_false_iff_ne]; intro e; exact h3 (by rw [e]; rfl)
  have e3 : (x == 13#8) = false := by simp only [beq_eq_false_iff_ne]; intro e; exact h4 (by rw [e]; rfl)
  have e4 : (x == 10#8) = false := by simp only [beq_eq_false_iff_ne]; intro e; exact h5 (by rw [e]; rfl)
  simp only [DN.News.ArticleScan.gap, DN.News.CommandSpec.isWS, DN.News.CommandSpec.SP, DN.News.CommandSpec.TAB,
    DN.News.FrameSpec.CR, DN.News.FrameSpec.LF, e1, e2, e3, e4, Bool.or_false, Bool.not_false]

/-! ## No group twice -/

theorem eraseDups_len {α : Type} [BEq α] [LawfulBEq α] : ∀ (n : Nat) (l : List α), l.length ≤ n →
    l.eraseDups.length ≤ l.length ∧ (l.eraseDups.length = l.length ↔ l.Nodup)
  | _, [], _ => by simp [List.eraseDups_nil]
  | 0, _ :: _, h => by simp at h
  | n + 1, a :: as, h => by
    rw [List.eraseDups_cons, List.length_cons, List.length_cons]
    have hf := List.length_filter_le (fun b => !b == a) as
    simp only [List.length_cons] at h
    obtain ⟨h1, h2⟩ := eraseDups_len n (as.filter fun b => !b == a) (by omega)
    refine ⟨by omega, fun he => ?_, fun hn => ?_⟩
    · have hfl := List.length_filter_eq_length_iff.1 (show (as.filter fun b => !b == a).length = as.length by omega)
      have hfe : as.filter (fun b => !b == a) = as := List.filter_eq_self.2 hfl
      rw [hfe] at h2
      refine List.nodup_cons.2 ⟨fun ha => ?_, h2.1 (by rw [hfe] at he; omega)⟩
      have := hfl a ha; simp at this
    · obtain ⟨ha, hn'⟩ := List.nodup_cons.1 hn
      have hfe : as.filter (fun b => !b == a) = as :=
        List.filter_eq_self.2 fun b hb => by simp only [Bool.not_eq_true']; exact beq_eq_false_iff_ne.2 fun e => ha
                                              (e ▸ hb)
      rw [hfe] at h2 ⊢
      have := h2.2 hn'; omega

/-- **The groups each once**, as `Context.ok` says, as the program checks: no group equal to one before it. -/
theorem eraseDups_iff {α : Type} [BEq α] [LawfulBEq α] (l : List α) :
    (l.eraseDups.length == l.length) = true ↔ ∀ x (hx : x < l.length) y (hy : y < x), l[y] ≠ l[x] := by
  rw [beq_iff_eq, (eraseDups_len l.length l (Nat.le_refl _)).2, List.Nodup, List.pairwise_iff_getElem]
  exact ⟨fun h x hx y hy => h y x (by omega) hx hy, fun h i j _ hj hij => h j hj i hij⟩

/-! ## Bytes put in the input -/

/-- A byte copied into the input: from `off` past local `p`, at index `x`. -/
def copyB (x p : String) (off : Nat) : List Syntax.PStmt :=
  [kept x (ArticleProg.idCap - 1),
   .storeb (Syntax.eAdd (Syntax.atOff (Syntax.v "a") aInput) (Syntax.v x))
     (byte (Syntax.eAdd (Syntax.eAdd (Syntax.v p) (Syntax.n off)) (Syntax.v x))),
   inc x]

/-- `artContext`'s copy of `len` bytes from `off` past local `p` into the input, by index `x`. -/
def copyS (x len p : String) (off : Nat) : List Syntax.PStmt :=
  [.dec x (Syntax.n 0), .while (Syntax.eLt (Syntax.v x) (Syntax.v len)) (copyB x p off)]

/-- **Bytes put in the input**: `B`, read from `off` past local `p`, put from the input's start. -/
theorem copy_frag (o : Oracle σ) {R : Ret} {A : Word} {s1 : PancakeState σ} (hA : Area ArticleProg.ofs A s1)
    {l : List (String × Value)} (hla : l.lookup "a" = some A) {x len p : String} (hxa : x ≠ "a") (hxl : x ≠ len)
    (hxp : x ≠ p) (hx : Fresh x l = true) {B : Bytes} (hB : B.length ≤ ArticleProg.idCap)
    (hl : l.lookup len = some (BitVec.ofNat 64 B.length)) {P off : Nat}
    (hp : l.lookup p = some (at_ A P)) (hS : aIO ≤ P + off) (hS2 : P + off + B.length < 2 ^ 40) {M : Word → Word}
    (hby : ∀ i (hi : i < B.length), memLoadByte M s1.memaddrs s1.be (at_ A (P + off + i)) = some B[i]) :
    FragR o R (copyS x len p off) (RunF s1 l (· = M))
      (RunF s1 ((x, BitVec.ofNat 64 B.length) :: l) (· = putB M s1.be A aInput B)) := by
  have hA8 := hA.hA
  have hin := DN.News.AbnfLayout.input_le
  have hai := DN.News.AbnfLeaves.aInput_eq; have him := inputMax_eq
  have hX := X_eq; have hXv := X_val; have hic : ArticleProg.idCap = 256 := rfl
  unfold copyS
  refine fragR_of (frag_append (xs := [_]) (runF_dec o rfl hx (v := BitVec.ofNat 64 0) fun _ _ => rfl) ?_)
  let I : Assn σ := fun u => ∃ i, i ≤ B.length ∧
    RunF s1 ((x, BitVec.ofNat 64 i) :: l) (· = putB M s1.be A aInput (B.take i)) u
  have hlx : ∀ i, ((x, BitVec.ofNat 64 i) :: l).lookup len = some (BitVec.ofNat 64 B.length) := fun i => by
    rw [lookup_cons_ne (Ne.symm hxl)]; exact hl
  have hcond : ∀ u i, i ≤ B.length → RunF s1 ((x, BitVec.ofNat 64 i) :: l) (· = putB M s1.be A aInput (B.take i)) u →
      eval u (.cmp .less (.var x) (.var len)) = some (bw (decide (i < B.length))) := fun u i hi h =>
    FramerCode.eval_lt (by omega) (by omega) (ev_var (vals_lookup h.1.vals (lookup_head _ _ _)))
      (ev_var (vals_lookup h.1.vals (hlx i)))
  have hlow : LowKK (copyB x p off) := lowK_any _ (k := .skip) rfl
  refine frag_conseq (frag_while o rfl hlow (I := I) (fun u k ⟨i, hi, h⟩ => ⟨i, hi, runF_clock _ _ _ u k h⟩)
    (fun u y w _ hy => by simp [copyB, declared, kept, inc] at hy) (fun u ⟨i, hi, h⟩ => ⟨_, hcond u i hi h⟩) ?_)
    (fun u h => ⟨0, Nat.zero_le _, by simpa [putB] using h⟩) fun u ⟨⟨i, hi, h⟩, h0⟩ => ?_
  · refine frag_conseq (P0 := fun u => ∃ i, (i < B.length ∧
      RunF s1 ((x, BitVec.ofNat 64 i) :: l) (· = putB M s1.be A aInput (B.take i)) u)) (frag_exists hlow fun i => ?_)
      (fun u ⟨⟨i, hi, h⟩, hne⟩ => ⟨i, by rw [hcond u i hi h] at hne; exact of_decide_eq_true (bw_ne0 hne), h⟩)
      fun _ h => h
    refine frag_pure (i < B.length) (fun u h => h.1) hlow fun hi => ?_
    refine frag_conseq (P0 := RunF s1 ((x, BitVec.ofNat 64 i) :: l) (· = putB M s1.be A aInput (B.take i))) ?_
      (fun u h => h.2) fun _ h => h
    have hla' : ((x, BitVec.ofNat 64 i) :: l).lookup "a" = some A := by
      rw [lookup_cons_ne (Ne.symm hxa)]; exact hla
    have hpl : ((x, BitVec.ofNat 64 i) :: l).lookup p = some (at_ A P) := by
      rw [lookup_cons_ne (Ne.symm hxp)]; exact hp
    have htl : (B.take i).length = i := List.length_take_of_le (Nat.le_of_lt hi)
    refine frag_append (xs := [_]) (kept_frag o (by decide) (runF_clock _ _ _)
      fun u h => ⟨i, vals_lookup h.1.vals (lookup_head _ _ _), by omega⟩) ?_
    refine frag_append (xs := [_]) (DN.News.ArticleOut.putAt_frag o hla' (by rw [hai]; rfl) (lookup_head _ _ _) rfl
      (b := B[i]) (fun u h => ⟨_, loadByte_eval (ev_add (ev_add (ev_var (vals_lookup h.1.vals hpl)) rfl)
        (ev_var (vals_lookup h.1.vals (lookup_head _ _ _)))) (by
          rw [at_add, at_add, h.2, h.1.memaddrs, h.1.be, DN.News.ArticleDateOk.load_putB_other (.inr (by omega))
            (by omega) (by omega)]
          exact hby i hi), DN.News.ArticleRun.setWidth_byte _⟩)
      (by rw [DN.News.ScanRun.align_at hA8]; exact hA.dom _ (by omega) (by omega))) ?_
    refine frag_conseq (runF_set o rfl (x := x) (lookup_head _ _ _) (v := BitVec.ofNat 64 (i + 1))
      fun u h => DN.News.AbnfComment.ev_inc (vals_lookup h.1.vals (lookup_head _ _ _))) (fun _ h => h) fun u h =>
        ⟨i + 1, hi, ?_⟩
    rw [DN.News.ArticleFields.without_fresh hx] at h
    refine runF_mono h (fun q hq => hq) fun m hm => ?_
    rw [hm, List.take_add_one, List.getElem?_eq_getElem hi, Option.toList_some, putB_snoc, htl]
  · rw [hcond u i hi h] at h0
    have : i = B.length := by have := of_decide_eq_false (bw_eq0 h0); omega
    subst this
    rw [List.take_length] at h
    exact h

/-! ## `artContext`, part by part -/

open Syntax (v n eEq eLt eLe eAnd eAdd eMul) in
/-- The identity's length read and bounded. -/
def ctxHead : List Syntax.PStmt :=
  [ArticleProg.area, .dec "il" (wd ArticleProg.xIdLen),
   ifs (or2 (eLt (v "il") (n 0)) (eLt (n 200) (v "il"))) [.ret (n 0)]]

open Syntax (v n eEq eLt eLe eAnd eAdd eMul) in
/-- The identity matched as a path identity. -/
def ctxGram : List Syntax.PStmt :=
  guardS (.call "gi" "artGrammar" [n (AbnfProg.ruleIndex "path-identity"), n 0, v "il"]) ++
    [ifs (eEq (v "gi") (n 0)) [.ret (n 0)]]

open Syntax (v n eEq eLt eLe eAnd eAdd eMul) in
/-- The random value's byte `j` a hexadecimal digit, else 0 given back. -/
def randB : List Syntax.PStmt :=
  [kept "j" (ArticleProg.randCap - 1), .dec "b" (byte (eAdd (Syntax.atOff (v "a") ArticleProg.xRand) (v "j"))),
   .ite (or2 (ArticleProg.isDig (v "b")) (eAnd (eLe (n 97) (v "b")) (eLe (v "b") (n 102)))) [inc "j"] [.ret (n 0)]]

open Syntax (v n eLt) in
/-- The random value's bytes, each checked. -/
def randJ : List Syntax.PStmt := [.dec "j" (n 0), .while (eLt (v "j") (v "rl")) randB]

open Syntax (v n eEq eLt eLe eAnd eAdd eMul) in
/-- The random value's length bounded, its bytes hexadecimal digits. -/
def ctxRand : List Syntax.PStmt :=
  [.dec "rl" (wd ArticleProg.xRandLen), ifs (or2 (eLt (v "rl") (n 1)) (eLt (n 16) (v "rl"))) [.ret (n 0)]] ++ randJ

open Syntax (v n eEq eLt eLe eAnd eAdd eMul) in
/-- Group `y` before group `x` compared with it, byte by byte if their lengths are equal. -/
def dupB : List Syntax.PStmt :=
  [.dec "u" (eAdd (Syntax.atOff (v "a") ArticleProg.xGroups) (eMul (v "y") (n ArticleProg.groupSize))),
   ifs (eEq (.loadw 1 (v "u")) (v "gl"))
     [.dec "i" (n 0), .dec "same" (n 1),
      .while (eLt (v "i") (v "gl"))
        [kept "i" 63,
         ifs (ne (byte (eAdd (Syntax.atOff (v "t") 8) (v "i"))) (byte (eAdd (Syntax.atOff (v "u") 8) (v "i"))))
           [.assign "same" (n 0)],
         inc "i"],
      ifs (v "same") [.ret (n 0)]],
   inc "y"]

open Syntax (v n eEq eLt eLe eAnd eAdd eMul) in
/-- Group `x`: its length bounded, put in the input, not reserved, of the grammar, not one before it. -/
def groupB : List Syntax.PStmt :=
  [.dec "t" (eAdd (Syntax.atOff (v "a") ArticleProg.xGroups) (eMul (v "x") (n ArticleProg.groupSize))),
   .dec "gl" (.loadw 1 (v "t")), ifs (or2 (eLt (v "gl") (n 0)) (eLt (n 64) (v "gl"))) [.ret (n 0)]] ++
  copyS "gli" "gl" "t" 8 ++
  guardS (.call "ge" "artElem" [n 0, v "gl", n 44]) ++ [ifs (wd ArticleProg.xElemRes) [.ret (n 0)]] ++
  guardS (.call "gg" "artGrammar" [n (AbnfProg.ruleIndex "newsgroup-name"), n 0, v "gl"]) ++
  [ifs (eEq (v "gg") (n 0)) [.ret (n 0)], .dec "y" (n 0), .while (eLt (v "y") (v "x")) dupB, inc "x"]

open Syntax (v n eLt) in
/-- Each group checked, then the context fit. -/
def groupsX : List Syntax.PStmt := [.dec "x" (n 0), .while (eLt (v "x") (v "gn")) groupB, .ret (n 1)]

open Syntax (v n eLt) in
/-- The groups' count bounded, each group checked, the context fit. -/
def ctxGroups : List Syntax.PStmt :=
  [.dec "gn" (wd ArticleProg.xGroupsN), ifs (or2 (eLt (v "gn") (n 0)) (eLt (n 64) (v "gn"))) [.ret (n 0)]] ++ groupsX

theorem artContext_g : guardL ArticleProg.artContext.body =
    ctxHead ++ copyS "ili" "il" "a" ArticleProg.xId ++ ctxGram ++ ctxRand ++ ctxGroups := by
  unfold ArticleProg.artContext
  simp only [DN.News.ArticleGrammar.guardL_append]
  rfl

/-! ## What `artContext` reads and writes -/

open DN.News.ArticleListRun (BytesAt gAt)

/-- The words `artContext` may write: the input's, the slots, the input's length and `artElem`'s. -/
def CtxScr (A : Word) (x : Word) : Prop :=
  (∃ y, aInput ≤ y ∧ y < aIO ∧ x = at_ A y) ∨ (∃ k, k < slots ∧ InSlot A k x) ∨ x = at_ A aLen ∨ elemScratch A x

/-- **The context in the area**, each length as it is: what `artContext` reads. The sequence number, run and
connection are bounded as `Context.ok` asks; the program never reads them. -/
structure CtxIn (A : Word) (dm : Word → Bool) (be : Bool) (ctx : ArticleSpec.Context) (m : Word → Word) : Prop where
  idLen : m (at_ A ArticleProg.xIdLen) = BitVec.ofNat 64 ctx.identity.length
  idLt : ctx.identity.length < 2 ^ 63
  id : BytesAt A dm be ArticleProg.xId ArticleProg.idCap ctx.identity m
  randLen : m (at_ A ArticleProg.xRandLen) = BitVec.ofNat 64 ctx.random.length
  randLt : ctx.random.length < 2 ^ 63
  rand : BytesAt A dm be ArticleProg.xRand ArticleProg.randCap ctx.random m
  groupsN : m (at_ A ArticleProg.xGroupsN) = BitVec.ofNat 64 ctx.groups.length
  groupsLt : ctx.groups.length < 2 ^ 63
  groups : ∀ j, j < ctx.groups.length → j < 64 → m (at_ A (gAt j)) = BitVec.ofNat 64 ctx.groups[j]!.length ∧
    ctx.groups[j]!.length < 2 ^ 63 ∧ BytesAt A dm be (gAt j + 8) 64 ctx.groups[j]! m
  seq : ctx.seq < 2 ^ 64
  run : ctx.run < 2 ^ 64
  conn : ctx.conn < 2 ^ 64

/-- `artContext`'s memory: the grammar's words with the input `B`, every set, other words as in `m0`. -/
structure CtxM (s1 : PancakeState σ) (A : Word) (m0 : Word → Word) (B : Bytes) (M : Word → Word) : Prop where
  reads : Reads s1 A B M
  sets : AllSets A M
  frame : ∀ x, ¬CtxScr A x → M x = m0 x

/-- **What `artContext` gives back**: 1 if the context fits, else 0. The failed flag is clear, other words kept, every
set in place. -/
def CtxRet (A : Word) (ctx : ArticleSpec.Context) (m0 : Word → Word) : Ret := fun v m =>
  v = BitVec.ofNat 64 (bnat ctx.ok) ∧ m (at_ A aBroken) = 0 ∧ (∀ x, ¬CtxScr A x → m x = m0 x) ∧ AllSets A m

/-- A word past the slots, before `artElem`'s and not its two scalars, is none `artContext` writes. -/
theorem ctx_free {A : Word} {y : Nat} (h1 : ArticleProg.X ≤ y) (h2 : y < ArticleProg.xElem)
    (h3 : y ≠ ArticleProg.xElemLen) (h4 : y ≠ ArticleProg.xElemRes) : ¬CtxScr A (at_ A y) := by
  have hX := X_val; have hE := DN.News.ArticleListRun.xElem_eq; have hs := sets_le_X; have hXe := X_eq
  have hio := DN.News.AbnfLayout.io_le; have hp := DN.News.AbnfLayout.pow_lt
  have hw : ∀ j, ArticleProg.w j = 497936 + 8 * j := DN.News.ArticleFields.w_eq
  rintro (⟨z, -, z2, e⟩ | ⟨k, hk, i, hi, e⟩ | e | (⟨k, hk, e⟩ | e | e))
  · have := DN.News.ScanRun.at_inj (y := z) (by omega) (by omega) e; omega
  · have h3' := DN.News.AbnfSets.off_lt hk (8 * i) (by rw [DN.News.AbnfSets.setSize_eq] at hi ⊢; omega)
    have := DN.News.ScanRun.at_inj (by omega) (by omega) e; omega
  · have := DN.News.ScanRun.at_inj (by omega) (by decide) e; have : aLen = 8 := rfl; omega
  · have := DN.News.ScanRun.at_inj (by omega) (by omega) e; omega
  · exact h3 (DN.News.ScanRun.at_inj (by omega) (by simp only [ArticleProg.xElemLen, hw]; omega) e)
  · exact h4 (DN.News.ScanRun.at_inj (by omega) (by simp only [ArticleProg.xElemRes, hw]; omega) e)

theorem broken_free {A : Word} : ¬CtxScr A (at_ A aBroken) := by
  have hX := X_val; have hs := sets_le_X; have hXe := X_eq
  have hai := DN.News.AbnfLeaves.aInput_eq; have hb : aBroken = 24 := rfl
  rintro (⟨z, z1, z2, e⟩ | ⟨k, hk, i, hi, e⟩ | e | h)
  · have := DN.News.ScanRun.at_inj (y := z) (by decide) (by
      have := DN.News.AbnfLayout.io_le; have := DN.News.AbnfLayout.pow_lt; omega) e; omega
  · have h3' := DN.News.AbnfSets.off_lt hk (8 * i) (by rw [DN.News.AbnfSets.setSize_eq] at hi ⊢; omega)
    have := DN.News.ScanRun.at_inj (by decide) (by omega) e
    have : aSets ≤ DN.News.AbnfSets.off k := Nat.le_add_right _ _
    have := DN.News.AbnfLayout.pow_lt; have := DN.News.AbnfLayout.io_le
    have := DN.News.AbnfLayout.input_le
    omega
  · have := DN.News.ScanRun.at_inj (by decide) (by decide) e; have : aLen = 8 := rfl; omega
  · exact DN.News.ArticleListRun.not_scratch_low (by have := DN.News.ArticleGrammar.broken_low; omega) h

/-- Bounds for `reads_in` over the places of the grammar's words, taken as numbers: `omega` cannot unfold them. -/
theorem b_mask {P Mk C S b : Nat} (hm : P + 512 ≤ Mk) (hc : Mk + 64 ≤ C) (hcl : C ≤ S) (hb : b < 8) :
    P ≤ Mk + 8 * b ∧ Mk + 8 * b < S := by omega

theorem b_class {P Mk C S k i nc : Nat} (hm : P + 512 ≤ Mk) (hc : Mk + 64 ≤ C) (hce : C + 32 * nc ≤ S)
    (hk : k < nc) (hi : i < 4) : P ≤ C + 32 * k + 8 * i ∧ C + 32 * k + 8 * i < S := by omega

theorem b_text {P Mk C T S k nc nt d : Nat} (hm : P + 512 ≤ Mk) (hc : Mk + 64 ≤ C) (ht : C + 32 * nc ≤ T)
    (hte : T + 24 * nt ≤ S) (hk : k < nt) (hd : d < 24) : P ≤ T + 24 * k + d ∧ T + 24 * k + d < S := by omega

theorem b_tb {P Mk C T TB S nc nt tb tm to tl i : Nat} (hm : P + 512 ≤ Mk) (hc : Mk + 64 ≤ C)
    (ht : C + 32 * nc ≤ T) (htt : T + 24 * nt ≤ TB) (htb : TB + tb + tm + 1 ≤ S) (hof : to + tl ≤ tb) (hi : i < tl) :
    P ≤ (TB + to + i) / 8 * 8 ∧ (TB + to + i) / 8 * 8 < S := by omega

/-- What the leaves read, the input `B` put, kept where the words from the powers to the slots are. -/
theorem reads_in {s0 : PancakeState σ} {A : Word} (hA8 : A.toNat % 8 = 0) {B0 B : Bytes} {m0 m : Word → Word}
    (h : Reads s0 A B0 m0) (hin : InputAt m s0.memaddrs s0.be A B)
    (keep : ∀ y, aPow ≤ y → y < aSets → m (at_ A y) = m0 (at_ A y)) : Reads s0 A B m := by
  have hp := DN.News.AbnfLayout.pow_lt
  have hm := DN.News.AbnfLayout.mask_after; have hc := DN.News.AbnfLayout.class_after
  refine ⟨hin, fun j hj => ?_, fun b hb => ?_, fun k hk i hi => ?_, fun k hk => ?_⟩
  · rw [keep (aPow + 8 * j) (Nat.le_add_right _ _) (by omega)]; exact h.pows j hj
  · have := b_mask hm hc DN.News.AbnfLayout.aClass_le hb
    rw [keep (aMask + 8 * b) this.1 this.2]; exact h.masks b hb
  · have := b_class hm hc DN.News.AbnfLayout.classes_end hk hi
    rw [keep (aClass + 32 * k + 8 * i) this.1 this.2]; exact h.classes k hk i hi
  · have ht := DN.News.AbnfLayout.texts_after
    have hte := DN.News.AbnfLayout.texts_end
    have htt := DN.News.AbnfLayout.bytes_after
    have b0 := b_text (d := 0) hm hc ht hte hk (by decide)
    rw [Nat.add_zero] at b0
    have b8 := b_text (d := 8) hm hc ht hte hk (by decide)
    have b16 := b_text (d := 16) hm hc ht hte hk (by decide)
    obtain ⟨t0, t1, t2, t3⟩ := h.texts k hk
    refine ⟨by rw [keep (aTexts + 24 * k) b0.1 b0.2]; exact t0, by rw [keep _ b8.1 b8.2]; exact t1,
      by rw [keep _ b16.1 b16.2]; exact t2,
      fun i hi => ?_⟩
    have := t3 i hi
    have bt := b_tb hm hc ht htt DN.News.AbnfLayout.textBytes_le (textOff_le hk) hi
    unfold memLoadByte at this ⊢
    rw [DN.News.ScanRun.align_at hA8] at this ⊢
    rw [keep ((aTextBytes + textOff k + i) / 8 * 8) bt.1 bt.2]
    exact this

/-- Every set kept where the slots' words are. -/
theorem sets_hi {A : Word} {m M : Word → Word} (hall : AllSets A m)
    (hk : ∀ y, aSets ≤ y → y < ArticleProg.X → M (at_ A y) = m (at_ A y)) : AllSets A M := fun k hk' => by
  obtain ⟨S, hS⟩ := hall k hk'
  refine ⟨S, setAt_frame hS fun i hi => hk _ (Nat.le_trans (Nat.le_add_right _ _) (Nat.le_add_right _ _)) ?_⟩
  have h3 := DN.News.AbnfSets.off_lt hk' (8 * i) (by rw [DN.News.AbnfSets.setSize_eq] at hi ⊢; omega)
  have hX' := X_eq
  omega

theorem not_scratch_X {A : Word} {y : Nat} (hy : y < ArticleProg.X) : ¬elemScratch A (at_ A y) := by
  have hX := X_val; have hE := DN.News.ArticleListRun.xElem_eq
  have hw : ∀ j, ArticleProg.w j = 497936 + 8 * j := DN.News.ArticleFields.w_eq
  rintro (⟨k, hk, e⟩ | e | e)
  · have := DN.News.ScanRun.at_inj (by omega) (by omega) e; omega
  · have := DN.News.ScanRun.at_inj (by omega) (by simp only [ArticleProg.xElemLen, hw]; omega) e
    simp only [ArticleProg.xElemLen, hw] at this; omega
  · have := DN.News.ScanRun.at_inj (by omega) (by simp only [ArticleProg.xElemRes, hw]; omega) e
    simp only [ArticleProg.xElemRes, hw] at this; omega

/-- Where an input byte's word lies: from the input on, below its end, the powers and the slots' end. -/
theorem in_word {z : Nat} (h1 : aInput ≤ z) (h2 : z < aInput + 256) :
    aInput ≤ z / 8 * 8 ∧ z / 8 * 8 < aIO ∧ z / 8 * 8 < aPow ∧ z / 8 * 8 < aSets + slots * setSize ∧
      z / 8 * 8 % 8 = 0 ∧ z < 2 ^ 63 := by
  have := DN.News.AbnfLeaves.aInput_eq; have := DN.News.AbnfLayout.input_le; have := inputMax_eq
  have := DN.News.AbnfLayout.io_le; have := DN.News.AbnfLayout.pow_lt; have := sets_le_X; have := X_eq
  have := X_val
  omega

theorem lt40 {y : Nat} (h : y < ArticleProg.X) : y < 2 ^ 40 := by rw [X_val] at h; omega

theorem pow_le_X {y : Nat} (h : aSets ≤ y) : aPow ≤ y :=
  Nat.le_trans (Nat.le_trans (Nat.le_add_right _ _) DN.News.AbnfLayout.pow_lt) h

theorem sets_lt40 {y : Nat} (h : y < aSets) : y < 2 ^ 40 := lt40 (Nat.lt_of_lt_of_le h sets_le_X)

/-- **The input `B'` put**, `artContext`'s memory kept. -/
theorem ctxM_put {s1 : PancakeState σ} {A : Word} (hA : Area ArticleProg.ofs A s1) {m0 M : Word → Word}
    {B B' : Bytes} (hM : CtxM s1 A m0 B M) (hB' : B'.length ≤ ArticleProg.idCap) :
    CtxM s1 A m0 B' (putB M s1.be A aInput B') := by
  have hA8 := hA.hA
  have hic : ArticleProg.idCap = 256 := rfl
  have far : ∀ y, aPow ≤ y → y < 2 ^ 40 → putB M s1.be A aInput B' (at_ A y) = M (at_ A y) := fun y h1 h2 =>
    DN.News.ArticleCheck.putB_word _ hA8 _ _ _ _ fun z z1 z2 e => by
      have hw := in_word z1 (by rw [DN.News.AbnfLeaves.aInput_eq] at z2 ⊢; omega)
      have hy := DN.News.ScanRun.at_inj (by omega) (by omega) e
      exact absurd (hy ▸ h1) (Nat.not_le.2 hw.2.2.1)
  refine ⟨reads_in hA8 hM.reads (fun j hj => ?_) fun y h1 h2 => far y h1 (sets_lt40 h2),
    sets_hi hM.sets fun y h1 h2 => far y (pow_le_X h1) (lt40 h2), fun x hx => ?_⟩
  · have hw := in_word (z := aInput + j) (Nat.le_add_right _ _) (by rw [DN.News.AbnfLeaves.aInput_eq]; omega)
    have := DN.News.ArticleDateOk.load_putB (m := M) (dm := s1.memaddrs) (be := s1.be) (A := A) (x := aInput)
      (bs := B') (by rw [DN.News.AbnfLeaves.aInput_eq]; omega) j hj
      (by rw [DN.News.ScanRun.align_at hA8]; exact hA.dom _ hw.2.2.2.1 hw.2.2.2.2.1)
    rw [this, getElem!_pos B' j hj]
  · rw [DN.News.ArticleCheck.putB_word _ hA8 _ _ _ _ fun z z1 z2 e => by
      have hw := in_word z1 (by rw [DN.News.AbnfLeaves.aInput_eq] at z2 ⊢; omega)
      exact hx (.inl ⟨z / 8 * 8, hw.1, hw.2.1, e⟩)]
    exact hM.frame x hx

/-- **The input copied** from the context: `B'` read at `off` past `p`, put from the input's start. -/
theorem ctx_copy (o : Oracle σ) {R : Ret} {A : Word} {s1 : PancakeState σ} (hA : Area ArticleProg.ofs A s1)
    {l : List (String × Value)} (hla : l.lookup "a" = some A) {x len p : String} (hxa : x ≠ "a") (hxl : x ≠ len)
    (hxp : x ≠ p) (hx : Fresh x l = true) {B B' : Bytes} (hB' : B'.length ≤ ArticleProg.idCap)
    (hl : l.lookup len = some (BitVec.ofNat 64 B'.length)) {P off : Nat}
    (hp : l.lookup p = some (at_ A P)) (hS : aIO ≤ P + off) (hS2 : P + off + B'.length < 2 ^ 40) {m0 M : Word → Word}
    (hM : CtxM s1 A m0 B M)
    (hby : ∀ i (hi : i < B'.length), memLoadByte M s1.memaddrs s1.be (at_ A (P + off + i)) = some B'[i]) :
    FragR o R (copyS x len p off) (RunF s1 l (· = M))
      (fun u => ∃ M', RunF s1 ((x, BitVec.ofNat 64 B'.length) :: l) (· = M') u ∧ CtxM s1 A m0 B' M') :=
  fragR_conseq (copy_frag o hA hla hxa hxl hxp hx hB' hl hp hS hS2 hby) (fun _ h => h)
    fun _ h => ⟨_, h, ctxM_put hA hM hB'⟩

/-- **The grammar asked of the input**: whether rule `Ru` matches all of `B`, the memory kept. -/
theorem ctx_gram (o : Oracle σ) {R : Ret} {A : Word} {s1 : PancakeState σ} (hA : Area ArticleProg.ofs A s1)
    (hcode : ArtCode s1.code) {l : List (String × Value)} (hla : l.lookup "a" = some A) {rt : String}
    (hra : rt ≠ "a") (hrt : Fresh rt l = true) {m0 M : Word → Word} {B : Bytes} (hM : CtxM s1 A m0 B M)
    (hB : B.length ≤ ArticleProg.idCap) (hb0 : m0 (at_ A aBroken) = 0) {Ru : Nat} (hRu : Ru ∈ ArticleProg.usedRules)
    {b : Bool} (hok : DN.News.Abnf.matches? AbnfRules.grammar AbnfRules.depth Ru (B.map BitVec.toNat) = .ok b)
    {e3 : Syntax.PExpr} {E3 : PancakeExp} (he3 : Lower.lowerExp e3 = some E3)
    (hv3 : ∀ u, RunF s1 l (· = M) u → eval u E3 = some (BitVec.ofNat 64 B.length)) :
    FragR o R (guardS (.call rt "artGrammar" [Syntax.n Ru, Syntax.n 0, e3])) (RunF s1 l (· = M))
      (fun u => ∃ M', RunF s1 ((rt, bw (ArticleSpec.grammarSays Ru B)) :: l) (· = M') u ∧ CtxM s1 A m0 B M') := by
  have him := inputMax_eq; have hic : ArticleProg.idCap = 256 := rfl; have hM' := artMax_eq
  have hsg : seg B 0 B.length = B := by simp [seg]
  have hG := DN.News.ArticleFields.gram_field (a := B) (S := 0) (E := B.length) (Nat.zero_le _) (Nat.le_refl _)
    (R := Ru) (by rw [hsg]; exact hok)
  rw [hsg] at hG
  refine fragR_conseq (DN.News.ArticleFields.gramCall_frag o hA hcode hra hla hrt (a := B) (by omega) hM.reads
    hM.sets ((hM.frame _ broken_free).trans hb0) hRu (S := 0) (E := B.length) (by omega) (by omega) (Nat.le_refl _)
    rfl rfl he3 (fun _ _ => rfl) (fun _ _ => rfl) hv3) (fun _ h => h) fun u ⟨m, h, hR, hall, hfr⟩ => ⟨m, ?_, hR, hall,
      fun x hx => (hfr x (fun k hk hin => hx (.inr (.inl ⟨k, hk, hin⟩))) fun e => hx (.inr (.inr (.inl e)))).trans
        (hM.frame x hx)⟩
  rw [hG] at h; exact h

/-- **`artElem` on the input**: whether its element before a comma is reserved, the memory kept. -/
theorem ctx_elem (o : Oracle σ) {R : Ret} {A : Word} {s1 : PancakeState σ} (hA : Area ArticleProg.ofs A s1)
    (hD : ArtDom A s1.memaddrs) (hcode : ArtCode s1.code) {l : List (String × Value)} (hla : l.lookup "a" = some A)
    {rt y : String} (hra : rt ≠ "a") (hrt : Fresh rt l = true) {m0 M : Word → Word} {B : Bytes}
    (hM : CtxM s1 A m0 B M) (hB : B.length ≤ ArticleProg.idCap) (hb0 : m0 (at_ A aBroken) = 0)
    (hy : l.lookup y = some (BitVec.ofNat 64 B.length)) :
    FragR o R (guardS (.call rt "artElem" [Syntax.n 0, Syntax.v y, Syntax.n 44])) (RunF s1 l (· = M))
      (fun u => ∃ w M', RunF s1 ((rt, w) :: l) (· = M') u ∧ CtxM s1 A m0 B M' ∧
        M' (at_ A ArticleProg.xElemRes) =
          BitVec.ofNat 64 (bnat (ArticleSpec.reserved (DN.News.ArticleList.elem B 0 B.length ArticleSpec.COMMA)))) := by
  have hA8 := hA.hA; have hM' := artMax_eq; have hic : ArticleProg.idCap = 256 := rfl
  have hb : M (at_ A aBroken) = 0 := (hM.frame _ broken_free).trans hb0
  refine fragR_conseq (gcall_frag o hA hcode hra (f := ArticleProg.artElem) DN.News.ArticleListRun.mem_artElem
    (by decide) (args := [.const (BitVec.ofNat 64 0), .var y, .const (BitVec.ofNat 64 44)]) rfl hla
    (vs := [BitVec.ofNat 64 0, BitVec.ofNat 64 B.length, BitVec.ofNat 64 44]) rfl
    (fun u h => by simp only [evalArgs, ev_var (vals_lookup h.1.vals hy)]; rfl)
    (Rf := DN.News.ArticleListRun.ElemRet A s1.memaddrs s1.be B 0 B.length ArticleSpec.COMMA)
    (fun s hA1 _ hm hbe hloc hF => by
      have := DN.News.ArticleListRun.artElem_ok o hA1 (sep := ArticleSpec.COMMA) (by rw [hm]; exact hD) (by omega)
        (by rw [hF, hm, hbe]; exact hM.reads.input) (Nat.zero_le _) (Nat.le_refl _)
        ((hloc "p").trans rfl) ((hloc "e").trans rfl) ((hloc "sep").trans rfl)
      rw [hm, hbe] at this; exact this) hrt
    (G := fun _ m => DN.News.ArticleListRun.ElemOut A s1.memaddrs s1.be M
      (DN.News.ArticleList.elem B 0 B.length ArticleSpec.COMMA) m)
    (fun m m' v hm hr => by subst hm; exact hr.2)
    fun v m h => by rw [h.1 _ DN.News.ArticleListRun.broken_scr]; exact hb) (fun u h => h) fun u ⟨v, h⟩ => ?_
  obtain ⟨hfr, -, -, hres⟩ := h.2
  have hlo : ∀ z, z < ArticleProg.X → u.memory (at_ A z) = M (at_ A z) := fun z hz => hfr _ (not_scratch_X hz)
  exact ⟨v, u.memory, ⟨h.1, rfl⟩, ⟨DN.News.ArticleCheck.reads_lo hA8 (by omega) hM.reads hlo,
    DN.News.ArticleCheck.sets_lo hM.sets hlo, fun x hx => (hfr x fun h' => hx (.inr (.inr (.inr h')))).trans
      (hM.frame x hx)⟩, hres⟩

/-! ## `artContext` as `Context.ok` -/

theorem ok_iff (ctx : ArticleSpec.Context) : ctx.ok = true ↔
    ArticleSpec.grammarSays (ArticleSpec.ruleNamed "path-identity") ctx.identity = true ∧ ctx.identity.length ≤ 200 ∧
    1 ≤ ctx.random.length ∧ ctx.random.length ≤ 16 ∧ ctx.random.all ArticleSpec.isHexDigit = true ∧
    ctx.seq < 2 ^ 64 ∧ ctx.run < 2 ^ 64 ∧ ctx.conn < 2 ^ 64 ∧ ctx.groups.length ≤ 64 ∧
    (ctx.groups.eraseDups.length == ctx.groups.length) = true ∧
    ctx.groups.all (fun g => g.length ≤ 64 && !ArticleSpec.reserved g &&
      ArticleSpec.grammarSays (ArticleSpec.ruleNamed "newsgroup-name") g) = true := by
  unfold ArticleSpec.Context.ok
  simp only [Bool.and_eq_true, decide_eq_true_eq, and_assoc]

theorem ok_id {ctx : ArticleSpec.Context} (h : ctx.ok = true) : ArticleSpec.grammarSays
    (ArticleSpec.ruleNamed "path-identity") ctx.identity = true :=
  ((ok_iff ctx).1 h).1
theorem ok_idLen {ctx : ArticleSpec.Context} (h : ctx.ok = true) : ctx.identity.length ≤ 200 := ((ok_iff ctx).1 h).2.1
theorem ok_rand {ctx : ArticleSpec.Context} (h : ctx.ok = true) : 1 ≤ ctx.random.length ∧ ctx.random.length ≤ 16 :=
    ⟨((ok_iff ctx).1 h).2.2.1,
    ((ok_iff ctx).1 h).2.2.2.1⟩
theorem ok_hex {ctx : ArticleSpec.Context} (h : ctx.ok = true) : ctx.random.all ArticleSpec.isHexDigit = true :=
    ((ok_iff ctx).1 h).2.2.2.2.1
theorem ok_groupsLen {ctx : ArticleSpec.Context} (h : ctx.ok = true) : ctx.groups.length ≤ 64 :=
    ((ok_iff ctx).1 h).2.2.2.2.2.2.2.2.1
theorem ok_dups {ctx : ArticleSpec.Context} (h : ctx.ok = true) : (ctx.groups.eraseDups.length == ctx.groups.length) =
    true := ((ok_iff ctx).1 h).2.2.2.2.2.2.2.2.2.1
theorem ok_groups {ctx : ArticleSpec.Context} (h : ctx.ok = true) : ctx.groups.all
    (fun g => g.length ≤ 64 && !ArticleSpec.reserved g &&
    ArticleSpec.grammarSays (ArticleSpec.ruleNamed "newsgroup-name") g) = true := ((ok_iff ctx).1 h).2.2.2.2.2.2.2.2.2.2

theorem copyI_low : LowKK (copyS "ili" "il" "a" ArticleProg.xId) := lowK_any _ (k := .skip) rfl
theorem gram_low : LowKK ctxGram := lowK_any _ (k := .skip) rfl
theorem rand_low : LowKK ctxRand := lowK_any _ (k := .skip) rfl
theorem groups_low : LowKK ctxGroups := lowK_any _ (k := .skip) rfl

/-- The program names rules as `AbnfProg` does, the rules as `ArticleSpec` does: the same index. -/
theorem pid_rule : AbnfProg.ruleIndex "path-identity" = ArticleSpec.ruleNamed "path-identity" := rfl
theorem nn_rule : AbnfProg.ruleIndex "newsgroup-name" = ArticleSpec.ruleNamed "newsgroup-name" := rfl

theorem pid_used : AbnfProg.ruleIndex "path-identity" ∈ ArticleProg.usedRules := by
  unfold ArticleProg.usedRules; exact List.mem_eraseDups.2 (List.mem_append_right _ (by simp))

theorem nn_used : AbnfProg.ruleIndex "newsgroup-name" ∈ ArticleProg.usedRules := by
  unfold ArticleProg.usedRules; exact List.mem_eraseDups.2 (List.mem_append_right _ (by simp))

theorem io_le_X : aIO ≤ ArticleProg.X :=
  Nat.le_trans DN.News.AbnfLayout.io_le (Nat.le_trans (Nat.le_trans (Nat.le_add_right _ _) DN.News.AbnfLayout.pow_lt)
    sets_le_X)

/-- A byte of the context's area as the context gave it. -/
theorem ctx_byte {s1 : PancakeState σ} {A : Word} (hA8 : A.toNat % 8 = 0) {m0 M : Word → Word} {B : Bytes}
    (hM : CtxM s1 A m0 B M) {y : Nat} (h1 : ArticleProg.xGroups ≤ y) (h2 : y < ArticleProg.xElem) :
    memLoadByte M s1.memaddrs s1.be (at_ A y) = memLoadByte m0 s1.memaddrs s1.be (at_ A y) := by
  have hX := X_val; have hG := DN.News.ArticleListRun.xGroups_eq; have hE := DN.News.ArticleListRun.xElem_eq
  have hw : ∀ j, ArticleProg.w j = 497936 + 8 * j := DN.News.ArticleFields.w_eq
  refine DN.News.ArticleOut.load_frame hM.frame ?_
  rw [DN.News.ScanRun.align_at hA8]
  exact ctx_free (by omega) (by omega) (by simp only [ArticleProg.xElemLen, hw]; omega)
    (by simp only [ArticleProg.xElemRes, hw]; omega)

/-- A word of the context's as the context gave it. -/
theorem ctx_word {s1 : PancakeState σ} {A : Word} {m0 M : Word → Word} {B : Bytes} (hM : CtxM s1 A m0 B M) {i : Nat}
    (hi : i < 21) : M (at_ A (ArticleProg.w i)) = m0 (at_ A (ArticleProg.w i)) := by
  have hX := X_val; have hE := DN.News.ArticleListRun.xElem_eq
  have hw : ∀ j, ArticleProg.w j = 497936 + 8 * j := DN.News.ArticleFields.w_eq
  exact hM.frame _ (ctx_free (by rw [hw]; omega) (by rw [hw]; omega) (by simp only [ArticleProg.xElemLen, hw]; omega)
    (by simp only [ArticleProg.xElemRes, hw]; omega))

/-- **A bound checked**: 0 given back past it, else the value within it. -/
theorem bound_frag (o : Oracle σ) {R : Ret} {s1 : PancakeState σ} {L : List (String × Value)}
    {F : (Word → Word) → Prop} {x : String} {N lo hi : Nat} (hN : N < 2 ^ 63) (hlo : lo < 2 ^ 63) (hhi : hi < 2 ^ 63)
    (hx : L.lookup x = some (BitVec.ofNat 64 N))
    (hbad : N < lo ∨ hi < N → ∀ u, RunF s1 L F u → R (BitVec.ofNat 64 0) u.memory) :
    FragR o R [ifs (or2 (Syntax.eLt (Syntax.v x) (Syntax.n lo)) (Syntax.eLt (Syntax.n hi) (Syntax.v x)))
      [.ret (Syntax.n 0)]] (RunF s1 L F) (fun u => RunF s1 L F u ∧ lo ≤ N ∧ N ≤ hi) :=
  fragR_if o rfl (lowKK_ret rfl) (fun k => ⟨k, rfl⟩) (fun u k h => ⟨runF_clock _ _ _ u k h.1, h.2⟩)
    (fun _ _ _ _ hy => nomatch hy) (fun _ _ _ _ hy => nomatch hy) (b := decide (N < lo) || decide (hi < N))
    (fun u h => FramerCode.eval_or2 (FramerCode.eval_lt hN hlo (ev_var (vals_lookup h.1.vals hx)) rfl)
      (FramerCode.eval_lt hhi hN rfl (ev_var (vals_lookup h.1.vals hx))))
    (fun hb => fragR_ret o rfl fun u h => ⟨_, rfl, hbad (by
      simp only [Bool.or_eq_true, decide_eq_true_eq] at hb; exact hb) u h⟩)
    fun hb => fragR_of (frag_nil o fun u h => ⟨h, by
      simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not] at hb; omega⟩)

/-- **The grammar's answer checked**: 0 given back if it says no. -/
theorem gram_check (o : Oracle σ) {R : Ret} {s1 : PancakeState σ} {L : List (String × Value)}
    {F : (Word → Word) → Prop} {rt : String} {G : Bool} (hx : L.lookup rt = some (bw G))
    (hbad : G = false → ∀ u, RunF s1 L F u → R (BitVec.ofNat 64 0) u.memory) :
    FragR o R [ifs (Syntax.eEq (Syntax.v rt) (Syntax.n 0)) [.ret (Syntax.n 0)]] (RunF s1 L F)
      (fun u => RunF s1 L F u ∧ G = true) :=
  fragR_if o rfl (lowKK_ret rfl) (fun k => ⟨k, rfl⟩) (fun u k h => ⟨runF_clock _ _ _ u k h.1, h.2⟩)
    (fun _ _ _ _ hy => nomatch hy) (fun _ _ _ _ hy => nomatch hy) (b := !G)
    (fun u h => by
      rw [FramerCode.eval_eq (x := if G then 1 else 0) (y := 0) (by split <;> decide) (by decide)
        (by rw [ev_var (vals_lookup h.1.vals hx), DN.News.ArticleRun.bw_ofNat]) rfl]
      cases G <;> rfl)
    (fun hb => fragR_ret o rfl fun u h => ⟨_, rfl, hbad (by revert hb; cases G <;> decide) u h⟩)
    fun hb => fragR_of (frag_nil o fun u h => ⟨h, by revert hb; cases G <;> decide⟩)

theorem eval_ne {t : PancakeState σ} {a b : PancakeExp} {x y : Nat} (hx : x < 2 ^ 64) (hy : y < 2 ^ 64)
    (ha : eval t a = some (BitVec.ofNat 64 x)) (hb : eval t b = some (BitVec.ofNat 64 y)) :
    eval t (.cmp .equal (.cmp .equal a b) (.const (BitVec.ofNat 64 0))) = some (bw (!decide (x = y))) := by
  have h1 := FramerCode.eval_eq hx hy ha hb
  rw [DN.News.ArticleRun.bw_ofNat] at h1
  rw [FramerCode.eval_eq (t := t) (y := 0) (by split <;> decide) (by decide) h1 rfl]
  cases decide (x = y) <;> rfl

theorem cmp_succ {g1 g2 : Bytes} (i : Nat) :
    decide (∀ j, j < i + 1 → g1[j]! = g2[j]!) =
      (decide (∀ j, j < i → g1[j]! = g2[j]!) && !!decide ((g1[i]!).toNat = (g2[i]!).toNat)) := by
  rw [Bool.not_not]
  apply Bool.eq_iff_iff.2
  simp only [decide_eq_true_eq, Bool.and_eq_true]
  constructor
  · intro hh; exact ⟨fun j hj => hh j (by omega), BitVec.toNat_inj.2 (hh i (by omega))⟩
  · rintro ⟨h1, h2⟩ j hj
    by_cases e : j = i
    · subst e; exact BitVec.toNat_inj.1 h2
    · exact h1 j (by omega)

theorem cmp_full {g1 g2 : Bytes} {N : Nat} (hg : g1.length = N) (hg2 : g2.length = N) :
    decide (∀ j, j < N → g1[j]! = g2[j]!) = decide (g1 = g2) := by
  apply Bool.eq_iff_iff.2
  simp only [decide_eq_true_eq]
  constructor
  · intro hh; refine List.ext_getElem (by omega) fun j h1 h2 => ?_
    have := hh j (by omega); rwa [getElem!_pos g1 j h1, getElem!_pos g2 j h2] at this
  · rintro rfl j _; rfl

/-- A refusal of the context: 0, nothing more written. -/
theorem ctx_ret0 {s1 : PancakeState σ} {A : Word} {m0 M : Word → Word} {B : Bytes} (hM : CtxM s1 A m0 B M)
    (hb : m0 (at_ A aBroken) = 0) {ctx : ArticleSpec.Context} (hok : ctx.ok = false) :
    CtxRet A ctx m0 (BitVec.ofNat 64 0) M :=
  ⟨by rw [hok]; rfl, (hM.frame _ broken_free).trans hb, hM.frame, hM.sets⟩

/-- Byte `i` of group `t` and of group `u` compared: `same` 0 if they differ. -/
def cmpB : List Syntax.PStmt :=
  [kept "i" 63,
   ifs (ne (byte (Syntax.eAdd (Syntax.atOff (Syntax.v "t") 8) (Syntax.v "i")))
     (byte (Syntax.eAdd (Syntax.atOff (Syntax.v "u") 8) (Syntax.v "i")))) [.assign "same" (Syntax.n 0)],
   inc "i"]

/-- Group `t`'s first `gl` bytes and group `u`'s compared: `same` 1 if they are equal. -/
def cmpS : List Syntax.PStmt :=
  [.dec "i" (Syntax.n 0), .dec "same" (Syntax.n 1), .while (Syntax.eLt (Syntax.v "i") (Syntax.v "gl")) cmpB]

/-- **Two groups compared** byte by byte: `same` 1 exactly if they are equal. -/
theorem cmp_frag (o : Oracle σ) {R : Ret} {s1 : PancakeState σ} {A : Word} {L : List (String × Value)}
    {g1 g2 : Bytes} {N : Nat} (hN : N ≤ 64) (hg : g1.length = N) (hg2 : g2.length = N) {Pt Pu : Nat}
    (ht : L.lookup "t" = some (at_ A Pt)) (hu : L.lookup "u" = some (at_ A Pu))
    (hgl : L.lookup "gl" = some (BitVec.ofNat 64 N)) (hfi : Fresh "i" L = true) (hfs : Fresh "same" L = true)
    {M : Word → Word} (hbt : ∀ i, i < N → memLoadByte M s1.memaddrs s1.be (at_ A (Pt + 8 + i)) = some g1[i]!)
    (hbu : ∀ i, i < N → memLoadByte M s1.memaddrs s1.be (at_ A (Pu + 8 + i)) = some g2[i]!) :
    FragR o R cmpS (RunF s1 L (· = M))
      (RunF s1 (("i", BitVec.ofNat 64 N) :: ("same", BitVec.ofNat 64 (bnat (decide (g1 = g2)))) :: L) (· = M)) := by
  unfold cmpS
  refine fragR_of (frag_append (xs := [_]) (runF_dec o rfl hfi (v := BitVec.ofNat 64 0) fun _ _ => rfl) ?_)
  refine frag_append (xs := [_]) (runF_dec o rfl (fresh_cons (by decide) hfs) (v := BitVec.ofNat 64 1)
    fun _ _ => rfl) ?_
  let Ls : Nat → Bool → List (String × Value) := fun i b =>
    ("i", BitVec.ofNat 64 i) :: ("same", BitVec.ofNat 64 (bnat b)) :: L
  let P : Nat → Bool := fun i => decide (∀ j, j < i → g1[j]! = g2[j]!)
  let I : Assn σ := fun u => ∃ i, i ≤ N ∧ RunF s1 (Ls i (P i)) (· = M) u
  have hcond : ∀ u i b, i ≤ N → RunF s1 (Ls i b) (· = M) u →
      eval u (.cmp .less (.var "i") (.var "gl")) = some (bw (decide (i < N))) := fun u i b hi h =>
    FramerCode.eval_lt (by omega) (by omega) (ev_var (vals_lookup h.1.vals rfl))
      (ev_var (vals_lookup h.1.vals hgl))
  have hlow : LowKK cmpB := lowK_any _ (k := .skip) rfl
  refine frag_conseq (frag_while o rfl hlow (I := I) (fun u k ⟨i, hi, h⟩ => ⟨i, hi, runF_clock _ _ _ u k h⟩)
    (fun u y w _ hy => by simp [cmpB, declared, kept, inc, ifs] at hy) (fun u ⟨i, hi, h⟩ => ⟨_, hcond u i _ hi h⟩)
      ?_)
    (fun u h => ⟨0, Nat.zero_le _, runF_mono h (fun q hq => by
      have hP0 : P 0 = true := by simp [P]
      simp only [Ls, hP0, List.mem_cons] at hq
      rcases hq with rfl | rfl | hq
      · exact List.mem_cons_of_mem _ List.mem_cons_self
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hq)) fun _ e => e⟩) fun u ⟨⟨i, hi, h⟩, h0⟩ => ?_
  · refine frag_conseq (P0 := fun u => ∃ i, i < N ∧ RunF s1 (Ls i (P i)) (· = M) u) (frag_exists hlow fun i => ?_)
      (fun u ⟨⟨i, hi, h⟩, hne⟩ => ⟨i, by rw [hcond u i _ hi h] at hne; exact of_decide_eq_true (bw_ne0 hne), h⟩)
      fun _ g2 => g2
    refine frag_pure (i < N) (fun u h => h.1) hlow fun hi => ?_
    refine frag_conseq (P0 := RunF s1 (Ls i (P i)) (· = M)) ?_ (fun u h => h.2) fun _ h => h
    have hlt : ∀ b, (Ls i b).lookup "t" = some (at_ A Pt) := fun _ => ht
    have hlu : ∀ b, (Ls i b).lookup "u" = some (at_ A Pu) := fun _ => hu
    refine frag_append (xs := [_]) (kept_frag o (by decide) (runF_clock _ _ _)
      fun u h => ⟨i, vals_lookup h.1.vals rfl, by omega⟩) ?_
    have hgi := (g1[i]!).isLt; have hhi := (g2[i]!).isLt
    have hev : ∀ u, RunF s1 (Ls i (P i)) (· = M) u → ∀ (Q : Nat) (c : BitVec 8) (x : String),
        (Ls i (P i)).lookup x = some (at_ A Q) →
        memLoadByte M s1.memaddrs s1.be (at_ A (Q + 8 + i)) = some c →
        eval u (.loadByte (.op .add (.op .add (.var x) (.const (BitVec.ofNat 64 8))) (.var "i"))) =
          some (BitVec.ofNat 64 c.toNat) := fun u h Q c x hx hm => by
      refine loadByte_eval (w := at_ A (Q + 8 + i)) ?_ (by rw [h.2, h.1.memaddrs, h.1.be]; exact hm)
      simp only [eval, vals_lookup h.1.vals hx, vals_lookup h.1.vals (show (Ls i (P i)).lookup "i" = _ from rfl)]
      rw [at_add, at_add]
    let b := !decide ((g1[i]!).toNat = (g2[i]!).toNat)
    have hLs : ∀ q ∈ L, q.1 ≠ "same" ∧ q.1 ≠ "i" := fun q hq =>
      ⟨DN.News.ScanRun.fresh_ne hfs q hq, DN.News.ScanRun.fresh_ne hfi q hq⟩
    refine frag_append (xs := [_]) (DN.News.ScanRun.frag_if o rfl (lowK_any _ (k := .skip) rfl) (fun k => ⟨k, rfl⟩)
      rfl rfl (Q := RunF s1 (Ls i (P i && !b)) (· = M)) (runF_clock _ _ _) (b := b) (fun u h => eval_ne (by omega)
        (by omega) (hev u h Pt _ "t" (hlt _) (hbt i hi)) (hev u h Pu _ "u" (hlu _) (hbu i hi)))
      (fun hb => frag_conseq (runF_set o rfl (x := "same") rfl (v := BitVec.ofNat 64 0) fun _ _ => rfl) (fun _ h => h)
        fun u h => runF_mono h (fun q hq => by
          rw [hb] at hq
          simp only [Ls, List.mem_cons, Bool.not_true, Bool.and_false] at hq
          rcases hq with rfl | rfl | hq
          · exact List.mem_cons_of_mem _ (mem_without List.mem_cons_self (show "i" ≠ "same" by decide))
          · exact List.mem_cons_self
          · exact List.mem_cons_of_mem _ (mem_without (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hq))
              (hLs q hq).1)) fun _ e => e)
      (fun hb => frag_nil o fun u h => by rw [hb, Bool.not_false, Bool.and_true]; exact h)) ?_
    refine frag_conseq (runF_set o rfl (x := "i") rfl (v := BitVec.ofNat 64 (i + 1))
      fun u h => DN.News.AbnfComment.ev_inc (vals_lookup h.1.vals rfl)) (fun _ h => h)
      fun u h => ⟨i + 1, by omega, runF_mono h (fun q hq => by
        rw [show P (i + 1) = (P i && !b) from cmp_succ i] at hq
        simp only [Ls, List.mem_cons] at hq
        rcases hq with rfl | rfl | hq
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (mem_without (List.mem_cons_of_mem _ List.mem_cons_self)
            (show "same" ≠ "i" by decide))
        · exact List.mem_cons_of_mem _ (mem_without (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hq))
            (hLs q hq).2)) fun _ e => e⟩
  · rw [hcond u i _ hi h] at h0
    have : i = N := by have := of_decide_eq_false (bw_eq0 h0); omega
    subst this
    have hP : P i = decide (g1 = g2) := cmp_full hg hg2
    rw [hP] at h; exact h

/-- **A group before `x` compared with it**: none equal, else 0 given back. -/
theorem dup_step (o : Oracle σ) {A : Word} {s1 : PancakeState σ} (hD : ArtDom A s1.memaddrs) {ctx : ArticleSpec.Context}
    {m0 M : Word → Word} {B : Bytes} (hM : CtxM s1 A m0 B M) (hb0 : m0 (at_ A aBroken) = 0) {x : Nat}
    (hx : x < ctx.groups.length) (hN : ctx.groups[x].length ≤ 64) {L : List (String × Value)}
    (hla : L.lookup "a" = some A) (hgl : L.lookup "gl" = some (BitVec.ofNat 64 ctx.groups[x].length))
    (ht : L.lookup "t" = some (at_ A (gAt x))) (hfu : Fresh "u" L = true) (hfi : Fresh "i" L = true)
    (hfs : Fresh "same" L = true) (hfy : Fresh "y" L = true)
    (hw : ∀ j (hj : j < ctx.groups.length), j < 64 → M (at_ A (gAt j)) = BitVec.ofNat 64 ctx.groups[j].length)
    (hby : ∀ j (hj : j < ctx.groups.length), j < 64 → ∀ i, i < 64 → i < ctx.groups[j].length →
      memLoadByte M s1.memaddrs s1.be (at_ A (gAt j + 8 + i)) = some ctx.groups[j][i]!)
    (hl64 : ∀ j (hj : j < ctx.groups.length), j < 64 → ctx.groups[j].length < 2 ^ 63)
    (hx64 : x < 64) {y : Nat} (hy : y < x) :
    FragR o (CtxRet A ctx m0) dupB (RunF s1 (("y", BitVec.ofNat 64 y) :: L) (· = M))
      (fun u => RunF s1 (("u", at_ A (gAt y)) :: ("y", BitVec.ofNat 64 (y + 1)) :: L) (· = M) u ∧
        ctx.groups[y] ≠ ctx.groups[x]) := by
  have hyl : y < ctx.groups.length := by omega
  let gx := ctx.groups[x]; let gy := ctx.groups[y]
  have hgx := hby x hx hx64; have hgy := hby y hyl (by omega)
  unfold dupB
  let L1 : List (String × Value) := ("u", at_ A (gAt y)) :: ("y", BitVec.ofNat 64 y) :: L
  refine fragR_append (xs := [_]) (fragR_of (runF_dec o rfl (fresh_cons (by decide) hfu) (v := at_ A (gAt y))
    fun u h => by
    simp only [eval, vals_lookup h.1.vals (show (("y", BitVec.ofNat 64 y) :: L).lookup "a" = some A by
      rw [lookup_cons_ne (by decide)]; exact hla), vals_lookup h.1.vals (lookup_head _ _ _)]
    rw [DN.News.ArticleRun.at_mul]; unfold gAt; rw [Nat.mul_comm])) ?_
  have hl1 : ∀ z, z ≠ "u" → z ≠ "y" → L1.lookup z = L.lookup z := fun z h1 h2 => by
    show (("u", _) :: ("y", _) :: L).lookup z = _
    rw [lookup_cons_ne h1, lookup_cons_ne h2]
  have hfr1 : ∀ z, Fresh z L = true → z ≠ "u" → z ≠ "y" → Fresh z L1 = true := fun z hz h1 h2 =>
    fresh_cons (Ne.symm h1) (fresh_cons (Ne.symm h2) hz)
  refine fragR_append (xs := [_]) (M := fun u => RunF s1 L1 (· = M) u ∧ ctx.groups[y] ≠ ctx.groups[x])
    (fragR_if o rfl (lowK_any _ (k := .skip) rfl) (fun k => ⟨k, rfl⟩) (fun u k h => ⟨runF_clock _ _ _ u k h.1, h.2⟩)
      (fun u z w h hz => by
        have hz' : z = "i" ∨ z = "same" := by simpa [cmpS, declared, kept, inc, ifs] using hz
        rcases hz' with rfl | rfl
        · exact ⟨runF_restore h.1 (hfr1 _ hfi (by decide) (by decide)) w, h.2⟩
        · exact ⟨runF_restore h.1 (hfr1 _ hfs (by decide) (by decide)) w, h.2⟩)
      (fun _ _ _ _ hz => nomatch hz) (b := decide (gy.length = gx.length))
      (fun u h => FramerCode.eval_eq (Nat.lt_trans (hl64 y hyl (by omega)) (by decide))
        (Nat.lt_trans (hl64 x hx hx64) (by decide))
        (by
          rw [show eval u (.loadWord (.var "u")) = some (u.memory (at_ A (gAt y))) from
            DN.News.ArticleRun.loadA_eval h.1.memaddrs (DN.News.ArticleListRun.gAt_dom hD (by omega))
              (ev_var (vals_lookup h.1.vals (lookup_head _ _ _))), h.2, hw y hyl (by omega)])
        (ev_var (vals_lookup h.1.vals (by rw [hl1 _ (by decide) (by decide)]; exact hgl)))) (fun hb => ?_)
      fun hb => fragR_of (frag_nil o fun u h => ⟨h, fun e => by
        have := of_decide_eq_false hb; exact this (by rw [show gy = gx from e])⟩)) ?_
  · have hlen : gy.length = gx.length := of_decide_eq_true hb
    refine fragR_append (cmp_frag o (L := L1) (g1 := gx) (g2 := gy) hN rfl hlen
      (by rw [hl1 _ (by decide) (by decide)]; exact ht) (lookup_head _ _ _)
      (by rw [hl1 _ (by decide) (by decide)]; exact hgl) (hfr1 _ hfi (by decide) (by decide))
      (hfr1 _ hfs (by decide) (by decide)) (fun i hi => hgx i (by omega) hi)
      fun i hi => hgy i (by omega) (by rw [← hlen] at hi; exact hi))
      ?_
    let E := decide (gx = gy)
    have hEv : BitVec.ofNat 64 (bnat E) = bw E := by cases E <;> rfl
    refine fragR_if o rfl (lowKK_ret rfl) (fun k => ⟨k, rfl⟩) (fun u k h => ⟨runF_clock _ _ _ u k h.1, h.2⟩)
      (fun _ _ _ _ hz => nomatch hz) (fun _ _ _ _ hz => nomatch hz) (b := E)
      (fun u h => by rw [ev_var (vals_lookup h.1.vals rfl), hEv]; rfl) (fun hE => ?_)
      fun hE => fragR_of (frag_nil o fun u h => ⟨runF_mono h (fun q hq => List.mem_cons_of_mem _
        (List.mem_cons_of_mem _ hq)) fun _ e => e, fun e => by
          have := of_decide_eq_false hE; exact this (by rw [show gy = gx from e])⟩)
    exact fragR_ret o rfl fun u h => ⟨_, rfl, ctx_ret0 (M := u.memory) (by rw [h.2]; exact hM) hb0
      (Bool.eq_false_iff.2 fun hok => by
        have hd := (eraseDups_iff ctx.groups).1 (ok_dups hok) x hx y hy
        exact hd (of_decide_eq_true hE).symm)⟩
  refine fragR_pure _ (fun u h => h.2) (lowK_any _ (k := .skip) rfl) fun hne => ?_
  refine fragR_of (frag_conseq (runF_set o rfl (x := "y") (by rw [lookup_cons_ne (by decide)]; exact lookup_head _ _ _)
    (v := BitVec.ofNat 64 (y + 1)) fun u h => DN.News.AbnfComment.ev_inc (vals_lookup h.1.vals
      (show L1.lookup "y" = _ by rw [lookup_cons_ne (by decide)]; exact lookup_head _ _ _))) (fun u h => h.1)
    fun u h => ⟨runF_mono h (fun q hq => ?_) fun _ e => e, hne⟩)
  rcases List.mem_cons.1 hq with rfl | hq
  · exact List.mem_cons_of_mem _ (mem_without List.mem_cons_self (show "u" ≠ "y" by decide))
  rcases List.mem_cons.1 hq with rfl | hq
  · exact List.mem_cons_self
  · exact List.mem_cons_of_mem _ (mem_without (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hq))
      (DN.News.ScanRun.fresh_ne hfy q hq))

/-- The groups before `x` each fit, none equal to one before it. -/
def GOk (gs : List Bytes) (x : Nat) : Prop :=
  ∀ x' (h : x' < gs.length), x' < x → gs[x'].length ≤ 64 ∧ ArticleSpec.reserved gs[x'] = false ∧
    ArticleSpec.grammarSays (ArticleSpec.ruleNamed "newsgroup-name") gs[x'] = true ∧
      ∀ y (hy : y < x'), gs[y]'(by omega) ≠ gs[x']

theorem gok_all {gs : List Bytes} (h : GOk gs gs.length) :
    gs.all (fun g => g.length ≤ 64 && !ArticleSpec.reserved g &&
      ArticleSpec.grammarSays (ArticleSpec.ruleNamed "newsgroup-name") g) = true ∧
    (gs.eraseDups.length == gs.length) = true := by
  refine ⟨List.all_eq_true.2 fun g hg => ?_, (eraseDups_iff gs).2 fun x hx y hy => (h x hx hx).2.2.2 y hy⟩
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hg
  obtain ⟨h1, h2, h3, -⟩ := h i hi hi
  simp [h1, h2, h3]

/-- A group's name not of the grammar, or reserved, or too long: the context does not fit. -/
theorem group_bad {ctx : ArticleSpec.Context} {x : Nat} (hx : x < ctx.groups.length)
    (h : ¬(ctx.groups[x].length ≤ 64 ∧ ArticleSpec.reserved ctx.groups[x] = false ∧
      ArticleSpec.grammarSays (ArticleSpec.ruleNamed "newsgroup-name") ctx.groups[x] = true)) : ctx.ok = false :=
  Bool.eq_false_iff.2 fun hok => h (by
    have := List.all_eq_true.1 (ok_groups hok) _ (List.getElem_mem hx)
    simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at this
    exact ⟨this.1.1, this.1.2, this.2⟩)

theorem bnat_word (b : Bool) : BitVec.ofNat 64 (bnat b) = (if b then 1 else 0 : Word) := by cases b <;> rfl

theorem gAt_free {j : Nat} (hj : j < 64) {y : Nat} (hy : y < 88) :
    ArticleProg.X ≤ gAt j + y ∧ gAt j + y < ArticleProg.xElem ∧ ArticleProg.xGroups ≤ gAt j + y ∧
      gAt j + y ≠ ArticleProg.xElemLen ∧ gAt j + y ≠ ArticleProg.xElemRes ∧ gAt j + y < 2 ^ 40 := by
  have hX := X_val; have hG := DN.News.ArticleListRun.xGroups_eq; have hE := DN.News.ArticleListRun.xElem_eq
  have hw : ∀ i, ArticleProg.w i = 497936 + 8 * i := DN.News.ArticleFields.w_eq
  have hgs : ArticleProg.groupSize = 80 := rfl
  unfold gAt; simp only [ArticleProg.xElemLen, ArticleProg.xElemRes, hw, hgs]; omega

/-- A group's length word as the context gave it, where `artContext` keeps the context. -/
theorem group_word {s1 : PancakeState σ} {A : Word} {ctx : ArticleSpec.Context}
    (hctx : CtxIn A s1.memaddrs s1.be ctx s1.memory) {M : Word → Word} {B : Bytes} (hM : CtxM s1 A s1.memory B M)
    {j : Nat} (hj : j < ctx.groups.length) (h64 : j < 64) :
    M (at_ A (gAt j)) = BitVec.ofNat 64 ctx.groups[j].length := by
  have hf := gAt_free h64 (y := 0) (by decide); rw [Nat.add_zero] at hf
  rw [hM.frame _ (ctx_free hf.1 hf.2.1 hf.2.2.2.1 hf.2.2.2.2.1), (hctx.groups j hj h64).1, getElem!_pos _ j hj]

/-- A group's byte as the context gave it, where `artContext` keeps the context. -/
theorem group_byte {s1 : PancakeState σ} {A : Word} (hA8 : A.toNat % 8 = 0) {ctx : ArticleSpec.Context}
    (hctx : CtxIn A s1.memaddrs s1.be ctx s1.memory) {M : Word → Word} {B : Bytes} (hM : CtxM s1 A s1.memory B M)
    {j : Nat} (hj : j < ctx.groups.length) (h64 : j < 64) {i : Nat} (hi6 : i < 64) (hi : i < ctx.groups[j].length) :
    memLoadByte M s1.memaddrs s1.be (at_ A (gAt j + 8 + i)) = some ctx.groups[j][i]! := by
  have hfi := gAt_free h64 (y := 8 + i) (by omega)
  rw [← Nat.add_assoc] at hfi
  rw [ctx_byte hA8 hM hfi.2.2.1 hfi.2.1]
  have := (hctx.groups j hj h64).2.2 i hi6 (by rw [getElem!_pos _ j hj]; exact hi)
  rw [getElem!_pos _ j hj] at this; exact this

theorem group_lt {s1 : PancakeState σ} {A : Word} {ctx : ArticleSpec.Context}
    (hctx : CtxIn A s1.memaddrs s1.be ctx s1.memory) {j : Nat} (hj : j < ctx.groups.length) (h64 : j < 64) :
    ctx.groups[j].length < 2 ^ 63 := by
  have := (hctx.groups j hj h64).2.1; rwa [getElem!_pos _ j hj] at this

/-- **Group `x` checked**: its length bounded, it put in the input, not reserved, of the grammar. None before it is
equal; else 0 given back. -/
theorem group_step (o : Oracle σ) {A : Word} {s1 : PancakeState σ} (hA : Area ArticleProg.ofs A s1)
    (hD : ArtDom A s1.memaddrs) (hcode : ArtCode s1.code) (hb0 : s1.memory (at_ A aBroken) = 0)
    {ctx : ArticleSpec.Context}
    (hctx : CtxIn A s1.memaddrs s1.be ctx s1.memory)
    (hgr : ∀ x (hx : x < ctx.groups.length), x < 64 → GOk ctx.groups x → ctx.groups[x].length ≤ 64 →
      ∃ b, DN.News.Abnf.matches? AbnfRules.grammar AbnfRules.depth (ArticleSpec.ruleNamed "newsgroup-name")
        (ctx.groups[x].map BitVec.toNat) = .ok b)
    {L5 : List (String × Value)} (hla : L5.lookup "a" = some A)
    (hfr : ∀ z ∈ ["x", "t", "gl", "gli", "ge", "gg", "y", "u", "i", "same"], Fresh z L5 = true)
    {x : Nat} (hx : x < ctx.groups.length) (hx64 : x < 64) (hpre : GOk ctx.groups x) {B : Bytes}
    {M : Word → Word} (hM : CtxM s1 A s1.memory B M) :
    FragR o (CtxRet A ctx s1.memory) groupB (RunF s1 (("x", BitVec.ofNat 64 x) :: L5) (· = M))
      (fun u => ∃ B' M', RunF s1 (("x", BitVec.ofNat 64 (x + 1)) :: L5) (· = M') u ∧ CtxM s1 A s1.memory B' M' ∧
        GOk ctx.groups (x + 1)) := by
  have hA8 := hA.hA
  let g := ctx.groups[x]
  let N := g.length
  have hg63 : N < 2 ^ 63 := group_lt hctx hx hx64
  let L0 : List (String × Value) := ("x", BitVec.ofNat 64 x) :: L5
  unfold groupB
  -- the group's place and length
  refine fragR_append (xs := [_]) (fragR_of (runF_dec o rfl (fresh_cons (by decide) (hfr "t" (by simp)))
    (v := at_ A (gAt x)) fun u h' => by
      simp only [eval, vals_lookup h'.1.vals (show L0.lookup "a" = some A by
        rw [lookup_cons_ne (by decide)]; exact hla), vals_lookup h'.1.vals (lookup_head _ _ _)]
      rw [DN.News.ArticleRun.at_mul]; unfold gAt; rw [Nat.mul_comm])) ?_
  have hMw : M (at_ A (gAt x)) = BitVec.ofNat 64 N := group_word hctx hM hx hx64
  refine fragR_append (xs := [_]) (fragR_of (runF_dec o rfl
    (fresh_cons (by decide) (fresh_cons (by decide) (hfr "gl" (by simp)))) (v := BitVec.ofNat 64 N) fun u h' => by
      rw [DN.News.ArticleRun.loadA_eval h'.1.memaddrs (DN.News.ArticleListRun.gAt_dom hD hx64)
        (ev_var (vals_lookup h'.1.vals (lookup_head _ _ _))), h'.2, hMw])) ?_
  let Lg : List (String × Value) := ("gl", BitVec.ofNat 64 N) :: ("t", at_ A (gAt x)) :: L0
  have hlg : ∀ z, Fresh z [("gl", BitVec.ofNat 64 N), ("t", at_ A (gAt x)), ("x", BitVec.ofNat 64 x)] = true →
      Lg.lookup z = L5.lookup z := fun z h => DN.News.ArticleFields.lookup_fresh (pre := [_, _, _]) L5 h
  -- the length bounded
  refine fragR_append (xs := [_]) (M := fun u => RunF s1 Lg (· = M) u ∧ N ≤ 64) ?_
    (fragR_pure _ (fun u h => h.2) (lowK_any _ (k := .skip) rfl) fun hN => fragR_conseq ?_ (fun u h => h.1)
      fun _ h => h)
  · exact fragR_conseq (bound_frag o hg63 (by decide) (by decide) (x := "gl") (lo := 0) (hi := 64) rfl
      fun hbd u h => ctx_ret0 (M := u.memory) (by rw [h.2]; exact hM) hb0
        (group_bad hx fun ⟨h3, _⟩ => by have h3' : N ≤ 64 := h3; omega)) (fun _ h => h) fun u h => ⟨h.1, h.2.2⟩
  have hNc : N ≤ ArticleProg.idCap := by have : ArticleProg.idCap = 256 := rfl; omega
  -- the group put in the input
  have hf8 := gAt_free hx64 (y := 8 + 64) (by decide)
  have hfw := gAt_free hx64 (y := 0) (by decide)
  rw [Nat.add_zero] at hfw
  refine fragR_append (ctx_copy o hA (l := Lg) (by rw [hlg _ rfl]; exact hla) (x := "gli") (len := "gl") (p := "t")
    (by decide) (by decide) (by decide) (DN.News.AbnfLeaves.fresh_app (l1 := [_, _, _]) rfl (hfr "gli" (by simp)))
      (B' := g) hNc
    (lookup_head _ _ _) (P := gAt x) (off := 8) rfl
    (Nat.le_trans io_le_X (by omega)) (by omega) hM fun i hi => by
      have := group_byte hA8 hctx hM hx hx64 (i := i) (by omega) hi; rwa [getElem!_pos g i hi] at this) ?_
  refine fragR_exists (lowK_any _ (k := .skip) rfl) fun M1 => fragR_pure _ (fun u h => h.2)
    (lowK_any _ (k := .skip) rfl) fun hM1 => fragR_conseq ?_ (fun u h => h.1) fun _ h => h
  let Lc : List (String × Value) := ("gli", BitVec.ofNat 64 N) :: Lg
  -- the group not reserved
  refine fragR_append (ctx_elem o hA hD hcode (l := Lc)
    ((DN.News.ArticleFields.lookup_fresh (pre := [_, _, _, _]) L5 rfl).trans hla) (rt := "ge") (y := "gl")
    (by decide) (DN.News.AbnfLeaves.fresh_app (l1 := [_, _, _, _]) rfl (hfr "ge" (by simp))) hM1 hNc hb0
    (by rw [lookup_cons_ne (by decide)]; exact lookup_head _ _ _)) ?_
  refine fragR_exists (lowK_any _ (k := .skip) rfl) fun w => fragR_exists (lowK_any _ (k := .skip) rfl) fun M2 =>
    fragR_pure _ (fun u h => h.2) (lowK_any _ (k := .skip) rfl) fun ⟨hM2, hres⟩ =>
      fragR_conseq ?_ (fun u h => h.1) fun _ h => h
  let r := ArticleSpec.reserved (DN.News.ArticleList.elem g 0 g.length ArticleSpec.COMMA)
  let Le : List (String × Value) := ("ge", w) :: Lc
  obtain ⟨bn, hbn⟩ := hgr x hx hx64 hpre hN
  have hwhole : ArticleSpec.grammarSays (ArticleSpec.ruleNamed "newsgroup-name") g = true →
      DN.News.ArticleList.elem g 0 g.length ArticleSpec.COMMA = g := fun hG => elem_whole (group_bytes hbn hG)
  have hla_e : Le.lookup "a" = some A := (DN.News.ArticleFields.lookup_fresh (pre := [_, _, _, _, _]) L5 rfl).trans hla
  refine fragR_append (xs := [_]) (M := fun u => RunF s1 Le (· = M2) u ∧ r = false) ?_
    (fragR_pure _ (fun u h => h.2) (lowK_any _ (k := .skip) rfl) fun hr => fragR_conseq ?_ (fun u h => h.1)
      fun _ h => h)
  · refine fragR_if o (wd_lower 22) (lowKK_ret rfl) (fun k => ⟨k, rfl⟩) (fun u k h => ⟨runF_clock _ _ _ u k h.1, h.2⟩)
      (fun _ _ _ _ hy => nomatch hy) (fun _ _ _ _ hy => nomatch hy) (b := r)
      (fun u h => by
        rw [loadA_eval h.1.memaddrs (artDom_w hD (i := 22) (by decide)) (atA_eval (vals_lookup h.1.vals hla_e)), h.2]
        show some (M2 (at_ A ArticleProg.xElemRes)) = _
        rw [hres, bnat_word])
      (fun h2 => fragR_ret o rfl fun u h => ⟨_, rfl, ctx_ret0 (M := u.memory) (by rw [h.2]; exact hM2) hb0
        (group_bad hx fun ⟨_, h4, h5⟩ => by
          have : r = ArticleSpec.reserved g := by show ArticleSpec.reserved _ = _; rw [hwhole h5]
          rw [this, h4] at h2; exact absurd h2 (by decide))⟩)
      fun h2 => fragR_of (frag_nil o fun u h => ⟨h, h2⟩)
  -- the group of the grammar
  refine fragR_append (ctx_gram o hA hcode (l := Le) hla_e (rt := "gg") (by decide)
    (DN.News.AbnfLeaves.fresh_app (l1 := [_, _, _, _, _]) rfl (hfr "gg" (by simp))) hM2 hNc hb0 nn_used hbn
      (e3 := Syntax.v "gl") rfl
    fun u h => ev_var (vals_lookup h.1.vals (by
      rw [lookup_cons_ne (by decide), lookup_cons_ne (by decide)]; exact lookup_head _ _ _))) ?_
  refine fragR_exists (lowK_any _ (k := .skip) rfl) fun M3 => fragR_pure _ (fun u h => h.2)
    (lowK_any _ (k := .skip) rfl) fun hM3 => fragR_conseq ?_ (fun u h => h.1) fun _ h => h
  let Gn := ArticleSpec.grammarSays (AbnfProg.ruleIndex "newsgroup-name") g
  let L7 : List (String × Value) := ("gg", bw Gn) :: Le
  refine fragR_append (xs := [_]) (M := fun u => RunF s1 L7 (· = M3) u ∧ Gn = true) ?_
    (fragR_pure _ (fun u h => h.2) (lowK_any _ (k := .skip) rfl) fun hG => fragR_conseq ?_ (fun u h => h.1)
      fun _ h => h)
  · exact gram_check o (lookup_head _ _ _) fun hGf u h => ctx_ret0 (M := u.memory) (by rw [h.2]; exact hM3) hb0
      (group_bad hx fun ⟨_, _, h5⟩ => by
        have hGt : Gn = true := by show ArticleSpec.grammarSays _ _ = _; rw [nn_rule]; exact h5
        rw [hGf] at hGt; exact absurd hGt (by decide))
  -- none before it equal
  have hla7 : L7.lookup "a" = some A := (DN.News.ArticleFields.lookup_fresh (pre := [_, _, _, _, _, _]) L5 rfl).trans
    hla
  have hf7 : ∀ z ∈ ["y", "u", "i", "same"], Fresh z L7 = true := fun z hz =>
    DN.News.AbnfLeaves.fresh_app (l1 := [_, _, _, _, _, _])
      (by simp only [List.mem_cons, List.mem_nil_iff, or_false] at hz; rcases hz with rfl | rfl | rfl | rfl <;> rfl)
      (hfr z (by simp only [List.mem_cons, List.mem_nil_iff, or_false] at hz; rcases hz with rfl | rfl | rfl | rfl <;>
                  decide))
  refine fragR_append (xs := [_]) (fragR_of (runF_dec o rfl (hf7 "y" (by simp)) (v := BitVec.ofNat 64 0)
    fun _ _ => rfl)) ?_
  have hlx : ∀ y, (("y", BitVec.ofNat 64 y) :: L7).lookup "x" = some (BitVec.ofNat 64 x) := fun _ => rfl
  let DI : Assn σ := fun u => ∃ y, y ≤ x ∧ (∀ y', y' < y → ctx.groups[y']! ≠ g) ∧
    RunF s1 (("y", BitVec.ofNat 64 y) :: L7) (· = M3) u
  have hcy : ∀ u y, y ≤ x → RunF s1 (("y", BitVec.ofNat 64 y) :: L7) (· = M3) u →
      eval u (.cmp .less (.var "y") (.var "x")) = some (bw (decide (y < x))) := fun u y hy h =>
    FramerCode.eval_lt (by omega) (by omega) (ev_var (vals_lookup h.1.vals rfl)) (ev_var (vals_lookup h.1.vals (hlx y)))
  have hw3 : ∀ j (hj : j < ctx.groups.length), j < 64 → M3 (at_ A (gAt j)) = BitVec.ofNat 64 ctx.groups[j].length :=
    fun j hj h64 => group_word hctx hM3 hj h64
  have hb3 : ∀ j (hj : j < ctx.groups.length), j < 64 → ∀ i, i < 64 → i < ctx.groups[j].length →
      memLoadByte M3 s1.memaddrs s1.be (at_ A (gAt j + 8 + i)) = some ctx.groups[j][i]! :=
    fun j hj h64 i hi6 hi => group_byte hA8 hctx hM3 hj h64 hi6 hi
  have hl64 : ∀ j (hj : j < ctx.groups.length), j < 64 → ctx.groups[j].length < 2 ^ 63 :=
    fun j hj h64 => group_lt hctx hj h64
  have hgl7 : L7.lookup "gl" = some (BitVec.ofNat 64 ctx.groups[x].length) := rfl
  have ht7 : L7.lookup "t" = some (at_ A (gAt x)) := rfl
  have lowD : LowKK dupB := lowK_any _ (k := .skip) rfl
  refine fragR_append (xs := [_]) (fragR_conseq (fragR_while o rfl lowD (I := DI)
    (fun u k ⟨y, h1, h2, h⟩ => ⟨y, h1, h2, runF_clock _ _ _ u k h⟩)
    (fun u z w ⟨y, h1, h2, h⟩ hz => by
      have hz' : z = "u" := by simpa [dupB, declared, ifs, inc] using hz
      subst hz'; exact ⟨y, h1, h2, runF_restore h (fresh_cons (by decide) (hf7 "u" (by simp))) w⟩)
    (fun u ⟨y, h1, _, h⟩ => ⟨_, hcy u y h1 h⟩) ?_)
    (fun u h => ⟨0, Nat.zero_le _, fun _ h => absurd h (Nat.not_lt_zero _), h⟩) fun _ h => h) ?_
  · refine fragR_conseq (P0 := fun u => ∃ y, (y < x ∧ (∀ y', y' < y → ctx.groups[y']! ≠ g)) ∧
      RunF s1 (("y", BitVec.ofNat 64 y) :: L7) (· = M3) u) (fragR_exists lowD fun y => ?_)
      (fun u ⟨⟨y, h1, h2, h⟩, hne⟩ => ⟨y, ⟨by rw [hcy u y h1 h] at hne; exact of_decide_eq_true (bw_ne0 hne), h2⟩, h⟩)
      fun _ h => h
    refine fragR_pure _ (fun u h => h.1) lowD fun ⟨hy, hpy⟩ =>
      fragR_conseq (P0 := RunF s1 (("y", BitVec.ofNat 64 y) :: L7) (· = M3)) ?_ (fun u h => h.2) fun _ h => h
    refine fragR_conseq (dup_step o hD hM3 hb0 hx hN (L := L7) hla7 hgl7 ht7 (hf7 "u" (by simp)) (hf7 "i" (by simp))
      (hf7 "same" (by simp)) (hf7 "y" (by simp)) hw3 hb3 hl64 hx64 hy) (fun _ h => h)
      fun u ⟨h, hne⟩ => ⟨y + 1, by omega, fun y' hy' => ?_,
        runF_mono h (fun q hq => List.mem_cons_of_mem _ hq) fun _ e => e⟩
    by_cases e : y' = y
    · subst e; rw [getElem!_pos _ y' (by omega)]; exact hne
    · exact hpy y' (by omega)
  -- the next group
  have hyx : ∀ u y, y ≤ x → RunF s1 (("y", BitVec.ofNat 64 y) :: L7) (· = M3) u →
      eval u (.cmp .less (.var "y") (.var "x")) = some 0 → y = x := fun u y h1 h h0 => by
    rw [hcy u y h1 h] at h0; have := of_decide_eq_false (bw_eq0 h0); omega
  refine fragR_pure (∀ y', y' < x → ctx.groups[y']! ≠ g)
    (fun u ⟨⟨y, h1, h2, h⟩, h0⟩ => by obtain rfl := hyx u y h1 h h0; exact h2) (lowK_any _ (k := .skip) rfl)
    fun hall => fragR_conseq (P0 := RunF s1 (("y", BitVec.ofNat 64 x) :: L7) (· = M3)) ?_
      (fun u ⟨⟨y, h1, h2, h⟩, h0⟩ => by obtain rfl := hyx u y h1 h h0; exact h) fun _ h => h
  refine fragR_of (frag_conseq (runF_set o rfl (x := "x") (hlx x) (v := BitVec.ofNat 64 (x + 1))
    fun u h => DN.News.AbnfComment.ev_inc (vals_lookup h.1.vals (hlx x))) (fun _ h => h)
    fun u h => ⟨g, M3, runF_mono h (fun q hq => ?_) fun _ e => e, hM3, fun x' hx' hlt => ?_⟩)
  · rcases List.mem_cons.1 hq with rfl | hq
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (mem_without (List.mem_append_right (as := [("y", BitVec.ofNat 64 x),
        ("gg", bw Gn), ("ge", w), ("gli", BitVec.ofNat 64 N), ("gl", BitVec.ofNat 64 N), ("t", at_ A (gAt x)),
        ("x", BitVec.ofNat 64 x)]) hq) (DN.News.ScanRun.fresh_ne (hfr "x" (by simp)) q hq))
  · by_cases e : x' = x
    · subst e
      have hGt : ArticleSpec.grammarSays (ArticleSpec.ruleNamed "newsgroup-name") g = true := hG
      have hres' : ArticleSpec.reserved g = false := by
        have : r = ArticleSpec.reserved g := by show ArticleSpec.reserved _ = _; rw [hwhole hGt]
        rw [← this]; exact hr
      exact ⟨hN, hres', hGt, fun y hy => by have := hall y hy; rwa [getElem!_pos _ y (by omega)] at this⟩
    · exact hpre x' hx' (by omega)

/-- **`artContext` answers whether the context fits** (`Context.ok`), if it returns. The grammar's answers on the
identity and the groups are premises. -/
theorem artContext_ok (o : Oracle σ) {A : Word} {s1 : PancakeState σ} (hA : Area ArticleProg.ofs A s1)
    (hD : ArtDom A s1.memaddrs) (hcode : ArtCode s1.code) {B0 : Bytes} (hR : Reads s1 A B0 s1.memory)
    (hall : AllSets A s1.memory) (hb : s1.memory (at_ A aBroken) = 0) {ctx : ArticleSpec.Context}
    (hctx : CtxIn A s1.memaddrs s1.be ctx s1.memory)
    (hid : ctx.identity.length ≤ 200 → ∃ b, DN.News.Abnf.matches? AbnfRules.grammar AbnfRules.depth
      (ArticleSpec.ruleNamed "path-identity") (ctx.identity.map BitVec.toNat) = .ok b)
    (hgr : ∀ x (hx : x < ctx.groups.length), x < 64 → GOk ctx.groups x → ctx.groups[x].length ≤ 64 →
      ∃ b, DN.News.Abnf.matches? AbnfRules.grammar AbnfRules.depth (ArticleSpec.ruleNamed "newsgroup-name")
        (ctx.groups[x].map BitVec.toNat) = .ok b) :
    ∃ body, Lower.lower (gd ArticleProg.artContext) = some body ∧
      SafeR o (fun s => s = s1) body (CtxRet A ctx s1.memory) fun _ => False := by
  have hA8 := hA.hA
  have hic : ArticleProg.idCap = 256 := rfl
  have hil := hctx.idLen; have hil63 := hctx.idLt; have hidb := hctx.id
  have hrl := hctx.randLen; have hrl63 := hctx.randLt; have hrb := hctx.rand
  have hgn := hctx.groupsN; have hgn63 := hctx.groupsLt
  have hM0 : CtxM s1 A s1.memory B0 s1.memory := ⟨hR, hall, fun _ _ => rfl⟩
  refine body_of ?_
  show FragR o _ (guardL ArticleProg.artContext.body) _ _
  rw [artContext_g, List.append_assoc, List.append_assoc, List.append_assoc]
  obtain ⟨EA, hEA⟩ := DN.News.AbnfSets.atOff_lower ArticleProg.ofs
  refine fragR_conseq (P0 := RunF s1 [] (· = s1.memory)) ?_ (entry_run (l := []) (fun q hq => nomatch hq) rfl)
    fun _ h => h
  -- the identity's length
  let L := ctx.identity.length
  refine fragR_append (M := fun u => RunF s1 [("il", BitVec.ofNat 64 L), ("a", A)] (· = s1.memory) u ∧ L ≤ 200) ?_
    (fragR_pure _ (fun u h => h.2) (lowKK_append copyI_low (lowKK_append gram_low (lowKK_append rand_low groups_low)))
      fun hL => fragR_conseq ?_ (fun u h => h.1) fun _ h => h)
  · unfold ctxHead
    refine fragR_append (xs := [_]) (fragR_of (runF_dec o hEA rfl (v := A) fun u h =>
      DN.News.AbnfSets.areaAt_eval hA h.1.base hEA)) ?_
    refine fragR_append (xs := [_]) (fragR_of (runF_dec o (wd_lower 6) rfl (v := BitVec.ofNat 64 L) fun u h => by
      rw [loadA_eval h.1.memaddrs (artDom_w hD (i := 6) (by decide)) (atA_eval (vals_lookup h.1.vals rfl)), h.2]
      exact congrArg some hil)) ?_
    exact fragR_conseq (bound_frag o hil63 (by decide) (by decide) (x := "il") (lo := 0) (hi := 200) rfl
      fun hbd u h => ctx_ret0 (M := u.memory) (by rw [h.2]; exact hM0) hb
        (Bool.eq_false_iff.2 fun hok => by have := ok_idLen hok; omega)) (fun _ h => h) fun u h => ⟨h.1, h.2.2⟩
  -- the identity put in the input
  have hLc : L ≤ ArticleProg.idCap := by omega
  have lowR := lowKK_append gram_low (lowKK_append rand_low groups_low)
  refine fragR_append (ctx_copy o hA (l := [("il", BitVec.ofNat 64 L), ("a", A)]) rfl (x := "ili") (len := "il")
    (p := "a") (by decide) (by decide) (by decide) rfl (B' := ctx.identity) hLc rfl (P := 0) (off := ArticleProg.xId)
    (by rw [DN.News.ScanRun.at_zero]; rfl)
    (by rw [Nat.zero_add]; exact Nat.le_trans io_le_X (by rw [X_val, DN.News.ArticleAdded.xId_eq]; decide))
    (by rw [Nat.zero_add, DN.News.ArticleAdded.xId_eq]; omega) hM0 fun i hi => by
      rw [Nat.zero_add]; have := hidb i (by omega) hi; rw [getElem!_pos _ i hi] at this; exact this) ?_
  refine fragR_exists lowR fun M1 => fragR_pure _ (fun u h => h.2) lowR fun hM1 =>
    fragR_conseq ?_ (fun u h => h.1) fun _ h => h
  -- the identity of the grammar
  obtain ⟨b1, hb1⟩ := hid hL
  unfold ctxGram
  rw [List.append_assoc]
  have lowR2 : LowKK ([ifs (Syntax.eEq (Syntax.v "gi") (Syntax.n 0)) [.ret (Syntax.n 0)]] ++ (ctxRand ++ ctxGroups)) :=
    lowKK_append (lowK_any _ (k := .skip) rfl) (lowKK_append rand_low groups_low)
  refine fragR_append (ctx_gram o hA hcode (l := [("ili", BitVec.ofNat 64 L), ("il", BitVec.ofNat 64 L), ("a", A)])
    rfl (rt := "gi") (by decide) rfl hM1 hLc hb pid_used hb1 (e3 := Syntax.v "il") rfl
    fun u h => ev_var (vals_lookup h.1.vals rfl)) ?_
  refine fragR_exists lowR2 fun M2 => fragR_pure _ (fun u h => h.2) lowR2 fun hM2 =>
    fragR_conseq ?_ (fun u h => h.1) fun _ h => h
  let G := ArticleSpec.grammarSays (AbnfProg.ruleIndex "path-identity") ctx.identity
  refine fragR_append (M := fun u => RunF s1 [("gi", bw G), ("ili", BitVec.ofNat 64 L), ("il", BitVec.ofNat 64 L),
    ("a", A)] (· = M2) u ∧ G = true) ?_
    (fragR_pure _ (fun u h => h.2) (lowKK_append rand_low groups_low) fun hG =>
      fragR_conseq ?_ (fun u h => h.1) fun _ h => h)
  · exact gram_check o (lookup_head _ _ _) fun hG u h => ctx_ret0 (M := u.memory) (by rw [h.2]; exact hM2) hb
      (Bool.eq_false_iff.2 fun hok => by
        have hGt : G = true := by show ArticleSpec.grammarSays _ _ = _; rw [pid_rule]; exact ok_id hok
        rw [hG] at hGt; exact absurd hGt (by decide))
  -- the random value
  let RL := ctx.random.length
  let L3 : List (String × Value) := [("gi", bw G), ("ili", BitVec.ofNat 64 L), ("il", BitVec.ofNat 64 L), ("a", A)]
  unfold ctxRand
  have lowJ : LowKK (randJ ++ ctxGroups) := lowKK_append (lowK_any _ (k := .skip) rfl) groups_low
  refine fragR_append (xs := [_]) (fragR_of (runF_dec o (wd_lower 7) rfl (v := BitVec.ofNat 64 RL) fun u h => by
    rw [loadA_eval h.1.memaddrs (artDom_w hD (i := 7) (by decide)) (atA_eval (vals_lookup h.1.vals rfl)), h.2]
    exact congrArg some ((ctx_word hM2 (i := 7) (by decide)).trans hrl))) ?_
  refine fragR_append (xs := [_]) (M := fun u => RunF s1 (("rl", BitVec.ofNat 64 RL) :: L3) (· = M2) u ∧
    1 ≤ RL ∧ RL ≤ 16) ?_ (fragR_pure _ (fun u h => h.2) lowJ fun hRL =>
      fragR_conseq ?_ (fun u h => h.1) fun _ h => h)
  · exact bound_frag o hrl63 (by decide) (by decide) (x := "rl") (lo := 1) (hi := 16) rfl
      fun hbd u h => ctx_ret0 (M := u.memory) (by rw [h.2]; exact hM2) hb
        (Bool.eq_false_iff.2 fun hok => by have := ok_rand hok; omega)
  -- each byte of it a hexadecimal digit
  let L4 : List (String × Value) := ("rl", BitVec.ofNat 64 RL) :: L3
  refine fragR_append (xs := [_]) (fragR_of (runF_dec o rfl rfl (v := BitVec.ofNat 64 0) fun _ _ => rfl)) ?_
  let IJ : Assn σ := fun u => ∃ j, j ≤ RL ∧ (∀ j', j' < j → ArticleSpec.isHexDigit ctx.random[j']! = true) ∧
    RunF s1 (("j", BitVec.ofNat 64 j) :: L4) (· = M2) u
  have hcondJ : ∀ u j, j ≤ RL → RunF s1 (("j", BitVec.ofNat 64 j) :: L4) (· = M2) u →
      eval u (.cmp .less (.var "j") (.var "rl")) = some (bw (decide (j < RL))) := fun u j hj h =>
    FramerCode.eval_lt (by omega) hrl63 (ev_var (vals_lookup h.1.vals rfl)) (ev_var (vals_lookup h.1.vals rfl))
  have lowB : LowKK randB := lowK_any _ (k := .skip) rfl
  refine fragR_append (xs := [_]) (fragR_conseq (fragR_while o rfl lowB (I := IJ)
    (fun u k ⟨j, h1, h2, h⟩ => ⟨j, h1, h2, runF_clock _ _ _ u k h⟩)
    (fun u y w ⟨j, h1, h2, h⟩ hy => by
      have hy' : y = "b" := by simpa [randB, declared, kept, inc] using hy
      subst hy'; exact ⟨j, h1, h2, runF_restore h rfl w⟩)
    (fun u ⟨j, h1, _, h⟩ => ⟨_, hcondJ u j h1 h⟩) ?_)
    (fun u h => ⟨0, Nat.zero_le _, fun _ h => absurd h (Nat.not_lt_zero _), h⟩) fun _ h => h) ?_
  · refine fragR_conseq (P0 := fun u => ∃ j, (j < RL ∧ (∀ j', j' < j → ArticleSpec.isHexDigit ctx.random[j']! = true)) ∧
      RunF s1 (("j", BitVec.ofNat 64 j) :: L4) (· = M2) u) (fragR_exists lowB fun j => ?_)
      (fun u ⟨⟨j, h1, h2, h⟩, hne⟩ => ⟨j, ⟨by rw [hcondJ u j h1 h] at hne; exact of_decide_eq_true (bw_ne0 hne), h2⟩,
        h⟩)
      fun _ h => h
    refine fragR_pure _ (fun u h => h.1) lowB fun ⟨hj, hpre⟩ =>
      fragR_conseq (P0 := RunF s1 (("j", BitVec.ofNat 64 j) :: L4) (· = M2)) ?_ (fun u h => h.2) fun _ h => h
    have hRL' : RL ≤ ArticleProg.randCap := by have : ArticleProg.randCap = 32 := rfl; omega
    let c := ctx.random[j]!
    refine fragR_append (xs := [_]) (fragR_of (kept_frag o (by decide) (runF_clock _ _ _)
      fun u h => ⟨j, vals_lookup h.1.vals rfl, by have : ArticleProg.randCap = 32 := rfl; omega⟩)) ?_
    refine fragR_append (xs := [_]) (fragR_of (runF_dec o rfl rfl (v := BitVec.ofNat 64 c.toNat) fun u h => by
      have ha : eval u (.op .add (.op .add (.var "a") (.const (BitVec.ofNat 64 ArticleProg.xRand))) (.var "j")) =
          some (at_ A (ArticleProg.xRand + j)) := by
        have ea : u.locals "a" = some A := vals_lookup h.1.vals rfl
        have ej : u.locals "j" = some (BitVec.ofNat 64 j) := vals_lookup h.1.vals rfl
        simp only [eval, ea, ej]
        rw [← at_add]; rfl
      refine loadByte_eval ha ?_
      have hg1 : ArticleProg.xGroups ≤ ArticleProg.xRand + j := by
        rw [DN.News.ArticleListRun.xGroups_eq, DN.News.ArticleAdded.xRand_eq]; omega
      have hg2 : ArticleProg.xRand + j < ArticleProg.xElem := by
        rw [DN.News.ArticleListRun.xElem_eq, DN.News.ArticleAdded.xRand_eq]; omega
      rw [h.2, h.1.memaddrs, h.1.be, ctx_byte hA8 hM2 hg1 hg2]
      exact hrb j (by omega) (by omega))) ?_
    refine fragR_if o rfl (lowK_any _ (k := .skip) rfl) (lowKK_ret rfl)
      (Q := IJ) (fun u k ⟨j, h1, h2, h⟩ => ⟨j, h1, h2, runF_clock _ _ _ u k h⟩)
      (fun _ _ _ _ hy => by simp [declared, inc] at hy) (fun _ _ _ _ hy => nomatch hy) (b := ArticleSpec.isHexDigit c)
      (fun u h => by
        have hv : u.locals "b" = some (BitVec.ofNat 64 c.toNat) := vals_lookup h.1.vals rfl
        have hc := c.isLt
        exact FramerCode.eval_or2 (FramerCode.eval_and (FramerCode.eval_le (by decide) (by omega) rfl (ev_var hv))
          (FramerCode.eval_le (by omega) (by decide) (ev_var hv) rfl))
          (FramerCode.eval_and (FramerCode.eval_le (by decide) (by omega) rfl (ev_var hv))
            (FramerCode.eval_le (by omega) (by decide) (ev_var hv) rfl))) (fun hx => ?_) fun hx => ?_
    · refine fragR_of (frag_conseq (runF_set o rfl (x := "j") rfl (v := BitVec.ofNat 64 (j + 1))
        fun u h => DN.News.AbnfComment.ev_inc (vals_lookup h.1.vals rfl)) (fun _ h => h)
          fun u h => ⟨j + 1, by omega, fun j' hj' => ?_, runF_mono h (fun q hq => by
            rcases List.mem_cons.1 hq with rfl | hq
            · exact List.mem_cons_self
            · refine List.mem_cons_of_mem _ (mem_without (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hq)) ?_)
              simp only [L4, L3, List.mem_cons, List.mem_nil_iff, or_false] at hq
              rcases hq with rfl | rfl | rfl | rfl | rfl <;> simp) fun _ e => e⟩)
      by_cases e : j' = j
      · subst e; exact hx
      · exact hpre j' (by omega)
    · exact fragR_ret o rfl fun u h => ⟨_, rfl, ctx_ret0 (M := u.memory) (by rw [h.2]; exact hM2) hb
        (Bool.eq_false_iff.2 fun hok => by
          have hall := ok_hex hok
          have hmem : c ∈ ctx.random := by
            show ctx.random[j]! ∈ ctx.random
            rw [getElem!_pos _ j hj]; exact List.getElem_mem hj
          have := List.all_eq_true.1 hall c hmem
          rw [hx] at this; exact absurd this (by decide))⟩
  have hjRL : ∀ u j, j ≤ RL → RunF s1 (("j", BitVec.ofNat 64 j) :: L4) (· = M2) u →
      eval u (.cmp .less (.var "j") (.var "rl")) = some 0 → j = RL := fun u j h1 h h0 => by
    rw [hcondJ u j h1 h] at h0; have := of_decide_eq_false (bw_eq0 h0); omega
  refine fragR_pure (∀ j', j' < RL → ArticleSpec.isHexDigit ctx.random[j']! = true)
    (fun u ⟨⟨j, h1, h2, h⟩, h0⟩ => by obtain rfl := hjRL u j h1 h h0; exact h2) groups_low fun hHex =>
      fragR_conseq (P0 := RunF s1 (("j", BitVec.ofNat 64 RL) :: L4) (· = M2)) ?_
        (fun u ⟨⟨j, h1, h2, h⟩, h0⟩ => by obtain rfl := hjRL u j h1 h h0; exact h) fun _ h => h
  have hHexAll : ctx.random.all ArticleSpec.isHexDigit = true := List.all_eq_true.2 fun c hc => by
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hc
    have := hHex i hi; rw [getElem!_pos _ i hi] at this; exact this
  -- the groups
  let GN := ctx.groups.length
  let L5 : List (String × Value) := ("gn", BitVec.ofNat 64 GN) :: ("j", BitVec.ofNat 64 RL) :: L4
  unfold ctxGroups
  refine fragR_append (xs := [_]) (fragR_of (runF_dec o (wd_lower 8) rfl (v := BitVec.ofNat 64 GN) fun u h => by
    rw [loadA_eval h.1.memaddrs (artDom_w hD (i := 8) (by decide)) (atA_eval (vals_lookup h.1.vals rfl)), h.2]
    exact congrArg some ((ctx_word hM2 (i := 8) (by decide)).trans hgn))) ?_
  have lowX : LowKK groupsX := lowK_any _ (k := .skip) rfl
  refine fragR_append (xs := [_]) (M := fun u => RunF s1 L5 (· = M2) u ∧ GN ≤ 64) ?_
    (fragR_pure _ (fun u h => h.2) lowX fun hGN => fragR_conseq ?_ (fun u h => h.1) fun _ h => h)
  · exact fragR_conseq (bound_frag o hgn63 (by decide) (by decide) (x := "gn") (lo := 0) (hi := 64) rfl
      fun hbd u h => ctx_ret0 (M := u.memory) (by rw [h.2]; exact hM2) hb
        (Bool.eq_false_iff.2 fun hok => by have := ok_groupsLen hok; omega)) (fun _ h => h) fun u h => ⟨h.1, h.2.2⟩
  refine fragR_append (xs := [_]) (fragR_of (runF_dec o rfl rfl (v := BitVec.ofNat 64 0) fun _ _ => rfl)) ?_
  let GI : Assn σ := fun u => ∃ x B M, x ≤ GN ∧ GOk ctx.groups x ∧
    RunF s1 (("x", BitVec.ofNat 64 x) :: L5) (· = M) u ∧ CtxM s1 A s1.memory B M
  have hcx : ∀ u x M, x ≤ GN → RunF s1 (("x", BitVec.ofNat 64 x) :: L5) (· = M) u →
      eval u (.cmp .less (.var "x") (.var "gn")) = some (bw (decide (x < GN))) := fun u x M hx h =>
    FramerCode.eval_lt (by omega) (by omega) (ev_var (vals_lookup h.1.vals rfl)) (ev_var (vals_lookup h.1.vals rfl))
  have lowG : LowKK groupB := lowK_any _ (k := .skip) rfl
  have hfr5 : ∀ z ∈ ["x", "t", "gl", "gli", "ge", "gg", "y", "u", "i", "same"], Fresh z L5 = true := fun z hz => by
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  refine fragR_append (xs := [_]) (fragR_conseq (fragR_while o rfl lowG (I := GI)
    (fun u k ⟨x, B, M, h1, h2, h, hM⟩ => ⟨x, B, M, h1, h2, runF_clock _ _ _ u k h, hM⟩)
    (fun u z w ⟨x, B, M, h1, h2, h, hM⟩ hz => by
      have hz' : z = "t" ∨ z = "gl" ∨ z = "gli" ∨ z = "ge" ∨ z = "gg" ∨ z = "y" := by
        simpa [groupB, copyS, declared, ifs, inc, kept, guardS] using hz
      refine ⟨x, B, M, h1, h2, runF_restore h ?_ w, hM⟩
      rcases hz' with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl)
    (fun u ⟨x, _, M, h1, _, h, _⟩ => ⟨_, hcx u x M h1 h⟩) ?_)
    (fun u h => ⟨0, _, M2, Nat.zero_le _, fun x' _ h => absurd h (Nat.not_lt_zero _), h, hM2⟩) fun _ h => h) ?_
  · refine fragR_conseq (P0 := fun u => ∃ t : Nat × Bytes × (Word → Word), (t.1 < GN ∧ GOk ctx.groups t.1 ∧
      CtxM s1 A s1.memory t.2.1 t.2.2) ∧ RunF s1 (("x", BitVec.ofNat 64 t.1) :: L5) (· = t.2.2) u)
      (fragR_exists lowG fun t => ?_) (fun u ⟨⟨x, B, M, h1, h2, h, hM⟩, hne⟩ => ⟨(x, B, M),
        ⟨by rw [hcx u x M h1 h] at hne; exact of_decide_eq_true (bw_ne0 hne), h2, hM⟩, h⟩) fun _ h => h
    obtain ⟨x, B, M⟩ := t
    refine fragR_pure _ (fun u h => h.1) lowG fun ⟨hx, hpre, hM⟩ =>
      fragR_conseq (P0 := RunF s1 (("x", BitVec.ofNat 64 x) :: L5) (· = M)) ?_ (fun u h => h.2) fun _ h => h
    exact fragR_conseq (group_step o hA hD hcode hb hctx hgr (L5 := L5) rfl hfr5 hx (by omega) hpre hM) (fun _ h => h)
      fun u ⟨B', M', h, hM', hok'⟩ => ⟨x + 1, B', M', by omega, hok', h, hM'⟩
  -- the context fits
  refine fragR_ret o rfl fun u ⟨⟨x, B, M, h1, h2, h, hM⟩, h0⟩ => ⟨_, rfl, ?_⟩
  rw [hcx u x M h1 h] at h0
  have hxN : x = GN := by have := of_decide_eq_false (bw_eq0 h0); omega
  subst hxN
  obtain ⟨hall', hdup⟩ := gok_all h2
  have hok : ctx.ok = true := (ok_iff ctx).2 ⟨hG, hL, hRL.1, hRL.2, hHexAll, hctx.seq, hctx.run, hctx.conn, hGN, hdup,
    hall'⟩
  rw [h.2]
  exact ⟨by rw [hok]; rfl, (hM.frame _ broken_free).trans hb, hM.frame, hM.sets⟩

/-! ## The premises can hold -/

theorem nameByte_witness : NameByte 97 := by unfold NameByte; decide

/-- The empty context: it does not fit, having no random value. One that fits needs the grammar's answers, which the
kernels cannot work out. -/
theorem ctxIn_witness : CtxIn 0 (fun _ => true) false
    { groups := [], identity := [], wall := 0, seq := 0, random := [], run := 0, conn := 0 } (fun _ => 0) :=
  ⟨rfl, by decide, fun _ _ h => absurd h (Nat.not_lt_zero _), rfl, by decide, fun _ _ h => absurd h (Nat.not_lt_zero _),
    rfl, by decide, fun _ h => absurd h (Nat.not_lt_zero _), by decide, by decide, by decide⟩

theorem ctxM_witness : CtxM (bareState ()) 0 DN.News.AbnfMain.baseMem [] DN.News.AbnfMain.baseMem :=
  ⟨DN.News.AbnfMain.base_witness.2.2, DN.News.AbnfMain.base_witness.1, fun _ _ => rfl⟩

theorem gok_witness : GOk [] 0 := fun _ h => absurd h (Nat.not_lt_zero _)

end DN.News.ArticleContext
