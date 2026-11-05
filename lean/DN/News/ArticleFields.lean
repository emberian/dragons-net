-- SPDX-License-Identifier: AGPL-3.0-or-later
import DN.News.ArticleAdded

/-!
# DN.News.ArticleFields

`artCheck`'s loop over the fields. Each field is checked as `ArticleSpec.fieldRefusal` checks it. The loop keeps
each entry's first field and the first fields of the refusals checked after the loop.
-/

namespace DN.News.ArticleFields

open DN.News.ArticleSpec (Bytes Field)
open DN.News.ArticleLines (seg Lines cont groups fieldOf segs)
open DN.Compiler DN.Compiler.Wp DN.Compiler.WpRet DN.Compiler.Frag DN.News.AbnfProg
open DN.News.AbnfSets DN.News.FunRun DN.News.AbnfLeaves DN.News.ArticleRun
open DN.News.ScanRun (at_ vals_lookup Fresh)
open DN.News.ArticleProg (artMax guardL guardS ifs wd)
open DN.News.FramerCode (bw ev_var)
open DN.News.ArticleTables (esP allNames esP_size esP_mem)

variable {σ : Type}

/-! ## What the rules make of a field, by its entry -/

/-- The flags of a name, a bit each, in the order `artCheck` tests them. -/
def flagList (r : ArticleSpec.Rules) (s : String) : List Bool :=
  [ArticleProg.isIn r.injected s, ArticleProg.isIn r.traced s, ArticleProg.isIn r.deprecated s,
   ArticleProg.isIn r.notOffered s, ArticleProg.isIn r.once s, ArticleProg.isIn ArticleSpec.idFields s,
   ArticleProg.isIn ArticleProg.dateFields s, ArticleProg.lowerS s == "received"]

theorem flagsOf_fold (r : ArticleSpec.Rules) (s : String) :
    ArticleProg.flagsOf r s = (List.range 8).foldl (DN.News.AbnfMatch.bitStep fun i => (flagList r s).getD i false) 0 :=
  rfl

/-- **Bit `i` of a name's flags** is its `i`th flag. -/
theorem flagsOf_bit (r : ArticleSpec.Rules) (s : String) (i : Nat) :
    (ArticleProg.flagsOf r s).testBit i = (decide (i < 8) && (flagList r s).getD i false) := by
  rw [flagsOf_fold]; exact (DN.News.AbnfMatch.fold_bits _ 8).2 i

theorem flagsOf_lt (r : ArticleSpec.Rules) (s : String) : ArticleProg.flagsOf r s < 256 := by
  rw [flagsOf_fold]; exact (DN.News.AbnfMatch.fold_bits _ 8).1

theorem any_congr' {α : Type} {p q : α → Bool} : ∀ {l : List α}, (∀ x ∈ l, p x = q x) → l.any p = l.any q
  | [], _ => rfl
  | x :: l, h => by
    rw [List.any_cons, List.any_cons, h x List.mem_cons_self, any_congr' fun y hy => h y (List.mem_cons_of_mem _ hy)]

theorem find?_congr' {α : Type} {p q : α → Bool} : ∀ {l : List α}, (∀ x ∈ l, p x = q x) → l.find? p = l.find? q
  | [], _ => rfl
  | x :: l, h => by
    rw [List.find?_cons, List.find?_cons, h x List.mem_cons_self,
      find?_congr' fun y hy => h y (List.mem_cons_of_mem _ hy)]

/-- **A field of entry `k` is one of a list** the rules read exactly when the entry is, without case. -/
theorem isOne_class {name : Bytes} {k : Nat} (hk : k < esP.length) (hc : DN.News.ArticleRun.classOf esP name = k)
    {l : List String} (hl : ∀ n ∈ l, n ∈ allNames) :
    l.any (ArticleSpec.named name ·) = ArticleProg.isIn l esP[k] := by
  unfold ArticleProg.isIn
  exact any_congr' fun n hn => DN.News.ArticleTables.class_named hk hc (hl n hn)

/-- **A field of no entry is in no list** the rules read. -/
theorem isOne_none {name : Bytes} (hc : DN.News.ArticleRun.classOf esP name = esP.length) {l : List String}
    (hl : ∀ n ∈ l, n ∈ allNames) : l.any (ArticleSpec.named name ·) = false := by
  rw [any_congr' (q := fun _ => false) fun n hn => DN.News.ArticleTables.class_none hc (hl n hn)]
  simp

theorem rules_names : ∀ p ∈ AbnfRules.fieldRules, p.1 ∈ allNames := by
  intro p hp
  have : p.1 ∈ AbnfRules.fieldRules.map (·.1) := List.mem_map_of_mem hp
  simp only [allNames, List.mem_append]
  simp [this]

/-- **A field's rule is its entry's**, or the rule of no entry. -/
theorem ruleOf_class {f : Field} {k : Nat} (hk : k < esP.length) (hc : DN.News.ArticleRun.classOf esP f.name = k) :
    ArticleSpec.ruleOf f = ArticleProg.ruleOfName esP[k] := by
  unfold ArticleSpec.ruleOf ArticleProg.ruleOfName
  rw [find?_congr' fun p hp => DN.News.ArticleTables.class_named hk hc (rules_names p hp)]

theorem ruleOf_none {f : Field} (hc : DN.News.ArticleRun.classOf esP f.name = esP.length) :
    ArticleSpec.ruleOf f = AbnfRules.optionalField := by
  unfold ArticleSpec.ruleOf
  rw [find?_congr' (q := fun _ => false) fun p hp => DN.News.ArticleTables.class_none hc (rules_names p hp),
    List.find?_eq_none.2 fun _ _ => by decide]
  rfl

/-! ## A field's check -/

/-- A refusal's number, from 1 in the order of `Refusal`, as the program returns it. -/
def refNum : ArticleSpec.Refusal → Nat
  | .noHeader => 1 | .noSeparator => 2 | .headerTooLong => 3 | .lineTooLong => 4 | .malformed => 5
  | .injected _ => 6 | .traced _ => 7 | .deprecated _ => 8 | .notOffered _ => 9 | .blankLine _ => 10
  | .badField _ => 11 | .repeated _ => 12 | .missing _ => 13 | .posted => 14 | .longMessageId _ => 15
  | .noSender => 16 | .distributionAll => 17 | .badDate _ => 18 | .dateAhead _ => 19 | .datePast _ => 20
  | .tooManyGroups => 21 | .reservedGroup => 22 | .noKnownGroup => 23

theorem and_two_pow (F i : Nat) : F &&& 2 ^ i = (F.testBit i).toNat * 2 ^ i :=
  Nat.eq_of_testBit_eq fun j => by
    rw [Nat.testBit_and, Nat.testBit_two_pow]
    by_cases hj : i = j
    · subst hj; cases h : F.testBit i <;> simp
    · cases h : F.testBit i <;> simp [hj]

/-- **A flag tested**: bit `i` of the local `fl`, as `artCheck` tests it. -/
theorem bit_eval {u : PancakeState σ} {F : Nat} (hF : F < 2 ^ 64) (hx : u.locals "fl" = some (BitVec.ofNat 64 F))
    {i : Nat} (hi : i < 64) :
    eval u (.cmp .equal (.cmp .equal (.op .and_ (.var "fl") (.const (BitVec.ofNat 64 (2 ^ i))))
      (.const (BitVec.ofNat 64 0))) (.const (BitVec.ofNat 64 0))) = some (bw (F.testBit i)) := by
  have h2 : 2 ^ i < 2 ^ 64 := Nat.pow_lt_pow_right (by decide) hi
  have hp : 0 < 2 ^ i := Nat.two_pow_pos i
  have hand : BitVec.ofNat 64 F &&& BitVec.ofNat 64 (2 ^ i) = BitVec.ofNat 64 ((F.testBit i).toNat * 2 ^ i) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_and, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hF,
      Nat.mod_eq_of_lt h2, and_two_pow]
    cases F.testBit i <;> simp [Nat.mod_eq_of_lt h2]
  simp only [eval, hx, hand]
  cases F.testBit i
  · rw [Bool.toNat_false, Nat.zero_mul, if_pos rfl]; rfl
  · have hne : BitVec.ofNat 64 (true.toNat * 2 ^ i) ≠ 0#64 := fun h => by
      have := congrArg BitVec.toNat h
      simp only [Bool.toNat_true, Nat.one_mul, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h2] at this
      omega
    rw [if_neg hne]; rfl

/-- The program's answer for one field: a refusal's number, or 0. It reads the flags `F`, whether a body line is
blank, and whether the grammar takes the field. -/
def whyOf (F : Nat) (blank gram : Bool) : Nat :=
  if F.testBit 0 then 6 else if F.testBit 1 then 7 else if F.testBit 2 then 8 else if F.testBit 3 then 9
  else if blank then 10 else if !gram then 11 else 0

/-- What `fieldRefusal` answers, as a number: the refusal's, or 0. -/
def fieldNum (f : Field) : Nat := ((ArticleSpec.fieldRefusal ArticleSpec.spec f).map refNum).getD 0

/-- The numbers are those of the program's list of refusals, from one. -/
theorem refNum_refusals : ArticleProg.refusals.map refNum = List.range' 1 23 := rfl

/-- No reason, no refusal. -/
theorem fieldNum_zero {f : Field} (h : fieldNum f = 0) : ArticleSpec.fieldRefusal ArticleSpec.spec f = none := by
  unfold fieldNum at h
  cases e : ArticleSpec.fieldRefusal ArticleSpec.spec f with
  | none => rfl
  | some x => rw [e] at h; cases x <;> simp [refNum] at h

theorem lists_names : (∀ n ∈ ArticleSpec.spec.injected, n ∈ allNames) ∧ (∀ n ∈ ArticleSpec.spec.traced, n ∈ allNames) ∧
    (∀ n ∈ ArticleSpec.spec.deprecated, n ∈ allNames) ∧ (∀ n ∈ ArticleSpec.spec.notOffered, n ∈ allNames) ∧
    (∀ n ∈ ArticleSpec.spec.once, n ∈ allNames) ∧ (∀ n ∈ ArticleSpec.idFields, n ∈ allNames) ∧
    (∀ n ∈ ArticleProg.dateFields, n ∈ allNames) ∧ (∀ n ∈ ArticleProg.readNames, n ∈ allNames) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intro n hn <;> simp only [allNames, List.mem_append] <;> simp [hn]

theorem names_len : ∀ n ∈ allNames, n.length ≤ 64 := by decide +kernel

theorem esP_short : ∀ s ∈ esP, s.length ≤ 64 := fun s h => names_len s (esP_mem h)

/-- **A field of entry `k` is checked as the rules check it.** The blank lines and the grammar are given. -/
theorem fieldNum_class {f : Field} {k : Nat} (hk : k < esP.length) (hc : DN.News.ArticleRun.classOf esP f.name = k)
    {g : Bool} (hg : ArticleSpec.grammarSays (ArticleSpec.ruleOf f) f.text = g) :
    fieldNum f =
      whyOf (ArticleProg.flagsOf ArticleSpec.spec esP[k]) (f.body.any (·.all DN.News.CommandSpec.isWS)) g := by
  obtain ⟨l1, l2, l3, l4, -, -, -, -⟩ := lists_names
  have e1 := isOne_class hk hc l1
  have e2 := isOne_class hk hc l2
  have e3 := isOne_class hk hc l3
  have e4 := isOne_class hk hc l4
  unfold fieldNum ArticleSpec.fieldRefusal ArticleSpec.isOne whyOf
  rw [e1, e2, e3, e4, hg, flagsOf_bit, flagsOf_bit, flagsOf_bit, flagsOf_bit]
  simp only [flagList, List.getD_cons_zero, List.getD_cons_succ, show (0 < 8) = True from eq_true (by decide),
    show (1 < 8) = True from eq_true (by decide), show (2 < 8) = True from eq_true (by decide),
    show (3 < 8) = True from eq_true (by decide), decide_true, Bool.true_and]
  have hb : ArticleSpec.spec.blank = true := rfl
  rw [hb, Bool.true_and]
  cases ArticleProg.isIn ArticleSpec.spec.injected esP[k] <;> cases ArticleProg.isIn ArticleSpec.spec.traced esP[k] <;>
    cases ArticleProg.isIn ArticleSpec.spec.deprecated esP[k] <;>
    cases ArticleProg.isIn ArticleSpec.spec.notOffered esP[k] <;>
    cases f.body.any (·.all DN.News.CommandSpec.isWS) <;> cases g <;> rfl

/-- **A field of no entry** is checked by its blank lines and the rule of no entry alone. -/
theorem fieldNum_none {f : Field} (hc : DN.News.ArticleRun.classOf esP f.name = esP.length) {g : Bool}
    (hg : ArticleSpec.grammarSays (ArticleSpec.ruleOf f) f.text = g) :
    fieldNum f = whyOf 0 (f.body.any (·.all DN.News.CommandSpec.isWS)) g := by
  obtain ⟨l1, l2, l3, l4, -, -, -, -⟩ := lists_names
  unfold fieldNum ArticleSpec.fieldRefusal ArticleSpec.isOne whyOf
  rw [isOne_none hc l1, isOne_none hc l2, isOne_none hc l3, isOne_none hc l4, hg]
  have hb : ArticleSpec.spec.blank = true := rfl
  rw [hb, Bool.true_and]
  cases f.body.any (·.all DN.News.CommandSpec.isWS) <;> cases g <;> rfl

/-- **A field's blank lines** are those `artBlank` reads: the first line past the colon, then the continuations. -/
theorem body_blank {a : Bytes} {sep P e : Nat} {more : List (Nat × Nat)} (h : Lines a P ((P, e) :: more) sep)
    (hK : P + DN.News.ArticleLines.nameLen a P e < e) :
    (fieldOf a ((P, e) :: more.takeWhile (cont a))).body.any (·.all DN.News.CommandSpec.isWS) =
      ((seg a (P + DN.News.ArticleLines.nameLen a P e + 1) e).all DN.News.CommandSpec.isWS ||
        DN.News.ArticleLines.blankL a more) := by
  have hea := (DN.News.ArticleLines.lines_mem h (P, e) List.mem_cons_self).2.2.2.2
  have hnl : (DN.News.ArticleLines.nameAt a (P, e)).length = DN.News.ArticleLines.nameLen a P e := by
    show (seg a P (P + DN.News.ArticleLines.nameLen a P e)).length = _
    rw [DN.News.ArticleLines.seg_length a (by omega) (by omega)]; omega
  simp only [ArticleSpec.Field.body, fieldOf, segs, List.map_cons, List.headD_cons, hnl, List.any_cons,
    DN.News.ArticleScan.seg_drop, DN.News.ArticleLines.blankL, List.any_map]
  rfl

/-! ## The grammar called -/

open DN.News.Abnf DN.News.AbnfMatch DN.News.AbnfGen

theorem gram_field {a : Bytes} {S E : Nat} (hSE : S ≤ E) (hEa : E ≤ a.length) {R : Nat} {b : Bool}
    (h : DN.News.Abnf.matches? AbnfRules.grammar AbnfRules.depth R ((seg a S E).map BitVec.toNat) = .ok b) :
    setOf (Matches AbnfRules.grammar (inputOf (a.take E))
      (.ref R) S) E = ArticleSpec.grammarSays R (seg a S E) := by
  rw [DN.News.ArticleGrammar.gram_says hSE hEa h]
  unfold ArticleSpec.grammarSays; rw [h]

theorem reads_state {s s' : PancakeState σ} (hm : s'.memaddrs = s.memaddrs) (hbe : s'.be = s.be) {A : Word}
    {b : Bytes} {m : Word → Word} : Reads s' A b m ↔ Reads s A b m := by
  constructor <;> intro h
  · exact ⟨by rw [← hm, ← hbe]; exact h.input, h.pows, h.masks, h.classes, by rw [← hm, ← hbe]; exact h.texts⟩
  · exact ⟨by rw [hm, hbe]; exact h.input, h.pows, h.masks, h.classes, by rw [hm, hbe]; exact h.texts⟩

theorem gramRet_state {s s' : PancakeState σ} (hm : s'.memaddrs = s.memaddrs) (hbe : s'.be = s.be) {A : Word}
    {a : Bytes} {R S E : Nat} {m0 : Word → Word} :
    DN.News.ArticleGrammar.GramRet s' A a R S E m0 = DN.News.ArticleGrammar.GramRet s A a R S E m0 := by
  funext v m
  simp only [DN.News.ArticleGrammar.GramRet, DN.News.ArticleGrammar.GramMem, Base, reads_state hm hbe]

theorem mem_artGrammar : gd ArticleProg.artGrammar ∈ ArticleProg.functions ArticleSpec.spec esP .none :=
  List.mem_append_right _ (List.mem_map.2 ⟨ArticleProg.artGrammar, by simp, rfl⟩)

/-- Words past the slots are in none. -/
theorem notInSlot_high {A : Word} {k y : Nat} (hk : k < slots) (hy : ArticleProg.X ≤ y) (hy2 : y < 2 ^ 40) :
    ¬InSlot A k (at_ A y) := by
  rintro ⟨i, hi, e⟩
  have h1 := DN.News.AbnfSets.off_lt hk (8 * i) (by rw [DN.News.AbnfSets.setSize_eq] at hi ⊢; omega)
  have hX := X_eq
  have := DN.News.ScanRun.at_inj (by omega) (by omega) e
  omega

/-- **A call of `artGrammar`**: whether rule `Ru` matches from `S` to `E`. What the leaves read and the sets are kept.
Every word outside the slots but the input's length is kept too. -/
theorem gramCall_frag (o : Oracle σ) {R : Ret} {A : Word} {s0 : PancakeState σ} (hA : Area ArticleProg.ofs A s0)
    (hcode : ArtCode s0.code) {rt : String} (hra : rt ≠ "a") {l : List (String × Value)}
    (hla : l.lookup "a" = some A) (hrt : Fresh rt l = true) {a : Bytes} (hal : a.length ≤ artMax) {M : Word → Word}
    (hR : Reads s0 A a M)
    (hall : AllSets A M) (hb : M (at_ A aBroken) = 0) {Ru S E : Nat} (hRu : Ru ∈ ArticleProg.usedRules)
    (hS : S ≤ inputMax) (hE : E ≤ inputMax) (hEa : E ≤ a.length) {e1 e2 e3 : Syntax.PExpr} {E1 E2 E3 : PancakeExp}
    (he1 : Lower.lowerExp e1 = some E1) (he2 : Lower.lowerExp e2 = some E2) (he3 : Lower.lowerExp e3 = some E3)
    (hv1 : ∀ u, RunF s0 l (· = M) u → eval u E1 = some (BitVec.ofNat 64 Ru))
    (hv2 : ∀ u, RunF s0 l (· = M) u → eval u E2 = some (BitVec.ofNat 64 S))
    (hv3 : ∀ u, RunF s0 l (· = M) u → eval u E3 = some (BitVec.ofNat 64 E)) :
    FragR o R (guardS (.call rt "artGrammar" [e1, e2, e3])) (RunF s0 l (· = M))
      (fun u => ∃ m, RunF s0 ((rt, bw (setOf (Matches AbnfRules.grammar
        (inputOf (a.take E)) (.ref Ru) S) E)) :: l) (· = m) u ∧
        Reads s0 A a m ∧ AllSets A m ∧
        ∀ x, (∀ k, k < slots → ¬InSlot A k x) → x ≠ at_ A aLen → m x = M x) := by
  have hA8 := hA.hA
  have hlen := DN.News.ArticleGrammar.reads_take hR E
  refine fragR_conseq (gcall_frag o hA hcode hra (f := ArticleProg.artGrammar) mem_artGrammar (by decide)
    (F := (· = M)) (args := [E1, E2, E3]) (by simp [Lower.lowerArgs, he1, he2, he3]) hla
    (vs := [BitVec.ofNat 64 Ru, BitVec.ofNat 64 S, BitVec.ofNat 64 E]) rfl
    (fun u h => by simp only [evalArgs, hv1 u h, hv2 u h, hv3 u h])
    (Rf := DN.News.ArticleGrammar.GramRet s0 A a Ru S E)
    (fun s1 hA1 hc hm hbe hloc hF => by
      have := DN.News.ArticleGrammar.artGrammar_ok o hA1 (by rw [hc]; exact hcode)
        (by rw [hF]; exact (reads_state hm hbe).2 hR) (by rw [hF]; exact hall) (by rw [hF]; exact hb) hRu hS hE hEa
        ((hloc "rule").trans rfl) ((hloc "s").trans rfl) ((hloc "e").trans rfl)
      rw [gramRet_state hm hbe] at this; exact this) hrt
    (G := fun w m => (Reads s0 A a m ∧ AllSets A m ∧
        ∀ x, (∀ k, k < slots → ¬InSlot A k x) → x ≠ at_ A aLen → m x = M x) ∧
      w = bw (setOf (Matches AbnfRules.grammar
        (inputOf (a.take E)) (.ref Ru) S) E))
    (fun m m' w hm hr => ?_) ?_) (fun u h => h) fun u ⟨w, h⟩ => ?_
  · obtain ⟨⟨⟨hall', -, hR'⟩, hK⟩, hw⟩ := hr
    subst hm
    have hfr : ∀ x, (∀ k, k < slots → ¬InSlot A k x) → x ≠ at_ A aLen → m' x = m x := fun x h1 h2 => by
      rw [hK x (h1 0 (by have := DN.News.AbnfLayout.slots_two; omega)) fun k _ hk => h1 k hk, upd_ne _ h2]
    refine ⟨⟨⟨fun x hx => ?_, hR'.pows, hR'.masks, hR'.classes, hR'.texts⟩, hall', hfr⟩, hw⟩
    have hin := input_below
    have hal2 := artMax_eq
    have := hR.input x hx
    unfold memLoadByte at this ⊢
    rw [DN.News.ScanRun.align_at hA8] at this ⊢
    rw [hfr _ (fun k hk => notInSlot hk (by have := aInput_eq; omega))
      (DN.News.ScanRun.at_ne (by have := aInput_eq; omega) (by have : aLen = 8 := rfl; omega) (by
        have := aInput_eq; have : aLen = 8 := rfl; omega))]
    exact this
  · intro w m h
    obtain ⟨⟨-, -, hfr⟩, -⟩ := h
    rw [hfr _ (fun k hk => notInSlot hk DN.News.ArticleGrammar.broken_low)
      (DN.News.ScanRun.at_ne (by have : aBroken = 24 := rfl; omega) (by have : aLen = 8 := rfl; omega)
        (by have : aBroken = 24 := rfl; have : aLen = 8 := rfl; omega))]
    exact hb
  · obtain ⟨⟨hR', hall', hfr⟩, hw⟩ := h.2
    subst hw; exact ⟨u.memory, ⟨h.1, rfl⟩, hR', hall', hfr⟩

/-! ## The other calls -/

theorem mem_artBlank : gd ArticleProg.artBlank ∈ ArticleProg.functions ArticleSpec.spec esP .none :=
  List.mem_append_right _ (List.mem_map.2 ⟨ArticleProg.artBlank, by simp, rfl⟩)

theorem mem_artNameAt : gd ArticleProg.artNameAt ∈ ArticleProg.functions ArticleSpec.spec esP .none :=
  List.mem_append_right _ (List.mem_map.2 ⟨ArticleProg.artNameAt, by simp, rfl⟩)

theorem mem_artReceived : gd ArticleProg.artReceived ∈ ArticleProg.functions ArticleSpec.spec esP .none :=
  List.mem_append_right _ (List.mem_map.2 ⟨ArticleProg.artReceived, by simp, rfl⟩)

theorem mem_artDate : gd (ArticleProg.artDate .none) ∈ ArticleProg.functions ArticleSpec.spec esP .none :=
  List.mem_append_right _ (List.mem_map.2 ⟨ArticleProg.artDate .none, by simp, rfl⟩)

/-- **A call of `artBlank`** on a field's start: whether a line of its body is white space alone. -/
theorem blankCall_frag (o : Oracle σ) {R : Ret} {A : Word} {s0 : PancakeState σ} (hA : Area ArticleProg.ofs A s0)
    (hD : ArtDom A s0.memaddrs) (hcode : ArtCode s0.code) {a : Bytes} (hlen : a.length ≤ artMax) {rt : String}
    (hra : rt ≠ "a") {l : List (String × Value)} (hla : l.lookup "a" = some A) (hrt : Fresh rt l = true)
    {m0 : Word → Word} {e1 : Syntax.PExpr} {E1 : PancakeExp} (he1 : Lower.lowerExp e1 = some E1) {SEP P e : Nat}
    {L : List (Nat × Nat)} (hf : DN.News.ArticleLines.FieldAt a SEP P e L)
    (hv1 : ∀ u, RunF s0 l (· = m0) u → eval u E1 = some (BitVec.ofNat 64 P))
    (hin : InputAt m0 s0.memaddrs s0.be A a) (hb : m0 (at_ A aBroken) = 0)
    (hsep : m0 (at_ A ArticleProg.xSep) = BitVec.ofNat 64 SEP) :
    FragR o R (guardS (.call rt "artBlank" [e1])) (RunF s0 l (· = m0))
      (RunF s0 ((rt, bw ((seg a (P + DN.News.ArticleLines.nameLen a P e + 1) e).all DN.News.CommandSpec.isWS ||
        DN.News.ArticleLines.blankL a L)) :: l) (· = fieldMem A (DN.News.ArticleLines.nameLen a P e) e m0)) := by
  refine fragR_conseq (gcall_frag o hA hcode hra (f := ArticleProg.artBlank) mem_artBlank (by decide)
    (F := (· = m0)) (args := [E1]) (by simp [Lower.lowerArgs, he1]) hla (vs := [BitVec.ofNat 64 P]) rfl
    (fun u h => by simp only [evalArgs, hv1 u h])
    (Rf := BlankRet A (DN.News.ArticleLines.nameLen a P e) e
      ((seg a (P + DN.News.ArticleLines.nameLen a P e + 1) e).all DN.News.CommandSpec.isWS ||
        DN.News.ArticleLines.blankL a L))
    (fun s1 hA1 hc hm hbe hloc hF1 => artBlank_ok o hA1 (by rw [hm]; exact hD) (by rw [hc]; exact hcode) hlen
      (by rw [hm, hbe, hF1]; exact hin) (by rw [hF1]; exact hb) hf (by rw [hF1]; exact hsep) ((hloc "p").trans rfl))
    hrt (G := fun v m => m = fieldMem A (DN.News.ArticleLines.nameLen a P e) e m0 ∧
      v = bw ((seg a (P + DN.News.ArticleLines.nameLen a P e + 1) e).all DN.News.CommandSpec.isWS ||
        DN.News.ArticleLines.blankL a L))
    (fun m m' v hm ⟨e1, e2⟩ => ⟨by rw [e1, hm], e2⟩)
    fun v m h => by rw [h.1]; exact (fieldMem_keep hA.hA hlen hin hb _ _).2) (fun u h => h) fun u ⟨v, h⟩ => ?_
  obtain ⟨hm, hv⟩ := h.2
  subst hv; exact ⟨h.1, hm⟩

/-- **A call of `artNameAt`** on a field's start: its name in `xName`, its length in `xNameLen`. -/
theorem nameCall_frag (o : Oracle σ) {R : Ret} {A : Word} {s0 : PancakeState σ} (hA : Area ArticleProg.ofs A s0)
    (hD : ArtDom A s0.memaddrs) (hcode : ArtCode s0.code) {a : Bytes} (hlen : a.length ≤ artMax) {rt : String}
    (hra : rt ≠ "a") {l : List (String × Value)} (hla : l.lookup "a" = some A) (hrt : Fresh rt l = true)
    {m0 : Word → Word} {e1 : Syntax.PExpr} {E1 : PancakeExp} (he1 : Lower.lowerExp e1 = some E1) {SEP P e : Nat}
    {L : List (Nat × Nat)} (hf : DN.News.ArticleLines.FieldAt a SEP P e L)
    (hK : DN.News.ArticleLines.nameLen a P e < ArticleProg.nameCap)
    (hv1 : ∀ u, RunF s0 l (· = m0) u → eval u E1 = some (BitVec.ofNat 64 P))
    (hin : InputAt m0 s0.memaddrs s0.be A a) (hb : m0 (at_ A aBroken) = 0)
    (hsep : m0 (at_ A ArticleProg.xSep) = BitVec.ofNat 64 SEP) :
    FragR o R (guardS (.call rt "artNameAt" [e1])) (RunF s0 l (· = m0))
      (RunF s0 ((rt, 0) :: l) (· = nameMem A s0.be (seg a P (P + DN.News.ArticleLines.nameLen a P e))
        (DN.News.ArticleLines.nameLen a P e) e m0)) := by
  refine fragR_conseq (gcall_frag o hA hcode hra (f := ArticleProg.artNameAt) mem_artNameAt (by decide)
    (F := (· = m0)) (args := [E1]) (by simp [Lower.lowerArgs, he1]) hla (vs := [BitVec.ofNat 64 P]) rfl
    (fun u h => by simp only [evalArgs, hv1 u h])
    (Rf := NameRet A s0.be (seg a P (P + DN.News.ArticleLines.nameLen a P e)) (DN.News.ArticleLines.nameLen a P e) e)
    (fun s1 hA1 hc hm hbe hloc hF1 => by
      have := artNameAt_ok o hA1 (by rw [hm]; exact hD) (by rw [hc]; exact hcode) hlen
        (by rw [hm, hbe, hF1]; exact hin) (by rw [hF1]; exact hb) hf (by rw [hF1]; exact hsep) hK
        ((hloc "p").trans rfl)
      rw [hbe] at this; exact this)
    hrt (G := fun v m => m = nameMem A s0.be (seg a P (P + DN.News.ArticleLines.nameLen a P e))
      (DN.News.ArticleLines.nameLen a P e) e m0 ∧ v = 0)
    (fun m m' v hm ⟨e1, e2⟩ => ⟨by rw [e1, hm], e2⟩) ?_) (fun u h => h) fun u ⟨v, h⟩ => ?_
  · intro v m h
    rw [h.1]
    unfold nameMem
    have hX := X_val
    have hxr : ArticleProg.xName = 505392 := rfl
    have hcol := DN.News.ArticleLines.fieldAt_colon hf
    have hmem := DN.News.ArticleLines.lines_mem hf.lines (P, e) List.mem_cons_self
    have hnc : ArticleProg.nameCap = 1024 := rfl
    exact (upd_ne _ (broken_ne_w (i := 11) (by decide) A)).trans ((putB_other _ hA.hA _ _ _ _
      (by have := DN.News.ArticleGrammar.broken_low; have := sets_le_X; omega)
      (by rw [DN.News.ArticleLines.seg_length a (by omega) (by omega)]; omega)).trans
      (fieldMem_keep hA.hA hlen hin hb _ _).2)
  · obtain ⟨hm, hv⟩ := h.2
    subst hv; exact ⟨h.1, hm⟩

/-- **A call of `artReceived`**: where the date of a Received field's value from `S` to `E` starts. -/
theorem recvCall_frag (o : Oracle σ) {R : Ret} {A : Word} {s0 : PancakeState σ} (hA : Area ArticleProg.ofs A s0)
    (hcode : ArtCode s0.code) {a : Bytes} (hlen : a.length ≤ artMax) {rt : String} (hra : rt ≠ "a")
    {l : List (String × Value)} (hla : l.lookup "a" = some A) (hrt : Fresh rt l = true) {m0 : Word → Word}
    (hb : m0 (at_ A aBroken) = 0) (hin : InputAt m0 s0.memaddrs s0.be A a) {S E : Nat} (hSE : S ≤ E)
    (hE : E ≤ a.length) {e1 e2 : Syntax.PExpr} {E1 E2 : PancakeExp}
    (he1 : Lower.lowerExp e1 = some E1) (he2 : Lower.lowerExp e2 = some E2)
    (hv1 : ∀ u, RunF s0 l (· = m0) u → eval u E1 = some (BitVec.ofNat 64 S))
    (hv2 : ∀ u, RunF s0 l (· = m0) u → eval u E2 = some (BitVec.ofNat 64 E)) :
    FragR o R (guardS (.call rt "artReceived" [e1, e2])) (RunF s0 l (· = m0))
      (fun u => ∃ Q, RunF s0 ((rt, BitVec.ofNat 64 Q) :: l) (· = m0) u ∧ S ≤ Q ∧ Q ≤ E ∧
        seg a Q E = ArticleSpec.receivedDate 0 0 (seg a S E)) := by
  refine fragR_conseq (gcall_frag o hA hcode hra (f := ArticleProg.artReceived) mem_artReceived (by decide)
    (F := (· = m0)) (DN.News.AbnfGen.lowerArgs_two he1 he2) hla (vs := [BitVec.ofNat 64 S, BitVec.ofNat 64 E]) rfl
    (fun u h => by simp only [evalArgs, hv1 u h, hv2 u h]) (Rf := DN.News.ArticleScan.RecvRet a S E)
    (fun s1 hA1 hc hm hbe hloc hF =>
      DN.News.ArticleScan.artReceived_ok o hA1 hlen (by rw [hF, hm, hbe]; exact hin) hSE hE
      ((hloc "s").trans rfl) ((hloc "e").trans rfl)) hrt
    (G := fun v m => m = m0 ∧ ∃ Q, v = BitVec.ofNat 64 Q ∧ S ≤ Q ∧ Q ≤ E ∧
      seg a Q E = ArticleSpec.receivedDate 0 0 (seg a S E))
    (fun m m' v hm hr => by obtain ⟨e, h⟩ := hr; exact ⟨e.trans hm, h⟩) fun v m h => by rw [h.1]; exact hb)
    (fun u h => h) fun u ⟨v, h⟩ => ?_
  obtain ⟨hm, Q, hv, h1, h2, h3⟩ := h.2
  subst hv; exact ⟨Q, ⟨h.1, hm⟩, h1, h2, h3⟩

/-- **A call of `artDate`**: what the date from `S` to `E` says; only the date's scratch words change. -/
theorem dateCall_frag (o : Oracle σ) {R : Ret} {A : Word} {s0 : PancakeState σ} (hA : Area ArticleProg.ofs A s0)
    (hD : ArtDom A s0.memaddrs) (hcode : ArtCode s0.code) {a : Bytes} (hlen : a.length ≤ artMax) {rt : String}
    (hra : rt ≠ "a") {l : List (String × Value)} (hla : l.lookup "a" = some A) (hrt : Fresh rt l = true)
    {m0 : Word → Word} (hP : Pows m0 A) (hb : m0 (at_ A aBroken) = 0) (hin : InputAt m0 s0.memaddrs s0.be A a)
    {S E : Nat} (hSE : S ≤ E) (hE : E ≤ a.length) {e1 e2 : Syntax.PExpr} {E1 E2 : PancakeExp}
    (he1 : Lower.lowerExp e1 = some E1) (he2 : Lower.lowerExp e2 = some E2)
    (hv1 : ∀ u, RunF s0 l (· = m0) u → eval u E1 = some (BitVec.ofNat 64 S))
    (hv2 : ∀ u, RunF s0 l (· = m0) u → eval u E2 = some (BitVec.ofNat 64 E)) :
    FragR o R (guardS (.call rt "artDate" [e1, e2])) (RunF s0 l (· = m0))
      (fun u => ∃ w m, RunF s0 ((rt, w) :: l) (· = m) u ∧ DN.News.ArticleDateOk.DateRet A a S E m0 w m) := by
  refine fragR_conseq (gcall_frag o hA hcode hra (f := ArticleProg.artDate .none) mem_artDate (by decide)
    (F := (· = m0)) (DN.News.AbnfGen.lowerArgs_two he1 he2) hla (vs := [BitVec.ofNat 64 S, BitVec.ofNat 64 E]) rfl
    (fun u h => by simp only [evalArgs, hv1 u h, hv2 u h]) (Rf := DN.News.ArticleDateOk.DateRet A a S E)
    (fun s1 hA1 hc hm hbe hloc hF => by
      have := DN.News.ArticleDateOk.artDate_ok o hA1 (by rw [hm]; exact hD) (by rw [hc]; exact hcode)
        (by rw [hF]; exact hP) (by rw [hF]; exact hb) hlen (by rw [hF, hm, hbe]; exact hin) hSE hE
        ((hloc "s").trans rfl) ((hloc "e").trans rfl)
      exact this) hrt
    (G := DN.News.ArticleDateOk.DateRet A a S E m0) (fun m m' w hm hr => by subst hm; exact hr) ?_)
    (fun u h => h) fun u ⟨w, h⟩ => ⟨w, u.memory, ⟨h.1, rfl⟩, h.2⟩
  intro w m h
  rw [DN.News.ArticleDateRun.dframe_low h.1 DN.News.ArticleGrammar.broken_low]; exact hb

/-! ## What the loop gathers -/

/-- A group's place: its first line's start. -/
def placeOf (g : List (Nat × Nat)) : Nat := (g.headD (0, 0)).1

/-- The first group that appears again when it may appear once, the fields `seen` before it. -/
def repG (a : Bytes) : List Field → List (List (Nat × Nat)) → Option (List (Nat × Nat))
  | _, [] => none
  | seen, g :: gs =>
    if ArticleSpec.isOne ArticleSpec.spec.once (fieldOf a g) &&
        seen.any (ArticleSpec.sameName ·.name (fieldOf a g).name)
    then some g else repG a (fieldOf a g :: seen) gs

theorem repeatedFrom_repG (a : Bytes) : ∀ (gs : List (List (Nat × Nat))) (seen : List Field),
    ArticleSpec.repeatedFrom ArticleSpec.spec (gs.map (fieldOf a)) seen =
      (repG a seen gs).map fun g => (fieldOf a g).name
  | [], _ => rfl
  | g :: gs, seen => by
    simp only [List.map_cons, ArticleSpec.repeatedFrom, repG]
    split
    · rfl
    · exact repeatedFrom_repG a gs _

/-- **The first repeated group of a longer prefix**: the shorter's, else the new group if it repeats. -/
theorem repG_snoc (a : Bytes) (g : List (Nat × Nat)) : ∀ (gd : List (List (Nat × Nat))) (seen : List Field),
    repG a seen (gd ++ [g]) = (repG a seen gd).or
      (if ArticleSpec.isOne ArticleSpec.spec.once (fieldOf a g) &&
          (seen ++ gd.map (fieldOf a)).any (ArticleSpec.sameName ·.name (fieldOf a g).name) then some g else none)
  | [], seen => by simp [repG]
  | g' :: gd, seen => by
    simp only [List.cons_append, repG, List.map_cons]
    split
    · rfl
    · rw [repG_snoc a g gd]
      congr 2
      simp only [List.any_append, List.any_cons, List.cons_append]
      cases List.any seen (ArticleSpec.sameName ·.name (fieldOf a g).name) <;>
        cases ArticleSpec.sameName (fieldOf a g').name (fieldOf a g).name <;> simp

theorem find_snoc (q : List (Nat × Nat) → Bool) (gd : List (List (Nat × Nat))) (g : List (Nat × Nat)) :
    (gd ++ [g]).find? q = (gd.find? q).or (if q g then some g else none) := by
  rw [List.find?_append]
  cases gd.find? q <;> cases h : q g <;> simp [h]

/-! ## The loop's body -/

open Syntax (v n eEq eLt eLe eAnd eAdd eSub eMul)

/-- Flag `b` of the field's entry, as `artCheck` tests it. -/
def bitE (b : Nat) : Syntax.PExpr := ne (eAnd (v "fl") (n b)) (n 0)

/-- The field's check: its end, its name's length, its entry, flags and rule, then the reasons in order. -/
def chkHead : List Syntax.PStmt :=
  [.call "fe" "artField" [v "p"], .dec "nl" (wd ArticleProg.xNl),
   .call "k" "artClass" [v "p", v "nl"], kept "k" (ArticleProg.E esP),
   .dec "fl" (.loadw 1 (eAdd (Syntax.atOff (v "a") (ArticleProg.xFlags esP)) (eMul (v "k") (n 8)))),
   .dec "ru" (.loadw 1 (eAdd (Syntax.atOff (v "a") (ArticleProg.xRuleT esP)) (eMul (v "k") (n 8)))),
   .dec "why" (n 0),
   .ite (bitE 1) [.assign "why" (n 6)]
     [.ite (bitE 2) [.assign "why" (n 7)]
       [.ite (bitE 4) [.assign "why" (n 8)] [ifs (bitE 8) [.assign "why" (n 9)]]]],
   ifs (eEq (v "why") (n 0)) [.call "bl" "artBlank" [v "p"], ifs (v "bl") [.assign "why" (n 10)]],
   ifs (eEq (v "why") (n 0))
     [.call "g" "artGrammar" [v "ru", v "p", v "fe"], ifs (eEq (v "g") (n 0)) [.assign "why" (n 11)]],
   ifs (v "why") [.call "cn" "artNameAt" [v "p"], .ret (v "why")]]

/-- What the loop keeps of a field: its entry's first field, a repeated field, a long identifier, a bad date. -/
def chkTail : List Syntax.PStmt :=
  [.dec "fk" (.loadw 1 (eAdd (Syntax.atOff (v "a") ArticleProg.xFirst) (eMul (v "k") (n 8)))),
   .ite (eLt (v "fk") (n 0)) [.store (eAdd (Syntax.atOff (v "a") ArticleProg.xFirst) (eMul (v "k") (n 8))) (v "p")]
     [ifs (eAnd (bitE 16) (eLt (v "rep") (n 0))) [.assign "rep" (v "p")]],
   .dec "vs" (eAdd (eAdd (v "p") (v "nl")) (n 1)), .dec "ve" (eSub (v "fe") (n 2)),
   ifs (eAnd (bitE 32) (eLt (v "lid") (n 0)))
     [.call "ml" "artMsgIds" [v "vs", v "ve"], ifs (v "ml") [.assign "lid" (v "p")]],
   ifs (eAnd (or2 (bitE 64) (bitE 128)) (eLt (v "bd") (n 0)))
     [.dec "ds" (v "vs"),
      ifs (bitE 128) [.call "rd" "artReceived" [v "vs", v "ve"], .assign "ds" (v "rd")],
      .call "dv" "artDate" [v "ds", v "ve"], ifs (eEq (v "dv") (n 0)) [.assign "bd" (v "p")]],
   .assign "p" (v "fe")]

/-! ## The loop's state -/

open DN.News.ArticleAdded (optW LoopF esP_length)

/-- The words the loop's calls write past the slots. They are the field's name length and first line's end, the
date's scratch, and the first identifier's place and length. -/
def HiScr (A : Word) (x : Word) : Prop :=
  x = at_ A ArticleProg.xNl ∨ x = at_ A ArticleProg.xE1 ∨ DN.News.ArticleDateRun.scratch A x ∨
    x = at_ A ArticleProg.xMsgS ∨ x = at_ A ArticleProg.xMsgL

/-- The words the loop writes: those, the input's length, the slots, the first fields' table. -/
def ChkScr (A : Word) (x : Word) : Prop :=
  HiScr A x ∨ x = at_ A aLen ∨ (∃ k, k < slots ∧ InSlot A k x) ∨
    ∃ k, k ≤ esP.length ∧ x = at_ A (ArticleProg.xFirst + 8 * k)

theorem hi_at {A : Word} {x : Word} (h : HiScr A x) :
    ∃ y, ArticleProg.X ≤ y ∧ y < ArticleProg.xFirst ∧ x = at_ A y := by
  have hX := X_val; have hF := xFirst_eq; have hT := DN.News.ArticleScan.xTok_eq
  rcases h with rfl | rfl | h | rfl | rfl
  · exact ⟨_, by simp only [ArticleProg.xNl, ArticleProg.w]; omega,
      by simp only [ArticleProg.xNl, ArticleProg.w]; omega, rfl⟩
  · exact ⟨_, by simp only [ArticleProg.xE1, ArticleProg.w]; omega,
      by simp only [ArticleProg.xE1, ArticleProg.w]; omega, rfl⟩
  · rcases h with rfl | rfl | rfl | rfl | rfl
    · exact ⟨_, by simp only [ArticleProg.xTokS, ArticleProg.w]; omega,
        by simp only [ArticleProg.xTokS, ArticleProg.w]; omega, rfl⟩
    · exact ⟨_, by simp only [ArticleProg.xTokLen, ArticleProg.w]; omega,
        by simp only [ArticleProg.xTokLen, ArticleProg.w]; omega, rfl⟩
    · exact ⟨_, by simp only [ArticleProg.xNumMod, ArticleProg.w]; omega,
        by simp only [ArticleProg.xNumMod, ArticleProg.w]; omega, rfl⟩
    · exact ⟨_, by simp only [ArticleProg.xValue, ArticleProg.w]; omega,
        by simp only [ArticleProg.xValue, ArticleProg.w]; omega, rfl⟩
    · exact ⟨_, by omega, by omega, rfl⟩
  · exact ⟨_, by simp only [ArticleProg.xMsgS, ArticleProg.w]; omega,
      by simp only [ArticleProg.xMsgS, ArticleProg.w]; omega, rfl⟩
  · exact ⟨_, by simp only [ArticleProg.xMsgL, ArticleProg.w]; omega,
      by simp only [ArticleProg.xMsgL, ArticleProg.w]; omega, rfl⟩

/-- A word below the slots or past the first fields' table is none the loop writes but the input's length. -/
theorem not_chk {A : Word} {y : Nat} (hy : y < aSets ∨ ArticleProg.xFirst + 8 * (esP.length + 1) ≤ y)
    (hy2 : y < 2 ^ 40) (hl : y ≠ aLen) : ¬ChkScr A (at_ A y) := by
  have hX := X_val; have hF := xFirst_eq; have hs := sets_le_X
  rw [esP_length] at hy
  rintro (h | h | ⟨k, hk, hin⟩ | ⟨k, hk, e⟩)
  · obtain ⟨z, h1, h2, e⟩ := hi_at h
    have := DN.News.ScanRun.at_inj (by omega) (by omega) e; omega
  · exact hl (DN.News.ScanRun.at_inj (by omega) (by decide) h)
  · rcases hy with hy | hy
    · exact notInSlot hk hy hin
    · have hXy : ArticleProg.X ≤ y := by rw [hX]; rw [hF] at hy; omega
      exact notInSlot_high hk hXy hy2 hin
  · rw [esP_length] at hk
    have := DN.News.ScanRun.at_inj (by omega) (by omega) e; omega

/-- The class of a group: its name's entry. -/
def classG (a : Bytes) (g : List (Nat × Nat)) : Nat := DN.News.ArticleRun.classOf esP (fieldOf a g).name

/-- Where the first group of class `k` starts. -/
def firstK (a : Bytes) (gd : List (List (Nat × Nat))) (k : Nat) : Option Nat :=
  (gd.find? (fun g => classG a g == k)).map placeOf

/-- **The loop's memory.** It holds what the leaves read, the sets, and each class's first group among those checked.
Every word the loop does not write is as in `m0`. -/
structure ChkM (s1 : PancakeState σ) (A : Word) (m0 : Word → Word) (a : Bytes) (gd : List (List (Nat × Nat)))
    (M : Word → Word) : Prop where
  reads : Reads s1 A a M
  sets : AllSets A M
  frame : ∀ x, ¬ChkScr A x → M x = m0 x
  first : ∀ k, k ≤ esP.length → M (at_ A (ArticleProg.xFirst + 8 * k)) = optW (firstK a gd k)

/-- What the leaves read is kept where the words below the slots are, for an article of any length. -/
theorem reads_keep' {s0 : PancakeState σ} {A : Word} {bytes : Bytes} (hA8 : A.toNat % 8 = 0)
    (hlen : bytes.length ≤ artMax) {m1 m : Word → Word} (h : Reads s0 A bytes m1)
    (keep : ∀ x, x < aSets → m (at_ A x) = m1 (at_ A x)) : Reads s0 A bytes m := by
  have hin := input_below
  have hR := reads_keep hA8 (bytes := []) (by simp) (m1 := m1) (m := m)
    ⟨fun x hx => absurd hx (Nat.not_lt_zero _), h.pows, h.masks, h.classes, h.texts⟩ keep
  refine ⟨fun x hx => ?_, hR.pows, hR.masks, hR.classes, hR.texts⟩
  have := h.input x hx
  unfold memLoadByte at this ⊢
  rw [DN.News.ScanRun.align_at hA8] at this ⊢
  rw [keep ((aInput + x) / 8 * 8) (by omega)]; exact this

/-- **Words past the slots written**, the loop's memory kept. -/
theorem chkM_hi {s1 : PancakeState σ} {A : Word} (hA8 : A.toNat % 8 = 0) {m0 : Word → Word} {a : Bytes}
    (hlen : a.length ≤ artMax) {gd : List (List (Nat × Nat))} {M M' : Word → Word} (h : ChkM s1 A m0 a gd M)
    (hk : ∀ x, ¬HiScr A x → M' x = M x) : ChkM s1 A m0 a gd M' := by
  have hX := X_val; have hF := xFirst_eq; have hs := sets_le_X
  have nlo : ∀ y, y < ArticleProg.X → ¬HiScr A (at_ A y) := fun y hy hh => by
    obtain ⟨z, h1, h2, e⟩ := hi_at hh
    have := DN.News.ScanRun.at_inj (by omega) (by omega) e; omega
  refine ⟨reads_keep' hA8 hlen h.reads fun x hx => hk _ (nlo x (by omega)), fun k hk' => ?_,
    fun x hx => (hk x fun hh => hx (.inl hh)).trans (h.frame x hx), fun k hk' => ?_⟩
  · obtain ⟨S, hS⟩ := h.sets k hk'
    refine ⟨S, setAt_frame hS fun i hi => hk _ fun hh => ?_⟩
    obtain ⟨z, h1, h2, e⟩ := hi_at hh
    have h3 := DN.News.AbnfSets.off_lt hk' (8 * i) (by rw [DN.News.AbnfSets.setSize_eq] at hi ⊢; omega)
    have hX' := X_eq
    have := DN.News.ScanRun.at_inj (by omega) (by omega) e
    omega
  · rw [esP_length] at hk'
    rw [hk _ fun hh => by
      obtain ⟨z, h1, h2, e⟩ := hi_at hh
      have := DN.News.ScanRun.at_inj (by omega) (by omega) e; omega]
    exact h.first k (by rw [esP_length]; exact hk')

/-- **The grammar called**: the loop's memory kept, given what the leaves read and the sets after. -/
theorem chkM_gram {s1 : PancakeState σ} {A : Word} {m0 : Word → Word} {a : Bytes} {gd : List (List (Nat × Nat))}
    {M M' : Word → Word} (h : ChkM s1 A m0 a gd M) (hR : Reads s1 A a M') (hall : AllSets A M')
    (hfr : ∀ x, (∀ k, k < slots → ¬InSlot A k x) → x ≠ at_ A aLen → M' x = M x) : ChkM s1 A m0 a gd M' := by
  have hX := X_val; have hF := xFirst_eq
  refine ⟨hR, hall, fun x hx => (hfr x (fun k hk hin => hx (.inr (.inr (.inl ⟨k, hk, hin⟩)))) fun e =>
    hx (.inr (.inl e))).trans (h.frame x hx), fun k hk => ?_⟩
  have hk' := hk; rw [esP_length] at hk'
  rw [hfr _ (fun j hj => notInSlot_high hj (by omega) (by omega)) (DN.News.ScanRun.at_ne (by omega) (by decide)
    (by have : aLen = 8 := rfl; omega))]
  exact h.first k hk

theorem firstK_snoc (a : Bytes) (gd : List (List (Nat × Nat))) (g : List (Nat × Nat)) (k : Nat) :
    firstK a (gd ++ [g]) k = (firstK a gd k).or (if classG a g = k then some (placeOf g) else none) := by
  unfold firstK
  rw [find_snoc]
  cases gd.find? (fun g => classG a g == k) <;> by_cases h : classG a g = k <;> simp [h]

theorem table_ne {A : Word} {j k : Nat} (hj : j ≤ esP.length) (hk : k ≤ esP.length) (h : j ≠ k) :
    at_ A (ArticleProg.xFirst + 8 * j) ≠ at_ A (ArticleProg.xFirst + 8 * k) := by
  have hF := xFirst_eq; rw [esP_length] at hj hk
  exact DN.News.ScanRun.at_ne (by omega) (by omega) (by omega)

/-- **A group whose class has a first group already**: the loop's memory as it is. -/
theorem chkM_seen {s1 : PancakeState σ} {A : Word} {m0 : Word → Word} {a : Bytes} {gd : List (List (Nat × Nat))}
    {M : Word → Word} (h : ChkM s1 A m0 a gd M) {g : List (Nat × Nat)} {P : Nat}
    (hs : firstK a gd (classG a g) = some P) : ChkM s1 A m0 a (gd ++ [g]) M := by
  refine ⟨h.reads, h.sets, h.frame, fun k hk => ?_⟩
  rw [h.first k hk, firstK_snoc]
  by_cases e : classG a g = k
  · subst e; rw [hs, Option.some_or]
  · rw [if_neg e]; cases firstK a gd k <;> rfl

/-- **The first group of its class**: its place stored in the table. -/
theorem chkM_store {s1 : PancakeState σ} {A : Word} (hA8 : A.toNat % 8 = 0) {m0 : Word → Word} {a : Bytes}
    (hlen : a.length ≤ artMax) {gd : List (List (Nat × Nat))} {M : Word → Word} (h : ChkM s1 A m0 a gd M)
    {g : List (Nat × Nat)} (hk : classG a g ≤ esP.length) (hn : firstK a gd (classG a g) = none) :
    ChkM s1 A m0 a (gd ++ [g])
      (upd M (at_ A (ArticleProg.xFirst + 8 * classG a g)) (BitVec.ofNat 64 (placeOf g))) := by
  have hX := X_val; have hF := xFirst_eq; have hs := sets_le_X
  have hk' := hk; rw [esP_length] at hk'
  refine ⟨reads_keep' hA8 hlen h.reads fun x hx => upd_ne _ (DN.News.ScanRun.at_ne (by omega) (by omega) (by omega)),
    fun k hk2 => ?_, fun x hx => ?_, fun j hj => ?_⟩
  · obtain ⟨S, hS⟩ := h.sets k hk2
    refine ⟨S, setAt_frame hS fun i hi => upd_ne _ fun e => ?_⟩
    have h3 := DN.News.AbnfSets.off_lt hk2 (8 * i) (by rw [DN.News.AbnfSets.setSize_eq] at hi ⊢; omega)
    have hX' := X_eq
    have := DN.News.ScanRun.at_inj (by omega) (by omega) e
    omega
  · rw [upd_ne _ fun e => hx (.inr (.inr (.inr ⟨_, hk, e⟩)))]; exact h.frame x hx
  · rw [firstK_snoc]
    by_cases e : classG a g = j
    · subst e; rw [upd_eq, hn, if_pos rfl]; rfl
    · rw [upd_ne _ (table_ne hj hk (Ne.symm e)), if_neg e, h.first j hj]; cases firstK a gd j <;> rfl

/-- The loop's state: the locals `L`, the memory as `ChkM` says. -/
def ChkSt (s1 : PancakeState σ) (A : Word) (m0 : Word → Word) (a : Bytes) (gd : List (List (Nat × Nat)))
    (L : List (String × Value)) : Assn σ :=
  fun u => ∃ M, RunF s1 L (· = M) u ∧ ChkM s1 A m0 a gd M

theorem cs_clock {s1 : PancakeState σ} {A : Word} {m0 : Word → Word} {a : Bytes} {gd : List (List (Nat × Nat))}
    {L : List (String × Value)} : Safe.ClockFree (ChkSt s1 A m0 a gd L) :=
  fun u k ⟨M, h, hv⟩ => ⟨M, runF_clock _ _ _ u k h, hv⟩

theorem cs_restore {s1 : PancakeState σ} {A : Word} {m0 : Word → Word} {a : Bytes} {gd : List (List (Nat × Nat))}
    {L : List (String × Value)} {u : PancakeState σ} (h : ChkSt s1 A m0 a gd L u) {y : String}
    (hy : Fresh y L = true) (w : Option Value) : ChkSt s1 A m0 a gd L (restore u y w) :=
  let ⟨M, hr, hv⟩ := h; ⟨M, runF_restore hr hy w, hv⟩

theorem cs_lift (o : Oracle σ) {R : Ret} {xs : List Syntax.PStmt} (hlow : LowKK xs) {s1 : PancakeState σ} {A : Word}
    {m0 : Word → Word} {a : Bytes} {gd : List (List (Nat × Nat))} {L : List (String × Value)} {Q : Assn σ}
    (h : ∀ M, ChkM s1 A m0 a gd M → FragR o R xs (RunF s1 L (· = M)) Q) : FragR o R xs (ChkSt s1 A m0 a gd L) Q := by
  refine fragR_exists hlow fun M => ?_
  exact fragR_pure (ChkM s1 A m0 a gd M) (fun u h => h.2) hlow fun hM =>
    fragR_conseq (h M hM) (fun u h => h.1) fun _ h => h

/-- **An assignment** with the memory as it is. -/
theorem cs_set (o : Oracle σ) {R : Ret} {s1 : PancakeState σ} {A : Word} {m0 : Word → Word} {a : Bytes}
    {gd : List (List (Nat × Nat))} {L : List (String × Value)} {x : String} {e : Syntax.PExpr} {E : PancakeExp}
    (he : Lower.lowerExp e = some E) {w : Value} (hx : L.lookup x = some w) {val : Value}
    (hv : ∀ u M, RunF s1 L (· = M) u → eval u E = some val) :
    FragR o R [.assign x e] (ChkSt s1 A m0 a gd L) (ChkSt s1 A m0 a gd ((x, val) :: DN.News.ScanRun.without x L)) :=
  cs_lift o (lowKK_one rfl (a := .assign x E) (by simp only [Lower.lowerStmt1, he])) fun M hM =>
    fragR_of (frag_conseq (runF_set o he hx (v := val)
    fun u h => hv u M h) (fun _ h => h) fun u h => ⟨M, h, hM⟩)

/-- **A local declared** with the memory as it is. -/
theorem cs_dec (o : Oracle σ) {R : Ret} {s1 : PancakeState σ} {A : Word} {m0 : Word → Word} {a : Bytes}
    {gd : List (List (Nat × Nat))} {L : List (String × Value)} {x : String} {e : Syntax.PExpr} {E : PancakeExp}
    (he : Lower.lowerExp e = some E) (hx : Fresh x L = true) {val : Value}
    (hv : ∀ u M, RunF s1 L (· = M) u → ChkM s1 A m0 a gd M → eval u E = some val) :
    FragR o R [.dec x e] (ChkSt s1 A m0 a gd L) (ChkSt s1 A m0 a gd ((x, val) :: L)) :=
  cs_lift o (lowKK_dec he) fun M hM => fragR_of (frag_conseq (runF_dec o he hx (v := val)
    fun u h => hv u M h hM) (fun _ h => h) fun _ h => ⟨M, h, hM⟩)

/-! ## What the loop reads -/

/-- **The tables kept** where the words from the flags' on are. -/
theorem tablesAt_hi {A : Word} (hA8 : A.toNat % 8 = 0) {dm : Word → Bool} {be : Bool} {es : List String}
    (hsz : ArticleProg.size es < 2 ^ 40) {m M : Word → Word}
    (hk : ∀ y, ArticleProg.xFlags es ≤ y → y < 2 ^ 40 → M (at_ A y) = m (at_ A y))
    (h : TablesAt A dm be m es) : TablesAt A dm be M es := by
  obtain ⟨h1, h2, h3, h4, h5, -⟩ := DN.News.ArticleTables.lay es
  refine ⟨fun k hk' => ?_, fun k hk' => ?_, fun k hk' i hi => ?_⟩
  · rw [hk _ (by omega) (by omega)]; exact h.off k hk'
  · rw [hk _ (by omega) (by omega)]; exact h.len k hk'
  · have hb := h.bytes k hk' i hi
    have hoff : offOf es k + i < ArticleProg.nameBytes es := by have := offOf_le es hk'; omega
    unfold memLoadByte at hb ⊢
    rw [DN.News.ScanRun.align_at hA8] at hb ⊢
    rw [hk _ (by omega) (by omega)]; exact hb

/-- **The flags and rules kept** where the words from the flags' on are. -/
theorem kindsAt_hi {r : ArticleSpec.Rules} {A : Word} {es : List String} (hsz : ArticleProg.size es < 2 ^ 40)
    {m M : Word → Word} (hk : ∀ y, ArticleProg.xFlags es ≤ y → y < 2 ^ 40 → M (at_ A y) = m (at_ A y))
    (h : DN.News.ArticleTables.KindsAt r es A m) : DN.News.ArticleTables.KindsAt r es A M := by
  obtain ⟨h1, h2, h3, h4, h5, -⟩ := DN.News.ArticleTables.lay es
  refine ⟨fun k hk' => ?_, fun k hk' => ?_, ?_, ?_⟩
  · rw [hk _ (by omega) (by omega)]; exact h.flags k hk'
  · rw [hk _ (by omega) (by omega)]; exact h.rules k hk'
  · rw [hk _ (by omega) (by omega)]; exact h.flagsE
  · rw [hk _ (by omega) (by omega)]; exact h.ruleE

theorem chk_hi {s1 : PancakeState σ} {A : Word} {m0 : Word → Word} {a : Bytes} {gd : List (List (Nat × Nat))}
    {M : Word → Word} (h : ChkM s1 A m0 a gd M) {y : Nat} (hy : ArticleProg.xFlags esP ≤ y) (hy2 : y < 2 ^ 40) :
    M (at_ A y) = m0 (at_ A y) := by
  have hl := (DN.News.ArticleTables.lay esP).1
  exact h.frame _ (not_chk (.inr (hl ▸ hy)) hy2 (by have := xFirst_eq; have : aLen = 8 := rfl; omega))

/-- An article's scalar word the loop does not write. -/
theorem not_chk_w {A : Word} {i : Nat} (hi : i < 32) (h15 : i ≠ 15) (h17 : i ≠ 17) (h18 : i ≠ 18) (h19 : i ≠ 19)
    (h20 : i ≠ 20) (h23 : i ≠ 23) (h24 : i ≠ 24) (h25 : i ≠ 25) : ¬ChkScr A (at_ A (ArticleProg.w i)) := by
  have hX := X_val; have hF := xFirst_eq; have hT := DN.News.ArticleScan.xTok_eq
  have hwi : ArticleProg.w i = 497936 + 8 * i := by simp only [ArticleProg.w, hX]
  have hw : ∀ y, y < 2 ^ 40 → at_ A (ArticleProg.w i) = at_ A y → 497936 + 8 * i = y := fun y hy e => by
    rw [← hwi]; exact DN.News.ScanRun.at_inj (by omega) (by omega) e
  have hs : ∀ j, ArticleProg.w j = 497936 + 8 * j := fun j => by simp only [ArticleProg.w, hX]
  rintro (h | h | ⟨k, hk, hin⟩ | ⟨k, hk, e⟩)
  · rcases h with e | e | (e | e | e | e | e) | e | e
    · have := hw _ (by rw [ArticleProg.xNl, hs]; omega) e; rw [ArticleProg.xNl, hs] at this; omega
    · have := hw _ (by rw [ArticleProg.xE1, hs]; omega) e; rw [ArticleProg.xE1, hs] at this; omega
    · have := hw _ (by rw [ArticleProg.xTokS, hs]; omega) e; rw [ArticleProg.xTokS, hs] at this; omega
    · have := hw _ (by rw [ArticleProg.xTokLen, hs]; omega) e; rw [ArticleProg.xTokLen, hs] at this; omega
    · have := hw _ (by rw [ArticleProg.xNumMod, hs]; omega) e; rw [ArticleProg.xNumMod, hs] at this; omega
    · have := hw _ (by rw [ArticleProg.xValue, hs]; omega) e; rw [ArticleProg.xValue, hs] at this; omega
    · have := hw _ (by omega) e; omega
    · have := hw _ (by rw [ArticleProg.xMsgS, hs]; omega) e; rw [ArticleProg.xMsgS, hs] at this; omega
    · have := hw _ (by rw [ArticleProg.xMsgL, hs]; omega) e; rw [ArticleProg.xMsgL, hs] at this; omega
  · have := hw _ (by decide) h; have : aLen = 8 := rfl; omega
  · exact notInSlot_high hk (by rw [hwi]; omega) (by rw [hwi]; omega) hin
  · rw [esP_length] at hk; have := hw _ (by omega) e; omega

/-- The address of word `j` of a table at `x`, `j` in the local `iv`. -/
theorem idxA_lower {x : Nat} (hx : (x == 0) = false) (iv : String) :
    Lower.lowerExp (eAdd (Syntax.atOff (v "a") x) (eMul (v iv) (n 8))) =
      some (.op .add (.op .add (.var "a") (.const (BitVec.ofNat 64 x)))
        (.mul (.var iv) (.const (BitVec.ofNat 64 8)))) := by
  rw [atOff_eq hx]; rfl

theorem idx_lower {x : Nat} (hx : (x == 0) = false) :
    Lower.lowerExp (.loadw 1 (eAdd (Syntax.atOff (v "a") x) (eMul (v "k") (n 8)))) =
      some (.loadWord (.op .add (.op .add (.var "a") (.const (BitVec.ofNat 64 x)))
        (.mul (.var "k") (.const (BitVec.ofNat 64 8))))) := by
  simp only [Lower.lowerExp, idxA_lower hx "k"]

theorem idx_eval {u : PancakeState σ} {A : Word} (ha : u.locals "a" = some A) {k : Nat}
    (hk : u.locals "k" = some (BitVec.ofNat 64 k)) {s1 : PancakeState σ} (hm : u.memaddrs = s1.memaddrs) {x : Nat}
    (hdm : s1.memaddrs (at_ A (x + 8 * k)) = true) :
    eval u (.loadWord (.op .add (.op .add (.var "a") (.const (BitVec.ofNat 64 x)))
      (.mul (.var "k") (.const (BitVec.ofNat 64 8))))) = some (u.memory (at_ A (x + 8 * k))) :=
  loadA_eval hm hdm (by simp only [eval, ha, hk]; rw [at_mul])

/-- The flags of entry `k`, none for no entry. -/
def flE (k : Nat) : Nat := if h : k < esP.length then ArticleProg.flagsOf ArticleSpec.spec esP[k] else 0

/-- The rule of entry `k`, `optional-field` for no entry. -/
def ruE (k : Nat) : Nat := if h : k < esP.length then ArticleProg.ruleOfName esP[k] else AbnfRules.optionalField

theorem flE_mem {A : Word} {m : Word → Word} (h : DN.News.ArticleTables.KindsAt ArticleSpec.spec esP A m) {k : Nat}
    (hk : k ≤ esP.length) : m (at_ A (ArticleProg.xFlags esP + 8 * k)) = BitVec.ofNat 64 (flE k) := by
  unfold flE
  by_cases h' : k < esP.length
  · rw [dif_pos h']; exact h.flags k h'
  · rw [dif_neg h', show k = esP.length by omega]; exact h.flagsE

theorem ruE_mem {A : Word} {m : Word → Word} (h : DN.News.ArticleTables.KindsAt ArticleSpec.spec esP A m) {k : Nat}
    (hk : k ≤ esP.length) : m (at_ A (ArticleProg.xRuleT esP + 8 * k)) = BitVec.ofNat 64 (ruE k) := by
  unfold ruE
  by_cases h' : k < esP.length
  · rw [dif_pos h']; exact h.rules k h'
  · rw [dif_neg h', show k = esP.length by omega]; exact h.ruleE

theorem flE_lt (k : Nat) : flE k < 256 := by
  unfold flE; split
  · exact flagsOf_lt _ _
  · decide

/-! ## A field's entry -/

open DN.News.ArticleAdded (Ss)

/-- The loop's locals. -/
def chkL (A : Word) (SEP P : Nat) (REP LID BD : Word) : List (String × Value) :=
  [("p", BitVec.ofNat 64 P), ("bd", BD), ("lid", LID), ("rep", REP), ("sep", BitVec.ofNat 64 SEP), ("a", A)]

/-- The locals once a field's entry is known. -/
def hdL (A : Word) (SEP P : Nat) (REP LID BD : Word) (NX K k : Nat) : List (String × Value) :=
  ("ru", BitVec.ofNat 64 (ruE k)) :: ("fl", BitVec.ofNat 64 (flE k)) :: ("k", BitVec.ofNat 64 k) ::
    ("nl", BitVec.ofNat 64 K) :: ("fe", BitVec.ofNat 64 NX) :: chkL A SEP P REP LID BD

/-- The facts on `m0` the loop reads. -/
structure ChkBase (s1 : PancakeState σ) (A : Word) (m0 : Word → Word) (SEP : Nat) (es : List String) : Prop where
  broken : m0 (at_ A aBroken) = 0
  sep : m0 (at_ A ArticleProg.xSep) = BitVec.ofNat 64 SEP
  tdom : TabDom A s1.memaddrs es
  tabs : TablesAt A s1.memaddrs s1.be m0 es
  kinds : DN.News.ArticleTables.KindsAt ArticleSpec.spec es A m0

theorem chk_broken {s1 : PancakeState σ} {A : Word} {m0 : Word → Word} {a : Bytes} {gd : List (List (Nat × Nat))}
    {M : Word → Word} (h : ChkM s1 A m0 a gd M) (hb : m0 (at_ A aBroken) = 0) : M (at_ A aBroken) = 0 :=
  (h.frame _ (not_chk (.inl DN.News.ArticleGrammar.broken_low) (by decide) (by decide))).trans hb

theorem chk_sep {s1 : PancakeState σ} {A : Word} {m0 : Word → Word} {a : Bytes} {gd : List (List (Nat × Nat))}
    {M : Word → Word} (h : ChkM s1 A m0 a gd M) {SEP : Nat} {es : List String} (hB : ChkBase s1 A m0 SEP es) :
    M (at_ A ArticleProg.xSep) = BitVec.ofNat 64 SEP :=
  (h.frame _ (not_chk_w (i := 16) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide))).trans hB.sep

/-- **A field's end, its name's length, entry, flags and rule.** -/
theorem chk_entry (o : Oracle σ) {R : Ret} {A : Word} {s1 : PancakeState σ} (hA : Area ArticleProg.ofs A s1)
    (hD : ArtDom A s1.memaddrs) (hcode : ArtCode s1.code) {m0 : Word → Word} {a : Bytes} (hlen : a.length ≤ artMax)
    {SEP : Nat} (hB : ChkBase s1 A m0 SEP esP)
    {gd : List (List (Nat × Nat))} {P e : Nat} {more : List (Nat × Nat)}
    (hf : DN.News.ArticleLines.FieldAt a SEP P e more) {REP LID BD : Word} :
    FragR o R (guardS (.call "fe" "artField" [v "p"]) ++ ([.dec "nl" (wd ArticleProg.xNl)] : Ss) ++
        guardS (.call "k" "artClass" [v "p", v "nl"]) ++
        ([kept "k" (ArticleProg.E esP),
          .dec "fl" (.loadw 1 (eAdd (Syntax.atOff (v "a") (ArticleProg.xFlags esP)) (eMul (v "k") (n 8)))),
          .dec "ru" (.loadw 1 (eAdd (Syntax.atOff (v "a") (ArticleProg.xRuleT esP)) (eMul (v "k") (n 8)))),
          .dec "why" (n 0)] : Ss))
      (ChkSt s1 A m0 a gd (chkL A SEP P REP LID BD))
      (ChkSt s1 A m0 a gd (("why", 0) :: hdL A SEP P REP LID BD (DN.News.ArticleLines.nextOf a more SEP)
        (DN.News.ArticleLines.nameLen a P e)
        (classOf esP (seg a P (P + DN.News.ArticleLines.nameLen a P e))))) := by
  have hA8 := hA.hA
  have hcol := DN.News.ArticleLines.fieldAt_colon hf
  have hmem := DN.News.ArticleLines.lines_mem hf.lines (P, e) List.mem_cons_self
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := DN.News.ArticleTables.lay esP
  let K := DN.News.ArticleLines.nameLen a P e
  let NX := DN.News.ArticleLines.nextOf a more SEP
  let k := classOf esP (seg a P (P + K))
  have hk : k ≤ esP.length := DN.News.ArticleAdded.classOf_le esP _
  -- the field's end and its name's length
  refine fragR_append (xs := guardS (.call "fe" "artField" [v "p"]) ++ ([.dec "nl" (wd ArticleProg.xNl)] : Ss))
    (M := ChkSt s1 A m0 a gd (("nl", BitVec.ofNat 64 K) :: ("fe", BitVec.ofNat 64 NX) ::
    chkL A SEP P REP LID BD)) (cs_lift o (lowK_any _ (k := .skip) rfl) fun M hM => ?_) ?_
  · have hbM := chk_broken hM hB.broken
    have hsepM : M (at_ A ArticleProg.xSep) = BitVec.ofNat 64 SEP :=
      chk_sep hM hB
    refine fragR_append (fieldCall_frag o hA hD hcode hlen (rt := "fe") (by decide) (l := chkL A SEP P REP LID BD) rfl
      rfl (e1 := v "p") rfl hf (fun u h => ev_var (vals_lookup h.1.vals rfl)) hM.reads.input hbM hsepM) ?_
    refine fragR_conseq (fragR_of (runF_dec o (wd_lower 17) rfl (v := BitVec.ofNat 64 K) fun u h => by
      rw [loadA_eval h.1.memaddrs (artDom_w hD (i := 17) (by decide)) (atA_eval (vals_lookup h.1.vals rfl)), h.2]
      exact congrArg some (fieldMem_nl A K e M))) (fun _ h => h) fun u h => ⟨_, h, chkM_hi hA8 hlen hM fun x hx => ?_⟩
    simp only [fieldMem]
    rw [upd_ne _ fun h => hx (.inr (.inl h)), upd_ne _ fun h => hx (.inl h)]
  -- its entry
  refine fragR_append (xs := guardS (.call "k" "artClass" [v "p", v "nl"]))
    (M := ChkSt s1 A m0 a gd (("k", BitVec.ofNat 64 k) :: ("nl", BitVec.ofNat 64 K) ::
    ("fe", BitVec.ofNat 64 NX) :: chkL A SEP P REP LID BD)) (cs_lift o (lowK_any _ (k := .skip) rfl) fun M hM => ?_) ?_
  · refine fragR_conseq (DN.News.ArticleAdded.classCall_frag o hA hcode (rt := "k") (by decide)
      (l := ("nl", BitVec.ofNat 64 K) ::
      ("fe", BitVec.ofNat 64 NX) :: chkL A SEP P REP LID BD) rfl rfl (chk_broken hM hB.broken) hB.tdom
      (tablesAt_hi hA8 esP_size (fun y hy hy2 => chk_hi hM hy hy2) hB.tabs) esP_short esP_size hM.reads.input hlen
      (P := P) (NL := K) (by omega) (e1 := v "p") (e2 := v "nl") rfl rfl
      (fun u h => ev_var (vals_lookup h.1.vals rfl)) (fun u h => ev_var (vals_lookup h.1.vals rfl))) (fun _ h => h)
      fun u h => ⟨_, h, hM⟩
  refine fragR_append (xs := [_]) (fragR_of (kept_frag o (by simp only [ArticleProg.E, esP_length]; decide) cs_clock
    fun u ⟨M, h, _⟩ => ⟨k, vals_lookup h.1.vals rfl, hk⟩)) ?_
  -- its flags and rule
  have hdmF : s1.memaddrs (at_ A (ArticleProg.xFlags esP + 8 * k)) = true :=
    hB.tdom _ (by omega) (by simp only [ArticleProg.size] at h5 ⊢; omega) (by omega)
  have hdmR : s1.memaddrs (at_ A (ArticleProg.xRuleT esP + 8 * k)) = true :=
    hB.tdom _ (by omega) (by simp only [ArticleProg.size] at h5 ⊢; omega) (by omega)
  have hkM : ∀ M, ChkM s1 A m0 a gd M → DN.News.ArticleTables.KindsAt ArticleSpec.spec esP A M := fun M hM =>
    kindsAt_hi esP_size (fun y hy hy2 => chk_hi hM hy hy2) hB.kinds
  have hxF : (ArticleProg.xFlags esP == 0) = false := by
    rw [h1]; exact beq_false_of_ne (by omega)
  have hxR : (ArticleProg.xRuleT esP == 0) = false := by
    rw [h2]; exact beq_false_of_ne (by omega)
  refine fragR_append (xs := [_]) (cs_dec o (idx_lower hxF) rfl (val := BitVec.ofNat 64 (flE k)) fun u M h hM => by
    rw [idx_eval (vals_lookup h.1.vals rfl) (vals_lookup h.1.vals rfl) h.1.memaddrs hdmF, h.2]
    exact congrArg some (flE_mem (hkM M hM) hk)) ?_
  refine fragR_append (xs := [_]) (cs_dec o (idx_lower hxR) rfl (val := BitVec.ofNat 64 (ruE k)) fun u M h hM => by
    rw [idx_eval (vals_lookup h.1.vals rfl) (vals_lookup h.1.vals rfl) h.1.memaddrs hdmR, h.2]
    exact congrArg some (ruE_mem (hkM M hM) hk)) ?_
  exact cs_dec o rfl rfl (val := 0) fun u M h hM => rfl

/-! ## The reason found -/

theorem without_fresh {x : String} {w : Value} {l : List (String × Value)} (h : Fresh x l = true) :
    DN.News.ScanRun.without x ((x, w) :: l) = l := by
  unfold DN.News.ScanRun.without
  rw [List.filter_cons_of_neg (by simp)]
  exact List.filter_eq_self.2 fun q hq => by
    have := List.all_eq_true.1 h q hq; simpa using this

theorem cs_sub {s1 : PancakeState σ} {A : Word} {m0 : Word → Word} {a : Bytes} {gd : List (List (Nat × Nat))}
    {L L' : List (String × Value)} {u : PancakeState σ} (h : ChkSt s1 A m0 a gd L u) (hl : ∀ q ∈ L', q ∈ L) :
    ChkSt s1 A m0 a gd L' u :=
  let ⟨M, hr, hv⟩ := h; ⟨M, runF_mono hr hl fun _ h => h, hv⟩

theorem fresh_mem {x : String} {l : List (String × Value)} (h : Fresh x l = true) {q : String × Value} (hq : q ∈ l) :
    q.1 ≠ x := by simpa using List.all_eq_true.1 h q hq

theorem lookup_fresh {x : String} : ∀ {pre : List (String × Value)} (l : List (String × Value)), Fresh x pre = true →
    (pre ++ l).lookup x = l.lookup x
  | [], _, _ => rfl
  | (k, w) :: pre, l, h => by
    simp only [Fresh, List.all_cons, Bool.and_eq_true] at h
    have hk : (x == k) = false := by
      have := h.1; simp only [bne_iff_ne, ne_eq] at this; exact beq_false_of_ne fun e => this e.symm
    rw [List.cons_append, List.lookup_cons, hk]
    exact lookup_fresh l h.2

/-- **A local set** in the middle of the locals. -/
theorem set_in (o : Oracle σ) {R : Ret} {s1 : PancakeState σ} {A : Word} {m0 : Word → Word} {a : Bytes}
    {gd : List (List (Nat × Nat))} (pre post : List (String × Value)) {x : String} (hpre : Fresh x pre = true)
    (hpost : Fresh x post = true) {w0 : Value} {e : Syntax.PExpr} {E : PancakeExp} (he : Lower.lowerExp e = some E)
    {val : Value} (hv : ∀ u M, RunF s1 (pre ++ (x, w0) :: post) (· = M) u → eval u E = some val) :
    FragR o R [.assign x e] (ChkSt s1 A m0 a gd (pre ++ (x, w0) :: post))
      (ChkSt s1 A m0 a gd (pre ++ (x, val) :: post)) := by
  have hl : (pre ++ (x, w0) :: post).lookup x = some w0 := by
    rw [lookup_fresh _ hpre, List.lookup_cons, beq_self_eq_true]
  refine fragR_conseq (cs_set o he hl hv) (fun _ h => h) fun u h => cs_sub h fun q hq => ?_
  rcases List.mem_append.1 hq with hq | hq
  · exact List.mem_cons_of_mem _ (mem_without (List.mem_append_left _ hq) (fresh_mem hpre hq))
  · rcases List.mem_cons.1 hq with rfl | hq
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (mem_without (List.mem_append_right _ (List.mem_cons_of_mem _ hq))
        (fresh_mem hpost hq))

/-- The reason the flags give: 6 to 9, or 0. -/
def whyFlags (F : Nat) : Nat :=
  if F.testBit 0 then 6 else if F.testBit 1 then 7 else if F.testBit 2 then 8 else if F.testBit 3 then 9 else 0

theorem cs_bit {s1 : PancakeState σ} {A : Word} {m0 : Word → Word} {a : Bytes} {gd : List (List (Nat × Nat))}
    {L : List (String × Value)} {F : Nat} (hF : F < 256) (hfl : L.lookup "fl" = some (BitVec.ofNat 64 F)) {i : Nat}
    (hi : i < 64) {u : PancakeState σ} (h : ChkSt s1 A m0 a gd L u) :
    eval u (.cmp .equal (.cmp .equal (.op .and_ (.var "fl") (.const (BitVec.ofNat 64 (2 ^ i))))
      (.const (BitVec.ofNat 64 0))) (.const (BitVec.ofNat 64 0))) = some (bw (F.testBit i)) :=
  let ⟨_, hr, _⟩ := h; bit_eval (by omega) (vals_lookup hr.1.vals hfl) hi

/-- **The reasons of the flags**: injected, traced, deprecated, not offered. -/
theorem chk_bits (o : Oracle σ) {R : Ret} {s1 : PancakeState σ} {A : Word} {m0 : Word → Word} {a : Bytes}
    {gd : List (List (Nat × Nat))} {Hd : List (String × Value)} (hfr : Fresh "why" Hd = true) {F : Nat}
    (hF : F < 256) (hfl : Hd.lookup "fl" = some (BitVec.ofNat 64 F)) :
    FragR o R [.ite (bitE 1) [.assign "why" (n 6)]
      [.ite (bitE 2) [.assign "why" (n 7)] [.ite (bitE 4) [.assign "why" (n 8)] [ifs (bitE 8) [.assign "why" (n 9)]]]]]
      (ChkSt s1 A m0 a gd (("why", 0) :: Hd)) (ChkSt s1 A m0 a gd (("why", BitVec.ofNat 64 (whyFlags F)) :: Hd)) := by
  have hfl' : (("why", (0 : Value)) :: Hd).lookup "fl" = some (BitVec.ofNat 64 F) := hfl
  refine fragR_if o rfl (lowK_any _ (k := .skip) rfl) (lowK_any _ (k := .skip) rfl) cs_clock
    (fun _ _ _ _ hy => by simp [declared] at hy) (fun _ _ _ _ hy => by simp [declared] at hy) (b := F.testBit 0)
    (fun u h => cs_bit hF hfl' (i := 0) (by decide) h) (fun hb => ?_) fun hb => ?_
  · rw [show whyFlags F = 6 by unfold whyFlags; rw [if_pos hb]]; exact set_in o [] Hd rfl hfr rfl fun _ _ _ => rfl
  refine fragR_if o rfl (lowK_any _ (k := .skip) rfl) (lowK_any _ (k := .skip) rfl) cs_clock
    (fun _ _ _ _ hy => by simp [declared] at hy) (fun _ _ _ _ hy => by simp [declared] at hy) (b := F.testBit 1)
    (fun u h => cs_bit hF hfl' (i := 1) (by decide) h) (fun hb1 => ?_) fun hb1 => ?_
  · rw [show whyFlags F = 7 by unfold whyFlags; rw [if_neg (by simp [hb]), if_pos hb1]]
    exact set_in o [] Hd rfl hfr rfl fun _ _ _ => rfl
  refine fragR_if o rfl (lowK_any _ (k := .skip) rfl) (lowK_any _ (k := .skip) rfl) cs_clock
    (fun _ _ _ _ hy => by simp [declared] at hy) (fun _ _ _ _ hy => by simp [declared, ifs] at hy) (b := F.testBit 2)
    (fun u h => cs_bit hF hfl' (i := 2) (by decide) h) (fun hb2 => ?_) fun hb2 => ?_
  · rw [show whyFlags F = 8 by unfold whyFlags; rw [if_neg (by simp [hb]), if_neg (by simp [hb1]), if_pos hb2]]
    exact set_in o [] Hd rfl hfr rfl fun _ _ _ => rfl
  refine fragR_if o rfl (lowK_any _ (k := .skip) rfl) (lowK_any _ (k := .skip) rfl) cs_clock
    (fun _ _ _ _ hy => by simp [declared] at hy) (fun _ _ _ _ hy => by simp [declared] at hy) (b := F.testBit 3)
    (fun u h => cs_bit hF hfl' (i := 3) (by decide) h) (fun hb3 => ?_) fun hb3 => ?_
  · rw [show whyFlags F = 9 by
      unfold whyFlags; rw [if_neg (by simp [hb]), if_neg (by simp [hb1]), if_neg (by simp [hb2]), if_pos hb3]]
    exact set_in o [] Hd rfl hfr rfl fun _ _ _ => rfl
  · rw [show whyFlags F = 0 by
      unfold whyFlags
      rw [if_neg (by simp [hb]), if_neg (by simp [hb1]), if_neg (by simp [hb2]), if_neg (by simp [hb3])]]
    exact fragR_of (frag_nil o fun _ h => h)

/-- **The reason set**, the locals past `Hd` dropped. -/
theorem why_set' (o : Oracle σ) {R : Ret} {s1 : PancakeState σ} {A : Word} {m0 : Word → Word} {a : Bytes}
    {gd : List (List (Nat × Nat))} {L Hd : List (String × Value)} {w0 : Value} (hw : L.lookup "why" = some w0)
    (hfr : Fresh "why" Hd = true) (hsub : ∀ q ∈ Hd, q ∈ L) (W : Nat) :
    FragR o R [.assign "why" (n W)] (ChkSt s1 A m0 a gd L) (ChkSt s1 A m0 a gd (("why", BitVec.ofNat 64 W) :: Hd)) :=
  fragR_conseq (cs_set o rfl hw (val := BitVec.ofNat 64 W) fun _ _ _ => rfl) (fun _ h => h) fun u h => cs_sub h
    fun q hq => by
      rcases List.mem_cons.1 hq with rfl | hq
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (mem_without (hsub q hq) (fresh_mem hfr hq))

/-- What the program's reason is after the blank lines' check: as before, else 10 if a line is blank. -/
def whyBlank (W : Nat) (B : Bool) : Nat := if W = 0 then (if B then 10 else 0) else W

theorem cs_eq0 {s1 : PancakeState σ} {A : Word} {m0 : Word → Word} {a : Bytes} {gd : List (List (Nat × Nat))}
    {L : List (String × Value)} {x : String} {W : Nat} (hW : W < 2 ^ 64) (hx : L.lookup x = some (BitVec.ofNat 64 W))
    {u : PancakeState σ} (h : ChkSt s1 A m0 a gd L u) :
    eval u (.cmp .equal (.var x) (.const (BitVec.ofNat 64 0))) = some (bw (decide (W = 0))) :=
  let ⟨_, hr, _⟩ := h; DN.News.FramerCode.eval_eq hW (by decide) (ev_var (vals_lookup hr.1.vals hx)) rfl

/-- **A blank line of the body**, checked when no reason is found yet. -/
theorem chk_blank (o : Oracle σ) {R : Ret} {A : Word} {s1 : PancakeState σ} (hA : Area ArticleProg.ofs A s1)
    (hD : ArtDom A s1.memaddrs) (hcode : ArtCode s1.code) {m0 : Word → Word} {a : Bytes} (hlen : a.length ≤ artMax)
    {SEP : Nat} (hB : ChkBase s1 A m0 SEP esP) {gd : List (List (Nat × Nat))} {P e : Nat} {more : List (Nat × Nat)}
    (hf : DN.News.ArticleLines.FieldAt a SEP P e more) {Hd : List (String × Value)} (hfr : Fresh "why" Hd = true)
    (hbl : Fresh "bl" Hd = true) (hp : Hd.lookup "p" = some (BitVec.ofNat 64 P)) (ha : Hd.lookup "a" = some A)
    {W : Nat} (hW : W < 2 ^ 63) :
    FragR o R (guardS (ifs (eEq (v "why") (n 0)) [.call "bl" "artBlank" [v "p"], ifs (v "bl") [.assign "why" (n 10)]]))
      (ChkSt s1 A m0 a gd (("why", BitVec.ofNat 64 W) :: Hd))
      (ChkSt s1 A m0 a gd (("why", BitVec.ofNat 64 (whyBlank W
        ((seg a (P + DN.News.ArticleLines.nameLen a P e + 1) e).all DN.News.CommandSpec.isWS ||
          DN.News.ArticleLines.blankL a more))) :: Hd)) := by
  have hA8 := hA.hA
  let B := (seg a (P + DN.News.ArticleLines.nameLen a P e + 1) e).all DN.News.CommandSpec.isWS ||
    DN.News.ArticleLines.blankL a more
  have hfw : Fresh "bl" (("why", BitVec.ofNat 64 W) :: Hd) = true := by
    simp only [Fresh, List.all_cons]; exact Bool.and_eq_true_iff.2 ⟨rfl, hbl⟩
  refine fragR_if o rfl (lowK_any _ (k := .skip) rfl) (lowK_any _ (k := .skip) rfl) cs_clock
    (fun u y w h hy => by
      have : y = "bl" := by simpa [declared, guardS, guardL, ifs] using hy
      subst this; exact cs_restore h (by
        simp only [Fresh, List.all_cons]; exact Bool.and_eq_true_iff.2 ⟨rfl, hbl⟩) w)
    (fun _ _ _ _ hy => nomatch hy) (b := decide (W = 0))
    (fun u h => cs_eq0 (by omega) rfl h) (fun h0 => ?_) fun h0 => ?_
  · have hW0 : W = 0 := of_decide_eq_true h0
    refine fragR_append (xs := guardS (.call "bl" "artBlank" [v "p"]))
      (M := ChkSt s1 A m0 a gd (("bl", bw B) :: ("why", BitVec.ofNat 64 W) :: Hd))
      (cs_lift o (lowK_any _ (k := .skip) rfl) fun M hM => ?_) ?_
    · have hsepM : M (at_ A ArticleProg.xSep) = BitVec.ofNat 64 SEP :=
        chk_sep hM hB
      refine fragR_conseq (blankCall_frag o hA hD hcode hlen (rt := "bl") (by decide)
        (l := ("why", BitVec.ofNat 64 W) :: Hd) ha hfw (e1 := v "p") rfl hf
        (fun u h => ev_var (vals_lookup h.1.vals hp)) hM.reads.input (chk_broken hM hB.broken) hsepM)
        (fun _ h => h) fun u h => ⟨_, h, chkM_hi hA8 hlen hM fun x hx => ?_⟩
      simp only [fieldMem]
      rw [upd_ne _ fun h => hx (.inr (.inl h)), upd_ne _ fun h => hx (.inl h)]
    refine fragR_if o rfl (lowK_any _ (k := .skip) rfl) (lowK_any _ (k := .skip) rfl) cs_clock
      (fun _ _ _ _ hy => nomatch hy) (fun _ _ _ _ hy => nomatch hy) (b := B)
      (fun u ⟨_, hr, _⟩ => ev_var (vals_lookup hr.1.vals rfl)) (fun hb1 => ?_) fun hb1 => ?_
    · rw [show whyBlank W B = 10 by unfold whyBlank; rw [if_pos hW0, if_pos hb1]]
      exact why_set' o rfl hfr (fun q hq => List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hq)) 10
    · rw [show whyBlank W B = 0 by unfold whyBlank; rw [if_pos hW0, if_neg (by simp [hb1])]]
      exact fragR_of (frag_nil o fun u h => cs_sub h fun q hq => by
        rcases List.mem_cons.1 hq with rfl | hq
        · rw [hW0]; exact List.mem_cons_of_mem _ List.mem_cons_self
        · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hq))
  · have hW0 : ¬W = 0 := of_decide_eq_false h0
    rw [show whyBlank W B = W by unfold whyBlank; rw [if_neg hW0]]
    exact fragR_of (frag_nil o fun _ h => h)

theorem ruleOfName_mem (s : String) :
    ArticleProg.ruleOfName s ∈ AbnfRules.fieldRules.map (·.2) ++ [AbnfRules.optionalField] := by
  unfold ArticleProg.ruleOfName
  cases h : AbnfRules.fieldRules.find? (fun p => ArticleProg.lowerS p.1 == ArticleProg.lowerS s) with
  | none => simp
  | some p => exact List.mem_append_left _ (List.mem_map.2 ⟨p, List.mem_of_find?_eq_some h, rfl⟩)

theorem ruE_used (k : Nat) : ruE k ∈ ArticleProg.usedRules := by
  have h : ∀ x, x ∈ AbnfRules.fieldRules.map (·.2) ++ [AbnfRules.optionalField] → x ∈ ArticleProg.usedRules :=
    fun x hx => by unfold ArticleProg.usedRules; exact List.mem_eraseDups.2 (List.mem_append_left _ hx)
  unfold ruE; split
  · exact h _ (ruleOfName_mem _)
  · exact h _ (by simp)

/-- What the program's reason is after the grammar's check: as before, else 11 if the grammar refuses. -/
def whyGram (W : Nat) (G : Bool) : Nat := if W = 0 then (if G then 0 else 11) else W

/-- **The field's grammar**, checked when no reason is found yet. -/
theorem chk_gram (o : Oracle σ) {R : Ret} {A : Word} {s1 : PancakeState σ} (hA : Area ArticleProg.ofs A s1)
    (hcode : ArtCode s1.code) {m0 : Word → Word} {a : Bytes} (hlen : a.length ≤ artMax)
    {SEP : Nat} (hB : ChkBase s1 A m0 SEP esP) {gd : List (List (Nat × Nat))} {Hd : List (String × Value)}
    (hfr : Fresh "why" Hd = true) (hg : Fresh "g" Hd = true) {P NX k : Nat}
    (hp : Hd.lookup "p" = some (BitVec.ofNat 64 P)) (ha : Hd.lookup "a" = some A)
    (hfe : Hd.lookup "fe" = some (BitVec.ofNat 64 NX)) (hru : Hd.lookup "ru" = some (BitVec.ofNat 64 (ruE k)))
    (hP : P ≤ inputMax) (hNX : NX ≤ inputMax) (hNXa : NX ≤ a.length) {W : Nat} (hW : W < 2 ^ 63) :
    FragR o R (guardS (ifs (eEq (v "why") (n 0))
        [.call "g" "artGrammar" [v "ru", v "p", v "fe"], ifs (eEq (v "g") (n 0)) [.assign "why" (n 11)]]))
      (ChkSt s1 A m0 a gd (("why", BitVec.ofNat 64 W) :: Hd))
      (ChkSt s1 A m0 a gd (("why", BitVec.ofNat 64 (whyGram W
        (setOf (Matches AbnfRules.grammar (inputOf (a.take NX)) (.ref (ruE k)) P) NX))) :: Hd)) := by
  let G := setOf (Matches AbnfRules.grammar (inputOf (a.take NX)) (.ref (ruE k)) P) NX
  have hfw : Fresh "g" (("why", BitVec.ofNat 64 W) :: Hd) = true := by
    simp only [Fresh, List.all_cons]; exact Bool.and_eq_true_iff.2 ⟨rfl, hg⟩
  refine fragR_if o rfl (lowK_any _ (k := .skip) rfl) (lowK_any _ (k := .skip) rfl) cs_clock
    (fun u y w h hy => by
      have : y = "g" := by simpa [declared, guardS, guardL, ifs] using hy
      subst this; exact cs_restore h (by
        simp only [Fresh, List.all_cons]; exact Bool.and_eq_true_iff.2 ⟨rfl, hg⟩) w)
    (fun _ _ _ _ hy => nomatch hy) (b := decide (W = 0))
    (fun u h => cs_eq0 (by omega) rfl h) (fun h0 => ?_) fun h0 => ?_
  · have hW0 : W = 0 := of_decide_eq_true h0
    refine fragR_append (xs := guardS (.call "g" "artGrammar" [v "ru", v "p", v "fe"]))
      (M := ChkSt s1 A m0 a gd (("g", bw G) :: ("why", BitVec.ofNat 64 W) :: Hd))
      (cs_lift o (lowK_any _ (k := .skip) rfl) fun M hM => ?_) ?_
    · refine fragR_conseq (gramCall_frag o hA hcode (rt := "g") (by decide) (l := ("why", BitVec.ofNat 64 W) :: Hd)
        ha hfw hlen hM.reads hM.sets (chk_broken hM hB.broken) (ruE_used k) hP hNX hNXa (e1 := v "ru") (e2 := v "p")
        (e3 := v "fe") rfl rfl rfl (fun u h => ev_var (vals_lookup h.1.vals hru))
        (fun u h => ev_var (vals_lookup h.1.vals hp)) (fun u h => ev_var (vals_lookup h.1.vals hfe)))
        (fun _ h => h) fun u ⟨m, h, hR, hall, hfr'⟩ => ⟨m, h, chkM_gram hM hR hall hfr'⟩
    have hGv : bw G = BitVec.ofNat 64 (if G then 1 else 0) := DN.News.ArticleRun.bw_ofNat G
    refine fragR_if o rfl (lowK_any _ (k := .skip) rfl) (lowK_any _ (k := .skip) rfl) cs_clock
      (fun _ _ _ _ hy => nomatch hy) (fun _ _ _ _ hy => nomatch hy) (b := decide ((if G then 1 else 0) = 0))
      (fun u h => cs_eq0 (by split <;> decide) (by rw [← hGv]; rfl) h) (fun hb1 => ?_) fun hb1 => ?_
    · have hG : G = false := by cases hG' : G <;> simp_all
      rw [show whyGram W G = 11 by unfold whyGram; rw [if_pos hW0, hG]; rfl]
      exact why_set' o rfl hfr (fun q hq => List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hq)) 11
    · have hG : G = true := by cases hG' : G <;> simp_all
      rw [show whyGram W G = 0 by unfold whyGram; rw [if_pos hW0, hG]; rfl]
      exact fragR_of (frag_nil o fun u h => cs_sub h fun q hq => by
        rcases List.mem_cons.1 hq with rfl | hq
        · rw [hW0]; exact List.mem_cons_of_mem _ List.mem_cons_self
        · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hq))
  · have hW0 : ¬W = 0 := of_decide_eq_false h0
    rw [show whyGram W G = W by unfold whyGram; rw [if_neg hW0]]
    exact fragR_of (frag_nil o fun _ h => h)

/-- **A reason found**: the field's name kept for the answer, the reason given back. -/
theorem chk_ret (o : Oracle σ) {R : Ret} {A : Word} {s1 : PancakeState σ} (hA : Area ArticleProg.ofs A s1)
    (hD : ArtDom A s1.memaddrs) (hcode : ArtCode s1.code) {m0 : Word → Word} {a : Bytes} (hlen : a.length ≤ artMax)
    {SEP : Nat} (hB : ChkBase s1 A m0 SEP esP) {gd : List (List (Nat × Nat))} {P e : Nat} {more : List (Nat × Nat)}
    (hf : DN.News.ArticleLines.FieldAt a SEP P e more)
    (hK : DN.News.ArticleLines.nameLen a P e < ArticleProg.nameCap) {Hd : List (String × Value)}
    (hcn : Fresh "cn" Hd = true) (hp : Hd.lookup "p" = some (BitVec.ofNat 64 P)) (ha : Hd.lookup "a" = some A)
    {W : Nat} (hW : W < 2 ^ 63)
    (hR : ∀ M, ChkM s1 A m0 a gd M → W ≠ 0 → R (BitVec.ofNat 64 W) (nameMem A s1.be
      (seg a P (P + DN.News.ArticleLines.nameLen a P e)) (DN.News.ArticleLines.nameLen a P e) e M)) :
    FragR o R (guardS (ifs (v "why") [.call "cn" "artNameAt" [v "p"], .ret (v "why")]))
      (ChkSt s1 A m0 a gd (("why", BitVec.ofNat 64 W) :: Hd))
      (fun u => ChkSt s1 A m0 a gd (("why", BitVec.ofNat 64 W) :: Hd) u ∧ W = 0) := by
  have hfw : Fresh "cn" (("why", BitVec.ofNat 64 W) :: Hd) = true := by
    simp only [Fresh, List.all_cons]; exact Bool.and_eq_true_iff.2 ⟨rfl, hcn⟩
  have hev : ∀ u, ChkSt s1 A m0 a gd (("why", BitVec.ofNat 64 W) :: Hd) u →
      eval u (.var "why") = some (BitVec.ofNat 64 W) := fun u ⟨_, hr, _⟩ => ev_var (vals_lookup hr.1.vals rfl)
  have hz : ∀ u, ChkSt s1 A m0 a gd (("why", BitVec.ofNat 64 W) :: Hd) u → (eval u (.var "why") = some 0 ↔ W = 0) :=
    fun u h => by
      rw [hev u h]
      constructor
      · intro e; have := congrArg BitVec.toNat (Option.some.inj e)
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at this; exact this
      · intro e; rw [e]; rfl
  refine fragR_ite o rfl (fun u c h => ⟨cs_clock u c h.1, h.2⟩) (fun u h => ⟨_, hev u h⟩) ?_ (fun u y w h hy => by
      have : y = "cn" := by simpa [declared, guardS, guardL, ifs] using hy
      subst this; exact ⟨cs_restore h.1 hfw w, h.2⟩) ?_ (fun _ _ _ _ hy => nomatch hy)
  · have hlow : LowKK (guardS (.call "cn" "artNameAt" [v "p"]) ++ [.ret (v "why")]) :=
      lowKK_append (lowK_any _ (k := .skip) rfl) (lowKK_ret rfl)
    refine fragR_conseq (P0 := fun u => ∃ M, RunF s1 (("why", BitVec.ofNat 64 W) :: Hd) (· = M) u ∧
      (ChkM s1 A m0 a gd M ∧ W ≠ 0)) ?_ (fun u ⟨⟨M, hr, hM⟩, hne⟩ => ⟨M, hr, hM, fun e =>
        hne ((hz u ⟨M, hr, hM⟩).2 e)⟩) fun _ h => h
    refine fragR_exists hlow fun M => ?_
    refine fragR_pure (ChkM s1 A m0 a gd M ∧ W ≠ 0) (fun u h => h.2) hlow fun ⟨hM, hW0⟩ => ?_
    refine fragR_conseq (P0 := RunF s1 (("why", BitVec.ofNat 64 W) :: Hd) (· = M)) ?_ (fun u h => h.1)
      fun _ h => h
    refine fragR_append (nameCall_frag o hA hD hcode hlen (rt := "cn") (by decide)
      (l := ("why", BitVec.ofNat 64 W) :: Hd) ha hfw (e1 := v "p") rfl hf hK
      (fun u h => ev_var (vals_lookup h.1.vals hp)) hM.reads.input (chk_broken hM hB.broken)
      (chk_sep hM hB)) ?_
    exact fragR_ret o rfl fun u h => ⟨_, ev_var (vals_lookup h.1.vals rfl), by rw [h.2]; exact hR M hM hW0⟩
  · exact fragR_of (frag_nil o fun u h => ⟨h.1, (hz u h.1).1 h.2⟩)

/-! ## The field's check -/

/-- **What `fieldRefusal` answers**, by the field's entry: its flags, blank lines and rule. -/
theorem fieldNum_eq (f : Field) : fieldNum f = whyOf (flE (classOf esP f.name)) (f.body.any (·.all
    DN.News.CommandSpec.isWS)) (ArticleSpec.grammarSays (ruE (classOf esP f.name)) f.text) := by
  rcases Nat.lt_or_ge (classOf esP f.name) esP.length with h | h
  · rw [fieldNum_class h rfl rfl, ruleOf_class h rfl]
    unfold flE ruE; rw [dif_pos h, dif_pos h]
  · have hk : classOf esP f.name = esP.length := by have := DN.News.ArticleAdded.classOf_le esP f.name; omega
    rw [fieldNum_none hk rfl, ruleOf_none hk]
    unfold flE ruE; rw [dif_neg (by omega), dif_neg (by omega)]

theorem whyOf_eq (F : Nat) (B G : Bool) : whyGram (whyBlank (whyFlags F) B) G = whyOf F B G := by
  unfold whyGram whyBlank whyFlags whyOf
  cases F.testBit 0 <;> cases F.testBit 1 <;> cases F.testBit 2 <;> cases F.testBit 3 <;> cases B <;> cases G <;> rfl

theorem whyFlags_le (F : Nat) : whyFlags F ≤ 9 := by
  unfold whyFlags; split <;> (try split) <;> (try split) <;> (try split) <;> omega
theorem whyBlank_le (W : Nat) (B : Bool) (h : W ≤ 10) : whyBlank W B ≤ 10 := by
  unfold whyBlank; split <;> (try split) <;> omega

theorem chkHead_g : guardL chkHead =
    guardS (.call "fe" "artField" [v "p"]) ++ ([.dec "nl" (wd ArticleProg.xNl)] : Ss) ++
      guardS (.call "k" "artClass" [v "p", v "nl"]) ++
      ([kept "k" (ArticleProg.E esP),
        .dec "fl" (.loadw 1 (eAdd (Syntax.atOff (v "a") (ArticleProg.xFlags esP)) (eMul (v "k") (n 8)))),
        .dec "ru" (.loadw 1 (eAdd (Syntax.atOff (v "a") (ArticleProg.xRuleT esP)) (eMul (v "k") (n 8)))),
        .dec "why" (n 0)] : Ss) ++
      (([.ite (bitE 1) [.assign "why" (n 6)]
        [.ite (bitE 2) [.assign "why" (n 7)]
          [.ite (bitE 4) [.assign "why" (n 8)] [ifs (bitE 8) [.assign "why" (n 9)]]]]]
        : Ss) ++
      (guardS (ifs (eEq (v "why") (n 0)) [.call "bl" "artBlank" [v "p"], ifs (v "bl") [.assign "why" (n 10)]]) ++
      (guardS (ifs (eEq (v "why") (n 0))
        [.call "g" "artGrammar" [v "ru", v "p", v "fe"], ifs (eEq (v "g") (n 0)) [.assign "why" (n 11)]]) ++
      guardS (ifs (v "why") [.call "cn" "artNameAt" [v "p"], .ret (v "why")])))) := rfl

/-- **One field checked** as `fieldRefusal` checks it. A reason is given back with the field's name kept. Else the
locals hold its end, name's length, entry, flags and rule. -/
theorem chk_head (o : Oracle σ) {R : Ret} {A : Word} {s1 : PancakeState σ} (hA : Area ArticleProg.ofs A s1)
    (hD : ArtDom A s1.memaddrs) (hcode : ArtCode s1.code) {m0 : Word → Word} {a : Bytes} (hlen : a.length ≤ artMax)
    {SEP : Nat} (hB : ChkBase s1 A m0 SEP esP)
    (hSI : SEP ≤ inputMax) {gd : List (List (Nat × Nat))} {P e : Nat} {more : List (Nat × Nat)}
    (hf : DN.News.ArticleLines.FieldAt a SEP P e more)
    (hK : DN.News.ArticleLines.nameLen a P e < ArticleProg.nameCap) {REP LID BD : Word}
    (hm : (fieldNum (fieldOf a ((P, e) :: more.takeWhile (cont a))) = 0 ∨
      fieldNum (fieldOf a ((P, e) :: more.takeWhile (cont a))) = 11) →
      ∃ b, matches? AbnfRules.grammar AbnfRules.depth (ArticleSpec.ruleOf (fieldOf a ((P, e) :: more.takeWhile
        (cont a)))) ((fieldOf a ((P, e) :: more.takeWhile (cont a))).text.map BitVec.toNat) = .ok b)
    (hR : ∀ M, ChkM s1 A m0 a gd M → fieldNum (fieldOf a ((P, e) :: more.takeWhile (cont a))) ≠ 0 →
      R (BitVec.ofNat 64 (fieldNum (fieldOf a ((P, e) :: more.takeWhile (cont a))))) (nameMem A s1.be
        (seg a P (P + DN.News.ArticleLines.nameLen a P e)) (DN.News.ArticleLines.nameLen a P e) e M)) :
    FragR o R (guardL chkHead) (ChkSt s1 A m0 a gd (chkL A SEP P REP LID BD))
      (fun u => ChkSt s1 A m0 a gd (("why", 0) :: hdL A SEP P REP LID BD (DN.News.ArticleLines.nextOf a more SEP)
        (DN.News.ArticleLines.nameLen a P e) (classOf esP (seg a P (P + DN.News.ArticleLines.nameLen a P e)))) u ∧
        fieldNum (fieldOf a ((P, e) :: more.takeWhile (cont a))) = 0) := by
  let K := DN.News.ArticleLines.nameLen a P e
  let NX := DN.News.ArticleLines.nextOf a more SEP
  let k := classOf esP (seg a P (P + K))
  let f := fieldOf a ((P, e) :: more.takeWhile (cont a))
  let Hd := hdL A SEP P REP LID BD NX K k
  let F := flE k
  let B := (seg a (P + K + 1) e).all DN.News.CommandSpec.isWS || DN.News.ArticleLines.blankL a more
  let G := setOf (Matches AbnfRules.grammar (inputOf (a.take NX)) (.ref (ruE k)) P) NX
  have hcol := DN.News.ArticleLines.fieldAt_colon hf
  have hmore := (DN.News.ArticleLines.lines_tail hf.lines).2
  have hNXs := DN.News.ArticleLines.lines_sep (DN.News.ArticleAdded.lines_next more (e + 2) hmore)
  have hNXg := (DN.News.ArticleLines.nextOf_ge hmore).1
  have hkf : classOf esP f.name = k := rfl
  have htext : f.text = seg a P NX := DN.News.ArticleAdded.fieldText hf.lines
  have hbody : f.body.any (·.all DN.News.CommandSpec.isWS) = B := body_blank hf.lines hcol.2.1
  have hG : (∃ b, matches? AbnfRules.grammar AbnfRules.depth (ArticleSpec.ruleOf f) (f.text.map BitVec.toNat) = .ok b) →
      G = ArticleSpec.grammarSays (ruE k) (seg a P NX) := fun ⟨b, hb⟩ => by
    have hru : ArticleSpec.ruleOf f = ruE k := by
      rcases Nat.lt_or_ge k esP.length with h | h
      · rw [ruleOf_class h hkf]; unfold ruE; rw [dif_pos h]
      · rw [ruleOf_none (by have := DN.News.ArticleAdded.classOf_le esP f.name; omega)]; unfold ruE
        rw [dif_neg (by omega)]
    rw [hru, htext] at hb
    exact gram_field (by omega) (by omega) hb
  have hfn : fieldNum f = whyGram (whyBlank (whyFlags F) B) (ArticleSpec.grammarSays (ruE k) (seg a P NX)) := by
    rw [whyOf_eq, fieldNum_eq, hkf, hbody, htext]
  have hnum : fieldNum f = whyGram (whyBlank (whyFlags F) B) G := by
    by_cases h0 : whyBlank (whyFlags F) B = 0
    · rw [hG (hm (by rw [hfn, h0]; unfold whyGram; rw [if_pos rfl]; split <;> simp)), hfn]
    · rw [hfn]; unfold whyGram; rw [if_neg h0, if_neg h0]
  have hW5 := whyBlank_le (whyFlags F) B (by have := whyFlags_le F; omega)
  have hHd : ∀ x, x ∈ ["why", "bl", "g", "cn"] → Fresh x Hd = true := fun x hx => by
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl <;> rfl
  rw [chkHead_g]
  refine fragR_append (chk_entry o hA hD hcode hlen hB hf) ?_
  refine fragR_append (chk_bits o (hHd "why" (by simp)) (flE_lt k) rfl) ?_
  refine fragR_append (chk_blank o hA hD hcode hlen hB hf (hHd "why" (by simp)) (hHd "bl" (by simp)) rfl rfl
    (W := whyFlags F) (by have := whyFlags_le F; omega)) ?_
  refine fragR_append (chk_gram o hA hcode hlen hB (k := k) (hHd "why" (by simp)) (hHd "g" (by simp)) rfl rfl rfl rfl
    (by omega) (by omega) (by omega) (W := whyBlank (whyFlags F) B) (by omega)) ?_
  refine fragR_conseq (chk_ret o hA hD hcode hlen hB hf hK (hHd "cn" (by simp)) rfl rfl
    (W := whyGram (whyBlank (whyFlags F) B) G) (by unfold whyGram; split <;> (try split) <;> omega)
    (fun M hM hne => by rw [← hnum] at hne ⊢; exact hR M hM hne)) (fun _ h => h) fun u ⟨h, h0⟩ => ?_
  rw [h0] at h
  exact ⟨h, hnum.trans h0⟩

/-! ## The classes compared -/

theorem entry_of_class {es : List String} {name : Bytes} {k : Nat} (hk : k < es.length)
    (hc : DN.News.ArticleRun.classOf es name = k) :
    entryIs es[k] name = true := by
  have hf : es.findIdx? (entryIs · name) = some k := by
    unfold DN.News.ArticleRun.classOf at hc
    cases h : es.findIdx? (entryIs · name) with
    | none => rw [h, Option.getD_none] at hc; omega
    | some i => rw [h, Option.getD_some] at hc; rw [hc]
  obtain ⟨hk2, he, -⟩ := List.findIdx?_eq_some_iff_getElem.1 hf
  exact he

theorem class_congr {es : List String} {n1 n2 : Bytes} (h : ArticleSpec.sameName n1 n2 = true) :
    DN.News.ArticleRun.classOf es n1 = DN.News.ArticleRun.classOf es n2 := by
  have e : n1.map ArticleSpec.lowerB = n2.map ArticleSpec.lowerB := beq_iff_eq.1 h
  unfold DN.News.ArticleRun.classOf entryIs; rw [e]

/-- **Two names of one entry** are the same name. -/
theorem class_same {n1 n2 : Bytes} {k : Nat} (hk : k < esP.length) (h1 : classOf esP n1 = k) :
    classOf esP n2 = k ↔ ArticleSpec.sameName n2 n1 = true := by
  constructor
  · intro h2
    have e1 := beq_iff_eq.1 (entry_of_class hk h1)
    have e2 := beq_iff_eq.1 (entry_of_class hk h2)
    unfold ArticleSpec.sameName; rw [e1, e2]; exact beq_self_eq_true _
  · intro h; rw [class_congr h, h1]

theorem isSome_firstK (a : Bytes) (gd : List (List (Nat × Nat))) (k : Nat) :
    (firstK a gd k).isSome = gd.any (fun g => classG a g == k) := by
  unfold firstK
  rw [Option.isSome_map]
  apply Bool.eq_iff_iff.2
  rw [List.find?_isSome, List.any_eq_true]

/-- **Some field before of the same name** exactly when the table has its class's first group. -/
theorem seen_firstK {a : Bytes} {gd : List (List (Nat × Nat))} {g : List (Nat × Nat)} (hk : classG a g < esP.length) :
    (([] : List Field) ++ gd.map (fieldOf a)).any (ArticleSpec.sameName ·.name (fieldOf a g).name) =
      (firstK a gd (classG a g)).isSome := by
  rw [isSome_firstK, List.nil_append, List.any_map]
  exact any_congr' fun g' _ => by
    apply Bool.eq_iff_iff.2
    rw [beq_iff_eq]
    exact (class_same hk rfl).symm

/-- **A list the flags read**: its bit in the flags of the field's entry. -/
theorem flE_isOne {name : Bytes} {i : Nat} (hi : i < 8) {l : List String} (hl : ∀ n ∈ l, n ∈ allNames)
    (hil : ∀ s, (flagList ArticleSpec.spec s).getD i false = ArticleProg.isIn l s) :
    l.any (ArticleSpec.named name ·) = (flE (classOf esP name)).testBit i := by
  rcases Nat.lt_or_ge (classOf esP name) esP.length with h | h
  · rw [isOne_class h rfl hl]; unfold flE; rw [dif_pos h, flagsOf_bit, hil, decide_eq_true hi, Bool.true_and]
  · have hk : classOf esP name = esP.length := by have := DN.News.ArticleAdded.classOf_le esP name; omega
    rw [isOne_none hk hl]; unfold flE; rw [dif_neg (by omega), Nat.zero_testBit]

theorem lowerS_received : ArticleProg.lowerS "Received" = "received" := by decide +kernel

theorem received_all : "Received" ∈ allNames := by
  simp only [allNames, List.mem_append]; simp [ArticleProg.readNames]

/-- **Received** by the flags of the field's entry. -/
theorem flE_received (name : Bytes) : ArticleSpec.named name "Received" = (flE (classOf esP name)).testBit 7 := by
  rcases Nat.lt_or_ge (classOf esP name) esP.length with h | h
  · rw [DN.News.ArticleTables.class_named h rfl received_all]; unfold flE
    rw [dif_pos h, flagsOf_bit, decide_eq_true (by decide : 7 < 8), Bool.true_and, lowerS_received]
    show _ = (ArticleProg.lowerS esP[classOf esP name] == "received")
    rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq, eq_comm]
  · have hk : classOf esP name = esP.length := by have := DN.News.ArticleAdded.classOf_le esP name; omega
    rw [DN.News.ArticleTables.class_none hk received_all]; unfold flE; rw [dif_neg (by omega), Nat.zero_testBit]

/-- A date field is not Received. -/
theorem flE_dates (k : Nat) (h : (flE k).testBit 6 = true) : (flE k).testBit 7 = false := by
  unfold flE at h ⊢
  split at h
  · rename_i hk
    rw [dif_pos hk]
    rw [flagsOf_bit, decide_eq_true (by decide : 6 < 8), Bool.true_and] at h
    rw [flagsOf_bit, decide_eq_true (by decide : 7 < 8), Bool.true_and]
    simp only [flagList, List.getD_cons_succ, List.getD_cons_zero] at h ⊢
    cases e : (ArticleProg.lowerS esP[k] == "received")
    · rfl
    · unfold ArticleProg.isIn at h
      rw [beq_iff_eq.1 e] at h
      exact absurd h (by decide +kernel)
  · simp at h

theorem once_bit (name : Bytes) :
    ArticleSpec.spec.once.any (ArticleSpec.named name ·) = (flE (classOf esP name)).testBit 4 :=
  flE_isOne (by decide) lists_names.2.2.2.2.1 fun _ => rfl

theorem ids_bit (name : Bytes) :
    ArticleSpec.idFields.any (ArticleSpec.named name ·) = (flE (classOf esP name)).testBit 5 :=
  flE_isOne (by decide) lists_names.2.2.2.2.2.1 fun _ => rfl

theorem dates_bit (name : Bytes) :
    ArticleProg.dateFields.any (ArticleSpec.named name ·) = (flE (classOf esP name)).testBit 6 :=
  flE_isOne (by decide) lists_names.2.2.2.2.2.2.1 fun _ => rfl

/-! ## What the loop gathers, a field at a time -/

/-- Where the first repeated field starts. -/
def repP (a : Bytes) (gd : List (List (Nat × Nat))) : Option Nat := (repG a [] gd).map placeOf

/-- A field holding a Message-ID too long. -/
def lidQ (a : Bytes) (g : List (Nat × Nat)) : Bool :=
  ArticleSpec.isOne ArticleSpec.idFields (fieldOf a g) &&
    (ArticleSpec.msgIds (fieldOf a g).value).any (·.length > ArticleSpec.spec.idMax)

/-- A field holding a date that means none. -/
def bdQ (a : Bytes) (g : List (Nat × Nat)) : Bool :=
  (ArticleSpec.dateText (fieldOf a g)).any fun t => (ArticleSpec.dateValue t).isNone

/-- Where the first field of a kind starts. -/
def placeBy (q : List (Nat × Nat) → Bool) (gd : List (List (Nat × Nat))) : Option Nat := (gd.find? q).map placeOf

theorem placeBy_snoc (q : List (Nat × Nat) → Bool) (gd : List (List (Nat × Nat))) (g : List (Nat × Nat)) :
    placeBy q (gd ++ [g]) = (placeBy q gd).or (if q g then some (placeOf g) else none) := by
  unfold placeBy; rw [find_snoc, Option.map_or]; cases q g <;> rfl

theorem rep_cond (a : Bytes) (gd : List (List (Nat × Nat))) (g : List (Nat × Nat)) :
    (ArticleSpec.isOne ArticleSpec.spec.once (fieldOf a g) &&
      (([] : List Field) ++ gd.map (fieldOf a)).any (ArticleSpec.sameName ·.name (fieldOf a g).name)) =
      ((flE (classG a g)).testBit 4 && (firstK a gd (classG a g)).isSome) := by
  have h4 : (ArticleSpec.spec.once.any fun x => ArticleSpec.named (fieldOf a g).name x) =
      (flE (classG a g)).testBit 4 := once_bit _
  unfold ArticleSpec.isOne
  rw [h4]
  rcases Nat.lt_or_ge (classG a g) esP.length with h | h
  · rw [seen_firstK h]
  · unfold flE; rw [dif_neg (by omega)]; simp only [Nat.zero_testBit, Bool.false_and]

theorem repP_snoc (a : Bytes) (gd : List (List (Nat × Nat))) (g : List (Nat × Nat)) :
    repP a (gd ++ [g]) = (repP a gd).or (if (flE (classG a g)).testBit 4 && (firstK a gd (classG a g)).isSome then
      some (placeOf g) else none) := by
  unfold repP; rw [repG_snoc, rep_cond, Option.map_or]
  cases (flE (classG a g)).testBit 4 && (firstK a gd (classG a g)).isSome <;> rfl

theorem lidQ_eq (a : Bytes) (g : List (Nat × Nat)) :
    lidQ a g = ((flE (classG a g)).testBit 5 &&
      (ArticleSpec.msgIds (fieldOf a g).value).any (·.length > ArticleSpec.spec.idMax)) := by
  unfold lidQ ArticleSpec.isOne; rw [ids_bit]; rfl

/-- The date a field's check reads, by the flags of its entry. -/
theorem bdQ_eq (a : Bytes) (g : List (Nat × Nat)) :
    bdQ a g = if (flE (classG a g)).testBit 6 then (ArticleSpec.dateValue (fieldOf a g).value).isNone
      else if (flE (classG a g)).testBit 7 then
        (ArticleSpec.dateValue (ArticleSpec.receivedDate 0 0 (fieldOf a g).value)).isNone
      else false := by
  unfold bdQ ArticleSpec.dateText
  rw [show ["Date", "Injection-Date", "Expires", "Resent-Date"] = ArticleProg.dateFields from rfl, dates_bit,
    flE_received]
  change Option.any _ (if (flE (classG a g)).testBit 6 = true then _ else
    if (flE (classG a g)).testBit 7 = true then _ else none) = _
  by_cases h6 : (flE (classG a g)).testBit 6 = true
  · rw [if_pos h6, if_pos h6]; rfl
  · rw [if_neg h6, if_neg h6]
    by_cases h7 : (flE (classG a g)).testBit 7 = true
    · rw [if_pos h7, if_pos h7]; rfl
    · rw [if_neg h7, if_neg h7]; rfl

/-! ## The table and the repeated field -/

theorem repG_mem {a : Bytes} : ∀ {gd : List (List (Nat × Nat))} {seen : List Field} {g : List (Nat × Nat)},
    repG a seen gd = some g → g ∈ gd
  | [], _, _, h => nomatch h
  | g' :: gd, seen, g, h => by
    unfold repG at h
    split at h
    · cases h; exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (repG_mem h)

/-- Places below `2 ^ 63`, each a group's. -/
def Placed (gd : List (List (Nat × Nat))) : Prop := ∀ g ∈ gd, placeOf g < 2 ^ 63

theorem firstK_small {a : Bytes} {gd : List (List (Nat × Nat))} (hs : Placed gd) {k : Nat} :
    ∀ x, firstK a gd k = some x → x < 2 ^ 63 := fun x h => by
  unfold firstK at h
  cases hf : gd.find? (fun g => classG a g == k) with
  | none => rw [hf] at h; nomatch h
  | some g => rw [hf] at h; cases h; exact hs g (List.mem_of_find?_eq_some hf)

theorem placeBy_small {q : List (Nat × Nat) → Bool} {gd : List (List (Nat × Nat))} (hs : Placed gd) :
    ∀ x, placeBy q gd = some x → x < 2 ^ 63 := fun x h => by
  unfold placeBy at h
  cases hf : gd.find? q with
  | none => rw [hf] at h; nomatch h
  | some g => rw [hf] at h; cases h; exact hs g (List.mem_of_find?_eq_some hf)

theorem repP_small {a : Bytes} {gd : List (List (Nat × Nat))} (hs : Placed gd) :
    ∀ x, repP a gd = some x → x < 2 ^ 63 := fun x h => by
  unfold repP at h
  cases hf : repG a [] gd with
  | none => rw [hf] at h; nomatch h
  | some g => rw [hf] at h; cases h; exact hs g (repG_mem hf)

theorem idxA_eval {u : PancakeState σ} {A : Word} (ha : u.locals "a" = some A) {k : Nat}
    (hk : u.locals "k" = some (BitVec.ofNat 64 k)) {x : Nat} :
    eval u (.op .add (.op .add (.var "a") (.const (BitVec.ofNat 64 x)))
      (.mul (.var "k") (.const (BitVec.ofNat 64 8)))) =
      some (at_ A (x + 8 * k)) := by
  simp only [eval, ha, hk]; rw [at_mul]

/-- The locals in the tail of the loop's body. -/
def tlL (A : Word) (SEP P NX K k : Nat) (FK REP LID BD : Word) : List (String × Value) :=
  ("fk", FK) :: ("why", 0) :: hdL A SEP P REP LID BD NX K k

theorem tl_rep (A : Word) (SEP P NX K k : Nat) (FK REP LID BD : Word) : tlL A SEP P NX K k FK REP LID BD =
    [("fk", FK), ("why", 0), ("ru", BitVec.ofNat 64 (ruE k)), ("fl", BitVec.ofNat 64 (flE k)), ("k", BitVec.ofNat 64 k),
      ("nl", BitVec.ofNat 64 K), ("fe", BitVec.ofNat 64 NX), ("p", BitVec.ofNat 64 P), ("bd", BD), ("lid", LID)] ++
      ("rep", REP) :: [("sep", BitVec.ofNat 64 SEP), ("a", A)] := rfl

/-- **The field's place in the table** if its class has none yet. Else the repeated field's, if it may appear once. -/
theorem chk_first (o : Oracle σ) {R : Ret} {A : Word} {s1 : PancakeState σ} (hA : Area ArticleProg.ofs A s1)
    {m0 : Word → Word} {a : Bytes} (hlen : a.length ≤ artMax) {SEP : Nat} (hB : ChkBase s1 A m0 SEP esP)
    {gd : List (List (Nat × Nat))} (hs : Placed gd) {P e NX K : Nat} {more : List (Nat × Nat)} {LID BD : Word} :
    FragR o R [.dec "fk" (.loadw 1 (eAdd (Syntax.atOff (v "a") ArticleProg.xFirst) (eMul (v "k") (n 8)))),
      .ite (eLt (v "fk") (n 0)) [.store (eAdd (Syntax.atOff (v "a") ArticleProg.xFirst) (eMul (v "k") (n 8))) (v "p")]
        [ifs (eAnd (bitE 16) (eLt (v "rep") (n 0))) [.assign "rep" (v "p")]]]
      (ChkSt s1 A m0 a gd (("why", 0) :: hdL A SEP P (optW (repP a gd)) LID BD NX K
        (classG a ((P, e) :: more.takeWhile (cont a)))))
      (ChkSt s1 A m0 a (gd ++ [(P, e) :: more.takeWhile (cont a)]) (tlL A SEP P NX K
        (classG a ((P, e) :: more.takeWhile (cont a)))
        (optW (firstK a gd (classG a ((P, e) :: more.takeWhile (cont a)))))
        (optW (repP a (gd ++ [(P, e) :: more.takeWhile (cont a)]))) LID BD)) := by
  let g := (P, e) :: more.takeWhile (cont a)
  let k := classG a g
  have hk : k ≤ esP.length := DN.News.ArticleAdded.classOf_le esP _
  have hF := xFirst_eq
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := DN.News.ArticleTables.lay esP
  have hdm : s1.memaddrs (at_ A (ArticleProg.xFirst + 8 * k)) = true := DN.News.ArticleAdded.first_dom hB.tdom hk
  have hx0 : (ArticleProg.xFirst == 0) = false := by rw [hF]; rfl
  refine fragR_append (xs := [_]) (cs_dec o (idx_lower hx0) rfl (val := optW (firstK a gd k)) fun u M h hM => by
    rw [idx_eval (vals_lookup h.1.vals rfl) (vals_lookup h.1.vals rfl) h.1.memaddrs hdm, h.2]
    exact congrArg some (hM.first k hk)) ?_
  refine fragR_if o rfl (lowK_any _ (k := .skip) rfl) (lowK_any _ (k := .skip) rfl) cs_clock
    (fun _ _ _ _ hy => nomatch hy) (fun _ _ _ _ hy => by simp [declared, ifs] at hy)
    (b := (firstK a gd k).isNone) (fun u ⟨_, hr, _⟩ => DN.News.ArticleAdded.lt0_eval (firstK_small hs)
      (ev_var (vals_lookup hr.1.vals rfl))) (fun hn => ?_) fun hn => ?_
  · have hn' : firstK a gd k = none := Option.isNone_iff_eq_none.1 hn
    have hrep : repP a (gd ++ [g]) = repP a gd := by
      rw [repP_snoc, hn']; simp
    rw [hrep]
    refine cs_lift o (lowK_any _ (k := .skip) rfl) fun M hM => ?_
    refine fragR_of (frag_conseq (runF_storeA o (idxA_lower hx0 "k") rfl hdm
      (fun u h => idxA_eval (vals_lookup h.1.vals rfl) (vals_lookup h.1.vals rfl))
      (val := fun _ => BitVec.ofNat 64 P) (fun u h => ev_var (vals_lookup h.1.vals rfl))
      (G := (· = upd M (at_ A (ArticleProg.xFirst + 8 * k)) (BitVec.ofNat 64 P))) fun m hm => by rw [hm])
      (fun _ h => h) fun u h => ⟨_, h, chkM_store hA.hA hlen hM hk hn'⟩)
  · obtain ⟨p0, hp0⟩ := Option.isSome_iff_exists.1 (by simpa using hn : (firstK a gd k).isSome = true)
    refine fragR_conseq (P0 := ChkSt s1 A m0 a (gd ++ [g]) (tlL A SEP P NX K k (optW (firstK a gd k))
      (optW (repP a gd)) LID BD)) ?_ (fun u ⟨M, hr, hM⟩ => ⟨M, hr, chkM_seen hM hp0⟩) fun _ h => h
    have hsome : (firstK a gd k).isSome = true := by rw [hp0]; rfl
    refine fragR_if o rfl (lowK_any _ (k := .skip) rfl) (lowK_any _ (k := .skip) rfl) cs_clock
      (fun _ _ _ _ hy => nomatch hy) (fun _ _ _ _ hy => nomatch hy)
      (b := (flE k).testBit 4 && (repP a gd).isNone) (fun u h => DN.News.FramerCode.eval_and
        (cs_bit (flE_lt k) rfl (i := 4) (by decide) h)
        (let ⟨_, hr, _⟩ := h; DN.News.ArticleAdded.lt0_eval (repP_small hs) (ev_var (vals_lookup hr.1.vals rfl))))
      (fun hb => ?_) fun hb => ?_
    · have ⟨hb4, hbn⟩ := Bool.and_eq_true_iff.1 hb
      have hrep : repP a (gd ++ [g]) = some P := by
        rw [repP_snoc, Option.isNone_iff_eq_none.1 hbn, hb4, hsome]; rfl
      rw [hrep, tl_rep, tl_rep]
      exact set_in o _ _ rfl rfl rfl fun u M h => ev_var (vals_lookup h.1.vals rfl)
    · have hrep : repP a (gd ++ [g]) = repP a gd := by
        rw [repP_snoc, hsome, Bool.and_true]
        cases h4 : (flE k).testBit 4
        · simp
        · rw [h4, Bool.true_and] at hb
          obtain ⟨x, hx⟩ := Option.isSome_iff_exists.1 (by simpa using hb : (repP a gd).isSome = true)
          rw [hx]; rfl
      rw [hrep]
      exact fragR_of (frag_nil o fun _ h => h)

/-! ## The long identifier -/

/-- **A Message-ID too long**, looked for in a field of the identifiers' when none is found yet. -/
theorem chk_lid (o : Oracle σ) {R : Ret} {A : Word} {s1 : PancakeState σ} (hA : Area ArticleProg.ofs A s1)
    (hD : ArtDom A s1.memaddrs) (hcode : ArtCode s1.code) {m0 : Word → Word} {a : Bytes} (hlen : a.length ≤ artMax)
    {SEP : Nat} (hB : ChkBase s1 A m0 SEP esP) {gd gd2 : List (List (Nat × Nat))} (hs : Placed gd)
    {g : List (Nat × Nat)} {VS VE : Nat} (hVS : VS ≤ VE) (hVE : VE ≤ a.length)
    (hval : (fieldOf a g).value = seg a VS VE)
    {P NX K : Nat} (hPg : placeOf g = P) {FK REP BD : Word} :
    FragR o R (guardS (ifs (eAnd (bitE 32) (eLt (v "lid") (n 0)))
        [.call "ml" "artMsgIds" [v "vs", v "ve"], ifs (v "ml") [.assign "lid" (v "p")]]))
      (ChkSt s1 A m0 a gd2 (("ve", BitVec.ofNat 64 VE) :: ("vs", BitVec.ofNat 64 VS) ::
        tlL A SEP P NX K (classG a g) FK REP (optW (placeBy (lidQ a) gd)) BD))
      (ChkSt s1 A m0 a gd2 (("ve", BitVec.ofNat 64 VE) :: ("vs", BitVec.ofNat 64 VS) ::
        tlL A SEP P NX K (classG a g) FK REP (optW (placeBy (lidQ a) (gd ++ [g]))) BD)) := by
  let k := classG a g
  let LB := (ArticleSpec.msgIds (seg a VS VE)).any (·.length > ArticleSpec.spec.idMax)
  have hq : lidQ a g = ((flE k).testBit 5 && LB) := by rw [lidQ_eq, hval]
  have hsnoc := placeBy_snoc (lidQ a) gd g
  rw [hPg, hq] at hsnoc
  refine fragR_if o rfl (lowK_any _ (k := .skip) rfl) (lowK_any _ (k := .skip) rfl) cs_clock
    (fun u y w h hy => by
      have : y = "ml" := by simpa [declared, guardS, guardL, ifs] using hy
      subst this; exact cs_restore h rfl w)
    (fun _ _ _ _ hy => nomatch hy) (b := (flE k).testBit 5 && (placeBy (lidQ a) gd).isNone)
    (fun u h => DN.News.FramerCode.eval_and (cs_bit (flE_lt k) rfl (i := 5) (by decide) h)
      (let ⟨_, hr, _⟩ := h; DN.News.ArticleAdded.lt0_eval (placeBy_small hs) (ev_var (vals_lookup hr.1.vals rfl))))
    (fun hb => ?_) fun hb => ?_
  · obtain ⟨hb5, hbn⟩ := Bool.and_eq_true_iff.1 hb
    rw [hsnoc, Option.isNone_iff_eq_none.1 hbn, hb5, Bool.true_and]
    refine fragR_append (xs := guardS (.call "ml" "artMsgIds" [v "vs", v "ve"]))
      (M := ChkSt s1 A m0 a gd2 (("ml", bw LB) :: ("ve", BitVec.ofNat 64 VE) :: ("vs", BitVec.ofNat 64 VS) ::
        tlL A SEP P NX K k FK REP (optW none) BD))
      (cs_lift o (lowK_any _ (k := .skip) rfl) fun M hM => ?_) ?_
    · refine fragR_conseq (DN.News.ArticleAdded.idsCall_frag o hA hD hcode (rt := "ml") (by decide)
        (l := ("ve", BitVec.ofNat 64 VE) :: ("vs", BitVec.ofNat 64 VS) :: tlL A SEP P NX K k FK REP (optW none) BD)
        rfl rfl (chk_broken hM hB.broken) hlen hM.reads.input hVS hVE (e1 := v "vs") (e2 := v "ve") rfl rfl
        (fun u h => ev_var (vals_lookup h.1.vals rfl)) (fun u h => ev_var (vals_lookup h.1.vals rfl)))
        (fun _ h => h) fun u ⟨w, m, h, hw, w1, w2, hm, _⟩ => ?_
      subst hw
      refine ⟨m, h, chkM_hi hA.hA hlen hM fun x hx => ?_⟩
      rw [hm, upd_ne _ fun e => hx (.inr (.inr (.inr (.inr e)))), upd_ne _ fun e => hx (.inr (.inr (.inr (.inl e))))]
    refine fragR_if o rfl (lowK_any _ (k := .skip) rfl) (lowK_any _ (k := .skip) rfl) cs_clock
      (fun _ _ _ _ hy => nomatch hy) (fun _ _ _ _ hy => nomatch hy) (b := LB)
      (fun u ⟨_, hr, _⟩ => ev_var (vals_lookup hr.1.vals rfl)) (fun hl => ?_) fun hl => ?_
    · rw [if_pos hl]
      have := set_in o (R := R) (s1 := s1) (A := A) (m0 := m0) (a := a) (gd := gd2) (x := "lid")
        ([("ml", bw LB), ("ve", BitVec.ofNat 64 VE), ("vs", BitVec.ofNat 64 VS), ("fk", FK), ("why", 0),
          ("ru", BitVec.ofNat 64 (ruE k)), ("fl", BitVec.ofNat 64 (flE k)), ("k", BitVec.ofNat 64 k),
          ("nl", BitVec.ofNat 64 K), ("fe", BitVec.ofNat 64 NX), ("p", BitVec.ofNat 64 P), ("bd", BD)])
        [("rep", REP), ("sep", BitVec.ofNat 64 SEP), ("a", A)] rfl rfl (w0 := optW none) (e := v "p") rfl
        (val := BitVec.ofNat 64 P) fun u M h => ev_var (vals_lookup h.1.vals rfl)
      exact fragR_conseq this (fun _ h => h) fun u h => cs_sub h fun q hq => List.mem_cons_of_mem _ hq
    · rw [if_neg (by simp [hl])]
      exact fragR_of (frag_nil o fun u h => cs_sub h fun q hq => List.mem_cons_of_mem _ hq)
  · have hl : (if ((flE k).testBit 5 && LB) = true then some P else none).isNone ∨
        (placeBy (lidQ a) gd).isSome := by
      cases h5 : (flE k).testBit 5
      · left; simp
      · rw [h5, Bool.true_and] at hb; right; simpa using hb
    have he : placeBy (lidQ a) (gd ++ [g]) = placeBy (lidQ a) gd := by
      rw [hsnoc]
      rcases hl with hl | hl
      · rw [Option.isNone_iff_eq_none.1 hl]; cases placeBy (lidQ a) gd <;> rfl
      · obtain ⟨x, hx⟩ := Option.isSome_iff_exists.1 hl; rw [hx]; rfl
    rw [he]
    exact fragR_of (frag_nil o fun _ h => h)

/-! ## The date that means none -/

/-- **The date's start**: Received's past its tokens, else the value's. -/
theorem chk_ds (o : Oracle σ) {R : Ret} {A : Word} {s1 : PancakeState σ} (hA : Area ArticleProg.ofs A s1)
    (hcode : ArtCode s1.code) {m0 : Word → Word} {a : Bytes} (hlen : a.length ≤ artMax) {SEP : Nat}
    (hB : ChkBase s1 A m0 SEP esP) {gd : List (List (Nat × Nat))} {L : List (String × Value)}
    (ha : L.lookup "a" = some A)
    {VS VE F : Nat} (hF : F < 256) (hvs : L.lookup "vs" = some (BitVec.ofNat 64 VS))
    (hve : L.lookup "ve" = some (BitVec.ofNat 64 VE)) (hfl : L.lookup "fl" = some (BitVec.ofNat 64 F))
    (hrd : Fresh "rd" L = true) (hds : Fresh "ds" L = true) (hVS : VS ≤ VE) (hVE : VE ≤ a.length) :
    FragR o R (guardS (ifs (bitE 128) [.call "rd" "artReceived" [v "vs", v "ve"], .assign "ds" (v "rd")]))
      (ChkSt s1 A m0 a gd (("ds", BitVec.ofNat 64 VS) :: L))
      (fun u => ∃ D, ChkSt s1 A m0 a gd (("ds", BitVec.ofNat 64 D) :: L) u ∧ D ≤ VE ∧
        seg a D VE = if F.testBit 7 then ArticleSpec.receivedDate 0 0 (seg a VS VE) else seg a VS VE) := by
  have hrd' : Fresh "rd" (("ds", BitVec.ofNat 64 VS) :: L) = true := by
    simp only [Fresh, List.all_cons]; exact Bool.and_eq_true_iff.2 ⟨rfl, hrd⟩
  refine fragR_if o rfl (lowK_any _ (k := .skip) rfl) (lowK_any _ (k := .skip) rfl)
    (fun u c ⟨D, h, h1⟩ => ⟨D, cs_clock u c h, h1⟩) (fun u y w ⟨D, h, h1⟩ hy => by
      have : y = "rd" := by simpa [declared, guardS, guardL, ifs] using hy
      subst this
      exact ⟨D, cs_restore h (by simp only [Fresh, List.all_cons]; exact Bool.and_eq_true_iff.2 ⟨rfl, hrd⟩) w, h1⟩)
    (fun _ _ _ _ hy => nomatch hy) (b := F.testBit 7) (fun u h => cs_bit hF (by
      rw [List.lookup_cons, beq_false_of_ne (by decide)]; exact hfl) (i := 7) (by decide) h)
    (fun h7 => ?_) fun h7 => ?_
  · have hlow : LowKK (guardS (.call "rd" "artReceived" [v "vs", v "ve"]) ++ [.assign "ds" (v "rd")]) :=
      lowK_any _ (k := .skip) rfl
    refine cs_lift o hlow fun M hM => ?_
    have hl : ∀ x, x ≠ "ds" → (("ds", BitVec.ofNat 64 VS) :: L).lookup x = L.lookup x := fun x hx => by
      rw [List.lookup_cons, beq_false_of_ne hx]
    refine fragR_append (DN.News.ArticleFields.recvCall_frag o hA hcode hlen (rt := "rd") (by decide)
      (l := ("ds", BitVec.ofNat 64 VS) :: L) ((hl "a" (by decide)).trans ha) hrd' (chk_broken hM hB.broken)
      hM.reads.input hVS hVE (e1 := v "vs") (e2 := v "ve") rfl rfl
      (fun u h => ev_var (vals_lookup h.1.vals ((hl "vs" (by decide)).trans hvs)))
      (fun u h => ev_var (vals_lookup h.1.vals ((hl "ve" (by decide)).trans hve)))) ?_
    refine fragR_exists (lowK_any _ (k := .skip) rfl) fun Q => ?_
    refine fragR_pure (VS ≤ Q ∧ Q ≤ VE ∧ seg a Q VE = ArticleSpec.receivedDate 0 0 (seg a VS VE)) (fun u h => h.2)
      (lowK_any _ (k := .skip) rfl) fun ⟨h1, h2, h3⟩ => ?_
    refine fragR_conseq (fragR_of (runF_set o rfl (x := "ds") (w := BitVec.ofNat 64 VS) rfl (v := BitVec.ofNat 64 Q)
      fun u h => ev_var (vals_lookup h.1.vals rfl))) (fun u h => h.1) fun u h => ⟨Q, ⟨M, runF_mono h (fun q hq => ?_)
        fun _ h => h, hM⟩, h2, by rw [if_pos h7]; exact h3⟩
    rcases List.mem_cons.1 hq with rfl | hq
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (mem_without (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hq))
        (fresh_mem hds hq))
  · exact fragR_of (frag_nil o fun u h => ⟨VS, h, hVS, by rw [if_neg (by simp [h7])]⟩)

/-- What the date says, as `artDate` answers: 0 for none. -/
theorem date_ans {A : Word} {a : Bytes} {S E : Nat} {m0 : Word → Word} {w : Word} {m : Word → Word}
    (h : DN.News.ArticleDateOk.DateRet A a S E m0 w m) :
    ∃ x, w = BitVec.ofNat 64 x ∧ x < 3 ∧ (x = 0 ↔ (ArticleSpec.dateValue (seg a S E)).isNone = true) := by
  rcases h.2 with ⟨rfl, h0⟩ | ⟨rfl, t, ht, -⟩ | ⟨rfl, t, ht, -⟩
  · exact ⟨0, rfl, by decide, by simp [h0]⟩
  · exact ⟨1, rfl, by decide, by simp [ht]⟩
  · exact ⟨2, rfl, by decide, by simp [ht]⟩

theorem bdQ_cond (a : Bytes) (g : List (Nat × Nat)) {VS VE : Nat} (hval : (fieldOf a g).value = seg a VS VE) :
    bdQ a g = (((flE (classG a g)).testBit 6 || (flE (classG a g)).testBit 7) &&
      (ArticleSpec.dateValue (if (flE (classG a g)).testBit 7 then ArticleSpec.receivedDate 0 0 (seg a VS VE)
        else seg a VS VE)).isNone) := by
  rw [bdQ_eq, hval]
  cases h6 : (flE (classG a g)).testBit 6
  · cases h7 : (flE (classG a g)).testBit 7 <;> simp
  · rw [flE_dates _ h6]; simp

/-- **A date that means none**, looked for in a field of the dates' or Received when none is found yet. -/
theorem chk_bd (o : Oracle σ) {R : Ret} {A : Word} {s1 : PancakeState σ} (hA : Area ArticleProg.ofs A s1)
    (hD : ArtDom A s1.memaddrs) (hcode : ArtCode s1.code) {m0 : Word → Word} {a : Bytes} (hlen : a.length ≤ artMax)
    {SEP : Nat} (hB : ChkBase s1 A m0 SEP esP) {gd gd2 : List (List (Nat × Nat))} (hs : Placed gd)
    {g : List (Nat × Nat)} {VS VE : Nat} (hVS : VS ≤ VE) (hVE : VE ≤ a.length)
    (hval : (fieldOf a g).value = seg a VS VE)
    {P NX K : Nat} (hPg : placeOf g = P) {FK REP LID : Word} :
    FragR o R (guardS (ifs (eAnd (or2 (bitE 64) (bitE 128)) (eLt (v "bd") (n 0)))
        [.dec "ds" (v "vs"),
         ifs (bitE 128) [.call "rd" "artReceived" [v "vs", v "ve"], .assign "ds" (v "rd")],
         .call "dv" "artDate" [v "ds", v "ve"], ifs (eEq (v "dv") (n 0)) [.assign "bd" (v "p")]]))
      (ChkSt s1 A m0 a gd2 (("ve", BitVec.ofNat 64 VE) :: ("vs", BitVec.ofNat 64 VS) ::
        tlL A SEP P NX K (classG a g) FK REP LID (optW (placeBy (bdQ a) gd))))
      (ChkSt s1 A m0 a gd2 (("ve", BitVec.ofNat 64 VE) :: ("vs", BitVec.ofNat 64 VS) ::
        tlL A SEP P NX K (classG a g) FK REP LID (optW (placeBy (bdQ a) (gd ++ [g]))))) := by
  let k := classG a g
  let F := flE k
  let DT := if F.testBit 7 then ArticleSpec.receivedDate 0 0 (seg a VS VE) else seg a VS VE
  let VL := fun (BD : Word) => ("ve", BitVec.ofNat 64 VE) :: ("vs", BitVec.ofNat 64 VS) ::
    tlL A SEP P NX K k FK REP LID BD
  have hsnoc := placeBy_snoc (bdQ a) gd g
  rw [hPg, bdQ_cond a g hval] at hsnoc
  refine fragR_if o rfl (lowK_any _ (k := .skip) rfl) (lowK_any _ (k := .skip) rfl) cs_clock
    (fun u y w h hy => by
      have : y = "ds" ∨ y = "dv" := by simpa [declared, guardS, guardL, ifs] using hy
      rcases this with rfl | rfl
      · exact cs_restore h rfl w
      · exact cs_restore h rfl w)
    (fun _ _ _ _ hy => nomatch hy) (b := (F.testBit 6 || F.testBit 7) && (placeBy (bdQ a) gd).isNone)
    (fun u h => DN.News.FramerCode.eval_and (DN.News.FramerCode.eval_or2
        (cs_bit (flE_lt k) rfl (i := 6) (by decide) h) (cs_bit (flE_lt k) rfl (i := 7) (by decide) h))
      (let ⟨_, hr, _⟩ := h; DN.News.ArticleAdded.lt0_eval (placeBy_small hs) (ev_var (vals_lookup hr.1.vals rfl))))
    (fun hb => ?_) fun hb => ?_
  · obtain ⟨hb67, hbn⟩ := Bool.and_eq_true_iff.1 hb
    rw [hsnoc, Option.isNone_iff_eq_none.1 hbn, hb67, Bool.true_and]
    refine fragR_append (xs := [.dec "ds" (v "vs")]) (cs_dec o rfl rfl (val := BitVec.ofNat 64 VS)
      fun u M h _ => ev_var (vals_lookup h.1.vals rfl)) ?_
    refine fragR_append (chk_ds o hA hcode hlen hB (L := VL (optW none)) rfl (flE_lt k) rfl rfl rfl rfl rfl hVS hVE) ?_
    have hlow : LowKK (guardS (.call "dv" "artDate" [v "ds", v "ve"]) ++
        guardS (ifs (eEq (v "dv") (n 0)) [.assign "bd" (v "p")])) := lowK_any _ (k := .skip) rfl
    refine fragR_exists hlow fun D => ?_
    refine fragR_pure (D ≤ VE ∧ seg a D VE = DT) (fun u h => h.2) hlow fun ⟨hD1, hD2⟩ => ?_
    refine fragR_conseq (P0 := ChkSt s1 A m0 a gd2 (("ds", BitVec.ofNat 64 D) :: VL (optW none))) ?_ (fun u h => h.1)
      fun _ h => h
    refine fragR_append (M := fun u => ∃ x,
      ChkSt s1 A m0 a gd2 (("dv", BitVec.ofNat 64 x) :: ("ds", BitVec.ofNat 64 D) ::
      VL (optW none)) u ∧ x < 3 ∧ (x = 0 ↔ (ArticleSpec.dateValue DT).isNone = true))
      (cs_lift o (lowK_any _ (k := .skip) rfl) fun M hM => ?_) ?_
    · refine fragR_conseq (dateCall_frag o hA hD hcode hlen (rt := "dv") (by decide)
        (l := ("ds", BitVec.ofNat 64 D) :: VL (optW none)) rfl rfl hM.reads.pows (chk_broken hM hB.broken)
        hM.reads.input hD1 hVE (e1 := v "ds") (e2 := v "ve") rfl rfl
        (fun u h => ev_var (vals_lookup h.1.vals rfl)) (fun u h => ev_var (vals_lookup h.1.vals rfl)))
        (fun _ h => h) fun u ⟨w, m, h, hr⟩ => ?_
      obtain ⟨x, rfl, hx3, hx0⟩ := date_ans hr
      refine ⟨x, ⟨m, h, chkM_hi hA.hA hlen hM fun y hy => hr.1 y fun hsc => hy (.inr (.inr (.inl hsc)))⟩, hx3, ?_⟩
      rw [← hD2]; exact hx0
    refine fragR_exists (lowK_any _ (k := .skip) rfl) fun x => ?_
    refine fragR_pure (x < 3 ∧ (x = 0 ↔ (ArticleSpec.dateValue DT).isNone = true)) (fun u h => h.2)
      (lowK_any _ (k := .skip) rfl) fun ⟨hx3, hx0⟩ => ?_
    refine fragR_conseq ?_ (fun u h => h.1) fun _ h => h
    refine fragR_if o rfl (lowK_any _ (k := .skip) rfl) (lowK_any _ (k := .skip) rfl) cs_clock
      (fun _ _ _ _ hy => nomatch hy) (fun _ _ _ _ hy => nomatch hy) (b := decide (x = 0))
      (fun u h => cs_eq0 (by omega) rfl h) (fun h0 => ?_) fun h0 => ?_
    · rw [if_pos (hx0.1 (of_decide_eq_true h0))]
      have := set_in o (R := R) (s1 := s1) (A := A) (m0 := m0) (a := a) (gd := gd2) (x := "bd")
        ([("dv", BitVec.ofNat 64 x), ("ds", BitVec.ofNat 64 D), ("ve", BitVec.ofNat 64 VE), ("vs", BitVec.ofNat 64 VS),
          ("fk", FK), ("why", 0), ("ru", BitVec.ofNat 64 (ruE k)), ("fl", BitVec.ofNat 64 (flE k)),
          ("k", BitVec.ofNat 64 k), ("nl", BitVec.ofNat 64 K), ("fe", BitVec.ofNat 64 NX), ("p", BitVec.ofNat 64 P)])
        [("lid", LID), ("rep", REP), ("sep", BitVec.ofNat 64 SEP), ("a", A)] rfl rfl (w0 := optW none) (e := v "p") rfl
        (val := BitVec.ofNat 64 P) fun u M h => ev_var (vals_lookup h.1.vals rfl)
      exact fragR_conseq this (fun _ h => h) fun u h => cs_sub h fun q hq =>
        List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hq)
    · rw [if_neg (fun e => absurd (hx0.2 e) (of_decide_eq_false h0))]
      exact fragR_of (frag_nil o fun u h => cs_sub h fun q hq => List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hq))
  · have he : placeBy (bdQ a) (gd ++ [g]) = placeBy (bdQ a) gd := by
      rw [hsnoc]
      cases h67 : (F.testBit 6 || F.testBit 7)
      · rw [Bool.false_and]; cases placeBy (bdQ a) gd <;> rfl
      · rw [h67, Bool.true_and] at hb
        obtain ⟨y, hy⟩ := Option.isSome_iff_exists.1 (by simpa using hb : (placeBy (bdQ a) gd).isSome = true)
        rw [hy]; rfl
    rw [he]
    exact fragR_of (frag_nil o fun _ h => h)

/-! ## The field's tail -/

theorem chkTail_g : guardL chkTail =
    [.dec "fk" (.loadw 1 (eAdd (Syntax.atOff (v "a") ArticleProg.xFirst) (eMul (v "k") (n 8)))),
      .ite (eLt (v "fk") (n 0)) [.store (eAdd (Syntax.atOff (v "a") ArticleProg.xFirst) (eMul (v "k") (n 8))) (v "p")]
        [ifs (eAnd (bitE 16) (eLt (v "rep") (n 0))) [.assign "rep" (v "p")]]] ++
    ([.dec "vs" (eAdd (eAdd (v "p") (v "nl")) (n 1)), .dec "ve" (eSub (v "fe") (n 2))] ++
    (guardS (ifs (eAnd (bitE 32) (eLt (v "lid") (n 0)))
        [.call "ml" "artMsgIds" [v "vs", v "ve"], ifs (v "ml") [.assign "lid" (v "p")]]) ++
    (guardS (ifs (eAnd (or2 (bitE 64) (bitE 128)) (eLt (v "bd") (n 0)))
        [.dec "ds" (v "vs"),
         ifs (bitE 128) [.call "rd" "artReceived" [v "vs", v "ve"], .assign "ds" (v "rd")],
         .call "dv" "artDate" [v "ds", v "ve"], ifs (eEq (v "dv") (n 0)) [.assign "bd" (v "p")]]) ++
    [.assign "p" (v "fe")]))) := rfl

/-- **The rest of a field's turn.** It keeps its class's first group, the repeated field, the long identifier and
the date that means none. The loop moves past it. -/
theorem chk_tail (o : Oracle σ) {R : Ret} {A : Word} {s1 : PancakeState σ} (hA : Area ArticleProg.ofs A s1)
    (hD : ArtDom A s1.memaddrs) (hcode : ArtCode s1.code) {m0 : Word → Word} {a : Bytes} (hlen : a.length ≤ artMax)
    {SEP : Nat} (hB : ChkBase s1 A m0 SEP esP) {gd : List (List (Nat × Nat))} (hs : Placed gd) {P e : Nat}
    {more : List (Nat × Nat)} (hf : DN.News.ArticleLines.FieldAt a SEP P e more) :
    FragR o R (guardL chkTail)
      (ChkSt s1 A m0 a gd (("why", 0) :: hdL A SEP P (optW (repP a gd)) (optW (placeBy (lidQ a) gd))
        (optW (placeBy (bdQ a) gd)) (DN.News.ArticleLines.nextOf a more SEP) (DN.News.ArticleLines.nameLen a P e)
        (classG a ((P, e) :: more.takeWhile (cont a)))))
      (ChkSt s1 A m0 a (gd ++ [(P, e) :: more.takeWhile (cont a)]) (chkL A SEP (DN.News.ArticleLines.nextOf a more SEP)
        (optW (repP a (gd ++ [(P, e) :: more.takeWhile (cont a)])))
        (optW (placeBy (lidQ a) (gd ++ [(P, e) :: more.takeWhile (cont a)])))
        (optW (placeBy (bdQ a) (gd ++ [(P, e) :: more.takeWhile (cont a)]))))) := by
  let g := (P, e) :: more.takeWhile (cont a)
  let K := DN.News.ArticleLines.nameLen a P e
  let NX := DN.News.ArticleLines.nextOf a more SEP
  let k := classG a g
  have hcol := DN.News.ArticleLines.fieldAt_colon hf
  have hmore := (DN.News.ArticleLines.lines_tail hf.lines).2
  have hNXs := DN.News.ArticleLines.lines_sep (DN.News.ArticleAdded.lines_next more (e + 2) hmore)
  have hNXg := (DN.News.ArticleLines.nextOf_ge hmore).1
  have hval : (fieldOf a g).value = seg a (P + K + 1) (NX - 2) := DN.News.ArticleAdded.value_seg hf.lines hcol.2.1
  rw [chkTail_g]
  refine fragR_append (chk_first o hA hlen hB hs) ?_
  refine fragR_append (xs := [_]) (cs_dec o rfl rfl (val := BitVec.ofNat 64 (P + K + 1)) fun u M h _ =>
    ev_add3 (vals_lookup h.1.vals rfl) (vals_lookup h.1.vals rfl)) ?_
  refine fragR_append (xs := [_]) (cs_dec o rfl rfl (val := BitVec.ofNat 64 (NX - 2)) fun u M h _ =>
    ev_sub (y := 2) (by rw [show 2 + (NX - 2) = NX by omega]; exact ev_var (vals_lookup h.1.vals rfl)) rfl) ?_
  refine fragR_append (chk_lid o hA hD hcode hlen hB (gd2 := gd ++ [g]) hs (by omega) (by omega) hval rfl) ?_
  refine fragR_append (chk_bd o hA hD hcode hlen hB (gd2 := gd ++ [g]) hs (by omega) (by omega) hval rfl) ?_
  have := set_in o (R := R) (s1 := s1) (A := A) (m0 := m0) (a := a) (gd := gd ++ [g]) (x := "p")
    ([("ve", BitVec.ofNat 64 (NX - 2)), ("vs", BitVec.ofNat 64 (P + K + 1)), ("fk", optW (firstK a gd k)), ("why", 0),
      ("ru", BitVec.ofNat 64 (ruE k)), ("fl", BitVec.ofNat 64 (flE k)), ("k", BitVec.ofNat 64 k),
      ("nl", BitVec.ofNat 64 K), ("fe", BitVec.ofNat 64 NX)])
    [("bd", optW (placeBy (bdQ a) (gd ++ [g]))), ("lid", optW (placeBy (lidQ a) (gd ++ [g]))),
      ("rep", optW (repP a (gd ++ [g]))), ("sep", BitVec.ofNat 64 SEP), ("a", A)] rfl rfl
    (w0 := BitVec.ofNat 64 P) (e := v "fe") rfl (val := BitVec.ofNat 64 NX)
    fun u M h => ev_var (vals_lookup h.1.vals rfl)
  refine fragR_conseq this (fun _ h => h) fun u h => cs_sub h fun q hq => ?_
  simp only [chkL, List.mem_cons, List.mem_nil_iff, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl <;> simp <;> rfl

/-! ## The loop -/

theorem head_ok {a : Bytes} {SEP : Nat} {L : List (Nat × Nat)} (hL : Lines a 0 L SEP)
    (hok : L.any (DN.News.ArticleLines.malLine a) = false) : ∀ q r, L = q :: r → cont a q = false := fun q r hqr => by
  subst hqr
  have := List.any_eq_false.1 hok q List.mem_cons_self
  have h0 := (DN.News.ArticleLines.lines_tail hL).1
  cases hc : cont a q
  · rfl
  · simp [DN.News.ArticleLines.malLine, hc, h0] at this

/-- Each field starts inside the article. -/
theorem groups_place {a : Bytes} {SEP : Nat} {L : List (Nat × Nat)} (hL : Lines a 0 L SEP)
    (hok : L.any (DN.News.ArticleLines.malLine a) = false) : ∀ g ∈ groups a L, placeOf g < a.length := fun g hg => by
  obtain ⟨P, e, more, rfl, -, -, hm⟩ := DN.News.ArticleAdded.mem_groups L.length L 0 (Nat.le_refl _) hL
    (head_ok hL hok) g hg
  have := DN.News.ArticleLines.lines_mem hL (P, e) hm
  show P < a.length; omega

/-- **The loop's invariant**: the fields before the place, none refused, and what the loop gathered of them. -/
def ChkI (s1 : PancakeState σ) (A : Word) (m0 : Word → Word) (a : Bytes) (L : List (Nat × Nat)) (SEP : Nat) :
    Assn σ := fun u =>
  ∃ t, LoopF a L SEP t ∧ (∀ g ∈ t.2.2, fieldNum (fieldOf a g) = 0) ∧
    ChkSt s1 A m0 a t.2.2 (chkL A SEP t.1 (optW (repP a t.2.2)) (optW (placeBy (lidQ a) t.2.2))
      (optW (placeBy (bdQ a) t.2.2))) u

theorem chkI_eval {s1 : PancakeState σ} {A : Word} {m0 : Word → Word} {a : Bytes} {L : List (Nat × Nat)} {SEP : Nat}
    (hsa : SEP < 2 ^ 63) {u : PancakeState σ} {t : Nat × List (Nat × Nat) × List (List (Nat × Nat))}
    (hf : LoopF a L SEP t) {REP LID BD : Word} {gd : List (List (Nat × Nat))}
    (h : ChkSt s1 A m0 a gd (chkL A SEP t.1 REP LID BD) u) :
    eval u (.cmp .less (.var "p") (.var "sep")) = some (bw (decide (t.1 < SEP))) := by
  obtain ⟨M, hr, -⟩ := h
  have hl := DN.News.ArticleLines.lines_sep hf.1
  exact DN.News.FramerCode.eval_lt (t := u) (a := .var "p") (b := .var "sep") (x := t.1) (y := SEP) (by omega)
    (by omega) (ev_var (vals_lookup hr.1.vals rfl)) (ev_var (vals_lookup hr.1.vals rfl))

/-- What the loop's premises say of a refused field: its reason and name given back. -/
def RefR (s1 : PancakeState σ) (A : Word) (m0 : Word → Word) (a : Bytes) (L : List (Nat × Nat)) (R : Ret) : Prop :=
  ∀ (gd : List (List (Nat × Nat))) (P e : Nat) (more : List (Nat × Nat)) (rest : List (List (Nat × Nat))),
    groups a L = gd ++ ((P, e) :: more.takeWhile (cont a)) :: rest → (∀ g ∈ gd, fieldNum (fieldOf a g) = 0) →
    fieldNum (fieldOf a ((P, e) :: more.takeWhile (cont a))) ≠ 0 → ∀ M, ChkM s1 A m0 a gd M →
    R (BitVec.ofNat 64 (fieldNum (fieldOf a ((P, e) :: more.takeWhile (cont a))))) (nameMem A s1.be
      (seg a P (P + DN.News.ArticleLines.nameLen a P e)) (DN.News.ArticleLines.nameLen a P e) e M)

/-- The grammar answers on each field it checks: those up to the first refused, refused by it or by nothing. -/
def GramOk (a : Bytes) (L : List (Nat × Nat)) : Prop :=
  ∀ (gd : List (List (Nat × Nat))) (g : List (Nat × Nat)) (rest : List (List (Nat × Nat))),
    groups a L = gd ++ g :: rest → (∀ g' ∈ gd, fieldNum (fieldOf a g') = 0) →
    (fieldNum (fieldOf a g) = 0 ∨ fieldNum (fieldOf a g) = 11) →
    ∃ b, matches? AbnfRules.grammar AbnfRules.depth (ArticleSpec.ruleOf (fieldOf a g))
      ((fieldOf a g).text.map BitVec.toNat) = .ok b

/-- **One field's turn**: refused with its reason and name, else gathered and the loop past it. -/
theorem chk_body (o : Oracle σ) {R : Ret} {A : Word} {s1 : PancakeState σ} (hA : Area ArticleProg.ofs A s1)
    (hD : ArtDom A s1.memaddrs) (hcode : ArtCode s1.code) {m0 : Word → Word} {a : Bytes} (hlen : a.length ≤ artMax)
    {SEP : Nat} (hB : ChkBase s1 A m0 SEP esP)
    (hSI : SEP ≤ inputMax) {L : List (Nat × Nat)} (hL : Lines a 0 L SEP)
    (hok : L.any (DN.News.ArticleLines.malLine a) = false) (hline : ∀ q ∈ L, q.2 - q.1 ≤ ArticleProg.nameCap)
    (hm : GramOk a L) (hR : RefR s1 A m0 a L R) :
    FragR o R (guardL (chkHead ++ chkTail))
      (fun u => ChkI s1 A m0 a L SEP u ∧ eval u (.cmp .less (.var "p") (.var "sep")) ≠ some 0)
      (ChkI s1 A m0 a L SEP) := by
  have hM := artMax_eq
  have hsa : SEP < 2 ^ 63 := by have := (DN.News.ArticleLines.lines_sep hL).2.2; omega
  have hlow : LowKK (guardL (chkHead ++ chkTail)) := lowK_any _ (k := .skip) rfl
  refine fragR_conseq (P0 := fun u => ∃ t, (LoopF a L SEP t ∧ t.1 < SEP ∧ ∀ g ∈ t.2.2, fieldNum (fieldOf a g) = 0) ∧
    ChkSt s1 A m0 a t.2.2 (chkL A SEP t.1 (optW (repP a t.2.2)) (optW (placeBy (lidQ a) t.2.2))
      (optW (placeBy (bdQ a) t.2.2))) u) ?_
    (fun u ⟨⟨t, hf, hz, hcs⟩, hne⟩ => ⟨t, ⟨hf, ?_, hz⟩, hcs⟩) fun _ h => h
  · refine fragR_exists hlow fun t => ?_
    obtain ⟨P, Lr, gd⟩ := t
    refine fragR_pure (LoopF a L SEP (P, Lr, gd) ∧ P < SEP ∧ ∀ g ∈ gd, fieldNum (fieldOf a g) = 0) (fun u h => h.1)
      hlow fun ⟨⟨hL', hsub, hhd, hgr⟩, hPS, hz⟩ => ?_
    refine fragR_conseq ?_ (fun u h => h.2) fun _ h => h
    simp only at hL' hsub hhd hgr ⊢
    obtain ⟨e, more, rfl, -, he2, hPe, hea, hmore⟩ := DN.News.ArticleLines.lines_cons hL' hPS
    have hc0 : cont a (P, e) = false := hhd _ _ rfl
    have hmal : DN.News.ArticleLines.malName a (P, e) = false := by
      have := List.any_eq_false.1 hok (P, e) (hsub _ List.mem_cons_self)
      simpa [DN.News.ArticleLines.malLine, hc0] using this
    have hf : DN.News.ArticleLines.FieldAt a SEP P e more := ⟨hL', hc0, hmal⟩
    have hcol := DN.News.ArticleLines.fieldAt_colon hf
    have hnext := DN.News.ArticleAdded.lines_next more (e + 2) hmore
    let g := (P, e) :: more.takeWhile (cont a)
    have hgr' : groups a L = gd ++ g :: groups a (more.dropWhile (cont a)) := by
      rw [hgr, DN.News.ArticleAdded.groups_cons]
    have hs : Placed gd := fun g' hg' => by
      have := groups_place hL hok g' (by rw [hgr']; exact List.mem_append_left _ hg'); omega
    have hK : DN.News.ArticleLines.nameLen a P e < ArticleProg.nameCap := by
      have := hline (P, e) (hsub _ List.mem_cons_self); simp only at this; omega
    rw [DN.News.ArticleGrammar.guardL_append]
    refine fragR_append (chk_head o hA hD hcode hlen hB hSI (gd := gd) hf hK (hm gd g _ hgr' hz)
      (fun M hM' hne => hR gd P e more _ hgr' hz hne M hM')) ?_
    refine fragR_pure (fieldNum (fieldOf a g) = 0) (fun u h => h.2) (lowK_any _ (k := .skip) rfl) fun hz0 => ?_
    refine fragR_conseq (chk_tail o hA hD hcode hlen hB hs hf) (fun u h => h.1) fun u h => ?_
    refine ⟨(DN.News.ArticleLines.nextOf a more SEP, more.dropWhile (cont a), gd ++ [g]),
      ⟨hnext, fun q hq => hsub q (List.mem_cons_of_mem _ (List.dropWhile_subset _ hq)),
        fun q r hqr => DN.News.ArticleAdded.dropWhile_head _ _ q r hqr, by rw [hgr']; simp⟩, fun g' hg' => ?_, h⟩
    rcases List.mem_append.1 hg' with hg' | hg'
    · exact hz g' hg'
    · rw [List.mem_singleton.1 hg']; exact hz0
  · have hl := DN.News.ArticleLines.lines_sep hf.1
    have e := chkI_eval hsa hf hcs
    rcases Nat.lt_or_ge t.1 SEP with hlt | hge
    · exact hlt
    · exact absurd (by rw [e, decide_eq_false (by omega)]; rfl) hne

theorem chkI_clock {s1 : PancakeState σ} {A : Word} {m0 : Word → Word} {a : Bytes} {L : List (Nat × Nat)} {SEP : Nat} :
    Safe.ClockFree (ChkI s1 A m0 a L SEP) :=
  fun u k ⟨t, hf, hz, h⟩ => ⟨t, hf, hz, cs_clock u k h⟩

theorem chk_decl : declared (guardL (chkHead ++ chkTail)) = ["fe", "nl", "k", "fl", "ru", "why", "fk", "vs", "ve"] :=
  rfl

/-- **The fields checked in order.** The first refused is given back with its name. Else none is refused, and the
loop gathered what the rest of `artCheck` reads. -/
theorem chk_loop (o : Oracle σ) {R : Ret} {A : Word} {s1 : PancakeState σ} (hA : Area ArticleProg.ofs A s1)
    (hD : ArtDom A s1.memaddrs) (hcode : ArtCode s1.code) {m0 : Word → Word} {a : Bytes} (hlen : a.length ≤ artMax)
    {SEP : Nat} (hB : ChkBase s1 A m0 SEP esP)
    (hSI : SEP ≤ inputMax) {L : List (Nat × Nat)} (hL : Lines a 0 L SEP)
    (hok : L.any (DN.News.ArticleLines.malLine a) = false) (hline : ∀ q ∈ L, q.2 - q.1 ≤ ArticleProg.nameCap)
    (hm : GramOk a L) (hR : RefR s1 A m0 a L R) :
    FragR o R [.while (eLt (v "p") (v "sep")) (guardL (chkHead ++ chkTail))]
      (ChkSt s1 A m0 a [] (chkL A SEP 0 (optW none) (optW none) (optW none)))
      (fun u => ChkSt s1 A m0 a (groups a L) (chkL A SEP SEP (optW (repP a (groups a L)))
        (optW (placeBy (lidQ a) (groups a L))) (optW (placeBy (bdQ a) (groups a L)))) u ∧
        ∀ g ∈ groups a L, fieldNum (fieldOf a g) = 0) := by
  have hM := artMax_eq
  have hsa : SEP < 2 ^ 63 := by have := (DN.News.ArticleLines.lines_sep hL).2.2; omega
  refine fragR_conseq (fragR_while o rfl (lowK_any _ (k := .skip) rfl) (I := ChkI s1 A m0 a L SEP) chkI_clock
    (fun u y w ⟨t, hf, hz, h⟩ hy => by
      rw [chk_decl] at hy
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hy
      have hfr : Fresh y (chkL A SEP t.1 (optW (repP a t.2.2)) (optW (placeBy (lidQ a) t.2.2))
          (optW (placeBy (bdQ a) t.2.2))) = true := by
        rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
      exact ⟨t, hf, hz, cs_restore h hfr w⟩)
    (fun u ⟨t, hf, _, h⟩ => ⟨_, chkI_eval hsa hf h⟩)
    (chk_body o hA hD hcode hlen hB hSI hL hok hline hm hR))
    (fun u h => ⟨(0, L, []), ⟨hL, fun _ h => h, head_ok hL hok, rfl⟩, (fun _ h => nomatch h), h⟩)
    fun u ⟨⟨t, hf, hz, h⟩, h0⟩ => ?_
  rw [chkI_eval hsa hf h] at h0
  have hge : SEP ≤ t.1 := by
    rcases Nat.lt_or_ge t.1 SEP with hlt | hge
    · rw [decide_eq_true hlt] at h0; exact absurd h0 (by decide)
    · exact hge
  have hle := (DN.News.ArticleLines.lines_sep hf.1).1
  have hg := hf.2.2.2
  rw [DN.News.ArticleLines.lines_at_sep hf.1 hge, show groups a [] = [] by rw [groups], List.append_nil] at hg
  have e : t.1 = SEP := by omega
  rw [hg]; rw [e] at h; exact ⟨h, hz⟩

/-! ## The table cleared -/

/-- The table cleared up to `i`, every other word as in `m0`. -/
def ClrI (s1 : PancakeState σ) (A : Word) (m0 : Word → Word) (l : List (String × Value)) : Assn σ := fun u =>
  ∃ i M, i ≤ esP.length + 1 ∧ RunF s1 (("i", BitVec.ofNat 64 i) :: l) (· = M) u ∧
    (∀ j, j < i → M (at_ A (ArticleProg.xFirst + 8 * j)) = optW none) ∧
    ∀ x, (∀ j, j < i → x ≠ at_ A (ArticleProg.xFirst + 8 * j)) → M x = m0 x

theorem clrI_eval {s1 : PancakeState σ} {l : List (String × Value)} {i : Nat}
    {M : Word → Word} (hi : i ≤ esP.length + 1) {u : PancakeState σ}
    (h : RunF s1 (("i", BitVec.ofNat 64 i) :: l) (· = M) u) :
    eval u (.cmp .less (.var "i") (.const (BitVec.ofNat 64 (ArticleProg.E esP + 1)))) =
      some (bw (decide (i < esP.length + 1))) := by
  have := esP_length
  exact DN.News.FramerCode.eval_lt (t := u) (x := i) (y := esP.length + 1) (by omega) (by omega)
    (ev_var (vals_lookup h.1.vals rfl)) rfl

/-- **The first fields' table cleared**: each class's word -1, so the loop's memory holds for no field. -/
theorem chk_clear (o : Oracle σ) {R : Ret} {A : Word} {s1 : PancakeState σ} (hA : Area ArticleProg.ofs A s1)
    {m0 : Word → Word} {a : Bytes} (hlen : a.length ≤ artMax) (hT : TabDom A s1.memaddrs esP)
    (hR : Reads s1 A a m0) (hall : AllSets A m0) {l : List (String × Value)}
    (hla : l.lookup "a" = some A) (hi : Fresh "i" l = true) :
    FragR o R [.while (eLt (v "i") (n (ArticleProg.E esP + 1)))
        [.store (eAdd (Syntax.atOff (v "a") ArticleProg.xFirst) (eMul (v "i") (n 8))) ArticleProg.neg1, inc "i"]]
      (RunF s1 (("i", 0) :: l) (· = m0))
      (fun u => ∃ M, RunF s1 (("i", BitVec.ofNat 64 (esP.length + 1)) :: l) (· = M) u ∧ ChkM s1 A m0 a [] M) := by
  have hA8 := hA.hA
  have hF := xFirst_eq; have hX := X_val; have hs := sets_le_X
  have hE := esP_length
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := DN.News.ArticleTables.lay esP
  have hx0 : (ArticleProg.xFirst == 0) = false := by rw [hF]; rfl
  refine fragR_conseq (fragR_while o rfl (lowK_any _ (k := .skip) rfl) (I := ClrI s1 A m0 l)
    (fun u c ⟨i, M, h1, h, h2, h3⟩ => ⟨i, M, h1, runF_clock _ _ _ u c h, h2, h3⟩)
    (fun u y w ⟨i, M, hi', h, h2, h3⟩ hy => by simp [declared, inc] at hy)
    (fun u ⟨i, M, hi', h, _⟩ => ⟨_, clrI_eval hi' h⟩) ?_)
    (fun u h => ⟨0, m0, by omega, h, fun j hj => absurd hj (Nat.not_lt_zero _), fun _ _ => rfl⟩)
    fun u ⟨⟨i, M, hi', h, hcl, hfr⟩, h0⟩ => ?_
  · refine fragR_conseq (P0 := fun u => ∃ i M, (i < esP.length + 1 ∧ (∀ j, j < i →
      M (at_ A (ArticleProg.xFirst + 8 * j)) = optW none) ∧
      ∀ x, (∀ j, j < i → x ≠ at_ A (ArticleProg.xFirst + 8 * j)) → M x = m0 x) ∧
      RunF s1 (("i", BitVec.ofNat 64 i) :: l) (· = M) u) ?_ (fun u ⟨⟨i, M, hi', h, h2, h3⟩, hne⟩ => ⟨i, M, ⟨by
        rw [clrI_eval hi' h] at hne
        rcases Nat.lt_or_ge i (esP.length + 1) with hlt | hge
        · exact hlt
        · rw [decide_eq_false (by omega)] at hne; exact absurd rfl hne, h2, h3⟩, h⟩) fun _ h => h
    refine fragR_exists (lowK_any _ (k := .skip) rfl) fun i => fragR_exists (lowK_any _ (k := .skip) rfl) fun M => ?_
    refine fragR_pure _ (fun u h => h.1) (lowK_any _ (k := .skip) rfl) fun ⟨hlt, hcl, hfr⟩ => ?_
    refine fragR_conseq ?_ (fun u h => h.2) fun _ h => h
    have hdm : s1.memaddrs (at_ A (ArticleProg.xFirst + 8 * i)) = true := DN.News.ArticleAdded.first_dom hT (by omega)
    refine fragR_of (frag_append (xs := [_]) (runF_storeA o (idxA_lower hx0 "i") rfl hdm
      (fun u h => by
        have ha_i : (("i", BitVec.ofNat 64 i) :: l).lookup "a" = some A := hla
        simp only [eval, vals_lookup h.1.vals ha_i, vals_lookup h.1.vals
          (show (("i", BitVec.ofNat 64 i) :: l).lookup "i" = some (BitVec.ofNat 64 i) from rfl)]
        rw [at_mul])
      (val := fun _ => optW none) (fun u h => rfl)
      (G := (· = upd M (at_ A (ArticleProg.xFirst + 8 * i)) (optW none))) fun m hm => by rw [hm]) ?_)
    refine frag_conseq (runF_set o rfl (x := "i") rfl (v := BitVec.ofNat 64 (i + 1)) fun u h => by
      simp only [eval, vals_lookup h.1.vals (show (("i", BitVec.ofNat 64 i) :: l).lookup "i" = _ from rfl)]
      rw [← BitVec.ofNat_add]) (fun _ h => h) fun u h => ⟨i + 1, _, by omega, by rw [without_fresh hi] at h; exact h,
        fun j hj => ?_, fun x hx => ?_⟩
    · by_cases e : j = i
      · subst e; exact upd_eq _ _ _
      · rw [upd_ne _ (table_ne (by omega) (by omega) e)]; exact hcl j (by omega)
    · rw [upd_ne _ (hx i (by omega))]; exact hfr x fun j hj => hx j (by omega)
  · rw [clrI_eval hi' h] at h0
    have hi1 : i = esP.length + 1 := by
      rcases Nat.lt_or_ge i (esP.length + 1) with hlt | hge
      · rw [decide_eq_true hlt] at h0; exact absurd h0 (by decide)
      · omega
    rw [hi1] at h
    have hnt : ∀ y, (y < aSets ∨ ArticleProg.xFirst + 8 * (esP.length + 1) ≤ y) → y < 2 ^ 40 →
        ∀ j, j < i → at_ A y ≠ at_ A (ArticleProg.xFirst + 8 * j) := fun y hy hy2 j hj e => by
      have := DN.News.ScanRun.at_inj (by omega) (by omega) e; omega
    refine ⟨M, h, reads_keep' hA8 hlen hR fun x hx => hfr _ (hnt x (.inl hx) (by omega)), fun k hk => ?_,
      fun x hx => hfr x fun j hj e => hx (.inr (.inr (.inr ⟨j, by omega, e⟩))), fun k hk => hcl k (by omega)⟩
    obtain ⟨S, hS⟩ := hall k hk
    refine ⟨S, setAt_frame hS fun i' hi' => hfr _ fun j hj e => ?_⟩
    have h3 := DN.News.AbnfSets.off_lt hk (8 * i') (by rw [DN.News.AbnfSets.setSize_eq] at hi' ⊢; omega)
    have hX' := X_eq
    have := DN.News.ScanRun.at_inj (by omega) (by omega) e
    omega

/-! ## The table by name -/

theorem class_min {es : List String} {name : Bytes} {j : Nat} (hj : j < DN.News.ArticleRun.classOf es name)
    (hjl : j < es.length) : entryIs es[j] name = false := by
  unfold DN.News.ArticleRun.classOf at hj
  cases h : es.findIdx? (entryIs · name) with
  | none => simpa using List.findIdx?_eq_none_iff.1 h es[j] (List.getElem_mem _)
  | some k =>
    rw [h, Option.getD_some] at hj
    obtain ⟨_, _, hmin⟩ := List.findIdx?_eq_some_iff_getElem.1 h
    simpa using hmin j hj

theorem class_le_of {es : List String} {name : Bytes} {i : Nat} (hi : i < es.length) (he : entryIs es[i] name = true) :
    DN.News.ArticleRun.classOf es name ≤ i := by
  rcases Nat.lt_or_ge i (DN.News.ArticleRun.classOf es name) with h | h
  · rw [class_min h hi] at he; nomatch he
  · exact h

theorem entryIs_congr {s t : String} (h : ArticleProg.lowerS s = ArticleProg.lowerS t) (name : Bytes) :
    entryIs s name = entryIs t name := by
  unfold entryIs lowCodes; rw [h]

/-- The entry of a name some entry has without case: the first such. -/
theorem entry_spec {es : List String} {nm : String}
    (hs : (es.findIdx? (fun x => ArticleProg.lowerS x == ArticleProg.lowerS nm)).isSome) :
    ∃ i, ArticleProg.entryOf es nm = i ∧ ∃ hi : i < es.length, ArticleProg.lowerS es[i] = ArticleProg.lowerS nm ∧
      ∀ j (hj : j < i), ArticleProg.lowerS es[j] ≠ ArticleProg.lowerS nm := by
  obtain ⟨i, hi⟩ := Option.isSome_iff_exists.1 hs
  obtain ⟨hlt, hp, hmin⟩ := List.findIdx?_eq_some_iff_getElem.1 hi
  refine ⟨i, by unfold ArticleProg.entryOf; rw [hi]; rfl, hlt, by simpa using hp, fun j hj e => ?_⟩
  exact hmin j hj (by simp [e])

/-- A name the rules read has an entry. -/
theorem entry_some {nm : String} (hn : nm ∈ allNames) :
    (esP.findIdx? (fun x => ArticleProg.lowerS x == ArticleProg.lowerS nm)).isSome := by
  obtain ⟨t, ht, hl⟩ := DN.News.ArticleTables.foldl_cover allNames [] nm (by rw [List.nil_append]; exact hn)
  rw [← DN.News.ArticleTables.esP_eq] at ht
  rw [List.findIdx?_isSome]; exact List.any_eq_true.2 ⟨t, ht, by simp [hl]⟩

/-- **A field is of a name's entry** exactly when it has that name, without case. -/
theorem class_entry {nm : String} (hn : nm ∈ allNames) (name : Bytes) :
    classOf esP name = ArticleProg.entryOf esP nm ↔ ArticleSpec.named name nm = true := by
  obtain ⟨i, hei, hlt, hlow, hmin⟩ := entry_spec (entry_some hn)
  rw [hei]
  constructor
  · intro hc; rw [DN.News.ArticleTables.class_named hlt hc hn]; exact beq_iff_eq.2 hlow.symm
  · intro hnm
    rcases Nat.lt_or_ge (classOf esP name) esP.length with hk | hk
    · rw [DN.News.ArticleTables.class_named hk rfl hn] at hnm
      have hlk : ArticleProg.lowerS esP[classOf esP name] = ArticleProg.lowerS nm := (beq_iff_eq.1 hnm).symm
      have h1 : ¬classOf esP name < i := fun h => hmin _ h hlk
      have h2 : ¬i < classOf esP name := fun h => absurd (class_le_of hlt (by
        rw [entryIs_congr (hlow.trans hlk.symm)]; exact entry_of_class hk rfl)) (by omega)
      omega
    · have hk' : classOf esP name = esP.length := by
        have := DN.News.ArticleAdded.classOf_le esP name; omega
      rw [DN.News.ArticleTables.class_none hk' hn] at hnm; nomatch hnm

/-- **The table read by name**: where the first field of a name the rules read starts. -/
theorem chkM_firstW {s1 : PancakeState σ} {A : Word} {m0 : Word → Word} {a : Bytes} {L : List (Nat × Nat)}
    {M : Word → Word} (h : ChkM s1 A m0 a (groups a L) M) {nm : String} (hn : nm ∈ allNames) :
    DN.News.ArticleAdded.FirstW A M a L nm := by
  unfold DN.News.ArticleAdded.FirstW DN.News.ArticleAdded.firstP DN.News.ArticleAdded.firstG
  rw [h.first _ (DN.News.ArticleAdded.entry_le esP nm)]
  unfold firstK
  have hc : ∀ g ∈ groups a L, (classG a g == ArticleProg.entryOf esP nm) =
      ArticleSpec.named (DN.News.ArticleLines.nameAt a (g.headD (0, 0))) nm :=
    fun g _ => Bool.eq_iff_iff.2 (beq_iff_eq.trans (class_entry hn (fieldOf a g).name))
  rw [find?_congr' hc]
  rfl

/-! ## Witnesses -/

theorem hiScr_witness : HiScr 0 (at_ 0 ArticleProg.xNl) := .inl rfl

theorem placed_witness : Placed [[(0, 1)]] := fun g hg => by rw [List.mem_singleton.1 hg]; decide

/-- The empty article only: `matches?` on a real field overflows the kernels' stacks. -/
theorem gramOk_witness : GramOk [] [] := fun _ _ _ h => by rw [groups] at h; exact absurd h.symm (by simp)

/-- `RefR` is a premise on the answer `R`; `artCheck`'s verdict meets it in the next module. -/
theorem refR_witness : RefR (bareState ()) 0 (fun _ => 0) [] [] (fun _ _ => True) := fun _ _ _ _ _ h => by
  rw [groups] at h; exact absurd h.symm (by simp)

/-- On the one entry `a`, as the tables' own witnesses. -/
theorem chkBase_witness : ChkBase (bareState ()) 0 DN.News.ArticleTables.wTabMem 0 ["a"] := by
  obtain ⟨l1, l2, l3, l4, l5, l6⟩ := DN.News.ArticleTables.lay ["a"]
  have hl : (["a"] : List String).length = 1 := rfl
  have hw := DN.News.ArticleTables.entryAt_witness
  have hlow : ∀ y, y < ArticleProg.xFirst → DN.News.ArticleTables.wTabMem (at_ 0 y) = 0 := fun y hy => by
    unfold DN.News.ArticleTables.wTabMem
    rw [upd_ne _ (DN.News.ArticleTables.at40 (by omega) (by omega) (by omega)),
      upd_ne _ (DN.News.ArticleTables.at40 (by omega) (by omega) (by omega)),
      upd_ne _ (DN.News.ArticleTables.at40 (by omega) (by omega) (by omega)),
      upd_ne _ (DN.News.ArticleTables.at40 (by omega) (by omega) (by omega)),
      upd_ne _ (DN.News.ArticleTables.at40 (by omega) (by omega) (by omega))]
  refine ⟨hlow _ (by have : aBroken = 24 := rfl; omega),
    hlow _ (by simp only [ArticleProg.xSep, ArticleProg.w, X_val]; omega),
    DN.News.ArticleRun.tabDom_witness, ⟨fun k hk => ?_, fun k hk => ?_, fun k hk i hi => ?_⟩,
    DN.News.ArticleTables.kindsAt_witness⟩
  · obtain rfl : k = 0 := by simp at hk; omega
    exact hw.off
  · obtain rfl : k = 0 := by simp at hk; omega
    exact hw.len
  · obtain rfl : k = 0 := by simp at hk; omega
    exact hw.bytes i hi

/-- The base memory with the first fields' table cleared. -/
noncomputable def wClr (x : Word) : Word :=
  @ite _ (∃ k, k ≤ esP.length ∧ x = at_ 0 (ArticleProg.xFirst + 8 * k)) (Classical.propDecidable _) (optW none)
    (DN.News.AbnfMain.baseMem x)

theorem chkM_witness : ChkM (bareState ()) 0 wClr [] [] wClr := by
  have hF := xFirst_eq; have hX := X_val; have hs := sets_le_X; have hE := esP_length
  have hb := DN.News.AbnfMain.base_witness
  have hnot : ∀ y, y < ArticleProg.X → wClr (at_ 0 y) = DN.News.AbnfMain.baseMem (at_ 0 y) := fun y hy => by
    unfold wClr
    exact if_neg fun ⟨k, hk, e⟩ => by have := DN.News.ScanRun.at_inj (by omega) (by omega) e; omega
  refine ⟨reads_keep' (by decide) (by simp) hb.2.2 fun x hx => hnot x (by omega), fun k hk => ?_, fun _ _ => rfl,
    fun k hk => if_pos ⟨k, hk, rfl⟩⟩
  obtain ⟨S, hS⟩ := hb.1 k hk
  refine ⟨S, setAt_frame hS fun i hi => ?_⟩
  have h3 := DN.News.AbnfSets.off_lt hk (8 * i) (by rw [DN.News.AbnfSets.setSize_eq] at hi ⊢; omega)
  have hX' := X_eq
  exact hnot _ (by omega)

end DN.News.ArticleFields
