-- SPDX-License-Identifier: AGPL-3.0-or-later
import DN.News.AbnfComment
import DN.News.AbnfEnds
import DN.News.AbnfOrder

/-!
# DN.News.AbnfGen

`gen`, proven to write what it is named for: its statements for a term, from one slot into another, leave there the
ends of the term's matches from the first slot's positions, every slot a set, every word as it was but those of the
second slot and of the slots kept for the statements' own sets (`gen_ok`, `Does`). A repetition's loop runs as
`endsFrom` does, a frontier and the ends counted; after `lo` rounds and one more than the input has positions, its
frontier adds nothing (`cnt_full`). A rule's function called is taken as its contract says (`BodyOk`).
-/

namespace DN.News.AbnfGen

open DN.Compiler DN.Compiler.Wp DN.Compiler.WpRet DN.Compiler.Frag DN.News.AbnfProg DN.News.AbnfLayout
open DN.News.AbnfSets DN.News.FunRun DN.News.AbnfLeaves
open DN.News.ScanRun (at_ at_add at_ne at_inj Vals vals_lookup vals_cons vals_set Fresh without lookup_head
  lookup_without fresh_cons)
open DN.News.FramerCode (bw ev_var)
open DN.News.AbnfMatch (Matches)
open DN.News.AbnfComment (commentAdd ruleComment_ok commentSet_iff ev_inc)

variable {σ : Type}

/-! ## The locals' names -/

/-- Digits read back as a number. -/
def digitsVal (cs : List Char) : Nat := cs.foldl (fun n c => 10 * n + (c.toNat - 48)) 0

theorem digitsVal_snoc (cs : List Char) (c : Char) :
    digitsVal (cs ++ [c]) = 10 * digitsVal cs + (c.toNat - 48) := by
  simp only [digitsVal, List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem digitsVal_toDigits (n : Nat) : digitsVal (Nat.toDigits 10 n) = n := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    rw [Nat.toDigits_eq_if (by decide)]
    split
    · rename_i h
      simp only [digitsVal, List.foldl_cons, List.foldl_nil, Nat.toNat_digitChar_of_lt_ten h]
      omega
    · rename_i h
      rw [digitsVal_snoc, ih (n / 10) (by omega), Nat.toNat_digitChar_sub_48_of_lt_ten (Nat.mod_lt _ (by decide))]
      omega

theorem takeWhile_digits (n : Nat) {z : List Char} (hz : ∀ c ∈ z.head?, c.isDigit = false) :
    (Nat.toDigits 10 n ++ z).takeWhile Char.isDigit = Nat.toDigits 10 n := by
  have hd : ∀ c ∈ Nat.toDigits 10 n, c.isDigit = true := fun c hc => Nat.isDigit_of_mem_toDigits (by decide)
    (by decide) hc
  generalize Nat.toDigits 10 n = D at hd ⊢
  induction D with
  | nil =>
    cases z with
    | nil => rfl
    | cons c z => simp only [List.nil_append, List.takeWhile_cons, hz c rfl]; rfl
  | cons c D ih =>
    simp only [List.cons_append, List.takeWhile_cons, hd c (List.mem_cons_self ..), if_true]
    exact congrArg _ (ih fun c hc => hd c (List.mem_cons_of_mem _ hc))

/-- The letters a generated local's name starts with. -/
def heads : List Char := ['c', 'e', 'f', 'x', 'n', 'g', 'i']

/-- `x` is the name `gen` gives a local of number `k`: a letter, `k`'s digits and maybe `b` or `d`. -/
def GenName (x : String) (k : Nat) : Prop :=
  ∃ p ∈ heads, ∃ z ∈ [[], ['b'], ['d']], x.toList = p :: (Nat.toDigits 10 k ++ z)

theorem genName_inj {x : String} {k j : Nat} (h1 : GenName x k) (h2 : GenName x j) : k = j := by
  obtain ⟨p, -, z, hz, e1⟩ := h1
  obtain ⟨p', -, z', hz', e2⟩ := h2
  rw [e1] at e2
  have e := (List.cons.inj e2).2
  have hzd : ∀ z ∈ [[], ['b'], ['d']], ∀ c ∈ z.head?, c.isDigit = false := by decide
  have := congrArg (List.takeWhile Char.isDigit) e
  rw [takeWhile_digits k (hzd z hz), takeWhile_digits j (hzd z' hz')] at this
  rw [← digitsVal_toDigits k, ← digitsVal_toDigits j, this]

/-- A generated name has a digit second. -/
theorem genName_digit {x : String} {k : Nat} (h : GenName x k) :
    ∃ p c rest, x.toList = p :: c :: rest ∧ c.isDigit = true := by
  obtain ⟨p, -, z, -, e⟩ := h
  rw [e]
  have hne : Nat.toDigits 10 k ≠ [] := Nat.toDigits_ne_nil
  cases hD : Nat.toDigits 10 k with
  | nil => exact absurd hD hne
  | cons c D => exact ⟨p, c, D ++ z, rfl, Nat.isDigit_of_mem_toDigits (by decide) (by decide)
    (hD ▸ List.mem_cons_self ..)⟩

theorem genName_of {p : Char} (hp : p ∈ heads) {z : List Char} (hz : z ∈ [[], ['b'], ['d']]) {x : String} {k : Nat}
    (e : x.toList = p :: (Nat.toDigits 10 k ++ z)) : GenName x k := ⟨p, hp, z, hz, e⟩

theorem tl_name {p : String} {c : Char} (hp : p.toList = [c]) (k : Nat) :
    (p ++ toString k).toList = c :: Nat.toDigits 10 k := by
  show (p ++ Nat.repr k).toList = _
  rw [String.toList_append, hp, Nat.toList_repr]; rfl

theorem tl_f (k : Nat) : (s!"f{k}").toList = 'f' :: Nat.toDigits 10 k := tl_name rfl k
theorem tl_x (k : Nat) : (s!"x{k}").toList = 'x' :: Nat.toDigits 10 k := tl_name rfl k
theorem tl_n (k : Nat) : (s!"n{k}").toList = 'n' :: Nat.toDigits 10 k := tl_name rfl k
theorem tl_g (k : Nat) : (s!"g{k}").toList = 'g' :: Nat.toDigits 10 k := tl_name rfl k
theorem tl_i (k : Nat) : (s!"i{k}").toList = 'i' :: Nat.toDigits 10 k := tl_name rfl k
theorem tl_e (k : Nat) : (s!"e{k}").toList = 'e' :: Nat.toDigits 10 k := tl_name rfl k
theorem tl_cb (k : Nat) : (s!"{s!"c{k}"}b").toList = 'c' :: (Nat.toDigits 10 k ++ ['b']) := by
  show ("c" ++ Nat.repr k ++ "b").toList = _; rw [String.toList_append, String.toList_append, Nat.toList_repr]; rfl
theorem tl_cd (k : Nat) : (s!"{s!"c{k}"}d").toList = 'c' :: (Nat.toDigits 10 k ++ ['d']) := by
  show ("c" ++ Nat.repr k ++ "d").toList = _; rw [String.toList_append, String.toList_append, Nat.toList_repr]; rfl

/-- A letter of `heads` and a number's digits: a generated name. -/
theorem name_of {p : String} {c : Char} (hp : p.toList = [c]) (hc : c ∈ heads) (k : Nat) :
    GenName (p ++ toString k) k :=
  genName_of hc (z := []) (by decide) (by rw [tl_name hp, List.append_nil])

theorem name_c (k : Nat) : GenName s!"c{k}" k := name_of rfl (by decide) k
theorem name_e (k : Nat) : GenName s!"e{k}" k := name_of rfl (by decide) k
theorem name_f (k : Nat) : GenName s!"f{k}" k := name_of rfl (by decide) k
theorem name_x (k : Nat) : GenName s!"x{k}" k := name_of rfl (by decide) k
theorem name_n (k : Nat) : GenName s!"n{k}" k := name_of rfl (by decide) k
theorem name_g (k : Nat) : GenName s!"g{k}" k := name_of rfl (by decide) k
theorem name_i (k : Nat) : GenName s!"i{k}" k := name_of rfl (by decide) k
theorem name_cb (k : Nat) : GenName s!"{s!"c{k}"}b" k :=
  genName_of (p := 'c') (by decide) (z := ['b']) (by decide) (tl_cb k)
theorem name_cd (k : Nat) : GenName s!"{s!"c{k}"}d" k :=
  genName_of (p := 'c') (by decide) (z := ['d']) (by decide) (tl_cd k)

/-- No local of `l` has a generated name numbered from `lo` to below `hi`. -/
def Avoid (l : List (String × Value)) (lo hi : Nat) : Prop :=
  ∀ q ∈ l, ∀ j, lo ≤ j → j < hi → ¬GenName q.1 j

theorem fresh_of {l : List (String × Value)} {lo hi k : Nat} (ha : Avoid l lo hi) (h1 : lo ≤ k) (h2 : k < hi)
    {x : String} (hx : GenName x k) : Fresh x l = true := by
  simp only [Fresh, List.all_eq_true, bne_iff_ne, ne_eq]
  intro q hq e
  exact ha q hq k h1 h2 (e ▸ hx)

/-! ## Sets of positions in slots -/

/-- The positions `P` says, as a set. -/
noncomputable def setOf (P : Nat → Prop) : Nat → Bool := fun e => @decide (P e) (Classical.propDecidable _)

theorem setOf_iff {P : Nat → Prop} {e : Nat} : setOf P e = true ↔ P e :=
  @decide_eq_true_iff _ (Classical.propDecidable _)

theorem setOf_false {P : Nat → Prop} {e : Nat} (h : ¬P e) : setOf P e = false := by
  cases e' : setOf P e
  · rfl
  · exact absurd (setOf_iff.1 e') h

theorem setOf_eq {T : Nat → Bool} {P : Nat → Prop} (h : ∀ e, T e = true ↔ P e) : T = setOf P :=
  funext fun e => Bool.eq_iff_iff.2 ((h e).trans setOf_iff.symm)

section
variable (A : Word) (bytes : List (BitVec 8))

/-- The ends of the matches of `t` from the positions of `S`, on the input `bytes`. -/
def Ends (t : Abnf.Term) (S : Nat → Bool) (e : Nat) : Prop :=
  ∃ x, S x = true ∧ Matches AbnfRules.grammar (inputOf bytes) t x e

/-- Slot `k` of `m` holds the positions `P` says. -/
def Holds (m : Word → Word) (k : Nat) (P : Nat → Prop) : Prop := SetAt m A k (setOf P)

/-- Every slot holds a set. -/
def AllSets (m : Word → Word) : Prop := ∀ k, k < slots → ∃ S, SetAt m A k S

/-- Every word as in `m0` but slot `kd`'s and those of the slots from `free` on. -/
def Kept (kd free : Nat) (m0 m : Word → Word) : Prop :=
  ∀ a, ¬InSlot A kd a → (∀ k, free ≤ k → k < slots → ¬InSlot A k a) → m a = m0 a

end

/-- What a call takes besides its slots: every slot a set, the input's length, and what the leaves read. -/
def Base (s0 : PancakeState σ) (A : Word) (bytes : List (BitVec 8)) (m : Word → Word) : Prop :=
  AllSets A m ∧ m (at_ A aLen) = BitVec.ofNat 64 bytes.length ∧ Reads s0 A bytes m

section
variable {A : Word} {kd free : Nat} {m0 m1 m : Word → Word}

theorem kept_refl (m : Word → Word) : Kept A kd free m m := fun _ _ _ => rfl

theorem kept_trans (h1 : Kept A kd free m0 m1) (h2 : Kept A kd free m1 m) : Kept A kd free m0 m :=
  fun a ha hb => (h2 a ha hb).trans (h1 a ha hb)

/-- What a frame of slot `k` keeps, `k` being `kd` or one from `free` on. -/
theorem kept_frame {k : Nat} (hk : k = kd ∨ free ≤ k ∧ k < slots) (h : Frame A k m0 m) : Kept A kd free m0 m :=
  fun a ha hb => h a (hk.elim (fun e => by rw [e]; exact ha) fun ⟨h1, h2⟩ => hb k h1 h2)

/-- What is kept with more slots free, `kd'` being `kd` or one from `free` on. -/
theorem kept_wide {kd' free' : Nat} (hf : free ≤ free') (hk : kd' = kd ∨ free ≤ kd' ∧ kd' < slots)
    (h : Kept A kd' free' m0 m) : Kept A kd free m0 m :=
  fun a ha hb => h a (hk.elim (fun e => by rw [e]; exact ha) fun ⟨h1, h2⟩ => hb _ h1 h2)
    fun k h1 h2 => hb k (by omega) h2

/-- A slot below `free` but `kd` keeps its set. -/
theorem setAt_kept {k : Nat} {S : Nat → Bool} (h : SetAt m0 A k S) (hk : k < free) (hks : k < slots)
    (hkd : kd < slots) (hne : k ≠ kd) (hm : Kept A kd free m0 m) : SetAt m A k S :=
  setAt_frame h fun i hi => hm _ (fun ⟨_, hi', e⟩ => hne (slotW_inj hks hkd hi hi' e).1)
    fun k' h1 h2 ⟨_, hi', e⟩ => by have := (slotW_inj hks h2 hi hi' e).1; omega

/-- The words below the slots are kept. -/
theorem kept_low (hkd : kd < slots) (h : Kept A kd free m0 m) {x : Nat} (hx : x < aSets) :
    m (at_ A x) = m0 (at_ A x) :=
  h _ (notInSlot hkd hx) fun _ _ hk => notInSlot hk hx

theorem aLen_low : aLen < aSets := by have := pow_lt; simp only [aLen]; omega

theorem base_keep {s0 : PancakeState σ} {bytes : List (BitVec 8)} (hA8 : A.toNat % 8 = 0)
    (hlen : bytes.length ≤ inputMax) (hkd : kd < slots) (h : Base s0 A bytes m0) (hm : Kept A kd free m0 m)
    (hall : AllSets A m) : Base s0 A bytes m :=
  ⟨hall, by rw [kept_low hkd hm aLen_low]; exact h.2.1, reads_keep hA8 hlen h.2.2 fun _ hx => kept_low hkd hm hx⟩

/-- Every slot a set after slot `kd` alone changed. -/
theorem allSets_frame {T : Nat → Bool} (h : AllSets A m0) (hkd : kd < slots) (hT : SetAt m A kd T)
    (hf : Frame A kd m0 m) : AllSets A m := fun k hk => by
  by_cases e : k = kd
  · subst e; exact ⟨T, hT⟩
  · obtain ⟨S, hS⟩ := h k hk; exact ⟨S, setAt_other hS hkd hk (fun e' => e e'.symm) hf⟩

end

/-! ## The program's code -/

/-- The code holds each of the program's functions as it lowers. -/
def ProgCode (code : String → Option (List String × PancakeProg)) (ofs : Nat) : Prop :=
  ∀ f ∈ functions .none ofs, ∀ body, Lower.lower f = some body → code f.name = some (f.params.map (·.2), body)

/-- What rule `i`'s function gives back: zero, slot `kd` the ends of the rule's matches from the positions of `S`,
every slot a set, every word as in `m0` but slot `kd`'s and those of the slots from the rule's frame on. -/
def RuleRet (A : Word) (bytes : List (BitVec 8)) (i kd : Nat) (S : Nat → Bool) (m0 : Word → Word) : Ret :=
  fun v m => v = 0 ∧ Holds A m kd (Ends bytes (.ref i) S) ∧ AllSets A m ∧ Kept A kd (frameOf i) m0 m

/-- Rule `i`'s function as `code` holds it, shown from any entry with the area, two slots below its frame and what
calls take. -/
def BodyOk (o : Oracle σ) (ofs : Nat) (code : String → Option (List String × PancakeProg)) (i : Nat) : Prop :=
  ∀ (s1 : PancakeState σ) (A : Word) (ks kd : Nat) (S : Nat → Bool) (bytes : List (BitVec 8)),
    Area ofs A s1 → s1.code = code → ks < frameOf i → kd < frameOf i → ks ≠ kd →
    s1.locals "s" = some (BitVec.ofNat 64 ks) → s1.locals "d" = some (BitVec.ofNat 64 kd) →
    bytes.length ≤ inputMax → SetAt s1.memory A ks S → Base s1 A bytes s1.memory →
    ∃ body, code (funName i) = some (["s", "d"], body) ∧
      SafeR o (fun s => s = s1) body (RuleRet A bytes i kd S s1.memory) fun _ => False

/-- **A call of a rule's function.** -/
theorem ruleCall_frag (o : Oracle σ) {ofs : Nat} {A : Word} {s0 : PancakeState σ} (hA : Area ofs A s0) {rt : String}
    {l : List (String × Value)} {F : (Word → Word) → Prop} (hrt : Fresh rt l = true) {i : Nat}
    (hb : BodyOk o ofs s0.code i) {e1 e2 : Syntax.PExpr} {E1 E2 : PancakeExp}
    (he1 : Lower.lowerExp e1 = some E1) (he2 : Lower.lowerExp e2 = some E2) {ks kd : Nat} (hks : ks < frameOf i)
    (hkd : kd < frameOf i) (hne : ks ≠ kd) (hv1 : ∀ u, RunF s0 l F u → eval u E1 = some (BitVec.ofNat 64 ks))
    (hv2 : ∀ u, RunF s0 l F u → eval u E2 = some (BitVec.ofNat 64 kd)) {S : Nat → Bool} {bytes : List (BitVec 8)}
    (hlen : bytes.length ≤ inputMax) (hS : ∀ m, F m → SetAt m A ks S ∧ Base s0 A bytes m) :
    Frag o [.call rt (funName i) [e1, e2]] (RunF s0 l F)
      (fun u => ∃ v, RunF s0 ((rt, v) :: l) (fun m' => ∃ m, F m ∧ RuleRet A bytes i kd S m v m') u) := by
  have hargs : Lower.lowerArgs [e1, e2] = some [E1, E2] := by simp [Lower.lowerArgs, he1, he2]
  refine frag_pure (∃ body, s0.code (funName i) = some (["s", "d"], body)) (fun u hu => ?_) (lowKK_call hargs)
    fun ⟨body, hcode⟩ => setCall_frag o hA (ps := ["s", "d"]) (args := [E1, E2])
      (vs := [BitVec.ofNat 64 ks, BitVec.ofNat 64 kd]) (by decide) hargs hcode rfl
      (fun u h => by simp only [evalArgs, hv1 u h, hv2 u h]) (R := RuleRet A bytes i kd S)
      (fun s1 hA1 hc hm hbe hloc hF => by
        obtain ⟨body', hc', hs⟩ := hb s1 A ks kd S bytes hA1 hc hks hkd hne ((hloc "s").trans rfl)
          ((hloc "d").trans rfl) hlen (hS _ hF).1 ⟨(hS _ hF).2.1, (hS _ hF).2.2.1, reads_of hm hbe (hS _ hF).2.2.2⟩
        rw [hcode] at hc'; cases hc'; exact hs) hrt fun m m' v hF hr => ⟨m, hF, hr⟩
  let s1 : PancakeState σ :=
    { u with locals := fun k => (["s", "d"].zip [BitVec.ofNat 64 ks, BitVec.ofNat 64 kd]).lookup k }
  obtain ⟨body, hc, -⟩ := hb s1 A ks kd S bytes ⟨by show u.baseAddr + _ = _; rw [hu.1.base]; exact hA.base, hA.hA,
      fun x hx h8 => by show u.memaddrs _ = true; rw [hu.1.memaddrs]; exact hA.dom x hx h8⟩
    hu.1.code hks hkd hne rfl rfl hlen (hS _ hu.2).1
    ⟨(hS _ hu.2).2.1, (hS _ hu.2).2.2.1, reads_of (s1 := s1) hu.1.memaddrs hu.1.be (hS _ hu.2).2.2.2⟩
  exact ⟨body, hc⟩

/-! ## What the grammar's order gives -/

theorem le_foldl_max : ∀ (L : List Nat) (a : Nat), a ≤ L.foldl max a ∧ ∀ x ∈ L, x ≤ L.foldl max a
  | [], a => ⟨Nat.le_refl _, fun _ h => nomatch h⟩
  | y :: L, a => by
    obtain ⟨h1, h2⟩ := le_foldl_max L (max a y)
    refine ⟨Nat.le_trans (Nat.le_max_left _ _) h1, fun x hx => ?_⟩
    rcases List.mem_cons.1 hx with rfl | hx
    · exact Nat.le_trans (Nat.le_max_right _ _) h1
    · exact h2 x hx

theorem frame_le {i : Nat} (hi : i ∈ order) : frameOf i + need i ≤ slots :=
  (le_foldl_max _ _).2 _ (List.mem_map.2 ⟨i, hi, rfl⟩)

theorem order_all {i : Nat} (hi : i ∈ order) : i < AbnfRules.grammar.size ∧ roots ≤ frameOf i ∧
    (i = commentRule ∨ AbnfOrder.enough steps (termOf i) = true) ∧
      ∀ j ∈ callees i, frameOf i + need i ≤ frameOf j := by
  have := List.all_eq_true.1 AbnfOrder.facts.2.2.1 i hi
  simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true, beq_iff_eq, List.all_eq_true] at this
  exact ⟨this.1.1.1, this.1.1.2, this.1.2, this.2⟩

theorem order_has {i : Nat} (hi : i < AbnfRules.grammar.size) (hf : hasFun i = true) : i ∈ order := by
  have := List.all_eq_true.1 AbnfOrder.facts.2.2.2 i (List.mem_range.2 hi)
  simp only [hf, Bool.not_true, Bool.false_or, List.contains_iff_mem] at this
  exact this

/-- Each function calls only those before it. -/
theorem order_callees {k : Nat} (hk : k < order.length) : ∀ j ∈ callees order[k], j ∈ order.take k := by
  have := List.all_eq_true.1 (show ordered = true from AbnfOrder.facts.1) (order[k], k)
    (List.mem_iff_getElem.2 ⟨k, by simpa using hk, by simp⟩)
  simp only [List.all_eq_true, List.contains_iff_mem] at this
  exact this

/-- **A call of one of the program's functions**, its body shown as its `_ok` theorem shows it, from any entry with
the area and its parameters; the code holds it as it lowers. -/
theorem progCall_frag (o : Oracle σ) {ofs : Nat} {A : Word} {s0 : PancakeState σ} (hA : Area ofs A s0)
    {rt : String} {f : Syntax.PFun} (hnd : (f.params.map (·.2)).Nodup) {as : List Syntax.PExpr}
    {args : List PancakeExp} (has : Lower.lowerArgs as = some args)
    (hcode : ∀ body, Lower.lower f = some body → s0.code f.name = some (f.params.map (·.2), body))
    {l : List (String × Value)} {F : (Word → Word) → Prop} {vs : List Value}
    (hlen : (f.params.map (·.2)).length = vs.length) (hargs : ∀ u, RunF s0 l F u → evalArgs u args = some vs)
    {R : (Word → Word) → Ret}
    (hbody : ∀ s1 : PancakeState σ, Area ofs A s1 → s1.code = s0.code → s1.memaddrs = s0.memaddrs →
      s1.be = s0.be → (∀ k, s1.locals k = ((f.params.map (·.2)).zip vs).lookup k) → F s1.memory →
      ∃ body, Lower.lower f = some body ∧ SafeR o (fun s => s = s1) body (R s1.memory) fun _ => False)
    (hrt : Fresh rt l = true) {G : Value → (Word → Word) → Prop} (hG : ∀ m m' v, F m → R m v m' → G v m') :
    Frag o [.call rt f.name as] (RunF s0 l F) (fun u => ∃ v, RunF s0 ((rt, v) :: l) (G v) u) := by
  refine frag_pure (∃ body, Lower.lower f = some body) (fun u hu => ?_) (lowKK_call has) fun ⟨body, hb⟩ =>
    setCall_frag o hA hnd has (hcode body hb) hlen hargs
      (fun s1 hA1 hc hm hbe hloc hF => body_eq hb (hbody s1 hA1 hc hm hbe hloc hF)) hrt hG
  obtain ⟨body, hb, -⟩ := hbody { u with locals := fun k => ((f.params.map (·.2)).zip vs).lookup k }
    ⟨by show u.baseAddr + _ = _; rw [hu.1.base]; exact hA.base, hA.hA,
      fun x hx h8 => by show u.memaddrs _ = true; rw [hu.1.memaddrs]; exact hA.dom x hx h8⟩
    hu.1.code hu.1.memaddrs hu.1.be (fun _ => rfl) hu.2
  exact ⟨body, hb⟩

theorem progCode_of {code : String → Option (List String × PancakeProg)} {ofs : Nat} (h : ProgCode code ofs)
    {f : Syntax.PFun} (hf : f ∈ functions .none ofs) :
    ∀ body, Lower.lower f = some body → code f.name = some (f.params.map (·.2), body) := h f hf

/-! ## `gen`'s locals and slots -/

/-- The locals `l'` have generated names numbered from `k` to below `k'`. -/
def Named (l' : List (String × Value)) (k k' : Nat) : Prop := ∀ q ∈ l', ∃ j, k ≤ j ∧ j < k' ∧ GenName q.1 j

theorem avoid_mono {l : List (String × Value)} {lo hi lo' hi' : Nat} (h : Avoid l lo hi) (h1 : lo ≤ lo')
    (h2 : hi' ≤ hi) : Avoid l lo' hi' := fun q hq j hj1 hj2 => h q hq j (by omega) (by omega)

/-- Locals numbered apart from `lo` to below `hi` added. -/
theorem avoid_append {l l' : List (String × Value)} {lo hi a b : Nat} (h : Avoid l lo hi) (hn : Named l' a b)
    (hab : b ≤ lo ∨ hi ≤ a) : Avoid (l' ++ l) lo hi := fun q hq j hj1 hj2 hg => by
  rcases List.mem_append.1 hq with hq | hq
  · obtain ⟨j', h1, h2, hg'⟩ := hn q hq
    have := genName_inj hg hg'
    omega
  · exact h q hq j hj1 hj2 hg

theorem named_mono {l' : List (String × Value)} {a b a' b' : Nat} (h : Named l' a b) (h1 : a' ≤ a) (h2 : b ≤ b') :
    Named l' a' b' := fun q hq => let ⟨j, hj1, hj2, hg⟩ := h q hq; ⟨j, by omega, by omega, hg⟩

theorem named_append {l1 l2 : List (String × Value)} {a b : Nat} (h1 : Named l1 a b) (h2 : Named l2 a b) :
    Named (l1 ++ l2) a b := fun q hq => (List.mem_append.1 hq).elim (h1 q) (h2 q)

/-- A generated name of number `k` is fresh among locals numbered apart from it. -/
theorem fresh_named {l' : List (String × Value)} {a b k : Nat} (h : Named l' a b) (hk : k < a ∨ b ≤ k) {x : String}
    (hx : GenName x k) : Fresh x l' = true := by
  simp only [Fresh, List.all_eq_true, bne_iff_ne, ne_eq]
  intro q hq e
  obtain ⟨j, h1, h2, hg⟩ := h q hq
  have := genName_inj hg (e ▸ hx)
  omega

theorem named_one {x : String} {v : Value} {j a b : Nat} (hx : GenName x j) (h1 : a ≤ j) (h2 : j < b) :
    Named [(x, v)] a b := fun q hq => by
  rw [List.mem_singleton] at hq; subst hq; exact ⟨j, h1, h2, hx⟩

/-- A slot named by an expression: a constant, or a local of `l`. -/
def SlotIs (l : List (String × Value)) (e : Syntax.PExpr) (k : Nat) : Prop :=
  e = Syntax.n k ∨ ∃ x, e = Syntax.v x ∧ (x, BitVec.ofNat 64 k) ∈ l

theorem slotIs_mono {l l2 : List (String × Value)} {e : Syntax.PExpr} {k : Nat} (h : SlotIs l e k)
    (hl : ∀ q ∈ l, q ∈ l2) : SlotIs l2 e k :=
  h.imp id fun ⟨x, he, hx⟩ => ⟨x, he, hl _ hx⟩

theorem slotIs_eval {l : List (String × Value)} {e : Syntax.PExpr} {k : Nat} (h : SlotIs l e k) :
    ∃ E, Lower.lowerExp e = some E ∧ ∀ u : PancakeState σ, Vals u l → eval u E = some (BitVec.ofNat 64 k) := by
  rcases h with rfl | ⟨x, rfl, hx⟩
  · exact ⟨_, rfl, fun _ _ => rfl⟩
  · exact ⟨_, rfl, fun u hu => hu _ hx⟩

theorem lower_n (c : Nat) : Lower.lowerExp (Syntax.n c) = some (.const (BitVec.ofNat 64 c)) := rfl

theorem lowerArgs_two {a b : Syntax.PExpr} {Ea Eb : PancakeExp} (ha : Lower.lowerExp a = some Ea)
    (hb : Lower.lowerExp b = some Eb) : Lower.lowerArgs [a, b] = some [Ea, Eb] := by simp [Lower.lowerArgs, ha, hb]

theorem lowerArgs_three {a b : Syntax.PExpr} {Ea Eb : PancakeExp} (ha : Lower.lowerExp a = some Ea)
    (hb : Lower.lowerExp b = some Eb) (c : Nat) :
    Lower.lowerArgs [a, b, Syntax.n c] = some [Ea, Eb, .const (BitVec.ofNat 64 c)] := by
  simp [Lower.lowerArgs, ha, hb, lower_n]

/-- A slot expression: a constant or a local. -/
def SlotE (e : Syntax.PExpr) : Prop := (∃ c, e = Syntax.n c) ∨ ∃ x, e = Syntax.v x

theorem slotE_lower {e : Syntax.PExpr} (h : SlotE e) : ∃ E, Lower.lowerExp e = some E := by
  rcases h with ⟨c, rfl⟩ | ⟨x, rfl⟩
  · exact ⟨_, rfl⟩
  · exact ⟨_, rfl⟩

/-! ## The leaves' tables hold every leaf -/

theorem idx_of_mem {α : Type} [BEq α] [LawfulBEq α] : ∀ {L : List α} {b : α}, b ∈ L →
    ∃ i, L.findIdx? (· == b) = some i ∧ L[i]? = some b
  | a :: L, b, h => by
    rw [List.findIdx?_cons]
    by_cases e : (a == b) = true
    · exact ⟨0, by rw [if_pos e], by rw [eq_of_beq e]; rfl⟩
    · have hb : b ∈ L := by
        rcases List.mem_cons.1 h with rfl | h
        · exact absurd (beq_self_eq_true _) e
        · exact h
      obtain ⟨i, hi, hg⟩ := idx_of_mem hb
      exact ⟨i + 1, by rw [if_neg e, hi]; rfl, hg⟩

theorem class_idx {b : List Nat} (h : Leaf.cls b ∈ allLeaves) : classes[classIndex b]? = some b := by
  have hb : b ∈ classes := List.mem_eraseDups.2 (List.mem_filterMap.2 ⟨_, h, rfl⟩)
  obtain ⟨i, hi, hg⟩ := idx_of_mem hb
  unfold classIndex; rw [hi]; exact hg

theorem text_idx {bs : List Nat} {c : Bool} (h : Leaf.text bs c ∈ allLeaves) :
    texts[textIndex (bs, c)]? = some (bs, c) := by
  have hb : (bs, c) ∈ texts := List.mem_eraseDups.2 (List.mem_filterMap.2 ⟨_, h, rfl⟩)
  obtain ⟨i, hi, hg⟩ := idx_of_mem hb
  unfold textIndex; rw [hi]; exact hg

theorem leafOf_some {t : Abnf.Term} {lf : Leaf} (h : leafOf t = some lf) :
    (∃ rs, classOf steps t = some rs ∧ lf = .cls (bitsOf rs)) ∨
      ∃ bs c, textOf steps t = some (bs, c) ∧ lf = .text bs (c && bs.any fun b => 97 ≤ b && b ≤ 122) := by
  unfold leafOf at h
  split at h
  · rename_i rs hrs; cases h; exact .inl ⟨rs, hrs, rfl⟩
  · cases ht : textOf steps t with
    | none => rw [ht] at h; cases h
    | some p =>
      obtain ⟨bs, c⟩ := p
      rw [ht] at h; cases h; exact .inr ⟨bs, c, rfl, rfl⟩

theorem steps_pos : 0 < steps := by decide +kernel

theorem steps_succ : ∃ s', steps = s' + 1 := ⟨steps - 1, by have := steps_pos; omega⟩

/-- A byte's range, a string and numeric values are leaves. -/
theorem leafOf_range {lo hi : Nat} : leafOf (.range lo hi) ≠ none := by
  obtain ⟨s', hs⟩ := steps_succ
  unfold leafOf; rw [hs]; exact fun h => nomatch h

theorem leafOf_text {s : String} : leafOf (.text s) ≠ none := by
  obtain ⟨s', hs⟩ := steps_succ
  unfold leafOf; rw [hs]
  split
  · exact fun h => nomatch h
  · exact fun h => nomatch h

theorem leafOf_exact {s : List Nat} : leafOf (.exact s) ≠ none := by
  obtain ⟨s', hs⟩ := steps_succ
  unfold leafOf; rw [hs]
  split
  · exact fun h => nomatch h
  · exact fun h => nomatch h

/-! ## The calls `gen` makes -/

section calls
variable (o : Oracle σ) {ofs : Nat} {A : Word} {s0 : PancakeState σ} {rt : String} {l : List (String × Value)}
  {F : (Word → Word) → Prop}

theorem mem_setClear : setClear .none ofs ∈ functions .none ofs := List.mem_append_left _ (.head _)
theorem mem_setUnion : setUnion .none ofs ∈ functions .none ofs :=
  List.mem_append_left _ (.tail _ (.tail _ (.head _)))
theorem mem_setCopy : setCopy .none ofs ∈ functions .none ofs :=
  List.mem_append_left _ (.tail _ (.tail _ (.tail _ (.head _))))
theorem mem_setVoid : setVoid .none ofs ∈ functions .none ofs :=
  List.mem_append_left _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))
theorem mem_setMinus : setMinus .none ofs ∈ functions .none ofs :=
  List.mem_append_left _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))))
theorem mem_setGrow : setGrow ∈ functions .none ofs :=
  List.mem_append_left _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))))
theorem mem_setEmpty : setEmpty .none ofs ∈ functions .none ofs :=
  List.mem_append_left _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))))))
theorem mem_leafClass : leafClass .none ofs ∈ functions .none ofs := List.mem_append_left _
  (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))))))))
theorem mem_leafText : leafText .none ofs ∈ functions .none ofs := List.mem_append_left _
  (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))))))))

theorem ruleFun_comment : ruleFun .none ofs commentRule = ruleComment .none ofs := by
  unfold ruleFun; rw [if_pos (beq_self_eq_true _)]

theorem comment_in : commentRule ∈ order :=
  order_has (by rw [AbnfMatch.comment_eq]; decide +kernel) (by unfold hasFun; rw [beq_self_eq_true]; rfl)

theorem mem_ruleComment : ruleComment .none ofs ∈ functions .none ofs :=
  List.mem_append_right _ (List.mem_map.2 ⟨commentRule, comment_in, ruleFun_comment⟩)

/-- **A call of `setClear`.** -/
theorem clear_frag (hA : Area ofs A s0) (hcode : ProgCode s0.code ofs) (hrt : Fresh rt l = true)
    {e1 : Syntax.PExpr} {E1 : PancakeExp} (he1 : Lower.lowerExp e1 = some E1) {k : Nat}
    (hk : k < slots) (hv1 : ∀ u, RunF s0 l F u → eval u E1 = some (BitVec.ofNat 64 k))
    (hall : ∀ m, F m → AllSets A m) :
    Frag o [.call rt "setClear" [e1]] (RunF s0 l F)
      (fun u => ∃ v, RunF s0 ((rt, v) :: l) (fun m' => ∃ m, F m ∧ ClearRet A k m v m') u) :=
  progCall_frag o hA (f := setClear .none ofs) (args := [E1]) (vs := [BitVec.ofNat 64 k])
    (by show ["d"].Nodup; decide) (by simp [Lower.lowerArgs, he1])
    (progCode_of hcode mem_setClear) rfl (fun u h => by simp only [evalArgs, hv1 u h]) (R := ClearRet A k)
    (fun s1 hA1 _ _ _ hloc hF => let ⟨_, hS⟩ := hall _ hF k hk; setClear_ok o hA1 hk ((hloc "d").trans rfl) hS)
    hrt fun m m' v hF hr => ⟨m, hF, hr⟩

/-- **A call of `setCopy`.** -/
theorem copy_frag (hA : Area ofs A s0) (hcode : ProgCode s0.code ofs) (hrt : Fresh rt l = true)
    {e1 e2 : Syntax.PExpr} {E1 E2 : PancakeExp} (he1 : Lower.lowerExp e1 = some E1)
    (he2 : Lower.lowerExp e2 = some E2) {kd ks : Nat} (h1 : kd < slots) (h2 : ks < slots) (hne : kd ≠ ks)
    (hv1 : ∀ u, RunF s0 l F u → eval u E1 = some (BitVec.ofNat 64 kd))
    (hv2 : ∀ u, RunF s0 l F u → eval u E2 = some (BitVec.ofNat 64 ks)) {Ss : Nat → Bool}
    (hS : ∀ m, F m → SetAt m A ks Ss ∧ AllSets A m) :
    Frag o [.call rt "setCopy" [e1, e2]] (RunF s0 l F)
      (fun u => ∃ v, RunF s0 ((rt, v) :: l) (fun m' => ∃ m, F m ∧ CopyRet A kd Ss m v m') u) :=
  progCall_frag o hA (f := setCopy .none ofs) (args := [E1, E2]) (vs := [BitVec.ofNat 64 kd, BitVec.ofNat 64 ks])
    (by show ["d", "s"].Nodup; decide) (by simp [Lower.lowerArgs, he1, he2]) (progCode_of hcode mem_setCopy) rfl
    (fun u h => by simp only [evalArgs, hv1 u h, hv2 u h]) (R := CopyRet A kd Ss)
    (fun s1 hA1 _ _ _ hloc hF => let ⟨_, hSd⟩ := (hS _ hF).2 kd h1
      setCopy_ok o hA1 h1 h2 hne ((hloc "d").trans rfl) ((hloc "s").trans rfl) hSd (hS _ hF).1)
    hrt fun m m' v hF hr => ⟨m, hF, hr⟩

/-- **A call of `setUnion`.** -/
theorem union_frag (hA : Area ofs A s0) (hcode : ProgCode s0.code ofs) (hrt : Fresh rt l = true)
    {e1 e2 : Syntax.PExpr} {E1 E2 : PancakeExp} (he1 : Lower.lowerExp e1 = some E1)
    (he2 : Lower.lowerExp e2 = some E2) {kd ks : Nat} (h1 : kd < slots) (h2 : ks < slots)
    (hv1 : ∀ u, RunF s0 l F u → eval u E1 = some (BitVec.ofNat 64 kd))
    (hv2 : ∀ u, RunF s0 l F u → eval u E2 = some (BitVec.ofNat 64 ks)) {Sd Ss : Nat → Bool}
    (hS : ∀ m, F m → SetAt m A kd Sd ∧ SetAt m A ks Ss) :
    Frag o [.call rt "setUnion" [e1, e2]] (RunF s0 l F)
      (fun u => ∃ v, RunF s0 ((rt, v) :: l) (fun m' => ∃ m, F m ∧ UnionRet A kd Sd Ss m v m') u) :=
  progCall_frag o hA (f := setUnion .none ofs) (args := [E1, E2]) (vs := [BitVec.ofNat 64 kd, BitVec.ofNat 64 ks])
    (by show ["d", "s"].Nodup; decide) (by simp [Lower.lowerArgs, he1, he2]) (progCode_of hcode mem_setUnion) rfl
    (fun u h => by simp only [evalArgs, hv1 u h, hv2 u h]) (R := UnionRet A kd Sd Ss)
    (fun s1 hA1 _ _ _ hloc hF => setUnion_ok o hA1 h1 h2 ((hloc "d").trans rfl) ((hloc "s").trans rfl) (hS _ hF).1
      (hS _ hF).2)
    hrt fun m m' v hF hr => ⟨m, hF, hr⟩

/-- **A call of `setVoid`.** -/
theorem void_frag (hA : Area ofs A s0) (hcode : ProgCode s0.code ofs) (hrt : Fresh rt l = true)
    {e1 e2 : Syntax.PExpr} {E1 E2 : PancakeExp} (he1 : Lower.lowerExp e1 = some E1)
    (he2 : Lower.lowerExp e2 = some E2) {ks kd : Nat} (h1 : ks < slots) (h2 : kd < slots)
    (hv1 : ∀ u, RunF s0 l F u → eval u E1 = some (BitVec.ofNat 64 ks))
    (hv2 : ∀ u, RunF s0 l F u → eval u E2 = some (BitVec.ofNat 64 kd)) {Ss : Nat → Bool}
    (hS : ∀ m, F m → SetAt m A ks Ss ∧ AllSets A m) :
    Frag o [.call rt "setVoid" [e1, e2]] (RunF s0 l F)
      (fun u => ∃ v, RunF s0 ((rt, v) :: l) (fun m' => ∃ m, F m ∧ VoidRet A kd Ss m v m') u) :=
  progCall_frag o hA (f := setVoid .none ofs) (args := [E1, E2]) (vs := [BitVec.ofNat 64 ks, BitVec.ofNat 64 kd])
    (by show ["s", "d"].Nodup; decide) (by simp [Lower.lowerArgs, he1, he2]) (progCode_of hcode mem_setVoid) rfl
    (fun u h => by simp only [evalArgs, hv1 u h, hv2 u h]) (R := VoidRet A kd Ss)
    (fun s1 hA1 _ _ _ hloc hF => let ⟨_, hSd⟩ := (hS _ hF).2 kd h2
      setVoid_ok o hA1 h1 h2 ((hloc "s").trans rfl) ((hloc "d").trans rfl) (hS _ hF).1 hSd)
    hrt fun m m' v hF hr => ⟨m, hF, hr⟩

/-- **A call of `setEmpty`.** -/
theorem empty_frag (hA : Area ofs A s0) (hcode : ProgCode s0.code ofs) (hrt : Fresh rt l = true)
    {e1 : Syntax.PExpr} {E1 : PancakeExp} (he1 : Lower.lowerExp e1 = some E1) {k : Nat}
    (hk : k < slots) (hv1 : ∀ u, RunF s0 l F u → eval u E1 = some (BitVec.ofNat 64 k)) {S : Nat → Bool}
    (hS : ∀ m, F m → SetAt m A k S) :
    Frag o [.call rt "setEmpty" [e1]] (RunF s0 l F)
      (fun u => ∃ v, RunF s0 ((rt, v) :: l) (fun m' => ∃ m, F m ∧ EmptyRet S m v m') u) :=
  progCall_frag o hA (f := setEmpty .none ofs) (args := [E1]) (vs := [BitVec.ofNat 64 k])
    (by show ["s"].Nodup; decide) (by simp [Lower.lowerArgs, he1]) (progCode_of hcode mem_setEmpty) rfl
    (fun u h => by simp only [evalArgs, hv1 u h]) (R := EmptyRet S)
    (fun s1 hA1 _ _ _ hloc hF => setEmpty_ok o hA1 hk ((hloc "s").trans rfl) (hS _ hF))
    hrt fun m m' v hF hr => ⟨m, hF, hr⟩

/-- **A call of `setGrow`.** -/
theorem grow_frag (hA : Area ofs A s0) (hcode : ProgCode s0.code ofs) (hrt : Fresh rt l = true)
    {e1 e2 : Syntax.PExpr} {E1 E2 : PancakeExp} (he1 : Lower.lowerExp e1 = some E1)
    (he2 : Lower.lowerExp e2 = some E2) {kx kd : Nat} (hkx : kx < slots) (hkd : kd < slots) (hne : kx ≠ kd)
    (hv1 : ∀ u, RunF s0 l F u → eval u E1 = some (BitVec.ofNat 64 kx))
    (hv2 : ∀ u, RunF s0 l F u → eval u E2 = some (BitVec.ofNat 64 kd)) {Sx Sd : Nat → Bool}
    (hS : ∀ m, F m → SetAt m A kx Sx ∧ SetAt m A kd Sd) :
    Frag o [.call rt "setGrow" [e1, e2]] (RunF s0 l F)
      (fun u => ∃ v, RunF s0 ((rt, v) :: l) (fun m' => ∃ m, F m ∧ GrowRet A kx kd Sx Sd m v m') u) :=
  progCall_frag o hA (f := setGrow) (args := [E1, E2]) (vs := [BitVec.ofNat 64 kx, BitVec.ofNat 64 kd])
    (by show ["x", "d"].Nodup; decide) (by simp [Lower.lowerArgs, he1, he2]) (progCode_of hcode mem_setGrow) rfl
    (fun u h => by simp only [evalArgs, hv1 u h, hv2 u h]) (R := GrowRet A kx kd Sx Sd)
    (fun s1 hA1 hc _ _ hloc hF => by
      obtain ⟨bm, hbm, -⟩ := setMinus_ok o (area_locals hA1 fun k =>
        [("d", BitVec.ofNat 64 kx), ("s", BitVec.ofNat 64 kd)].lookup k) hkx hkd rfl rfl (hS _ hF).1 (hS _ hF).2
      obtain ⟨bu, hbu, -⟩ := setUnion_ok o (area_locals hA1 fun k =>
        [("d", BitVec.ofNat 64 kd), ("s", BitVec.ofNat 64 kx)].lookup k) hkd hkx rfl rfl (hS _ hF).2 (hS _ hF).1
      exact setGrow_ok o hA1 hkx hkd hne ((hloc "x").trans rfl) ((hloc "d").trans rfl) (hS _ hF).1 (hS _ hF).2 hbm
        (by rw [hc]; exact progCode_of hcode mem_setMinus bm hbm) hbu
        (by rw [hc]; exact progCode_of hcode mem_setUnion bu hbu))
    hrt fun m m' v hF hr => ⟨m, hF, hr⟩

/-- **A call of `leafClass`.** -/
theorem class_frag (hA : Area ofs A s0) (hcode : ProgCode s0.code ofs) (hrt : Fresh rt l = true)
    {e1 e2 : Syntax.PExpr} {E1 E2 : PancakeExp} (he1 : Lower.lowerExp e1 = some E1)
    (he2 : Lower.lowerExp e2 = some E2) {ks kd k : Nat} (hks : ks < slots) (hkd : kd < slots) (hne : ks ≠ kd)
    (hk : k < classes.length) (hv1 : ∀ u, RunF s0 l F u → eval u E1 = some (BitVec.ofNat 64 ks))
    (hv2 : ∀ u, RunF s0 l F u → eval u E2 = some (BitVec.ofNat 64 kd)) {S : Nat → Bool}
    {bytes : List (BitVec 8)} (hlen : bytes.length ≤ inputMax)
    (hS : ∀ m, F m → SetAt m A ks S ∧ Base s0 A bytes m) :
    Frag o [.call rt "leafClass" [e1, e2, Syntax.n k]] (RunF s0 l F)
      (fun u => ∃ v, RunF s0 ((rt, v) :: l)
        (fun m' => ∃ m, F m ∧ LeafRet A kd (below (classAdd S bytes k) (64 * setWords)) m v m') u) :=
  progCall_frag o hA (f := leafClass .none ofs) (args := [E1, E2, .const (BitVec.ofNat 64 k)])
    (vs := [BitVec.ofNat 64 ks, BitVec.ofNat 64 kd, BitVec.ofNat 64 k])
    (by show ["s", "d", "k"].Nodup; decide) (by simp [Lower.lowerArgs, he1, he2]; rfl)
    (progCode_of hcode mem_leafClass) rfl (fun u h => by simp only [evalArgs, hv1 u h, hv2 u h]; rfl)
    (R := LeafRet A kd (below (classAdd S bytes k) (64 * setWords)))
    (fun s1 hA1 _ hm hbe hloc hF => let ⟨_, hSd⟩ := (hS _ hF).2.1 kd hkd
      leafClass_ok o hA1 hks hkd hne hk ((hloc "s").trans rfl) ((hloc "d").trans rfl) ((hloc "k").trans rfl)
        (hS _ hF).1 hSd hlen (hS _ hF).2.2.1 (reads_of hm hbe (hS _ hF).2.2.2))
    hrt fun m m' v hF hr => ⟨m, hF, hr⟩

/-- **A call of `leafText`.** -/
theorem text_frag (hA : Area ofs A s0) (hcode : ProgCode s0.code ofs) (hrt : Fresh rt l = true)
    {e1 e2 : Syntax.PExpr} {E1 E2 : PancakeExp} (he1 : Lower.lowerExp e1 = some E1)
    (he2 : Lower.lowerExp e2 = some E2) {ks kd k : Nat} (hks : ks < slots) (hkd : kd < slots) (hne : ks ≠ kd)
    (hk : k < texts.length) (hv1 : ∀ u, RunF s0 l F u → eval u E1 = some (BitVec.ofNat 64 ks))
    (hv2 : ∀ u, RunF s0 l F u → eval u E2 = some (BitVec.ofNat 64 kd)) {S : Nat → Bool}
    {bytes : List (BitVec 8)} (hlen : bytes.length ≤ inputMax)
    (hS : ∀ m, F m → SetAt m A ks S ∧ Base s0 A bytes m) :
    Frag o [.call rt "leafText" [e1, e2, Syntax.n k]] (RunF s0 l F)
      (fun u => ∃ v, RunF s0 ((rt, v) :: l)
        (fun m' => ∃ m, F m ∧ LeafRet A kd (below (textAdd S bytes k) (64 * setWords)) m v m') u) :=
  progCall_frag o hA (f := leafText .none ofs) (args := [E1, E2, .const (BitVec.ofNat 64 k)])
    (vs := [BitVec.ofNat 64 ks, BitVec.ofNat 64 kd, BitVec.ofNat 64 k])
    (by show ["s", "d", "k"].Nodup; decide) (by simp [Lower.lowerArgs, he1, he2]; rfl)
    (progCode_of hcode mem_leafText) rfl (fun u h => by simp only [evalArgs, hv1 u h, hv2 u h]; rfl)
    (R := LeafRet A kd (below (textAdd S bytes k) (64 * setWords)))
    (fun s1 hA1 _ hm hbe hloc hF => let ⟨_, hSd⟩ := (hS _ hF).2.1 kd hkd
      leafText_ok o hA1 hks hkd hne hk ((hloc "s").trans rfl) ((hloc "d").trans rfl) ((hloc "k").trans rfl)
        (hS _ hF).1 hSd hlen (hS _ hF).2.2.1 (reads_of hm hbe (hS _ hF).2.2.2))
    hrt fun m m' v hF hr => ⟨m, hF, hr⟩


end calls

/-! ## What `gen`'s statements do -/

/-- `r`'s statements lower and declare locals of generated names numbered from `k` to below `r.2`. -/
def Shape (k : Nat) (r : List Syntax.PStmt × Nat) : Prop :=
  LowKK r.1 ∧ k ≤ r.2 ∧ ∀ y ∈ declared r.1, ∃ j, k ≤ j ∧ j < r.2 ∧ GenName y j

/-- What a term's statements leave: slot `kd` the ends of `t`'s matches from `S`, every slot a set, every word as in
`m` but those of slot `kd` and of the slots from `free` on. -/
def Left (A : Word) (s0 : PancakeState σ) (bytes : List (BitVec 8)) (t : Abnf.Term) (S : Nat → Bool)
    (kd free : Nat) (F : (Word → Word) → Prop) (m' : Word → Word) : Prop :=
  ∃ m, F m ∧ Holds A m' kd (Ends bytes t S) ∧ Base s0 A bytes m' ∧ Kept A kd free m m'

/-- What statements `r.1` for term `t` do, from slot `s` into slot `d` with the slots from `free` on their own,
their locals numbered from `k` to below `r.2`: from any state where slot `s` holds `S` and every call has what it
takes, what `Left` says. `nn`, the input's length, is a local where `rp` says the statements read it. -/
def Does (o : Oracle σ) (A : Word) (s0 : PancakeState σ) (bytes : List (BitVec 8)) (rp : Bool) (t : Abnf.Term)
    (s d : Syntax.PExpr) (free k : Nat) (r : List Syntax.PStmt × Nat) : Prop :=
  ∀ (l : List (String × Value)) (F : (Word → Word) → Prop) (ks kd : Nat) (S : Nat → Bool),
    SlotIs l s ks → SlotIs l d kd → ks < free → kd < free → ks ≠ kd → Avoid l k r.2 →
    (rp = true → ("nn", BitVec.ofNat 64 bytes.length) ∈ l) →
    (∀ m, F m → SetAt m A ks S ∧ Base s0 A bytes m) →
    Frag o r.1 (RunF s0 l F)
      (fun u => ∃ l', Named l' k r.2 ∧ RunF s0 (l' ++ l) (Left A s0 bytes t S kd free F) u)

/-- `g` does what `gen` is to do with `f` steps, for the terms they reach. -/
def GenOk (o : Oracle σ) (ofs : Nat) (A : Word) (s0 : PancakeState σ) (bytes : List (BitVec 8)) (f : Nat)
    (g : Gen) : Prop :=
  ∀ t s d free k, AbnfOrder.enough f t = true →
    (∀ j ∈ callsOf f t, BodyOk o ofs s0.code j ∧ free + needOf f t ≤ frameOf j) →
    (∀ lf ∈ leavesOf f t, lf ∈ allLeaves) → free + needOf f t ≤ slots → SlotE s → SlotE d →
    Shape k (g t s d free k) ∧ Does o A s0 bytes (repeats f t) t s d free k (g t s d free k)

section cases
variable (o : Oracle σ) {ofs : Nat} {A : Word} {s0 : PancakeState σ} {bytes : List (BitVec 8)}

/-- What a call leaves in slot `kd` alone, the ends of `t`'s matches, `Left` leaves. -/
theorem left_one (hA : Area ofs A s0) (hlen : bytes.length ≤ inputMax)
    {t : Abnf.Term} {S T : Nat → Bool} (hT : ∀ e, T e = true ↔ Ends bytes t S e) {kd free : Nat}
    (hkd : kd < slots) {F : (Word → Word) → Prop} (hF : ∀ m, F m → Base s0 A bytes m) {m m' : Word → Word}
    (hm : F m) (hS : SetAt m' A kd T) (hfr : Frame A kd m m') : Left A s0 bytes t S kd free F m' :=
  ⟨m, hm, by unfold Holds; rw [← setOf_eq hT]; exact hS,
    base_keep hA.hA hlen hkd (hF m hm) (kept_frame (free := 0) (.inl rfl) hfr)
    (allSets_frame (hF m hm).1 hkd hS hfr), kept_frame (.inl rfl) hfr⟩

/-- **A leaf**: its call. -/
theorem leaf_ok (hA : Area ofs A s0) (hcode : ProgCode s0.code ofs) (hlen : bytes.length ≤ inputMax)
    {t : Abnf.Term} {lf : Leaf} (ht : leafOf t = some lf) (hlf : lf ∈ allLeaves)
    {s d : Syntax.PExpr} (hs : SlotE s) (hd : SlotE d) {free : Nat} (hfree : free ≤ slots) (k : Nat) (rp : Bool) :
    Shape k ([leafCall s!"c{k}" lf s d], k + 1) ∧
      Does o A s0 bytes rp t s d free k ([leafCall s!"c{k}" lf s d], k + 1) := by
  obtain ⟨Es, hEs⟩ := slotE_lower hs
  obtain ⟨Ed, hEd⟩ := slotE_lower hd
  refine ⟨⟨?_, Nat.le_succ _, ?_⟩, ?_⟩
  · cases lf <;> exact lowKK_call (lowerArgs_three hEs hEd _)
  · intro y hy
    cases lf <;>
    · simp only [leafCall, declared, List.mem_cons, List.not_mem_nil, or_false] at hy
      subst hy; exact ⟨k, Nat.le_refl _, Nat.lt_succ_self _, name_c k⟩
  · intro l F ks kd S hS hD hks hkd hne hav _ hF
    obtain ⟨Es', hEs', hvs⟩ := slotIs_eval (σ := σ) hS
    obtain ⟨Ed', hEd', hvd⟩ := slotIs_eval (σ := σ) hD
    have hrt : Fresh s!"c{k}" l = true := fresh_of hav (Nat.le_refl _) (Nat.lt_succ_self _) (name_c k)
    have hkd' : kd < slots := by omega
    have post : ∀ T : Nat → Bool, (∀ e, T e = true ↔ Ends bytes t S e) → ∀ u : PancakeState σ,
        (∃ v, RunF s0 ((s!"c{k}", v) :: l) (fun m' => ∃ m, F m ∧ LeafRet A kd T m v m') u) →
        ∃ l', Named l' k (k + 1) ∧ RunF s0 (l' ++ l) (Left A s0 bytes t S kd free F) u :=
      fun T hT u ⟨v, h⟩ => ⟨[(s!"c{k}", v)], named_one (name_c k) (Nat.le_refl _) (Nat.lt_succ_self _),
        runF_mono h (fun _ hq => hq) fun m' ⟨m, hm, hr⟩ =>
          left_one hA hlen hT hkd' (fun m hm => (hF m hm).2) hm hr.2.1 hr.2.2⟩
    rcases leafOf_some ht with ⟨rs, hrs, rfl⟩ | ⟨bs, c, hbs, rfl⟩
    · have hidx := class_idx hlf
      exact frag_conseq (class_frag o hA hcode hrt hEs' hEd' (by omega) hkd' hne
        (List.getElem?_eq_some_iff.1 hidx).1 (fun u h => hvs u h.1.vals) (fun u h => hvd u h.1.vals) hlen hF)
        (fun _ h => h) (post _ fun e => classSet_iff hrs hidx hlen e)
    · have hidx := text_idx hlf
      exact frag_conseq (text_frag o hA hcode hrt hEs' hEd' (by omega) hkd' hne
        (List.getElem?_eq_some_iff.1 hidx).1 (fun u h => hvs u h.1.vals) (fun u h => hvd u h.1.vals) hlen hF)
        (fun _ h => h) (post _ fun e => textSet_iff hbs hidx hlen e)

/-- **A rule's function called.** -/
theorem ref_ok (hA : Area ofs A s0) (hlen : bytes.length ≤ inputMax)
    {i : Nat} (hb : BodyOk o ofs s0.code i) {s d : Syntax.PExpr} (hs : SlotE s) (hd : SlotE d)
    {free : Nat} (hfi : free ≤ frameOf i) (hfree : free ≤ slots) (k : Nat) (rp : Bool) :
    Shape k ([.call s!"c{k}" (funName i) [s, d]], k + 1) ∧
      Does o A s0 bytes rp (.ref i) s d free k ([.call s!"c{k}" (funName i) [s, d]], k + 1) := by
  obtain ⟨Es, hEs⟩ := slotE_lower hs
  obtain ⟨Ed, hEd⟩ := slotE_lower hd
  refine ⟨⟨lowKK_call (lowerArgs_two hEs hEd), Nat.le_succ _, fun y hy => ?_⟩, ?_⟩
  · simp only [declared, List.mem_cons, List.not_mem_nil, or_false] at hy
    subst hy; exact ⟨k, Nat.le_refl _, Nat.lt_succ_self _, name_c k⟩
  · intro l F ks kd S hS hD hks hkd hne hav _ hF
    obtain ⟨Es', hEs', hvs⟩ := slotIs_eval (σ := σ) hS
    obtain ⟨Ed', hEd', hvd⟩ := slotIs_eval (σ := σ) hD
    have hrt : Fresh s!"c{k}" l = true := fresh_of hav (Nat.le_refl _) (Nat.lt_succ_self _) (name_c k)
    have hkd' : kd < slots := by omega
    refine frag_conseq (ruleCall_frag o hA hrt hb hEs' hEd' (by omega) (by omega) hne (fun u h => hvs u h.1.vals)
      (fun u h => hvd u h.1.vals) hlen hF) (fun _ h => h) fun u ⟨v, h⟩ => ⟨[(s!"c{k}", v)],
        named_one (name_c k) (Nat.le_refl _) (Nat.lt_succ_self _), runF_mono h (fun _ hq => hq) ?_⟩
    rintro m' ⟨m, hm, -, hH, hall, hkept⟩
    exact ⟨m, hm, hH, base_keep hA.hA hlen hkd' (hF m hm).2 hkept hall, kept_wide hfi (.inl rfl) hkept⟩

theorem holds_congr {m : Word → Word} {k : Nat} {P P' : Nat → Prop} (h : Holds A m k P) (hp : ∀ e, P e ↔ P' e) :
    Holds A m k P' := by
  have e : setOf P = setOf P' := setOf_eq fun e => setOf_iff.trans (hp e)
  unfold Holds; rw [← e]; exact h

/-- What statements do for one term they do for another with the same matches. -/
theorem does_congr {rp rp' : Bool} {t t' : Abnf.Term} {s d : Syntax.PExpr} {free k : Nat}
    {r : List Syntax.PStmt × Nat} (h : Does o A s0 bytes rp t s d free k r) (hrp : rp = true → rp' = true)
    (ht : ∀ x e, Matches AbnfRules.grammar (inputOf bytes) t x e ↔
      Matches AbnfRules.grammar (inputOf bytes) t' x e) :
    Does o A s0 bytes rp' t' s d free k r := fun l F ks kd S hS hD hks hkd hne hav hnn hF =>
  frag_conseq (h l F ks kd S hS hD hks hkd hne hav (fun e => hnn (hrp e)) hF) (fun _ h => h)
    fun _ ⟨l', hn, hr⟩ => ⟨l', hn, runF_mono hr (fun _ hq => hq) fun _ ⟨m, hm, hH, hb, hk⟩ =>
      ⟨m, hm, holds_congr hH fun e => ⟨fun ⟨x, hx, hm⟩ => ⟨x, hx, (ht x e).1 hm⟩,
        fun ⟨x, hx, hm⟩ => ⟨x, hx, (ht x e).2 hm⟩⟩, hb, hk⟩⟩

/-- **An empty sequence**: the positions copied. -/
theorem nil_ok (hA : Area ofs A s0) (hcode : ProgCode s0.code ofs) (hlen : bytes.length ≤ inputMax)
    {s d : Syntax.PExpr} (hs : SlotE s) (hd : SlotE d) {free : Nat} (hfree : free ≤ slots) (k : Nat)
    (rp : Bool) :
    Shape k ([.call s!"c{k}" "setCopy" [d, s]], k + 1) ∧
      Does o A s0 bytes rp (.seq []) s d free k ([.call s!"c{k}" "setCopy" [d, s]], k + 1) := by
  obtain ⟨Es, hEs⟩ := slotE_lower hs
  obtain ⟨Ed, hEd⟩ := slotE_lower hd
  refine ⟨⟨lowKK_call (lowerArgs_two hEd hEs), Nat.le_succ _, fun y hy => ?_⟩, ?_⟩
  · simp only [declared, List.mem_cons, List.not_mem_nil, or_false] at hy
    subst hy; exact ⟨k, Nat.le_refl _, Nat.lt_succ_self _, name_c k⟩
  · intro l F ks kd S hS hD hks hkd hne hav _ hF
    obtain ⟨Es', hEs', hvs⟩ := slotIs_eval (σ := σ) hS
    obtain ⟨Ed', hEd', hvd⟩ := slotIs_eval (σ := σ) hD
    have hrt : Fresh s!"c{k}" l = true := fresh_of hav (Nat.le_refl _) (Nat.lt_succ_self _) (name_c k)
    have hkd' : kd < slots := by omega
    refine frag_conseq (copy_frag o hA hcode hrt hEd' hEs' hkd' (by omega) (Ne.symm hne) (fun u h => hvd u h.1.vals)
      (fun u h => hvs u h.1.vals) fun m hm => ⟨(hF m hm).1, (hF m hm).2.1⟩) (fun _ h => h)
      fun u ⟨v, h⟩ => ⟨[(s!"c{k}", v)], named_one (name_c k) (Nat.le_refl _) (Nat.lt_succ_self _),
        runF_mono h (fun _ hq => hq) fun m' ⟨m, hm, hr⟩ =>
          left_one hA hlen (fun e => ?_) hkd' (fun m hm => (hF m hm).2) hm hr.2.1 hr.2.2⟩
    simp only [Ends, AbnfMatch.seq_iff, AbnfMatch.seq_nil_iff]
    exact ⟨fun h => ⟨e, h, rfl⟩, fun ⟨x, hx, he⟩ => he ▸ hx⟩

/-- **An empty choice**: no position. -/
theorem altNil_ok (hA : Area ofs A s0) (hcode : ProgCode s0.code ofs) (hlen : bytes.length ≤ inputMax)
    {s d : Syntax.PExpr} (hd : SlotE d) {free : Nat} (hfree : free ≤ slots) (k : Nat) (rp : Bool) :
    Shape k ([.call s!"c{k}" "setClear" [d]], k + 1) ∧
      Does o A s0 bytes rp (.alt []) s d free k ([.call s!"c{k}" "setClear" [d]], k + 1) := by
  obtain ⟨Ed, hEd⟩ := slotE_lower hd
  refine ⟨⟨lowKK_call (a := [Ed]) (by simp [Lower.lowerArgs, hEd]), Nat.le_succ _, fun y hy => ?_⟩, ?_⟩
  · simp only [declared, List.mem_cons, List.not_mem_nil, or_false] at hy
    subst hy; exact ⟨k, Nat.le_refl _, Nat.lt_succ_self _, name_c k⟩
  · intro l F ks kd S _ hD _ hkd _ hav _ hF
    obtain ⟨Ed', hEd', hvd⟩ := slotIs_eval (σ := σ) hD
    have hrt : Fresh s!"c{k}" l = true := fresh_of hav (Nat.le_refl _) (Nat.lt_succ_self _) (name_c k)
    have hkd' : kd < slots := by omega
    refine frag_conseq (clear_frag o hA hcode hrt hEd' hkd' (fun u h => hvd u h.1.vals) fun m hm => (hF m hm).2.1)
      (fun _ h => h) fun u ⟨v, h⟩ => ⟨[(s!"c{k}", v)], named_one (name_c k) (Nat.le_refl _) (Nat.lt_succ_self _),
        runF_mono h (fun _ hq => hq) fun m' ⟨m, hm, hr⟩ =>
          left_one hA hlen (fun e => ?_) hkd' (fun m hm => (hF m hm).2) hm hr.2.1 hr.2.2⟩
    exact Iff.intro (fun h => nomatch h) fun ⟨_, _, hm⟩ => let ⟨_, ht, _⟩ := AbnfMatch.alt_iff.1 hm; nomatch ht

/-! ## A sequence -/

theorem ends_seq_one {t : Abnf.Term} {X : Nat → Bool} (e : Nat) : Ends bytes (.seq [t]) X e ↔ Ends bytes t X e := by
  simp only [Ends, AbnfMatch.seq_iff, AbnfMatch.seq_cons_iff, AbnfMatch.seq_nil_iff]
  exact ⟨fun ⟨x, hx, q, hq, he⟩ => ⟨x, hx, he ▸ hq⟩, fun ⟨x, hx, hq⟩ => ⟨x, hx, e, hq, rfl⟩⟩

theorem ends_seq_cons {t : Abnf.Term} {ts : List Abnf.Term} {X : Nat → Bool} (e : Nat) :
    Ends bytes (.seq (t :: ts)) X e ↔ Ends bytes (.seq ts) (setOf (Ends bytes t X)) e := by
  simp only [Ends, AbnfMatch.seq_iff, AbnfMatch.seq_cons_iff, setOf_iff]
  exact ⟨fun ⟨x, hx, q, hq, he⟩ => ⟨q, ⟨x, hx, hq⟩, he⟩,
    fun ⟨q, ⟨x, hx, hq⟩, he⟩ => ⟨x, hx, q, hq, he⟩⟩

theorem clock_named {l : List (String × Value)} {a b : Nat} {G : (Word → Word) → Prop} :
    Safe.ClockFree (σ := σ) fun u => ∃ l', Named l' a b ∧ RunF s0 (l' ++ l) G u :=
  fun u c ⟨l', hn, h⟩ => ⟨l', hn, runF_clock _ _ _ u c h⟩

theorem restore_named {l : List (String × Value)} {a b lo hi : Nat} {G : (Word → Word) → Prop}
    (hav : Avoid l lo hi) (hab : a ≤ hi) {u : PancakeState σ} {y : String} (v : Option Value)
    (hy : ∃ j, lo ≤ j ∧ j < a ∧ GenName y j) (h : ∃ l', Named l' a b ∧ RunF s0 (l' ++ l) G u) :
    ∃ l', Named l' a b ∧ RunF s0 (l' ++ l) G (restore u y v) := by
  obtain ⟨l', hn, hr⟩ := h
  obtain ⟨j, h1, h2, hg⟩ := hy
  refine ⟨l', hn, runF_restore hr (fresh_app (fresh_named hn (.inl h2) hg) ?_) v⟩
  exact fresh_of hav h1 (by omega) hg

theorem slotE_src {s : Syntax.PExpr} (hs : SlotE s) (free i : Nat) :
    SlotE (if i == 0 then s else Syntax.n (free + (i + 1) % 2)) := by
  split
  · exact hs
  · exact .inl ⟨_, rfl⟩

/-- What a sequence's terms from the `i`th leave: slot `d` the ends of their matches from the positions of the slot
term `i` reads. -/
def SeqPre (f : Nat) (free : Nat) (ts : List Abnf.Term) (code : String → Option (List String × PancakeProg)) :
    Prop :=
  ∀ t ∈ ts, AbnfOrder.enough f t = true ∧
    (∀ j ∈ callsOf f t, BodyOk o ofs code j ∧ free + 2 + needOf f t ≤ frameOf j) ∧
    (∀ lf ∈ leavesOf f t, lf ∈ allLeaves) ∧ free + 2 + needOf f t ≤ slots

/-- **A sequence's terms from the `i`th.** -/
theorem seqFrom_ok (hA : Area ofs A s0) (hcode : ProgCode s0.code ofs) (hlen : bytes.length ≤ inputMax)
    {f : Nat} {g : Gen} (hg : GenOk o ofs A s0 bytes f g) {s d : Syntax.PExpr} (hs : SlotE s)
    (hd : SlotE d) {free : Nat} (hfree : free + 2 ≤ slots) :
    ∀ (ts : List Abnf.Term) (i k : Nat), ts ≠ [] → SeqPre o (ofs := ofs) f free ts s0.code →
    Shape k (seqFrom g s d free i ts k) ∧
    ∀ (l : List (String × Value)) (F : (Word → Word) → Prop) (ks kd : Nat) (X : Nat → Bool),
      SlotIs l (if i == 0 then s else Syntax.n (free + (i + 1) % 2)) ks → SlotIs l d kd → ks < free + 2 →
      ks ≠ free + i % 2 → kd < free → ks ≠ kd → Avoid l k (seqFrom g s d free i ts k).2 →
      (ts.any (repeats f) = true → ("nn", BitVec.ofNat 64 bytes.length) ∈ l) →
      (∀ m, F m → SetAt m A ks X ∧ Base s0 A bytes m) →
      Frag o (seqFrom g s d free i ts k).1 (RunF s0 l F)
        (fun u => ∃ l', Named l' k (seqFrom g s d free i ts k).2 ∧
          RunF s0 (l' ++ l) (Left A s0 bytes (.seq ts) X kd free F) u) := by
  intro ts
  induction ts with
  | nil => intro _ _ h; exact absurd rfl h
  | cons t ts ih =>
    intro i k _ hts
    obtain ⟨hen, hca, hle, hsl⟩ := hts t (List.mem_cons_self ..)
    cases ts with
    | nil =>
      obtain ⟨hsh, hdo⟩ := hg t _ d (free + 2) k hen hca hle hsl (slotE_src hs free i) hd
      generalize hb : g t (if i == 0 then s else Syntax.n (free + (i + 1) % 2)) d (free + 2) k = B at hsh hdo
      obtain ⟨b, k'⟩ := B
      have e : seqFrom g s d free i [t] k = (b, k' + 1) := by rw [seqFrom, hb]
      rw [e]
      refine ⟨⟨hsh.1, Nat.le_succ_of_le hsh.2.1, fun y hy =>
        let ⟨j, h1, h2, h3⟩ := hsh.2.2 y hy; ⟨j, h1, by omega, h3⟩⟩, ?_⟩
      intro l F ks kd X hS hD hks _ hkd hne hav hnn hF
      exact frag_conseq (hdo l F ks kd X hS hD hks (by omega) hne (avoid_mono hav (Nat.le_refl _) (Nat.le_succ _))
        (fun e => hnn (by simp [e])) hF) (fun _ h => h) fun u ⟨l', hn, hr⟩ =>
          ⟨l', named_mono hn (Nat.le_refl _) (Nat.le_succ _), runF_mono hr (fun _ hq => hq)
            fun _ ⟨m, hm, hH, hB, hK⟩ =>
              ⟨m, hm, holds_congr hH fun e => (ends_seq_one e).symm, hB, kept_wide (by omega) (.inl rfl) hK⟩⟩
    | cons t' ts' =>
      obtain ⟨ihs, ihd⟩ := ih (i + 1) k (List.cons_ne_nil _ _) fun x hx => hts x (List.mem_cons_of_mem _ hx)
      generalize hR : seqFrom g s d free (i + 1) (t' :: ts') k = Rr at ihs ihd
      obtain ⟨R, k1⟩ := Rr
      obtain ⟨hsh, hdo⟩ := hg t _ (Syntax.n (free + i % 2)) (free + 2) k1 hen hca hle hsl (slotE_src hs free i)
        (.inl ⟨_, rfl⟩)
      generalize hb : g t (if i == 0 then s else Syntax.n (free + (i + 1) % 2)) (Syntax.n (free + i % 2)) (free + 2)
        k1 = B at hsh hdo
      obtain ⟨b, k2⟩ := B
      have e : seqFrom g s d free i (t :: t' :: ts') k = (b ++ [.call s!"e{k2}" "setVoid" [Syntax.n (free + i % 2), d],
          .ite (Syntax.v s!"e{k2}") [] R], k2 + 1) := by
        rw [seqFrom] <;> first | simp only [hR, hb] | exact fun h => nomatch h
      rw [e]
      obtain ⟨Ed, hEd⟩ := slotE_lower hd
      have hk1 := ihs.2.1
      have hk2 := hsh.2.1
      have hlowT : LowKK [.call s!"e{k2}" "setVoid" [Syntax.n (free + i % 2), d], .ite (Syntax.v s!"e{k2}") [] R] :=
        lowKK_append (xs := [_]) (lowKK_call (lowerArgs_two (lower_n _) hEd)) (lowKK_ite rfl lowKK_nil ihs.1)
      refine ⟨⟨lowKK_append hsh.1 hlowT, by omega, fun y hy => ?_⟩, ?_⟩
      · rw [declared_append] at hy
        rcases List.mem_append.1 hy with hy | hy
        · obtain ⟨j, h1, h2, h3⟩ := hsh.2.2 y hy
          exact ⟨j, by omega, by omega, h3⟩
        · simp only [declared, List.mem_cons, List.not_mem_nil, or_false] at hy
          subst hy; exact ⟨k2, by omega, Nat.lt_succ_self _, name_e k2⟩
      intro l F ks kd X hS hD hks hks2 hkd hne hav hnn hF
      have hkd' : kd < slots := by omega
      have hdst : free + i % 2 < slots := by omega
      obtain ⟨Ed', hEd', hvd⟩ := slotIs_eval (σ := σ) hD
      refine frag_append (hdo l F ks (free + i % 2) X hS (.inl rfl) hks (by omega) hks2
        (avoid_mono hav hk1 (Nat.le_succ _)) (fun e => hnn (by simp [e])) hF)
        (frag_exists hlowT (P := fun l1 u => Named l1 k1 k2 ∧
          RunF s0 (l1 ++ l) (Left A s0 bytes t X (free + i % 2) (free + 2) F) u) fun l1 => ?_)
      show Frag o _ (fun u => Named l1 k1 k2 ∧
        RunF s0 (l1 ++ l) (Left A s0 bytes t X (free + i % 2) (free + 2) F) u) _
      refine frag_pure (Named l1 k1 k2) (fun _ h => h.1) hlowT fun hn1 => ?_
      refine frag_conseq (P0 := RunF s0 (l1 ++ l) (Left A s0 bytes t X (free + i % 2) (free + 2) F))
        (P0' := fun u => ∃ l', Named l' k1 (k2 + 1) ∧
          RunF s0 (l' ++ l) (Left A s0 bytes (.seq (t :: t' :: ts')) X kd free F) u) ?_
        (fun _ h => h.2) fun _ ⟨l', hn, h⟩ => ⟨l', named_mono hn hk1 (Nat.le_refl _), h⟩
      have hrt : Fresh s!"e{k2}" (l1 ++ l) = true :=
        fresh_app (fresh_named hn1 (.inr (Nat.le_refl _)) (name_e k2)) (fresh_of hav (by omega) (Nat.lt_succ_self _)
          (name_e k2))
      let G1 := Left A s0 bytes t X (free + i % 2) (free + 2) F
      let Ss := setOf (Ends bytes t X)
      refine frag_append (xs := [_]) (void_frag o hA hcode (l := l1 ++ l) (F := G1) hrt (lower_n _) hEd' hdst hkd'
        (fun _ _ => rfl) (fun u h => hvd u fun q hq => h.1.vals q (List.mem_append_right _ hq)) (Ss := Ss)
        fun m ⟨_, _, hH, hB, _⟩ => ⟨hH, hB.1⟩) (frag_exists (lowKK_ite rfl lowKK_nil ihs.1) fun v => ?_)
      -- the branch
      let P' : Assn σ := fun u => ∃ l', Named l' k1 (k2 + 1) ∧
        RunF s0 (l' ++ l) (Left A s0 bytes (.seq (t :: t' :: ts')) X kd free F) u
      refine frag_ite o (c := Syntax.v s!"e{k2}") rfl (P' := P') clock_named (fun u h => ⟨v, vals_lookup h.1.vals
        (lookup_head _ _ _)⟩) (frag_nil o fun u ⟨h, h0⟩ => ?_) (noDecl _ rfl) (frag_conseq (ihd ((s!"e{k2}", v) ::
          (l1 ++ l)) (Left A s0 bytes t X (free + i % 2) (free + 2) F) (free + (i + 1 + 1) % 2) kd Ss
          (.inl (by simp)) (slotIs_mono hD fun q hq => List.mem_cons_of_mem _ (List.mem_append_right _ hq))
          (by omega) (by omega) hkd (by omega) (fun q hq j hj1 hj2 hg => ?_)
          (fun e => List.mem_cons_of_mem _ (List.mem_append_right _ (hnn (by simp [e])))) fun m hm => ?_)
          (fun u ⟨h, h0⟩ => ?_) fun u ⟨l3, hn3, h3⟩ => ?_) fun u y v' hu hy =>
          restore_named hav (by omega) v' (ihs.2.2 y hy) hu
      · -- the term reached nothing: neither does the sequence
        have hv : v ≠ 0 := fun e => h0 (by rw [← e]; exact vals_lookup h.1.vals (lookup_head _ _ _))
        refine ⟨(s!"e{k2}", v) :: l1, named_append (named_one (name_e k2) hk2 (Nat.lt_succ_self _))
          (named_mono hn1 (Nat.le_refl _) (Nat.le_succ _)), runF_mono h (fun _ hq => hq) ?_⟩
        rintro m'' ⟨m', ⟨m, hm, _, hB, hK⟩, hr⟩
        rcases hr with ⟨hnone, -, hS0, hfr⟩ | ⟨-, hv0, -⟩
        · refine ⟨m, hm, ?_, base_keep hA.hA hlen hkd' hB (kept_frame (free := 0) (.inl rfl) hfr)
            (allSets_frame hB.1 hkd' hS0 hfr), kept_trans (kept_wide (by omega) (.inr ⟨by omega, hdst⟩) hK)
            (kept_frame (.inl rfl) hfr)⟩
          have hT : ∀ e, (fun _ => false : Nat → Bool) e = true ↔ Ends bytes (.seq (t :: t' :: ts')) X e :=
            fun e => Iff.intro (fun h => absurd h Bool.false_ne_true) fun he =>
              let ⟨y, hy, _⟩ := (ends_seq_cons e).1 he; absurd ((hnone y).symm.trans hy) Bool.false_ne_true
          unfold Holds
          rw [← setOf_eq hT]
          exact hS0
        · exact absurd hv0 hv
      · rcases List.mem_cons.1 hq with rfl | hq
        · have := genName_inj hg (name_e k2); simp only at hj2; omega
        rcases List.mem_append.1 hq with hq | hq
        · obtain ⟨j', h1, -, h3⟩ := hn1 q hq
          have := genName_inj hg h3; simp only at hj2; omega
        · exact hav q hq j hj1 (by simp only at hj2; omega) hg
      · obtain ⟨_, _, hH, hB, _⟩ := hm
        have e : free + (i + 1 + 1) % 2 = free + i % 2 := by omega
        rw [e]; exact ⟨hH, hB⟩
      · have hv0 : v = 0 := Option.some.inj ((vals_lookup h.1.vals (lookup_head _ _ _)).symm.trans h0)
        refine runF_mono h (fun _ hq => hq) fun m'' ⟨m', hm', hr⟩ => ?_
        rcases hr with ⟨-, hv1, -⟩ | ⟨-, -, hmm⟩
        · rw [hv0] at hv1; exact absurd hv1 (by decide)
        · exact hmm ▸ hm'
      · refine ⟨(s!"e{k2}", v) :: l1, named_append (named_one (name_e k2) hk2 (Nat.lt_succ_self _))
          (named_mono hn1 (Nat.le_refl _) (Nat.le_succ _)), runF_mono h3 (fun _ hq => List.mem_append_right _ hq) ?_⟩
        rintro m3 ⟨m2, ⟨m, hm, -, -, hK1⟩, hH, hB, hK⟩
        exact ⟨m, hm, holds_congr hH fun e => (ends_seq_cons e).symm, hB,
          kept_trans (kept_wide (by omega) (.inr ⟨by omega, hdst⟩) hK1) hK⟩

/-! ## A choice -/

/-- What the alternatives `us` take of `gen`, with the slots from `free + 1` on for theirs. -/
def AltPre (f free : Nat) (us : List Abnf.Term) (code : String → Option (List String × PancakeProg)) : Prop :=
  ∀ u ∈ us, AbnfOrder.enough f u = true ∧
    (∀ j ∈ callsOf f u, BodyOk o ofs code j ∧ free + 1 + needOf f u ≤ frameOf j) ∧
    (∀ lf ∈ leavesOf f u, lf ∈ allLeaves) ∧ free + 1 + needOf f u ≤ slots

/-- **The alternatives after the first**, each into slot `free` and added to slot `d`. -/
theorem altRest_ok (hA : Area ofs A s0) (hcode : ProgCode s0.code ofs) (hlen : bytes.length ≤ inputMax)
    {f : Nat} {g : Gen} (hg : GenOk o ofs A s0 bytes f g) {s d : Syntax.PExpr} (hs : SlotE s)
    (hd : SlotE d) {free : Nat} (hfree : free + 1 ≤ slots) :
    ∀ (us : List Abnf.Term) (k : Nat), AltPre o (ofs := ofs) f free us s0.code →
    Shape k (altRest g s d free us k) ∧
    ∀ (l : List (String × Value)) (F : (Word → Word) → Prop) (ks kd : Nat) (S D : Nat → Bool),
      SlotIs l s ks → SlotIs l d kd → ks < free → kd < free → ks ≠ kd →
      Avoid l k (altRest g s d free us k).2 →
      (us.any (repeats f) = true → ("nn", BitVec.ofNat 64 bytes.length) ∈ l) →
      (∀ m, F m → SetAt m A ks S ∧ SetAt m A kd D ∧ Base s0 A bytes m) →
      Frag o (altRest g s d free us k).1 (RunF s0 l F)
        (fun u => ∃ l', Named l' k (altRest g s d free us k).2 ∧ RunF s0 (l' ++ l) (fun m' => ∃ m, F m ∧
          Holds A m' kd (fun e => D e = true ∨ ∃ u ∈ us, Ends bytes u S e) ∧ Base s0 A bytes m' ∧
            Kept A kd free m m') u) := by
  intro us
  induction us with
  | nil =>
    intro k _
    refine ⟨⟨lowKK_nil, Nat.le_refl _, fun _ h => nomatch h⟩, ?_⟩
    intro l F ks kd S D _ _ _ _ _ _ _ hF
    refine frag_nil o fun w h => ⟨[], ⟨(fun _ hq => nomatch hq), ?_⟩⟩
    refine runF_mono h (fun _ hq => hq) fun m hm => ⟨m, hm, ?_, (hF m hm).2.2, kept_refl m⟩
    unfold Holds
    rw [← setOf_eq fun e => ⟨fun h => .inl h, fun h => h.elim id fun ⟨_, hu, _⟩ => nomatch hu⟩]
    exact (hF m hm).2.1
  | cons t0 us ih =>
    intro k hpre
    obtain ⟨hen, hca, hle, hsl⟩ := hpre t0 (List.mem_cons_self ..)
    obtain ⟨hsh, hdo⟩ := hg t0 s (Syntax.n free) (free + 1) k hen hca hle hsl hs (.inl ⟨_, rfl⟩)
    generalize hb : g t0 s (Syntax.n free) (free + 1) k = B at hsh hdo
    obtain ⟨b, k1⟩ := B
    obtain ⟨ihs, ihd⟩ := ih (k1 + 1) fun x hx => hpre x (List.mem_cons_of_mem _ hx)
    generalize hR : altRest g s d free us (k1 + 1) = Rr at ihs ihd
    obtain ⟨R, k2⟩ := Rr
    have e : altRest g s d free (t0 :: us) k = (b ++ [.call s!"c{k1}" "setUnion" [d, Syntax.n free]] ++ R, k2) := by
      rw [altRest]; simp only [hb, hR]
    rw [e]
    obtain ⟨Ed, hEd⟩ := slotE_lower hd
    have hk1 := hsh.2.1
    have hk2 := ihs.2.1
    have hlowT : LowKK ([.call s!"c{k1}" "setUnion" [d, Syntax.n free]] ++ R) :=
      lowKK_append (lowKK_call (lowerArgs_two hEd (lower_n _))) ihs.1
    refine ⟨⟨by rw [List.append_assoc]; exact lowKK_append hsh.1 hlowT, by omega, fun y hy => ?_⟩, ?_⟩
    · rw [declared_append, declared_append] at hy
      rcases List.mem_append.1 hy with hy | hy
      · rcases List.mem_append.1 hy with hy | hy
        · obtain ⟨j, h1, h2, h3⟩ := hsh.2.2 y hy
          exact ⟨j, h1, by omega, h3⟩
        · simp only [declared, List.mem_cons, List.not_mem_nil, or_false] at hy
          subst hy; exact ⟨k1, hk1, by omega, name_c k1⟩
      · obtain ⟨j, h1, h2, h3⟩ := ihs.2.2 y hy
        exact ⟨j, by omega, h2, h3⟩
    intro l F ks kd S D hS hD hks hkd hne hav hnn hF
    have hkd' : kd < slots := by omega
    have hfs : free < slots := by omega
    obtain ⟨Ed', hEd', hvd⟩ := slotIs_eval (σ := σ) hD
    rw [List.append_assoc]
    refine frag_append (hdo l F ks free S hS (.inl rfl) (by omega) (by omega) (by omega)
      (avoid_mono hav (Nat.le_refl _) (by omega)) (fun e => hnn (by simp [e]))
      fun m hm => ⟨(hF m hm).1, (hF m hm).2.2⟩)
      (frag_exists hlowT (P := fun l1 u => Named l1 k k1 ∧
        RunF s0 (l1 ++ l) (Left A s0 bytes t0 S free (free + 1) F) u) fun l1 => ?_)
    show Frag o _ (fun w => Named l1 k k1 ∧ RunF s0 (l1 ++ l) (Left A s0 bytes t0 S free (free + 1) F) w) _
    refine frag_pure (Named l1 k k1) (fun _ h => h.1) hlowT fun hn1 => ?_
    refine frag_conseq (P0 := RunF s0 (l1 ++ l) (Left A s0 bytes t0 S free (free + 1) F)) ?_ (fun _ h => h.2)
      fun _ h => h
    have hrt : Fresh s!"c{k1}" (l1 ++ l) = true :=
      fresh_app (fresh_named hn1 (.inr (Nat.le_refl _)) (name_c k1)) (fresh_of hav hk1 (by omega) (name_c k1))
    refine frag_append (union_frag o hA hcode hrt hEd' (lower_n _) hkd' hfs
      (fun w h => hvd w fun q hq => h.1.vals q (List.mem_append_right _ hq)) (fun _ _ => rfl)
      (Sd := D) (Ss := setOf (Ends bytes t0 S)) fun m ⟨m0, hm0, hH, _, hK⟩ =>
        ⟨setAt_kept (hF m0 hm0).2.1 (by omega) hkd' hfs (by omega) hK, hH⟩)
      (frag_exists ihs.1 fun v => ?_)
    have hrt2 : Avoid ((s!"c{k1}", v) :: (l1 ++ l)) (k1 + 1) k2 := fun q hq j hj1 hj2 hg => by
      rcases List.mem_cons.1 hq with rfl | hq
      · have := genName_inj hg (name_c k1); omega
      rcases List.mem_append.1 hq with hq | hq
      · obtain ⟨j', -, h2, h3⟩ := hn1 q hq; have := genName_inj hg h3; omega
      · exact hav q hq j (by omega) hj2 hg
    refine frag_conseq (ihd ((s!"c{k1}", v) :: (l1 ++ l)) _ ks kd S (fun x => D x || setOf (Ends bytes t0 S) x)
      (slotIs_mono hS fun q hq => List.mem_cons_of_mem _ (List.mem_append_right _ hq))
      (slotIs_mono hD fun q hq => List.mem_cons_of_mem _ (List.mem_append_right _ hq)) hks hkd hne hrt2
      (fun e => List.mem_cons_of_mem _ (List.mem_append_right _ (hnn (by simp [e])))) fun m'' hm'' => ?_)
      (fun _ h => h) fun w ⟨l3, hn3, h3⟩ => ⟨l3 ++ (s!"c{k1}", v) :: l1, ?_, ?_⟩
    · obtain ⟨m', ⟨m0, hm0, _, hB, hK⟩, -, hU, hfr⟩ := hm''
      exact ⟨setAt_other (setAt_kept (hF m0 hm0).1 (by omega) (by omega) hfs (by omega) hK) hkd' (by omega)
        (fun e => hne e.symm) hfr, hU, base_keep hA.hA hlen hkd' hB (kept_frame (free := 0) (.inl rfl) hfr)
          (allSets_frame hB.1 hkd' hU hfr)⟩
    · intro q hq
      rcases List.mem_append.1 hq with hq | hq
      · obtain ⟨j, h1, h2, h3⟩ := hn3 q hq; exact ⟨j, by omega, h2, h3⟩
      rcases List.mem_cons.1 hq with rfl | hq
      · exact ⟨k1, hk1, by omega, name_c k1⟩
      · obtain ⟨j, h1, h2, h3⟩ := hn1 q hq; exact ⟨j, h1, by omega, h3⟩
    · refine runF_mono h3 (fun q hq => by rwa [List.append_assoc, List.cons_append] at hq) ?_
      rintro m3 ⟨m2, ⟨m', ⟨m0, hm0, -, -, hK⟩, -, -, hfr⟩, hH, hB, hK3⟩
      refine ⟨m0, hm0, holds_congr hH fun e => ?_, hB, kept_trans (kept_trans (kept_wide (by omega)
        (.inr ⟨Nat.le_refl _, hfs⟩) hK) (kept_frame (.inl rfl) hfr)) hK3⟩
      simp only [Bool.or_eq_true, setOf_iff, List.mem_cons, exists_eq_or_imp]
      constructor
      · rintro ((h | h) | h)
        · exact .inl h
        · exact .inr (.inl h)
        · exact .inr (.inr h)
      · rintro (h | h | h)
        · exact .inl (.inl h)
        · exact .inl (.inr h)
        · exact .inr h

/-- **A choice of two terms or more**: the first into slot `d`, the others added. -/
theorem altCons_ok (hA : Area ofs A s0) (hcode : ProgCode s0.code ofs) (hlen : bytes.length ≤ inputMax)
    {f : Nat} {g : Gen} (hg : GenOk o ofs A s0 bytes f g) {s d : Syntax.PExpr} (hs : SlotE s)
    (hd : SlotE d) {free : Nat} (hfree : free + 1 ≤ slots) {u v : Abnf.Term} {vs : List Abnf.Term}
    (hpre : AltPre o (ofs := ofs) f free (u :: v :: vs) s0.code) (k : Nat) :
    Shape k (genAlt .none g s d free (u :: v :: vs) k) ∧
      Does o A s0 bytes ((u :: v :: vs).any (repeats f)) (.alt (u :: v :: vs)) s d free k
        (genAlt .none g s d free (u :: v :: vs) k) := by
  obtain ⟨hen, hca, hle, hsl⟩ := hpre u (List.mem_cons_self ..)
  obtain ⟨hsh, hdo⟩ := hg u s d (free + 1) k hen hca hle hsl hs hd
  generalize hb : g u s d (free + 1) k = B at hsh hdo
  obtain ⟨b, k1⟩ := B
  obtain ⟨ihs, ihd⟩ := altRest_ok o hA hcode hlen hg hs hd hfree (v :: vs) k1
    fun x hx => hpre x (List.mem_cons_of_mem _ hx)
  generalize hR : altRest g s d free (v :: vs) k1 = Rr at ihs ihd
  obtain ⟨R, k2⟩ := Rr
  have e : genAlt .none g s d free (u :: v :: vs) k = (b ++ R, k2) := by
    rw [genAlt]; simp only [hb]; rw [if_neg (by decide), hR]
  rw [e]
  have hk1 := hsh.2.1
  have hk2 := ihs.2.1
  refine ⟨⟨lowKK_append hsh.1 ihs.1, by omega, fun y hy => ?_⟩, ?_⟩
  · rw [declared_append] at hy
    rcases List.mem_append.1 hy with hy | hy
    · obtain ⟨j, h1, h2, h3⟩ := hsh.2.2 y hy; exact ⟨j, h1, by omega, h3⟩
    · obtain ⟨j, h1, h2, h3⟩ := ihs.2.2 y hy; exact ⟨j, by omega, h2, h3⟩
  intro l F ks kd S hS hD hks hkd hne hav hnn hF
  have hkd' : kd < slots := by omega
  refine frag_append (hdo l F ks kd S hS hD (by omega) (by omega) hne (avoid_mono hav (Nat.le_refl _) (by omega))
    (fun e => hnn (by simp [e])) hF) (frag_exists ihs.1 (P := fun l1 w => Named l1 k k1 ∧
      RunF s0 (l1 ++ l) (Left A s0 bytes u S kd (free + 1) F) w) fun l1 => ?_)
  show Frag o _ (fun w => Named l1 k k1 ∧ RunF s0 (l1 ++ l) (Left A s0 bytes u S kd (free + 1) F) w) _
  refine frag_pure (Named l1 k k1) (fun _ h => h.1) ihs.1 fun hn1 => ?_
  have hav2 : Avoid (l1 ++ l) k1 k2 := avoid_append (avoid_mono hav hk1 (Nat.le_refl _)) hn1 (.inl (Nat.le_refl _))
  refine frag_conseq (ihd (l1 ++ l) (Left A s0 bytes u S kd (free + 1) F) ks kd S (setOf (Ends bytes u S))
    (slotIs_mono hS fun q hq => List.mem_append_right _ hq) (slotIs_mono hD fun q hq => List.mem_append_right _ hq)
    hks hkd hne hav2 (fun e => List.mem_append_right _ (hnn (by simp [e]))) fun m ⟨m0, hm0, hH, hB, hK⟩ =>
      ⟨setAt_kept (hF m0 hm0).1 (by omega) (by omega) hkd' hne (kept_wide (by omega) (.inl rfl) hK), hH, hB⟩)
    (fun _ h => h.2) fun w ⟨l3, hn3, h3⟩ => ⟨l3 ++ l1, named_append (named_mono hn3 hk1 (Nat.le_refl _))
      (named_mono hn1 (Nat.le_refl _) hk2), runF_mono h3 (fun q hq => by rwa [List.append_assoc] at hq) ?_⟩
  rintro m3 ⟨m2, ⟨m0, hm0, -, -, hK⟩, hH, hB, hK3⟩
  refine ⟨m0, hm0, holds_congr hH fun e => ?_, hB, kept_trans (kept_wide (by omega) (.inl rfl) hK) hK3⟩
  simp only [setOf_iff, Ends, AbnfMatch.alt_iff]
  constructor
  · rintro (⟨x, hx, hm⟩ | ⟨t, ht, x, hx, hm⟩)
    · exact ⟨x, hx, u, List.mem_cons_self .., hm⟩
    · exact ⟨x, hx, t, List.mem_cons_of_mem _ ht, hm⟩
  · rintro ⟨x, hx, t, ht, hm⟩
    rcases List.mem_cons.1 ht with rfl | ht
    · exact .inl ⟨x, hx, hm⟩
    · exact .inr ⟨t, ht, x, hx, hm⟩

/-- **An optional term**: its matches, the positions themselves added. -/
theorem opt_ok (hA : Area ofs A s0) (hcode : ProgCode s0.code ofs) (hlen : bytes.length ≤ inputMax)
    {f : Nat} {g : Gen} (hg : GenOk o ofs A s0 bytes f g) {s d : Syntax.PExpr} (hs : SlotE s)
    (hd : SlotE d) {free : Nat} {u : Abnf.Term} (hen : AbnfOrder.enough f u = true)
    (hca : ∀ j ∈ callsOf f u, BodyOk o ofs s0.code j ∧ free + needOf f u ≤ frameOf j)
    (hle : ∀ lf ∈ leavesOf f u, lf ∈ allLeaves) (hsl : free + needOf f u ≤ slots) (k : Nat) :
    Shape k ((g u s d free k).1 ++ [.call s!"c{(g u s d free k).2}" "setUnion" [d, s]], (g u s d free k).2 + 1) ∧
      Does o A s0 bytes (repeats f u) (.rep 0 (some 1) u) s d free k
        ((g u s d free k).1 ++ [.call s!"c{(g u s d free k).2}" "setUnion" [d, s]], (g u s d free k).2 + 1) := by
  obtain ⟨hsh, hdo⟩ := hg u s d free k hen hca hle hsl hs hd
  generalize hb : g u s d free k = B at hsh hdo
  obtain ⟨b, k1⟩ := B
  obtain ⟨Es, hEs⟩ := slotE_lower hs
  obtain ⟨Ed, hEd⟩ := slotE_lower hd
  have hk1 := hsh.2.1
  have hlowT : LowKK [.call s!"c{k1}" "setUnion" [d, s]] := lowKK_call (lowerArgs_two hEd hEs)
  refine ⟨⟨lowKK_append hsh.1 hlowT, by simp only; omega, fun y hy => ?_⟩, ?_⟩
  · rw [declared_append] at hy
    rcases List.mem_append.1 hy with hy | hy
    · obtain ⟨j, h1, h2, h3⟩ := hsh.2.2 y hy; exact ⟨j, h1, by simp only; omega, h3⟩
    · simp only [declared, List.mem_cons, List.not_mem_nil, or_false] at hy
      subst hy; exact ⟨k1, hk1, Nat.lt_succ_self _, name_c k1⟩
  intro l F ks kd S hS hD hks hkd hne hav hnn hF
  have hkd' : kd < slots := by omega
  have hks' : ks < slots := by omega
  obtain ⟨Es', hEs', hvs⟩ := slotIs_eval (σ := σ) hS
  obtain ⟨Ed', hEd', hvd⟩ := slotIs_eval (σ := σ) hD
  refine frag_append (hdo l F ks kd S hS hD hks hkd hne (avoid_mono hav (Nat.le_refl _) (Nat.le_succ _)) hnn hF)
    (frag_exists hlowT (P := fun l1 w => Named l1 k k1 ∧
      RunF s0 (l1 ++ l) (Left A s0 bytes u S kd free F) w) fun l1 => ?_)
  show Frag o _ (fun w => Named l1 k k1 ∧ RunF s0 (l1 ++ l) (Left A s0 bytes u S kd free F) w) _
  refine frag_pure (Named l1 k k1) (fun _ h => h.1) hlowT fun hn1 => ?_
  have hrt : Fresh s!"c{k1}" (l1 ++ l) = true :=
    fresh_app (fresh_named hn1 (.inr (Nat.le_refl _)) (name_c k1)) (fresh_of hav hk1 (Nat.lt_succ_self _) (name_c k1))
  refine frag_conseq (union_frag o hA hcode hrt hEd' hEs' hkd' hks'
    (fun w h => hvd w fun q hq => h.1.vals q (List.mem_append_right _ hq))
    (fun w h => hvs w fun q hq => h.1.vals q (List.mem_append_right _ hq)) (Sd := setOf (Ends bytes u S)) (Ss := S)
    fun m ⟨m0, hm0, hH, _, hK⟩ => ⟨hH, setAt_kept (hF m0 hm0).1 hks hks' hkd' hne hK⟩) (fun _ h => h.2)
    fun w ⟨v, h⟩ => ⟨(s!"c{k1}", v) :: l1, named_append (named_one (name_c k1) hk1 (Nat.lt_succ_self _))
      (named_mono hn1 (Nat.le_refl _) (Nat.le_succ _)), runF_mono h (fun _ hq => hq) ?_⟩
  rintro m'' ⟨m', ⟨m0, hm0, -, hB, hK⟩, -, hU, hfr⟩
  refine ⟨m0, hm0, ?_, base_keep hA.hA hlen hkd' hB (kept_frame (free := 0) (.inl rfl) hfr)
    (allSets_frame hB.1 hkd' hU hfr), kept_trans hK (kept_frame (.inl rfl) hfr)⟩
  unfold Holds
  rw [← setOf_eq (T := fun x => setOf (Ends bytes u S) x || S x) fun e => ?_]
  · exact hU
  simp only [Bool.or_eq_true, setOf_iff, Ends, AbnfMatch.opt_iff]
  constructor
  · rintro (⟨x, hx, hm⟩ | h)
    · exact ⟨x, hx, .inr hm⟩
    · exact ⟨e, h, .inl rfl⟩
  · rintro ⟨x, hx, rfl | hm⟩
    · exact .inr hx
    · exact .inl ⟨x, hx, hm⟩

/-! ## A repetition's rounds -/

section bfs
variable (input : Array Nat) (u : Abnf.Term) (lo : Nat) (hi : Option Nat) (S : Nat → Bool)

/-- Where `j` matches of `u` in a row end from the positions of `S`. -/
def Reach (j e : Nat) : Prop := ∃ x, S x = true ∧ AbnfMatch.Rep AbnfRules.grammar input u j x e

/-- Where `lo` to `c` matches end: what the rounds up to `c` count. -/
def Done (c e : Nat) : Prop := ∃ j, lo ≤ j ∧ j ≤ c ∧ Reach input u S j e

/-- Where `c` matches end and no fewer from `lo` on: round `c`'s frontier. -/
def Front (c e : Nat) : Prop := Reach input u S c e ∧ ¬∃ j, lo ≤ j ∧ j < c ∧ Reach input u S j e

/-- Where the repetition's matches end. -/
def Target (e : Nat) : Prop := ∃ j, lo ≤ j ∧ (∀ h ∈ hi, j ≤ h) ∧ Reach input u S j e

/-- How many positions below `n` the set holds. -/
def cnt (D : Nat → Bool) : Nat → Nat
  | 0 => 0
  | n + 1 => cnt D n + if D n then 1 else 0

end bfs

section bfs2
variable {input : Array Nat} {u : Abnf.Term} {lo : Nat} {hi : Option Nat} {S : Nat → Bool}

theorem reach_succ {c e : Nat} :
    Reach input u S (c + 1) e ↔ ∃ y, Reach input u S c y ∧ Matches AbnfRules.grammar input u y e := by
  unfold Reach
  constructor
  · rintro ⟨x, hx, h⟩
    obtain ⟨y, h1, h2⟩ := AbnfEnds.rep_snoc.1 h
    exact ⟨y, ⟨x, hx, h1⟩, h2⟩
  · rintro ⟨y, ⟨x, hx, h1⟩, h2⟩
    exact ⟨x, hx, AbnfEnds.rep_snoc.2 ⟨y, h1, h2⟩⟩

theorem done_lt {c e : Nat} (hc : c < lo) : ¬Done input u lo S c e := fun ⟨_, h1, h2, _⟩ => by omega

theorem front_lt {c e : Nat} (hc : c < lo) : Front input u lo S c e ↔ Reach input u S c e :=
  ⟨fun h => h.1, fun h => ⟨h, fun ⟨_, h1, h2, _⟩ => by omega⟩⟩

theorem done_succ {c e : Nat} (hc : lo ≤ c + 1) :
    Done input u lo S (c + 1) e ↔ Done input u lo S c e ∨ Reach input u S (c + 1) e :=
  ⟨fun ⟨j, h1, h2, h⟩ => (Nat.lt_or_ge j (c + 1)).elim (fun hj => .inl ⟨j, h1, by omega, h⟩)
    fun hj => .inr (by rw [show j = c + 1 by omega] at h; exact h),
   fun h => h.elim (fun ⟨j, h1, h2, h⟩ => ⟨j, h1, by omega, h⟩) fun h => ⟨c + 1, hc, Nat.le_refl _, h⟩⟩

theorem front_succ {c e : Nat} :
    Front input u lo S (c + 1) e ↔ Reach input u S (c + 1) e ∧ ¬Done input u lo S c e :=
  ⟨fun ⟨h, hn⟩ => ⟨h, fun ⟨j, h1, h2, hj⟩ => hn ⟨j, h1, by omega, hj⟩⟩,
   fun ⟨h, hn⟩ => ⟨h, fun ⟨j, h1, h2, hj⟩ => hn ⟨j, h1, by omega, hj⟩⟩⟩

/-- What a round reaches from round `c`'s frontier, all `c + 1` matches reach but what is counted. -/
theorem next_cover {c e : Nat} (h : Reach input u S (c + 1) e) :
    Done input u lo S c e ∨ ∃ y, Front input u lo S c y ∧ Matches AbnfRules.grammar input u y e := by
  obtain ⟨y, hy, hm⟩ := reach_succ.1 h
  by_cases hf : Front input u lo S c y
  · exact .inr ⟨y, hf, hm⟩
  · have : ∃ j, lo ≤ j ∧ j < c ∧ Reach input u S j y := Classical.byContradiction fun hn => hf ⟨hy, hn⟩
    obtain ⟨j, h1, h2, hj⟩ := this
    exact .inl ⟨j + 1, by omega, by omega, reach_succ.2 ⟨y, hj, hm⟩⟩

theorem next_sub {c e : Nat} (h : ∃ y, Front input u lo S c y ∧ Matches AbnfRules.grammar input u y e) :
    Reach input u S (c + 1) e :=
  let ⟨y, hy, hm⟩ := h; reach_succ.2 ⟨y, hy.1, hm⟩

/-- **The rounds counted are all there are** once a round adds nothing they hold, up to the bound. -/
theorem complete {c : Nat} (hc : lo ≤ c) (hhi : ∀ h ∈ hi, c ≤ h)
    (hclose : ∀ y e, Front input u lo S c y → Matches AbnfRules.grammar input u y e → Done input u lo S c e)
    (e : Nat) :
    Done input u lo S c e ↔ Target input u lo hi S e := by
  constructor
  · rintro ⟨j, h1, h2, h⟩
    exact ⟨j, h1, fun h hh => Nat.le_trans h2 (hhi h hh), h⟩
  · rintro ⟨j, h1, -, h⟩
    suffices ∀ j e, lo ≤ j → Reach input u S j e → Done input u lo S c e from this j e h1 h
    intro j
    induction j with
    | zero => intro e h1 h; exact ⟨0, h1, Nat.zero_le _, h⟩
    | succ j ih =>
      intro e h1 h
      by_cases hj : j + 1 ≤ c
      · exact ⟨j + 1, h1, hj, h⟩
      · obtain ⟨y, hy, hm⟩ := reach_succ.1 h
        have hdy := ih y (by omega) hy
        by_cases hf : Front input u lo S c y
        · exact hclose y e hf hm
        · obtain ⟨j', h1', h2', hj'⟩ := hdy
          have : ∃ j₀, lo ≤ j₀ ∧ j₀ < c ∧ Reach input u S j₀ y := by
            by_cases hjc : j' < c
            · exact ⟨j', h1', hjc, hj'⟩
            · exact Classical.byContradiction fun hn => hf ⟨by rw [show c = j' by omega]; exact hj', hn⟩
          obtain ⟨j₀, a1, a2, a3⟩ := this
          exact ⟨j₀ + 1, by omega, by omega, reach_succ.2 ⟨y, a3, hm⟩⟩

end bfs2

/-! ### Counting the positions up to the input's end -/

theorem cnt_le (D : Nat → Bool) : ∀ n, cnt D n ≤ n
  | 0 => Nat.le_refl _
  | n + 1 => by have := cnt_le D n; simp only [cnt]; split <;> omega

theorem cnt_mono {D D' : Nat → Bool} (h : ∀ y, D y = true → D' y = true) : ∀ n, cnt D n ≤ cnt D' n
  | 0 => Nat.le_refl _
  | n + 1 => by
    have := cnt_mono h n
    simp only [cnt]
    by_cases e : D n = true
    · rw [if_pos e, if_pos (h n e)]; omega
    · rw [if_neg e]; split <;> omega

theorem cnt_lt {D D' : Nat → Bool} (h : ∀ y, D y = true → D' y = true) {x : Nat} (hx : D' x = true)
    (hn : D x ≠ true) : ∀ n, x < n → cnt D n < cnt D' n
  | 0, h0 => absurd h0 (Nat.not_lt_zero _)
  | n + 1, h1 => by
    simp only [cnt]
    by_cases e : x = n
    · subst e; rw [if_neg hn, if_pos hx]; have := cnt_mono h x; omega
    · have := cnt_lt h hx hn n (by omega)
      by_cases e2 : D n = true
      · rw [if_pos e2, if_pos (h n e2)]; omega
      · rw [if_neg e2]; split <;> omega

section count
variable {input : Array Nat} {u : Abnf.Term} {lo : Nat} {S : Nat → Bool}

/-- Past the input's end a match matches nothing. -/
theorem fixed {y e : Nat} (hy : input.size ≤ y) (h : Matches AbnfRules.grammar input u y e) : e = y := by
  have h1 := AbnfMatch.Matches.le h
  have h2 := AbnfEnds.Matches.bound h
  omega

/-- From round `lo` on, a frontier with a position up to the input's end comes after as many rounds as the counted
positions up to there. -/
def Cnt (input : Array Nat) (u : Abnf.Term) (lo : Nat) (S : Nat → Bool) (c : Nat) : Prop :=
  (∃ x, x ≤ input.size ∧ Front input u lo S c x) →
    c - lo + 1 ≤ cnt (setOf (Done input u lo S c)) (input.size + 1)

theorem cnt_zero (n : Nat) : cnt (fun _ => false) n = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [cnt, ih]

theorem cnt_lo : Cnt input u lo S lo := fun ⟨x, hx, hf⟩ => by
  have := cnt_lt (D := fun _ => false) (D' := setOf (Done input u lo S lo)) (fun _ h => nomatch h)
    (setOf_iff.2 ⟨lo, Nat.le_refl _, Nat.le_refl _, hf.1⟩) (by simp) (input.size + 1) (by omega)
  rw [cnt_zero] at this; omega

theorem cnt_step {c : Nat} (hc : lo ≤ c) (h : Cnt input u lo S c) : Cnt input u lo S (c + 1) :=
    fun ⟨x, hx, hf⟩ => by
  obtain ⟨hr, hnd⟩ := front_succ.1 hf
  obtain ⟨y, hy, hm⟩ := reach_succ.1 hr
  have hyn : y ≤ input.size := Classical.byContradiction fun hn => by
    have := fixed (by omega) hm
    subst this; exact hnd ⟨c, hc, Nat.le_refl _, hy⟩
  have hfy : Front input u lo S c y := ⟨hy, fun ⟨j, h1, h2, hj⟩ =>
    hnd ⟨j + 1, by omega, by omega, reach_succ.2 ⟨y, hj, hm⟩⟩⟩
  have h1 := h ⟨y, hyn, hfy⟩
  have h2 := cnt_lt (D := setOf (Done input u lo S c)) (D' := setOf (Done input u lo S (c + 1)))
    (fun z hz => setOf_iff.2 (let ⟨j, a, b, d⟩ := setOf_iff.1 hz; ⟨j, a, by omega, d⟩))
    (setOf_iff.2 ⟨c + 1, by omega, Nat.le_refl _, hr⟩) (fun e => hnd (setOf_iff.1 e)) (input.size + 1) (by omega)
  omega

/-- **After `lo` rounds and one more than the input has positions, the frontier adds nothing.** -/
theorem cnt_full {c : Nat} (hc : lo + input.size + 1 ≤ c) (h : Cnt input u lo S c) :
    ∀ y e, Front input u lo S c y → Matches AbnfRules.grammar input u y e → Done input u lo S c e := by
  intro y e hf hm
  by_cases hy : y ≤ input.size
  · have h1 := h ⟨y, hy, hf⟩
    have h2 := cnt_le (setOf (Done input u lo S c)) (input.size + 1)
    omega
  · rw [fixed (by omega) hm]
    exact ⟨c, by omega, Nat.le_refl _, hf.1⟩

end count

/-! ## A repetition's locals -/

theorem ne_heads {x y : String} {p q : Char} {r r' : List Char} (hx : x.toList = p :: r) (hy : y.toList = q :: r')
    (h : p ≠ q) : x ≠ y := fun e => h (by rw [e] at hx; rw [hx] at hy; exact (List.cons.inj hy).1)

/-- A name fresh in `L`, its letter starting no name of `pre`: fresh in `pre ++ L`. -/
theorem fresh_heads {y : String} {c : Char} {r : List Char} (hy : y.toList = c :: r) {L : List (String × Value)}
    (hL : Fresh y L = true) : ∀ (pre : List (String × Value)),
      (pre.all fun q => q.1.toList.head? != some c) = true → Fresh y (pre ++ L) = true
  | [], _ => hL
  | (x, _) :: pre, h => by
    simp only [List.all_cons, Bool.and_eq_true] at h
    exact fresh_cons (fun e => by subst e; rw [hy] at h; simp at h) (fresh_heads hy hL pre h.2)

/-- The repetition's counters and slots, its round `c`, before `base`. -/
def RL (k i go c nx fr : Nat) (base : List (String × Value)) : List (String × Value) :=
  (s!"i{k}", BitVec.ofNat 64 i) :: (s!"g{k}", BitVec.ofNat 64 go) :: (s!"n{k}", BitVec.ofNat 64 c) ::
    (s!"x{k}", BitVec.ofNat 64 nx) :: (s!"f{k}", BitVec.ofNat 64 fr) :: base

theorem lookup_mid {x : String} {w : Value} : ∀ {pre : List (String × Value)} (post : List (String × Value)),
    Fresh x pre = true → (pre ++ (x, w) :: post).lookup x = some w
  | [], _, _ => lookup_head _ _ _
  | q :: pre, post, h => by
    simp only [Fresh, List.all_cons, Bool.and_eq_true, bne_iff_ne, ne_eq] at h
    rw [List.cons_append, ScanRun.lookup_cons_ne (Ne.symm h.1)]
    exact lookup_mid post h.2

/-- **A local set** between others. -/
theorem runF_swap (o : Oracle σ) {G : (Word → Word) → Prop} {pre post : List (String × Value)} {x : String}
    (hpre : Fresh x pre = true) (hpost : Fresh x post = true) {e : Syntax.PExpr} {E : PancakeExp}
    (he : Lower.lowerExp e = some E) {w v : Value}
    (hv : ∀ u, RunF s0 (pre ++ (x, w) :: post) G u → eval u E = some v) :
    Frag o [.assign x e] (RunF s0 (pre ++ (x, w) :: post) G) (RunF s0 (pre ++ (x, v) :: post) G) :=
  AbnfComment.runF_set' o he (lookup_mid post hpre) hv fun q hq => by
    rcases List.mem_append.1 hq with hq | hq
    · exact .inr ⟨List.mem_append_left _ hq, ScanRun.fresh_ne hpre _ hq⟩
    rcases List.mem_cons.1 hq with rfl | hq
    · exact .inl rfl
    · exact .inr ⟨List.mem_append_right _ (List.mem_cons_of_mem _ hq), ScanRun.fresh_ne hpost _ hq⟩

/-! ## A repetition's loop -/

/-- The loop's memory after `c` rounds: while it goes on, slot `kd` the ends counted and slot `fr` the frontier; once
it stops, slot `kd` the repetition's ends. Every slot a set, every word as in one of `F`'s memories but slot `kd`'s
and those from `free` on. -/
def RepMem (A : Word) (s0 : PancakeState σ) (bytes : List (BitVec 8)) (u : Abnf.Term) (lo : Nat) (hi : Option Nat)
    (S : Nat → Bool) (kd free : Nat) (F : (Word → Word) → Prop) (go c fr : Nat) (m : Word → Word) : Prop :=
  ∃ m0, F m0 ∧ Base s0 A bytes m ∧ Kept A kd free m0 m ∧
    (go = 1 → Holds A m kd (Done (inputOf bytes) u lo S c) ∧ Holds A m fr (Front (inputOf bytes) u lo S c) ∧
      (lo ≤ c → Cnt (inputOf bytes) u lo S c)) ∧
    (go = 0 → Holds A m kd (Target (inputOf bytes) u lo hi S))

/-- The loop's counters: `go` a flag, `i` its turns within the bound, and while it goes on, `c` its rounds within
`hi`, `nx` one of its two slots and `fr` another below them. -/
def RepCnt (nn lo : Nat) (hi : Option Nat) (free i go c nx fr : Nat) : Prop :=
  (go = 0 ∨ go = 1) ∧ i ≤ nn + lo + 1 ∧
    (go = 1 → c = i ∧ (∀ h ∈ hi, c ≤ h) ∧ (nx = free ∨ nx = free + 1) ∧ fr < free + 2 ∧ fr ≠ nx)

/-- The loop's invariant. -/
def RepI (A : Word) (s0 : PancakeState σ) (bytes : List (BitVec 8)) (u : Abnf.Term) (lo : Nat) (hi : Option Nat)
    (S : Nat → Bool) (kd free k : Nat) (F : (Word → Word) → Prop) (base : List (String × Value)) : Assn σ :=
  fun w => ∃ i go c nx fr, RunF s0 (RL k i go c nx fr base) (RepMem A s0 bytes u lo hi S kd free F go c fr) w ∧
    RepCnt bytes.length lo hi free i go c nx fr

theorem repI_clock {A : Word} {bytes : List (BitVec 8)} {u : Abnf.Term} {lo : Nat} {hi : Option Nat}
    {S : Nat → Bool} {kd free k : Nat} {F : (Word → Word) → Prop} {base : List (String × Value)} :
    Safe.ClockFree (RepI A s0 bytes u lo hi S kd free k F base) :=
  fun w c ⟨i, go, cn, nx, fr, h, hc⟩ => ⟨i, go, cn, nx, fr, runF_clock _ _ _ w c h, hc⟩

/-- A name the loop's counters' are not. -/
def NotRL (k : Nat) (y : String) : Prop :=
  y ≠ s!"i{k}" ∧ y ≠ s!"g{k}" ∧ y ≠ s!"n{k}" ∧ y ≠ s!"x{k}" ∧ y ≠ s!"f{k}"

theorem fresh_RL {k i go c nx fr : Nat} {base : List (String × Value)} {y : String} (hy : NotRL k y)
    (hb : Fresh y base = true) : Fresh y (RL k i go c nx fr base) = true := by
  unfold Fresh at hb
  unfold RL Fresh
  simp only [List.all_cons, hb, Bool.and_true, Bool.and_eq_true, bne_iff_ne, ne_eq]
  exact ⟨fun e => hy.1 e.symm, fun e => hy.2.1 e.symm, fun e => hy.2.2.1 e.symm, fun e => hy.2.2.2.1 e.symm,
    fun e => hy.2.2.2.2 e.symm⟩

theorem repI_restore {A : Word} {bytes : List (BitVec 8)} {u : Abnf.Term} {lo : Nat} {hi : Option Nat}
    {S : Nat → Bool} {kd free k : Nat} {F : (Word → Word) → Prop} {base : List (String × Value)} {y : String}
    (hy : NotRL k y) (hb : Fresh y base = true) {w : PancakeState σ} (v : Option Value)
    (h : RepI A s0 bytes u lo hi S kd free k F base w) : RepI A s0 bytes u lo hi S kd free k F base (restore w y v) :=
  let ⟨i, go, c, nx, fr, hr, hc⟩ := h; ⟨i, go, c, nx, fr, runF_restore hr (fresh_RL hy hb) v, hc⟩

/-- A generated name of another number is no counter's. -/
theorem notRL_gen {k j : Nat} {y : String} (hy : GenName y j) (hj : j ≠ k) : NotRL k y :=
  ⟨fun e => hj (genName_inj hy (e ▸ name_i k)), fun e => hj (genName_inj hy (e ▸ name_g k)),
    fun e => hj (genName_inj hy (e ▸ name_n k)), fun e => hj (genName_inj hy (e ▸ name_x k)),
    fun e => hj (genName_inj hy (e ▸ name_f k))⟩

theorem notRL_e (k : Nat) : NotRL k s!"e{k}" :=
  ⟨ne_heads (tl_e k) (tl_i k) (by decide), ne_heads (tl_e k) (tl_g k) (by decide),
    ne_heads (tl_e k) (tl_n k) (by decide),
    ne_heads (tl_e k) (tl_x k) (by decide), ne_heads (tl_e k) (tl_f k) (by decide)⟩

theorem notRL_cd (k : Nat) : NotRL k s!"{s!"c{k}"}d" :=
  ⟨ne_heads (tl_cd k) (tl_i k) (by decide), ne_heads (tl_cd k) (tl_g k) (by decide),
    ne_heads (tl_cd k) (tl_n k) (by decide), ne_heads (tl_cd k) (tl_x k) (by decide),
    ne_heads (tl_cd k) (tl_f k) (by decide)⟩

section roundMem
variable {A : Word} {bytes : List (BitVec 8)} {u : Abnf.Term} {lo : Nat} {hi : Option Nat} {S : Nat → Bool}
  {kd free fr nx c : Nat} {F : (Word → Word) → Prop}

/-- What a round's body leaves: slot `nx` the ends of `u`'s matches from the frontier. -/
abbrev RoundBody (A : Word) (s0 : PancakeState σ) (bytes : List (BitVec 8)) (u : Abnf.Term) (lo : Nat)
    (hi : Option Nat) (S : Nat → Bool) (kd free fr nx c : Nat) (F : (Word → Word) → Prop) :
    (Word → Word) → Prop :=
  Left A s0 bytes u (setOf (Front (inputOf bytes) u lo S c)) nx (free + 2)
    (RepMem A s0 bytes u lo hi S kd free F 1 c fr)

theorem reach_none {input : Array Nat} {c : Nat} (h : ∀ e, ¬Reach input u S c e) :
    ∀ j, c ≤ j → ∀ e, ¬Reach input u S j e := by
  intro j hj
  induction j with
  | zero => have : c = 0 := by omega
            subst this; exact h
  | succ j ih =>
    intro e he
    by_cases hc : c = j + 1
    · subst hc; exact h e he
    · obtain ⟨y, hy, -⟩ := reach_succ.1 he
      exact ih (by omega) y hy

theorem ends_front {e : Nat} : Ends bytes u (setOf (Front (inputOf bytes) u lo S c)) e ↔
    ∃ y, Front (inputOf bytes) u lo S c y ∧ Matches AbnfRules.grammar (inputOf bytes) u y e := by
  simp only [Ends, setOf_iff]

/-- What a round leaves where it reaches nothing new: what it counted is all there is. -/
theorem round_none (hhi : ∀ h ∈ hi, c + 1 ≤ h)
    (hnone : ∀ e, ¬Ends bytes u (setOf (Front (inputOf bytes) u lo S c)) e) (e : Nat) :
    Done (inputOf bytes) u lo S c e ↔ Target (inputOf bytes) u lo hi S e := by
  by_cases hc : lo ≤ c
  · exact complete hc (fun h hh => by have := hhi h hh; omega)
      (fun y e hy hm => absurd (ends_front.2 ⟨y, hy, hm⟩) (hnone e)) e
  · have hr : ∀ e, ¬Reach (inputOf bytes) u S (c + 1) e := fun e he => by
      obtain ⟨y, hy, hm⟩ := reach_succ.1 he
      exact hnone e (ends_front.2 ⟨y, (front_lt (by omega)).2 hy, hm⟩)
    exact ⟨fun h => absurd h (done_lt (by omega)), fun ⟨j, h1, _, hj⟩ =>
      absurd hj (reach_none hr j (by omega) e)⟩

theorem body_mem {s0 : PancakeState σ} {m : Word → Word} (hkd : kd < free) (hnx : free ≤ nx) (hnxs : nx < slots)
    (h : RoundBody A s0 bytes u lo hi S kd free fr nx c F m) :
    ∃ m0, F m0 ∧ Base s0 A bytes m ∧ Kept A kd free m0 m ∧ Holds A m kd (Done (inputOf bytes) u lo S c) ∧
      Holds A m nx (Ends bytes u (setOf (Front (inputOf bytes) u lo S c))) ∧
      (lo ≤ c → Cnt (inputOf bytes) u lo S c) := by
  obtain ⟨m1, ⟨m0, hm0, hB1, hK1, h1, -⟩, hH, hB, hK⟩ := h
  obtain ⟨hD, -, hC⟩ := h1 rfl
  exact ⟨m0, hm0, hB, kept_trans hK1 (kept_wide (by omega) (.inr ⟨hnx, hnxs⟩) hK),
    setAt_kept hD (by omega) (by omega) hnxs (by omega) hK, hH, hC⟩

end roundMem

section roundMem2
variable {A : Word} {bytes : List (BitVec 8)} {u : Abnf.Term} {lo : Nat} {hi : Option Nat} {S : Nat → Bool}
  {kd free nx c : Nat} {F : (Word → Word) → Prop}

theorem done_next (hle : lo ≤ c + 1) (e : Nat) : Done (inputOf bytes) u lo S (c + 1) e ↔
    Done (inputOf bytes) u lo S c e ∨ Ends bytes u (setOf (Front (inputOf bytes) u lo S c)) e := by
  rw [done_succ hle, ends_front]
  constructor
  · rintro (h | h)
    · exact .inl h
    · exact next_cover h
  · rintro (h | h)
    · exact .inl h
    · exact .inr (next_sub h)

theorem front_next (e : Nat) : Front (inputOf bytes) u lo S (c + 1) e ↔
    Ends bytes u (setOf (Front (inputOf bytes) u lo S c)) e ∧ ¬Done (inputOf bytes) u lo S c e := by
  rw [front_succ, ends_front]
  constructor
  · rintro ⟨h, hn⟩
    rcases next_cover h with h' | h'
    · exact absurd h' hn
    · exact ⟨h', hn⟩
  · rintro ⟨h, hn⟩
    exact ⟨next_sub h, hn⟩

theorem cnt_next (hle : lo ≤ c + 1) (hC : lo ≤ c → Cnt (inputOf bytes) u lo S c) :
    Cnt (inputOf bytes) u lo S (c + 1) := by
  by_cases hc : lo ≤ c
  · exact cnt_step hc (hC hc)
  · have : lo = c + 1 := by omega
    rw [← this]; exact cnt_lo

/-- Every slot a set after two slots changed. -/
theorem allSets_two {m0 m : Word → Word} {k1 k2 : Nat} {T1 T2 : Nat → Bool} (h : AllSets A m0) (hk1 : k1 < slots)
    (hk2 : k2 < slots) (h1 : SetAt m A k1 T1) (h2 : SetAt m A k2 T2)
    (hf : ∀ a, ¬InSlot A k1 a → ¬InSlot A k2 a → m a = m0 a) : AllSets A m := fun k hk => by
  by_cases e1 : k = k1
  · subst e1; exact ⟨T1, h1⟩
  by_cases e2 : k = k2
  · subst e2; exact ⟨T2, h2⟩
  obtain ⟨S, hS⟩ := h k hk
  exact ⟨S, setAt_frame hS fun i hi => hf _ (fun ⟨_, hi', e⟩ => e1 (slotW_inj hk hk1 hi hi' e).1)
    fun ⟨_, hi', e⟩ => e2 (slotW_inj hk hk2 hi hi' e).1⟩

/-- **A round that counts**: the new positions into slot `kd`, and into slot `nx` as the next frontier. -/
theorem round_grow {s0 : PancakeState σ} {m m' : Word → Word} (hA8 : A.toNat % 8 = 0)
    (hlen : bytes.length ≤ inputMax) (hle : lo ≤ c + 1) (hkd : kd < free) (hnx : free ≤ nx) (hnxs : nx < slots)
    (h : ∃ m0, F m0 ∧ Base s0 A bytes m ∧ Kept A kd free m0 m ∧ Holds A m kd (Done (inputOf bytes) u lo S c) ∧
      Holds A m nx (Ends bytes u (setOf (Front (inputOf bytes) u lo S c))) ∧
      (lo ≤ c → Cnt (inputOf bytes) u lo S c))
    {v : Value} (hg : GrowRet A nx kd (setOf (Ends bytes u (setOf (Front (inputOf bytes) u lo S c))))
      (setOf (Done (inputOf bytes) u lo S c)) m v m') :
    RepMem A s0 bytes u lo hi S kd free F 1 (c + 1) nx m' := by
  obtain ⟨m0, hm0, hB, hK, -, -, hC⟩ := h
  obtain ⟨-, hX, hD, hf⟩ := hg
  have hkd' : kd < slots := by omega
  have hK' : Kept A kd free m m' := fun a ha hb => hf a (hb nx hnx hnxs) ha
  refine ⟨m0, hm0, base_keep hA8 hlen hkd' hB hK' (allSets_two hB.1 hnxs hkd' hX hD hf), kept_trans hK hK',
    fun _ => ⟨?_, ?_, fun _ => cnt_next hle hC⟩, fun h => nomatch h⟩
  · unfold Holds
    rw [← setOf_eq (T := fun z => setOf (Done (inputOf bytes) u lo S c) z ||
      (setOf (Ends bytes u (setOf (Front (inputOf bytes) u lo S c))) z &&
        !setOf (Done (inputOf bytes) u lo S c) z)) fun e => ?_]
    · exact hD
    rw [done_next hle]
    simp only [Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, setOf_iff]
    constructor
    · rintro (h | ⟨h, -⟩)
      · exact .inl h
      · exact .inr h
    · rintro (h | h)
      · exact .inl h
      · by_cases hd : Done (inputOf bytes) u lo S c e
        · exact .inl hd
        · exact .inr ⟨h, setOf_false hd⟩
  · unfold Holds
    rw [← setOf_eq (T := fun z => setOf (Ends bytes u (setOf (Front (inputOf bytes) u lo S c))) z &&
      !setOf (Done (inputOf bytes) u lo S c) z) fun e => ?_]
    · exact hX
    rw [front_next]
    simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, setOf_iff]
    constructor
    · rintro ⟨h, hn⟩
      exact ⟨h, fun hd => by rw [setOf_iff.2 hd] at hn; exact nomatch hn⟩
    · rintro ⟨h, hn⟩
      exact ⟨h, setOf_false hn⟩

/-- **A round before `lo`**: its positions the next frontier, none counted. -/
theorem round_skip {s0 : PancakeState σ} {m : Word → Word} (hlt : c + 1 < lo)
    (h : ∃ m0, F m0 ∧ Base s0 A bytes m ∧ Kept A kd free m0 m ∧ Holds A m kd (Done (inputOf bytes) u lo S c) ∧
      Holds A m nx (Ends bytes u (setOf (Front (inputOf bytes) u lo S c))) ∧
      (lo ≤ c → Cnt (inputOf bytes) u lo S c)) :
    RepMem A s0 bytes u lo hi S kd free F 1 (c + 1) nx m := by
  obtain ⟨m0, hm0, hB, hK, hD, hN, -⟩ := h
  refine ⟨m0, hm0, hB, hK, fun _ => ⟨holds_congr hD fun e => ⟨fun h => absurd h (done_lt (by omega)),
    fun h => absurd h (done_lt (by omega))⟩, holds_congr hN fun e => ?_, fun h => absurd h (by omega)⟩,
    fun h => nomatch h⟩
  rw [ends_front, front_lt hlt, reach_succ]
  exact ⟨fun ⟨y, hy, hm⟩ => ⟨y, (front_lt (by omega)).1 hy, hm⟩,
    fun ⟨y, hy, hm⟩ => ⟨y, (front_lt (by omega)).2 hy, hm⟩⟩

end roundMem2

theorem fresh_base {y : String} {k k' : Nat} (hy : GenName y k) (hcb : y ≠ s!"{s!"c{k}"}b")
    {l : List (String × Value)} (hav : Avoid l k k') (hk : k < k') (v0 : Value) :
    Fresh y ((s!"{s!"c{k}"}b", v0) :: l) = true := by
  have := fresh_of hav (Nat.le_refl _) hk hy
  unfold Fresh at this ⊢
  simp only [List.all_cons, this, Bool.and_true, bne_iff_ne, ne_eq]
  exact fun e => hcb e.symm

theorem cd_ne_cb (k : Nat) : s!"{s!"c{k}"}d" ≠ s!"{s!"c{k}"}b" := fun e => by
  have := congrArg String.toList e
  rw [tl_cd, tl_cb] at this
  have := List.append_cancel_left (List.cons.inj this).2
  exact absurd this (by decide)

theorem vals_mem {w : PancakeState σ} {l : List (String × Value)} {G : (Word → Word) → Prop}
    (h : RunF s0 l G w) {x : String} {v : Value} (hx : (x, v) ∈ l) : eval w (.var x) = some v := h.1.vals _ hx

theorem lowKK_repTail {k free lo : Nat} {d : Syntax.PExpr} (hd : SlotE d) : LowKK (repTail k free lo d) := by
  obtain ⟨Ed, hEd⟩ := slotE_lower hd
  unfold repTail
  refine lowKK_append (xs := [_]) (lowK_any _ (k := .skip) rfl) (lowKK_append (xs := [_])
    (lowKK_call (a := [.var _]) rfl) (lowKK_ite rfl (lowK_any _ (k := .skip) rfl) ?_))
  refine lowKK_append (xs := [_]) (lowKK_ite rfl lowKK_nil (lowKK_call (lowerArgs_two rfl hEd))) ?_
  exact lowK_any _ (k := .skip) rfl

/-- The round's slots swapped: `x{k}` names the other of the two slots. -/
theorem rep_swap (o : Oracle σ) {s0 : PancakeState σ} {A : Word} {bytes : List (BitVec 8)}
    {u : Abnf.Term} {lo : Nat} {hi : Option Nat} {S : Nat → Bool} {F : (Word → Word) → Prop} {kd free k k' : Nat}
    (hfree : free + 2 ≤ slots) {l : List (String × Value)} (hav : Avoid l k k') (hk : k < k') (v0 : Value)
    {i c nx : Nat} (hc : c = i) (hib : i < bytes.length + lo + 1) (hhi : ∀ h ∈ hi, c + 1 ≤ h)
    (hnx : nx = free ∨ nx = free + 1) :
    Frag o [.ite (Syntax.eEq (Syntax.v s!"x{k}") (Syntax.n free)) [.assign s!"x{k}" (Syntax.n (free + 1))]
        [.assign s!"x{k}" (Syntax.n free)]]
      (RunF s0 ((s!"e{k}", (0 : Value)) :: RL k (i + 1) 1 (c + 1) nx nx ((s!"{s!"c{k}"}b", v0) :: l))
        (RepMem A s0 bytes u lo hi S kd free F 1 (c + 1) nx))
      (RepI A s0 bytes u lo hi S kd free k F ((s!"{s!"c{k}"}b", v0) :: l)) := by
  let base := (s!"{s!"c{k}"}b", v0) :: l
  have hI := inputMax_eq
  have hsl := slots_le
  have hx1 : Fresh s!"x{k}" [(s!"e{k}", (0 : Value)), (s!"i{k}", BitVec.ofNat 64 (i + 1)),
      (s!"g{k}", BitVec.ofNat 64 1), (s!"n{k}", BitVec.ofNat 64 (c + 1))] = true :=
    fresh_heads (tl_x k) rfl [_, _, _, _]
      (by simp only [List.all_cons, List.all_nil, List.head?_cons, tl_e, tl_i, tl_g, tl_n]; rfl)
  have hx2 : Fresh s!"x{k}" ((s!"f{k}", BitVec.ofNat 64 nx) :: base) = true :=
    fresh_cons (ne_heads (tl_f k) (tl_x k) (by decide))
      (fresh_base (name_x k) (ne_heads (tl_x k) (tl_cb k) (by decide)) hav hk v0)
  have hfin : ∀ nx', (nx' = free ∨ nx' = free + 1) → nx ≠ nx' → ∀ w,
      RunF s0 ((s!"e{k}", (0 : Value)) :: RL k (i + 1) 1 (c + 1) nx' nx base)
        (RepMem A s0 bytes u lo hi S kd free F 1 (c + 1) nx) w → RepI A s0 bytes u lo hi S kd free k F base w :=
    fun nx' h1 h2 w h => ⟨i + 1, 1, c + 1, nx', nx, runF_mono h (fun q hq => List.mem_cons_of_mem _ hq)
      fun _ h => h, .inr rfl, by omega, fun _ => ⟨by omega, hhi, h1, by omega, h2⟩⟩
  refine ScanRun.frag_if o rfl (lowK_any _ (k := .skip) rfl) (lowK_any _ (k := .skip) rfl) rfl rfl repI_clock
    (b := decide (nx = free)) (fun w h => FramerCode.eval_eq (by omega) (by omega) (vals_mem h (by simp [RL])) rfl)
    (fun e => frag_conseq (runF_swap o (pre := [_, _, _, _]) hx1 hx2 rfl (v := BitVec.ofNat 64 (free + 1))
      fun _ _ => rfl) (fun _ h => h) (hfin (free + 1) (.inr rfl) (by have := of_decide_eq_true e; omega)))
    fun e => frag_conseq (runF_swap o (pre := [_, _, _, _]) hx1 hx2 rfl (v := BitVec.ofNat 64 free)
      fun _ _ => rfl) (fun _ h => h) (hfin free (.inl rfl) (by have := of_decide_eq_false e; omega))

/-- A round after its body: the count, then the loop stopped if the round reached nothing, else what it reached
added from round `lo` on and the slots swapped. -/
theorem rep_tail (o : Oracle σ) {ofs : Nat} {A : Word} {s0 : PancakeState σ} (hA : Area ofs A s0)
    (hcode : ProgCode s0.code ofs) {bytes : List (BitVec 8)} (hlen : bytes.length ≤ inputMax)
    {u : Abnf.Term} {lo : Nat} {hi : Option Nat} (hlo : lo < 2 ^ 32) {S : Nat → Bool} {F : (Word → Word) → Prop}
    {free k k' : Nat} (hfree : free + 2 ≤ slots) {d : Syntax.PExpr} (hdE : SlotE d) {kd : Nat} (hkd : kd < free)
    {l : List (String × Value)} (hd : SlotIs l d kd) (hav : Avoid l k k') (hk : k < k') (v0 : Value)
    {i c nx fr : Nat} (hc : c = i) (hib : i < bytes.length + lo + 1) (hhi : ∀ h ∈ hi, c + 1 ≤ h)
    (hnx : nx = free ∨ nx = free + 1) (hfr : fr < free + 2) (hne : fr ≠ nx) :
    Frag o (repTail k free lo d)
      (RunF s0 (RL k (i + 1) 1 c nx fr ((s!"{s!"c{k}"}b", v0) :: l)) (RoundBody A s0 bytes u lo hi S kd free fr nx c F))
      (RepI A s0 bytes u lo hi S kd free k F ((s!"{s!"c{k}"}b", v0) :: l)) := by
  let base := (s!"{s!"c{k}"}b", v0) :: l
  have hI := inputMax_eq
  have hsl := slots_le
  have hnxs : nx < slots := by omega
  have hkd' : kd < slots := by omega
  -- the count
  unfold repTail
  have hn1 : Fresh s!"n{k}" [(s!"i{k}", BitVec.ofNat 64 (i + 1)), (s!"g{k}", BitVec.ofNat 64 1)] = true := by
    simp only [Fresh, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true, bne_iff_ne, ne_eq]
    exact ⟨ne_heads (tl_i k) (tl_n k) (by decide), ne_heads (tl_g k) (tl_n k) (by decide)⟩
  have hn2 : Fresh s!"n{k}" ((s!"x{k}", BitVec.ofNat 64 nx) :: (s!"f{k}", BitVec.ofNat 64 fr) :: base) = true :=
    fresh_cons (ne_heads (tl_x k) (tl_n k) (by decide)) (fresh_cons (ne_heads (tl_f k) (tl_n k) (by decide))
      (fresh_base (name_n k) (ne_heads (tl_n k) (tl_cb k) (by decide)) hav hk v0))
  refine frag_append (xs := [_]) (runF_swap o (pre := [_, _]) hn1 hn2 rfl (v := BitVec.ofNat 64 (c + 1))
    fun w h => ev_inc (vals_mem h (by simp))) ?_
  -- whether the round reached anything
  have hre : Fresh s!"e{k}" (RL k (i + 1) 1 (c + 1) nx fr base) = true :=
    fresh_RL (notRL_e k) (fresh_base (name_e k) (ne_heads (tl_e k) (tl_cb k) (by decide)) hav hk v0)
  refine frag_append (xs := [_]) (empty_frag o hA hcode (l := RL k (i + 1) 1 (c + 1) nx fr base)
    (F := RoundBody A s0 bytes u lo hi S kd free fr nx c F) hre rfl hnxs (fun w h => vals_mem h (by simp [RL]))
    (S := setOf (Ends bytes u (setOf (Front (inputOf bytes) u lo S c)))) fun m hm =>
      let ⟨_, _, _, _, _, hN, _⟩ := body_mem hkd (by omega) hnxs hm; hN) ?_
  obtain ⟨Ed0, hEd0⟩ := slotE_lower hdE
  have hlowE : LowKK
      [.ite (Syntax.eLt (Syntax.v s!"n{k}") (Syntax.n lo)) [] [.call s!"{s!"c{k}"}d" "setGrow" [Syntax.v s!"x{k}", d]],
       .assign s!"f{k}" (Syntax.v s!"x{k}"),
       .ite (Syntax.eEq (Syntax.v s!"x{k}") (Syntax.n free)) [.assign s!"x{k}" (Syntax.n (free + 1))]
         [.assign s!"x{k}" (Syntax.n free)]] :=
    lowKK_append (xs := [_]) (lowKK_ite rfl lowKK_nil (lowKK_call (lowerArgs_two rfl hEd0)))
      (lowK_any _ (k := .skip) rfl)
  have hlowI := lowKK_ite (c := Syntax.v s!"e{k}") rfl (lowK_any [.assign s!"g{k}" (Syntax.n 0)] (k := .skip) rfl) hlowE
  refine frag_exists hlowI fun ve => ?_
  refine frag_pure (ve = 1 ∨ ve = 0) (fun w h => let ⟨_, _, _, hr⟩ := h.2; hr.elim (fun h => .inl h.1)
    fun h => .inr h.1) hlowI fun hve => ?_
  have hD := hd
  obtain ⟨Ed, hEd, hvd⟩ := slotIs_eval (σ := σ) hd
  rcases hve with rfl | rfl
  · -- the round reached nothing: the loop stops, what it counted all there is
    refine ScanRun.frag_if o rfl (lowK_any _ (k := .skip) rfl) hlowE rfl rfl repI_clock (b := true)
      (fun w h => vals_mem h (List.mem_cons_self ..)) (fun _ => ?_) fun h => nomatch h
    have hg1 : Fresh s!"g{k}" [(s!"e{k}", (1 : Value)), (s!"i{k}", BitVec.ofNat 64 (i + 1))] = true :=
      fresh_cons (ne_heads (tl_e k) (tl_g k) (by decide)) (fresh_cons (ne_heads (tl_i k) (tl_g k) (by decide)) rfl)
    have hg2 : Fresh s!"g{k}" ((s!"n{k}", BitVec.ofNat 64 (c + 1)) :: (s!"x{k}", BitVec.ofNat 64 nx) ::
        (s!"f{k}", BitVec.ofNat 64 fr) :: base) = true :=
      fresh_heads (tl_g k) (fresh_base (name_g k) (ne_heads (tl_g k) (tl_cb k) (by decide)) hav hk v0) [_, _, _]
        (by simp only [List.all_cons, List.all_nil, List.head?_cons, tl_n, tl_x, tl_f]; rfl)
    refine frag_conseq (runF_swap o (pre := [_, _]) hg1 hg2 rfl (v := BitVec.ofNat 64 0) fun _ _ => rfl)
      (fun _ h => h) fun w h => ⟨i + 1, 0, c + 1, nx, fr, runF_mono h (fun q hq => List.mem_cons_of_mem _ hq) ?_,
        .inl rfl, by omega, (fun h => nomatch h)⟩
    rintro m' ⟨m, hm, rfl, hr⟩
    rcases hr with ⟨-, hnone⟩ | ⟨h10, -⟩
    · obtain ⟨m0, hm0, hB, hK, hD, -, -⟩ := body_mem hkd (by omega) hnxs hm
      exact ⟨m0, hm0, hB, hK, (fun h => nomatch h), fun _ => holds_congr hD (round_none hhi fun e he => by
        have := hnone e; rw [setOf_iff.2 he] at this; exact nomatch this)⟩
    · exact absurd h10 (by decide)
  · refine ScanRun.frag_if o rfl (lowK_any _ (k := .skip) rfl) hlowE rfl rfl repI_clock (b := false)
      (fun w h => vals_mem h (List.mem_cons_self ..)) (fun h => nomatch h) fun _ => ?_
    have hcl : ∀ w, RunF s0 ((s!"e{k}", (0 : Value)) :: RL k (i + 1) 1 (c + 1) nx fr base)
        (fun m' => ∃ m, RoundBody A s0 bytes u lo hi S kd free fr nx c F m ∧
          EmptyRet (setOf (Ends bytes u (setOf (Front (inputOf bytes) u lo S c)))) m 0 m') w →
        eval w (.cmp .less (.var s!"n{k}") (.const (BitVec.ofNat 64 lo))) = some (bw (decide (c + 1 < lo))) :=
      fun w h => FramerCode.eval_lt (by omega) (by omega) (vals_mem h (by simp [RL])) rfl
    refine frag_append (xs := [_]) (M := RunF s0 ((s!"e{k}", (0 : Value)) :: RL k (i + 1) 1 (c + 1) nx fr base)
      (RepMem A s0 bytes u lo hi S kd free F 1 (c + 1) nx)) (frag_ite o rfl (runF_clock _ _ _)
        (fun w h => ⟨_, hcl w h⟩) ?_ (noDecl _ rfl) ?_ ?_) ?_
    · refine frag_nil o fun w ⟨h, hne0⟩ => runF_mono h (fun _ hq => hq) fun m' ⟨m, hm, hmm, _⟩ => ?_
      have hlt : c + 1 < lo := of_decide_eq_true (FramerCode.bw_ne0 (by rw [← hcl w h]; exact hne0))
      rw [hmm]; exact round_skip hlt (body_mem hkd (by omega) hnxs hm)
    · have hrt : Fresh s!"{s!"c{k}"}d" ((s!"e{k}", (0 : Value)) :: RL k (i + 1) 1 (c + 1) nx fr base) = true :=
        fresh_cons (ne_heads (tl_e k) (tl_cd k) (by decide)) (fresh_RL (notRL_cd k)
          (fresh_base (name_cd k) (cd_ne_cb k) hav hk v0))
      refine frag_pure (lo ≤ c + 1) (fun w h => by
          have := FramerCode.bw_eq0 (by rw [← hcl w h.1]; exact h.2); simp at this; omega)
        (lowKK_call (lowerArgs_two rfl hEd)) fun hle => ?_
      refine frag_conseq (grow_frag o hA hcode (rt := s!"{s!"c{k}"}d") hrt rfl hEd hnxs hkd' (by omega)
        (fun w h => vals_mem h (by simp [RL])) (fun w h => hvd w fun q hq => h.1.vals q (by simp [RL, base, hq]))
        (Sx := setOf (Ends bytes u (setOf (Front (inputOf bytes) u lo S c))))
        (Sd := setOf (Done (inputOf bytes) u lo S c)) fun m' ⟨m, hm, hmm, _⟩ => by
          obtain ⟨_, _, _, _, hD, hN, _⟩ := body_mem hkd (by omega) hnxs hm
          rw [hmm]; exact ⟨hN, hD⟩) (fun w h => h.1) fun w ⟨vg, h⟩ =>
            runF_mono h (fun q hq => List.mem_cons_of_mem _ hq) fun m'' ⟨m', ⟨m, hm, hmm, _⟩, hg⟩ =>
              round_grow hA.hA hlen hle hkd (by omega) hnxs (by rw [hmm]; exact body_mem hkd (by omega) hnxs hm) hg
    · intro w y v' h hy
      simp only [declared, List.mem_cons, List.not_mem_nil, or_false] at hy
      subst hy
      exact runF_restore h (fresh_cons (ne_heads (tl_e k) (tl_cd k) (by decide)) (fresh_RL (notRL_cd k)
        (fresh_base (name_cd k) (cd_ne_cb k) hav hk v0))) v'
    · -- the slots swapped
      have hf1 : Fresh s!"f{k}" [(s!"e{k}", (0 : Value)), (s!"i{k}", BitVec.ofNat 64 (i + 1)),
          (s!"g{k}", BitVec.ofNat 64 1), (s!"n{k}", BitVec.ofNat 64 (c + 1)), (s!"x{k}", BitVec.ofNat 64 nx)] = true :=
        fresh_heads (tl_f k) rfl [_, _, _, _, _]
          (by simp only [List.all_cons, List.all_nil, List.head?_cons, tl_e, tl_i, tl_g, tl_n, tl_x]; rfl)
      refine frag_append (xs := [_]) (M := RunF s0 ((s!"e{k}", (0 : Value)) :: RL k (i + 1) 1 (c + 1) nx nx base)
        (RepMem A s0 bytes u lo hi S kd free F 1 (c + 1) nx)) (runF_swap o (pre := [_, _, _, _, _]) hf1
        (fresh_base (name_f k) (ne_heads (tl_f k) (tl_cb k) (by decide)) hav hk v0) rfl (v := BitVec.ofNat 64 nx)
        fun w h => vals_mem h (by simp)) ?_
      exact rep_swap o hfree hav hk v0 hc hib hhi hnx

/-- **A round of the repetition's loop**: the body from the frontier into slot `nx`, then the count; a round that
reaches nothing stops the loop, another counts what it adds and swaps the slots. -/
theorem rep_round (o : Oracle σ) {ofs : Nat} {A : Word} {s0 : PancakeState σ} (hA : Area ofs A s0)
    (hcode : ProgCode s0.code ofs) {bytes : List (BitVec 8)} (hlen : bytes.length ≤ inputMax)
    {u : Abnf.Term} {lo : Nat} {hi : Option Nat} (hlo : lo < 2 ^ 32) {S : Nat → Bool} {F : (Word → Word) → Prop}
    {free k k' : Nat} (hfree : free + 2 ≤ slots) {rp : Bool} {body : List Syntax.PStmt}
    (hbody : Does o A s0 bytes rp u (Syntax.v s!"f{k}") (Syntax.v s!"x{k}") (free + 2) (k + 1) (body, k'))
    {d : Syntax.PExpr} (hdE : SlotE d) {kd : Nat} (hkd : kd < free)
    {l : List (String × Value)} (hd : SlotIs l d kd) (hav : Avoid l k k') (hk : k < k')
    (hnn : rp = true → ("nn", BitVec.ofNat 64 bytes.length) ∈ l) (v0 : Value)
    {i c nx fr : Nat} (hc : c = i) (hib : i < bytes.length + lo + 1) (hhi : ∀ h ∈ hi, c + 1 ≤ h)
    (hnx : nx = free ∨ nx = free + 1) (hfr : fr < free + 2) (hne : fr ≠ nx) :
    Frag o (body ++ repTail k free lo d)
      (RunF s0 (RL k (i + 1) 1 c nx fr ((s!"{s!"c{k}"}b", v0) :: l)) (RepMem A s0 bytes u lo hi S kd free F 1 c fr))
      (RepI A s0 bytes u lo hi S kd free k F ((s!"{s!"c{k}"}b", v0) :: l)) := by
  let base := (s!"{s!"c{k}"}b", v0) :: l
  have hI := inputMax_eq
  have hsl := slots_le
  have hnxs : nx < slots := by omega
  have hkd' : kd < slots := by omega
  have hlowT := lowKK_repTail (k := k) (free := free) (lo := lo) hdE
  have hl0 : ∀ q ∈ l, q ∈ RL k (i + 1) 1 c nx fr base := fun q hq => by simp [RL, base, hq]
  have hav1 : Avoid (RL k (i + 1) 1 c nx fr base) (k + 1) k' := fun q hq j hj1 hj2 hg => by
    simp only [RL, base, List.mem_cons] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | hq
    · have := genName_inj hg (name_i k); omega
    · have := genName_inj hg (name_g k); omega
    · have := genName_inj hg (name_n k); omega
    · have := genName_inj hg (name_x k); omega
    · have := genName_inj hg (name_f k); omega
    · have := genName_inj hg (name_cb k); omega
    · exact hav q hq j (by omega) hj2 hg
  -- the body
  refine frag_append (hbody (RL k (i + 1) 1 c nx fr base) _ fr nx (setOf (Front (inputOf bytes) u lo S c))
    (.inr ⟨_, rfl, by simp [RL]⟩) (.inr ⟨_, rfl, by simp [RL]⟩) hfr (by omega) hne hav1
    (fun e => hl0 _ (hnn e)) fun m ⟨_, _, hB, _, h1, _⟩ => ⟨(h1 rfl).2.1, hB⟩)
    (frag_exists hlowT fun l1 => frag_conseq (P0 := RunF s0 (RL k (i + 1) 1 c nx fr base)
      (RoundBody A s0 bytes u lo hi S kd free fr nx c F)) ?_ (fun w h => runF_mono h.2
        (fun q hq => List.mem_append_right _ hq) fun _ h => h) fun _ h => h)
  exact rep_tail o hA hcode hlen hlo hfree hdE hkd hd hav hk v0 hc hib hhi hnx hfr hne

/-- The loop's condition, as it lowers. -/
def repCond (k lo : Nat) : PancakeExp :=
  .op .and_ (.var s!"g{k}") (.cmp .less (.var s!"i{k}") (.op .add (.var "nn") (.const (BitVec.ofNat 64 (lo + 1)))))

theorem repCond_lower (k lo : Nat) : Lower.lowerExp (Syntax.eAnd (Syntax.v s!"g{k}")
    (Syntax.eLt (Syntax.v s!"i{k}") (Syntax.eAdd (Syntax.v "nn") (Syntax.n (lo + 1))))) = some (repCond k lo) := rfl

theorem bw_of {go : Nat} (h : go = 0 ∨ go = 1) : BitVec.ofNat 64 go = bw (decide (go = 1)) := by
  rcases h with rfl | rfl <;> rfl

theorem repCond_eval {k lo i go c nx fr nn : Nat} {base : List (String × Value)} {G : (Word → Word) → Prop}
    {w : PancakeState σ} (h : RunF s0 (RL k i go c nx fr base) G w) (hnn : ("nn", BitVec.ofNat 64 nn) ∈ base)
    (hgo : go = 0 ∨ go = 1) (hi : i < 2 ^ 63) (hb : nn + (lo + 1) < 2 ^ 63) :
    eval w (repCond k lo) = some (bw (decide (go = 1) && decide (i < nn + (lo + 1)))) :=
  FramerCode.eval_and (by rw [← bw_of hgo]; exact vals_mem h (by simp [RL]))
    (FramerCode.eval_lt hi hb (vals_mem h (by simp [RL])) (ev_inc (vals_mem h (by simp [RL, hnn]))))

theorem stop_done {input : Array Nat} {u : Abnf.Term} {lo c : Nat} {S : Nat → Bool} (e : Nat) :
    Done input u lo S c e ↔ Target input u lo (some c) S e :=
  ⟨fun ⟨j, h1, h2, h⟩ => ⟨j, h1, fun h' hh => by cases hh; exact h2, h⟩,
   fun ⟨j, h1, h2, h⟩ => ⟨j, h1, h2 c rfl, h⟩⟩

theorem target_ends {bytes : List (BitVec 8)} {u : Abnf.Term} {lo : Nat} {hi : Option Nat} {S : Nat → Bool}
    (e : Nat) : Target (inputOf bytes) u lo hi S e ↔ Ends bytes (.rep lo hi u) S e := by
  simp only [Target, Reach, Ends, AbnfMatch.rep_iff]
  exact ⟨fun ⟨j, h1, h2, x, hx, h⟩ => ⟨x, hx, j, h1, h2, h⟩,
    fun ⟨x, hx, j, h1, h2, h⟩ => ⟨j, h1, h2, x, hx, h⟩⟩

/-- **A turn of the repetition's loop**: the turn counted, the bound checked, a round while the loop goes on. -/
theorem rep_iter (o : Oracle σ) {ofs : Nat} {A : Word} {s0 : PancakeState σ} (hA : Area ofs A s0)
    (hcode : ProgCode s0.code ofs) {bytes : List (BitVec 8)} (hlen : bytes.length ≤ inputMax)
    {u : Abnf.Term} {lo : Nat} {hi : Option Nat} (hlo : lo < 2 ^ 32) (hhi32 : ∀ h ∈ hi, h < 2 ^ 32)
    {S : Nat → Bool}
    {F : (Word → Word) → Prop} {free k k' : Nat} (hfree : free + 2 ≤ slots) {rp : Bool} {body : List Syntax.PStmt}
    (hbody : Does o A s0 bytes rp u (Syntax.v s!"f{k}") (Syntax.v s!"x{k}") (free + 2) (k + 1) (body, k'))
    (hlowb : LowKK body) (hdecl : ∀ y ∈ declared body, ∃ j, k + 1 ≤ j ∧ j < k' ∧ GenName y j)
    {d : Syntax.PExpr} (hdE : SlotE d) {kd : Nat} (hkd : kd < free)
    {l : List (String × Value)} (hd : SlotIs l d kd) (hav : Avoid l k k') (hk : k < k')
    (hnnl : ("nn", BitVec.ofNat 64 bytes.length) ∈ l) (v0 : Value) :
    Frag o (inc s!"i{k}" :: repStop .none k hi ++ [.ite (Syntax.v s!"g{k}") (body ++ repTail k free lo d) []])
      (fun w => RepI A s0 bytes u lo hi S kd free k F ((s!"{s!"c{k}"}b", v0) :: l) w ∧
        eval w (repCond k lo) ≠ some 0)
      (RepI A s0 bytes u lo hi S kd free k F ((s!"{s!"c{k}"}b", v0) :: l)) := by
  let base := (s!"{s!"c{k}"}b", v0) :: l
  have hI := inputMax_eq
  have hlowT := lowKK_repTail (k := k) (free := free) (lo := lo) hdE
  have hlowS : LowKK (repStop .none k hi) := by cases hi <;> exact lowK_any _ (k := .skip) rfl
  have hlowIte : LowKK [.ite (Syntax.v s!"g{k}") (body ++ repTail k free lo d) []] :=
    lowKK_ite rfl (lowKK_append hlowb hlowT) lowKK_nil
  have hlow :
      LowKK (inc s!"i{k}" :: repStop .none k hi ++ [.ite (Syntax.v s!"g{k}") (body ++ repTail k free lo d) []]) :=
    lowKK_append (xs := [_] ++ _) (lowKK_append (xs := [_]) (lowK_any _ (k := .skip) rfl) hlowS) hlowIte
  have hnnb : ("nn", BitVec.ofNat 64 bytes.length) ∈ base := List.mem_cons_of_mem _ hnnl
  -- the restore of the round's locals
  have hres : ∀ w y v, RepI A s0 bytes u lo hi S kd free k F base w →
      y ∈ declared (body ++ repTail k free lo d) →
      RepI A s0 bytes u lo hi S kd free k F base (restore w y v) := fun w y v h hy => by
    rw [declared_append] at hy
    rcases List.mem_append.1 hy with hy | hy
    · obtain ⟨j, h1, h2, hg⟩ := hdecl y hy
      exact repI_restore (notRL_gen hg (by omega)) (fresh_cons (fun e => by
        have := genName_inj hg (e ▸ name_cb k); omega) (fresh_of hav (by omega) h2 hg)) v h
    · simp only [repTail, inc, declared, List.mem_cons, List.not_mem_nil, or_false] at hy
      subst hy
      exact repI_restore (notRL_e k) (fresh_base (name_e k) (ne_heads (tl_e k) (tl_cb k) (by decide)) hav hk v0) v h
  -- the state taken apart
  refine frag_conseq (P0 := fun w => ∃ q : Nat × Nat × Nat × Nat × Nat, RunF s0 (RL k q.1 q.2.1 q.2.2.1 q.2.2.2.1
      q.2.2.2.2 base) (RepMem A s0 bytes u lo hi S kd free F q.2.1 q.2.2.1 q.2.2.2.2) w ∧
        RepCnt bytes.length lo hi free q.1 q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2 ∧ eval w (repCond k lo) ≠ some 0)
    (frag_exists hlow fun ⟨i, go, c, nx, fr⟩ => ?_) (fun w ⟨⟨i, go, c, nx, fr, h, hc⟩, hne⟩ =>
      ⟨(i, go, c, nx, fr), h, hc, hne⟩) fun _ h => h
  refine frag_pure (go = 1 ∧ i < bytes.length + lo + 1) (fun w ⟨h, hc, hne⟩ => ?_) hlow fun ⟨hgo, hib⟩ => ?_
  · have hib := hc.2.1
    have := repCond_eval (lo := lo) h hnnb hc.1 (by omega) (by omega)
    rw [this] at hne
    have := FramerCode.bw_ne0 hne
    simp only [Bool.and_eq_true, decide_eq_true_eq] at this
    exact ⟨this.1, by omega⟩
  subst hgo
  refine frag_conseq (P0 := fun w =>
    RunF s0 (RL k i 1 c nx fr base) (RepMem A s0 bytes u lo hi S kd free F 1 c fr) w ∧
    RepCnt bytes.length lo hi free i 1 c nx fr) ?_ (fun w ⟨h, hc, _⟩ => ⟨h, hc⟩) fun _ h => h
  refine frag_pure (RepCnt bytes.length lo hi free i 1 c nx fr) (fun _ h => h.2) hlow fun hc => ?_
  obtain ⟨-, -, h3⟩ := hc
  obtain ⟨hc1, hchi, hnx, hfr, hne⟩ := h3 rfl
  subst hc1
  refine frag_conseq ?_ (fun _ h => h.1) fun _ h => h
  -- the turn counted
  have hi1 : Fresh s!"i{k}" ((s!"g{k}", BitVec.ofNat 64 1) :: (s!"n{k}", BitVec.ofNat 64 c) ::
      (s!"x{k}", BitVec.ofNat 64 nx) :: (s!"f{k}", BitVec.ofNat 64 fr) :: base) = true :=
    fresh_heads (tl_i k) (fresh_base (name_i k) (ne_heads (tl_i k) (tl_cb k) (by decide)) hav hk v0) [_, _, _, _]
      (by simp only [List.all_cons, List.all_nil, List.head?_cons, tl_g, tl_n, tl_x, tl_f]; rfl)
  refine frag_append (xs := [_])
    (M := RunF s0 (RL k (c + 1) 1 c nx fr base) (RepMem A s0 bytes u lo hi S kd free F 1 c fr))
    (runF_swap o (pre := []) rfl hi1 rfl (v := BitVec.ofNat 64 (c + 1)) fun w h => ev_inc (vals_mem h (by simp))) ?_
  -- the bound, then the round or nothing
  by_cases hgo : ∀ h ∈ hi, c + 1 ≤ h
  · have hstop : Frag o (repStop .none k hi) (RunF s0 (RL k (c + 1) 1 c nx fr base)
        (RepMem A s0 bytes u lo hi S kd free F 1 c fr)) (RunF s0 (RL k (c + 1) 1 c nx fr base)
        (RepMem A s0 bytes u lo hi S kd free F 1 c fr)) := by
      cases hi with
      | none => exact frag_nil o fun _ h => h
      | some h =>
        exact ScanRun.frag_if o rfl (lowK_any _ (k := .skip) rfl) lowKK_nil rfl rfl (runF_clock _ _ _)
          (b := decide (h ≤ c)) (fun w hw => FramerCode.eval_le (by have := hhi32 h rfl; omega) (by omega) rfl
            (vals_mem hw (by simp [RL]))) (fun e => absurd (of_decide_eq_true e) (by have := hgo h rfl; omega))
          fun _ => frag_nil o fun _ h => h
    refine frag_append hstop (frag_ite o rfl repI_clock (fun w h => ⟨BitVec.ofNat 64 1, vals_mem h (by simp [RL])⟩)
      (frag_conseq (rep_round o hA hcode hlen hlo hfree hbody hdE hkd hd hav hk (fun _ => hnnl) v0 rfl hib hgo hnx hfr
        hne) (fun _ h => h.1) fun _ h => h) hres (frag_unsat lowKK_nil fun w ⟨h, h0⟩ =>
          absurd ((vals_mem (v := BitVec.ofNat 64 1) h (by simp [RL])).symm.trans h0) (by decide)) (noDecl _ rfl))
  · -- the bound reached: the loop stops, what it counted all there is
    cases hi with
    | none => exact absurd (fun h hh => nomatch hh) hgo
    | some h =>
      have hch : c = h := by have := hchi h rfl; have : ¬c + 1 ≤ h := fun h' => hgo fun _ e => by cases e; exact h'
                             omega
      subst hch
      have hg1 : Fresh s!"g{k}" [(s!"i{k}", BitVec.ofNat 64 (c + 1))] = true :=
        fresh_cons (ne_heads (tl_i k) (tl_g k) (by decide)) rfl
      have hg2 : Fresh s!"g{k}" ((s!"n{k}", BitVec.ofNat 64 c) :: (s!"x{k}", BitVec.ofNat 64 nx) ::
          (s!"f{k}", BitVec.ofNat 64 fr) :: base) = true :=
        fresh_heads (tl_g k) (fresh_base (name_g k) (ne_heads (tl_g k) (tl_cb k) (by decide)) hav hk v0) [_, _, _]
          (by simp only [List.all_cons, List.all_nil, List.head?_cons, tl_n, tl_x, tl_f]; rfl)
      let P0 := RunF s0 (RL k (c + 1) 0 c nx fr base) (RepMem A s0 bytes u lo (some c) S kd free F 0 c fr)
      refine frag_append (M := P0) (ScanRun.frag_if o rfl (lowK_any _ (k := .skip) rfl) lowKK_nil rfl rfl
        (runF_clock _ _ _) (b := true) (fun w hw => (FramerCode.eval_le (x := c) (y := c)
          (by have := hhi32 c rfl; omega) (by have := hhi32 c rfl; omega) rfl
          (vals_mem hw (by simp [RL]))).trans (by rw [decide_eq_true (Nat.le_refl c)]))
        (fun _ => frag_conseq (runF_swap o (pre := [_]) hg1 hg2 rfl (v := BitVec.ofNat 64 0) fun _ _ => rfl)
          (fun _ h => h) fun w hw => runF_mono hw (fun _ hq => hq) fun m ⟨m0, hm0, hB, hK, h1, _⟩ =>
            ⟨m0, hm0, hB, hK, (fun h => nomatch h), fun _ => holds_congr (h1 rfl).1 stop_done⟩)
        fun e => nomatch e) (frag_ite o rfl repI_clock (fun w h => ⟨BitVec.ofNat 64 0, vals_mem h (by simp [RL])⟩)
          (frag_unsat (lowKK_append hlowb hlowT) fun w ⟨h, hne0⟩ => hne0 (vals_mem h (by simp [RL]))) hres
          (frag_nil o fun w ⟨h, _⟩ => ⟨c + 1, 0, c, nx, fr, h, .inl rfl, by omega, fun h => nomatch h⟩)
          (noDecl _ rfl))

theorem done_zero {input : Array Nat} {u : Abnf.Term} {lo : Nat} {S : Nat → Bool} (hz : lo = 0) (e : Nat) :
    S e = true ↔ Done input u lo S 0 e := by
  subst hz
  simp only [Done, Reach]
  exact ⟨fun h => ⟨0, Nat.le_refl _, Nat.le_refl _, e, h, .zero⟩, fun ⟨j, _, hj, x, hx, he⟩ => by
    have : j = 0 := by omega
    subst this; rw [AbnfMatch.rep_zero_iff] at he; rw [he]; exact hx⟩

theorem front_zero {input : Array Nat} {u : Abnf.Term} {lo : Nat} {S : Nat → Bool} (e : Nat) :
    S e = true ↔ Front input u lo S 0 e := by
  simp only [Front, Reach]
  exact ⟨fun h => ⟨⟨e, h, .zero⟩, fun ⟨_, _, hj, _⟩ => by omega⟩, fun ⟨⟨x, hx, he⟩, _⟩ => by
    rw [AbnfMatch.rep_zero_iff] at he; rw [he]; exact hx⟩

theorem genRep_eq {g : Gen} {s d : Syntax.PExpr} {free lo : Nat} {hi : Option Nat} {u : Abnf.Term} {k k' : Nat}
    {body : List Syntax.PStmt} (hb : g u (Syntax.v s!"f{k}") (Syntax.v s!"x{k}") (free + 2) (k + 1) = (body, k')) :
    genRep .none g s d free lo hi u k = (repStmts .none s d free lo hi k body, k') := by
  unfold genRep; rw [hb]

/-- **A repetition**: its loop, as `endsFrom` runs it, the rounds counted from `lo` to `hi`. -/
theorem rep_ok (hA : Area ofs A s0) (hcode : ProgCode s0.code ofs) (hlen : bytes.length ≤ inputMax)
    {f : Nat} {g : Gen} (hg : GenOk o ofs A s0 bytes f g) {s d : Syntax.PExpr} (hs : SlotE s)
    (hd : SlotE d) {free : Nat} (hfree : free + 2 ≤ slots) {lo : Nat} {hi : Option Nat} {u : Abnf.Term}
    (hlo : lo < 2 ^ 32) (hhi32 : ∀ h ∈ hi, h < 2 ^ 32) (hen : AbnfOrder.enough f u = true)
    (hca : ∀ j ∈ callsOf f u, BodyOk o ofs s0.code j ∧ free + 2 + needOf f u ≤ frameOf j)
    (hle : ∀ lf ∈ leavesOf f u, lf ∈ allLeaves) (hsl : free + 2 + needOf f u ≤ slots) (k : Nat) :
    Shape k (genRep .none g s d free lo hi u k) ∧
      Does o A s0 bytes true (.rep lo hi u) s d free k (genRep .none g s d free lo hi u k) := by
  obtain ⟨hsh, hdo⟩ := hg u (Syntax.v s!"f{k}") (Syntax.v s!"x{k}") (free + 2) (k + 1) hen hca hle hsl
    (.inr ⟨_, rfl⟩) (.inr ⟨_, rfl⟩)
  generalize hb : g u (Syntax.v s!"f{k}") (Syntax.v s!"x{k}") (free + 2) (k + 1) = B at hsh hdo
  obtain ⟨body, k'⟩ := B
  rw [genRep_eq hb]
  obtain ⟨Es, hEs⟩ := slotE_lower hs
  obtain ⟨Ed, hEd⟩ := slotE_lower hd
  have hk := hsh.2.1
  have hlowT := lowKK_repTail (k := k) (free := free) (lo := lo) hd
  have hlowS : LowKK (repStop .none k hi) := by cases hi <;> exact lowK_any _ (k := .skip) rfl
  have hlowB :
      LowKK (inc s!"i{k}" :: repStop .none k hi ++ [.ite (Syntax.v s!"g{k}") (body ++ repTail k free lo d) []]) :=
    lowKK_append (xs := [_] ++ _) (lowKK_append (xs := [_]) (lowK_any _ (k := .skip) rfl) hlowS)
      (lowKK_ite rfl (lowKK_append hsh.1 hlowT) lowKK_nil)
  have hlowW := lowKK_while (repCond_lower k lo) hlowB
  have hlowD : LowKK [.dec s!"f{k}" s, .dec s!"x{k}" (Syntax.n free), .dec s!"n{k}" (Syntax.n 0),
      .dec s!"g{k}" (Syntax.n 1), .dec s!"i{k}" (Syntax.n 0)] :=
    lowKK_append (xs := [_]) (lowKK_dec hEs) (lowKK_append (xs := [_]) (lowKK_dec rfl) (lowKK_append (xs := [_])
      (lowKK_dec rfl) (lowKK_append (xs := [_]) (lowKK_dec rfl) (lowKK_dec rfl))))
  have hlowC : LowKK [if lo == 0 then .call s!"{s!"c{k}"}b" "setCopy" [d, s]
      else .call s!"{s!"c{k}"}b" "setClear" [d]] := by
    split
    · exact lowKK_call (lowerArgs_two hEd hEs)
    · exact lowKK_call (a := [Ed]) (by simp [Lower.lowerArgs, hEd])
  refine ⟨⟨lowKK_append (xs := [_]) hlowC (lowKK_append (xs := [_, _, _, _, _]) hlowD hlowW), by omega,
    fun y hy => ?_⟩, ?_⟩
  · have : declared (repStmts .none s d free lo hi k body) = [s!"{s!"c{k}"}b", s!"f{k}", s!"x{k}", s!"n{k}", s!"g{k}",
        s!"i{k}"] := by unfold repStmts; split <;> rfl
    rw [this] at hy
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨k, Nat.le_refl _, by omega, name_cb k⟩
    · exact ⟨k, Nat.le_refl _, by omega, name_f k⟩
    · exact ⟨k, Nat.le_refl _, by omega, name_x k⟩
    · exact ⟨k, Nat.le_refl _, by omega, name_n k⟩
    · exact ⟨k, Nat.le_refl _, by omega, name_g k⟩
    · exact ⟨k, Nat.le_refl _, by omega, name_i k⟩
  intro l F ks kd S hS hD hks hkd hne hav hnn hF
  have hnnl := hnn rfl
  have hI := inputMax_eq
  have hkd' : kd < slots := by omega
  have hks' : ks < slots := by omega
  obtain ⟨Es', hEs', hvs⟩ := slotIs_eval (σ := σ) hS
  obtain ⟨Ed', hEd', hvd⟩ := slotIs_eval (σ := σ) hD
  have hcb : Fresh s!"{s!"c{k}"}b" l = true := fresh_of hav (Nat.le_refl _) (by omega) (name_cb k)
  let G0 : (Word → Word) → Prop := fun m' => ∃ m, F m ∧
    SetAt m' A kd (setOf (Done (inputOf bytes) u lo S 0)) ∧
    Frame A kd m m'
  have h1 : Frag o [if lo == 0 then .call s!"{s!"c{k}"}b" "setCopy" [d, s] else .call s!"{s!"c{k}"}b" "setClear" [d]]
      (RunF s0 l F) (fun w => ∃ v0, RunF s0 ((s!"{s!"c{k}"}b", v0) :: l) G0 w) := by
    by_cases hz : lo = 0
    · rw [if_pos (by simp [hz])]
      refine frag_conseq (copy_frag o hA hcode hcb hEd' hEs' hkd' hks' (Ne.symm hne) (fun w h => hvd w h.1.vals)
        (fun w h => hvs w h.1.vals) (Ss := S) fun m hm => ⟨(hF m hm).1, (hF m hm).2.1⟩) (fun _ h => h)
        fun w ⟨v0, h⟩ => ⟨v0, runF_mono h (fun _ hq => hq) fun m' ⟨m, hm, _, hS', hfr⟩ =>
          ⟨m, hm, by rw [← setOf_eq (done_zero hz)]; exact hS', hfr⟩⟩
    · rw [if_neg (by simp [hz])]
      refine frag_conseq (clear_frag o hA hcode hcb hEd' hkd' (fun w h => hvd w h.1.vals) fun m hm => (hF m hm).2.1)
        (fun _ h => h) fun w ⟨v0, h⟩ => ⟨v0, runF_mono h (fun _ hq => hq) fun m' ⟨m, hm, _, hS', hfr⟩ =>
          ⟨m, hm, by rw [← setOf_eq (T := fun _ => false) fun e =>
                       ⟨fun h => absurd h Bool.false_ne_true, fun h => absurd h (done_lt (by omega))⟩]
                     exact hS', hfr⟩⟩
  have hlowR := lowKK_append (xs := [_, _, _, _, _]) hlowD hlowW
  refine frag_append (xs := [_]) h1 (frag_exists hlowR fun v0 => ?_)
  let base := (s!"{s!"c{k}"}b", v0) :: l
  have hl : ∀ q ∈ l, q ∈ base := fun q hq => List.mem_cons_of_mem _ hq
  -- the frontier in slot `s`, the counters
  have hf : Fresh s!"f{k}" base = true :=
    fresh_base (name_f k) (ne_heads (tl_f k) (tl_cb k) (by decide)) hav (by omega) v0
  have hx : Fresh s!"x{k}" ((s!"f{k}", BitVec.ofNat 64 ks) :: base) = true :=
    fresh_cons (ne_heads (tl_f k) (tl_x k) (by decide)) (fresh_base (name_x k) (ne_heads (tl_x k) (tl_cb k) (by decide))
      hav (by omega) v0)
  have hn : Fresh s!"n{k}" ((s!"x{k}", BitVec.ofNat 64 free) :: (s!"f{k}", BitVec.ofNat 64 ks) :: base) = true :=
    fresh_cons (ne_heads (tl_x k) (tl_n k) (by decide)) (fresh_cons (ne_heads (tl_f k) (tl_n k) (by decide))
      (fresh_base (name_n k) (ne_heads (tl_n k) (tl_cb k) (by decide)) hav (by omega) v0))
  have hgn : Fresh s!"g{k}" ((s!"n{k}", BitVec.ofNat 64 0) :: (s!"x{k}", BitVec.ofNat 64 free) ::
      (s!"f{k}", BitVec.ofNat 64 ks) :: base) = true :=
    fresh_heads (tl_g k) (fresh_base (name_g k) (ne_heads (tl_g k) (tl_cb k) (by decide)) hav (by omega) v0) [_, _, _]
      (by simp only [List.all_cons, List.all_nil, List.head?_cons, tl_n, tl_x, tl_f]; rfl)
  have hin : Fresh s!"i{k}" ((s!"g{k}", BitVec.ofNat 64 1) :: (s!"n{k}", BitVec.ofNat 64 0) ::
      (s!"x{k}", BitVec.ofNat 64 free) :: (s!"f{k}", BitVec.ofNat 64 ks) :: base) = true :=
    fresh_heads (tl_i k) (fresh_base (name_i k) (ne_heads (tl_i k) (tl_cb k) (by decide)) hav (by omega) v0)
      [_, _, _, _] (by simp only [List.all_cons, List.all_nil, List.head?_cons, tl_g, tl_n, tl_x, tl_f]; rfl)
  refine frag_append (xs := [_]) (runF_dec o hEs' hf (v := BitVec.ofNat 64 ks) fun w h => hvs w fun q hq =>
    h.1.vals q (hl q hq)) (frag_append (xs := [_]) (runF_dec o rfl hx (v := BitVec.ofNat 64 free) fun _ _ => rfl)
    (frag_append (xs := [_]) (runF_dec o rfl hn (v := BitVec.ofNat 64 0) fun _ _ => rfl)
    (frag_append (xs := [_]) (runF_dec o rfl hgn (v := BitVec.ofNat 64 1) fun _ _ => rfl)
    (frag_append (xs := [_]) (runF_dec o rfl hin (v := BitVec.ofNat 64 0) fun _ _ => rfl) ?_))))
  -- the loop
  have hdef : ∀ w, RepI A s0 bytes u lo hi S kd free k F base w → ∃ v, eval w (repCond k lo) = some v :=
    fun w ⟨i, go, c, nx, fr, h, hc⟩ => ⟨_, repCond_eval h (hl _ hnnl) hc.1 (by have := hc.2.1; omega)
      (by omega)⟩
  refine frag_conseq (frag_while o (repCond_lower k lo) hlowB (I := RepI A s0 bytes u lo hi S kd free k F base)
    repI_clock (noDecl _ (by cases hi <;> rfl)) hdef (rep_iter o hA hcode hlen hlo hhi32 hfree hdo hsh.1 hsh.2.2 hd
      (by omega) hD hav (by omega) hnnl v0)) (fun w h => ?_) fun w ⟨hw, h0⟩ => ?_
  · -- the loop's start
    refine ⟨0, 1, 0, free, ks, runF_mono h (fun _ hq => hq) fun m' ⟨m, hm, hSd, hfr⟩ => ?_, .inr rfl, by omega,
      fun _ => ⟨rfl, fun h _ => Nat.zero_le h, .inl rfl, by omega, by omega⟩⟩
    refine ⟨m, hm, base_keep hA.hA hlen hkd' (hF m hm).2 (kept_frame (free := 0) (.inl rfl) hfr)
      (allSets_frame (hF m hm).2.1 hkd' hSd hfr), kept_frame (.inl rfl) hfr,
      fun _ => ⟨hSd, ?_, fun h0 => ?_⟩, fun h => nomatch h⟩
    · unfold Holds; rw [← setOf_eq front_zero]; exact setAt_other (hF m hm).1 hkd' hks' (Ne.symm hne) hfr
    · have : lo = 0 := by omega
      subst this; exact cnt_lo
  · -- the loop's end: what it counted all there is
    obtain ⟨i, go, c, nx, fr, h, hc⟩ := hw
    refine ⟨[(s!"i{k}", BitVec.ofNat 64 i), (s!"g{k}", BitVec.ofNat 64 go), (s!"n{k}", BitVec.ofNat 64 c),
      (s!"x{k}", BitVec.ofNat 64 nx), (s!"f{k}", BitVec.ofNat 64 fr), (s!"{s!"c{k}"}b", v0)], fun q hq => ?_,
      runF_mono h (fun _ hq => hq) fun m ⟨m0, hm0, hB, hK, hgo1, hgo0⟩ => ⟨m0, hm0, ?_, hB, hK⟩⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
      · exact ⟨k, Nat.le_refl _, by omega, name_i k⟩
      · exact ⟨k, Nat.le_refl _, by omega, name_g k⟩
      · exact ⟨k, Nat.le_refl _, by omega, name_n k⟩
      · exact ⟨k, Nat.le_refl _, by omega, name_x k⟩
      · exact ⟨k, Nat.le_refl _, by omega, name_f k⟩
      · exact ⟨k, Nat.le_refl _, by omega, name_cb k⟩
    rcases hc.1 with rfl | rfl
    · exact holds_congr (hgo0 rfl) target_ends
    · have hib := hc.2.1
      have := repCond_eval (lo := lo) h (hl _ hnnl) hc.1 (by omega) (by omega)
      rw [this] at h0
      have hge := FramerCode.bw_eq0 h0
      obtain ⟨hci, hchi, -⟩ := hc.2.2 rfl
      subst hci
      simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not] at hge
      have hge' : lo + (inputOf bytes).size + 1 ≤ c := by
        rw [inputOf_size]; rcases hge with h' | h'
        · exact absurd trivial h'
        · omega
      obtain ⟨hD1, -, hC⟩ := hgo1 rfl
      exact holds_congr hD1 fun e => (complete (by omega) hchi (cnt_full hge' (hC (by omega))) e).trans (target_ends e)

/-! ## `gen` by induction -/

theorem seq_one_iff {g : Array Abnf.Term} {input : Array Nat} {u : Abnf.Term} {x e : Nat} :
    Matches g input u x e ↔ Matches g input (.seq [u]) x e := by
  rw [AbnfMatch.seq_iff, AbnfMatch.seq_cons_iff]
  exact ⟨fun h => ⟨e, h, .nil⟩, fun ⟨q, h, hs⟩ => by rw [AbnfMatch.seq_nil_iff] at hs; rw [hs]; exact h⟩

theorem alt_one_iff {g : Array Abnf.Term} {input : Array Nat} {u : Abnf.Term} {x e : Nat} :
    Matches g input u x e ↔ Matches g input (.alt [u]) x e := by
  rw [AbnfMatch.alt_iff]
  exact ⟨fun h => ⟨u, List.mem_singleton_self _, h⟩, fun ⟨t, ht, h⟩ => by
    rw [List.mem_singleton] at ht; rw [← ht]; exact h⟩

theorem le_max_of_mem {L : List Abnf.Term} {f : Abnf.Term → Nat} {t : Abnf.Term} (ht : t ∈ L) :
    f t ≤ (L.map f).foldl max 0 := (le_foldl_max _ _).2 _ (List.mem_map.2 ⟨t, ht, rfl⟩)

/-- **A term that is no leaf**, each kind as `gen` writes it. -/
theorem genTerm_ok (hA : Area ofs A s0) (hcode : ProgCode s0.code ofs) (hlen : bytes.length ≤ inputMax)
    {f : Nat} {g : Gen} (hg : GenOk o ofs A s0 bytes f g) (t : Abnf.Term) (hl : leafOf t = none)
    {s d : Syntax.PExpr} (hs : SlotE s) (hd : SlotE d) (free k : Nat)
    (hen : AbnfOrder.enoughAt (AbnfOrder.enough f) none t = true)
    (hca : ∀ j ∈ callsAt (callsOf f) none t, BodyOk o ofs s0.code j ∧
      free + needAt (needOf f) none t ≤ frameOf j)
    (hle : ∀ lf ∈ leavesAt (leavesOf f) none t, lf ∈ allLeaves)
    (hsl : free + needAt (needOf f) none t ≤ slots) :
    Shape k (genTerm .none g t s d free k) ∧
      Does o A s0 bytes (repeatsAt (repeats f) none t) t s d free k (genTerm .none g t s d free k) := by
  cases t with
  | range lo hi => exact absurd hl leafOf_range
  | text s => exact absurd hl leafOf_text
  | exact s => exact absurd hl leafOf_exact
  | ref i =>
    obtain ⟨hb, hfi⟩ := hca i (List.mem_singleton_self _)
    exact ref_ok o hA hlen hb hs hd hfi hsl k _
  | seq ts =>
    cases ts with
    | nil => exact nil_ok o hA hcode hlen hs hd hsl k _
    | cons u us =>
      cases us with
      | nil =>
        have := hg u s d free k (by simpa [AbnfOrder.enoughAt] using hen)
          (fun j hj => hca j (by simpa [callsAt] using hj)) (fun lf h => hle lf (by simpa [leavesAt] using h))
          (by simpa [needAt] using hsl) hs hd
        refine ⟨this.1, does_congr o this.2 (fun e => by simpa [repeatsAt] using e) fun x e => seq_one_iff⟩
      | cons v vs =>
        have hpre : SeqPre o (ofs := ofs) f free (u :: v :: vs) s0.code := fun t ht => by
          have hn : 2 + needOf f t ≤ needAt (needOf f) none (.seq (u :: v :: vs)) :=
            Nat.add_le_add_left (le_max_of_mem ht) 2
          refine ⟨List.all_eq_true.1 (by simpa [AbnfOrder.enoughAt] using hen) t ht, fun j hj => ?_,
            fun lf h => hle lf (by simp only [leavesAt]; exact List.mem_flatMap.2 ⟨t, ht, h⟩), by omega⟩
          obtain ⟨hb, hf⟩ := hca j (by simp only [callsAt]; exact List.mem_flatMap.2 ⟨t, ht, hj⟩)
          exact ⟨hb, by omega⟩
        have hfree : free + 2 ≤ slots := by
          have : 2 ≤ needAt (needOf f) none (.seq (u :: v :: vs)) := Nat.le_add_right _ _
          omega
        obtain ⟨hsh, hdo⟩ :=
          seqFrom_ok o hA hcode hlen hg hs hd hfree (u :: v :: vs) 0 k (List.cons_ne_nil _ _) hpre
        refine ⟨hsh, fun l F ks kd S hS hD hks hkd hne hav hnn hF =>
          hdo l F ks kd S hS hD (by omega) (by omega) hkd hne
          hav (fun e => hnn (by simpa [repeatsAt] using e)) hF⟩
  | alt ts =>
    cases ts with
    | nil => exact altNil_ok o hA hcode hlen hd hsl k _
    | cons u us =>
      cases us with
      | nil =>
        have := hg u s d free k (by simpa [AbnfOrder.enoughAt] using hen)
          (fun j hj => hca j (by simpa [callsAt] using hj)) (fun lf h => hle lf (by simpa [leavesAt] using h))
          (by simpa [needAt] using hsl) hs hd
        refine ⟨this.1, does_congr o this.2 (fun e => by simpa [repeatsAt] using e) fun x e => alt_one_iff⟩
      | cons v vs =>
        have hpre : AltPre o (ofs := ofs) f free (u :: v :: vs) s0.code := fun t ht => by
          have hn : 1 + needOf f t ≤ needAt (needOf f) none (.alt (u :: v :: vs)) :=
            Nat.add_le_add_left (le_max_of_mem ht) 1
          refine ⟨List.all_eq_true.1 (by simpa [AbnfOrder.enoughAt] using hen) t ht, fun j hj => ?_,
            fun lf h => hle lf (by simp only [leavesAt]; exact List.mem_flatMap.2 ⟨t, ht, h⟩), by omega⟩
          obtain ⟨hb, hf⟩ := hca j (by simp only [callsAt]; exact List.mem_flatMap.2 ⟨t, ht, hj⟩)
          exact ⟨hb, by omega⟩
        have hfree : free + 1 ≤ slots := by
          have : 1 ≤ needAt (needOf f) none (.alt (u :: v :: vs)) := Nat.le_add_right _ _
          omega
        exact altCons_ok o hA hcode hlen hg hs hd hfree hpre k
  | rep lo hi u =>
    simp only [AbnfOrder.enoughAt, Bool.and_eq_true, decide_eq_true_eq] at hen
    obtain ⟨⟨hlo, hhi⟩, hen⟩ := hen
    have hhi32 : ∀ h ∈ hi, h < 2 ^ 32 := fun h hh => by
      cases hi with
      | none => cases hh
      | some h' => cases hh; simpa using hhi
    by_cases hopt : (lo == 0 && hi == some 1) = true
    · have e : genTerm .none g (.rep lo hi u) s d free k =
          ((g u s d free k).1 ++ [.call s!"c{(g u s d free k).2}" "setUnion" [d, s]], (g u s d free k).2 + 1) := by
        unfold genTerm; dsimp only; rw [if_pos hopt]
      rw [e]
      simp only [Bool.and_eq_true, beq_iff_eq] at hopt
      obtain ⟨rfl, rfl⟩ := hopt
      exact opt_ok o hA hcode hlen hg hs hd hen (fun j hj => hca j hj) hle hsl k
    · have e : genTerm .none g (.rep lo hi u) s d free k = genRep .none g s d free lo hi u k := by
        unfold genTerm; dsimp only; rw [if_neg hopt]
      rw [e]
      have hn : needAt (needOf f) none (.rep lo hi u) = 2 + needOf f u := by simp [needAt, hopt]
      have hr : repeatsAt (repeats f) none (.rep lo hi u) = true := by simp [repeatsAt, hopt]
      rw [hr]
      rw [hn] at hca hsl
      exact rep_ok o hA hcode hlen hg hs hd (by omega) hlo hhi32 hen
        (fun j hj => let ⟨hb, hf⟩ := hca j hj; ⟨hb, by omega⟩)
        hle (by omega) k

/-- **`gen` does what it is to**, for any steps. -/
theorem gen_ok (hA : Area ofs A s0) (hcode : ProgCode s0.code ofs) (hlen : bytes.length ≤ inputMax)
    : ∀ f, GenOk o ofs A s0 bytes f (gen .none f)
  | 0 => fun _ _ _ _ _ hen => absurd hen (by simp [AbnfOrder.enough])
  | f + 1 => fun t s d free k hen hca hle hsl hs hd => by
    rw [AbnfOrder.enough] at hen
    rw [callsOf, needOf] at hca
    rw [needOf] at hsl
    rw [leavesOf] at hle
    rw [gen, repeats]
    generalize hl : leafOf t = lf at hen hca hle hsl
    cases lf with
    | some lf =>
      exact leaf_ok o hA hcode hlen hl (hle lf (List.mem_singleton_self _)) hs hd (by simpa [needAt] using hsl) k _
    | none => exact genTerm_ok o hA hcode hlen (gen_ok hA hcode hlen f) t hl hs hd free k hen hca hle hsl

end cases

end DN.News.AbnfGen
