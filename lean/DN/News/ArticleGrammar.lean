-- SPDX-License-Identifier: AGPL-3.0-or-later
import DN.News.ArticleRun

/-!
# DN.News.ArticleGrammar

A grammar match from a place of the input is one of the input from that place on (`matches_shift`). `artGrammar`
answers whether a rule matches from `S` to `E` (`artGrammar_ok`, `gram_says`).
-/

namespace DN.News.ArticleGrammar

open DN.News.Abnf DN.News.AbnfMatch

/-- Input `inp'` is `inp` from place `s` on. -/
def Shift (s : Nat) (inp inp' : Array Nat) : Prop := ∀ p, inp[p + s]? = inp'[p]?

section
variable {g : Array Term} {inp inp' : Array Nat} {s : Nat}

theorem at_up (h : Shift s inp inp') (norm : Nat → Nat) :
    ∀ (cs : List Nat) (p : Nat), at? inp' norm p cs = at? inp norm (p + s) cs
  | [], _ => rfl
  | c :: cs, p => by
    simp only [at?]
    rw [← h p]
    cases inp[p + s]? with
    | none => rfl
    | some b => simp only; rw [at_up h norm cs (p + 1), show p + 1 + s = p + s + 1 by omega]

mutual
theorem Matches.up (h : Shift s inp inp') {t : Term} {p e : Nat} :
    Matches g inp' t p e → Matches g inp t (p + s) (e + s)
  | @Matches.range _ _ _ _ p _ hb h1 h2 => by
    rw [show p + 1 + s = p + s + 1 by omega]; exact .range (by rw [h p]; exact hb) h1 h2
  | @Matches.text _ _ cs p hat => by
    rw [show p + (codes cs).length + s = p + s + (codes cs).length by omega]
    exact .text (by rw [← at_up h]; exact hat)
  | @Matches.exact _ _ cs p hat => by
    rw [show p + cs.length + s = p + s + cs.length by omega]
    exact .exact (by rw [← at_up h]; exact hat)
  | .ref hu hm => .ref hu (Matches.up h hm)
  | .seq hs => .seq (Seq.up h hs)
  | .alt hm ht => .alt hm (Matches.up h ht)
  | .rep h1 h2 hr => .rep h1 h2 (Rep.up h hr)
theorem Seq.up (h : Shift s inp inp') {ts : List Term} {p e : Nat} :
    Seq g inp' ts p e → Seq g inp ts (p + s) (e + s)
  | .nil => .nil
  | .cons h1 h2 => .cons (Matches.up h h1) (Seq.up h h2)
theorem Rep.up (h : Shift s inp inp') {t : Term} {k p e : Nat} :
    Rep g inp' t k p e → Rep g inp t k (p + s) (e + s)
  | .zero => .zero
  | .succ h1 h2 => .succ (Matches.up h h1) (Rep.up h h2)
end

mutual
theorem Matches.down (h : Shift s inp inp') {t : Term} {p e : Nat} (hp : s ≤ p) :
    Matches g inp t p e → Matches g inp' t (p - s) (e - s)
  | @Matches.range _ _ _ _ p _ hb h1 h2 => by
    rw [show p + 1 - s = p - s + 1 by omega]
    exact .range (by rw [← h (p - s), Nat.sub_add_cancel hp]; exact hb) h1 h2
  | @Matches.text _ _ cs p hat => by
    rw [show p + (codes cs).length - s = p - s + (codes cs).length by omega]
    exact .text (by rw [at_up h, Nat.sub_add_cancel hp]; exact hat)
  | @Matches.exact _ _ cs p hat => by
    rw [show p + cs.length - s = p - s + cs.length by omega]
    exact .exact (by rw [at_up h, Nat.sub_add_cancel hp]; exact hat)
  | .ref hu hm => .ref hu (Matches.down h hp hm)
  | .seq hs => .seq (Seq.down h hp hs)
  | .alt hm ht => .alt hm (Matches.down h hp ht)
  | .rep h1 h2 hr => .rep h1 h2 (Rep.down h hp hr)
theorem Seq.down (h : Shift s inp inp') {ts : List Term} {p e : Nat} (hp : s ≤ p) :
    Seq g inp ts p e → Seq g inp' ts (p - s) (e - s)
  | .nil => .nil
  | .cons h1 h2 => .cons (Matches.down h hp h1) (Seq.down h (Nat.le_trans hp (Matches.le h1)) h2)
theorem Rep.down (h : Shift s inp inp') {t : Term} {k p e : Nat} (hp : s ≤ p) :
    Rep g inp t k p e → Rep g inp' t k (p - s) (e - s)
  | .zero => .zero
  | .succ h1 h2 => .succ (Matches.down h hp h1) (Rep.down h (Nat.le_trans hp (Matches.le h1)) h2)
end

/-- **A match from a place is a match of the input from there on.** -/
theorem matches_shift (h : Shift s inp inp') {t : Term} {p e : Nat} :
    Matches g inp t (p + s) (e + s) ↔ Matches g inp' t p e :=
  ⟨fun hm => by have := Matches.down h (Nat.le_add_left _ _) hm; simpa using this, Matches.up h⟩

end

/-! ## The program's grammar calls -/

open DN.Compiler DN.Compiler.Wp DN.Compiler.WpRet DN.Compiler.Frag DN.News.AbnfProg DN.News.AbnfLayout
open DN.News.AbnfSets DN.News.FunRun DN.News.AbnfLeaves DN.News.AbnfGen DN.News.AbnfMain DN.News.ArticleRun
open DN.News.AbnfRun (bodies_ok)
open DN.News.ScanRun (at_ at_add at_inj Vals vals_lookup Fresh without lookup_head fresh_cons)
open DN.News.ArticleLines (seg)
open DN.News.FramerCode (bw ev_var bw_ne0 bw_eq0)
open DN.News.ArticleProg (guardL guardS)
open DN.News.ArticleSpec (Bytes)

variable {σ : Type}

theorem guardL_append : ∀ (xs ys : List Syntax.PStmt), guardL (xs ++ ys) = guardL xs ++ guardL ys
  | [], _ => rfl
  | x :: xs, ys => by
    show guardS x ++ guardL (xs ++ ys) = (guardS x ++ guardL xs) ++ guardL ys
    rw [guardL_append xs ys, List.append_assoc]

theorem guardS_rootCall (i : Nat) : guardS (rootCall i) = [rootCall i, brk] := by
  unfold rootCall
  split
  · rfl
  · split
    · rename_i l _; cases l <;> rfl
    · rfl

/-- A branch to rule `i`'s call, as the article's program asks it. -/
def apick (i : Nat) : Syntax.PStmt := ArticleProg.ifs (Syntax.eEq (Syntax.v "rule") (Syntax.n i)) [rootCall i, brk]

theorem guardL_picks : ∀ L : List Nat,
    guardL (L.map fun i => ArticleProg.ifs (Syntax.eEq (Syntax.v "rule") (Syntax.n i)) [rootCall i]) = L.map apick
  | [] => rfl
  | i :: L => by
    show guardS (Syntax.PStmt.ite _ [rootCall i] []) ++ guardL _ = _
    rw [guardL_picks L]
    show [Syntax.PStmt.ite _ (guardS (rootCall i) ++ guardL []) (guardL [])] ++ _ = _
    rw [guardS_rootCall]; rfl

theorem artGrammar_guarded : guardL ArticleProg.artGrammar.body =
    [areaAt ArticleProg.ofs, kept "s" inputMax, kept "e" inputMax, ArticleProg.setW aLen (Syntax.v "e"),
     .call "z" "setClear" [Syntax.n 0], brk, .call "z1" "setClear" [Syntax.n 1], brk,
     .call "u" "setAdd" [Syntax.n 0, Syntax.v "s"], brk] ++ ArticleProg.usedRules.map apick ++
    [.call "h" "setHas" [Syntax.n 1, Syntax.v "e"], brk, .ret (Syntax.v "h")] := by
  show guardL (_ ++ _ ++ _) = _
  rw [guardL_append, guardL_append, guardL_picks]; rfl

/-- The code of the article's program holds the grammar's functions too. -/
theorem artCode_prog {code : String → Option (List String × PancakeProg)} (h : ArtCode code) :
    ProgCode code ArticleProg.ofs := fun f hf => h f (List.mem_append_left _ hf)

/-- What the grammar's calls keep: what they take for input `bytes`, and every word outside the slots as in `M1`. -/
def GramMem (s0 : PancakeState σ) (A : Word) (bytes : Bytes) (M1 m : Word → Word) : Prop :=
  Base s0 A bytes m ∧ Kept A 0 0 M1 m

section gram
variable {s0 : PancakeState σ} {A : Word} {bytes : Bytes} {M1 m m' : Word → Word}

theorem broken_low : aBroken < aSets := DN.News.AbnfMain.head_low (by rw [aInput_eq]; decide)

theorem gramMem_broken (h : GramMem s0 A bytes M1 m) : m (at_ A aBroken) = M1 (at_ A aBroken) :=
  kept_low (by have := slots_two; omega) h.2 broken_low

theorem gramMem_frame (hA8 : A.toNat % 8 = 0) (hlen : bytes.length ≤ inputMax) {k : Nat} (hk : k < slots)
    {T : Nat → Bool} (h : GramMem s0 A bytes M1 m) (hT : SetAt m' A k T) (hf : Frame A k m m') :
    GramMem s0 A bytes M1 m' :=
  ⟨base_keep hA8 hlen hk h.1 (kept_frame (free := 0) (.inl rfl) hf) (allSets_frame h.1.1 hk hT hf),
    kept_trans h.2 (kept_frame (.inr ⟨Nat.zero_le _, hk⟩) hf)⟩

end gram

/-- **Rule `R` called** from slot 0 into slot 1: its function or its leaf. Only slots change. -/
theorem rootR_frag (o : Oracle σ) {A : Word} {s0 : PancakeState σ} (hA : Area ArticleProg.ofs A s0)
    (hcode : ProgCode s0.code ArticleProg.ofs) {bytes : List (BitVec 8)} (hlen : bytes.length ≤ inputMax) {R : Nat}
    (hr : R < AbnfRules.grammar.size) {l : List (String × Value)} (hc : Fresh "c" l = true) {S0 : Nat → Bool}
    {M1 : Word → Word} :
    Frag o [rootCall R] (RunF s0 l fun m => GramMem s0 A bytes M1 m ∧ SetAt m A 0 S0)
      (RunF s0 l fun m => GramMem s0 A bytes M1 m ∧ Holds A m 1 (Ends bytes (.ref R) S0)) := by
  have h0 : 0 < slots := by have := slots_two; omega
  have h1 : 1 < slots := by have := slots_two; omega
  unfold rootCall
  by_cases hf : hasFun R = true
  · rw [if_pos hf]
    have hi := order_has hr hf
    obtain ⟨-, hroots, -, -⟩ := order_all hi
    have hroots' : 2 ≤ frameOf R := hroots
    refine frag_conseq (ruleCall_frag o hA (rt := "c") hc (bodies_ok o hcode R hi) (e1 := Syntax.n 0)
      (e2 := Syntax.n 1) rfl rfl (by omega) (by omega) (by decide) (fun _ _ => rfl) (fun _ _ => rfl) hlen
      fun m hm => ⟨hm.2, hm.1.1⟩) (fun _ h => h) fun w ⟨v, h⟩ =>
        runF_mono h (fun q hq => List.mem_cons_of_mem _ hq)
        fun m' ⟨m, hm, _, hH, hall, hK⟩ => ⟨⟨base_keep hA.hA hlen h1 hm.1.1 hK hall,
          kept_trans hm.1.2 (kept_wide (Nat.zero_le _) (.inr ⟨Nat.zero_le _, h1⟩) hK)⟩, hH⟩
  · rw [if_neg hf]
    have hf' : hasFun R = false := by simpa using hf
    obtain ⟨lf, hl⟩ : ∃ lf, leafOf (termOf R) = some lf := by
      unfold hasFun at hf'; simp only [Bool.or_eq_false_iff, beq_eq_false_iff_ne, Option.isNone_eq_false_iff,
        Option.isSome_iff_exists] at hf'
      exact hf'.2
    rw [hl]
    have hlf := leaf_rule hr hf' hl
    have post : ∀ T : Nat → Bool, (∀ e, T e = true ↔ Ends bytes (termOf R) S0 e) →
        ∀ w : PancakeState σ, (∃ v, RunF s0 (("c", v) :: l) (fun m' => ∃ m,
          (GramMem s0 A bytes M1 m ∧ SetAt m A 0 S0) ∧ LeafRet A 1 T m v m') w) →
        RunF s0 l (fun m => GramMem s0 A bytes M1 m ∧ Holds A m 1 (Ends bytes (.ref R) S0)) w :=
      fun T hT w ⟨v, h⟩ => runF_mono h (fun q hq => List.mem_cons_of_mem _ hq) fun m' ⟨m, hm, _, hS1, hfr⟩ =>
        ⟨gramMem_frame hA.hA hlen h1 hm.1 hS1 hfr, by
            unfold Holds; rw [← setOf_eq fun e => (hT e).trans (ends_ref hr e)]; exact hS1⟩
    rcases leafOf_some hl with ⟨rs, hrs, rfl⟩ | ⟨bs, c, hbs, rfl⟩
    · have hidx := class_idx hlf
      exact frag_conseq (class_frag o hA hcode hc rfl rfl h0 h1 (by decide) (List.getElem?_eq_some_iff.1 hidx).1
        (fun _ _ => rfl) (fun _ _ => rfl) hlen fun m hm => ⟨hm.2, hm.1.1⟩) (fun _ h => h)
        (post _ fun e => classSet_iff hrs hidx hlen e)
    · have hidx := text_idx hlf
      exact frag_conseq (text_frag o hA hcode hc rfl rfl h0 h1 (by decide) (List.getElem?_eq_some_iff.1 hidx).1
        (fun _ _ => rfl) (fun _ _ => rfl) hlen fun m hm => ⟨hm.2, hm.1.1⟩) (fun _ h => h)
        (post _ fun e => textSet_iff hbs hidx hlen e)

/-- **The check after a call** passes with the failed flag clear. -/
theorem brk_frag (o : Oracle σ) {A : Word} {s0 : PancakeState σ} (hA : Area ArticleProg.ofs A s0) {P : Assn σ}
    (hP : Safe.ClockFree P) (h : ∀ u, P u → u.locals "a" = some A ∧ u.memaddrs = s0.memaddrs ∧
      u.memory (at_ A aBroken) = 0) : Frag o [brk] P P :=
  frag_skip o broken_lower (lowKK_ret rfl) hP (fun u hu => by
    obtain ⟨ha, hm, h0⟩ := h u hu
    have hb : aBroken < aSets + slots * setSize := Nat.lt_of_lt_of_le broken_low (Nat.le_add_right _ _)
    rw [load_eval hA hm (y := aBroken) hb (by decide) (by simp only [eval, ha]; rfl), h0]) (noDecl _ rfl)

theorem lowKK_pick (i : Nat) : LowKK [rootCall i, brk] :=
  lowKK_append (xs := [rootCall i]) (lowKK_rootCall i) (lowK_any [brk] (k := .skip) rfl)

theorem pick_decl (i : Nat) : declared [rootCall i, brk] = ["c"] := by
  rw [show [rootCall i, brk] = [rootCall i] ++ [brk] from rfl, declared_append, rootCall_decl]; rfl

section picks
variable (o : Oracle σ) {R : Nat}

theorem rule_eval {w : PancakeState σ} {i : Nat} (hR : R < 2 ^ 64) (hi : i < 2 ^ 64)
    (h : eval w (.var "rule") = some (BitVec.ofNat 64 R)) :
    eval w (.cmp .equal (.var "rule") (.const (BitVec.ofNat 64 i))) = some (bw (decide (R = i))) :=
  FramerCode.eval_eq hR hi h rfl

/-- The branches of other rules than `R` pass. -/
theorem apicks_skip (hR : R < 2 ^ 64) {X : Assn σ} (hX : Safe.ClockFree X)
    (hXr : ∀ w, X w → eval w (.var "rule") = some (BitVec.ofNat 64 R))
    (hXc : ∀ w y v, X w → y = "c" → X (restore w y v)) :
    ∀ L : List Nat, R ∉ L → (∀ i ∈ L, i < 2 ^ 64) → Frag o (L.map apick) X X
  | [], _, _ => frag_nil o fun _ h => h
  | i :: L, hn, hb =>
    frag_append (xs := [_]) (frag_skip o rfl (lowKK_pick i) hX (fun w h => by
        rw [rule_eval hR (hb i List.mem_cons_self) (hXr w h)]
        rw [decide_eq_false (fun e => hn (by rw [e]; exact List.mem_cons_self))]; rfl)
      fun w y v h hy => hXc w y v h (by rw [pick_decl] at hy; simpa using hy))
      (apicks_skip hR hX hXr hXc L (fun h => hn (List.mem_cons_of_mem _ h)) fun j hj =>
        hb j (List.mem_cons_of_mem _ hj))

/-- **The branches**: the one of rule `R` calls it, the others pass. -/
theorem apicks_frag (hR : R < 2 ^ 64) {P Q : Assn σ} (hP : Safe.ClockFree P) (hQ : Safe.ClockFree Q)
    (hPr : ∀ w, P w → eval w (.var "rule") = some (BitVec.ofNat 64 R))
    (hQr : ∀ w, Q w → eval w (.var "rule") = some (BitVec.ofNat 64 R))
    (hPc : ∀ w y v, P w → y = "c" → P (restore w y v)) (hQc : ∀ w y v, Q w → y = "c" → Q (restore w y v))
    (hcall : Frag o [rootCall R, brk] P Q) :
    ∀ L : List Nat, L.Nodup → R ∈ L → (∀ i ∈ L, i < 2 ^ 64) → Frag o (L.map apick) P Q
  | [], _, hm, _ => nomatch hm
  | i :: L, hnd, hm, hb => by
    have hi := hb i List.mem_cons_self
    by_cases e : i = R
    · subst e
      refine frag_append (xs := [_]) (frag_ite o rfl hQ (fun w h => ⟨_, rule_eval hR hi (hPr w h)⟩)
        (frag_conseq hcall (fun _ h => h.1) fun _ h => h) (fun w y v h hy => hQc w y v h (by
          rw [pick_decl] at hy; simpa using hy))
        (frag_unsat lowKK_nil fun w ⟨h, h0⟩ => by rw [rule_eval hR hi (hPr w h)] at h0; simp [bw] at h0)
        (noDecl _ rfl)) (apicks_skip o hR hQ hQr hQc L (List.nodup_cons.1 hnd).1 fun j hj => hb j
          (List.mem_cons_of_mem _ hj))
    · refine frag_append (xs := [_]) (frag_skip o rfl (lowKK_pick i) hP (fun w h => by
          rw [rule_eval hR hi (hPr w h), decide_eq_false (Ne.symm e)]; rfl)
        fun w y v h hy => hPc w y v h (by rw [pick_decl] at hy; simpa using hy)) ?_
      exact apicks_frag hR hP hQ hPr hQr hPc hQc hcall L (List.nodup_cons.1 hnd).2
        ((List.mem_cons.1 hm).resolve_left (Ne.symm e)) fun j hj => hb j (List.mem_cons_of_mem _ hj)

end picks

theorem usedRules_ok : ArticleProg.usedRules.Nodup ∧ ∀ i ∈ ArticleProg.usedRules, i < AbnfRules.grammar.size := by
  decide +kernel

/-- What `artGrammar` gives back: 1 if rule `R` matches the input from `S` to `E`. The input's length word holds `E`,
and only slots changed besides. -/
def GramRet (s0 : PancakeState σ) (A : Word) (a : Bytes) (R S E : Nat) (m0 : Word → Word) : Ret := fun v m =>
  GramMem s0 A (a.take E) (upd m0 (at_ A aLen) (BitVec.ofNat 64 E)) m ∧
    v = bw (setOf (Matches AbnfRules.grammar (inputOf (a.take E)) (.ref R) S) E)

theorem reads_take {s0 : PancakeState σ} {A : Word} {a : Bytes} {m : Word → Word} (h : Reads s0 A a m) (E : Nat) :
    Reads s0 A (a.take E) m :=
  ⟨fun x hx => by
    have hx' : x < a.length := by rw [List.length_take] at hx; omega
    rw [getElem!_pos (a.take E) x hx, List.getElem_take, ← getElem!_pos a x hx']; exact h.input x hx',
   h.pows, h.masks, h.classes, h.texts⟩

theorem len_ne {A : Word} {x : Nat} (hx : aInput ≤ x) (hx' : x < aSets) : at_ A x ≠ at_ A aLen := fun e => by
  have := at_inj (by have := aSets_le; omega) (by decide) e
  rw [aInput_eq] at hx; simp only [aLen] at this; omega

theorem ends_one {bytes : Bytes} {t : Abnf.Term} {S : Nat} (e : Nat) :
    Ends bytes t (fun x => false || x == S) e ↔ Matches AbnfRules.grammar (inputOf bytes) t S e :=
  ⟨fun ⟨x, hx, hm⟩ => by simp only [Bool.false_or, beq_iff_eq] at hx; subst hx; exact hm,
   fun hm => ⟨S, by simp, hm⟩⟩

/-- **The grammar's answer** from `S` to `E` is what `matches?` says of those bytes alone, when it answers. -/
theorem gram_says {a : Bytes} {R S E depth : Nat} {b : Bool} (hSE : S ≤ E) (hEa : E ≤ a.length)
    (h : Abnf.matches? AbnfRules.grammar depth R ((seg a S E).map BitVec.toNat) = .ok b) :
    setOf (Matches AbnfRules.grammar (inputOf (a.take E)) (.ref R) S) E = b := by
  have hm := AbnfEnds.matches?_ok h
  have hin : ((seg a S E).map BitVec.toNat).toArray = inputOf (seg a S E) := rfl
  have hsl : (seg a S E).length = E - S := by simp only [seg, List.length_take, List.length_drop]; omega
  rw [hin, List.length_map, hsl] at hm
  have hsh : Shift S (inputOf (a.take E)) (inputOf (seg a S E)) := fun p => by
    simp only [inputOf, seg, List.getElem?_toArray, List.getElem?_map, List.getElem?_take, List.getElem?_drop]
    rw [Nat.add_comm S p]
    by_cases hp : p < E - S
    · rw [if_pos (by omega), if_pos hp]
    · rw [if_neg (by omega), if_neg hp]
  have e : Matches AbnfRules.grammar (inputOf (a.take E)) (.ref R) S E ↔
      Matches AbnfRules.grammar (inputOf (seg a S E)) (.ref R) 0 (E - S) := by
    have := matches_shift (g := AbnfRules.grammar) (t := .ref R) (p := 0) (e := E - S) hsh
    rwa [Nat.zero_add, Nat.sub_add_cancel hSE] at this
  cases b
  · exact setOf_false fun hM => absurd (hm.2 (e.1 hM)) (by decide)
  · exact setOf_iff.2 (e.2 (hm.1 rfl))

/-- **`artGrammar` answers whether rule `R` matches** the input from `S` to `E`, if it returns. The area holds what the
grammar reads and a set in each slot; `R` is one the article's program asks. -/
theorem artGrammar_ok (o : Oracle σ) {A : Word} {s1 : PancakeState σ} (hA : Area ArticleProg.ofs A s1)
    (hcode : ArtCode s1.code) {a : Bytes} (hR : Reads s1 A a s1.memory) (hall : AllSets A s1.memory)
    (hb : s1.memory (at_ A aBroken) = 0) {R S E : Nat} (hRu : R ∈ ArticleProg.usedRules) (hS : S ≤ inputMax)
    (hE : E ≤ inputMax) (hEa : E ≤ a.length) (hr : s1.locals "rule" = some (BitVec.ofNat 64 R))
    (hs : s1.locals "s" = some (BitVec.ofNat 64 S)) (he : s1.locals "e" = some (BitVec.ofNat 64 E)) :
    ∃ body, Lower.lower (gd ArticleProg.artGrammar) = some body ∧
      SafeR o (fun s => s = s1) body (GramRet s1 A a R S E s1.memory) fun _ => False := by
  have h0 : 0 < slots := by have := slots_two; omega
  have h1 : 1 < slots := by have := slots_two; omega
  have hIM := inputMax_eq
  have hpc := artCode_prog hcode
  have hRg := usedRules_ok.2 R hRu
  have hR64 : R < 2 ^ 64 := by have := size_lt; omega
  have hlen : (a.take E).length ≤ inputMax := by rw [List.length_take]; omega
  have hY : (BitVec.ofNat 64 S).toNat = S := by rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  have hbl : at_ A aBroken ≠ at_ A aLen := fun e => by
    have := at_inj (by decide) (by decide) e; simp only [aBroken, aLen] at this; omega
  generalize hM1 : upd s1.memory (at_ A aLen) (BitVec.ofNat 64 E) = M1
  have hM1b : M1 (at_ A aBroken) = 0 := by rw [← hM1, upd_ne _ hbl]; exact hb
  have hG1 : GramMem s1 A (a.take E) M1 M1 := by
    refine ⟨⟨fun k hk => ?_, ?_, ?_⟩, kept_refl _⟩
    · obtain ⟨T, hT⟩ := hall k hk
      exact ⟨T, setAt_frame hT fun i hi => by
        rw [← hM1]; exact upd_ne _ fun e => notInSlot hk aLen_low ⟨i, hi, e.symm⟩⟩
    · rw [← hM1, upd_eq, List.length_take, Nat.min_eq_left hEa]
    · exact reads_keep_low hA.hA hlen (reads_take hR E) fun x hx hx' => by
        rw [← hM1]; exact upd_ne _ (len_ne hx hx')
  have hbrk : ∀ {l : List (String × Value)} {F : (Word → Word) → Prop}, l.lookup "a" = some A →
      (∀ m, F m → GramMem s1 A (a.take E) M1 m) → Frag o [brk] (RunF s1 l F) (RunF s1 l F) :=
    fun hla hF => brk_frag o hA (runF_clock _ _ _) fun u h =>
      ⟨vals_lookup h.1.vals hla, h.1.memaddrs, (gramMem_broken (hF _ h.2)).trans hM1b⟩
  refine body_of ?_
  show FragR o _ (guardL ArticleProg.artGrammar.body) _ _
  rw [artGrammar_guarded]
  obtain ⟨EA, hEA⟩ := atOff_lower ArticleProg.ofs
  let L0 : List (String × Value) :=
    [("a", A), ("rule", BitVec.ofNat 64 R), ("s", BitVec.ofNat 64 S), ("e", BitVec.ofNat 64 E)]
  let L3 : List (String × Value) := ("u", 0) :: ("z1", 0) :: ("z", 0) :: L0
  let S0 : Nat → Bool := fun x => false || x == S
  refine fragR_conseq (P0 := RunF s1 [("rule", BitVec.ofNat 64 R), ("s", BitVec.ofNat 64 S),
    ("e", BitVec.ofNat 64 E)] (· = s1.memory)) ?_ (entry_run (fun q hq => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl
      · exact hr
      · exact hs
      · exact he) rfl) fun _ h => h
  refine fragR_append (xs := [_]) (fragR_of (runF_dec o hEA rfl (v := A) fun u h => areaAt_eval hA h.1.base hEA)) ?_
  refine fragR_append (xs := [_]) (fragR_of (kept_frag o (by decide) (runF_clock _ _ _) fun u h =>
    ⟨S, vals_lookup h.1.vals rfl, hS⟩)) ?_
  refine fragR_append (xs := [_]) (fragR_of (kept_frag o (by decide) (runF_clock _ _ _) fun u h =>
    ⟨E, vals_lookup h.1.vals rfl, hE⟩)) ?_
  refine fragR_append (xs := [_]) (fragR_of (runF_store o hA (G := GramMem s1 A (a.take E) M1) rfl rfl (y := aLen)
    (Nat.lt_of_lt_of_le aLen_low (Nat.le_add_right _ _)) (by decide) (fun u h => by
      have ha : u.locals "a" = some A := vals_lookup h.1.vals rfl
      simp only [eval, ha]; rfl) (val := fun _ => BitVec.ofNat 64 E) (fun u h => ev_var (vals_lookup h.1.vals rfl))
    fun m hm => by
      subst hm; show GramMem s1 A (a.take E) M1 (upd s1.memory (at_ A aLen) (BitVec.ofNat 64 E)); rw [hM1]
      exact hG1)) ?_
  -- slot 0 holds the start alone
  refine fragR_append (xs := [_]) (fragR_of (frag_conseq (clear_frag o hA hpc (rt := "z") rfl (e1 := Syntax.n 0)
    rfl h0 (fun _ _ => rfl) fun m hm => hm.1.1) (fun _ h => h)
    (P' := RunF s1 (("z", 0) :: L0) fun m => GramMem s1 A (a.take E) M1 m ∧ SetAt m A 0 fun _ => false)
    fun w ⟨v, h⟩ => by
      obtain ⟨m, hm, hv, hT, hf⟩ := h.2
      subst hv; exact ⟨h.1, gramMem_frame hA.hA hlen h0 hm hT hf, hT⟩)) ?_
  refine fragR_append (xs := [_]) (fragR_of (hbrk rfl fun _ h => h.1)) ?_
  refine fragR_append (xs := [_]) (fragR_of (frag_conseq (clear_frag o hA hpc (rt := "z1") rfl (e1 := Syntax.n 1)
    rfl h1 (fun _ _ => rfl) fun m hm => hm.1.1.1) (fun _ h => h)
    (P' := RunF s1 (("z1", 0) :: ("z", 0) :: L0) fun m => GramMem s1 A (a.take E) M1 m ∧ SetAt m A 0 fun _ => false)
    fun w ⟨v, h⟩ => by
      obtain ⟨m, hm, hv, hT, hf⟩ := h.2
      subst hv; exact ⟨h.1, gramMem_frame hA.hA hlen h1 hm.1 hT hf, setAt_other hm.2 h1 h0 (by decide) hf⟩)) ?_
  refine fragR_append (xs := [_]) (fragR_of (hbrk rfl fun _ h => h.1)) ?_
  refine fragR_append (xs := [_]) (fragR_of (frag_conseq (add_frag o hA hpc (rt := "u") rfl (e1 := Syntax.n 0)
    (e2 := Syntax.v "s") rfl rfl h0 (fun _ _ => rfl) (Y := BitVec.ofNat 64 S)
    (fun u h => ev_var (vals_lookup h.1.vals rfl)) fun m hm => ⟨hm.2, hm.1.1.2.2.pows⟩) (fun _ h => h)
    (P' := RunF s1 L3 fun m => GramMem s1 A (a.take E) M1 m ∧ SetAt m A 0 S0)
    fun w ⟨v, h⟩ => by
      obtain ⟨m, hm, hr⟩ := h.2
      rcases hr with ⟨-, hv, hT, hf⟩ | ⟨hgt, -, -⟩
      · subst hv; rw [hY] at hT; exact ⟨h.1, gramMem_frame hA.hA hlen h0 hm.1 hT hf, hT⟩
      · rw [hY] at hgt; omega)) ?_
  refine fragR_append (xs := [_]) (fragR_of (hbrk rfl fun _ h => h.1)) ?_
  -- the rule's call
  refine fragR_append (xs := ArticleProg.usedRules.map apick) (fragR_of (apicks_frag o hR64 (runF_clock _ _ _)
    (Q := RunF s1 L3 fun m => GramMem s1 A (a.take E) M1 m ∧ Holds A m 1 (Ends (a.take E) (.ref R) S0))
    (runF_clock _ _ _) (fun w h => ev_var (vals_lookup h.1.vals rfl)) (fun w h => ev_var (vals_lookup h.1.vals rfl))
    (fun w y v h hy => by subst hy; exact runF_restore h rfl v)
    (fun w y v h hy => by subst hy; exact runF_restore h rfl v)
    (frag_append (xs := [_]) (rootR_frag o hA hpc hlen hRg (l := L3) rfl) (hbrk rfl fun _ h => h.1))
    _ usedRules_ok.1 hRu fun i hi => by have := usedRules_ok.2 i hi; have := size_lt; omega)) ?_
  -- the answer
  refine fragR_append (xs := [_]) (fragR_of (has_frag o hA hpc (rt := "h") rfl (e1 := Syntax.n 1) (e2 := Syntax.v "e")
    rfl rfl h1 hE (fun _ _ => rfl) (fun u h => ev_var (vals_lookup h.1.vals rfl))
    (S := setOf (Ends (a.take E) (.ref R) S0)) fun m hm => ⟨hm.2, hm.1.1.2.2.pows⟩)) ?_
  refine fragR_append (xs := [_]) (fragR_of (brk_frag o hA (fun u k ⟨v, h⟩ => ⟨v, runF_clock _ _ _ u k h⟩)
    fun u ⟨v, h⟩ => ⟨vals_lookup h.1.vals rfl, h.1.memaddrs, by
      obtain ⟨m, hm, hm', -⟩ := h.2; rw [hm']; exact (gramMem_broken hm.1).trans hM1b⟩)) ?_
  refine fragR_ret o rfl fun u ⟨v, h⟩ => ⟨v, ev_var (vals_lookup h.1.vals rfl), ?_⟩
  obtain ⟨m, hm, hm', hv⟩ := h.2
  show GramMem s1 A (a.take E) (upd s1.memory (at_ A aLen) (BitVec.ofNat 64 E)) u.memory ∧ _
  rw [hM1, hm', hv, show setOf (Ends (a.take E) (.ref R) S0) = setOf (Matches AbnfRules.grammar
    (inputOf (a.take E)) (.ref R) S) from congrArg setOf (funext fun e => propext (ends_one e))]
  exact ⟨hm.1, rfl⟩

/-! ## Witnesses: each premise can hold -/

theorem shift_witness : Shift 0 #[] #[] := fun _ => rfl

theorem gramMem_witness : GramMem (bareState ()) 0 [] DN.News.AbnfMain.baseMem DN.News.AbnfMain.baseMem :=
  ⟨DN.News.AbnfMain.base_witness, kept_refl _⟩

end DN.News.ArticleGrammar
