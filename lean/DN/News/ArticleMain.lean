-- SPDX-License-Identifier: AGPL-3.0-or-later
import DN.News.ArticleContext

/-!
# DN.News.ArticleMain

A round of `main` answers a request in `xVerdict`, by its mode (`round_ok`). `dn_next` writes only below `xFirst`
(`next_frag`); a round keeps the entries' tables (`roundRet_hi`, `tables_kept`).
-/

namespace DN.News.ArticleMain

open DN.News.ArticleSpec (Bytes)
open DN.Compiler DN.Compiler.Wp DN.Compiler.WpRet DN.Compiler.Frag DN.News.AbnfProg
open DN.News.AbnfSets DN.News.FunRun DN.News.AbnfLeaves DN.News.ArticleRun
open DN.News.ScanRun (at_ vals_lookup Fresh fresh_cons lookup_cons_ne lookup_head)
open DN.News.ArticleProg (artMax ifs wd)
open DN.News.FramerCode (bw ev_var)
open DN.News.AbnfGen (AllSets vals_mem)
open DN.News.ArticleTables (esP esP_size)
open DN.News.ScanRun (without)

variable {σ : Type}

/-! ## `dn_next` -/

/-- **A word no written byte lies in** is kept by `writeByteArray`. -/
theorem write_keep (dm : Word → Bool) (be : Bool) {x : Word} :
    ∀ (bs : List (BitVec 8)) (p : Word) (m : Word → Word),
      (∀ j, j < bs.length → byteAlign (p + BitVec.ofNat 64 j) ≠ x) → writeByteArray dm be p bs m x = m x
  | [], _, _, _ => rfl
  | _ :: bs, p, m, h => by
    have h0 : byteAlign p ≠ x := by simpa using h 0 (by simp)
    have ih := write_keep dm be bs (p + 1) m fun j hj => by
      have := h (j + 1) (by simp; omega)
      rwa [DN.Compiler.Bytes.addr_succ] at this
    unfold writeByteArray memStoreByte
    cases hd : dm (byteAlign p)
    · rfl
    · simp only [if_true]; rw [if_neg (Ne.symm h0)]; exact ih

/-- The bytes below `xFirst` lie in addressable words. -/
theorem low_dom {A : Word} {s0 : PancakeState σ} (hA : Area ArticleProg.ofs A s0) (hD : ArtDom A s0.memaddrs)
    {j : Nat} (hj : j < ArticleProg.xFirst) : s0.memaddrs (byteAlign (A + BitVec.ofNat 64 j)) = true := by
  rw [show A + BitVec.ofNat 64 j = at_ A j from rfl, DN.News.ScanRun.align_at hA.hA]
  by_cases h : j / 8 * 8 < aSets
  · exact hA.dom _ (by omega) (by omega)
  · exact hD _ (by omega) (by omega) (by omega)

/-- **`dn_next` writes only below `xFirst`**: the words from there on are kept, and the locals. -/
theorem next_frag (o : Oracle σ) {A : Word} {s0 : PancakeState σ} (hA : Area ArticleProg.ofs A s0)
    (hD : ArtDom A s0.memaddrs) {l : List (String × Value)} (hla : l.lookup "a" = some A) {M : Word → Word} :
    Frag o [.ffi "dn_next" [Syntax.v "a", Syntax.n 8, Syntax.v "a", Syntax.n ArticleProg.xFirst]] (RunF s0 l (· = M))
      (fun u => ∃ M', RunF s0 l (· = M') u ∧
        ∀ y, ArticleProg.xFirst ≤ y → y < 2 ^ 64 → M' (at_ A y) = M (at_ A y)) := by
  have hF : ArticleProg.xFirst < 2 ^ 64 := by have := xFirst_eq; omega
  refine frag_one (a := .extCall "dn_next" (.var "a") (.const (BitVec.ofNat 64 8)) (.var "a")
    (.const (BitVec.ofNat 64 ArticleProg.xFirst))) rfl rfl rfl
    (fun _ _ ⟨M', h, hk⟩ => ⟨M', runF_clock _ _ _ _ _ h, hk⟩) (Safe.extCall fun s hs => ?_)
  have ha : eval s (.var "a") = some A := vals_lookup hs.1.vals hla
  obtain ⟨conf, hc, -⟩ := DN.Compiler.Bytes.readByteArray_some (m := s.memory) (dm := s.memaddrs) (be := s.be) A 8
    fun j hj => by
    rw [hs.1.memaddrs]; exact low_dom hA hD (by have := xFirst_eq; omega)
  obtain ⟨arr, harr, -⟩ := DN.Compiler.Bytes.readByteArray_some (m := s.memory) (dm := s.memaddrs) (be := s.be) A
    ArticleProg.xFirst fun j hj => by
    rw [hs.1.memaddrs]; exact low_dom hA hD hj
  refine ⟨A, _, A, _, conf, arr, ha, rfl, ha, rfl, hc, by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hF]; exact harr,
    fun ffi' bytes hl => ⟨_, ⟨⟨hs.1.vals, hs.1.memaddrs, hs.1.base, hs.1.code, hs.1.be⟩, rfl⟩, fun y hy hy2 => ?_⟩⟩
  have hal := DN.Compiler.WpBytes.readByteArray_length harr
  show writeByteArray s.memaddrs s.be A bytes s.memory (at_ A y) = M (at_ A y)
  rw [write_keep _ _ bytes A s.memory fun j hj => ?_, hs.2]
  rw [hl, hal] at hj
  rw [show A + BitVec.ofNat 64 j = at_ A j from rfl, DN.News.ScanRun.align_at hA.hA]
  exact DN.News.ScanRun.at_ne (by omega) hy2 (by omega)

/-! ## The round's tests -/

theorem slt_neg {W : Word} (h : ¬W.toNat < 2 ^ 63) : signedLt W (BitVec.ofNat 64 0) = true := by
  have : W.toInt < 0 := by
    rw [BitVec.toInt_eq_toNat_cond]; simp only [Nat.reducePow] at *; split <;> omega
  simp [signedLt, BitVec.slt_eq_decide, this]

/-- **`0 ≤ w < K`, signed**, is `w`'s number below `K`. -/
theorem range_lt {u : PancakeState σ} {x : String} {W : Word} (hx : u.locals x = some W) {K : Nat} (hK : K < 2 ^ 63) :
    eval u (.op .and_ (.cmp .notLess (.var x) (.const (BitVec.ofNat 64 0)))
      (.cmp .less (.var x) (.const (BitVec.ofNat 64 K)))) = some (bw (decide (W.toNat < K))) := by
  simp only [eval, hx]
  congr 1
  by_cases h : W.toNat < 2 ^ 63
  · obtain ⟨w, hw, rfl⟩ : ∃ w, w < 2 ^ 63 ∧ W = BitVec.ofNat 64 w := ⟨W.toNat, h, BitVec.eq_of_toNat_eq (by simp)⟩
    rw [DN.Compiler.WpBytes.signedLt_small hw (by decide), DN.Compiler.WpBytes.signedLt_small hw hK,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    by_cases h2 : w < K <;> simp [h2, bw]
  · rw [slt_neg h]; simp [bw, show ¬W.toNat < K by omega]

/-- **`0 ≤ w ≤ K`, signed**, is `w`'s number at most `K`. -/
theorem range_le {u : PancakeState σ} {x : String} {W : Word} (hx : u.locals x = some W) {K : Nat} (hK : K < 2 ^ 63) :
    eval u (.op .and_ (.cmp .notLess (.var x) (.const (BitVec.ofNat 64 0)))
      (.cmp .notLess (.const (BitVec.ofNat 64 K)) (.var x))) = some (bw (decide (W.toNat ≤ K))) := by
  simp only [eval, hx]
  congr 1
  by_cases h : W.toNat < 2 ^ 63
  · obtain ⟨w, hw, rfl⟩ : ∃ w, w < 2 ^ 63 ∧ W = BitVec.ofNat 64 w := ⟨W.toNat, h, BitVec.eq_of_toNat_eq (by simp)⟩
    rw [DN.Compiler.WpBytes.signedLt_small hw (by decide), DN.Compiler.WpBytes.signedLt_small hK hw,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    by_cases h2 : K < w <;> simp [h2, bw] <;> omega
  · rw [slt_neg h]; simp [bw, show ¬W.toNat ≤ K by omega]

theorem eq_eval {u : PancakeState σ} {E : PancakeExp} {W : Word} (hE : eval u E = some W) (k : Nat) :
    eval u (.cmp .equal E (.const (BitVec.ofNat 64 k))) = some (bw (decide (W = BitVec.ofNat 64 k))) := by
  simp only [eval, hE]; by_cases h : W = BitVec.ofNat 64 k <;> simp [h, bw]

/-- A state's memory named. -/
theorem runF_exact {s0 u : PancakeState σ} {l l' : List (String × Value)} {F : (Word → Word) → Prop}
    (h : RunF s0 l F u) (hl : ∀ q ∈ l', q ∈ l) : RunF s0 l' (· = u.memory) u ∧ F u.memory :=
  ⟨⟨(runF_mono h hl fun _ _ => trivial).1, rfl⟩, h.2⟩

/-- A fragment from two witnesses and a fact on them, shown for each. -/
theorem frag_given {α β : Type} {o : Oracle σ} {xs : List Syntax.PStmt} (hl : LowKK xs) {P : α → β → Assn σ}
    {X : α → β → Prop} {Q : Assn σ} (h : ∀ a b, X a b → Frag o xs (P a b) Q) :
    Frag o xs (fun u => ∃ a b, P a b u ∧ X a b) Q :=
  frag_exists hl fun a => frag_exists hl fun b => frag_pure _ (fun _ h => h.2) hl fun hx =>
    frag_conseq (h a b hx) (fun _ h => h.1) fun _ h => h

/-- A fragment from a memory `F` holds of, shown for each such memory. -/
theorem frag_runF {o : Oracle σ} {xs : List Syntax.PStmt} (hl : LowKK xs) {s0 : PancakeState σ}
    {L : List (String × Value)} {F : (Word → Word) → Prop} {Q : Assn σ}
    (h : ∀ m, F m → Frag o xs (RunF s0 L (· = m)) Q) : Frag o xs (RunF s0 L F) Q :=
  frag_conseq (P0 := fun u => ∃ m, RunF s0 L (· = m) u ∧ F m)
    (frag_exists hl fun m => frag_pure (F m) (fun _ h => h.2) hl fun hf => frag_conseq (h m hf) (fun _ h => h.1)
      fun _ h => h) (fun u h => ⟨u.memory, runF_exact h fun _ q => q⟩) fun _ h => h

/-! ## The calls -/

theorem mem_artContext : gd ArticleProg.artContext ∈ ArticleProg.functions ArticleSpec.spec esP .none :=
  List.mem_append_right _ (List.mem_map.2 ⟨ArticleProg.artContext, by simp, rfl⟩)

theorem mem_artCheck : gd (ArticleProg.artCheck ArticleSpec.spec esP) ∈
    ArticleProg.functions ArticleSpec.spec esP .none :=
  List.mem_append_right _ (List.mem_map.2 ⟨ArticleProg.artCheck ArticleSpec.spec esP, by simp, rfl⟩)

/-- **A call of `artContext`.** -/
theorem ctx_call (o : Oracle σ) {A : Word} {s0 : PancakeState σ} (hA : Area ArticleProg.ofs A s0)
    (hD : ArtDom A s0.memaddrs) (hcode : ArtCode s0.code) {l : List (String × Value)} (hc : Fresh "c" l = true)
    {m0 : Word → Word} {B0 : Bytes} (hR : Reads s0 A B0 m0) (hall : AllSets A m0) (hb : m0 (at_ A aBroken) = 0)
    {ctx : ArticleSpec.Context} (hctx : DN.News.ArticleContext.CtxIn A s0.memaddrs s0.be ctx m0)
    (hid : ctx.identity.length ≤ 200 → ∃ b, DN.News.Abnf.matches? AbnfRules.grammar AbnfRules.depth
      (ArticleSpec.ruleNamed "path-identity") (ctx.identity.map BitVec.toNat) = .ok b)
    (hgr : ∀ x (hx : x < ctx.groups.length), x < 64 → DN.News.ArticleContext.GOk ctx.groups x →
      ctx.groups[x].length ≤ 64 → ∃ b, DN.News.Abnf.matches? AbnfRules.grammar AbnfRules.depth
        (ArticleSpec.ruleNamed "newsgroup-name") (ctx.groups[x].map BitVec.toNat) = .ok b) :
    Frag o [.call "c" "artContext" []] (RunF s0 l (· = m0))
      (fun u => ∃ v, RunF s0 (("c", v) :: l) (DN.News.ArticleContext.CtxRet A ctx m0 v) u) :=
  DN.News.AbnfGen.progCall_frag o hA (f := gd ArticleProg.artContext) (by decide) (as := []) rfl
    (fun body hb' => hcode _ mem_artContext body hb') (vs := []) rfl (fun _ _ => rfl)
    (R := DN.News.ArticleContext.CtxRet A ctx) (fun s1 hA1 hc1 hm hbe _ hF => by
      exact DN.News.ArticleContext.artContext_ok o hA1 (by rw [hm]; exact hD) (by rw [hc1]; exact hcode)
        (by rw [hF]; exact reads_of hm hbe hR) (by rw [hF]; exact hall) (by rw [hF]; exact hb)
        (by rw [hm, hbe, hF]; exact hctx) hid hgr) hc (fun m m' v hm hr => hm ▸ hr)

/-- **A call of `artCheck`.** -/
theorem check_call (o : Oracle σ) {A : Word} {s0 : PancakeState σ} (hA : Area ArticleProg.ofs A s0)
    (hD : ArtDom A s0.memaddrs) (hT : TabDom A s0.memaddrs esP) (hcode : ArtCode s0.code) {l : List (String × Value)}
    (hc : Fresh "vd" l = true) {m0 : Word → Word} {a : Bytes} (hlen : a.length ≤ artMax) (hR : Reads s0 A a m0)
    (hall : AllSets A m0) (htab : TablesAt A s0.memaddrs s0.be m0 esP)
    (hkd : DN.News.ArticleTables.KindsAt ArticleSpec.spec esP A m0) (hb : m0 (at_ A aBroken) = 0)
    (hlw : m0 (at_ A ArticleProg.xLen) = BitVec.ofNat 64 a.length) {ctx : ArticleSpec.Context}
    (hctx : DN.News.ArticleAdded.CtxAt A s0.memaddrs s0.be ctx m0)
    (hGr : DN.News.ArticleListRun.GroupsAt A s0.memaddrs s0.be ctx.groups m0)
    (hgram : DN.News.ArticleLines.shapeOf ArticleSpec.spec a = 0 →
      DN.News.ArticleFields.GramOk a (DN.News.ArticleLines.spans a 0).1)
    (hgm : DN.News.ArticleLines.shapeOf ArticleSpec.spec a = 0 →
      (∀ g ∈ DN.News.ArticleLines.groups a (DN.News.ArticleLines.spans a 0).1,
        DN.News.ArticleFields.fieldNum (DN.News.ArticleLines.fieldOf a g) = 0) →
      ArticleSpec.has ((DN.News.ArticleLines.groups a (DN.News.ArticleLines.spans a 0).1).map
        (DN.News.ArticleLines.fieldOf a)) "Sender" = false →
      ∀ f, ArticleSpec.find? ((DN.News.ArticleLines.groups a (DN.News.ArticleLines.spans a 0).1).map
        (DN.News.ArticleLines.fieldOf a)) "From" = some f →
      ∃ b, DN.News.Abnf.matches? AbnfRules.grammar AbnfRules.depth (ArticleSpec.ruleNamed "mailbox")
        (f.value.map BitVec.toNat) = .ok b) :
    Frag o [.call "vd" "artCheck" []] (RunF s0 l (· = m0))
      (fun u => ∃ v, RunF s0 (("vd", v) :: l) (DN.News.ArticleCheck.CheckRet A s0.memaddrs s0.be ctx a m0 v) u) :=
  DN.News.AbnfGen.progCall_frag o hA (f := gd (ArticleProg.artCheck ArticleSpec.spec esP)) (by decide) (as := []) rfl
    (fun body hb' => hcode _ mem_artCheck body hb') (vs := []) rfl (fun _ _ => rfl)
    (R := DN.News.ArticleCheck.CheckRet A s0.memaddrs s0.be ctx a) (fun s1 hA1 hc1 hm hbe _ hF => by
      have := DN.News.ArticleCheck.artCheck_ok o hA1 (by rw [hm]; exact hD) (by rw [hm]; exact hT)
        (by rw [hc1]; exact hcode) hlen (by rw [hF]; exact reads_of hm hbe hR) (by rw [hF]; exact hall)
        (by rw [hm, hbe, hF]; exact htab) (by rw [hF]; exact hkd) (by rw [hF]; exact hb) (by rw [hF]; exact hlw)
        (by rw [hm, hbe, hF]; exact hctx) (by rw [hm, hbe, hF]; exact hGr) hgram hgm
      rw [hm, hbe] at this; exact this) hc (fun m m' v hm hr => hm ▸ hr)

/-- The wall clock's date fits the output. -/
theorem date_fits {wall : Nat} (hw : wall < ArticleProg.wallMax) :
    ([] : Bytes).length + (ArticleSpec.formatDate wall).length ≤ ArticleProg.outMax := by
  have hwm : ArticleProg.wallMax = 2 ^ 40 := rfl
  rw [DN.News.ArticleOut.formatDate_length (by omega)]
  have := DN.News.Calendar.civilFrom_range (wall / 86400) (by omega)
  have := DN.News.ArticleAdded.decimal_le20 _ (show (ArticleSpec.civilFromDays (wall / 86400)).1 < 2 ^ 64 by omega)
  have : ArticleProg.outMax = 69632 := rfl
  simp only [List.length_nil]; omega

/-- **A call of `artFormat`** from the output's start. -/
theorem fmt_call (o : Oracle σ) {A : Word} {s0 : PancakeState σ} (hA : Area ArticleProg.ofs A s0)
    (hD : ArtDom A s0.memaddrs) (hcode : ArtCode s0.code) {l : List (String × Value)} (hc : Fresh "f" l = true)
    {m0 : Word → Word} (hP : Pows m0 A) (hb : m0 (at_ A aBroken) = 0) {wall : Nat}
    (hwall : wall < ArticleProg.wallMax) (hw : m0 (at_ A ArticleProg.xWall) = BitVec.ofNat 64 wall) :
    Frag o [.call "f" "artFormat" [Syntax.n 0]] (RunF s0 l (· = m0))
      (fun u => ∃ v, RunF s0 (("f", v) :: l) (DN.News.ArticleOut.FmtRet A s0.memaddrs s0.be [] wall m0 v) u) :=
  DN.News.AbnfGen.progCall_frag o hA (f := gd ArticleProg.artFormat) (by decide) (as := [Syntax.n 0]) rfl
    (fun body hb' => hcode _ DN.News.ArticleAdded.mem_artFormat body hb') (vs := [BitVec.ofNat 64 0]) rfl
    (fun _ _ => rfl) (R := DN.News.ArticleOut.FmtRet A s0.memaddrs s0.be [] wall) (fun s1 hA1 hc1 hm hbe hl hF => by
      have := DN.News.ArticleOut.artFormat_ok o hA1 (by rw [hm]; exact hD) (by rw [hc1]; exact hcode)
        (by rw [hF]; exact hP) (by rw [hF]; exact hb) (OUT := []) (fun _ _ h => absurd h (by simp)) hwall
        (by rw [hF]; exact hw) (date_fits hwall) (by rw [hl]; rfl)
      rw [hm, hbe] at this; exact this) hc (fun m m' v hm hr => hm ▸ hr)

/-- **A call of `artDate`** over the whole input. -/
theorem date_call (o : Oracle σ) {A : Word} {s0 : PancakeState σ} (hA : Area ArticleProg.ofs A s0)
    (hD : ArtDom A s0.memaddrs) (hcode : ArtCode s0.code) {l : List (String × Value)} (hc : Fresh "d" l = true)
    {m0 : Word → Word} (hP : Pows m0 A) (hb : m0 (at_ A aBroken) = 0) {a : Bytes} (hlen : a.length ≤ artMax)
    (hin : InputAt m0 s0.memaddrs s0.be A a) (hln : l.lookup "ln" = some (BitVec.ofNat 64 a.length)) :
    Frag o [.call "d" "artDate" [Syntax.n 0, Syntax.v "ln"]] (RunF s0 l (· = m0))
      (fun u => ∃ v, RunF s0 (("d", v) :: l) (DN.News.ArticleDateOk.DateRet A a 0 a.length m0 v) u) :=
  DN.News.AbnfGen.progCall_frag o hA (f := gd (ArticleProg.artDate .none)) (by decide)
    (as := [Syntax.n 0, Syntax.v "ln"]) rfl
    (fun body hb' => hcode _ DN.News.ArticleFields.mem_artDate body hb')
    (vs := [BitVec.ofNat 64 0, BitVec.ofNat 64 a.length]) rfl
    (fun u h => by simp only [evalArgs, eval, vals_lookup h.1.vals hln])
    (R := DN.News.ArticleDateOk.DateRet A a 0 a.length) (fun s1 hA1 hc1 hm hbe hl hF => by
      have := DN.News.ArticleDateOk.artDate_ok o hA1 (by rw [hm]; exact hD) (by rw [hc1]; exact hcode)
        (by rw [hF]; exact hP) (by rw [hF]; exact hb) hlen (by rw [hm, hbe, hF]; exact hin) (Nat.zero_le _)
        (Nat.le_refl _) (by rw [hl]; rfl) (by rw [hl]; rfl)
      exact this) hc (fun m m' v hm hr => hm ▸ hr)

/-! ## The round -/

/-- The names a round declares. -/
def roundNames : List String := ["md", "ans", "wl", "ln", "inw", "inl", "c", "vd", "f", "d"]

/-- The round's locals once its words are read, `ans` the answer so far. -/
def Ld (l : List (String × Value)) (MD WL LN ans : Word) : List (String × Value) :=
  ("inl", bw (decide (LN.toNat ≤ artMax))) :: ("inw", bw (decide (WL.toNat < ArticleProg.wallMax))) :: ("ln", LN) ::
    ("wl", WL) :: ("ans", ans) :: ("md", MD) :: l

theorem ld_fresh {l : List (String × Value)} (hfr : ∀ y ∈ roundNames, Fresh y l = true) {y : String}
    (hy : y = "c" ∨ y = "vd" ∨ y = "f" ∨ y = "d") (MD WL LN ans : Word) : Fresh y (Ld l MD WL LN ans) = true := by
  unfold Ld
  rcases hy with rfl | rfl | rfl | rfl <;>
    exact fresh_cons (by decide) (fresh_cons (by decide) (fresh_cons (by decide) (fresh_cons (by decide)
      (fresh_cons (by decide) (fresh_cons (by decide) (hfr _ (by simp [roundNames])))))))

theorem ld_set {l : List (String × Value)} (hans : Fresh "ans" l = true) {MD WL LN ans v : Word} (q0 : String × Value) :
    ∀ q ∈ Ld l MD WL LN v, q ∈ ("ans", v) :: without "ans" (q0 :: Ld l MD WL LN ans) := by
  intro q hq
  simp only [Ld, List.mem_cons] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | hq
  rotate_right
  · exact .tail _ (mem_without (by simp [Ld, hq]) (DN.News.ScanRun.fresh_ne hans q hq))
  all_goals first | exact .head _ | exact .tail _ (mem_without (by simp [Ld]) (by simp))

theorem ld_tail {l : List (String × Value)} {MD WL LN ans : Word} (q0 : String × Value) :
    ∀ q ∈ Ld l MD WL LN ans, q ∈ q0 :: Ld l MD WL LN ans := fun _ h => .tail _ h

theorem ld_l {l : List (String × Value)} {MD WL LN ans : Word} : ∀ q ∈ l, q ∈ Ld l MD WL LN ans := fun _ h => by
  simp [Ld, h]

/-- A state of the round's, its answer and memory any. -/
theorem ex_clock {s0 : PancakeState σ} {L : Word → List (String × Value)} {X : Word → (Word → Word) → Prop} :
    Safe.ClockFree (fun u => ∃ v m, RunF s0 (L v) (· = m) u ∧ X v m) :=
  fun _ _ ⟨v, m, h, hx⟩ => ⟨v, m, runF_clock _ _ _ _ _ h, hx⟩

theorem ex_restore {s0 : PancakeState σ} {l : List (String × Value)} {MD WL LN : Word}
    {X : Word → (Word → Word) → Prop} {y : String} (hy : ∀ v, Fresh y (Ld l MD WL LN v) = true) :
    ∀ u w, (∃ v m, RunF s0 (Ld l MD WL LN v) (· = m) u ∧ X v m) →
      ∃ v m, RunF s0 (Ld l MD WL LN v) (· = m) (restore u y w) ∧ X v m :=
  fun _ w ⟨v, m, h, hx⟩ => ⟨v, m, runF_restore h (hy v) w, hx⟩

theorem c3_eval {s0 u : PancakeState σ} {l : List (String × Value)} {MD WL LN ans : Word} {m : Word → Word}
    (h : RunF s0 (Ld l MD WL LN ans) (· = m) u) :
    eval u (.cmp .equal (.var "md") (.const (BitVec.ofNat 64 3))) = some (bw (decide (MD = 3))) :=
  eq_eval (vals_mem h (by simp [Ld])) 3

theorem c0_eval {A : Word} {s0 u : PancakeState σ} (hD : ArtDom A s0.memaddrs) {l : List (String × Value)}
    (hla : l.lookup "a" = some A) {MD WL LN ans : Word} {m : Word → Word} (h : RunF s0 (Ld l MD WL LN ans) (· = m) u) :
    eval u (.op .and_ (.cmp .equal (.var "md") (.const (BitVec.ofNat 64 0)))
      (.op .and_ (.cmp .equal (.loadWord (.op .add (.var "a") (.const (BitVec.ofNat 64 ArticleProg.xCtxOk))))
        (.const (BitVec.ofNat 64 1))) (.op .and_ (.var "inw") (.var "inl")))) =
      some (bw (decide (MD = 0) && (decide (m (at_ A ArticleProg.xCtxOk) = 1) &&
        (decide (WL.toNat < ArticleProg.wallMax) && decide (LN.toNat ≤ artMax))))) := by
  have ha : u.locals "a" = some A := vals_lookup h.1.vals hla
  refine FramerCode.eval_and (eq_eval (vals_mem h (by simp [Ld])) 0) (FramerCode.eval_and ?_
    (FramerCode.eval_and (vals_mem h (by simp [Ld])) (vals_mem h (by simp [Ld]))))
  have := eq_eval (loadA_eval h.1.memaddrs (artDom_w hD (i := 9) (by decide)) (atA_eval ha)) 1
  rw [h.2] at this; exact this

theorem c1_eval {s0 u : PancakeState σ} {l : List (String × Value)} {MD WL LN ans : Word} {m : Word → Word}
    (h : RunF s0 (Ld l MD WL LN ans) (· = m) u) :
    eval u (.op .and_ (.cmp .equal (.var "md") (.const (BitVec.ofNat 64 1))) (.var "inw")) =
      some (bw (decide (MD = 1) && decide (WL.toNat < ArticleProg.wallMax))) :=
  FramerCode.eval_and (eq_eval (vals_mem h (by simp [Ld])) 1) (vals_mem h (by simp [Ld]))

theorem c2_eval {s0 u : PancakeState σ} {l : List (String × Value)} {MD WL LN ans : Word} {m : Word → Word}
    (h : RunF s0 (Ld l MD WL LN ans) (· = m) u) :
    eval u (.op .and_ (.cmp .equal (.var "md") (.const (BitVec.ofNat 64 2))) (.var "inl")) =
      some (bw (decide (MD = 2) && decide (LN.toNat ≤ artMax))) :=
  FramerCode.eval_and (eq_eval (vals_mem h (by simp [Ld])) 2) (vals_mem h (by simp [Ld]))

section
open Syntax (v n eEq eAnd)
open ArticleProg (setW)

/-- The test of a context's request. -/
abbrev if3 : Syntax.PStmt := ifs (eEq (v "md") (n 3)) [.call "c" "artContext" [], .assign "ans" (v "c")]
/-- The test of an article's request. -/
abbrev if0 : Syntax.PStmt := ifs (eAnd (eEq (v "md") (n 0)) (eAnd (eEq (wd ArticleProg.xCtxOk) (n 1))
  (eAnd (v "inw") (v "inl")))) [.call "vd" "artCheck" [], .assign "ans" (v "vd")]
/-- The test of a date's request. -/
abbrev if1 : Syntax.PStmt :=
  ifs (eAnd (eEq (v "md") (n 1)) (v "inw")) [.call "f" "artFormat" [n 0], setW ArticleProg.xOutLen (v "f"),
    .assign "ans" (n 0)]
/-- The test of a date-time's request. -/
abbrev if2 : Syntax.PStmt :=
  ifs (eAnd (eEq (v "md") (n 2)) (v "inl")) [.call "d" "artDate" [n 0, v "ln"],
    .ite (eEq (v "d") (n 1)) [.assign "ans" (n 0)] [ifs (eEq (v "d") (n 0)) [.assign "ans" (n 1)]]]

theorem if0_lower : Lower.lowerExp (eAnd (eEq (v "md") (n 0)) (eAnd (eEq (wd ArticleProg.xCtxOk) (n 1))
    (eAnd (v "inw") (v "inl")))) = some (.op .and_ (.cmp .equal (.var "md") (.const (BitVec.ofNat 64 0)))
      (.op .and_ (.cmp .equal (.loadWord (.op .add (.var "a") (.const (BitVec.ofNat 64 ArticleProg.xCtxOk))))
        (.const (BitVec.ofNat 64 1))) (.op .and_ (.var "inw") (.var "inl")))) := by
  rfl

/-- **A test not passed**: nothing done. -/
theorem skip_if {o : Oracle σ} {c : Syntax.PExpr} {C : PancakeExp} (hc : Lower.lowerExp c = some C)
    {t : List Syntax.PStmt} (hlt : LowKK t) {s0 : PancakeState σ} {L : List (String × Value)} {m : Word → Word}
    (hd : ∀ y ∈ declared t, Fresh y L = true) (h0 : ∀ u, RunF s0 L (· = m) u → eval u C = some (bw false)) :
    Frag o [ifs c t] (RunF s0 L (· = m)) (RunF s0 L (· = m)) :=
  frag_ifR o hc hlt lowKK_nil (runF_clock _ _ _) (fun u y w h hy => runF_restore h (hd y hy) w)
    (fun _ _ _ _ h => by simp [declared] at h) h0 (fun h => nomatch h) fun _ => frag_nil o fun _ h => h

end

theorem ld_a {l : List (String × Value)} {A : Word} (hla : l.lookup "a" = some A) {MD WL LN ans : Word}
    {x : String} (w : Value) (hq : x ≠ "a") : ((x, w) :: Ld l MD WL LN ans).lookup "a" = some A := by
  rw [lookup_cons_ne (Ne.symm hq)]; exact hla

/-- **A context's request**: `artContext`'s answer the round's. -/
theorem run3 (o : Oracle σ) {A : Word} {s0 : PancakeState σ} (hA : Area ArticleProg.ofs A s0)
    (hD : ArtDom A s0.memaddrs) (hcode : ArtCode s0.code) {l : List (String × Value)}
    (hfr : ∀ y ∈ roundNames, Fresh y l = true) {MD WL LN : Word}
      (h3 : MD = 3) {m0 : Word → Word} {B0 : Bytes}
    (hR : Reads s0 A B0 m0) (hall : AllSets A m0) (hb : m0 (at_ A aBroken) = 0) {ctx : ArticleSpec.Context}
    (hctx : DN.News.ArticleContext.CtxIn A s0.memaddrs s0.be ctx m0)
    (hid : ctx.identity.length ≤ 200 → ∃ b, DN.News.Abnf.matches? AbnfRules.grammar AbnfRules.depth
      (ArticleSpec.ruleNamed "path-identity") (ctx.identity.map BitVec.toNat) = .ok b)
    (hgr : ∀ x (hx : x < ctx.groups.length), x < 64 → DN.News.ArticleContext.GOk ctx.groups x →
      ctx.groups[x].length ≤ 64 → ∃ b, DN.News.Abnf.matches? AbnfRules.grammar AbnfRules.depth
        (ArticleSpec.ruleNamed "newsgroup-name") (ctx.groups[x].map BitVec.toNat) = .ok b) :
    Frag o [if3] (RunF s0 (Ld l MD WL LN 255) (· = m0))
      (fun u => ∃ v m, RunF s0 (Ld l MD WL LN v) (· = m) u ∧ DN.News.ArticleContext.CtxRet A ctx m0 v m) :=
  frag_ifR o rfl (lowK_any _ (k := .skip) rfl) lowKK_nil ex_clock
    (fun u y w h hy => by
      simp [declared] at hy; subst hy; exact ex_restore (fun v => ld_fresh hfr (.inl rfl) _ _ _ v) u w h)
    (fun _ _ _ _ h => by simp [declared] at h) (b := true) (fun u h => by rw [c3_eval h, decide_eq_true h3])
    (fun _ => frag_append (xs := [_]) (ctx_call o hA hD hcode (ld_fresh hfr (.inl rfl) _ _ _ _) hR hall hb hctx hid hgr)
      (frag_exists (lowK_any _ (k := .skip) rfl) fun v => frag_conseq
        (runF_set o rfl (l := ("c", v) :: Ld l MD WL LN 255) rfl (fun u h => vals_mem h (.head _)))
        (fun _ h => h) fun u h => ⟨v, u.memory, runF_exact h (ld_set (hfr "ans" (by simp [roundNames])) _)⟩))
    fun h => nomatch h

/-- **An article's request**, `xCtxOk` 1 and the words in range: `artCheck`'s answer the round's. -/
theorem run0 (o : Oracle σ) {A : Word} {s0 : PancakeState σ} (hA : Area ArticleProg.ofs A s0)
    (hD : ArtDom A s0.memaddrs) (hT : TabDom A s0.memaddrs esP) (hcode : ArtCode s0.code)
    {l : List (String × Value)} (hla : l.lookup "a" = some A)
    (hfr : ∀ y ∈ roundNames, Fresh y l = true) {MD WL LN : Word}
      {m0 : Word → Word}
    (h0 : MD = 0 ∧ m0 (at_ A ArticleProg.xCtxOk) = 1 ∧ WL.toNat < ArticleProg.wallMax ∧ LN.toNat ≤ artMax)
    {a : Bytes} (hlen : a.length ≤ artMax) (hR : Reads s0 A a m0)
    (hall : AllSets A m0) (htab : TablesAt A s0.memaddrs s0.be m0 esP)
    (hkd : DN.News.ArticleTables.KindsAt ArticleSpec.spec esP A m0) (hb : m0 (at_ A aBroken) = 0)
    (hlw : m0 (at_ A ArticleProg.xLen) = BitVec.ofNat 64 a.length) {ctx : ArticleSpec.Context}
    (hctx : DN.News.ArticleAdded.CtxAt A s0.memaddrs s0.be ctx m0)
    (hGr : DN.News.ArticleListRun.GroupsAt A s0.memaddrs s0.be ctx.groups m0)
    (hgram : DN.News.ArticleLines.shapeOf ArticleSpec.spec a = 0 →
      DN.News.ArticleFields.GramOk a (DN.News.ArticleLines.spans a 0).1)
    (hgm : DN.News.ArticleLines.shapeOf ArticleSpec.spec a = 0 →
      (∀ g ∈ DN.News.ArticleLines.groups a (DN.News.ArticleLines.spans a 0).1,
        DN.News.ArticleFields.fieldNum (DN.News.ArticleLines.fieldOf a g) = 0) →
      ArticleSpec.has ((DN.News.ArticleLines.groups a (DN.News.ArticleLines.spans a 0).1).map
        (DN.News.ArticleLines.fieldOf a)) "Sender" = false →
      ∀ f, ArticleSpec.find? ((DN.News.ArticleLines.groups a (DN.News.ArticleLines.spans a 0).1).map
        (DN.News.ArticleLines.fieldOf a)) "From" = some f →
      ∃ b, DN.News.Abnf.matches? AbnfRules.grammar AbnfRules.depth (ArticleSpec.ruleNamed "mailbox")
        (f.value.map BitVec.toNat) = .ok b) :
    Frag o [if0] (RunF s0 (Ld l MD WL LN 255) (· = m0))
      (fun u => ∃ v m, RunF s0 (Ld l MD WL LN v) (· = m) u ∧
        DN.News.ArticleCheck.CheckRet A s0.memaddrs s0.be ctx a m0 v m) :=
  frag_ifR o if0_lower (lowK_any _ (k := .skip) rfl) lowKK_nil ex_clock
    (fun u y w h hy => by
      simp [declared] at hy; subst hy; exact ex_restore (fun v => ld_fresh hfr (.inr (.inl rfl)) _ _ _ v) u w h)
    (fun _ _ _ _ h => by simp [declared] at h) (b := true)
    (fun u h => by rw [c0_eval hD hla h]; obtain ⟨e0, e1, e2, e3⟩ := h0; simp [e0, e1, e2, e3])
    (fun _ => frag_append (xs := [_]) (check_call o hA hD hT hcode (ld_fresh hfr (.inr (.inl rfl)) _ _ _ _) hlen hR
        hall htab hkd hb hlw hctx hGr hgram hgm)
      (frag_exists (lowK_any _ (k := .skip) rfl) fun v => frag_conseq
        (runF_set o rfl (l := ("vd", v) :: Ld l MD WL LN 255) rfl (fun u h => vals_mem h (.head _)))
        (fun _ h => h) fun u h => ⟨v, u.memory, runF_exact h (ld_set (hfr "ans" (by simp [roundNames])) _)⟩))
    fun h => nomatch h

/-- **A date's request**, the wall clock in range: its date in the output, 0 the round's answer. -/
theorem run1 (o : Oracle σ) {A : Word} {s0 : PancakeState σ} (hA : Area ArticleProg.ofs A s0)
    (hD : ArtDom A s0.memaddrs) (hcode : ArtCode s0.code) {l : List (String × Value)} (hla : l.lookup "a" = some A)
    (hfr : ∀ y ∈ roundNames, Fresh y l = true) {MD WL LN : Word}
      (h1 : MD = 1 ∧ WL.toNat < ArticleProg.wallMax) {m0 : Word → Word} (hP : Pows m0 A)
    (hb : m0 (at_ A aBroken) = 0) (hw : m0 (at_ A ArticleProg.xWall) = WL) :
    Frag o [if1] (RunF s0 (Ld l MD WL LN 255) (· = m0))
      (fun u => ∃ v m, RunF s0 (Ld l MD WL LN v) (· = m) u ∧ v = 0 ∧
        ∃ f m1, DN.News.ArticleOut.FmtRet A s0.memaddrs s0.be [] WL.toNat m0 f m1 ∧
          m = upd m1 (at_ A ArticleProg.xOutLen) f) := by
  have hw' : m0 (at_ A ArticleProg.xWall) = BitVec.ofNat 64 WL.toNat := by rw [hw]; simp
  refine frag_ifR o rfl (lowK_any _ (k := .skip) rfl) lowKK_nil ex_clock
    (fun u y w h hy => by
      simp [declared, ArticleProg.setW] at hy; subst hy
      exact ex_restore (fun v => ld_fresh hfr (.inr (.inr (.inl rfl))) _ _ _ v) u w h)
    (fun _ _ _ _ h => by simp [declared] at h) (b := true)
    (fun u h => by rw [c1_eval h, decide_eq_true h1.1, decide_eq_true h1.2]; rfl) (fun _ => ?_) fun h => nomatch h
  refine frag_append (xs := [_]) (fmt_call o hA hD hcode (ld_fresh hfr (.inr (.inr (.inl rfl))) _ _ _ _) hP hb h1.2 hw')
    (frag_exists (lowK_any _ (k := .skip) rfl) fun f => frag_runF (lowK_any _ (k := .skip) rfl) fun m1 hret => ?_)
  refine frag_append (xs := [_]) (runF_storeA o (atOffW_lower 12) rfl (artDom_w hD (by decide))
    (fun u h => atA_eval (vals_lookup h.1.vals (ld_a hla _ (by decide)))) (val := fun _ => f)
    (fun u h => vals_mem h (.head _)) (G := (· = upd m1 (at_ A ArticleProg.xOutLen) f)) fun m hm => by subst hm; rfl) ?_
  exact frag_conseq (runF_set o rfl (l := ("f", f) :: Ld l MD WL LN 255) rfl (v := BitVec.ofNat 64 0) fun _ _ => rfl)
    (fun _ h => h) fun u h =>
      ⟨_, _, runF_mono h (ld_set (hfr "ans" (by simp [roundNames])) _) (fun _ e => e), rfl, f, m1, hret, rfl⟩

/-- A date's answer as a round gives it: 0 for seconds, 1 for none, 255 past the range. -/
def dateAns (d : Word) : Word := if d = 1 then 0 else if d = 0 then 1 else 255

/-- **A date-time's request**, the input's length in range: `artDate`'s answer over the input, as `dateAns` gives it. -/
theorem run2 (o : Oracle σ) {A : Word} {s0 : PancakeState σ} (hA : Area ArticleProg.ofs A s0)
    (hD : ArtDom A s0.memaddrs) (hcode : ArtCode s0.code) {l : List (String × Value)}
    (hfr : ∀ y ∈ roundNames, Fresh y l = true) {MD WL LN : Word}
      (h2 : MD = 2 ∧ LN.toNat ≤ artMax) {m0 : Word → Word} (hP : Pows m0 A)
    (hb : m0 (at_ A aBroken) = 0) {a : Bytes} (hlen : a.length ≤ artMax) (hin : InputAt m0 s0.memaddrs s0.be A a)
    (hLN : LN = BitVec.ofNat 64 a.length) :
    Frag o [if2] (RunF s0 (Ld l MD WL LN 255) (· = m0))
      (fun u => ∃ v m, RunF s0 (Ld l MD WL LN v) (· = m) u ∧
        ∃ d, DN.News.ArticleDateOk.DateRet A a 0 a.length m0 d m ∧ v = dateAns d) := by
  have hd := ld_fresh hfr (.inr (.inr (.inr rfl)))
  have hans := hfr "ans" (by simp [roundNames])
  refine frag_ifR o rfl (lowK_any _ (k := .skip) rfl) lowKK_nil ex_clock
    (fun u y w h hy => by simp [declared] at hy; subst hy; exact ex_restore (fun v => hd _ _ _ v) u w h)
    (fun _ _ _ _ h => by simp [declared] at h) (b := true)
    (fun u h => by rw [c2_eval h, decide_eq_true h2.1, decide_eq_true h2.2]; rfl) (fun _ => ?_) fun h => nomatch h
  refine frag_append (xs := [_]) (date_call o hA hD hcode (hd _ _ _ _) hP hb hlen hin (by rw [← hLN]; rfl))
    (frag_exists (lowK_any _ (k := .skip) rfl) fun d => frag_runF (lowK_any _ (k := .skip) rfl) fun m1 hret => ?_)
  have hv : ∀ k, ∀ u, RunF s0 (("d", d) :: Ld l MD WL LN 255) (· = m1) u →
      eval u (.cmp .equal (.var "d") (.const (BitVec.ofNat 64 k))) = some (bw (decide (d = BitVec.ofNat 64 k))) :=
    fun k u h => eq_eval (vals_mem h (.head _)) k
  have hset : ∀ k : Nat, dateAns d = BitVec.ofNat 64 k → Frag o [.assign "ans" (Syntax.n k)]
      (RunF s0 (("d", d) :: Ld l MD WL LN 255) (· = m1))
      (fun u => ∃ v m, RunF s0 (Ld l MD WL LN v) (· = m) u ∧
        ∃ d, DN.News.ArticleDateOk.DateRet A a 0 a.length m0 d m ∧ v = dateAns d) := fun k hk =>
    frag_conseq (runF_set o rfl (l := ("d", d) :: Ld l MD WL LN 255) rfl (v := BitVec.ofNat 64 k) fun _ _ => rfl)
      (fun _ h => h) fun u h => ⟨_, _, runF_mono h (ld_set hans _) (fun _ e => e), d, hret, hk.symm⟩
  refine frag_ifR o rfl (lowK_any _ (k := .skip) rfl) (lowK_any _ (k := .skip) rfl) ex_clock
    (fun _ _ _ _ h => by simp [declared] at h) (fun _ _ _ _ h => by simp [declared, ifs] at h) (hv 1)
    (fun e1 => hset 0 (by simp [dateAns, of_decide_eq_true e1])) fun e1 => ?_
  refine frag_ifR o rfl (lowK_any _ (k := .skip) rfl) lowKK_nil ex_clock
    (fun _ _ _ _ h => by simp [declared] at h) (fun _ _ _ _ h => by simp [declared] at h) (hv 0)
    (fun e0 => hset 1 (by simp [dateAns, of_decide_eq_true e0])) fun e0 =>
      frag_nil o fun u h => ⟨_, _, runF_mono h (ld_tail _) (fun _ e => e), d, hret, by
        simp [dateAns, of_decide_eq_false e1, of_decide_eq_false e0]⟩

/-- **The round's end**: the failed flag clear, a context's answer kept in `xCtxOk`, the answer in `xVerdict`. -/
theorem tail_frag (o : Oracle σ) {A : Word} {s0 : PancakeState σ} (hA : Area ArticleProg.ofs A s0)
    (hD : ArtDom A s0.memaddrs) {l : List (String × Value)} (hla : l.lookup "a" = some A) {MD WL LN ans : Word}
    {m : Word → Word} (hb : m (at_ A aBroken) = 0) :
    Frag o [ifs (word (Syntax.v "a") aBroken) [.assign "ans" (Syntax.n 255)],
      ifs (Syntax.eEq (Syntax.v "md") (Syntax.n 3)) [ArticleProg.setW ArticleProg.xCtxOk (Syntax.v "ans")],
      ArticleProg.setW ArticleProg.xVerdict (Syntax.v "ans")] (RunF s0 (Ld l MD WL LN ans) (· = m))
      (RunF s0 l (· = upd (if MD = 3 then upd m (at_ A ArticleProg.xCtxOk) ans else m)
        (at_ A ArticleProg.xVerdict) ans)) := by
  have hla' : (Ld l MD WL LN ans).lookup "a" = some A := hla
  have hbI : aBroken < aInput := by rw [aInput_eq]; decide
  refine frag_append (xs := [_]) (skip_if rfl (lowK_any _ (k := .skip) rfl) (fun _ h => by simp [declared] at h)
    fun u h => by
      rw [DN.News.AbnfMain.load_at hA h.1.memaddrs (vals_lookup h.1.vals hla') hbI (by decide), h.2, hb]; rfl) ?_
  refine frag_append (xs := [_]) (frag_ifR o rfl (lowK_any _ (k := .skip) rfl) lowKK_nil (runF_clock _ _ _)
    (fun _ _ _ _ h => by simp [declared, ArticleProg.setW] at h) (fun _ _ _ _ h => by simp [declared] at h)
    (fun u h => c3_eval h)
    (Q := RunF s0 (Ld l MD WL LN ans) (· = if MD = 3 then upd m (at_ A ArticleProg.xCtxOk) ans else m))
    (fun e => runF_storeA o (atOffW_lower 9) rfl (artDom_w hD (by decide))
      (fun u h => atA_eval (vals_lookup h.1.vals hla')) (val := fun _ => ans) (fun u h => vals_mem h (by simp [Ld]))
      fun m' hm => by subst hm; show _ = _; rw [if_pos (of_decide_eq_true e)]; rfl)
    fun e => frag_nil o fun u h => ⟨h.1, by rw [h.2, if_neg (of_decide_eq_false e)]⟩) ?_
  exact frag_conseq (runF_storeA o (atOffW_lower 10) rfl (artDom_w hD (by decide))
    (fun u h => atA_eval (vals_lookup h.1.vals hla')) (val := fun _ => ans) (fun u h => vals_mem h (by simp [Ld]))
    (G := (· = upd (if MD = 3 then upd m (at_ A ArticleProg.xCtxOk) ans else m) (at_ A ArticleProg.xVerdict) ans))
    fun m' hm => by subst hm; rfl) (fun _ h => h) fun _ h => runF_mono h ld_l fun _ e => e

/-- **What a round leaves** from `m0`, the memory its calls see, by the mode in `xMode`. Mode 3 gives `artContext`'s
answer, also kept in `xCtxOk`; 0 `artCheck`'s, given `xCtxOk` 1 and words in range. Mode 1 writes the wall clock's date,
2 gives `artDate`'s answer by `dateAns`; else 255. -/
def RoundRet (A : Word) (dm : Word → Bool) (be : Bool) (ctx : ArticleSpec.Context) (a : Bytes) (m0 m : Word → Word) :
    Prop :=
  if m0 (at_ A ArticleProg.xMode) = 3 then ∃ v m1, DN.News.ArticleContext.CtxRet A ctx m0 v m1 ∧
    m = upd (upd m1 (at_ A ArticleProg.xCtxOk) v) (at_ A ArticleProg.xVerdict) v
  else if m0 (at_ A ArticleProg.xMode) = 0 ∧ m0 (at_ A ArticleProg.xCtxOk) = 1 ∧
      (m0 (at_ A ArticleProg.xWall)).toNat < ArticleProg.wallMax ∧ (m0 (at_ A ArticleProg.xLen)).toNat ≤ artMax then
    ∃ v m1, DN.News.ArticleCheck.CheckRet A dm be ctx a m0 v m1 ∧ m = upd m1 (at_ A ArticleProg.xVerdict) v
  else if m0 (at_ A ArticleProg.xMode) = 1 ∧ (m0 (at_ A ArticleProg.xWall)).toNat < ArticleProg.wallMax then
    ∃ f m1, DN.News.ArticleOut.FmtRet A dm be [] (m0 (at_ A ArticleProg.xWall)).toNat m0 f m1 ∧
      m = upd (upd m1 (at_ A ArticleProg.xOutLen) f) (at_ A ArticleProg.xVerdict) 0
  else if m0 (at_ A ArticleProg.xMode) = 2 ∧ (m0 (at_ A ArticleProg.xLen)).toNat ≤ artMax then
    ∃ d m1, DN.News.ArticleDateOk.DateRet A a 0 a.length m0 d m1 ∧ m = upd m1 (at_ A ArticleProg.xVerdict) (dateAns d)
  else m = upd m0 (at_ A ArticleProg.xVerdict) 255

theorem skip3 {o : Oracle σ} {s0 : PancakeState σ} {l : List (String × Value)}
    (hfr : ∀ y ∈ roundNames, Fresh y l = true)
    {MD WL LN ans : Word} {m : Word → Word} (h : MD ≠ 3) :
    Frag o [if3] (RunF s0 (Ld l MD WL LN ans) (· = m)) (RunF s0 (Ld l MD WL LN ans) (· = m)) :=
  skip_if rfl (lowK_any _ (k := .skip) rfl)
    (fun y hy => by simp [declared] at hy; subst hy; exact ld_fresh hfr (by simp) _ _ _ _)
    fun u hu => by rw [c3_eval hu, decide_eq_false h]

theorem skip0 {o : Oracle σ} {A : Word} {s0 : PancakeState σ} (hD : ArtDom A s0.memaddrs)
    {l : List (String × Value)} (hla : l.lookup "a" = some A) (hfr : ∀ y ∈ roundNames, Fresh y l = true)
    {MD WL LN ans : Word} {m : Word → Word}
    (h : ¬(MD = 0 ∧ m (at_ A ArticleProg.xCtxOk) = 1 ∧ WL.toNat < ArticleProg.wallMax ∧ LN.toNat ≤ artMax)) :
    Frag o [if0] (RunF s0 (Ld l MD WL LN ans) (· = m)) (RunF s0 (Ld l MD WL LN ans) (· = m)) :=
  skip_if if0_lower (lowK_any _ (k := .skip) rfl)
    (fun y hy => by simp [declared] at hy; subst hy; exact ld_fresh hfr (by simp) _ _ _ _)
    fun u hu => by rw [c0_eval hD hla hu]; congr 2; simpa using h

theorem skip1 {o : Oracle σ} {s0 : PancakeState σ} {l : List (String × Value)}
    (hfr : ∀ y ∈ roundNames, Fresh y l = true)
    {MD WL LN ans : Word} {m : Word → Word} (h : ¬(MD = 1 ∧ WL.toNat < ArticleProg.wallMax)) :
    Frag o [if1] (RunF s0 (Ld l MD WL LN ans) (· = m)) (RunF s0 (Ld l MD WL LN ans) (· = m)) :=
  skip_if rfl (lowK_any _ (k := .skip) rfl)
    (fun y hy => by simp [declared, ArticleProg.setW] at hy; subst hy; exact ld_fresh hfr (by simp) _ _ _ _)
    fun u hu => by rw [c1_eval hu]; congr 2; simpa using h

theorem skip2 {o : Oracle σ} {s0 : PancakeState σ} {l : List (String × Value)}
    (hfr : ∀ y ∈ roundNames, Fresh y l = true)
    {MD WL LN ans : Word} {m : Word → Word} (h : ¬(MD = 2 ∧ LN.toNat ≤ artMax)) :
    Frag o [if2] (RunF s0 (Ld l MD WL LN ans) (· = m)) (RunF s0 (Ld l MD WL LN ans) (· = m)) :=
  skip_if rfl (lowK_any _ (k := .skip) rfl)
    (fun y hy => by simp [declared] at hy; subst hy; exact ld_fresh hfr (by simp) _ _ _ _)
    fun u hu => by rw [c2_eval hu]; congr 2; simpa using h

/-- **A round of `main`** leaves what `RoundRet` says, from the memory `dn_next` leaves, the failed flag cleared.
Each call's premises are asked only where its request is made. -/
theorem round_ok (o : Oracle σ) {A : Word} {s0 : PancakeState σ} (hA : Area ArticleProg.ofs A s0)
    (hD : ArtDom A s0.memaddrs) (hT : TabDom A s0.memaddrs esP) (hcode : ArtCode s0.code)
    {l : List (String × Value)} (hla : l.lookup "a" = some A) (hfr : ∀ y ∈ roundNames, Fresh y l = true)
    {M M0 : Word → Word} (hM0 : M0 = upd M (at_ A aBroken) 0) {ctx : ArticleSpec.Context} {a : Bytes}
    (h3 : M0 (at_ A ArticleProg.xMode) = 3 → (∃ B, Reads s0 A B M0) ∧ AllSets A M0 ∧
      DN.News.ArticleContext.CtxIn A s0.memaddrs s0.be ctx M0 ∧
      (ctx.identity.length ≤ 200 → ∃ b, DN.News.Abnf.matches? AbnfRules.grammar AbnfRules.depth
        (ArticleSpec.ruleNamed "path-identity") (ctx.identity.map BitVec.toNat) = .ok b) ∧
      ∀ x (hx : x < ctx.groups.length), x < 64 → DN.News.ArticleContext.GOk ctx.groups x →
        ctx.groups[x].length ≤ 64 → ∃ b, DN.News.Abnf.matches? AbnfRules.grammar AbnfRules.depth
          (ArticleSpec.ruleNamed "newsgroup-name") (ctx.groups[x].map BitVec.toNat) = .ok b)
    (h0 : M0 (at_ A ArticleProg.xMode) = 0 → M0 (at_ A ArticleProg.xCtxOk) = 1 →
      (M0 (at_ A ArticleProg.xWall)).toNat < ArticleProg.wallMax → (M0 (at_ A ArticleProg.xLen)).toNat ≤ artMax →
      a.length ≤ artMax ∧ Reads s0 A a M0 ∧ AllSets A M0 ∧ TablesAt A s0.memaddrs s0.be M0 esP ∧
      DN.News.ArticleTables.KindsAt ArticleSpec.spec esP A M0 ∧
      M0 (at_ A ArticleProg.xLen) = BitVec.ofNat 64 a.length ∧ DN.News.ArticleAdded.CtxAt A s0.memaddrs s0.be ctx M0 ∧
      DN.News.ArticleListRun.GroupsAt A s0.memaddrs s0.be ctx.groups M0 ∧
      (DN.News.ArticleLines.shapeOf ArticleSpec.spec a = 0 →
        DN.News.ArticleFields.GramOk a (DN.News.ArticleLines.spans a 0).1) ∧
      (DN.News.ArticleLines.shapeOf ArticleSpec.spec a = 0 →
        (∀ g ∈ DN.News.ArticleLines.groups a (DN.News.ArticleLines.spans a 0).1,
          DN.News.ArticleFields.fieldNum (DN.News.ArticleLines.fieldOf a g) = 0) →
        ArticleSpec.has ((DN.News.ArticleLines.groups a (DN.News.ArticleLines.spans a 0).1).map
          (DN.News.ArticleLines.fieldOf a)) "Sender" = false →
        ∀ f, ArticleSpec.find? ((DN.News.ArticleLines.groups a (DN.News.ArticleLines.spans a 0).1).map
          (DN.News.ArticleLines.fieldOf a)) "From" = some f →
        ∃ b, DN.News.Abnf.matches? AbnfRules.grammar AbnfRules.depth (ArticleSpec.ruleNamed "mailbox")
          (f.value.map BitVec.toNat) = .ok b))
    (h1 : M0 (at_ A ArticleProg.xMode) = 1 → (M0 (at_ A ArticleProg.xWall)).toNat < ArticleProg.wallMax → Pows M0 A)
    (h2 : M0 (at_ A ArticleProg.xMode) = 2 → (M0 (at_ A ArticleProg.xLen)).toNat ≤ artMax →
      Pows M0 A ∧ a.length ≤ artMax ∧ M0 (at_ A ArticleProg.xLen) = BitVec.ofNat 64 a.length ∧
      InputAt M0 s0.memaddrs s0.be A a) :
    Frag o ArticleProg.round (RunF s0 l (· = M)) (RunF s0 l (RoundRet A s0.memaddrs s0.be ctx a M0)) := by
  have hb0 : M0 (at_ A aBroken) = 0 := by rw [hM0]; exact upd_eq _ _ _
  have hbS := DN.News.ArticleGrammar.broken_low
  have hans := hfr "ans" (by simp [roundNames])
  have hld : ∀ (L : List (String × Value)) (F : (Word → Word) → Prop) u, RunF s0 L F u → L.lookup "a" = some A →
      ∀ i, i < 32 → eval u (.loadWord (.op .add (.var "a") (.const (BitVec.ofNat 64 (ArticleProg.w i))))) =
        some (u.memory (at_ A (ArticleProg.w i))) := fun _ _ u h hl i hi =>
    loadA_eval h.1.memaddrs (artDom_w hD hi) (atA_eval (vals_lookup h.1.vals hl))
  unfold ArticleProg.round
  refine frag_append (xs := [_]) (DN.News.AbnfSets.runF_store o hA (d := Syntax.atOff (Syntax.v "a") aBroken)
    (e := Syntax.n 0) rfl rfl (y := aBroken) (by omega) (by decide)
    (fun w h => by simp only [eval, vals_lookup h.1.vals hla]; rfl) (val := fun _ => 0) (fun _ _ => rfl)
    (G := (· = M0)) fun m hm => by rw [hM0, hm]) ?_
  refine frag_append (xs := [_]) (runF_dec o (wd_lower 0) (hfr "md" (by simp [roundNames]))
    (v := M0 (at_ A ArticleProg.xMode))
    fun u h => by rw [hld _ _ u h hla 0 (by decide), h.2]; rfl) ?_
  refine frag_append (xs := [_]) (runF_dec o rfl (fresh_cons (by decide) hans) (v := BitVec.ofNat 64 255)
    fun _ _ => rfl) ?_
  refine frag_append (xs := [_]) (runF_dec o (wd_lower 2)
    (fresh_cons (by decide) (fresh_cons (by decide) (hfr "wl" (by simp [roundNames]))))
    (v := M0 (at_ A ArticleProg.xWall))
    fun u h => by rw [hld _ _ u h hla 2 (by decide), h.2]; rfl) ?_
  refine frag_append (xs := [_]) (runF_dec o (wd_lower 1)
    (fresh_cons (by decide) (fresh_cons (by decide) (fresh_cons (by decide) (hfr "ln" (by simp [roundNames])))))
    (v := M0 (at_ A ArticleProg.xLen)) fun u h => by rw [hld _ _ u h hla 1 (by decide), h.2]; rfl) ?_
  refine frag_append (xs := [_]) (runF_dec o rfl (fresh_cons (by decide) (fresh_cons (by decide)
    (fresh_cons (by decide) (fresh_cons (by decide) (hfr "inw" (by simp [roundNames]))))))
    (v := bw (decide ((M0 (at_ A ArticleProg.xWall)).toNat < ArticleProg.wallMax)))
    fun u h => range_lt (vals_lookup h.1.vals rfl) (by decide)) ?_
  refine frag_append (xs := [_]) (runF_dec o rfl (fresh_cons (by decide) (fresh_cons (by decide) (fresh_cons (by decide)
    (fresh_cons (by decide) (fresh_cons (by decide) (hfr "inl" (by simp [roundNames])))))))
    (v := bw (decide ((M0 (at_ A ArticleProg.xLen)).toNat ≤ artMax)))
    fun u h => range_le (vals_lookup h.1.vals rfl) (by decide)) ?_
  refine frag_conseq (P0 := RunF s0 (Ld l (M0 (at_ A ArticleProg.xMode)) (M0 (at_ A ArticleProg.xWall))
    (M0 (at_ A ArticleProg.xLen)) 255) (· = M0)) ?_ (fun _ h => h) fun _ h => h
  have hmid : ∀ (v : Word) (m : Word → Word), m (at_ A aBroken) = 0 →
      (∀ mf, mf = upd (if M0 (at_ A ArticleProg.xMode) = 3 then upd m (at_ A ArticleProg.xCtxOk) v else m)
        (at_ A ArticleProg.xVerdict) v → RoundRet A s0.memaddrs s0.be ctx a M0 mf) →
      Frag o [ifs (word (Syntax.v "a") aBroken) [.assign "ans" (Syntax.n 255)],
        ifs (Syntax.eEq (Syntax.v "md") (Syntax.n 3)) [ArticleProg.setW ArticleProg.xCtxOk (Syntax.v "ans")],
        ArticleProg.setW ArticleProg.xVerdict (Syntax.v "ans")]
        (RunF s0 (Ld l (M0 (at_ A ArticleProg.xMode)) (M0 (at_ A ArticleProg.xWall)) (M0 (at_ A ArticleProg.xLen)) v)
          (· = m)) (RunF s0 l (RoundRet A s0.memaddrs s0.be ctx a M0)) := fun v m hb hR =>
    frag_conseq (tail_frag o hA hD hla hb) (fun _ h => h) fun _ h => runF_mono h (fun _ q => q) fun mf e => hR mf e
  by_cases c3 : M0 (at_ A ArticleProg.xMode) = 3
  · obtain ⟨⟨B, hR⟩, hall, hctx, hid, hgr⟩ := h3 c3
    refine frag_append (xs := [_]) (run3 o hA hD hcode hfr c3 hR hall hb0 hctx hid hgr) ?_
    refine frag_given (lowK_any _ (k := .skip) rfl) fun v m1 hret => ?_
    refine frag_append (xs := [_]) (skip0 hD hla hfr (by rw [c3]; simp)) ?_
    refine frag_append (xs := [_]) (skip1 hfr (by rw [c3]; simp)) ?_
    refine frag_append (xs := [_]) (skip2 hfr (by rw [c3]; simp)) ?_
    exact hmid v m1 hret.2.1 fun mf e => by
      unfold RoundRet; rw [if_pos c3]; rw [if_pos c3] at e; exact ⟨v, m1, hret, e⟩
  refine frag_append (xs := [_]) (skip3 hfr c3) ?_
  by_cases c0 : M0 (at_ A ArticleProg.xMode) = 0 ∧ M0 (at_ A ArticleProg.xCtxOk) = 1 ∧
      (M0 (at_ A ArticleProg.xWall)).toNat < ArticleProg.wallMax ∧ (M0 (at_ A ArticleProg.xLen)).toNat ≤ artMax
  · obtain ⟨hlen, hR, hall, htab, hkd, hlw, hctx, hGr, hgram, hgm⟩ := h0 c0.1 c0.2.1 c0.2.2.1 c0.2.2.2
    refine frag_append (xs := [_]) (run0 o hA hD hT hcode hla hfr c0 hlen hR hall htab hkd hb0 hlw hctx hGr hgram hgm)
      ?_
    refine frag_given (lowK_any _ (k := .skip) rfl) fun v m1 hret => ?_
    refine frag_append (xs := [_]) (skip1 hfr (by rw [c0.1]; simp)) ?_
    refine frag_append (xs := [_]) (skip2 hfr (by rw [c0.1]; simp)) ?_
    exact hmid v m1 hret.1 fun mf e => by
      unfold RoundRet; rw [if_neg c3, if_pos c0]; rw [if_neg c3] at e; exact ⟨v, m1, hret, e⟩
  refine frag_append (xs := [_]) (skip0 hD hla hfr c0) ?_
  by_cases c1 : M0 (at_ A ArticleProg.xMode) = 1 ∧ (M0 (at_ A ArticleProg.xWall)).toNat < ArticleProg.wallMax
  · refine frag_append (xs := [_]) (run1 o hA hD hcode hla hfr c1 (h1 c1.1 c1.2) hb0 rfl) ?_
    refine frag_given (lowK_any _ (k := .skip) rfl) fun v m ⟨hv, f, m1, hret, hm⟩ => ?_
    have hbm : m (at_ A aBroken) = 0 := by
      rw [hm, upd_ne _ (show at_ A aBroken ≠ at_ A ArticleProg.xOutLen from broken_ne_w (i := 12) (by decide) A),
        hret.2.1 _ DN.News.ArticleOut.broken_out, hb0]
    refine frag_append (xs := [_]) (skip2 hfr (by rw [c1.1]; simp)) ?_
    exact hmid v m hbm fun mf e => by
      unfold RoundRet; rw [if_neg c3, if_neg c0, if_pos c1]; rw [if_neg c3, hm, hv] at e; exact ⟨f, m1, hret, e⟩
  refine frag_append (xs := [_]) (skip1 hfr c1) ?_
  by_cases c2 : M0 (at_ A ArticleProg.xMode) = 2 ∧ (M0 (at_ A ArticleProg.xLen)).toNat ≤ artMax
  · obtain ⟨hP, hlen, hlw, hin⟩ := h2 c2.1 c2.2
    refine frag_append (xs := [_]) (run2 o hA hD hcode hfr c2 hP hb0 hlen hin hlw) ?_
    refine frag_given (lowK_any _ (k := .skip) rfl) fun v m ⟨d, hret, hv⟩ => ?_
    exact hmid v m (by rw [hret.1 _ (DN.News.ArticleDateRun.not_scratch_low hbS), hb0]) fun mf e => by
      unfold RoundRet; rw [if_neg c3, if_neg c0, if_neg c1, if_pos c2]; rw [if_neg c3, hv] at e
      exact ⟨d, m, hret, e⟩
  refine frag_append (xs := [_]) (skip2 hfr c2) ?_
  exact hmid _ M0 hb0 fun mf e => by
    unfold RoundRet; rw [if_neg c3, if_neg c0, if_neg c1, if_neg c2]; rw [if_neg c3] at e; exact e

/-! ## What a round keeps -/

theorem low_ne {A : Word} {z y : Nat} (hz : z < ArticleProg.xFirst) (hy : ArticleProg.xFirst ≤ y) (hy2 : y < 2 ^ 40) :
    at_ A y ≠ at_ A z := by
  have := xFirst_eq; exact DN.News.ScanRun.at_ne (by omega) (by omega) (by omega)

theorem w_ne {A : Word} {i y : Nat} (hi : i < 32) (hy : ArticleProg.xFirst ≤ y) (hy2 : y < 2 ^ 40) :
    at_ A y ≠ at_ A (ArticleProg.w i) := low_ne (w_lt hi) hy hy2

theorem not_ctxScr {A : Word} {y : Nat} (hy : ArticleProg.xFirst ≤ y) (hy2 : y < 2 ^ 40) :
    ¬DN.News.ArticleContext.CtxScr A (at_ A y) := by
  have hX := X_val; have hF := xFirst_eq; have hs := sets_le_X
  have hio : aIO < aSets := Nat.lt_of_le_of_lt DN.News.AbnfLayout.io_le
    (Nat.lt_of_lt_of_le (Nat.lt_add_of_pos_right (by decide)) DN.News.AbnfLayout.pow_lt)
  rintro (⟨z, -, h2, e⟩ | ⟨k, hk, hin⟩ | e | he)
  · exact low_ne (by omega) hy hy2 e
  · exact DN.News.ArticleFields.notInSlot_high hk (by omega) hy2 hin
  · exact low_ne (z := aLen) (by have : aLen = 8 := rfl; omega) hy hy2 e
  · obtain ⟨z, -, h2, e⟩ := DN.News.ArticleCheck.g_at (.inl he)
    exact low_ne h2 hy hy2 e

theorem not_checkScr {A : Word} {y : Nat} (hy : ArticleProg.xFlags esP ≤ y) (hy2 : y < 2 ^ 40) :
    ¬DN.News.ArticleCheck.CheckScr A (at_ A y) := by
  have hl := (DN.News.ArticleTables.lay esP).1
  have hF := xFirst_eq; have hM : ArticleProg.xName + ArticleProg.nameCap = 506416 := rfl
  have hy1 : ArticleProg.xFirst ≤ y := by omega
  rintro (h | h | h | ⟨z, -, h2, e⟩ | ⟨i, hi, e⟩)
  · exact DN.News.ArticleFields.not_chk (.inr (hl ▸ hy)) hy2 (by have : aLen = 8 := rfl; omega) h
  · obtain ⟨z, -, h2, e⟩ := DN.News.ArticleCheck.g_at h
    exact low_ne h2 hy1 hy2 e
  · exact DN.News.ArticleAdded.high_add hy1 hy2 h
  · exact low_ne (by omega) hy1 hy2 e
  · exact w_ne (by omega) hy1 hy2 e

theorem not_outScr {A : Word} {y : Nat} (hy : ArticleProg.xFirst ≤ y) (hy2 : y < 2 ^ 40) :
    ¬DN.News.ArticleOut.OutScr A (at_ A y) := fun ⟨_, _, h2, e⟩ => low_ne h2 hy hy2 e

theorem not_dateScr {A : Word} {y : Nat} (hy : ArticleProg.xFirst ≤ y) (hy2 : y < 2 ^ 40) :
    ¬DN.News.ArticleDateRun.scratch A (at_ A y) := by
  have hT := DN.News.ArticleScan.xTok_eq; have hF := xFirst_eq
  rintro (e | e | e | e | e)
  · exact w_ne (i := 19) (by decide) hy hy2 e
  · exact w_ne (i := 20) (by decide) hy hy2 e
  · exact w_ne (i := 25) (by decide) hy hy2 e
  · exact w_ne (i := 15) (by decide) hy hy2 e
  · exact low_ne (by omega) hy hy2 e

/-- **A round keeps every word from the flags' table on**: those of the entries' tables. -/
theorem roundRet_hi {A : Word} {dm : Word → Bool} {be : Bool} {ctx : ArticleSpec.Context} {a : Bytes}
    {m0 m : Word → Word} (h : RoundRet A dm be ctx a m0 m) {y : Nat} (hy : ArticleProg.xFlags esP ≤ y)
    (hy2 : y < 2 ^ 40) : m (at_ A y) = m0 (at_ A y) := by
  have hy1 : ArticleProg.xFirst ≤ y := by have := (DN.News.ArticleTables.lay esP).1; omega
  have hv : at_ A y ≠ at_ A ArticleProg.xVerdict := w_ne (i := 10) (by decide) hy1 hy2
  unfold RoundRet at h
  split at h
  · obtain ⟨v, m1, hr, rfl⟩ := h
    rw [upd_ne _ hv, upd_ne _ (show at_ A y ≠ at_ A ArticleProg.xCtxOk from w_ne (i := 9) (by decide) hy1 hy2),
      hr.2.2.1 _ (not_ctxScr hy1 hy2)]
  split at h
  · obtain ⟨v, m1, hr, rfl⟩ := h
    rw [upd_ne _ hv, hr.2.1 _ (not_checkScr hy hy2)]
  split at h
  · obtain ⟨f, m1, hr, rfl⟩ := h
    rw [upd_ne _ hv, upd_ne _ (show at_ A y ≠ at_ A ArticleProg.xOutLen from w_ne (i := 12) (by decide) hy1 hy2),
      hr.2.1 _ (not_outScr hy1 hy2)]
  split at h
  · obtain ⟨d, m1, hr, rfl⟩ := h
    rw [upd_ne _ hv, hr.1 _ (not_dateScr hy1 hy2)]
  rw [h, upd_ne _ hv]

/-- **The entries' tables kept** by `dn_next` and by a round. -/
theorem tables_kept {A : Word} (hA8 : A.toNat % 8 = 0) {dm : Word → Bool} {be : Bool} {m m' : Word → Word}
    (hk : ∀ y, ArticleProg.xFlags esP ≤ y → y < 2 ^ 40 → m' (at_ A y) = m (at_ A y))
    (ht : TablesAt A dm be m esP) (hkd : DN.News.ArticleTables.KindsAt ArticleSpec.spec esP A m) :
    TablesAt A dm be m' esP ∧ DN.News.ArticleTables.KindsAt ArticleSpec.spec esP A m' :=
  ⟨DN.News.ArticleFields.tablesAt_hi hA8 esP_size hk ht, DN.News.ArticleFields.kindsAt_hi esP_size hk hkd⟩

/-! ## The premises can hold -/

/-- A request of no mode: 255 its answer. -/
theorem roundRet_witness : RoundRet 0 (fun _ => true) false
    { groups := [], identity := [], wall := 0, seq := 0, random := [], run := 0, conn := 0 } [] (fun _ => 5)
    (upd (fun _ => 5) (at_ 0 ArticleProg.xVerdict) 255) := by
  unfold RoundRet; rw [if_neg (by decide), if_neg (by decide), if_neg (by decide), if_neg (by decide)]

end DN.News.ArticleMain
