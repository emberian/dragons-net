-- SPDX-License-Identifier: AGPL-3.0-or-later
import DN.News.ArticleOut
import DN.News.ArticleTables

/-!
# DN.News.ArticleAdded

`artAdded` as the program holds it. If it returns, it writes the header section `ArticleSpec.added` makes, and the
message identifier.
-/

namespace DN.News.ArticleAdded

open DN.News.ArticleSpec (Bytes Field)
open DN.News.ArticleLines (seg seg_app seg_length Lines cont groups fieldOf segs)
open DN.News.FrameSpec (CR LF)
open DN.Compiler DN.Compiler.Wp DN.Compiler.WpRet DN.Compiler.Frag DN.News.AbnfProg
open DN.News.AbnfSets DN.News.FunRun DN.News.AbnfLeaves DN.News.ArticleRun DN.News.ArticleScan
open DN.News.ArticleDateRun DN.News.ArticleDateOk DN.News.ArticleListRun DN.News.ArticleOut
open DN.News.ScanRun (at_ at_add vals_lookup without Fresh)
open DN.News.FramerCode (bw ev_var bw_ne0 bw_eq0)
open DN.News.ArticleProg (artMax guardL guardS ifs wd setW codes)
open Syntax (v n eEq eLt eLe eAnd eAdd eSub eMul)

open DN.News.ArticleTables (esP esL es_eq)

variable {σ : Type}

/-! ## A field's bytes -/

/-- A line and its CRLF are the bytes up to the next line. -/
theorem line_crlf {a : Bytes} {s e p : Nat} {L : List (Nat × Nat)} (h : Lines a s ((s, e) :: L) p) {x : Nat}
    (hx : x ≤ e) : seg a x e ++ DN.News.CommandSpec.crlf = seg a x (e + 2) := by
  cases h with
  | line he hlt hne hL =>
    have hf := DN.News.ArticleLines.eolOf_found a (q := s) (lim := a.length) (by rw [he]; exact hlt)
    rw [he] at hf
    obtain ⟨hc, h1⟩ := hf
    simp only [DN.News.ArticleLines.crlfAt, Bool.and_eq_true, beq_iff_eq] at hc
    rw [seg_app a hx (Nat.le_add_right e 2), DN.News.ArticleLines.seg_succ a (by omega) (by omega),
      DN.News.ArticleLines.seg_succ a (by omega) (by omega), DN.News.ArticleLines.seg_self]
    rw [List.getElem?_eq_getElem (by omega)] at hc
    rw [List.getElem?_eq_getElem (by omega)] at hc
    simp only [Option.some.injEq] at hc
    rw [hc.1, hc.2]; rfl

theorem line_le {a : Bytes} {s e p : Nat} {L : List (Nat × Nat)} (h : Lines a s ((s, e) :: L) p) : s ≤ e := by
  cases h with
  | line he hlt _ _ =>
    have := DN.News.ArticleLines.eolOf_low a (q := s) (lim := a.length) (by rw [he]; exact hlt)
    rw [he] at this; exact this

/-- **A field's text is the input's bytes** from its first line to the next field's. -/
theorem text_seg {a : Bytes} {sep : Nat} : ∀ (L : List (Nat × Nat)) (s e : Nat), Lines a s ((s, e) :: L) sep →
    (((s, e) :: L.takeWhile (cont a)).map fun q => seg a q.1 q.2 ++ DN.News.CommandSpec.crlf).flatten =
      seg a s (DN.News.ArticleLines.nextOf a L sep)
  | [], s, e, h => by
    have hl := line_crlf h (line_le h)
    obtain ⟨-, hL⟩ := DN.News.ArticleLines.lines_tail h
    cases hL with
    | sep _ _ => simp [hl, DN.News.ArticleLines.nextOf_nil]
  | (q, eq) :: L, s, e, h => by
    have hl := line_crlf h (line_le h)
    obtain ⟨-, hL⟩ := DN.News.ArticleLines.lines_tail h
    obtain ⟨hq, -⟩ := DN.News.ArticleLines.lines_tail hL
    simp only at hq
    subst hq
    cases hc : cont a (e + 2, eq)
    · simp only [List.takeWhile_cons, hc, Bool.false_eq_true, if_false, List.map_cons, List.map_nil,
        List.flatten_cons, List.flatten_nil, List.append_nil, hl, DN.News.ArticleLines.nextOf_stop hc]
    · have ih := text_seg L (e + 2) eq hL
      have hge := (DN.News.ArticleLines.nextOf_ge hL).1
      have hse : s ≤ e + 2 := by have := line_le h; omega
      simp only [List.takeWhile_cons, hc, if_true, List.map_cons, List.flatten_cons] at ih ⊢
      rw [DN.News.ArticleLines.nextOf_cont hc] at hge
      rw [DN.News.ArticleLines.nextOf_cont hc, ← List.append_assoc, hl, List.append_assoc, ih, ← seg_app a hse hge]

/-- **A field's body after `x` is the input's bytes** up to its last line's end. -/
theorem rest_seg {a : Bytes} {sep : Nat} : ∀ (L : List (Nat × Nat)) (s e x : Nat), Lines a s ((s, e) :: L) sep →
    x ≤ e → seg a x e ++ ((L.takeWhile (cont a)).map fun q => DN.News.CommandSpec.crlf ++ seg a q.1 q.2).flatten =
      seg a x (DN.News.ArticleLines.nextOf a L sep - 2)
  | [], s, e, x, h, hx => by
    obtain ⟨-, hL⟩ := DN.News.ArticleLines.lines_tail h
    cases hL with
    | sep _ _ => simp [DN.News.ArticleLines.nextOf_nil]
  | (q, eq) :: L, s, e, x, h, hx => by
    obtain ⟨-, hL⟩ := DN.News.ArticleLines.lines_tail h
    obtain ⟨hq, hL'⟩ := DN.News.ArticleLines.lines_tail hL
    simp only at hq hL'
    subst hq
    cases hc : cont a (e + 2, eq)
    · simp only [List.takeWhile_cons, hc, Bool.false_eq_true, if_false, List.map_nil, List.flatten_nil,
        List.append_nil, DN.News.ArticleLines.nextOf_stop hc, Nat.add_sub_cancel]
    · have ih := rest_seg L (e + 2) eq (e + 2) hL (line_le hL)
      have hge := (DN.News.ArticleLines.nextOf_ge hL').1
      have hle := line_le hL
      simp only [List.takeWhile_cons, hc, if_true, List.map_cons, List.flatten_cons]
      rw [DN.News.ArticleLines.nextOf_cont hc, ← List.append_assoc, ← List.append_assoc, line_crlf h hx,
        List.append_assoc, ih, ← seg_app a (by omega) (by omega)]

/-! ## Path's entry -/

/-- **A name's entry is entry `k` exactly when it is `k`'s**, no entry before `k` spelled as it is. -/
theorem class_k {l : List String} {k : Nat} (hk : k < l.length)
    (hpre : ∀ j (hj : j < k), DN.News.ArticleRun.lowCodes (l.get ⟨j, Nat.lt_trans hj hk⟩) ≠
      DN.News.ArticleRun.lowCodes (l.get ⟨k, hk⟩)) (name : Bytes) :
    decide (DN.News.ArticleRun.classOf l name ≠ k) = !DN.News.ArticleRun.entryIs (l.get ⟨k, hk⟩) name := by
  cases hm : DN.News.ArticleRun.entryIs (l.get ⟨k, hk⟩) name
  · have : DN.News.ArticleRun.classOf l name ≠ k := fun e => by
      unfold DN.News.ArticleRun.classOf at e
      cases hf : l.findIdx? (DN.News.ArticleRun.entryIs · name) with
      | none => rw [hf, Option.getD_none] at e; omega
      | some i =>
        rw [hf, Option.getD_some] at e
        subst e
        obtain ⟨_, h2, -⟩ := List.findIdx?_eq_some_iff_getElem.1 hf
        have : DN.News.ArticleRun.entryIs (l.get ⟨i, hk⟩) name = true := h2
        rw [hm] at this; exact absurd this (by decide)
    simp [this]
  · have : DN.News.ArticleRun.classOf l name = k := DN.News.ArticleRun.classOf_eq hk (fun j hj => by
      have hm' := hm
      unfold DN.News.ArticleRun.entryIs at hm' ⊢
      rw [beq_iff_eq] at hm'
      rw [hm', beq_eq_false_iff_ne]
      exact fun e => hpre j hj e.symm) hm
    simp [this]

theorem path_entry : ArticleProg.entryOf esP "Path" = 21 := by rw [es_eq]; decide +kernel
theorem path_lt : 21 < esL.length := by decide
theorem path_codes :
    DN.News.ArticleRun.lowCodes (esL.get ⟨21, path_lt⟩) =
      (DN.News.CommandSpec.ascii "Path").map ArticleSpec.lowerB := by
  decide +kernel
theorem path_first : ∀ j (hj : j < 21), DN.News.ArticleRun.lowCodes (esL.get ⟨j, Nat.lt_trans hj path_lt⟩) ≠
    DN.News.ArticleRun.lowCodes (esL.get ⟨21, path_lt⟩) := by
  decide +kernel

/-- **A field's entry is Path's exactly when its name is Path**, read without case. -/
theorem class_path (name : Bytes) :
    decide (DN.News.ArticleRun.classOf esP name ≠ 21) = !ArticleSpec.named name "Path" := by
  rw [es_eq, class_k path_lt path_first name]
  unfold ArticleSpec.named ArticleSpec.sameName DN.News.ArticleRun.entryIs; rw [path_codes]

/-! ## Calls -/

theorem mem_artClass : gd (ArticleProg.artClass esP .none) ∈ ArticleProg.functions ArticleSpec.spec esP .none :=
  List.mem_append_right _ (List.mem_map.2 ⟨ArticleProg.artClass esP .none, by simp, rfl⟩)

/-- **A call of `artClass`**: the entry of the name of `NL` bytes at `P`, the memory as it was. -/
theorem classCall_frag (o : Oracle σ) {R : Ret} {A : Word} {s0 : PancakeState σ} (hA : Area ArticleProg.ofs A s0)
    (hcode : ArtCode s0.code) {rt : String} (hra : rt ≠ "a") {l : List (String × Value)}
    (hla : l.lookup "a" = some A) (hrt : Fresh rt l = true) {m0 : Word → Word} (hb : m0 (at_ A aBroken) = 0)
    (hT : TabDom A s0.memaddrs esP) (htab : TablesAt A s0.memaddrs s0.be m0 esP) (hes : ∀ s ∈ esP, s.length ≤ 64)
    (hsz : ArticleProg.size esP < 2 ^ 40) {a : Bytes} (hin : InputAt m0 s0.memaddrs s0.be A a)
    (hlen : a.length ≤ artMax)
    {P NL : Nat} (hPN : P + NL ≤ a.length) {e1 e2 : Syntax.PExpr} {E1 E2 : PancakeExp}
    (he1 : Lower.lowerExp e1 = some E1) (he2 : Lower.lowerExp e2 = some E2)
    (hv1 : ∀ u, RunF s0 l (· = m0) u → eval u E1 = some (BitVec.ofNat 64 P))
    (hv2 : ∀ u, RunF s0 l (· = m0) u → eval u E2 = some (BitVec.ofNat 64 NL)) :
    FragR o R (guardS (.call rt "artClass" [e1, e2])) (RunF s0 l (· = m0))
      (RunF s0 ((rt, BitVec.ofNat 64 (classOf esP (seg a P (P + NL)))) :: l) (· = m0)) := by
  refine fragR_conseq (gcall_frag o hA hcode hra (f := ArticleProg.artClass esP .none) mem_artClass (by decide)
    (DN.News.AbnfGen.lowerArgs_two he1 he2) hla (vs := [BitVec.ofNat 64 P, BitVec.ofNat 64 NL]) rfl
    (fun u h => by simp only [evalArgs, hv1 u h, hv2 u h]) (Rf := ClassRet esP (seg a P (P + NL)))
    (fun s1 hA1 _ hm hbe hloc hF => by
      have := artClass_ok o hA1 (by rw [hm]; exact hT) (by rw [hF, hm, hbe]; exact htab) hes hsz
        (by rw [hF, hm, hbe]; exact hin) hlen hPN ((hloc "p").trans rfl) ((hloc "nl").trans rfl)
      exact this) hrt
    (G := fun w m => m = m0 ∧ w = BitVec.ofNat 64 (classOf esP (seg a P (P + NL))))
    (fun m m' w hm hr => ⟨hr.1.trans hm, hr.2⟩) fun w m h => by rw [h.1]; exact hb) (fun u h => h)
    fun u ⟨w, h⟩ => ?_
  obtain ⟨hm, hw⟩ := h.2
  subst hw; exact ⟨h.1, hm⟩

theorem mem_artCopy : gd (ArticleProg.artCopy esP .none) ∈ ArticleProg.functions ArticleSpec.spec esP .none :=
  List.mem_append_right _ (List.mem_map.2 ⟨ArticleProg.artCopy esP .none, by simp, rfl⟩)

/-- **A call of `artCopy`**, the check after it passed: `SRC` after the output `OUT`, the place past it. -/
theorem copyCall_frag (o : Oracle σ) {R : Ret} {A : Word} {s0 : PancakeState σ} (hA : Area ArticleProg.ofs A s0)
    (hD : ArtDom A s0.memaddrs) (hcode : ArtCode s0.code) (hsz : ArticleProg.size esP < 2 ^ 40) {rt : String}
    (hra : rt ≠ "a") {l : List (String × Value)} (hla : l.lookup "a" = some A) (hrt : Fresh rt l = true)
    {m0 : Word → Word} (hb : m0 (at_ A aBroken) = 0) {OUT SRC : Bytes}
    (hO : BytesAt A s0.memaddrs s0.be ArticleProg.xOut ArticleProg.outMax OUT m0) {S : Nat}
    (hS : BytesAt A s0.memaddrs s0.be S SRC.length SRC m0) (hSd : S + SRC.length ≤ ArticleProg.xDec)
    (hfit : OUT.length + SRC.length ≤ ArticleProg.outMax) {e1 e2 e3 : Syntax.PExpr} {E1 E2 E3 : PancakeExp}
    (he1 : Lower.lowerExp e1 = some E1) (he2 : Lower.lowerExp e2 = some E2) (he3 : Lower.lowerExp e3 = some E3)
    (hv1 : ∀ u, RunF s0 l (· = m0) u → eval u E1 = some (BitVec.ofNat 64 OUT.length))
    (hv2 : ∀ u, RunF s0 l (· = m0) u → eval u E2 = some (BitVec.ofNat 64 S))
    (hv3 : ∀ u, RunF s0 l (· = m0) u → eval u E3 = some (BitVec.ofNat 64 SRC.length)) :
    FragR o R (guardS (.call rt "artCopy" [e1, e2, e3])) (RunF s0 l (· = m0))
      (fun u => ∃ m, RunF s0 ((rt, BitVec.ofNat 64 (OUT.length + SRC.length)) :: l) (· = m) u ∧
        (∀ x, ¬OutScr A x → m x = m0 x) ∧
        BytesAt A s0.memaddrs s0.be ArticleProg.xOut ArticleProg.outMax (OUT ++ SRC) m) := by
  refine fragR_conseq (gcall_frag o hA hcode hra (f := ArticleProg.artCopy esP .none) mem_artCopy (by decide)
    (args := [E1, E2, E3]) (by simp [Lower.lowerArgs, he1, he2, he3]) hla
    (vs := [BitVec.ofNat 64 OUT.length, BitVec.ofNat 64 S, BitVec.ofNat 64 SRC.length]) rfl
    (fun u h => by simp only [evalArgs, hv1 u h, hv2 u h, hv3 u h])
    (Rf := CopyRet A s0.memaddrs s0.be OUT SRC)
    (fun s1 hA1 _ hm hbe hloc hF => by
      have := artCopy_ok o hsz hA1 (by rw [hm]; exact hD) (by rw [hF, hm, hbe]; exact hO)
        (by rw [hF, hm, hbe]; exact hS) hSd hfit ((hloc "o").trans rfl) ((hloc "src").trans rfl)
        ((hloc "len").trans rfl)
      rw [hm, hbe] at this; exact this) hrt
    (G := fun w m => w = BitVec.ofNat 64 (OUT.length + SRC.length) ∧ (∀ x, ¬OutScr A x → m x = m0 x) ∧
      BytesAt A s0.memaddrs s0.be ArticleProg.xOut ArticleProg.outMax (OUT ++ SRC) m)
    (fun m m' w hm hr => by subst hm; exact hr)
    fun w m h => by rw [h.2.1 _ broken_out]; exact hb) (fun u h => h) fun u ⟨w, h⟩ => ?_
  obtain ⟨hw, hfr, hout⟩ := h.2
  subst hw; exact ⟨u.memory, ⟨h.1, rfl⟩, hfr, hout⟩

/-- The failed flag is none of the message identifier's words. -/
theorem broken_msg {A : Word} : ¬MsgScr A (at_ A aBroken) := fun h => by
  have := broken_low; have := sets_le_X; have := X_val; have := xMsg_eq
  rcases h with e | ⟨z, h1, h2, e⟩
  · exact broken_ne_w (i := 13) (by decide) A e
  · have := DN.News.ScanRun.at_inj (by omega) (by simp only [ArticleProg.msgCap] at h2; omega) e; omega

theorem mem_artToMsg : gd (ArticleProg.artToMsg esP) ∈ ArticleProg.functions ArticleSpec.spec esP .none :=
  List.mem_append_right _ (List.mem_map.2 ⟨ArticleProg.artToMsg esP, by simp, rfl⟩)

/-- **A call of `artToMsg`**, the check after it passed: `SRC` as the message identifier, its length in `xMsgLen`. -/
theorem msgCall_frag (o : Oracle σ) {R : Ret} {A : Word} {s0 : PancakeState σ} (hA : Area ArticleProg.ofs A s0)
    (hD : ArtDom A s0.memaddrs) (hcode : ArtCode s0.code) (hsz : ArticleProg.size esP < 2 ^ 40) {rt : String}
    (hra : rt ≠ "a") {l : List (String × Value)} (hla : l.lookup "a" = some A) (hrt : Fresh rt l = true)
    {m0 : Word → Word} (hb : m0 (at_ A aBroken) = 0) {SRC : Bytes} {S : Nat}
    (hS : BytesAt A s0.memaddrs s0.be S SRC.length SRC m0) (hSz : S + SRC.length ≤ ArticleProg.size esP)
    (hSm : S + SRC.length ≤ ArticleProg.X ∨ ArticleProg.xMsg + ArticleProg.msgCap ≤ S)
    (hSl : SRC.length < ArticleProg.msgCap) {e1 e2 : Syntax.PExpr} {E1 E2 : PancakeExp}
    (he1 : Lower.lowerExp e1 = some E1) (he2 : Lower.lowerExp e2 = some E2)
    (hv1 : ∀ u, RunF s0 l (· = m0) u → eval u E1 = some (BitVec.ofNat 64 S))
    (hv2 : ∀ u, RunF s0 l (· = m0) u → eval u E2 = some (BitVec.ofNat 64 SRC.length)) :
    FragR o R (guardS (.call rt "artToMsg" [e1, e2])) (RunF s0 l (· = m0))
      (fun u => ∃ w m, RunF s0 ((rt, w) :: l) (· = m) u ∧ MsgRet A s0.memaddrs s0.be SRC m0 w m) := by
  refine fragR_conseq (gcall_frag o hA hcode hra (f := ArticleProg.artToMsg esP) mem_artToMsg (by decide)
    (DN.News.AbnfGen.lowerArgs_two he1 he2) hla (vs := [BitVec.ofNat 64 S, BitVec.ofNat 64 SRC.length]) rfl
    (fun u h => by simp only [evalArgs, hv1 u h, hv2 u h]) (Rf := MsgRet A s0.memaddrs s0.be SRC)
    (fun s1 hA1 _ hm hbe hloc hF => by
      have := artToMsg_ok o hsz hA1 (by rw [hm]; exact hD) (by rw [hF, hm, hbe]; exact hS) hSz hSm hSl
        ((hloc "src").trans rfl) ((hloc "len").trans rfl)
      rw [hm, hbe] at this; exact this) hrt
    (G := MsgRet A s0.memaddrs s0.be SRC m0) (fun m m' w hm hr => by subst hm; exact hr)
    fun w m h => by rw [h.1 _ broken_msg]; exact hb) (fun u h => h) fun u ⟨w, h⟩ => ⟨w, u.memory, ⟨h.1, rfl⟩, h.2⟩

theorem mem_artMsgIds : gd (ArticleProg.artMsgIds ArticleSpec.spec .none) ∈
    ArticleProg.functions ArticleSpec.spec esP .none :=
  List.mem_append_right _ (List.mem_map.2 ⟨ArticleProg.artMsgIds ArticleSpec.spec .none, by simp, rfl⟩)

/-- **A call of `artMsgIds`**, the check after it passed. It returns whether an identifier is too long. The first
one's place and length are in `xMsgS` and `xMsgL`. -/
theorem idsCall_frag (o : Oracle σ) {R : Ret} {A : Word} {s0 : PancakeState σ} (hA : Area ArticleProg.ofs A s0)
    (hD : ArtDom A s0.memaddrs) (hcode : ArtCode s0.code) {rt : String} (hra : rt ≠ "a") {l : List (String × Value)}
    (hla : l.lookup "a" = some A) (hrt : Fresh rt l = true) {m0 : Word → Word} (hb : m0 (at_ A aBroken) = 0)
    {a : Bytes} (hlen : a.length ≤ artMax) (hin : InputAt m0 s0.memaddrs s0.be A a) {S E : Nat} (hSE : S ≤ E)
    (hE : E ≤ a.length) {e1 e2 : Syntax.PExpr} {E1 E2 : PancakeExp}
    (he1 : Lower.lowerExp e1 = some E1) (he2 : Lower.lowerExp e2 = some E2)
    (hv1 : ∀ u, RunF s0 l (· = m0) u → eval u E1 = some (BitVec.ofNat 64 S))
    (hv2 : ∀ u, RunF s0 l (· = m0) u → eval u E2 = some (BitVec.ofNat 64 E)) :
    FragR o R (guardS (.call rt "artMsgIds" [e1, e2])) (RunF s0 l (· = m0))
      (fun u => ∃ w m, RunF s0 ((rt, w) :: l) (· = m) u ∧ IdsRet ArticleSpec.spec.idMax A a S E m0 w m) := by
  have hbw : ∀ (w1 w2 : Word),
      upd (upd m0 (at_ A ArticleProg.xMsgS) w1) (at_ A ArticleProg.xMsgL) w2 (at_ A aBroken) = 0 := fun w1 w2 =>
    (upd_ne _ (broken_ne_w (i := 24) (by decide) A)).trans ((upd_ne _ (broken_ne_w (i := 23) (by decide) A)).trans hb)
  refine fragR_conseq (gcall_frag o hA hcode hra (f := ArticleProg.artMsgIds ArticleSpec.spec .none) mem_artMsgIds
    (by decide) (DN.News.AbnfGen.lowerArgs_two he1 he2) hla (vs := [BitVec.ofNat 64 S, BitVec.ofNat 64 E]) rfl
    (fun u h => by simp only [evalArgs, hv1 u h, hv2 u h]) (Rf := IdsRet ArticleSpec.spec.idMax A a S E)
    (fun s1 hA1 _ hm hbe hloc hF => artMsgIds_ok o (by decide) hA1 (by rw [hm]; exact hD) hlen
      (by rw [hF, hm, hbe]; exact hin) hSE hE ((hloc "s").trans rfl) ((hloc "e").trans rfl)) hrt
    (G := IdsRet ArticleSpec.spec.idMax A a S E m0) (fun m m' w hm hr => by subst hm; exact hr)
    fun w m h => by obtain ⟨-, w1, w2, hm, -⟩ := h; rw [hm]; exact hbw w1 w2) (fun u h => h)
    fun u ⟨w, h⟩ => ⟨w, u.memory, ⟨h.1, rfl⟩, h.2⟩

theorem mem_artFormat : gd ArticleProg.artFormat ∈ ArticleProg.functions ArticleSpec.spec esP .none :=
  List.mem_append_right _ (List.mem_map.2 ⟨ArticleProg.artFormat, by simp, rfl⟩)

/-- **A call of `artFormat`**, the check after it passed: the wall clock's date after the output `OUT`. -/
theorem fmtCall_frag (o : Oracle σ) {R : Ret} {A : Word} {s0 : PancakeState σ} (hA : Area ArticleProg.ofs A s0)
    (hD : ArtDom A s0.memaddrs) (hcode : ArtCode s0.code) {rt : String} (hra : rt ≠ "a") {l : List (String × Value)}
    (hla : l.lookup "a" = some A) (hrt : Fresh rt l = true) {m0 : Word → Word} (hP : Pows m0 A)
    (hb : m0 (at_ A aBroken) = 0) {OUT : Bytes}
    (hO : BytesAt A s0.memaddrs s0.be ArticleProg.xOut ArticleProg.outMax OUT m0) {wall : Nat}
    (hwall : wall < ArticleProg.wallMax) (hw : m0 (at_ A ArticleProg.xWall) = BitVec.ofNat 64 wall)
    (hfit : OUT.length + (ArticleSpec.formatDate wall).length ≤ ArticleProg.outMax)
    (ho : l.lookup "o" = some (BitVec.ofNat 64 OUT.length)) :
    FragR o R (guardS (.call rt "artFormat" [v "o"])) (RunF s0 l (· = m0))
      (fun u => ∃ m, RunF s0 ((rt, BitVec.ofNat 64 (OUT.length + (ArticleSpec.formatDate wall).length)) :: l)
        (· = m) u ∧ (∀ x, ¬OutScr A x → m x = m0 x) ∧
        BytesAt A s0.memaddrs s0.be ArticleProg.xOut ArticleProg.outMax (OUT ++ ArticleSpec.formatDate wall) m) := by
  refine fragR_conseq (gcall_frag o hA hcode hra (f := ArticleProg.artFormat) mem_artFormat (by decide)
    (args := [.var "o"]) rfl hla (vs := [BitVec.ofNat 64 OUT.length]) rfl
    (fun u h => by simp only [evalArgs, ev_var (vals_lookup h.1.vals ho)]) (Rf := FmtRet A s0.memaddrs s0.be OUT wall)
    (fun s1 hA1 hc hm hbe hloc hF => by
      have := artFormat_ok o hA1 (by rw [hm]; exact hD) (by rw [hc]; exact hcode) (by rw [hF]; exact hP)
        (by rw [hF]; exact hb) (by rw [hF, hm, hbe]; exact hO) hwall (by rw [hF]; exact hw) hfit ((hloc "o").trans rfl)
      rw [hm, hbe] at this; exact this) hrt
    (G := fun w m => w = BitVec.ofNat 64 (OUT.length + (ArticleSpec.formatDate wall).length) ∧
      (∀ x, ¬OutScr A x → m x = m0 x) ∧
      BytesAt A s0.memaddrs s0.be ArticleProg.xOut ArticleProg.outMax (OUT ++ ArticleSpec.formatDate wall) m)
    (fun m m' w hm hr => by subst hm; exact hr)
    fun w m h => by rw [h.2.1 _ broken_out]; exact hb) (fun u h => h) fun u ⟨w, h⟩ => ?_
  obtain ⟨hw', hfr, hout⟩ := h.2
  subst hw'; exact ⟨u.memory, ⟨h.1, rfl⟩, hfr, hout⟩

/-! ## `artAdded`'s body -/

open ArticleProg (firstOf putConst xId xIdLen xRandLen xSep xRand xSeq xRun xConn xNl xE1 xMsgS xMsgL xMsgLen
  xOutLen xOut readIn isWS)

/-- Statements, the type list literals in `++` chains are given so that they elaborate at once. -/
abbrev Ss : Type := List Syntax.PStmt

/-- A copy into the output, the output's place moved past it. -/
def copyS (name : String) (src len : Syntax.PExpr) : List Syntax.PStmt :=
  [.call name "artCopy" [v "o", src, len], .assign "o" (v name)]

/-- The date into the output. -/
def fmtS (name : String) : List Syntax.PStmt := [.call name "artFormat" [v "o"], .assign "o" (v name)]

/-- A number's digits into the output. -/
def numS (name : String) (x : Syntax.PExpr) : List Syntax.PStmt :=
  [.call name "artNum10" [v "o", x], .assign "o" (v name)]

/-- Whether the server adds Injection-Date, as the program asks it of the first fields. -/
def addDateE : Syntax.PExpr :=
  let combos := [false, true].flatMap fun i => [false, true].flatMap fun mi => [false, true].map (i, mi, ·)
  let flag (s : String) : Syntax.PExpr := eLe (n 0) (firstOf esP s)
  combos.foldl (fun acc (i, mi, d) =>
    if ArticleSpec.spec.injectionDate i mi d then
      Syntax.eOr acc (eAnd (eEq (flag "Injection-Date") (n i.toNat))
        (eAnd (eEq (flag "Message-ID") (n mi.toNat)) (eEq (flag "Date") (n d.toNat))))
    else acc) (n 0)

/-- Path's first line after the server's identity: the white space skipped, folded if too long, the rest copied. -/
def pathYes : List Syntax.PStmt :=
  ([.call "pf" "artField" [v "pp"], .dec "pn" (wd xNl), .dec "pe" (wd xE1),
   .dec "r0" (eAdd (eAdd (v "pp") (v "pn")) (n 1)), .dec "g" (n 1),
   .while (v "g")
     [.ite (eLt (v "r0") (v "pe"))
       (readIn "c" "r0" ++ ([.ite (isWS (v "c")) [inc "r0"] [.assign "g" (n 0)]] : Ss)) [.assign "g" (n 0)]],
   .ite (eLt (n ArticleSpec.spec.lineMax) (eAdd (n 15) (eAdd (v "idl") (eSub (v "pe") (v "r0")))))
     (putConst "\r\n !") (putConst "!")] : Ss) ++
  copyS "o2" (eAdd (n aInput) (v "r0")) (eSub (v "pe") (v "r0")) ++ putConst "\r\n" ++
  copyS "o3" (eAdd (n (aInput + 2)) (v "pe")) (eSub (v "pf") (eAdd (v "pe") (n 2)))

/-- The fields but Path copied. -/
def keptBody : List Syntax.PStmt :=
  [.call "fe" "artField" [v "p"], .call "ck" "artClass" [v "p", wd xNl],
   ifs (eAnd (ne (v "ck") (n (ArticleProg.entryOf esP "Path"))) (n 1))
     (copyS "o4" (eAdd (n aInput) (v "p")) (eSub (v "fe") (v "p"))),
   .assign "p" (v "fe")]

/-- A new message identifier written out and kept. -/
def newIdS : List Syntax.PStmt :=
  putConst "Message-ID: " ++ ([.dec "ms" (v "o")] : Ss) ++ putConst "<" ++ numS "o5" (wd xSeq) ++
    putConst "." ++
    copyS "o6" (n xRand) (v "rl") ++ putConst "@" ++ copyS "o7" (n xId) (v "idl") ++ putConst ">" ++
    ([.call "tm" "artToMsg" [eAdd (n xOut) (v "ms"), eSub (v "o") (v "ms")]] : Ss) ++ putConst "\r\n"

/-- The article's message identifier kept. -/
def oldIdS : List Syntax.PStmt :=
  [.call "hf" "artField" [v "hid"], .dec "hn" (wd xNl),
   .call "ml" "artMsgIds" [eAdd (eAdd (v "hid") (v "hn")) (n 1), eSub (v "hf") (n 2)],
   setW xMsgLen (n 0),
   ifs (eLe (n 0) (wd xMsgS)) [.call "tn" "artToMsg" [eAdd (n aInput) (wd xMsgS), wd xMsgL]]]

theorem artAdded_split : (ArticleProg.artAdded ArticleSpec.spec esP .none).body =
    ([areaAt ArticleProg.ofs, .dec "o" (n 0), .dec "idl" (wd xIdLen), kept "idl" 200, .dec "rl" (wd xRandLen),
     kept "rl" 16] : Ss) ++
    putConst "Path: " ++ copyS "o1" (n xId) (v "idl") ++ putConst "!.POSTED" ++
    ([.dec "pp" (firstOf esP "Path"), .ite (eLe (n 0) (v "pp")) pathYes (putConst "!not-for-mail\r\n"),
     .dec "sep" (wd xSep), .dec "p" (n 0), .while (eLt (v "p") (v "sep")) keptBody,
     .dec "hid" (firstOf esP "Message-ID"), .ite (eLt (v "hid") (n 0)) newIdS oldIdS,
     ifs (eLt (firstOf esP "Date") (n 0)) (putConst "Date: " ++ fmtS "o8" ++ putConst "\r\n")] : Ss) ++
    putConst "Injection-Info: " ++ copyS "o9" (n xId) (v "idl") ++ putConst "; logging-data=" ++
    numS "oa" (wd xRun) ++ putConst "." ++ numS "ob" (wd xConn) ++ putConst "\r\n" ++
    ([ifs addDateE (putConst "Injection-Date: " ++ fmtS "oc" ++ putConst "\r\n"),
     setW xOutLen (v "o"), .ret (n 0)] : Ss) := rfl

theorem guardS_ifs (c : Syntax.PExpr) (t : Ss) : guardS (ifs c t) = [.ite c (guardL t) []] := rfl
theorem guardS_ite (c : Syntax.PExpr) (t e : Ss) :
    guardS (.ite c t e) = [.ite c (guardL t) (guardL e)] := rfl
theorem guardS_while (c : Syntax.PExpr) (b : Ss) : guardS (.while c b) = [.while c (guardL b)] := rfl
theorem guardS_dec (x : String) (e : Syntax.PExpr) : guardS (.dec x e) = [.dec x e] := rfl

theorem g_head : guardL [areaAt ArticleProg.ofs, .dec "o" (n 0), .dec "idl" (wd xIdLen), kept "idl" 200,
    .dec "rl" (wd xRandLen), kept "rl" 16] = [areaAt ArticleProg.ofs, .dec "o" (n 0), .dec "idl" (wd xIdLen),
    kept "idl" 200, .dec "rl" (wd xRandLen), kept "rl" 16] := rfl

theorem g_mid : guardL ([.dec "pp" (firstOf esP "Path"),
    .ite (eLe (n 0) (v "pp")) pathYes (putConst "!not-for-mail\r\n"),
    .dec "sep" (wd xSep), .dec "p" (n 0), .while (eLt (v "p") (v "sep")) keptBody,
    .dec "hid" (firstOf esP "Message-ID"), .ite (eLt (v "hid") (n 0)) newIdS oldIdS,
    ifs (eLt (firstOf esP "Date") (n 0)) (putConst "Date: " ++ fmtS "o8" ++ putConst "\r\n")] : Ss) =
    ([.dec "pp" (firstOf esP "Path"), .ite (eLe (n 0) (v "pp")) (guardL pathYes) (putConst "!not-for-mail\r\n"),
     .dec "sep" (wd xSep), .dec "p" (n 0), .while (eLt (v "p") (v "sep")) (guardL keptBody),
     .dec "hid" (firstOf esP "Message-ID"), .ite (eLt (v "hid") (n 0)) (guardL newIdS) (guardL oldIdS),
     .ite (eLt (firstOf esP "Date") (n 0)) (putConst "Date: " ++ guardL (fmtS "o8") ++ putConst "\r\n") []] : Ss) := by
  rw [guardL_cons, guardL_cons, guardL_cons, guardL_cons, guardL_cons, guardL_cons, guardL_cons, guardL_cons,
    guardS_dec, guardS_ite, guardS_dec, guardS_dec, guardS_while, guardS_dec, guardS_ite, guardS_ifs,
    DN.News.ArticleGrammar.guardL_append, DN.News.ArticleGrammar.guardL_append, guardL_putConst, guardL_putConst,
    guardL_putConst]
  rfl

theorem g_tail : guardL ([ifs addDateE (putConst "Injection-Date: " ++ fmtS "oc" ++ putConst "\r\n"),
    setW xOutLen (v "o"), .ret (n 0)] : Ss) =
    ([.ite addDateE (putConst "Injection-Date: " ++ guardL (fmtS "oc") ++ putConst "\r\n") [], setW xOutLen (v "o"),
     .ret (n 0)] : Ss) := by
  rw [guardL_cons, guardS_ifs, DN.News.ArticleGrammar.guardL_append, DN.News.ArticleGrammar.guardL_append,
    guardL_putConst, guardL_putConst]
  rfl

theorem artAdded_body : guardL (ArticleProg.artAdded ArticleSpec.spec esP .none).body =
    ([areaAt ArticleProg.ofs, .dec "o" (n 0), .dec "idl" (wd xIdLen), kept "idl" 200, .dec "rl" (wd xRandLen),
     kept "rl" 16] : Ss) ++
    putConst "Path: " ++ guardL (copyS "o1" (n xId) (v "idl")) ++ putConst "!.POSTED" ++
    ([.dec "pp" (firstOf esP "Path"), .ite (eLe (n 0) (v "pp")) (guardL pathYes) (putConst "!not-for-mail\r\n"),
     .dec "sep" (wd xSep), .dec "p" (n 0), .while (eLt (v "p") (v "sep")) (guardL keptBody),
     .dec "hid" (firstOf esP "Message-ID"), .ite (eLt (v "hid") (n 0)) (guardL newIdS) (guardL oldIdS),
     .ite (eLt (firstOf esP "Date") (n 0)) (putConst "Date: " ++ guardL (fmtS "o8") ++ putConst "\r\n") []] : Ss) ++
    putConst "Injection-Info: " ++ guardL (copyS "o9" (n xId) (v "idl")) ++ putConst "; logging-data=" ++
    guardL (numS "oa" (wd xRun)) ++ putConst "." ++ guardL (numS "ob" (wd xConn)) ++ putConst "\r\n" ++
    ([.ite addDateE (putConst "Injection-Date: " ++ guardL (fmtS "oc") ++ putConst "\r\n") [],
     setW xOutLen (v "o"), .ret (n 0)] : Ss) := by
  rw [artAdded_split]
  simp only [DN.News.ArticleGrammar.guardL_append, guardL_putConst]
  rw [g_head, g_mid, g_tail]

/-! ## What `artAdded` reads and writes -/

/-- The context in the area. It holds the server's identity and the random value with their lengths. Then the
sequence number, the run, the connection and the wall clock. -/
def CtxAt (A : Word) (dm : Word → Bool) (be : Bool) (ctx : ArticleSpec.Context) (m : Word → Word) : Prop :=
  ctx.identity.length ≤ 200 ∧ m (at_ A xIdLen) = BitVec.ofNat 64 ctx.identity.length ∧
    BytesAt A dm be xId ctx.identity.length ctx.identity m ∧
  ctx.random.length ≤ 16 ∧ m (at_ A xRandLen) = BitVec.ofNat 64 ctx.random.length ∧
    BytesAt A dm be xRand ctx.random.length ctx.random m ∧
  ctx.seq < 2 ^ 64 ∧ m (at_ A xSeq) = BitVec.ofNat 64 ctx.seq ∧ ctx.run < 2 ^ 64 ∧
    m (at_ A xRun) = BitVec.ofNat 64 ctx.run ∧ ctx.conn < 2 ^ 64 ∧ m (at_ A xConn) = BitVec.ofNat 64 ctx.conn ∧
  ctx.wall < ArticleProg.wallMax ∧ m (at_ A ArticleProg.xWall) = BitVec.ofNat 64 ctx.wall

/-- The words `artAdded` and its callees write: the output's and digits', the message identifier's. Also the field's
name length and first line's end. Also the first identifier's place and length, and the output's length. -/
def AddScr (A : Word) (x : Word) : Prop :=
  OutScr A x ∨ MsgScr A x ∨ x = at_ A xNl ∨ x = at_ A xE1 ∨ x = at_ A xMsgS ∨ x = at_ A xMsgL ∨ x = at_ A xOutLen

theorem xId_eq : ArticleProg.xId = 505104 := rfl
theorem xRand_eq : ArticleProg.xRand = 505360 := rfl

/-- A word `artAdded` keeps: below the output's words, not a scalar word, not the message identifier's. -/
theorem not_addScr {A : Word} {y : Nat} (h1 : y < ArticleProg.X ∨ ArticleProg.xGroups ≤ y)
    (h3 : ¬(ArticleProg.xMsg ≤ y ∧ y < ArticleProg.xMsg + ArticleProg.msgCap)) (h2 : y < ArticleProg.xDec) :
    ¬AddScr A (at_ A y) := by
  have hX := X_val
  have hm := xMsg_eq
  have hmc : ArticleProg.msgCap = 256 := rfl
  have hg := xGroups_eq
  have hd := xDec_eq
  rw [hm, hmc] at h3
  rw [hX, hg] at h1
  rw [hd] at h2
  have hw : ∀ i, i < 32 → at_ A y ≠ at_ A (ArticleProg.w i) := fun i hi => by
    refine DN.News.ScanRun.at_ne (by omega) (w_lt64 hi) ?_
    simp only [ArticleProg.w]; omega
  rintro (h | h | h | h | h | h | h)
  · obtain ⟨z, h4, h5, e⟩ := h
    have := DN.News.ScanRun.at_inj (by omega) (by rw [xFirst_eq] at h5; omega) e
    rw [hd] at h4; omega
  · rcases h with e | ⟨z, h4, h5, e⟩
    · exact hw 13 (by decide) e
    · have := DN.News.ScanRun.at_inj (by omega) (by rw [hm, hmc] at h5; omega) e
      subst this; rw [hm] at h4; rw [hm, hmc] at h5; exact h3 ⟨h4, h5⟩
  · exact hw 17 (by decide) h
  · exact hw 18 (by decide) h
  · exact hw 23 (by decide) h
  · exact hw 24 (by decide) h
  · exact hw 12 (by decide) h

/-! ## The output written so far -/

/-- A set of words written: the output's at least, `artAdded`'s at most. -/
def Scr (A : Word) (S : Word → Prop) : Prop := (∀ x, OutScr A x → S x) ∧ ∀ x, S x → AddScr A x

theorem scr_not {A : Word} {S : Word → Prop} (hS : Scr A S) {x : Word} (h : ¬AddScr A x) : ¬S x :=
  fun hx => h (hS.2 x hx)

theorem scr_add {A : Word} : Scr A (AddScr A) := ⟨fun _ h => .inl h, fun _ h => h⟩
theorem scr_out {A : Word} : Scr A (OutScr A) := ⟨fun _ h => h, fun _ h => .inl h⟩

/-- The output written so far, `P`, with the locals `L`; every word outside `S` as `m0` holds it. -/
def AOut (S : Word → Prop) (s1 : PancakeState σ) (A : Word) (m0 : Word → Word) (L : List (String × Value))
    (P : Bytes) : Assn σ :=
  fun u => ∃ M, RunF s1 L (· = M) u ∧ BytesAt A s1.memaddrs s1.be ArticleProg.xOut ArticleProg.outMax P M ∧
    ∀ x, ¬S x → M x = m0 x

theorem aout_clock {S : Word → Prop} {s1 : PancakeState σ} {A : Word} {m0 : Word → Word} {L : List (String × Value)}
    {P : Bytes} :
    Safe.ClockFree (AOut S s1 A m0 L P) := fun u k ⟨M, h, hv⟩ => ⟨M, runF_clock _ _ _ u k h, hv⟩

theorem aout_of {S : Word → Prop} {s1 : PancakeState σ} {A : Word} {m0 : Word → Word} {L L' : List (String × Value)}
    {P : Bytes} {u : PancakeState σ} (h : AOut S s1 A m0 L P u) (hl : ∀ q ∈ L', L.lookup q.1 = some q.2) :
    AOut S s1 A m0 L' P u :=
  let ⟨M, hr, hv⟩ := h; ⟨M, runF_of hr hl, hv⟩

theorem aout_lift (o : Oracle σ) {R : Ret} {xs : List Syntax.PStmt} (hlow : LowKK xs) {S : Word → Prop}
    {s1 : PancakeState σ} {A : Word} {m0 : Word → Word} {L1 : List (String × Value)} {P1 : Bytes} {Q : Assn σ}
    (h : ∀ M, BytesAt A s1.memaddrs s1.be ArticleProg.xOut ArticleProg.outMax P1 M → (∀ x, ¬S x → M x = m0 x) →
      FragR o R xs (RunF s1 L1 (· = M)) Q) :
    FragR o R xs (AOut S s1 A m0 L1 P1) Q := by
  refine fragR_exists hlow fun M => ?_
  exact fragR_pure (BytesAt A s1.memaddrs s1.be ArticleProg.xOut ArticleProg.outMax P1 M ∧
    ∀ x, ¬S x → M x = m0 x) (fun u h => h.2) hlow fun ⟨hO, hfr⟩ =>
      fragR_conseq (h M hO hfr) (fun u h => h.1) fun _ h => h

theorem out_add {A : Word} {S : Word → Prop} {M M' m0 : Word → Word} (h1 : ∀ x, ¬OutScr A x → M' x = M x)
    (hS : ∀ x, OutScr A x → S x) (h2 : ∀ x, ¬S x → M x = m0 x) : ∀ x, ¬S x → M' x = m0 x := fun x hx =>
  (h1 x fun h => hx (hS x h)).trans (h2 x hx)

/-- **A text written out**, `o` past it. -/
theorem add_const (o : Oracle σ) {R : Ret} {A : Word} {S : Word → Prop} (hS : Scr A S) {s1 : PancakeState σ}
    (hD : ArtDom A s1.memaddrs) (hA8 : A.toNat % 8 = 0) {m0 : Word → Word} {L : List (String × Value)}
    (hla : L.lookup "a" = some A) {P : Bytes} (ho : L.lookup "o" = some (BitVec.ofNat 64 P.length)) {s : String}
    (hs : Ascii s) (hfit : P.length + s.length ≤ ArticleProg.outMax) :
    FragR o R (putConst s) (AOut S s1 A m0 L P)
      (AOut S s1 A m0 (("o", BitVec.ofNat 64 (P ++ DN.News.CommandSpec.ascii s).length) :: without "o" L)
        (P ++ DN.News.CommandSpec.ascii s)) :=
  aout_lift o (putConst_low s) fun M hO hfr => fragR_of (frag_conseq (putConst_frag o hD hA8 hla ho hs hfit hO
    (m0 := M) fun _ _ => rfl) (fun _ h => h) fun u ⟨M', h, hO', hfr'⟩ => ⟨M', by
      rw [List.length_append, ascii_length]; exact h, hO', out_add hfr' hS.1 hfr⟩)

/-- An article's scalar word `artAdded` does not write is kept. -/
theorem not_addScr_w {A : Word} {i : Nat} (hi : i < 32)
    (hne : i ≠ 12 ∧ i ≠ 13 ∧ i ≠ 17 ∧ i ≠ 18 ∧ i ≠ 23 ∧ i ≠ 24) : ¬AddScr A (at_ A (ArticleProg.w i)) := by
  have hX := X_val
  have hl := w_lt64 hi
  rintro (h | h | h | h | h | h | h)
  · obtain ⟨z, h4, h5, e⟩ := h
    have := DN.News.ScanRun.at_inj (by omega) (by rw [xFirst_eq] at h5; omega) e
    rw [xDec_eq] at h4; simp only [ArticleProg.w] at this; omega
  · rcases h with e | ⟨z, h4, h5, e⟩
    · exact w_ne hi (by decide) hne.2.1 A e
    · have := DN.News.ScanRun.at_inj (by omega) (by simp only [ArticleProg.msgCap, xMsg_eq] at h5; omega) e
      rw [xMsg_eq] at h4; simp only [ArticleProg.w] at this; omega
  · exact w_ne hi (by decide) hne.2.2.1 A h
  · exact w_ne hi (by decide) hne.2.2.2.1 A h
  · exact w_ne hi (by decide) hne.2.2.2.2.1 A h
  · exact w_ne hi (by decide) hne.2.2.2.2.2 A h
  · exact w_ne hi (by decide) hne.1 A h

theorem broken_add {A : Word} : ¬AddScr A (at_ A aBroken) :=
  not_addScr (.inl (by have := broken_low; have := sets_le_X; omega))
    (by have := broken_low; have := sets_le_X; have := X_val; rw [xMsg_eq]; omega)
    (by have := broken_low; have := sets_le_X; have := X_val; rw [xDec_eq]; omega)

/-- **A copy written out**, `o` past it. -/
theorem add_copy (o : Oracle σ) {R : Ret} {A : Word} {S : Word → Prop} (hS : Scr A S) {s1 : PancakeState σ}
    (hA : Area ArticleProg.ofs A s1) (hD : ArtDom A s1.memaddrs) (hcode : ArtCode s1.code)
    (hsz : ArticleProg.size esP < 2 ^ 40) {m0 : Word → Word} (hb : m0 (at_ A aBroken) = 0) {L : List (String × Value)}
    (hla : L.lookup "a" = some A) {name : String} (hra : name ≠ "a") (hno : "o" ≠ name) (hrt : Fresh name L = true)
    {P SRC : Bytes} (ho : L.lookup "o" = some (BitVec.ofNat 64 P.length)) {S0 : Nat}
    (hSrc : BytesAt A s1.memaddrs s1.be S0 SRC.length SRC m0)
    (hSk : ∀ i, i < SRC.length → ¬AddScr A (byteAlign (at_ A (S0 + i)))) (hSd : S0 + SRC.length ≤ ArticleProg.xDec)
    (hfit : P.length + SRC.length ≤ ArticleProg.outMax) {e2 e3 : Syntax.PExpr} {E2 E3 : PancakeExp}
    (hlow : LowKK (guardL (copyS name e2 e3))) (he2 : Lower.lowerExp e2 = some E2) (he3 : Lower.lowerExp e3 = some E3)
    (hv2 : ∀ u M, RunF s1 L (· = M) u → (∀ x, ¬S x → M x = m0 x) → eval u E2 = some (BitVec.ofNat 64 S0))
    (hv3 : ∀ u M, RunF s1 L (· = M) u → (∀ x, ¬S x → M x = m0 x) → eval u E3 = some (BitVec.ofNat 64 SRC.length)) :
    FragR o R (guardL (copyS name e2 e3)) (AOut S s1 A m0 L P)
      (AOut S s1 A m0 (("o", BitVec.ofNat 64 (P ++ SRC).length) ::
        without "o" ((name, BitVec.ofNat 64 (P.length + SRC.length)) :: L)) (P ++ SRC)) := by
  refine aout_lift o hlow fun M hO hfr => ?_
  show FragR o R (guardS (.call name "artCopy" [v "o", e2, e3]) ++ [.assign "o" (v name)]) _ _
  refine fragR_append (copyCall_frag o hA hD hcode hsz hra hla hrt (by rw [hfr _ (scr_not hS broken_add)]; exact hb) hO
    (bytesAt_frame hSrc fun i _ hl => hfr _ (scr_not hS (hSk i hl))) hSd hfit (e1 := v "o") rfl he2 he3
    (fun u h => ev_var (vals_lookup h.1.vals ho)) (fun u h => hv2 u M h hfr) fun u h => hv3 u M h hfr) ?_
  refine fragR_exists (lowK_any _ (k := .skip) rfl) fun m => ?_
  refine fragR_pure ((∀ x, ¬OutScr A x → m x = M x) ∧
    BytesAt A s1.memaddrs s1.be ArticleProg.xOut ArticleProg.outMax (P ++ SRC) m) (fun u h => h.2)
    (lowK_any _ (k := .skip) rfl) fun ⟨hfr2, hO2⟩ => ?_
  refine fragR_of (frag_conseq (runF_set o rfl (by rw [DN.News.ScanRun.lookup_cons_ne hno]; exact ho)
    (v := BitVec.ofNat 64 (P.length + SRC.length))
    fun u h => ev_var (vals_lookup h.1.vals (DN.News.ScanRun.lookup_head _ _ _))) (fun u h => h.1) fun u h => ⟨m, by
      rw [List.length_append]; exact h, hO2, out_add hfr2 hS.1 hfr⟩)

/-- **A number's digits written out**, `o` past them. -/
theorem add_num (o : Oracle σ) {R : Ret} {A : Word} {S : Word → Prop} (hS : Scr A S) {s1 : PancakeState σ}
    (hA : Area ArticleProg.ofs A s1) (hD : ArtDom A s1.memaddrs) (hcode : ArtCode s1.code) {m0 : Word → Word}
    (hb : m0 (at_ A aBroken) = 0) {L : List (String × Value)} (hla : L.lookup "a" = some A) {name : String}
    (hra : name ≠ "a") (hno : "o" ≠ name) (hrt : Fresh name L = true) {P : Bytes}
    (ho : L.lookup "o" = some (BitVec.ofNat 64 P.length)) {X : Nat} (hX : X < 2 ^ 64)
    (hfit : P.length + (ArticleSpec.decimal X).length ≤ ArticleProg.outMax) {e2 : Syntax.PExpr} {E2 : PancakeExp}
    (hlow : LowKK (guardL (numS name e2))) (he2 : Lower.lowerExp e2 = some E2)
    (hv2 : ∀ u M, RunF s1 L (· = M) u → (∀ x, ¬S x → M x = m0 x) → eval u E2 = some (BitVec.ofNat 64 X)) :
    FragR o R (guardL (numS name e2)) (AOut S s1 A m0 L P)
      (AOut S s1 A m0 (("o", BitVec.ofNat 64 (P ++ ArticleSpec.decimal X).length) ::
        without "o" ((name, BitVec.ofNat 64 (P.length + (ArticleSpec.decimal X).length)) :: L))
        (P ++ ArticleSpec.decimal X)) := by
  refine aout_lift o hlow fun M hO hfr => ?_
  show FragR o R (guardS (.call name "artNum10" [v "o", e2]) ++ [.assign "o" (v name)]) _ _
  refine fragR_append (num10Call_frag o hA hD hcode hra hla hrt (by rw [hfr _ (scr_not hS broken_add)]; exact hb) hO hX
    hfit ho
    he2 fun u h => hv2 u M h hfr) ?_
  refine fragR_exists (lowK_any _ (k := .skip) rfl) fun m => ?_
  refine fragR_pure ((∀ x, ¬OutScr A x → m x = M x) ∧
    BytesAt A s1.memaddrs s1.be ArticleProg.xOut ArticleProg.outMax (P ++ ArticleSpec.decimal X) m) (fun u h => h.2)
    (lowK_any _ (k := .skip) rfl) fun ⟨hfr2, hO2⟩ => ?_
  refine fragR_of (frag_conseq (runF_set o rfl (by rw [DN.News.ScanRun.lookup_cons_ne hno]; exact ho)
    (v := BitVec.ofNat 64 (P.length + (ArticleSpec.decimal X).length))
    fun u h => ev_var (vals_lookup h.1.vals (DN.News.ScanRun.lookup_head _ _ _))) (fun u h => h.1) fun u h => ⟨m, by
      rw [List.length_append]; exact h, hO2, out_add hfr2 hS.1 hfr⟩)

theorem pows_frame {A : Word} {S : Word → Prop} (hS : Scr A S) {M m0 : Word → Word}
    (hfr : ∀ x, ¬S x → M x = m0 x) (hP : Pows m0 A) : Pows M A := fun j hj => by
  rw [hfr _ (scr_not hS (not_addScr (.inl (by have := (pow_in hj).2; have := sets_le_X; omega))
    (by have := (pow_in hj).2; have := sets_le_X; have := X_val; rw [xMsg_eq]; omega)
    (by have := (pow_in hj).2; have := sets_le_X; have := X_val; rw [xDec_eq]; omega)))]
  exact hP j hj

/-- **The wall clock's date written out**, `o` past it. -/
theorem add_fmt (o : Oracle σ) {R : Ret} {A : Word} {S : Word → Prop} (hS : Scr A S) {s1 : PancakeState σ}
    (hA : Area ArticleProg.ofs A s1) (hD : ArtDom A s1.memaddrs) (hcode : ArtCode s1.code) {m0 : Word → Word}
    (hP : Pows m0 A) (hb : m0 (at_ A aBroken) = 0) {L : List (String × Value)} (hla : L.lookup "a" = some A)
    {name : String} (hra : name ≠ "a") (hno : "o" ≠ name) (hrt : Fresh name L = true) {P : Bytes}
    (ho : L.lookup "o" = some (BitVec.ofNat 64 P.length)) {wall : Nat} (hwall : wall < ArticleProg.wallMax)
    (hw : m0 (at_ A ArticleProg.xWall) = BitVec.ofNat 64 wall)
    (hfit : P.length + (ArticleSpec.formatDate wall).length ≤ ArticleProg.outMax) :
    FragR o R (guardL (fmtS name)) (AOut S s1 A m0 L P)
      (AOut S s1 A m0 (("o", BitVec.ofNat 64 (P ++ ArticleSpec.formatDate wall).length) ::
        without "o" ((name, BitVec.ofNat 64 (P.length + (ArticleSpec.formatDate wall).length)) :: L))
        (P ++ ArticleSpec.formatDate wall)) := by
  refine aout_lift o (lowK_any _ (k := .skip) rfl) fun M hO hfr => ?_
  have hwall' : M (at_ A ArticleProg.xWall) = BitVec.ofNat 64 wall := by
    exact (hfr _ (scr_not hS (not_addScr_w (i := 2) (by decide) (by decide)))).trans hw
  have hPM := pows_frame hS hfr hP
  show FragR o R (guardS (.call name "artFormat" [v "o"]) ++ [.assign "o" (v name)]) _ _
  refine fragR_append (fmtCall_frag o hA hD hcode hra hla hrt hPM (by rw [hfr _ (scr_not hS broken_add)]; exact hb) hO
    hwall
    hwall' hfit ho) ?_
  refine fragR_exists (lowK_any _ (k := .skip) rfl) fun m => ?_
  refine fragR_pure ((∀ x, ¬OutScr A x → m x = M x) ∧
    BytesAt A s1.memaddrs s1.be ArticleProg.xOut ArticleProg.outMax (P ++ ArticleSpec.formatDate wall) m)
    (fun u h => h.2) (lowK_any _ (k := .skip) rfl) fun ⟨hfr2, hO2⟩ => ?_
  refine fragR_of (frag_conseq (runF_set o rfl (by rw [DN.News.ScanRun.lookup_cons_ne hno]; exact ho)
    (v := BitVec.ofNat 64 (P.length + (ArticleSpec.formatDate wall).length))
    fun u h => ev_var (vals_lookup h.1.vals (DN.News.ScanRun.lookup_head _ _ _))) (fun u h => h.1) fun u h => ⟨m, by
      rw [List.length_append]; exact h, hO2, out_add hfr2 hS.1 hfr⟩)

/-! ## The fields kept -/


/-- **A slice of the input as a copy's source**: its bytes from `aInput + P`. -/
theorem input_seg {A : Word} {dm : Word → Bool} {be : Bool} {m : Word → Word} {a : Bytes}
    (hin : InputAt m dm be A a) {P E : Nat} (hPE : P ≤ E) (hE : E ≤ a.length) :
    BytesAt A dm be (aInput + P) (seg a P E).length (seg a P E) m := fun i hi _ => by
  rw [seg_length a hPE hE] at hi
  rw [Nat.add_assoc, hin (P + i) (by omega), getElem!_pos (seg a P E) i (by rw [seg_length a hPE hE]; omega),
    getElem!_pos a (P + i) (by omega)]
  simp [seg, List.getElem_take, List.getElem_drop]

/-- An input byte's word is none `artAdded` writes. -/
theorem input_add {A : Word} (hA8 : A.toNat % 8 = 0) {y : Nat} (hy : y < aInput + artMax) :
    ¬AddScr A (byteAlign (at_ A y)) := by
  have := input_below; have := sets_le_X; have := X_val; have := artMax_eq
  rw [DN.News.ScanRun.align_at hA8]
  exact not_addScr (.inl (by omega)) (by rw [xMsg_eq]; omega) (by rw [xDec_eq]; omega)

/-- **The test of a field kept**: its entry is not Path's. -/
theorem keep_eval {u : PancakeState σ} {c : Nat} (hc : c < 2 ^ 64) {x : String}
    (hx : u.locals x = some (BitVec.ofNat 64 c)) :
    eval u (.op .and_ (.cmp .equal (.cmp .equal (.var x) (.const (BitVec.ofNat 64 (ArticleProg.entryOf esP "Path"))))
      (.const (BitVec.ofNat 64 0))) (.const (BitVec.ofNat 64 1))) = some (bw (decide (c ≠ 21))) := by
  rw [path_entry]
  rw [FramerCode.eval_and (p := decide (BitVec.ofNat 64 c ≠ BitVec.ofNat 64 21)) (q := true)
    (ne_eval (ev_var hx) rfl) rfl, Bool.and_true]
  congr 2
  apply decide_eq_decide.2
  constructor
  · intro h e; exact h (by rw [e])
  · intro h e; exact h (DN.Compiler.NatToDec.ofNat64_inj hc (by decide) e)

/-- A word past the output's is none `artAdded` writes. -/
theorem high_add {A : Word} {y : Nat} (h1 : ArticleProg.xFirst ≤ y) (h2 : y < 2 ^ 40) : ¬AddScr A (at_ A y) := by
  have hX := X_val; have hF := xFirst_eq; have hm := xMsg_eq; have hmc : ArticleProg.msgCap = 256 := rfl
  have hw : ∀ i, i < 32 → at_ A y ≠ at_ A (ArticleProg.w i) := fun i hi => by
    refine DN.News.ScanRun.at_ne (by omega) (w_lt64 hi) ?_
    simp only [ArticleProg.w]; omega
  rintro (h | h | h | h | h | h | h)
  · obtain ⟨z, h4, h5, e⟩ := h
    have := DN.News.ScanRun.at_inj (by omega) (by omega) e
    omega
  · rcases h with e | ⟨z, h4, h5, e⟩
    · exact hw 13 (by decide) e
    · have := DN.News.ScanRun.at_inj (by omega) (by omega) e; omega
  · exact hw 17 (by decide) h
  · exact hw 18 (by decide) h
  · exact hw 23 (by decide) h
  · exact hw 24 (by decide) h
  · exact hw 12 (by decide) h

/-- **The entries' tables kept** where only `artAdded`'s words change. -/
theorem tablesAt_frame {A : Word} (hA8 : A.toNat % 8 = 0) {dm : Word → Bool} {be : Bool} {es : List String}
    (hsz : ArticleProg.size es < 2 ^ 40) {m M : Word → Word} (hfr : ∀ x, ¬AddScr A x → M x = m x)
    (h : TablesAt A dm be m es) : TablesAt A dm be M es := by
  have hnT := xFirst_le_nameT es
  have hsz' : ArticleProg.xNameBytes es + ArticleProg.nameBytes es ≤ ArticleProg.size es := by
    simp only [ArticleProg.size]; omega
  have hNB : ArticleProg.xNameT es + 16 * es.length = ArticleProg.xNameBytes es := rfl
  have hT : ∀ k, k < es.length → ArticleProg.xNameT es + 16 * k + 8 < ArticleProg.size es := fun k hk => by
    simp only [ArticleProg.size] at hsz' ⊢; omega
  refine ⟨fun k hk => ?_, fun k hk => ?_, fun k hk i hi => ?_⟩
  · have := hT k hk
    rw [hfr _ (high_add (by omega) (by omega))]; exact h.off k hk
  · have := hT k hk
    rw [hfr _ (high_add (by omega) (by omega))]; exact h.len k hk
  · have hb := h.bytes k hk i hi
    have hoff : offOf es k + i < ArticleProg.nameBytes es := by have := offOf_le es hk; omega
    unfold memLoadByte at hb ⊢
    rw [DN.News.ScanRun.align_at hA8] at hb ⊢
    rw [hfr _ (high_add (by have := xFirst_mod; simp only [ArticleProg.xNameBytes] at hNB ⊢; omega)
      (by omega))]; exact hb

/-- The input kept where only `artAdded`'s words change. -/
theorem input_frame {A : Word} (hA8 : A.toNat % 8 = 0) {dm : Word → Bool} {be : Bool} {a : Bytes}
    (hlen : a.length ≤ artMax) {m M : Word → Word} (hfr : ∀ x, ¬AddScr A x → M x = m x) (h : InputAt m dm be A a) :
    InputAt M dm be A a := fun x hx => by
  rw [load_frame hfr (input_add hA8 (by omega))]; exact h x hx

/-- What `artField` writes is `artAdded`'s: the output kept, every other word too. -/
theorem fieldMem_add {A : Word} (hA8 : A.toNat % 8 = 0) {dm : Word → Bool} {be : Bool} {M m0 : Word → Word}
    {P : Bytes} (k e : Nat) (hO : BytesAt A dm be ArticleProg.xOut ArticleProg.outMax P M)
    (hfr : ∀ x, ¬AddScr A x → M x = m0 x) :
    BytesAt A dm be ArticleProg.xOut ArticleProg.outMax P (fieldMem A k e M) ∧
      ∀ x, ¬AddScr A x → fieldMem A k e M x = m0 x := by
  have hne : ∀ y, ArticleProg.xDec ≤ y → y < ArticleProg.xFirst → ∀ i, i = 17 ∨ i = 18 →
      at_ A y ≠ at_ A (ArticleProg.w i) := fun y h1 h2 i hi => DN.News.ScanRun.at_ne
    (by rw [xFirst_eq] at h2; omega) (w_lt64 (by omega)) (by
      rw [xDec_eq] at h1; simp only [ArticleProg.w, X_val]; omega)
  refine ⟨bytesAt_frame hO fun i hi _ => ?_, fun x hx => ?_⟩
  · have hmx : ArticleProg.outMax = 69632 := rfl
    have hy1 : ArticleProg.xDec ≤ (ArticleProg.xOut + i) / 8 * 8 := by rw [xDec_eq, xOut_eq]; omega
    have hy2 : (ArticleProg.xOut + i) / 8 * 8 < ArticleProg.xFirst := by rw [xFirst_eq, xOut_eq]; omega
    rw [DN.News.ScanRun.align_at hA8]
    simp only [fieldMem, ArticleProg.xNl, ArticleProg.xE1]
    rw [upd_ne _ (hne _ hy1 hy2 18 (.inr rfl)), upd_ne _ (hne _ hy1 hy2 17 (.inl rfl))]
  · simp only [fieldMem]
    rw [upd_ne _ fun h => hx (.inr (.inr (.inr (.inl h)))), upd_ne _ fun h => hx (.inr (.inr (.inl h)))]
    exact hfr x hx

theorem aout_restore {S : Word → Prop} {s1 : PancakeState σ} {A : Word} {m0 : Word → Word}
    {L : List (String × Value)} {P : Bytes} {u : PancakeState σ} (h : AOut S s1 A m0 L P u) {y : String}
    (hy : Fresh y L = true) (w : Option Value) : AOut S s1 A m0 L P (restore u y w) :=
  let ⟨M, hr, hv⟩ := h; ⟨M, runF_restore hr hy w, hv⟩

/-- **An assignment** with the output as it is. -/
theorem add_set (o : Oracle σ) {R : Ret} {S : Word → Prop} {s1 : PancakeState σ} {A : Word} {m0 : Word → Word}
    {L : List (String × Value)} {P : Bytes} {x : String} {e : Syntax.PExpr} {E : PancakeExp}
    (he : Lower.lowerExp e = some E) {w : Value} (hl : L.lookup x = some w) {val : Value}
    (hv : ∀ u M, RunF s1 L (· = M) u → eval u E = some val) :
    FragR o R [.assign x e] (AOut S s1 A m0 L P) (AOut S s1 A m0 ((x, val) :: without x L) P) :=
  aout_lift o (lowKK_one rfl (a := .assign x E) (by simp [Lower.lowerStmt1, he])) fun M hO hfr =>
    fragR_of (frag_conseq (runF_set o he hl fun u h => hv u M h) (fun _ h => h) fun u h => ⟨M, h, hO, hfr⟩)

/-- **The lines from the next field on.** -/
theorem lines_next {a : Bytes} {sep : Nat} : ∀ (L : List (Nat × Nat)) (s : Nat), Lines a s L sep →
    Lines a (DN.News.ArticleLines.nextOf a L sep) (L.dropWhile (cont a)) sep
  | [], s, h => by
    cases h with
    | sep he hlt => exact .sep he hlt
  | (q1, q2) :: more, s, h => by
    cases hc : cont a (q1, q2)
    · rw [DN.News.ArticleLines.nextOf_stop hc, List.dropWhile_cons_of_neg (by simp [hc])]
      rw [← (DN.News.ArticleLines.lines_tail h).1] at h; exact h
    · rw [DN.News.ArticleLines.nextOf_cont hc, List.dropWhile_cons_of_pos hc]
      exact lines_next more _ (DN.News.ArticleLines.lines_tail h).2

/-- Whether a field is kept as it came: all but Path. -/
def keepF (f : Field) : Bool := !ArticleSpec.named f.name "Path"

/-- The fields kept, of the groups `gs`, as they travel. -/
def keptT (a : Bytes) (gs : List (List (Nat × Nat))) : Bytes :=
  (((gs.map (fieldOf a)).filter keepF).map (·.text)).flatten

theorem keptT_append (a : Bytes) (g1 g2 : List (List (Nat × Nat))) :
    keptT a (g1 ++ g2) = keptT a g1 ++ keptT a g2 := by
  simp [keptT, List.map_append, List.filter_append, List.flatten_append]

theorem keptT_one (a : Bytes) (g : List (Nat × Nat)) :
    keptT a [g] = if keepF (fieldOf a g) then (fieldOf a g).text else [] := by
  unfold keptT; cases h : keepF (fieldOf a g) <;> simp [List.filter, h]

theorem keptT_nil (a : Bytes) : keptT a [] = [] := rfl

/-- **A field's bytes**: from its first line to the next field. -/
theorem fieldText {a : Bytes} {sep s e : Nat} {L : List (Nat × Nat)} (h : Lines a s ((s, e) :: L) sep) :
    (fieldOf a ((s, e) :: L.takeWhile (cont a))).text = seg a s (DN.News.ArticleLines.nextOf a L sep) := by
  rw [← text_seg L s e h]
  simp only [ArticleSpec.Field.text, fieldOf, segs, List.map_map]
  rfl

theorem dropWhile_head {α : Type} (p : α → Bool) : ∀ (l : List α) (q : α) (r : List α), l.dropWhile p = q :: r →
    p q = false
  | [], _, _, h => by simp at h
  | x :: l, q, r, h => by
    by_cases hx : p x = true
    · rw [List.dropWhile_cons_of_pos hx] at h; exact dropWhile_head p l q r h
    · rw [List.dropWhile_cons_of_neg hx] at h; cases h; simpa using hx

theorem groups_cons (a : Bytes) (q : Nat × Nat) (more : List (Nat × Nat)) :
    groups a (q :: more) = (q :: more.takeWhile (cont a)) :: groups a (more.dropWhile (cont a)) := by
  rw [groups]

/-! ## The loop of fields kept -/

/-- The loop's lasting locals: the empty line's place, the lengths, the area. -/
def baseL (A : Word) (SEP RL IDL : Nat) : List (String × Value) :=
  [("sep", BitVec.ofNat 64 SEP), ("rl", BitVec.ofNat 64 RL), ("idl", BitVec.ofNat 64 IDL), ("a", A)]

/-- The loop's locals: the field's start, the output's end, the rest. -/
def loopL (A : Word) (SEP RL IDL P O : Nat) : List (String × Value) :=
  ("p", BitVec.ofNat 64 P) :: ("o", BitVec.ofNat 64 O) :: baseL A SEP RL IDL

/-- Where the loop is: the lines `t.2.1` from `t.1` on, the groups `t.2.2` before them copied. -/
def LoopF (a : Bytes) (L : List (Nat × Nat)) (SEP : Nat) (t : Nat × List (Nat × Nat) × List (List (Nat × Nat))) :
    Prop :=
  Lines a t.1 t.2.1 SEP ∧ (∀ q ∈ t.2.1, q ∈ L) ∧ (∀ q r, t.2.1 = q :: r → cont a q = false) ∧
    groups a L = t.2.2 ++ groups a t.2.1

def LoopI (s1 : PancakeState σ) (A : Word) (m0 : Word → Word) (a : Bytes) (L : List (Nat × Nat)) (SEP RL IDL : Nat)
    (OUT0 : Bytes) : Assn σ := fun u =>
  ∃ t, LoopF a L SEP t ∧
    AOut (AddScr A) s1 A m0 (loopL A SEP RL IDL t.1 (OUT0 ++ keptT a t.2.2).length) (OUT0 ++ keptT a t.2.2) u

theorem keptBody_g : guardL keptBody =
    guardS (.call "fe" "artField" [v "p"]) ++ guardS (.call "ck" "artClass" [v "p", wd xNl]) ++
    ([.ite (eAnd (DN.News.AbnfProg.ne (v "ck") (n (ArticleProg.entryOf esP "Path"))) (n 1))
      (guardL (copyS "o4" (eAdd (n aInput) (v "p")) (eSub (v "fe") (v "p")))) [], .assign "p" (v "fe")] : Ss) := rfl

theorem classOf_le (es : List String) (name : Bytes) : DN.News.ArticleRun.classOf es name ≤ es.length := by
  unfold DN.News.ArticleRun.classOf
  cases h : es.findIdx? (entryIs · name) with
  | none => exact Nat.le_refl _
  | some i => exact Nat.le_of_lt (List.findIdx?_eq_some_iff_findIdx_eq.1 h).1

theorem decl_copy (nm : String) (src len : Syntax.PExpr) : declared (guardL (copyS nm src len)) = [nm] := rfl

theorem esP_length : esP.length = 55 := by rw [es_eq]; rfl

theorem loop_eval {s1 : PancakeState σ} {A : Word} {m0 : Word → Word} {a : Bytes} {L : List (Nat × Nat)}
    {SEP RL IDL : Nat} {OUT0 : Bytes} {u : PancakeState σ} (hsa : SEP < 2 ^ 63)
    {t : Nat × List (Nat × Nat) × List (List (Nat × Nat))} (hf : LoopF a L SEP t)
    (hO : AOut (AddScr A) s1 A m0 (loopL A SEP RL IDL t.1 (OUT0 ++ keptT a t.2.2).length) (OUT0 ++ keptT a t.2.2) u) :
    eval u (.cmp .less (.var "p") (.var "sep")) = some (bw (decide (t.1 < SEP))) := by
  obtain ⟨M, hr, -⟩ := hO
  have hl := DN.News.ArticleLines.lines_sep hf.1
  exact DN.News.FramerCode.eval_lt (t := u) (a := .var "p") (b := .var "sep") (x := t.1) (y := SEP) (by omega)
    (by omega) (ev_var (vals_lookup hr.1.vals rfl)) (ev_var (vals_lookup hr.1.vals rfl))

/-- **One field**: copied if it is not Path, the loop past it. -/
theorem loop_body (o : Oracle σ) {R : Ret} {A : Word} {s1 : PancakeState σ} (hA : Area ArticleProg.ofs A s1)
    (hD : ArtDom A s1.memaddrs) (hcode : ArtCode s1.code) {m0 : Word → Word} {a : Bytes} (hlen : a.length ≤ artMax)
    (hin : InputAt m0 s1.memaddrs s1.be A a) (hb : m0 (at_ A aBroken) = 0) {SEP : Nat}
    (hsep : m0 (at_ A xSep) = BitVec.ofNat 64 SEP) (hT : TabDom A s1.memaddrs esP)
    (htab : TablesAt A s1.memaddrs s1.be m0 esP) (hes : ∀ s ∈ esP, s.length ≤ 64) (hsz : ArticleProg.size esP < 2 ^ 40)
    {L : List (Nat × Nat)} (hok : L.any (DN.News.ArticleLines.malLine a) = false) {RL IDL : Nat} {OUT0 : Bytes}
    (hK : (OUT0 ++ keptT a (groups a L)).length ≤ ArticleProg.outMax) :
    FragR o R (guardL keptBody)
      (fun u => LoopI s1 A m0 a L SEP RL IDL OUT0 u ∧ eval u (.cmp .less (.var "p") (.var "sep")) ≠ some 0)
      (LoopI s1 A m0 a L SEP RL IDL OUT0) := by
  have hA8 := hA.hA
  have hM := artMax_eq
  have hlow : LowKK (guardL keptBody) := lowK_any _ (k := .skip) rfl
  refine fragR_conseq (P0 := fun u => ∃ t, (LoopF a L SEP t ∧ t.1 < SEP) ∧
    AOut (AddScr A) s1 A m0 (loopL A SEP RL IDL t.1 (OUT0 ++ keptT a t.2.2).length) (OUT0 ++ keptT a t.2.2) u) ?_
    (fun u (h : LoopI s1 A m0 a L SEP RL IDL OUT0 u ∧ eval u (.cmp .less (.var "p") (.var "sep")) ≠ some 0) => by
      obtain ⟨⟨t, hf, hO⟩, hne⟩ := h
      refine ⟨t, ⟨hf, ?_⟩, hO⟩
      have hl := DN.News.ArticleLines.lines_sep hf.1
      have e := loop_eval (by omega) hf hO
      rcases Nat.lt_or_ge t.1 SEP with hlt | hge
      · exact hlt
      · exact absurd (by rw [e, decide_eq_false (by omega)]; rfl) hne) fun _ h => h
  refine fragR_exists hlow fun t => ?_
  obtain ⟨P, Lr, gd⟩ := t
  refine fragR_pure (LoopF a L SEP (P, Lr, gd) ∧ P < SEP) (fun u h => h.1) hlow fun ⟨⟨hL, hsub, hhd, hgr⟩, hPS⟩ => ?_
  refine fragR_conseq ?_ (fun u h => h.2) fun _ h => h
  simp only at hL hsub hhd hgr ⊢
  obtain ⟨e, more, rfl, -, he2, hPe, hea, hmore⟩ := DN.News.ArticleLines.lines_cons hL hPS
  have hc0 : cont a (P, e) = false := hhd _ _ rfl
  have hmal : DN.News.ArticleLines.malName a (P, e) = false := by
    have := List.any_eq_false.1 hok (P, e) (hsub _ List.mem_cons_self)
    simpa [DN.News.ArticleLines.malLine, hc0] using this
  have hf : DN.News.ArticleLines.FieldAt a SEP P e more := ⟨hL, hc0, hmal⟩
  have hnext := lines_next more (e + 2) hmore
  have hNXs := DN.News.ArticleLines.lines_sep hnext
  have hNXg := (DN.News.ArticleLines.nextOf_ge hmore).1
  have hcol := DN.News.ArticleLines.fieldAt_colon hf
  have htext := fieldText hL
  have hseg : (seg a P (DN.News.ArticleLines.nextOf a more SEP)).length = DN.News.ArticleLines.nextOf a more SEP - P :=
    seg_length a (by omega) (by omega)
  have hgr' : groups a L = gd ++ [(P, e) :: more.takeWhile (cont a)] ++ groups a (more.dropWhile (cont a)) := by
    rw [hgr, groups_cons]; simp
  have hK' := hK
  rw [hgr', keptT_append, keptT_append] at hK'
  have hcls := classOf_le esP (seg a P (P + DN.News.ArticleLines.nameLen a P e))
  rw [esP_length] at hcls
  have hkb : keepF (fieldOf a ((P, e) :: more.takeWhile (cont a))) =
      decide (DN.News.ArticleRun.classOf esP (seg a P (P + DN.News.ArticleLines.nameLen a P e)) ≠ 21) :=
    (class_path (seg a P (P + DN.News.ArticleLines.nameLen a P e))).symm
  rw [keptBody_g]
  let Pout := OUT0 ++ keptT a gd
  let NX := DN.News.ArticleLines.nextOf a more SEP
  let K := DN.News.ArticleLines.nameLen a P e
  let Lp := loopL A SEP RL IDL P Pout.length
  let Bm : List (String × Value) := baseL A SEP RL IDL
  let g := (P, e) :: more.takeWhile (cont a)
  have hNX1 : NX ≤ SEP := hNXs.1
  have hNX2 : SEP < a.length := hNXs.2.2
  have hNX3 : e + 2 ≤ NX := hNXg
  have hseg' : (seg a P NX).length = NX - P := hseg
  have hK1 : P + K < e := hcol.2.1
  -- the field's end and its class
  refine fragR_append (M := AOut (AddScr A) s1 A m0
    (("ck", BitVec.ofNat 64 (DN.News.ArticleRun.classOf esP (seg a P (P + K)))) ::
    ("fe", BitVec.ofNat 64 NX) :: Lp) Pout) (aout_lift o (lowK_any _ (k := .skip) rfl) fun M hO hfr => ?_) ?_
  · have hbM : M (at_ A aBroken) = 0 := (hfr _ broken_add).trans hb
    have hinM := input_frame hA8 hlen hfr hin
    have hsepM : M (at_ A xSep) = BitVec.ofNat 64 SEP :=
      (hfr _ (not_addScr_w (i := 16) (by decide) (by decide))).trans hsep
    have hk := fieldMem_keep hA8 hlen hinM hbM K e
    have hfm := fieldMem_add hA8 K e hO hfr
    refine fragR_append (fieldCall_frag o hA hD hcode hlen (rt := "fe") (by decide) (l := Lp) rfl rfl (e1 := v "p")
      rfl hf (fun u h => ev_var (vals_lookup h.1.vals rfl)) hinM hbM hsepM) ?_
    refine fragR_conseq (classCall_frag o hA hcode (rt := "ck") (by decide) (l := ("fe", BitVec.ofNat 64 NX) :: Lp)
      rfl rfl hk.2 hT (tablesAt_frame hA8 hsz hfm.2 htab) hes hsz hk.1 hlen (P := P) (NL := K) (by omega)
      (e1 := v "p") (e2 := wd xNl) rfl (wd_lower 17) (fun u h => ev_var (vals_lookup h.1.vals rfl)) (fun u h => by
        rw [loadA_eval h.1.memaddrs (artDom_w hD (i := 17) (by decide)) (atA_eval (vals_lookup h.1.vals rfl)), h.2]
        exact congrArg some (fieldMem_nl A K e M))) (fun _ h => h) fun u h => ⟨_, h, hfm.1, hfm.2⟩
  -- the field copied if kept
  refine fragR_append (xs := [_]) (fragR_if o rfl (lowK_any _ (k := .skip) rfl) (lowK_any _ (k := .skip) rfl)
    (Q := AOut (AddScr A) s1 A m0 (("fe", BitVec.ofNat 64 NX) :: ("p", BitVec.ofNat 64 P) ::
      ("o", BitVec.ofNat 64 (Pout ++ keptT a [g]).length) :: Bm) (Pout ++ keptT a [g])) aout_clock
    (fun u y w h hy => by
      rw [decl_copy] at hy; simp only [List.mem_singleton] at hy; subst hy; exact aout_restore h rfl w)
    (fun u y w h hy => nomatch hy) (b := keepF (fieldOf a g)) (fun u h => by
      obtain ⟨M, hr, -⟩ := h
      rw [hkb]
      exact keep_eval (by omega) (vals_lookup hr.1.vals rfl)) (fun hb1 => ?_) (fun hb0 => ?_)) ?_
  · rw [keptT_one, if_pos hb1, htext]
    have hS := input_seg hin (P := P) (E := NX) (by omega) (by omega)
    have hfit : Pout.length + (seg a P NX).length ≤ ArticleProg.outMax := by
      rw [keptT_one, if_pos hb1, htext] at hK'
      show (OUT0 ++ keptT a gd).length + _ ≤ _
      simp only [List.length_append] at hK' ⊢; omega
    refine fragR_conseq (add_copy o scr_add hA hD hcode hsz hb (L := ("ck", _) :: ("fe", BitVec.ofNat 64 NX) :: Lp)
      rfl (name := "o4") (by decide) (by decide) rfl (P := Pout) (SRC := seg a P NX) rfl (S0 := aInput + P) hS
      (fun i hi => input_add hA8 (by rw [hseg'] at hi; omega))
      (by have := input_below; have := sets_le_X; have := X_val; rw [hseg', xDec_eq]; omega) hfit
      (lowK_any _ (k := .skip) rfl) rfl rfl
      (fun u M h _ => WpBytes.eval_add rfl (ev_var (vals_lookup h.1.vals rfl)))
      (fun u M h _ => by
        rw [hseg']
        exact DN.News.ArticleCal.ev_subE (ev_var (vals_lookup h.1.vals rfl)) (ev_var (vals_lookup h.1.vals rfl))
          (by omega)
          (by omega))) (fun _ h => h) fun u h => aout_of h fun q hq => by
            simp only [Bm, baseL, List.mem_cons, List.mem_nil_iff, or_false] at hq
            rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  · rw [keptT_one, if_neg (by simp [hb0]), List.append_nil]
    exact fragR_of (frag_nil o fun u h => aout_of h fun q hq => by
      simp only [Bm, baseL, List.mem_cons, List.mem_nil_iff, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl)
  -- past the field
  refine fragR_conseq (add_set o (x := "p") (e := v "fe") rfl rfl (val := BitVec.ofNat 64 NX)
    fun u M h => ev_var (vals_lookup h.1.vals rfl)) (fun _ h => h) fun u h => ?_
  refine ⟨(NX, more.dropWhile (cont a), gd ++ [g]), ⟨hnext, fun q hq => hsub q (List.mem_cons_of_mem _
    (List.dropWhile_subset _ hq)), fun q r hqr => dropWhile_head _ _ q r hqr, by rw [hgr']⟩, ?_⟩
  simp only
  rw [keptT_append, ← List.append_assoc]
  exact aout_of h fun q hq => by
    simp only [loopL, baseL, List.mem_cons, List.mem_nil_iff, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

theorem loopI_clock {s1 : PancakeState σ} {A : Word} {m0 : Word → Word} {a : Bytes} {L : List (Nat × Nat)}
    {SEP RL IDL : Nat} {OUT0 : Bytes} : Safe.ClockFree (LoopI s1 A m0 a L SEP RL IDL OUT0) :=
  fun u k ⟨t, hf, hO⟩ => ⟨t, hf, aout_clock u k hO⟩

/-- **The fields but Path copied**, in order. -/
theorem loop_frag (o : Oracle σ) {R : Ret} {A : Word} {s1 : PancakeState σ} (hA : Area ArticleProg.ofs A s1)
    (hD : ArtDom A s1.memaddrs) (hcode : ArtCode s1.code) {m0 : Word → Word} {a : Bytes} (hlen : a.length ≤ artMax)
    (hin : InputAt m0 s1.memaddrs s1.be A a) (hb : m0 (at_ A aBroken) = 0) {SEP : Nat}
    (hsep : m0 (at_ A xSep) = BitVec.ofNat 64 SEP) (hT : TabDom A s1.memaddrs esP)
    (htab : TablesAt A s1.memaddrs s1.be m0 esP) (hes : ∀ s ∈ esP, s.length ≤ 64) (hsz : ArticleProg.size esP < 2 ^ 40)
    {L : List (Nat × Nat)} (hL : Lines a 0 L SEP) (hok : L.any (DN.News.ArticleLines.malLine a) = false)
    {RL IDL : Nat} {OUT0 : Bytes} (hK : (OUT0 ++ keptT a (groups a L)).length ≤ ArticleProg.outMax) :
    FragR o R [.while (eLt (v "p") (v "sep")) (guardL keptBody)]
      (AOut (AddScr A) s1 A m0 (loopL A SEP RL IDL 0 OUT0.length) OUT0)
      (AOut (AddScr A) s1 A m0 (loopL A SEP RL IDL SEP (OUT0 ++ keptT a (groups a L)).length)
        (OUT0 ++ keptT a (groups a L))) := by
  have hM := artMax_eq
  have hsa : SEP < 2 ^ 63 := by have := (DN.News.ArticleLines.lines_sep hL).2.2; omega
  have hdecl : declared (guardL keptBody) = ["fe", "ck"] := rfl
  refine fragR_conseq (fragR_while o rfl (lowK_any _ (k := .skip) rfl) (I := LoopI s1 A m0 a L SEP RL IDL OUT0)
    loopI_clock (fun u y w ⟨t, hf, hO⟩ hy => by
      rw [hdecl] at hy
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hy
      rcases hy with rfl | rfl
      · exact ⟨t, hf, aout_restore hO rfl w⟩
      · exact ⟨t, hf, aout_restore hO rfl w⟩)
    (fun u ⟨t, hf, hO⟩ => ⟨_, loop_eval hsa hf hO⟩)
    (loop_body o hA hD hcode hlen hin hb hsep hT htab hes hsz hok hK)) (fun u h => ⟨(0, L, []), ⟨hL,
      fun _ h => h, fun q r hqr => ?_, rfl⟩, by simpa [keptT_nil] using h⟩) fun u ⟨⟨t, hf, hO⟩, h0⟩ => ?_
  · subst hqr
    have := List.any_eq_false.1 hok q List.mem_cons_self
    have h0 := (DN.News.ArticleLines.lines_tail hL).1
    cases hc : cont a q
    · rfl
    · simp [DN.News.ArticleLines.malLine, hc, h0] at this
  · rw [loop_eval hsa hf hO] at h0
    have hge : SEP ≤ t.1 := by
      rcases Nat.lt_or_ge t.1 SEP with hlt | hge
      · rw [decide_eq_true hlt] at h0; exact absurd h0 (by decide)
      · exact hge
    have hle := (DN.News.ArticleLines.lines_sep hf.1).1
    have hg := hf.2.2.2
    rw [DN.News.ArticleLines.lines_at_sep hf.1 hge, show groups a [] = [] by rw [groups], List.append_nil] at hg
    have e : t.1 = SEP := by omega
    rw [hg]; rw [e] at hO; exact hO

/-! ## Path -/

/-- **White space skipped**: the bytes from `x` on without the white space they start with are those from `r` on. -/
theorem dropWS_seg {a : Bytes} {e : Nat} (he : e ≤ a.length) : ∀ (n x r : Nat), r - x = n → x ≤ r → r ≤ e →
    (∀ j, x ≤ j → j < r → DN.News.CommandSpec.isWS a[j]! = true) →
    (r = e ∨ DN.News.CommandSpec.isWS a[r]! = false) →
    (seg a x e).dropWhile DN.News.CommandSpec.isWS = seg a r e
  | 0, x, r, hn, hxr, hre, _, hstop => by
    have : x = r := by omega
    subst this
    rcases Nat.lt_or_ge x e with h | h
    · rcases hstop with rfl | hs
      · omega
      · have hn : ¬(DN.News.CommandSpec.isWS a[x]! = true) := by rw [hs]; decide
        rw [seg_cons a h he, List.dropWhile_cons_of_neg hn]
    · rw [show x = e by omega, DN.News.ArticleLines.seg_self]; rfl
  | n + 1, x, r, hn, hxr, hre, hws, hstop => by
    rw [seg_cons a (by omega) he, List.dropWhile_cons_of_pos (hws x (Nat.le_refl _) (by omega))]
    exact dropWS_seg he n (x + 1) r (by omega) (by omega) hre (fun j h1 h2 => hws j (by omega) h2) hstop

/-- A field's lines after its first, with their CRLFs, are the input's bytes up to the next field. -/
theorem cont_seg {a : Bytes} {sep s e : Nat} {L : List (Nat × Nat)} (h : Lines a s ((s, e) :: L) sep) :
    ((L.takeWhile (cont a)).map fun q => seg a q.1 q.2 ++ DN.News.CommandSpec.crlf).flatten =
      seg a (e + 2) (DN.News.ArticleLines.nextOf a L sep) := by
  have ht := text_seg L s e h
  have hle := line_le h
  have hg := (DN.News.ArticleLines.nextOf_ge (DN.News.ArticleLines.lines_tail h).2).1
  rw [List.map_cons, List.flatten_cons] at ht
  dsimp only at ht hg
  rw [line_crlf h hle, seg_app a (cp := e + 2) (by omega) hg] at ht
  exact List.append_cancel_left ht

/-- A line's end written out is CRLF. -/
theorem ascii_crlf : DN.News.CommandSpec.ascii "\r\n" = DN.News.CommandSpec.crlf := by decide

/-- The server's part of Path, before what the field held. -/
def pathHead (ctx : ArticleSpec.Context) : Bytes :=
  DN.News.CommandSpec.ascii "Path: " ++ ctx.identity ++ DN.News.CommandSpec.ascii "!.POSTED"

/-- **Path when the article had one**: the server's part, a bang or fold, its first line from `r`, the rest. -/
theorem pathField_some (ctx : ArticleSpec.Context) {a : Bytes} {sep P e r : Nat} {L : List (Nat × Nat)}
    (h : Lines a P ((P, e) :: L) sep) (hr1 :
    P + DN.News.ArticleLines.nameLen a P e + 1 ≤ r) (hre : r ≤ e)
    (hws : ∀ j, P + DN.News.ArticleLines.nameLen a P e + 1 ≤ j → j < r → DN.News.CommandSpec.isWS a[j]! = true)
    (hstop : r = e ∨ DN.News.CommandSpec.isWS a[r]! = false) :
    ArticleSpec.pathField ArticleSpec.spec ctx (some (fieldOf a ((P, e) :: L.takeWhile (cont a)))) =
      pathHead ctx ++
      (if ArticleSpec.spec.lineMax < 15 + ctx.identity.length + (e - r) then DN.News.CommandSpec.ascii "\r\n !"
        else DN.News.CommandSpec.ascii "!") ++
      seg a r e ++ DN.News.CommandSpec.crlf ++ seg a (e + 2) (DN.News.ArticleLines.nextOf a L sep) := by
  have hea := (DN.News.ArticleLines.lines_mem h (P, e) List.mem_cons_self).2.2.2.2
  have hnl : (DN.News.ArticleLines.nameAt a (P, e)).length = DN.News.ArticleLines.nameLen a P e := by
    show (seg a P (P + DN.News.ArticleLines.nameLen a P e)).length = _
    rw [seg_length a (by omega) (by omega)]; omega
  have hrest : ((seg a P e).drop ((DN.News.ArticleLines.nameAt a (P, e)).length + 1)).dropWhile
      DN.News.CommandSpec.isWS = seg a r e := by
    rw [hnl, seg_drop, ← Nat.add_assoc]
    exact dropWS_seg (by omega) _ _ _ rfl hr1 hre hws hstop
  have hmore : ((L.takeWhile (cont a)).map (fun q => seg a q.1 q.2) |>.map (· ++ DN.News.CommandSpec.crlf)).flatten =
      seg a (e + 2) (DN.News.ArticleLines.nextOf a L sep) := by
    rw [List.map_map]; exact cont_seg h
  have hrl : (seg a r e).length = e - r := seg_length a hre (by omega)
  have hhl : (pathHead ctx).length = 14 + ctx.identity.length := by
    have h1 : "Path: ".length = 6 := rfl
    have h2 : "!.POSTED".length = 8 := rfl
    simp only [pathHead, List.length_append, ascii_length]; omega
  unfold ArticleSpec.pathField
  simp only [Option.map_some, fieldOf, ArticleSpec.Field.body, segs, List.map_cons, List.headD_cons]
  have hph : DN.News.CommandSpec.ascii "Path: " ++ ctx.identity ++ DN.News.CommandSpec.ascii "!.POSTED" =
    pathHead ctx := rfl
  have hcr : DN.News.CommandSpec.ascii "\r\n !" = DN.News.CommandSpec.crlf ++ DN.News.CommandSpec.ascii " !" := by
    decide
  have hbg : DN.News.CommandSpec.ascii "!" = [ArticleSpec.BANG] := by decide
  rw [hrest, hph, List.map_append, List.flatten_append, hmore]
  by_cases hc : ArticleSpec.spec.lineMax < 15 + ctx.identity.length + (e - r)
  · have hn : ¬((pathHead ctx ++ [ArticleSpec.BANG] ++ seg a r e).length ≤ ArticleSpec.spec.lineMax) := by
      simp only [List.length_append, hhl, hrl, List.length_singleton]; omega
    rw [if_pos hc, if_neg hn, hcr]
    simp only [List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, List.append_nil, List.append_assoc]
  · have hn : (pathHead ctx ++ [ArticleSpec.BANG] ++ seg a r e).length ≤ ArticleSpec.spec.lineMax := by
      simp only [List.length_append, hhl, hrl, List.length_singleton]; omega
    rw [if_neg hc, if_pos hn, hbg]
    simp only [List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, List.append_nil, List.append_assoc]

/-- **Path when the article had none.** -/
theorem pathField_none (ctx : ArticleSpec.Context) :
    ArticleSpec.pathField ArticleSpec.spec ctx none =
      pathHead ctx ++ DN.News.CommandSpec.ascii "!not-for-mail\r\n" := by
  show pathHead ctx ++ _ ++ _ = _
  rw [List.append_assoc, show DN.News.CommandSpec.ascii "!not-for-mail" ++ DN.News.CommandSpec.crlf =
    DN.News.CommandSpec.ascii "!not-for-mail\r\n" by decide]

/-- **A declaration** with the output as it is. -/
theorem add_dec (o : Oracle σ) {S : Word → Prop} {s1 : PancakeState σ} {A : Word} {m0 : Word → Word}
    {L : List (String × Value)} {P : Bytes} {x : String} {e : Syntax.PExpr} {E : PancakeExp}
    (he : Lower.lowerExp e = some E) (hx : Fresh x L = true) {val : Value}
    (hv : ∀ u M, RunF s1 L (· = M) u → (∀ y, ¬S y → M y = m0 y) → eval u E = some val) :
    Frag o [.dec x e] (AOut S s1 A m0 L P) (AOut S s1 A m0 ((x, val) :: L) P) :=
  frag_dec o he fun u ⟨M, h, hO, hfr⟩ => ⟨val, hv u M h hfr, M,
    ⟨⟨DN.News.ScanRun.vals_cons h.1.vals hx val, h.1.memaddrs, h.1.base, h.1.code, h.1.be⟩, h.2⟩, hO, hfr⟩

/-- Path's first line's white space, skipped. -/
def wsBody : List Syntax.PStmt :=
  [.ite (eLt (v "r0") (v "pe"))
    (ArticleProg.readIn "c" "r0" ++ [.ite (ArticleProg.isWS (v "c")) [inc "r0"] [.assign "g" (n 0)]])
    [.assign "g" (n 0)]]

theorem pathYes_g : guardL pathYes = guardS (.call "pf" "artField" [v "pp"]) ++
    ([.dec "pn" (wd xNl), .dec "pe" (wd xE1), .dec "r0" (eAdd (eAdd (v "pp") (v "pn")) (n 1)), .dec "g" (n 1),
     .while (v "g") wsBody,
     .ite (eLt (n ArticleSpec.spec.lineMax) (eAdd (n 15) (eAdd (v "idl") (eSub (v "pe") (v "r0")))))
       (putConst "\r\n !") (putConst "!")] : Ss) ++
    guardL (copyS "o2" (eAdd (n aInput) (v "r0")) (eSub (v "pe") (v "r0"))) ++ putConst "\r\n" ++
    guardL (copyS "o3" (eAdd (n (aInput + 2)) (v "pe")) (eSub (v "pf") (eAdd (v "pe") (n 2)))) := rfl

/-- The locals in Path's branch. -/
def pyL (A : Word) (RL IDL O P0 NX K E R G : Nat) : List (String × Value) :=
  [("g", BitVec.ofNat 64 G), ("r0", BitVec.ofNat 64 R), ("pe", BitVec.ofNat 64 E), ("pn", BitVec.ofNat 64 K),
   ("pf", BitVec.ofNat 64 NX), ("pp", BitVec.ofNat 64 P0), ("o", BitVec.ofNat 64 O), ("rl", BitVec.ofNat 64 RL),
   ("idl", BitVec.ofNat 64 IDL), ("a", A)]

/-- What the skip has seen: white space from `x` to `r`, and if it stopped, why. -/
def WsF (a : Bytes) (E x : Nat) (rg : Nat × Nat) : Prop :=
  x ≤ rg.1 ∧ rg.1 ≤ E ∧ (∀ j, x ≤ j → j < rg.1 → DN.News.CommandSpec.isWS a[j]! = true) ∧
    (rg.2 = 1 ∨ (rg.2 = 0 ∧ (rg.1 = E ∨ DN.News.CommandSpec.isWS a[rg.1]! = false)))

def WsI (s1 : PancakeState σ) (A : Word) (m0 : Word → Word) (a : Bytes) (RL IDL O P0 NX K E x : Nat) (H : Bytes) :
    Assn σ := fun u =>
  ∃ rg, WsF a E x rg ∧ AOut (AddScr A) s1 A m0 (pyL A RL IDL O P0 NX K E rg.1 rg.2) H u

theorem wsI_clock {s1 : PancakeState σ} {A : Word} {m0 : Word → Word} {a : Bytes} {RL IDL O P0 NX K E x : Nat}
    {H : Bytes} : Safe.ClockFree (WsI s1 A m0 a RL IDL O P0 NX K E x H) :=
  fun u k ⟨rg, hf, hO⟩ => ⟨rg, hf, aout_clock u k hO⟩

/-- **One step of the skip.** -/
theorem ws_body (o : Oracle σ) {R : Ret} {A : Word} {s1 : PancakeState σ} (hA8 : A.toNat % 8 = 0)
    {m0 : Word → Word} {a : Bytes} (hlen : a.length ≤ artMax) (hin : InputAt m0 s1.memaddrs s1.be A a)
    {RL IDL O P0 NX K E x : Nat} (hE : E < a.length) {H : Bytes} :
    FragR o R wsBody (fun u => WsI s1 A m0 a RL IDL O P0 NX K E x H u ∧ eval u (.var "g") ≠ some 0)
      (WsI s1 A m0 a RL IDL O P0 NX K E x H) := by
  have hM := artMax_eq
  have hlow : LowKK wsBody := lowK_any _ (k := .skip) rfl
  refine fragR_conseq (P0 := fun u => ∃ rg : Nat × Nat, (WsF a E x rg ∧ rg.2 = 1) ∧
    AOut (AddScr A) s1 A m0 (pyL A RL IDL O P0 NX K E rg.1 rg.2) H u) ?_
    (fun u (h : WsI s1 A m0 a RL IDL O P0 NX K E x H u ∧ eval u (.var "g") ≠ some 0) => by
      obtain ⟨⟨rg, hf, hO⟩, hne⟩ := h
      refine ⟨rg, ⟨hf, ?_⟩, hO⟩
      rcases hf.2.2.2 with h1 | ⟨h0, -⟩
      · exact h1
      · obtain ⟨M, hr, -⟩ := hO
        exact absurd (by rw [ev_var (vals_lookup hr.1.vals rfl), h0]; rfl) hne) fun _ h => h
  refine fragR_exists hlow fun rg => ?_
  obtain ⟨r, g⟩ := rg
  refine fragR_pure (WsF a E x (r, g) ∧ g = 1) (fun u h => h.1) hlow fun ⟨⟨hxr, hrE, hws, _⟩, hg⟩ => ?_
  refine fragR_conseq ?_ (fun u h => h.2) fun _ h => h
  simp only at hxr hrE hws hg ⊢
  subst hg
  refine fragR_if o rfl (lowK_any _ (k := .skip) rfl) (lowK_any _ (k := .skip) rfl) wsI_clock
    (fun u y w ⟨rg, hf, hO⟩ hy => by
      change y ∈ ["c"] at hy
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hy; subst hy
      exact ⟨rg, hf, aout_restore hO rfl w⟩) (fun u y w h hy => by change y ∈ [] at hy; cases hy)
    (b := decide (r < E)) (fun u ⟨M, hr, _⟩ => DN.News.FramerCode.eval_lt (a := .var "r0") (b := .var "pe")
      (by omega) (by omega) (ev_var (vals_lookup hr.1.vals rfl)) (ev_var (vals_lookup hr.1.vals rfl)))
    (fun hq => ?_) (fun hq => ?_)
  · have hq := of_decide_eq_true hq
    refine fragR_append (xs := [_]) (fragR_of (kept_frag o (by decide) aout_clock fun u ⟨M, hr, _⟩ =>
      ⟨r, vals_lookup hr.1.vals rfl, by omega⟩)) ?_
    refine fragR_append (xs := [_]) (fragR_of (add_dec o rfl rfl (val := BitVec.ofNat 64 (a[r]!).toNat)
      fun u M h hfr => inByte_eval (input_run (input_frame hA8 hlen hfr hin) h) (vals_lookup h.1.vals rfl) (by omega)
        (vals_lookup h.1.vals rfl))) ?_
    refine fragR_if o rfl (lowK_any _ (k := .skip) rfl) (lowK_any _ (k := .skip) rfl) wsI_clock
      (fun u y w h hy => by change y ∈ [] at hy; cases hy) (fun u y w h hy => by change y ∈ [] at hy; cases hy)
      (b := DN.News.CommandSpec.isWS a[r]!) (fun u ⟨M, hr, _⟩ => by
        show eval u _ = some (bw (DN.News.CommandSpec.isWS a[r]!))
        rw [← isWS_bytes, ← DN.News.AbnfComment.bw_or]
        exact DN.News.FramerCode.eval_or (DN.News.FramerCode.eval_eq (byte_lt _) (by decide)
          (ev_var (vals_lookup hr.1.vals rfl)) rfl)
          (DN.News.FramerCode.eval_eq (byte_lt _) (by decide) (ev_var (vals_lookup hr.1.vals rfl)) rfl))
      (fun hw => ?_) (fun hw => ?_)
    · have hws' : ∀ j, x ≤ j → j < r + 1 → DN.News.CommandSpec.isWS a[j]! = true := fun j h1 h2 => by
        rcases Nat.lt_or_ge j r with h3 | h3
        · exact hws j h1 h3
        · rw [show j = r by omega]; exact hw
      refine fragR_conseq (add_set o (x := "r0") rfl rfl (val := BitVec.ofNat 64 (r + 1)) fun u M h =>
        WpBytes.eval_add (ev_var (vals_lookup h.1.vals rfl)) rfl) (fun _ h => h) fun u h => ⟨(r + 1, 1),
          ⟨by omega, by omega, hws', .inl rfl⟩, aout_of h fun q hq => by
              simp only [pyL, List.mem_cons, List.mem_nil_iff, or_false] at hq
              rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl⟩
    · refine fragR_conseq (add_set o (x := "g") rfl rfl (val := BitVec.ofNat 64 0) fun u M h => rfl) (fun _ h => h)
        fun u h => ⟨(r, 0), ⟨hxr, hrE, hws, .inr ⟨rfl, .inr (by simpa using hw)⟩⟩, aout_of h fun q hq => by
          simp only [pyL, List.mem_cons, List.mem_nil_iff, or_false] at hq
          rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl⟩
  · have hq := of_decide_eq_false hq
    refine fragR_conseq (add_set o (x := "g") rfl rfl (val := BitVec.ofNat 64 0) fun u M h => rfl) (fun _ h => h)
      fun u h => ⟨(r, 0), ⟨hxr, hrE, hws, .inr ⟨rfl, .inl (by omega)⟩⟩, aout_of h fun q hq => by
        simp only [pyL, List.mem_cons, List.mem_nil_iff, or_false] at hq
        rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl⟩

/-- **A scalar word declared**, its value known from the memory. -/
theorem add_decW (o : Oracle σ) {S : Word → Prop} {s1 : PancakeState σ} {A : Word} {m0 : Word → Word}
    {L : List (String × Value)} {P : Bytes} (hD : ArtDom A s1.memaddrs) (hla : L.lookup "a" = some A) {x : String}
    (hx : Fresh x L = true) {i : Nat} (hi : i < 32) {W : Word} {X : (Word → Word) → Prop}
    (hX : ∀ m, X m → m (at_ A (ArticleProg.w i)) = W) :
    Frag o [.dec x (wd (ArticleProg.w i))] (fun u => AOut S s1 A m0 L P u ∧ X u.memory)
      (fun u => AOut S s1 A m0 ((x, W) :: L) P u ∧ X u.memory) :=
  frag_dec o (wd_lower i) fun u ⟨⟨M, h, hO, hfr⟩, hx'⟩ => ⟨W, by
    rw [loadA_eval h.1.memaddrs (artDom_w hD hi) (atA_eval (vals_lookup h.1.vals hla))]
    exact congrArg some (hX _ hx'), ⟨M, ⟨⟨DN.News.ScanRun.vals_cons h.1.vals hx W, h.1.memaddrs, h.1.base, h.1.code,
      h.1.be⟩, h.2⟩, hO, hfr⟩, hx'⟩

/-- Path's locals before its branch. -/
def ppL (A : Word) (RL IDL O P0 : Nat) : List (String × Value) :=
  [("pp", BitVec.ofNat 64 P0), ("o", BitVec.ofNat 64 O), ("rl", BitVec.ofNat 64 RL), ("idl", BitVec.ofNat 64 IDL),
   ("a", A)]

/-- The lasting locals and the output's end. -/
def outL (A : Word) (RL IDL O : Nat) : List (String × Value) :=
  [("o", BitVec.ofNat 64 O), ("rl", BitVec.ofNat 64 RL), ("idl", BitVec.ofNat 64 IDL), ("a", A)]

/-- **The locals after an output step**: `o` moved past it, the others `T` as before. -/
theorem o_next {L T : List (String × Value)} (hT : ∀ q ∈ T, q.1 ≠ "o" ∧ L.lookup q.1 = some q.2) (O : Nat) :
    ∀ q ∈ ("o", BitVec.ofNat 64 O) :: T, (("o", BitVec.ofNat 64 O) :: without "o" L).lookup q.1 = some q.2 := by
  intro q hq
  rcases List.mem_cons.1 hq with rfl | hq
  · exact DN.News.ScanRun.lookup_head _ _ _
  · obtain ⟨h1, h2⟩ := hT q hq
    rw [DN.News.ScanRun.lookup_cons_ne h1, DN.News.ScanRun.lookup_without h1]; exact h2

theorem ascii_lit (s : String) (h : (s.toList.map Char.toNat).all (· < 256) = true) : Ascii s := by
  unfold Ascii codes
  intro c hc
  have := List.all_eq_true.1 h c hc
  simpa using this

/-- **Path when the article has one.** -/
theorem path_yes (o : Oracle σ) {R : Ret} {A : Word} {s1 : PancakeState σ} (hA : Area ArticleProg.ofs A s1)
    (hD : ArtDom A s1.memaddrs) (hcode : ArtCode s1.code) (hsz : ArticleProg.size esP < 2 ^ 40) {m0 : Word → Word}
    {a : Bytes} (hlen : a.length ≤ artMax) (hin : InputAt m0 s1.memaddrs s1.be A a) (hb : m0 (at_ A aBroken) = 0)
    {SEP : Nat} (hsep : m0 (at_ A xSep) = BitVec.ofNat 64 SEP) {P0 e0 : Nat} {more : List (Nat × Nat)}
    (hf : DN.News.ArticleLines.FieldAt a SEP P0 e0 more) (ctx : ArticleSpec.Context) (hid : ctx.identity.length ≤ 200)
    {RL : Nat} (hfit : (ArticleSpec.pathField ArticleSpec.spec ctx
      (some (fieldOf a ((P0, e0) :: more.takeWhile (cont a))))).length ≤ ArticleProg.outMax) :
    FragR o R (guardL pathYes)
      (AOut (AddScr A) s1 A m0 (ppL A RL ctx.identity.length (pathHead ctx).length P0) (pathHead ctx))
      (AOut (AddScr A) s1 A m0 (outL A RL ctx.identity.length (ArticleSpec.pathField ArticleSpec.spec ctx
        (some (fieldOf a ((P0, e0) :: more.takeWhile (cont a))))).length)
        (ArticleSpec.pathField ArticleSpec.spec ctx (some (fieldOf a ((P0, e0) :: more.takeWhile (cont a)))))) := by
  have hA8 := hA.hA
  have hM := artMax_eq
  let H := pathHead ctx
  let IDL := ctx.identity.length
  let K := DN.News.ArticleLines.nameLen a P0 e0
  let NX := DN.News.ArticleLines.nextOf a more SEP
  have hL := hf.lines
  have hcol := DN.News.ArticleLines.fieldAt_colon hf
  have hK1 : P0 + K < e0 := hcol.2.1
  have hmem := DN.News.ArticleLines.lines_mem hL (P0, e0) List.mem_cons_self
  have he0 : e0 < a.length := hmem.2.2.2.2
  have he2 : e0 + 2 ≤ SEP := hmem.2.2.1
  have hmore := (DN.News.ArticleLines.lines_tail hL).2
  have hNX : e0 + 2 ≤ NX := (DN.News.ArticleLines.nextOf_ge hmore).1
  have hNXs : NX ≤ SEP := (DN.News.ArticleLines.lines_sep (lines_next more (e0 + 2) hmore)).1
  have hSEP : SEP < a.length := (DN.News.ArticleLines.lines_sep hL).2.2
  have hhl : H.length = 14 + IDL := by
    have h1 : "Path: ".length = 6 := rfl
    have h2 : "!.POSTED".length = 8 := rfl
    simp only [H, IDL, pathHead, List.length_append, ascii_length]; omega
  rw [pathYes_g]
  -- the field's end, its name's length, its first line's end
  refine fragR_append (xs := guardS _) (M := fun u => AOut (AddScr A) s1 A m0 (("pf", BitVec.ofNat 64 NX) ::
    ppL A RL IDL H.length P0) H u ∧ (u.memory (at_ A (ArticleProg.w 17)) = BitVec.ofNat 64 K ∧
      u.memory (at_ A (ArticleProg.w 18)) = BitVec.ofNat 64 e0))
    (aout_lift o (lowK_any _ (k := .skip) rfl) fun M hO hfr => fragR_conseq (fieldCall_frag o hA hD hcode hlen
      (rt := "pf") (by decide) (l := ppL A RL IDL H.length P0) rfl rfl (e1 := v "pp") rfl hf
      (fun u h => ev_var (vals_lookup h.1.vals rfl)) (input_frame hA8 hlen hfr hin) ((hfr _ broken_add).trans hb)
      ((hfr _ (not_addScr_w (i := 16) (by decide) (by decide))).trans hsep)) (fun _ h => h) fun u h =>
        ⟨⟨_, h, (fieldMem_add hA8 K e0 hO hfr).1, (fieldMem_add hA8 K e0 hO hfr).2⟩,
          by rw [h.2]; exact fieldMem_nl A K e0 M, by rw [h.2]; exact fieldMem_e1 A K e0 M⟩) ?_
  let XM : (Word → Word) → Prop := fun m => m (at_ A (ArticleProg.w 17)) = BitVec.ofNat 64 K ∧
    m (at_ A (ArticleProg.w 18)) = BitVec.ofNat 64 e0
  refine fragR_append (xs := [_]) (fragR_of (add_decW o hD rfl (x := "pn") rfl (i := 17) (by decide) (X := XM)
    fun m h => h.1)) ?_
  refine fragR_append (xs := [_]) (fragR_of (add_decW o hD rfl (x := "pe") rfl (i := 18) (by decide) (X := XM)
    fun m h => h.2)) ?_
  refine fragR_conseq ?_ (fun u h => h.1) fun _ h => h
  refine fragR_append (xs := [_]) (fragR_of (add_dec o rfl rfl (val := BitVec.ofNat 64 (P0 + K + 1))
    fun u M h _ => WpBytes.eval_add (WpBytes.eval_add (ev_var (vals_lookup h.1.vals rfl))
      (ev_var (vals_lookup h.1.vals rfl))) rfl)) ?_
  refine fragR_append (xs := [_]) (fragR_of (add_dec o rfl rfl (val := BitVec.ofNat 64 1) fun u M h _ => rfl)) ?_
  -- the white space skipped
  refine fragR_append (xs := [_]) (fragR_conseq (fragR_while o (c := v "g") rfl (lowK_any _ (k := .skip) rfl)
    (I := WsI s1 A m0 a RL IDL H.length P0 NX K e0 (P0 + K + 1) H) wsI_clock
    (fun u y w h hy => by change y ∈ [] at hy; cases hy)
    (fun u ⟨rg, _, M, hr, _⟩ => ⟨_, ev_var (vals_lookup hr.1.vals rfl)⟩)
    (ws_body o hA8 hlen hin he0)) (fun u h => ⟨(P0 + K + 1, 1), ⟨Nat.le_refl _, by omega,
      fun j h1 h2 => absurd h2 (by omega), .inl rfl⟩, h⟩)
    (P' := fun u => ∃ rg : Nat × Nat, (WsF a e0 (P0 + K + 1) rg ∧ rg.2 = 0) ∧
      AOut (AddScr A) s1 A m0 (pyL A RL IDL H.length P0 NX K e0 rg.1 rg.2) H u)
    fun u ⟨⟨rg, hw, hO⟩, h0⟩ => ⟨rg, ⟨hw, by
      obtain ⟨M, hr, _⟩ := hO
      rw [ev_var (vals_lookup hr.1.vals rfl)] at h0
      rcases hw.2.2.2 with h1 | ⟨h1, _⟩
      · rw [h1] at h0; exact absurd h0 (by decide)
      · exact h1⟩, hO⟩) ?_
  have hlowR : LowKK ([.ite (eLt (n ArticleSpec.spec.lineMax) (eAdd (n 15) (eAdd (v "idl") (eSub (v "pe") (v "r0")))))
       (putConst "\r\n !") (putConst "!")] ++
    guardL (copyS "o2" (eAdd (n aInput) (v "r0")) (eSub (v "pe") (v "r0"))) ++ putConst "\r\n" ++
    guardL (copyS "o3" (eAdd (n (aInput + 2)) (v "pe")) (eSub (v "pf") (eAdd (v "pe") (n 2))))) :=
    lowKK_append (lowKK_append (lowKK_append (lowK_any _ (k := .skip) rfl) (lowK_any _ (k := .skip) rfl))
      (putConst_low _)) (lowK_any _ (k := .skip) rfl)
  refine fragR_exists hlowR fun rg => ?_
  obtain ⟨r, g⟩ := rg
  refine fragR_pure (WsF a e0 (P0 + K + 1) (r, g) ∧ g = 0) (fun u h => h.1) hlowR
    fun ⟨⟨hr1, hre, hws, hst⟩, hg⟩ => ?_
  refine fragR_conseq ?_ (fun u h => h.2) fun _ h => h
  simp only at hr1 hre hws hst hg ⊢
  subst hg
  have hstop : r = e0 ∨ DN.News.CommandSpec.isWS a[r]! = false := by
    rcases hst with h1 | ⟨_, h2⟩
    · exact absurd h1 (by decide)
    · exact h2
  have hPF := pathField_some ctx hL hr1 hre hws hstop
  rw [hPF]
  rw [hPF] at hfit
  obtain ⟨X, hXdef⟩ : ∃ X, X = if ArticleSpec.spec.lineMax < 15 + ctx.identity.length + (e0 - r) then
      DN.News.CommandSpec.ascii "\r\n !" else DN.News.CommandSpec.ascii "!" := ⟨_, rfl⟩
  rw [← hXdef]
  rw [← hXdef] at hfit
  have hseg1 : (seg a r e0).length = e0 - r := seg_length a hre (by omega)
  have hseg2 : (seg a (e0 + 2) (DN.News.ArticleLines.nextOf a more SEP)).length =
      DN.News.ArticleLines.nextOf a more SEP - (e0 + 2) := seg_length a hNX (by omega)
  have hcrl : DN.News.CommandSpec.crlf.length = 2 := rfl
  have hfit' := hfit
  have hhl' : (pathHead ctx).length = 14 + ctx.identity.length := hhl
  simp only [List.length_append, hhl', hseg1, hseg2, hcrl] at hfit'
  -- a bang, or a fold
  refine fragR_append (xs := [_]) (fragR_if o rfl (putConst_low _) (putConst_low _)
    (Q := AOut (AddScr A) s1 A m0 (("o", BitVec.ofNat 64 (H ++ X).length) ::
      without "o" (pyL A RL IDL H.length P0 NX K e0 r 0)) (H ++ X)) aout_clock
    (fun u y w h hy => by rw [putConst_declared] at hy; cases hy)
    (fun u y w h hy => by rw [putConst_declared] at hy; cases hy)
    (b := decide (ArticleSpec.spec.lineMax < 15 + ctx.identity.length + (e0 - r))) (fun u ⟨M, hr, _⟩ => by
      have e := DN.News.FramerCode.eval_lt (t := u) (a := .const (BitVec.ofNat 64 ArticleSpec.spec.lineMax))
        (x := ArticleSpec.spec.lineMax) (y := 15 + (IDL + (e0 - r))) (by decide) (by omega) rfl
        (WpBytes.eval_add (e := .const (BitVec.ofNat 64 15)) rfl
          (WpBytes.eval_add (e := .var "idl") (ev_var (vals_lookup hr.1.vals rfl))
          (DN.News.ArticleCal.ev_subE (a := .var "pe") (b := .var "r0") (ev_var (vals_lookup hr.1.vals rfl))
            (ev_var (vals_lookup hr.1.vals rfl)) hre (by omega))))
      rw [← Nat.add_assoc] at e; exact e) (fun hc => ?_) (fun hc => ?_)) ?_
  · have hc' := of_decide_eq_true hc
    have hX : X = DN.News.CommandSpec.ascii "\r\n !" := hXdef.trans (if_pos hc')
    rw [hX]
    exact add_const o scr_add hD hA8 rfl rfl (ascii_lit _ rfl) (by
      rw [hX] at hfit'; simp only [ascii_length] at hfit'; show (pathHead ctx).length + _ ≤ _; omega)
  · have hc' := of_decide_eq_false hc
    have hX : X = DN.News.CommandSpec.ascii "!" := hXdef.trans (if_neg hc')
    rw [hX]
    exact add_const o scr_add hD hA8 rfl rfl (ascii_lit _ rfl) (by
      rw [hX] at hfit'; simp only [ascii_length] at hfit'; show (pathHead ctx).length + _ ≤ _; omega)
  -- the first line's rest
  have hS2 := input_seg hin (P := r) (E := e0) hre (by omega)
  refine fragR_append (xs := guardL (copyS "o2" _ _)) (add_copy o scr_add hA hD hcode hsz hb
    (L := ("o", BitVec.ofNat 64 (H ++ X).length) :: without "o" (pyL A RL IDL H.length P0 NX K e0 r 0)) rfl
    (name := "o2") (by decide) (by decide) rfl (P := H ++ X) (SRC := seg a r e0) rfl (S0 := aInput + r) hS2
    (fun i hi => input_add hA8 (by rw [hseg1] at hi; omega))
    (by have := input_below; have := sets_le_X; have := X_val; rw [hseg1, xDec_eq]; omega)
    (by show (pathHead ctx ++ X).length + _ ≤ _; simp only [List.length_append, hhl', hseg1]; omega)
    (lowK_any _ (k := .skip) rfl) rfl rfl
    (fun u M h _ => WpBytes.eval_add (e := .const (BitVec.ofNat 64 aInput)) rfl (ev_var (vals_lookup h.1.vals rfl)))
    (fun u M h _ => by
      rw [hseg1]
      exact DN.News.ArticleCal.ev_subE (a := .var "pe") (b := .var "r0") (ev_var (vals_lookup h.1.vals rfl))
        (ev_var (vals_lookup h.1.vals rfl)) hre (by omega))) ?_
  refine fragR_append (xs := putConst "\r\n") (add_const o scr_add hD hA8 rfl rfl (ascii_lit _ rfl) (by
    show (pathHead ctx ++ X ++ seg a r e0).length + _ ≤ _
    simp only [List.length_append, hhl', hseg1]
    have : "\r\n".length = 2 := rfl
    omega)) ?_
  -- the field's other lines
  have hS3 := input_seg hin (P := e0 + 2) (E := DN.News.ArticleLines.nextOf a more SEP) hNX (by omega)
  refine fragR_conseq (add_copy o scr_add hA hD hcode hsz hb rfl (name := "o3") (by decide) (by decide) rfl
    (P := H ++ X ++ seg a r e0 ++ DN.News.CommandSpec.ascii "\r\n")
    (SRC := seg a (e0 + 2) (DN.News.ArticleLines.nextOf a more SEP)) rfl (S0 := aInput + (e0 + 2)) hS3
    (fun i hi => input_add hA8 (by rw [hseg2] at hi; omega))
    (by have := input_below; have := sets_le_X; have := X_val; rw [hseg2, xDec_eq]; omega)
    (by
      show (pathHead ctx ++ X ++ seg a r e0 ++ DN.News.CommandSpec.ascii "\r\n").length + _ ≤ _
      simp only [List.length_append, hhl', hseg1, hseg2, ascii_length]
      have : "\r\n".length = 2 := rfl
      omega)
    (lowK_any _ (k := .skip) rfl) rfl rfl
    (fun u M h _ => by
      rw [show aInput + (e0 + 2) = aInput + 2 + e0 by omega]
      exact WpBytes.eval_add (e := .const (BitVec.ofNat 64 (aInput + 2))) rfl (ev_var (vals_lookup h.1.vals rfl)))
    (fun u M h _ => by
      rw [hseg2]
      exact DN.News.ArticleCal.ev_subE (a := .var "pf") (b := .op .add (.var "pe") (.const (BitVec.ofNat 64 2)))
        (ev_var (vals_lookup h.1.vals rfl)) (WpBytes.eval_add (ev_var (vals_lookup h.1.vals rfl)) rfl) hNX
        (by omega))) (fun _ h => h) fun u h => ?_
  have hcr := ascii_crlf
  rw [hcr] at h
  exact aout_of h fun q hq => by
    simp only [outL, List.mem_cons, List.mem_nil_iff, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl <;> rfl

/-! ## The first fields -/

/-- The first field named `nm` among the groups. -/
def firstG (a : Bytes) (L : List (Nat × Nat)) (nm : String) : Option (List (Nat × Nat)) :=
  (groups a L).find? fun g => ArticleSpec.named (DN.News.ArticleLines.nameAt a (g.headD (0, 0))) nm

/-- Where the first field named `nm` starts. -/
def firstP (a : Bytes) (L : List (Nat × Nat)) (nm : String) : Option Nat :=
  (firstG a L nm).map fun g => (g.headD (0, 0)).1

/-- A place or none as a word: none is -1. -/
def optW (p : Option Nat) : Word := (p.map (BitVec.ofNat 64)).getD (BitVec.ofNat 64 (2 ^ 64 - 1))

/-- The first fields' table holds, for `nm`, where its first field starts, or -1. -/
def FirstW (A : Word) (m : Word → Word) (a : Bytes) (L : List (Nat × Nat)) (nm : String) : Prop :=
  m (at_ A (ArticleProg.xFirst + 8 * ArticleProg.entryOf esP nm)) = optW (firstP a L nm)

theorem find_fields (a : Bytes) (L : List (Nat × Nat)) (nm : String) :
    ArticleSpec.find? ((groups a L).map (fieldOf a)) nm = (firstG a L nm).map (fieldOf a) := by
  unfold ArticleSpec.find? firstG; rw [List.find?_map]; rfl

theorem has_fields (a : Bytes) (L : List (Nat × Nat)) (nm : String) :
    ArticleSpec.has ((groups a L).map (fieldOf a)) nm = (firstP a L nm).isSome := by
  unfold ArticleSpec.has firstP; rw [find_fields]; cases firstG a L nm <;> rfl

/-- **A group is a field's lines**: its first, no continuation, and the continuations after it. -/
theorem mem_groups {a : Bytes} {sep : Nat} : ∀ (n : Nat) (L : List (Nat × Nat)) (s : Nat), L.length ≤ n →
    Lines a s L sep → (∀ q r, L = q :: r → cont a q = false) → ∀ g ∈ groups a L,
    ∃ P e more, g = (P, e) :: more.takeWhile (cont a) ∧ Lines a P ((P, e) :: more) sep ∧ cont a (P, e) = false ∧
      (P, e) ∈ L
  | _, [], _, _, _, _, g, hg => by rw [groups] at hg; nomatch hg
  | 0, _ :: _, _, hn, _, _, _, _ => absurd hn (by simp)
  | n + 1, (q1, q2) :: more, s, hn, hL, hc, g, hg => by
    rw [groups_cons] at hg
    rcases List.mem_cons.1 hg with rfl | hg
    · have h1 := (DN.News.ArticleLines.lines_tail hL).1
      simp only at h1; subst h1
      exact ⟨q1, q2, more, rfl, hL, hc _ _ rfl, List.mem_cons_self⟩
    · obtain ⟨P, e, more', h1, h2, h3, h4⟩ := mem_groups n (more.dropWhile (cont a)) _
        (by have := DN.News.ArticleLines.dropWhile_len (cont a) more; simp only [List.length_cons] at hn; omega)
        (lines_next more (q2 + 2) (DN.News.ArticleLines.lines_tail hL).2) (fun q r h => dropWhile_head _ _ q r h) g hg
      exact ⟨P, e, more', h1, h2, h3, List.mem_cons_of_mem _ (List.dropWhile_subset _ h4)⟩

/-- **The first field of a name is a field**: where it starts, its lines, its name. -/
theorem first_at {a : Bytes} {SEP : Nat} {L : List (Nat × Nat)} (hL : Lines a 0 L SEP)
    (hok : L.any (DN.News.ArticleLines.malLine a) = false) {nm : String} {g : List (Nat × Nat)}
    (hg : firstG a L nm = some g) :
    ∃ P e more, g = (P, e) :: more.takeWhile (cont a) ∧ DN.News.ArticleLines.FieldAt a SEP P e more ∧
      ArticleSpec.named (DN.News.ArticleLines.nameAt a (P, e)) nm = true ∧ firstP a L nm = some P := by
  have hm := List.mem_of_find?_eq_some hg
  have hn := List.find?_some hg
  have hc0 : ∀ q r, L = q :: r → cont a q = false := fun q r hqr => by
    subst hqr
    have := List.any_eq_false.1 hok q List.mem_cons_self
    have h0 := (DN.News.ArticleLines.lines_tail hL).1
    cases hc : cont a q
    · rfl
    · simp [DN.News.ArticleLines.malLine, hc, h0] at this
  obtain ⟨P, e, more, rfl, h2, h3, h4⟩ := mem_groups L.length L 0 (Nat.le_refl _) hL hc0 g hm
  have hmal : DN.News.ArticleLines.malName a (P, e) = false := by
    have := List.any_eq_false.1 hok (P, e) h4
    simpa [DN.News.ArticleLines.malLine, h3] using this
  refine ⟨P, e, more, rfl, ⟨h2, h3, hmal⟩, hn, ?_⟩
  unfold firstP; rw [hg]; rfl

theorem first_none {a : Bytes} {L : List (Nat × Nat)} {nm : String} (h : firstG a L nm = none) :
    firstP a L nm = none := by unfold firstP; rw [h]; rfl

theorem wd_lowerX {x : Nat} (hx : (x == 0) = false) :
    Lower.lowerExp (wd x) = some (.loadWord (.op .add (.var "a") (.const (BitVec.ofNat 64 x)))) := by
  simp only [wd, word, Syntax.atOff, hx, Bool.false_eq_true, if_false]; rfl

theorem entry_le (es : List String) (s : String) : ArticleProg.entryOf es s ≤ es.length := by
  unfold ArticleProg.entryOf
  cases h : es.findIdx? (fun x => ArticleProg.lowerS x == ArticleProg.lowerS s) with
  | none => exact Nat.le_refl _
  | some i => exact Nat.le_of_lt (List.findIdx?_eq_some_iff_findIdx_eq.1 h).1

theorem entry_le55 (s : String) : ArticleProg.entryOf esP s ≤ 55 := esP_length ▸ entry_le esP s

theorem xFirst_le_size (es : List String) : ArticleProg.xFirst ≤ ArticleProg.size es := by
  have := xFirst_le_nameT es
  simp only [ArticleProg.size, ArticleProg.xNameBytes]; omega

theorem first_dom {A : Word} {dm : Word → Bool} {es : List String} (hT : TabDom A dm es) {k : Nat}
    (hk : k ≤ es.length) : dm (at_ A (ArticleProg.xFirst + 8 * k)) = true := by
  refine hT _ (Nat.le_add_right _ _) ?_ (by have := xFirst_mod; omega)
  simp only [ArticleProg.size, ArticleProg.xNameBytes, ArticleProg.xNameT, ArticleProg.xRuleT, ArticleProg.xFlags,
    ArticleProg.E]
  omega

/-- **A first field's place read** from the table. -/
theorem first_eval {s1 u : PancakeState σ} {A : Word} {S : Word → Prop} {m0 M : Word → Word}
    {L : List (String × Value)} (hla : L.lookup "a" = some A) {es : List String} (hT : TabDom A s1.memaddrs es)
    (hsz : ArticleProg.size es < 2 ^ 40) (hS : Scr A S) (h : RunF s1 L (· = M) u) (hfr : ∀ x, ¬S x → M x = m0 x)
    {nm : String} :
    eval u (.loadWord (.op .add (.var "a") (.const (BitVec.ofNat 64 (ArticleProg.xFirst +
      8 * ArticleProg.entryOf es nm))))) =
      some (m0 (at_ A (ArticleProg.xFirst + 8 * ArticleProg.entryOf es nm))) := by
  have hk := entry_le es nm
  rw [loadA_eval h.1.memaddrs (first_dom hT hk) (atA_eval (vals_lookup h.1.vals hla)), h.2]
  refine congrArg some (hfr _ (scr_not hS (high_add (Nat.le_add_right _ _) ?_)))
  simp only [ArticleProg.size, ArticleProg.xNameBytes, ArticleProg.xNameT, ArticleProg.xRuleT, ArticleProg.xFlags,
    ArticleProg.E] at hsz
  omega

theorem flag_eval {u : PancakeState σ} {F : PancakeExp} {p : Option Nat} (hp : ∀ x, p = some x → x < 2 ^ 63)
    (h : eval u F = some (optW p)) : eval u (.cmp .notLess F (.const (BitVec.ofNat 64 0))) = some (bw p.isSome) := by
  cases p with
  | none => simp only [eval, h]; rfl
  | some x =>
    exact DN.News.FramerCode.eval_le (a := .const (BitVec.ofNat 64 0)) (b := F) (x := 0) (y := x) (by decide)
      (hp x rfl) rfl h

theorem lt0_eval {u : PancakeState σ} {F : PancakeExp} {p : Option Nat} (hp : ∀ x, p = some x → x < 2 ^ 63)
    (h : eval u F = some (optW p)) : eval u (.cmp .less F (.const (BitVec.ofNat 64 0))) = some (bw p.isNone) := by
  cases p with
  | none => simp only [eval, h]; rfl
  | some x =>
    have := DN.News.FramerCode.eval_lt (a := F) (b := .const (BitVec.ofNat 64 0)) (x := x) (y := 0) (hp x rfl)
      (by decide) h rfl
    rw [this]; rfl

theorem firstP_lt {a : Bytes} {SEP : Nat} {L : List (Nat × Nat)} (hL : Lines a 0 L SEP)
    (hok : L.any (DN.News.ArticleLines.malLine a) = false) {nm : String} :
    ∀ x, firstP a L nm = some x → x < a.length := fun x hx => by
  cases hg : firstG a L nm with
  | none => rw [first_none hg] at hx; nomatch hx
  | some g =>
    obtain ⟨P, e, more, -, hf, -, hP⟩ := first_at hL hok hg
    rw [hP] at hx
    have hx' : P = x := Option.some.inj hx
    subst hx'
    have := DN.News.ArticleLines.lines_mem hf.lines (P, e) List.mem_cons_self
    omega

theorem first_ne0 (es : List String) (s : String) :
    ((ArticleProg.xFirst + 8 * ArticleProg.entryOf es s) == 0) = false := by
  have := xFirst_eq; simp only [beq_eq_false_iff_ne]; omega

theorem decl_pathYes : declared (guardL pathYes) = ["pf", "pn", "pe", "r0", "g", "o2", "o3"] := rfl

/-- **Path**: the server's part before the field the article had, or before `not-for-mail`. -/
theorem path_sel (o : Oracle σ) {R : Ret} {A : Word} {s1 : PancakeState σ} (hA : Area ArticleProg.ofs A s1)
    (hD : ArtDom A s1.memaddrs) (hcode : ArtCode s1.code) (hsz : ArticleProg.size esP < 2 ^ 40) {m0 : Word → Word}
    {a : Bytes} (hlen : a.length ≤ artMax) (hin : InputAt m0 s1.memaddrs s1.be A a) (hb : m0 (at_ A aBroken) = 0)
    {SEP : Nat} (hsep : m0 (at_ A xSep) = BitVec.ofNat 64 SEP) (hT : TabDom A s1.memaddrs esP)
    {L : List (Nat × Nat)} (hL : Lines a 0 L SEP) (hok : L.any (DN.News.ArticleLines.malLine a) = false)
    (hfw : FirstW A m0 a L "Path") (ctx : ArticleSpec.Context) (hid : ctx.identity.length ≤ 200) {RL : Nat}
    (hfit : (ArticleSpec.pathField ArticleSpec.spec ctx
      (ArticleSpec.find? ((groups a L).map (fieldOf a)) "Path")).length ≤ ArticleProg.outMax) :
    FragR o R ([.dec "pp" (firstOf esP "Path"),
        .ite (eLe (n 0) (v "pp")) (guardL pathYes) (putConst "!not-for-mail\r\n")] : Ss)
      (AOut (AddScr A) s1 A m0 (outL A RL ctx.identity.length (pathHead ctx).length) (pathHead ctx))
      (AOut (AddScr A) s1 A m0 (outL A RL ctx.identity.length (ArticleSpec.pathField ArticleSpec.spec ctx
        (ArticleSpec.find? ((groups a L).map (fieldOf a)) "Path")).length)
        (ArticleSpec.pathField ArticleSpec.spec ctx (ArticleSpec.find? ((groups a L).map (fieldOf a)) "Path"))) := by
  have hA8 := hA.hA
  have hM := artMax_eq
  have hlt := firstP_lt (nm := "Path") hL hok
  refine fragR_append (xs := [_]) (fragR_of (add_dec o (wd_lowerX (first_ne0 esP "Path")) rfl
    (val := optW (firstP a L "Path")) fun u M h hfr =>
      (first_eval rfl hT hsz scr_add h hfr).trans (congrArg some hfw))) ?_
  refine fragR_if o rfl (lowK_any _ (k := .skip) rfl) (putConst_low _) aout_clock (fun u y w h hy => by
      rw [decl_pathYes] at hy
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hy
      rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact aout_restore h rfl w)
    (fun u y w h hy => by rw [putConst_declared] at hy; cases hy) (b := (firstP a L "Path").isSome)
    (fun u ⟨M, hr, _⟩ => flag_eval (fun x hx => by have := hlt x hx; omega) (ev_var (vals_lookup hr.1.vals rfl)))
    (fun hs => ?_) (fun hs => ?_)
  · cases hg : firstG a L "Path" with
    | none => rw [first_none hg] at hs; nomatch hs
    | some g =>
      obtain ⟨P, e, more, rfl, hf, -, hP⟩ := first_at hL hok hg
      rw [find_fields, hg, Option.map_some] at hfit ⊢
      rw [hP]
      exact path_yes o hA hD hcode hsz hlen hin hb hsep hf ctx hid hfit
  · have hg : firstG a L "Path" = none := by
      cases hg : firstG a L "Path" with
      | none => rfl
      | some g => obtain ⟨_, _, _, _, _, _, hP⟩ := first_at hL hok hg; rw [hP] at hs; nomatch hs
    rw [find_fields, hg, Option.map_none, pathField_none] at hfit ⊢
    rw [first_none hg]
    refine fragR_conseq (add_const o scr_add hD hA8 rfl rfl (ascii_lit _ rfl) (by
      simp only [List.length_append, ascii_length] at hfit ⊢; exact hfit)) (fun _ h => h) fun u h => aout_of h
        fun q hq => by
          simp only [outL, List.mem_cons, List.mem_nil_iff, or_false] at hq
          rcases hq with rfl | rfl | rfl | rfl <;> rfl

/-! ## Message-ID -/

theorem decimal_le20 (x : Nat) (hx : x < 2 ^ 64) : (ArticleSpec.decimal x).length ≤ 20 := by
  show (DN.News.CommandSpec.decimal x).length ≤ 20
  rw [DN.News.DecimalRun.decimal_length]
  rcases Nat.lt_or_ge x (2 ^ 32) with h | h
  · have := DN.News.DecimalRun.numDigits_le_ten x h; omega
  · have hp := DN.News.DecimalRun.pow_numDigits_le x (by omega)
    rcases Nat.lt_or_ge (DN.News.DecimalRun.numDigits x) 21 with h2 | h2
    · omega
    · have : 10 ^ 20 ≤ 10 ^ (DN.News.DecimalRun.numDigits x - 1) := Nat.pow_le_pow_right (by decide) (by omega)
      have h20 : (10 : Nat) ^ 20 = 100000000000000000000 := rfl
      omega

theorem bytesAt_drop {A : Word} {dm : Word → Bool} {be : Bool} {o K : Nat} {P Q : Bytes} {m : Word → Word}
    (h : BytesAt A dm be o K (P ++ Q) m) (hK : (P ++ Q).length ≤ K) : BytesAt A dm be (o + P.length) Q.length Q m :=
  fun i hi _ => by
    have hl : (P ++ Q).length = P.length + Q.length := List.length_append
    have := h (P.length + i) (by omega) (by omega)
    rw [Nat.add_assoc, this, getElem!_pos (P ++ Q) _ (by omega), getElem!_pos Q i hi,
      List.getElem_append_right (by omega)]
    simp

/-- The message identifier `MID` kept, its length; every word outside `artAdded`'s as `m0` holds it. -/
def MsgF (A : Word) (dm : Word → Bool) (be : Bool) (MID : Bytes) (m0 M1 : Word → Word) : Prop :=
  BytesAt A dm be ArticleProg.xMsg ArticleProg.msgCap MID M1 ∧
    M1 (at_ A ArticleProg.xMsgLen) = BitVec.ofNat 64 MID.length ∧ ∀ x, ¬AddScr A x → M1 x = m0 x

/-- The output `P` after the message identifier: only the output's words change from here. -/
def MOut (s1 : PancakeState σ) (A : Word) (m0 : Word → Word) (MID : Bytes) (L : List (String × Value)) (P : Bytes) :
    Assn σ := fun u => ∃ M1, MsgF A s1.memaddrs s1.be MID m0 M1 ∧ AOut (OutScr A) s1 A M1 L P u

theorem mout_clock {s1 : PancakeState σ} {A : Word} {m0 : Word → Word} {MID : Bytes} {L : List (String × Value)}
    {P : Bytes} : Safe.ClockFree (MOut s1 A m0 MID L P) := fun u k ⟨M1, hm, hO⟩ => ⟨M1, hm, aout_clock u k hO⟩

theorem mout_restore {s1 : PancakeState σ} {A : Word} {m0 : Word → Word} {MID : Bytes} {L : List (String × Value)}
    {P : Bytes} {u : PancakeState σ} (h : MOut s1 A m0 MID L P u) {y : String} (hy : Fresh y L = true)
    (w : Option Value) : MOut s1 A m0 MID L P (restore u y w) :=
  let ⟨M1, hm, hO⟩ := h; ⟨M1, hm, aout_restore hO hy w⟩

theorem mout_of {s1 : PancakeState σ} {A : Word} {m0 : Word → Word} {MID : Bytes} {L L' : List (String × Value)}
    {P : Bytes} {u : PancakeState σ} (h : MOut s1 A m0 MID L P u) (hl : ∀ q ∈ L', L.lookup q.1 = some q.2) :
    MOut s1 A m0 MID L' P u :=
  let ⟨M1, hm, hO⟩ := h; ⟨M1, hm, aout_of hO hl⟩

/-- **A step after the message identifier**: one on the output alone. -/
theorem mout_lift (o : Oracle σ) {R : Ret} {xs : List Syntax.PStmt} (hlow : LowKK xs) {s1 : PancakeState σ}
    {A : Word} {m0 : Word → Word} {MID : Bytes} {L1 L2 : List (String × Value)} {P1 P2 : Bytes}
    (h : ∀ M1, MsgF A s1.memaddrs s1.be MID m0 M1 →
      FragR o R xs (AOut (OutScr A) s1 A M1 L1 P1) (AOut (OutScr A) s1 A M1 L2 P2)) :
    FragR o R xs (MOut s1 A m0 MID L1 P1) (MOut s1 A m0 MID L2 P2) := by
  refine fragR_exists hlow fun M1 => ?_
  exact fragR_pure (MsgF A s1.memaddrs s1.be MID m0 M1) (fun u h => h.1) hlow fun hm =>
    fragR_conseq (h M1 hm) (fun u h => h.2) fun u h => ⟨M1, hm, h⟩

theorem out_not_msg {A : Word} (hA8 : A.toNat % 8 = 0) {i : Nat} (hi : i < ArticleProg.outMax) :
    ¬MsgScr A (byteAlign (at_ A (ArticleProg.xOut + i))) := by
  have hx := xOut_eq; have hm := xMsg_eq; have hmx : ArticleProg.outMax = 69632 := rfl
  exact msg_word hA8 (by omega) (by simp only [ArticleProg.msgCap]; omega)

/-- The output kept where only the message identifier's words change. -/
theorem out_msg {A : Word} (hA8 : A.toNat % 8 = 0) {dm : Word → Bool} {be : Bool} {P : Bytes} {M m : Word → Word}
    (hO : BytesAt A dm be ArticleProg.xOut ArticleProg.outMax P M) (hm : ∀ x, ¬MsgScr A x → m x = M x) :
    BytesAt A dm be ArticleProg.xOut ArticleProg.outMax P m :=
  bytesAt_frame hO fun _ hi _ => hm _ (out_not_msg hA8 hi)

theorem msg_add {A : Word} {x : Word} (h : ¬AddScr A x) : ¬MsgScr A x := fun hm => h (.inr (.inl hm))

/-- **The message identifier copied** from bytes the memory holds, and the output kept: the step to `MOut`. -/
theorem msg_to (o : Oracle σ) {R : Ret} {A : Word} {s1 : PancakeState σ} (hA : Area ArticleProg.ofs A s1)
    (hD : ArtDom A s1.memaddrs) (hcode : ArtCode s1.code) (hsz : ArticleProg.size esP < 2 ^ 40) {rt : String}
    (hra : rt ≠ "a") {l : List (String × Value)} (hla : l.lookup "a" = some A) (hrt : Fresh rt l = true)
    {m0 M : Word → Word} (hb : m0 (at_ A aBroken) = 0) (hfr : ∀ x, ¬AddScr A x → M x = m0 x) {P SRC : Bytes}
    (hO : BytesAt A s1.memaddrs s1.be ArticleProg.xOut ArticleProg.outMax P M) {S : Nat}
    (hS : BytesAt A s1.memaddrs s1.be S SRC.length SRC M) (hSz : S + SRC.length ≤ ArticleProg.size esP)
    (hSm : S + SRC.length ≤ ArticleProg.X ∨ ArticleProg.xMsg + ArticleProg.msgCap ≤ S)
    (hSl : SRC.length < ArticleProg.msgCap) {e1 e2 : Syntax.PExpr} {E1 E2 : PancakeExp}
    (he1 : Lower.lowerExp e1 = some E1) (he2 : Lower.lowerExp e2 = some E2)
    (hv1 : ∀ u, RunF s1 l (· = M) u → eval u E1 = some (BitVec.ofNat 64 S))
    (hv2 : ∀ u, RunF s1 l (· = M) u → eval u E2 = some (BitVec.ofNat 64 SRC.length)) :
    FragR o R (guardS (.call rt "artToMsg" [e1, e2])) (RunF s1 l (· = M)) (MOut s1 A m0 SRC l P) :=
  fragR_conseq (msgCall_frag o hA hD hcode hsz hra hla hrt ((hfr _ broken_add).trans hb) hS hSz hSm hSl he1 he2 hv1
    hv2) (fun _ h => h) fun _ ⟨_, m, h, hm, hmsg, hlen⟩ => ⟨m, ⟨hmsg, hlen, fun x hx => (hm x (msg_add hx)).trans
      (hfr x hx)⟩, m, runF_mono h (fun _ hq => List.mem_cons_of_mem _ hq) (fun _ e => e), out_msg hA.hA hO hm,
      fun _ _ => rfl⟩

theorem mid_add {A : Word} (hA8 : A.toNat % 8 = 0) {y : Nat} (h1 : ArticleProg.xGroups ≤ y)
    (h2 : y < ArticleProg.xMsg) : ¬AddScr A (byteAlign (at_ A y)) := by
  have := xMsg_eq; have := xDec_eq; have := xGroups_eq
  rw [DN.News.ScanRun.align_at hA8]
  exact not_addScr (.inr (by omega)) (by omega) (by omega)

theorem newIdS_g : guardL newIdS = putConst "Message-ID: " ++ ([.dec "ms" (v "o")] : Ss) ++ putConst "<" ++
    guardL (numS "o5" (wd xSeq)) ++ putConst "." ++ guardL (copyS "o6" (n xRand) (v "rl")) ++ putConst "@" ++
    guardL (copyS "o7" (n xId) (v "idl")) ++ putConst ">" ++
    guardS (.call "tm" "artToMsg" [eAdd (n xOut) (v "ms"), eSub (v "o") (v "ms")]) ++ putConst "\r\n" := by
  simp only [newIdS, DN.News.ArticleGrammar.guardL_append, guardL_putConst]; rfl

/-- The locals while a new message identifier is written. -/
def msL (A : Word) (RL IDL O MS : Nat) : List (String × Value) :=
  [("o", BitVec.ofNat 64 O), ("ms", BitVec.ofNat 64 MS), ("rl", BitVec.ofNat 64 RL), ("idl", BitVec.ofNat 64 IDL),
   ("a", A)]

theorem add_norm {o : Oracle σ} {R : Ret} {xs : List Syntax.PStmt} {P : Assn σ} {S : Word → Prop}
    {s1 : PancakeState σ} {A : Word} {m0 : Word → Word} {L L' : List (String × Value)} {Q : Bytes}
    (h : FragR o R xs P (AOut S s1 A m0 L Q)) (hl : ∀ q ∈ L', L.lookup q.1 = some q.2) :
    FragR o R xs P (AOut S s1 A m0 L' Q) :=
  fragR_conseq h (fun _ h => h) fun _ h => aout_of h hl

/-- What a new message identifier adds to the header section. -/
def newIdText (ctx : ArticleSpec.Context) : Bytes :=
  DN.News.CommandSpec.ascii "Message-ID: " ++ ArticleSpec.generatedId ctx ++ DN.News.CommandSpec.crlf

/-- **A new message identifier**: written out, and kept as the message identifier. -/
theorem msg_new (o : Oracle σ) {R : Ret} {A : Word} {s1 : PancakeState σ} (hA : Area ArticleProg.ofs A s1)
    (hD : ArtDom A s1.memaddrs) (hcode : ArtCode s1.code) (hsz : ArticleProg.size esP < 2 ^ 40) {m0 : Word → Word}
    (hb : m0 (at_ A aBroken) = 0) {ctx : ArticleSpec.Context} (hctx : CtxAt A s1.memaddrs s1.be ctx m0)
    {SEP : Nat} {W : Word} {OUT1 : Bytes} (hfit : (OUT1 ++ newIdText ctx).length ≤ ArticleProg.outMax) :
    FragR o R (guardL newIdS)
      (AOut (AddScr A) s1 A m0 (("hid", W) :: loopL A SEP ctx.random.length ctx.identity.length SEP OUT1.length) OUT1)
      (MOut s1 A m0 (ArticleSpec.generatedId ctx)
        (outL A ctx.random.length ctx.identity.length (OUT1 ++ newIdText ctx).length) (OUT1 ++ newIdText ctx)) := by
  have hA8 := hA.hA
  obtain ⟨hi1, hi2, hi3, hr1, hr2, hr3, hs1, hs2, -, -, -, -, -, -⟩ := hctx
  have hdl := decimal_le20 ctx.seq hs1
  have hgl : (ArticleSpec.generatedId ctx).length = 4 + (ArticleSpec.decimal ctx.seq).length + ctx.random.length +
      ctx.identity.length := by
    have h1 : (DN.News.CommandSpec.ascii "<").length = 1 := rfl
    have h2 : (DN.News.CommandSpec.ascii ".").length = 1 := rfl
    have h3 : (DN.News.CommandSpec.ascii "@").length = 1 := rfl
    have h4 : (DN.News.CommandSpec.ascii ">").length = 1 := rfl
    simp only [ArticleSpec.generatedId, List.length_append, h1, h2, h3, h4]
    omega
  have hfit' := hfit
  have hm12 : "Message-ID: ".length = 12 := rfl
  have hcr : DN.News.CommandSpec.crlf.length = 2 := rfl
  simp only [newIdText, List.length_append, ascii_length, hgl, hm12, hcr] at hfit'
  have h1 : "<".length = 1 := rfl
  have h2 : ".".length = 1 := rfl
  have h3 : "@".length = 1 := rfl
  have h4 : ">".length = 1 := rfl
  have h5 : "\r\n".length = 2 := rfl
  have hX := xOut_eq; have hXm := xMsg_eq; have hXd := xDec_eq; have hXi := xId_eq; have hXr := xRand_eq
  have hXg := xGroups_eq
  have hsz' := xFirst_le_size esP
  have hxf : ArticleProg.xFirst = ArticleProg.xOut + ArticleProg.outMax := rfl
  rw [newIdS_g]
  simp only [List.append_assoc]
  let RL := ctx.random.length
  let IDL := ctx.identity.length
  let P1 := OUT1 ++ DN.News.CommandSpec.ascii "Message-ID: "
  have hn5 : ∀ (L : List (String × Value)) (O' MS : Nat), L.lookup "ms" = some (BitVec.ofNat 64 MS) →
      L.lookup "rl" = some (BitVec.ofNat 64 RL) → L.lookup "idl" = some (BitVec.ofNat 64 IDL) →
      L.lookup "a" = some A → ∀ q ∈ msL A RL IDL O' MS,
        (("o", BitVec.ofNat 64 O') :: without "o" L).lookup q.1 = some q.2 := fun L O' MS h1 h2 h3 h4 =>
    o_next (fun q hq => by
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl <;> exact ⟨by simp, by assumption⟩) O'
  refine fragR_append (add_const o scr_add hD hA8 rfl rfl (ascii_lit _ rfl) (by simp only [hm12]; omega)) ?_
  refine fragR_append (xs := [_]) (fragR_conseq (fragR_of (add_dec o rfl rfl (val := BitVec.ofNat 64 P1.length)
    fun u M h _ => ev_var (vals_lookup h.1.vals rfl))) (fun _ h => h)
    (P' := AOut (AddScr A) s1 A m0 (msL A RL IDL P1.length P1.length) P1) fun u h => aout_of h fun q hq => by
      simp only [msL, List.mem_cons, List.mem_nil_iff, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl | rfl <;> rfl) ?_
  refine fragR_append (add_norm (add_const o scr_add hD hA8 rfl rfl (ascii_lit _ rfl) (by
    simp only [P1, List.length_append, ascii_length, hm12, h1]; omega)) (hn5 _ _ _ rfl rfl rfl rfl)) ?_
  refine fragR_append (add_norm (add_num o scr_add hA hD hcode hb rfl (name := "o5") (by decide) (by decide) rfl rfl
    (X := ctx.seq) hs1 (by simp only [P1, List.length_append, ascii_length, hm12, h1]; omega)
    (lowK_any _ (k := .skip) rfl) (wd_lower 3) fun u M h hfr => by
      rw [loadA_eval h.1.memaddrs (artDom_w hD (i := 3) (by decide)) (atA_eval (vals_lookup h.1.vals rfl)), h.2]
      exact congrArg some ((hfr _ (not_addScr_w (i := 3) (by decide) (by decide))).trans hs2))
    (hn5 _ _ _ rfl rfl rfl rfl)) ?_
  refine fragR_append (add_norm (add_const o scr_add hD hA8 rfl rfl (ascii_lit _ rfl) (by
    simp only [P1, List.length_append, ascii_length, hm12, h1, h2]; omega)) (hn5 _ _ _ rfl rfl rfl rfl)) ?_
  refine fragR_append (add_norm (add_copy o scr_add hA hD hcode hsz hb rfl (name := "o6") (by decide) (by decide) rfl
    (SRC := ctx.random) rfl (S0 := ArticleProg.xRand) hr3 (fun i hi => mid_add hA8 (by omega) (by omega))
    (by omega) (by simp only [P1, List.length_append, ascii_length, hm12, h1, h2]; omega)
    (lowK_any _ (k := .skip) rfl) rfl rfl (fun u M h _ => rfl) fun u M h _ => ev_var (vals_lookup h.1.vals rfl))
    (hn5 _ _ _ rfl rfl rfl rfl)) ?_
  refine fragR_append (add_norm (add_const o scr_add hD hA8 rfl rfl (ascii_lit _ rfl) (by
    simp only [P1, List.length_append, ascii_length, hm12, h1, h2, h3]; omega)) (hn5 _ _ _ rfl rfl rfl rfl)) ?_
  refine fragR_append (add_norm (add_copy o scr_add hA hD hcode hsz hb rfl (name := "o7") (by decide) (by decide) rfl
    (SRC := ctx.identity) rfl (S0 := ArticleProg.xId) hi3 (fun i hi => mid_add hA8 (by omega) (by omega))
    (by omega) (by simp only [P1, List.length_append, ascii_length, hm12, h1, h2, h3]; omega)
    (lowK_any _ (k := .skip) rfl) rfl rfl (fun u M h _ => rfl) fun u M h _ => ev_var (vals_lookup h.1.vals rfl))
    (hn5 _ _ _ rfl rfl rfl rfl)) ?_
  refine fragR_append (add_norm (add_const o scr_add hD hA8 rfl rfl (ascii_lit _ rfl) (by
    simp only [P1, List.length_append, ascii_length, hm12, h1, h2, h3, h4]; omega)) (hn5 _ _ _ rfl rfl rfl rfl)) ?_
  -- the identifier kept
  have hP9 : OUT1 ++ DN.News.CommandSpec.ascii "Message-ID: " ++ DN.News.CommandSpec.ascii "<" ++
      ArticleSpec.decimal ctx.seq ++ DN.News.CommandSpec.ascii "." ++ ctx.random ++ DN.News.CommandSpec.ascii "@" ++
      ctx.identity ++ DN.News.CommandSpec.ascii ">" =
      (OUT1 ++ DN.News.CommandSpec.ascii "Message-ID: ") ++ ArticleSpec.generatedId ctx := by
    simp only [ArticleSpec.generatedId, List.append_assoc]
  have hlP : ((OUT1 ++ DN.News.CommandSpec.ascii "Message-ID: ") ++ ArticleSpec.generatedId ctx).length ≤
      ArticleProg.outMax := by
    simp only [List.length_append, ascii_length, hgl, hm12]; omega
  rw [hP9]
  have hmc : ArticleProg.msgCap = 256 := rfl
  refine aout_lift o (lowKK_append (lowK_any _ (k := .skip) rfl) (putConst_low _)) fun M hO hfr => ?_
  have hsub : (ArticleSpec.generatedId ctx).length =
      ((OUT1 ++ DN.News.CommandSpec.ascii "Message-ID: ") ++ ArticleSpec.generatedId ctx).length - P1.length := by
    simp only [P1, List.length_append]; omega
  have hSm : ArticleProg.xMsg + ArticleProg.msgCap ≤
      ArticleProg.xOut + (OUT1 ++ DN.News.CommandSpec.ascii "Message-ID: ").length := by
    rw [hmc, hXm, hX]; exact Nat.le_add_right_of_le (by decide)
  have hgl2 : (ArticleSpec.generatedId ctx).length < ArticleProg.msgCap := by rw [hmc, hgl]; omega
  refine fragR_append (msg_to o hA hD hcode hsz (rt := "tm") (by decide) rfl rfl hb hfr hO
    (bytesAt_drop hO hlP) (by simp only [List.length_append, ascii_length, hgl, hm12] at hlP ⊢; omega)
    (.inr hSm) hgl2 rfl rfl
    (fun u h => WpBytes.eval_add rfl (ev_var (vals_lookup h.1.vals rfl))) fun u h => ?_) ?_
  · rw [hsub]
    exact DN.News.ArticleCal.ev_subE (ev_var (vals_lookup h.1.vals rfl)) (ev_var (vals_lookup h.1.vals rfl))
      (by simp only [P1, List.length_append]; omega) (by simp only [List.length_append, ascii_length]; omega)
  refine fragR_conseq (mout_lift o (putConst_low _) fun M1 hm => add_const o scr_out hD hA8 rfl rfl
    (ascii_lit _ rfl) (by simp only [List.length_append, ascii_length, hgl, hm12, h5]; omega)) (fun _ h => h)
    fun u h => ?_
  have e : (OUT1 ++ DN.News.CommandSpec.ascii "Message-ID: ") ++ ArticleSpec.generatedId ctx ++
      DN.News.CommandSpec.ascii "\r\n" = OUT1 ++ newIdText ctx := by
    simp only [newIdText, List.append_assoc, ascii_crlf]
  rw [e] at h
  exact mout_of h fun q hq => by
    simp only [outL, List.mem_cons, List.mem_nil_iff, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl <;> rfl

/-- **A field's value is the input's bytes** from past its colon to the next field's CRLF. -/
theorem value_seg {a : Bytes} {sep P e : Nat} {more : List (Nat × Nat)} (h : Lines a P ((P, e) :: more) sep)
    (hK : P + DN.News.ArticleLines.nameLen a P e < e) :
    (fieldOf a ((P, e) :: more.takeWhile (cont a))).value =
      seg a (P + DN.News.ArticleLines.nameLen a P e + 1) (DN.News.ArticleLines.nextOf a more sep - 2) := by
  have hea := (DN.News.ArticleLines.lines_mem h (P, e) List.mem_cons_self).2.2.2.2
  have hnl : (DN.News.ArticleLines.nameAt a (P, e)).length = DN.News.ArticleLines.nameLen a P e := by
    show (seg a P (P + DN.News.ArticleLines.nameLen a P e)).length = _
    rw [seg_length a (by omega) (by omega)]; omega
  rw [← rest_seg more P e _ h (by omega)]
  simp only [ArticleSpec.Field.value, ArticleSpec.Field.body, fieldOf, segs, List.map_cons, List.headD_cons, hnl,
    seg_drop, List.map_map]
  rfl

theorem oldIdS_g : guardL oldIdS = guardS (.call "hf" "artField" [v "hid"]) ++ ([.dec "hn" (wd xNl)] : Ss) ++
    guardS (.call "ml" "artMsgIds" [eAdd (eAdd (v "hid") (v "hn")) (n 1), eSub (v "hf") (n 2)]) ++
    ([setW xMsgLen (n 0), .ite (eLe (n 0) (wd xMsgS))
      (guardS (.call "tn" "artToMsg" [eAdd (n aInput) (wd xMsgS), wd xMsgL])) []] : Ss) := rfl

/-- An output word is none of the article's scalar words. -/
theorem out_ne_w {A : Word} {y : Word} (hy : OutScr A y) {k : Nat} (hk : k < 32) : y ≠ at_ A (ArticleProg.w k) := by
  obtain ⟨z, h1, h2, rfl⟩ := hy
  exact DN.News.ScanRun.at_ne (by rw [xFirst_eq] at h2; omega) (w_lt64 hk) (by
    rw [xDec_eq] at h1; simp only [ArticleProg.w, X_val]; omega)

theorem out_at {A : Word} (hA8 : A.toNat % 8 = 0) {i : Nat} (hi : i < ArticleProg.outMax) :
    OutScr A (byteAlign (at_ A (ArticleProg.xOut + i))) := by
  rw [DN.News.ScanRun.align_at hA8]
  have hx := xOut_eq; have hd := xDec_eq; have hf := xFirst_eq; have hm : ArticleProg.outMax = 69632 := rfl
  exact ⟨_, by omega, by omega, rfl⟩

/-- The memory after the identifiers looked for: the field's end, the first identifier, its length cleared. -/
def oldMem (A : Word) (K e : Nat) (w1 w2 : Word) (M : Word → Word) : Word → Word :=
  upd (upd (upd (fieldMem A K e M) (at_ A xMsgS) w1) (at_ A xMsgL) w2) (at_ A ArticleProg.xMsgLen) 0

theorem oldMem_fr {A : Word} {M m0 : Word → Word} (hfr : ∀ x, ¬AddScr A x → M x = m0 x) (K e : Nat) (w1 w2 : Word) :
    ∀ x, ¬AddScr A x → oldMem A K e w1 w2 M x = m0 x := fun x hx => by
  simp only [oldMem, fieldMem]
  rw [upd_ne _ fun h => hx (.inr (.inl (.inl h))), upd_ne _ fun h => hx (.inr (.inr (.inr (.inr (.inr (.inl h)))))),
    upd_ne _ fun h => hx (.inr (.inr (.inr (.inr (.inl h))))), upd_ne _ fun h => hx (.inr (.inr (.inr (.inl h)))),
    upd_ne _ fun h => hx (.inr (.inr (.inl h)))]
  exact hfr x hx

theorem oldMem_out {A : Word} (hA8 : A.toNat % 8 = 0) {dm : Word → Bool} {be : Bool} {P : Bytes} {M : Word → Word}
    (hO : BytesAt A dm be ArticleProg.xOut ArticleProg.outMax P M) (K e : Nat) (w1 w2 : Word) :
    BytesAt A dm be ArticleProg.xOut ArticleProg.outMax P (oldMem A K e w1 w2 M) :=
  bytesAt_frame hO fun i hi _ => by
    have ho := out_at hA8 hi
    simp only [oldMem, fieldMem, ArticleProg.xMsgLen, ArticleProg.xNl, ArticleProg.xE1, xMsgS, xMsgL]
    rw [upd_ne _ (out_ne_w ho (k := 13) (by decide)), upd_ne _ (out_ne_w ho (k := 24) (by decide)),
      upd_ne _ (out_ne_w ho (k := 23) (by decide)), upd_ne _ (out_ne_w ho (k := 18) (by decide)),
      upd_ne _ (out_ne_w ho (k := 17) (by decide))]

theorem oldMem_s (A : Word) (K e : Nat) (w1 w2 : Word) (M : Word → Word) :
    oldMem A K e w1 w2 M (at_ A xMsgS) = w1 := by
  simp only [oldMem, ArticleProg.xMsgLen, xMsgS, xMsgL]
  rw [upd_ne _ (w_ne (by decide) (by decide) (by decide) A), upd_ne _ (w_ne (by decide) (by decide) (by decide) A),
    upd_eq]

theorem oldMem_l (A : Word) (K e : Nat) (w1 w2 : Word) (M : Word → Word) :
    oldMem A K e w1 w2 M (at_ A xMsgL) = w2 := by
  simp only [oldMem, ArticleProg.xMsgLen, xMsgS, xMsgL]
  rw [upd_ne _ (w_ne (by decide) (by decide) (by decide) A), upd_eq]

theorem oldMem_len (A : Word) (K e : Nat) (w1 w2 : Word) (M : Word → Word) :
    oldMem A K e w1 w2 M (at_ A ArticleProg.xMsgLen) = 0 := upd_eq _ _ _

/-- **The message identifier the article had**: its field's first identifier kept, or none. -/
theorem msg_old (o : Oracle σ) {R : Ret} {A : Word} {s1 : PancakeState σ} (hA : Area ArticleProg.ofs A s1)
    (hD : ArtDom A s1.memaddrs) (hcode : ArtCode s1.code) (hsz : ArticleProg.size esP < 2 ^ 40) {m0 : Word → Word}
    {a : Bytes} (hlen : a.length ≤ artMax) (hin : InputAt m0 s1.memaddrs s1.be A a) (hb : m0 (at_ A aBroken) = 0)
    {SEP : Nat} (hsep : m0 (at_ A xSep) = BitVec.ofNat 64 SEP) {P e : Nat} {more : List (Nat × Nat)}
    (hf : DN.News.ArticleLines.FieldAt a SEP P e more) {RL IDL : Nat} {OUT1 : Bytes}
    (hmid : ((ArticleSpec.msgIds (seg a (P + DN.News.ArticleLines.nameLen a P e + 1)
      (DN.News.ArticleLines.nextOf a more SEP - 2))).headD []).length < ArticleProg.msgCap) :
    FragR o R (guardL oldIdS)
      (AOut (AddScr A) s1 A m0 (("hid", BitVec.ofNat 64 P) :: loopL A SEP RL IDL SEP OUT1.length) OUT1)
      (MOut s1 A m0 ((ArticleSpec.msgIds (seg a (P + DN.News.ArticleLines.nameLen a P e + 1)
        (DN.News.ArticleLines.nextOf a more SEP - 2))).headD []) (outL A RL IDL OUT1.length) OUT1) := by
  have hA8 := hA.hA
  have hM := artMax_eq
  let K := DN.News.ArticleLines.nameLen a P e
  let NX := DN.News.ArticleLines.nextOf a more SEP
  have hL := hf.lines
  have hcol := DN.News.ArticleLines.fieldAt_colon hf
  have hK1 : P + K < e := hcol.2.1
  have hmem := DN.News.ArticleLines.lines_mem hL (P, e) List.mem_cons_self
  have hmore := (DN.News.ArticleLines.lines_tail hL).2
  have hNX : e + 2 ≤ NX := (DN.News.ArticleLines.nextOf_ge hmore).1
  have hNXs : NX ≤ SEP := (DN.News.ArticleLines.lines_sep (lines_next more (e + 2) hmore)).1
  have hSEP : SEP < a.length := (DN.News.ArticleLines.lines_sep hL).2.2
  let Lh := ("hid", BitVec.ofNat 64 P) :: loopL A SEP RL IDL SEP OUT1.length
  rw [oldIdS_g]
  simp only [List.append_assoc]
  refine aout_lift o (lowK_any _ (k := .skip) rfl) fun M hO hfr => ?_
  have hbM : M (at_ A aBroken) = 0 := (hfr _ broken_add).trans hb
  have hinM := input_frame hA8 hlen hfr hin
  have hk := fieldMem_keep hA8 hlen hinM hbM K e
  refine fragR_append (fieldCall_frag o hA hD hcode hlen (rt := "hf") (by decide) (l := Lh) rfl rfl (e1 := v "hid")
    rfl hf (fun u h => ev_var (vals_lookup h.1.vals rfl)) hinM hbM
    ((hfr _ (not_addScr_w (i := 16) (by decide) (by decide))).trans hsep)) ?_
  refine fragR_append (xs := [_]) (fragR_of (runF_dec o (wd_lower 17) rfl (v := BitVec.ofNat 64 K) fun u h => by
    rw [loadA_eval h.1.memaddrs (artDom_w hD (i := 17) (by decide)) (atA_eval (vals_lookup h.1.vals rfl)), h.2]
    exact congrArg some (fieldMem_nl A K e M))) ?_
  refine fragR_append (idsCall_frag o hA hD hcode (rt := "ml") (by decide) rfl rfl hk.2 hlen hk.1 (S := P + K + 1)
    (E := NX - 2) (by omega) (by omega) rfl rfl
    (fun u h => WpBytes.eval_add (WpBytes.eval_add (ev_var (vals_lookup h.1.vals rfl))
      (ev_var (vals_lookup h.1.vals rfl))) rfl)
    (fun u h => DN.News.ArticleCal.ev_subE (ev_var (vals_lookup h.1.vals rfl)) rfl (by omega) (by omega))) ?_
  refine fragR_exists (lowK_any _ (k := .skip) rfl) fun w => ?_
  refine fragR_exists (lowK_any _ (k := .skip) rfl) fun m => ?_
  refine fragR_pure (IdsRet ArticleSpec.spec.idMax A a (P + K + 1) (NX - 2) (fieldMem A K e M) w m) (fun u h => h.2)
    (lowK_any _ (k := .skip) rfl) fun hids => ?_
  obtain ⟨-, w1, w2, hm, hfirst⟩ := hids
  subst hm
  refine fragR_conseq ?_ (fun u h => h.1) fun _ h => h
  refine fragR_append (xs := [_]) (fragR_of (runF_storeA o
    (D := .op .add (.var "a") (.const (BitVec.ofNat 64 (ArticleProg.w 13)))) (E := .const 0)
    (by simp only [Syntax.atOff]; rfl) rfl (y := ArticleProg.w 13)
    (artDom_w hD (by decide)) (fun u h => atA_eval (vals_lookup h.1.vals rfl)) (val := fun _ => 0) (fun u h => rfl)
    (G := (· = oldMem A K e w1 w2 M)) fun m h => by rw [h]; rfl)) ?_
  have hfrO := oldMem_fr hfr K e w1 w2
  have hOO := oldMem_out hA8 hO K e w1 w2
  have hsE : ∀ u, RunF s1 (("ml", w) :: ("hn", BitVec.ofNat 64 K) :: ("hf", BitVec.ofNat 64 NX) :: Lh)
      (· = oldMem A K e w1 w2 M) u →
      eval u (.loadWord (.op .add (.var "a") (.const (BitVec.ofNat 64 xMsgS)))) = some w1 := fun u h => by
    rw [loadA_eval (y := xMsgS) h.1.memaddrs (artDom_w hD (i := 23) (by decide)) (atA_eval (vals_lookup h.1.vals rfl)),
      h.2]
    exact congrArg some (oldMem_s A K e w1 w2 M)
  have hlk : ∀ q ∈ outL A RL IDL OUT1.length,
      (("ml", w) :: ("hn", BitVec.ofNat 64 K) :: ("hf", BitVec.ofNat 64 NX) :: Lh).lookup q.1 = some q.2 :=
    fun q hq => by
      simp only [outL, List.mem_cons, List.mem_nil_iff, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl <;> rfl
  cases hids : ArticleSpec.msgIds (seg a (P + K + 1) (NX - 2)) with
  | nil =>
    rw [hids] at hfirst
    obtain ⟨h1, -⟩ := hfirst
    refine fragR_if o rfl (lowK_any _ (k := .skip) rfl) (lowK_any _ (k := .skip) rfl) mout_clock
      (fun u y v h hy => by
        change y ∈ ["tn"] at hy; simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
        subst hy; exact mout_restore h rfl v)
      (fun u y v h hy => by change y ∈ [] at hy; cases hy) (b := false)
      (fun u h => flag_eval (p := none) (fun x hx => nomatch hx) (by rw [hsE u h, h1]; rfl))
      (fun h => nomatch h) fun _ => fragR_of (frag_nil o fun u h => ?_)
    have hB0 : BytesAt A s1.memaddrs s1.be ArticleProg.xMsg ArticleProg.msgCap [] (oldMem A K e w1 w2 M) :=
      fun _ _ hi => absurd hi (Nat.not_lt_zero _)
    exact ⟨oldMem A K e w1 w2 M, ⟨hB0, oldMem_len A K e w1 w2 M, hfrO⟩,
      ⟨oldMem A K e w1 w2 M, runF_of h hlk, hOO, fun _ _ => rfl⟩⟩
  | cons id rest =>
    rw [hids] at hfirst hmid
    obtain ⟨cs, hc1, hc2, hc3, hc4, hc5⟩ := hfirst
    have hS := input_seg (input_frame hA8 hlen hfrO hin) (P := cs) (E := cs + id.length) (by omega) (by omega)
    rw [hc3] at hS
    refine fragR_if o rfl (lowK_any _ (k := .skip) rfl) (lowK_any _ (k := .skip) rfl) mout_clock
      (fun u y v h hy => by
        change y ∈ ["tn"] at hy; simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
        subst hy; exact mout_restore h rfl v)
      (fun u y v h hy => by change y ∈ [] at hy; cases hy) (b := true)
      (fun u h => flag_eval (p := some cs) (fun x hx => by cases hx; omega) (by rw [hsE u h, hc4]; rfl))
      (fun _ => ?_) (fun h => nomatch h)
    have hb' : oldMem A K e w1 w2 M (at_ A aBroken) = 0 := (hfrO _ broken_add).trans hb
    refine fragR_conseq (msg_to o hA hD hcode hsz (rt := "tn") (by decide) rfl rfl hb hfrO hOO hS
      (by have := input_below; have := sets_le_X; have := X_val
          simp only [ArticleProg.size, ArticleProg.xNameBytes, ArticleProg.xNameT, ArticleProg.xRuleT,
            ArticleProg.xFlags, xFirst_eq]
          omega)
      (.inl (by have := input_below; have := sets_le_X; omega)) hmid rfl (wd_lower 24)
      (fun u h => WpBytes.eval_add rfl (by rw [hsE u h, hc4]))
      (fun u h => by
        rw [loadA_eval h.1.memaddrs (artDom_w hD (i := 24) (by decide)) (atA_eval (vals_lookup h.1.vals rfl)), h.2]
        exact congrArg some ((oldMem_l A K e w1 w2 M).trans hc5))) (fun _ h => h) fun u h => mout_of h hlk

/-- The message identifier `artAdded` keeps: a new one, or the first the article's field holds. -/
def midOf (ctx : ArticleSpec.Context) (a : Bytes) (L : List (Nat × Nat)) : Bytes :=
  match firstG a L "Message-ID" with
  | none => ArticleSpec.generatedId ctx
  | some g => (ArticleSpec.msgIds (fieldOf a g).value).headD []

/-- What the message identifier adds to the header section. -/
def midText (ctx : ArticleSpec.Context) (a : Bytes) (L : List (Nat × Nat)) : Bytes :=
  match firstG a L "Message-ID" with
  | none => newIdText ctx
  | some _ => []

theorem decl_newIdS : declared (guardL newIdS) = ["ms", "o5", "o6", "o7", "tm"] := by
  rw [newIdS_g]; simp only [declared_append, putConst_declared]; rfl

theorem decl_oldIdS : declared (guardL oldIdS) = ["hf", "hn", "ml"] := by
  rw [oldIdS_g]; simp only [declared_append]; rfl

theorem newIdS_low : LowKK (guardL newIdS) := by
  rw [newIdS_g]
  exact lowKK_append (lowKK_append (lowKK_append (lowKK_append (lowKK_append (lowKK_append (lowKK_append
    (lowKK_append (lowKK_append (lowKK_append (putConst_low _) (lowK_any _ (k := .skip) rfl)) (putConst_low _))
    (lowK_any _ (k := .skip) rfl)) (putConst_low _)) (lowK_any _ (k := .skip) rfl)) (putConst_low _))
    (lowK_any _ (k := .skip) rfl)) (putConst_low _)) (lowK_any _ (k := .skip) rfl)) (putConst_low _)

/-- **Message-ID**: a new one written out and kept, or the article's first identifier kept. -/
theorem msg_sel (o : Oracle σ) {R : Ret} {A : Word} {s1 : PancakeState σ} (hA : Area ArticleProg.ofs A s1)
    (hD : ArtDom A s1.memaddrs) (hcode : ArtCode s1.code) (hsz : ArticleProg.size esP < 2 ^ 40) {m0 : Word → Word}
    {a : Bytes} (hlen : a.length ≤ artMax) (hin : InputAt m0 s1.memaddrs s1.be A a) (hb : m0 (at_ A aBroken) = 0)
    {SEP : Nat} (hsep : m0 (at_ A xSep) = BitVec.ofNat 64 SEP) (hT : TabDom A s1.memaddrs esP)
    {L : List (Nat × Nat)} (hL : Lines a 0 L SEP) (hok : L.any (DN.News.ArticleLines.malLine a) = false)
    (hfw : FirstW A m0 a L "Message-ID") {ctx : ArticleSpec.Context} (hctx : CtxAt A s1.memaddrs s1.be ctx m0)
    {OUT1 : Bytes} (hfit : (OUT1 ++ midText ctx a L).length ≤ ArticleProg.outMax)
    (hmidl : (midOf ctx a L).length < ArticleProg.msgCap) :
    FragR o R [.dec "hid" (firstOf esP "Message-ID"), .ite (eLt (v "hid") (n 0)) (guardL newIdS) (guardL oldIdS)]
      (AOut (AddScr A) s1 A m0 (loopL A SEP ctx.random.length ctx.identity.length SEP OUT1.length) OUT1)
      (MOut s1 A m0 (midOf ctx a L) (outL A ctx.random.length ctx.identity.length (OUT1 ++ midText ctx a L).length)
        (OUT1 ++ midText ctx a L)) := by
  have hM := artMax_eq
  have hlt := firstP_lt (nm := "Message-ID") hL hok
  refine fragR_append (xs := [_]) (fragR_of (add_dec o (wd_lowerX (first_ne0 esP "Message-ID")) rfl
    (val := optW (firstP a L "Message-ID")) fun u M h hfr =>
      (first_eval rfl hT hsz scr_add h hfr).trans (congrArg some hfw))) ?_
  refine fragR_if o rfl newIdS_low (lowK_any _ (k := .skip) rfl) mout_clock (fun u y w h hy => by
      rw [decl_newIdS] at hy
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hy
      rcases hy with rfl | rfl | rfl | rfl | rfl <;> exact mout_restore h rfl w)
    (fun u y w h hy => by
      rw [decl_oldIdS] at hy
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hy
      rcases hy with rfl | rfl | rfl <;> exact mout_restore h rfl w) (b := (firstP a L "Message-ID").isNone)
    (fun u ⟨M, hr, _⟩ => lt0_eval (fun x hx => by have := hlt x hx; omega) (ev_var (vals_lookup hr.1.vals rfl)))
    (fun hs => ?_) (fun hs => ?_)
  · cases hg : firstG a L "Message-ID" with
    | some g => obtain ⟨_, _, _, _, _, _, hP⟩ := first_at hL hok hg; rw [hP] at hs; nomatch hs
    | none =>
      have hmo : midOf ctx a L = ArticleSpec.generatedId ctx := by unfold midOf; rw [hg]
      have hmt : midText ctx a L = newIdText ctx := by unfold midText; rw [hg]
      rw [hmo, hmt]; rw [hmt] at hfit
      exact msg_new o hA hD hcode hsz hb hctx hfit
  · cases hg : firstG a L "Message-ID" with
    | none => rw [first_none hg] at hs; nomatch hs
    | some g =>
      obtain ⟨P, e, more, rfl, hf, -, hP⟩ := first_at hL hok hg
      have hcol := DN.News.ArticleLines.fieldAt_colon hf
      have hmo : midOf ctx a L = (ArticleSpec.msgIds (seg a (P + DN.News.ArticleLines.nameLen a P e + 1)
          (DN.News.ArticleLines.nextOf a more SEP - 2))).headD [] := by
        unfold midOf; rw [hg]; simp only; rw [value_seg hf.lines hcol.2.1]
      have hmt : midText ctx a L = [] := by unfold midText; rw [hg]
      rw [hmo, hmt, List.append_nil]; rw [hmo] at hmidl
      rw [hP]
      exact msg_old o hA hD hcode hsz hlen hin hb hsep hf hmidl

/-! ## The fields added after the article's -/

/-- A first field's place as the program reads it. -/
def firstE (es : List String) (s : String) : PancakeExp :=
  .loadWord (.op .add (.var "a") (.const (BitVec.ofNat 64 (ArticleProg.xFirst + 8 * ArticleProg.entryOf es s))))

theorem lt0_lower (es : List String) (s : String) : Lower.lowerExp (eLt (firstOf es s) (n 0)) =
    some (.cmp .less (firstE es s) (.const (BitVec.ofNat 64 0))) := by
  show Lower.lowerExp (.binop .lt (wd _) (n 0)) = _
  simp only [Lower.lowerExp, wd_lowerX (first_ne0 es s)]; rfl

theorem flag_lower (es : List String) (s : String) : Lower.lowerExp (eLe (n 0) (firstOf es s)) =
    some (.cmp .notLess (firstE es s) (.const (BitVec.ofNat 64 0))) := by
  show Lower.lowerExp (.binop .le (n 0) (wd _)) = _
  simp only [Lower.lowerExp, wd_lowerX (first_ne0 es s)]; rfl

/-- What the date adds to the header section. -/
def dateText (ctx : ArticleSpec.Context) (a : Bytes) (L : List (Nat × Nat)) : Bytes :=
  if (firstP a L "Date").isNone then
    DN.News.CommandSpec.ascii "Date: " ++ ArticleSpec.formatDate ctx.wall ++ DN.News.CommandSpec.crlf
  else []

theorem dateYes_low : LowKK (putConst "Date: " ++ guardL (fmtS "o8") ++ putConst "\r\n") :=
  lowKK_append (lowKK_append (putConst_low _) (lowK_any _ (k := .skip) rfl)) (putConst_low _)

theorem decl_dateYes : declared (putConst "Date: " ++ guardL (fmtS "o8") ++ putConst "\r\n") = ["o8"] := by
  simp only [declared_append, putConst_declared]; rfl

/-- **Date** added when the article has none. -/
theorem date_step (o : Oracle σ) {R : Ret} {A : Word} {s1 : PancakeState σ} (hA : Area ArticleProg.ofs A s1)
    (hD : ArtDom A s1.memaddrs) (hcode : ArtCode s1.code) (hT : TabDom A s1.memaddrs esP)
    (hsz : ArticleProg.size esP < 2 ^ 40) {m0 : Word → Word} (hP : Pows m0 A) (hb : m0 (at_ A aBroken) = 0)
    {ctx : ArticleSpec.Context}
    (hctx : CtxAt A s1.memaddrs s1.be ctx m0) {a : Bytes} {SEP : Nat} {L : List (Nat × Nat)} (hL : Lines a 0 L SEP)
    (hok : L.any (DN.News.ArticleLines.malLine a) = false) (hlen : a.length ≤ artMax) (hfw : FirstW A m0 a L "Date")
    {MID : Bytes} {RL IDL : Nat} {OUT2 : Bytes} (hfit : (OUT2 ++ dateText ctx a L).length ≤ ArticleProg.outMax) :
    FragR o R [.ite (eLt (firstOf esP "Date") (n 0)) (putConst "Date: " ++ guardL (fmtS "o8") ++ putConst "\r\n") []]
      (MOut s1 A m0 MID (outL A RL IDL OUT2.length) OUT2)
      (MOut s1 A m0 MID (outL A RL IDL (OUT2 ++ dateText ctx a L).length) (OUT2 ++ dateText ctx a L)) := by
  have hA8 := hA.hA
  have hM := artMax_eq
  have hlt := firstP_lt (nm := "Date") hL hok
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hw1, hw2⟩ := hctx
  refine mout_lift o (lowKK_ite (lt0_lower esP "Date") dateYes_low (lowK_any _ (k := .skip) rfl)) fun M1 hm => ?_
  have hfr1 := hm.2.2
  have hb1 : M1 (at_ A aBroken) = 0 := (hfr1 _ broken_add).trans hb
  have hw1' : M1 (at_ A ArticleProg.xWall) = BitVec.ofNat 64 ctx.wall :=
    (hfr1 _ (not_addScr_w (i := 2) (by decide) (by decide))).trans hw2
  have hP1 := pows_frame scr_add hfr1 hP
  have hft : ¬AddScr A (at_ A (ArticleProg.xFirst + 8 * ArticleProg.entryOf esP "Date")) :=
    high_add (Nat.le_add_right _ _) (by have := xFirst_eq; have := entry_le55 "Date"; omega)
  refine fragR_if o (lt0_lower esP "Date") dateYes_low (lowK_any _ (k := .skip) rfl) aout_clock
    (fun u y w h hy => by
      rw [decl_dateYes] at hy; simp only [List.mem_singleton] at hy; subst hy; exact aout_restore h rfl w)
    (fun u y w h hy => by change y ∈ [] at hy; cases hy) (b := (firstP a L "Date").isNone)
    (fun u ⟨M, hr, _, hfr⟩ => lt0_eval (fun x hx => by have := hlt x hx; omega)
      ((first_eval rfl hT hsz scr_out hr hfr).trans
        (congrArg some ((hfr1 _ hft).trans hfw)))) (fun hs => ?_) (fun hs => ?_)
  · have hdt : dateText ctx a L = DN.News.CommandSpec.ascii "Date: " ++ ArticleSpec.formatDate ctx.wall ++
        DN.News.CommandSpec.crlf := if_pos hs
    rw [hdt] at hfit ⊢
    have h6 : "Date: ".length = 6 := rfl
    have h2 : "\r\n".length = 2 := rfl
    have hcr : DN.News.CommandSpec.crlf.length = 2 := rfl
    simp only [List.length_append, ascii_length, h6, hcr] at hfit
    refine fragR_append (fragR_append (add_const o scr_out hD hA8 rfl rfl (ascii_lit _ rfl) (by
      simp only [h6]; omega)) (add_fmt o scr_out hA hD hcode hP1 hb1 rfl (name := "o8") (by decide)
      (by decide) rfl rfl hw1 hw1' (by simp only [List.length_append, ascii_length, h6]; omega)))
      (fragR_conseq (add_const o scr_out hD hA8 rfl rfl (ascii_lit _ rfl) (by
        simp only [List.length_append, ascii_length, h6, h2]; omega)) (fun _ h => h) fun u h => ?_)
    have e : OUT2 ++ DN.News.CommandSpec.ascii "Date: " ++ ArticleSpec.formatDate ctx.wall ++
        DN.News.CommandSpec.ascii "\r\n" = OUT2 ++ (DN.News.CommandSpec.ascii "Date: " ++
        ArticleSpec.formatDate ctx.wall ++ DN.News.CommandSpec.crlf) := by simp only [List.append_assoc, ascii_crlf]
    rw [e] at h
    exact aout_of h fun q hq => by
      simp only [outL, List.mem_cons, List.mem_nil_iff, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl <;> rfl
  · have hdt : dateText ctx a L = [] := if_neg (by simp [hs])
    rw [hdt, List.append_nil]
    exact fragR_of (frag_nil o fun u h => h)

/-- What Injection-Info adds to the header section. -/
def infoText (ctx : ArticleSpec.Context) : Bytes :=
  DN.News.CommandSpec.ascii "Injection-Info: " ++ ctx.identity ++ DN.News.CommandSpec.ascii "; logging-data=" ++
    ArticleSpec.decimal ctx.run ++ DN.News.CommandSpec.ascii "." ++ ArticleSpec.decimal ctx.conn ++
    DN.News.CommandSpec.crlf

theorem info_low : LowKK (putConst "Injection-Info: " ++ guardL (copyS "o9" (n xId) (v "idl")) ++
    putConst "; logging-data=" ++ guardL (numS "oa" (wd xRun)) ++ putConst "." ++ guardL (numS "ob" (wd xConn)) ++
    putConst "\r\n") :=
  lowKK_append (lowKK_append (lowKK_append (lowKK_append (lowKK_append (lowKK_append (putConst_low _)
    (lowK_any _ (k := .skip) rfl)) (putConst_low _)) (lowK_any _ (k := .skip) rfl)) (putConst_low _))
    (lowK_any _ (k := .skip) rfl)) (putConst_low _)

theorem outL_next {A : Word} {RL IDL : Nat} (L : List (String × Value)) (O' : Nat)
    (h2 : L.lookup "rl" = some (BitVec.ofNat 64 RL)) (h3 : L.lookup "idl" = some (BitVec.ofNat 64 IDL))
    (h4 : L.lookup "a" = some A) :
    ∀ q ∈ outL A RL IDL O', (("o", BitVec.ofNat 64 O') :: without "o" L).lookup q.1 = some q.2 :=
  o_next (fun q hq => by
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hq
    rcases hq with rfl | rfl | rfl <;> exact ⟨by simp, by assumption⟩) O'

/-- **Injection-Info**: the server's identity, the run and the connection. -/
theorem info_step (o : Oracle σ) {R : Ret} {A : Word} {s1 : PancakeState σ} (hA : Area ArticleProg.ofs A s1)
    (hD : ArtDom A s1.memaddrs) (hcode : ArtCode s1.code) (hsz : ArticleProg.size esP < 2 ^ 40) {m0 : Word → Word}
    (hb : m0 (at_ A aBroken) = 0) {ctx : ArticleSpec.Context} (hctx : CtxAt A s1.memaddrs s1.be ctx m0)
    {MID : Bytes} {OUT3 : Bytes} (hfit : (OUT3 ++ infoText ctx).length ≤ ArticleProg.outMax) :
    FragR o R (putConst "Injection-Info: " ++ guardL (copyS "o9" (n xId) (v "idl")) ++
      putConst "; logging-data=" ++ guardL (numS "oa" (wd xRun)) ++ putConst "." ++ guardL (numS "ob" (wd xConn)) ++
      putConst "\r\n")
      (MOut s1 A m0 MID (outL A ctx.random.length ctx.identity.length OUT3.length) OUT3)
      (MOut s1 A m0 MID (outL A ctx.random.length ctx.identity.length (OUT3 ++ infoText ctx).length)
        (OUT3 ++ infoText ctx)) := by
  have hA8 := hA.hA
  obtain ⟨hi1, -, hi3, -, -, -, -, -, hru1, hru2, hc1, hc2, -, -⟩ := hctx
  have hX := xOut_eq; have hXm := xMsg_eq; have hXd := xDec_eq; have hXi := xId_eq; have hXg := xGroups_eq
  have hdr := decimal_le20 ctx.run hru1
  have hdc := decimal_le20 ctx.conn hc1
  have h16 : "Injection-Info: ".length = 16 := rfl
  have h15 : "; logging-data=".length = 15 := rfl
  have h1 : ".".length = 1 := rfl
  have h2 : "\r\n".length = 2 := rfl
  have hcr : DN.News.CommandSpec.crlf.length = 2 := rfl
  have hfit' := hfit
  simp only [infoText, List.length_append, ascii_length, h16, h15, h1, hcr] at hfit'
  refine mout_lift o info_low fun M1 hm => ?_
  simp only [List.append_assoc]
  have hfr1 := hm.2.2
  have hb1 : M1 (at_ A aBroken) = 0 := (hfr1 _ broken_add).trans hb
  have hid1 : BytesAt A s1.memaddrs s1.be ArticleProg.xId ctx.identity.length ctx.identity M1 :=
    bytesAt_frame hi3 fun i _ hl => hfr1 _ (mid_add hA8 (by omega) (by omega))
  refine fragR_append (add_const o scr_out hD hA8 rfl rfl (ascii_lit _ rfl) (by simp only [h16]; omega)) ?_
  refine fragR_append (add_norm (add_copy o scr_out hA hD hcode hsz hb1 rfl (name := "o9") (by decide) (by decide)
    rfl (SRC := ctx.identity) rfl (S0 := ArticleProg.xId) hid1 (fun i hi => mid_add hA8 (by omega) (by omega))
    (by omega) (by simp only [List.length_append, ascii_length, h16]; omega) (lowK_any _ (k := .skip) rfl) rfl rfl
    (fun u M h _ => rfl) fun u M h _ => ev_var (vals_lookup h.1.vals rfl)) (outL_next _ _ rfl rfl rfl)) ?_
  refine fragR_append (add_norm (add_const o scr_out hD hA8 rfl rfl (ascii_lit _ rfl) (by
    simp only [List.length_append, ascii_length, h16, h15]; omega)) (outL_next _ _ rfl rfl rfl)) ?_
  refine fragR_append (add_norm (add_num o scr_out hA hD hcode hb1 rfl (name := "oa") (by decide) (by decide) rfl rfl
    (X := ctx.run) hru1 (by simp only [List.length_append, ascii_length, h16, h15]; omega)
    (lowK_any _ (k := .skip) rfl) (wd_lower 4) fun u M h hfr => by
      rw [loadA_eval h.1.memaddrs (artDom_w hD (i := 4) (by decide)) (atA_eval (vals_lookup h.1.vals rfl)), h.2]
      exact congrArg some ((hfr _ (scr_not scr_out (not_addScr_w (i := 4) (by decide) (by decide)))).trans
        ((hfr1 _ (not_addScr_w (i := 4) (by decide) (by decide))).trans hru2))) (outL_next _ _ rfl rfl rfl)) ?_
  refine fragR_append (add_norm (add_const o scr_out hD hA8 rfl rfl (ascii_lit _ rfl) (by
    simp only [List.length_append, ascii_length, h16, h15, h1]; omega)) (outL_next _ _ rfl rfl rfl)) ?_
  refine fragR_append (add_norm (add_num o scr_out hA hD hcode hb1 rfl (name := "ob") (by decide) (by decide) rfl rfl
    (X := ctx.conn) hc1 (by simp only [List.length_append, ascii_length, h16, h15, h1]; omega)
    (lowK_any _ (k := .skip) rfl) (wd_lower 5) fun u M h hfr => by
      rw [loadA_eval h.1.memaddrs (artDom_w hD (i := 5) (by decide)) (atA_eval (vals_lookup h.1.vals rfl)), h.2]
      exact congrArg some ((hfr _ (scr_not scr_out (not_addScr_w (i := 5) (by decide) (by decide)))).trans
        ((hfr1 _ (not_addScr_w (i := 5) (by decide) (by decide))).trans hc2))) (outL_next _ _ rfl rfl rfl)) ?_
  refine fragR_conseq (add_const o scr_out hD hA8 rfl rfl (ascii_lit _ rfl) (by
    simp only [List.length_append, ascii_length, h16, h15, h1, h2]; omega)) (fun _ h => h) fun u h => ?_
  have e : OUT3 ++ DN.News.CommandSpec.ascii "Injection-Info: " ++ ctx.identity ++
      DN.News.CommandSpec.ascii "; logging-data=" ++ ArticleSpec.decimal ctx.run ++ DN.News.CommandSpec.ascii "." ++
      ArticleSpec.decimal ctx.conn ++ DN.News.CommandSpec.ascii "\r\n" = OUT3 ++ infoText ctx := by
    simp only [infoText, List.append_assoc, ascii_crlf]
  rw [e] at h
  exact aout_of h (outL_next _ _ rfl rfl rfl)

/-- Whether a field of a name is there, as the program asks it. -/
def triP (i m d : Nat) : Syntax.PExpr :=
  eAnd (eEq (eLe (n 0) (firstOf esP "Injection-Date")) (n i))
    (eAnd (eEq (eLe (n 0) (firstOf esP "Message-ID")) (n m)) (eEq (eLe (n 0) (firstOf esP "Date")) (n d)))

theorem addDateE_eq : addDateE = Syntax.eOr (Syntax.eOr (Syntax.eOr (n 0) (triP 0 0 0)) (triP 0 0 1)) (triP 0 1 0) :=
  rfl

def flagE (s : String) : PancakeExp := .cmp .notLess (firstE esP s) (.const (BitVec.ofNat 64 0))

def triE (i m d : Nat) : PancakeExp :=
  .op .and_ (.cmp .equal (flagE "Injection-Date") (.const (BitVec.ofNat 64 i)))
    (.op .and_ (.cmp .equal (flagE "Message-ID") (.const (BitVec.ofNat 64 m)))
      (.cmp .equal (flagE "Date") (.const (BitVec.ofNat 64 d))))

def addE : PancakeExp :=
  .op .or_ (.op .or_ (.op .or_ (.const (BitVec.ofNat 64 0)) (triE 0 0 0)) (triE 0 0 1)) (triE 0 1 0)

theorem tri_lower (i m d : Nat) : Lower.lowerExp (triP i m d) = some (triE i m d) := by
  simp only [triP, Syntax.eAnd, Syntax.eEq, Lower.lowerExp, flag_lower]; rfl

theorem addDate_lower : Lower.lowerExp addDateE = some addE := by
  rw [addDateE_eq]
  simp only [Syntax.eOr, Lower.lowerExp, tri_lower]; rfl

theorem addE_eval {u : PancakeState σ} {b1 b2 b3 : Bool} (h1 : eval u (flagE "Injection-Date") = some (bw b1))
    (h2 : eval u (flagE "Message-ID") = some (bw b2)) (h3 : eval u (flagE "Date") = some (bw b3)) :
    eval u addE = some (bw (ArticleSpec.spec.injectionDate b1 b2 b3)) := by
  cases b1 <;> cases b2 <;> cases b3 <;> simp only [addE, triE, eval, h1, h2, h3] <;> rfl

/-- What Injection-Date adds to the header section. -/
def injText (ctx : ArticleSpec.Context) (a : Bytes) (L : List (Nat × Nat)) : Bytes :=
  if ArticleSpec.spec.injectionDate (firstP a L "Injection-Date").isSome (firstP a L "Message-ID").isSome
      (firstP a L "Date").isSome then
    DN.News.CommandSpec.ascii "Injection-Date: " ++ ArticleSpec.formatDate ctx.wall ++ DN.News.CommandSpec.crlf
  else []

theorem injYes_low : LowKK (putConst "Injection-Date: " ++ guardL (fmtS "oc") ++ putConst "\r\n") :=
  lowKK_append (lowKK_append (putConst_low _) (lowK_any _ (k := .skip) rfl)) (putConst_low _)

theorem decl_injYes : declared (putConst "Injection-Date: " ++ guardL (fmtS "oc") ++ putConst "\r\n") = ["oc"] := by
  simp only [declared_append, putConst_declared]; rfl

/-- **A first field's flag read**, the table kept since the start. -/
theorem flag_read {s1 u : PancakeState σ} {A : Word} {M M1 m0 : Word → Word} {L : List (String × Value)}
    (hla : L.lookup "a" = some A) (hT : TabDom A s1.memaddrs esP) (hsz : ArticleProg.size esP < 2 ^ 40)
    (h : RunF s1 L (· = M) u)
    (hfr : ∀ x, ¬OutScr A x → M x = M1 x) (hfr1 : ∀ x, ¬AddScr A x → M1 x = m0 x) {a : Bytes} {SEP : Nat}
    {L0 : List (Nat × Nat)} (hL : Lines a 0 L0 SEP) (hok : L0.any (DN.News.ArticleLines.malLine a) = false)
    (hlen : a.length ≤ artMax) {s : String} (hfw : FirstW A m0 a L0 s) :
    eval u (flagE s) = some (bw (firstP a L0 s).isSome) := by
  have hM := artMax_eq
  have hlt := firstP_lt (nm := s) hL hok
  have hft : ¬AddScr A (at_ A (ArticleProg.xFirst + 8 * ArticleProg.entryOf esP s)) :=
    high_add (Nat.le_add_right _ _) (by have := xFirst_eq; have := entry_le55 s; omega)
  exact flag_eval (fun x hx => by have := hlt x hx; omega)
    ((first_eval hla hT hsz scr_out h hfr).trans (congrArg some ((hfr1 _ hft).trans hfw)))

/-- **Injection-Date** added as the rules say, from which first fields the article has. -/
theorem inj_step (o : Oracle σ) {R : Ret} {A : Word} {s1 : PancakeState σ} (hA : Area ArticleProg.ofs A s1)
    (hD : ArtDom A s1.memaddrs) (hcode : ArtCode s1.code) (hT : TabDom A s1.memaddrs esP)
    (hsz : ArticleProg.size esP < 2 ^ 40) {m0 : Word → Word} (hP : Pows m0 A) (hb : m0 (at_ A aBroken) = 0)
    {ctx : ArticleSpec.Context}
    (hctx : CtxAt A s1.memaddrs s1.be ctx m0) {a : Bytes} {SEP : Nat} {L : List (Nat × Nat)} (hL : Lines a 0 L SEP)
    (hok : L.any (DN.News.ArticleLines.malLine a) = false) (hlen : a.length ≤ artMax)
    (hf1 : FirstW A m0 a L "Injection-Date") (hf2 : FirstW A m0 a L "Message-ID") (hf3 : FirstW A m0 a L "Date")
    {MID : Bytes} {RL IDL : Nat} {OUT4 : Bytes} (hfit : (OUT4 ++ injText ctx a L).length ≤ ArticleProg.outMax) :
    FragR o R ([.ite addDateE (putConst "Injection-Date: " ++ guardL (fmtS "oc") ++ putConst "\r\n") []] : Ss)
      (MOut s1 A m0 MID (outL A RL IDL OUT4.length) OUT4)
      (MOut s1 A m0 MID (outL A RL IDL (OUT4 ++ injText ctx a L).length) (OUT4 ++ injText ctx a L)) := by
  have hA8 := hA.hA
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hw1, hw2⟩ := hctx
  refine mout_lift o (lowKK_ite addDate_lower injYes_low (lowK_any _ (k := .skip) rfl)) fun M1 hm => ?_
  have hfr1 := hm.2.2
  have hb1 : M1 (at_ A aBroken) = 0 := (hfr1 _ broken_add).trans hb
  have hw1' : M1 (at_ A ArticleProg.xWall) = BitVec.ofNat 64 ctx.wall :=
    (hfr1 _ (not_addScr_w (i := 2) (by decide) (by decide))).trans hw2
  have hP1 := pows_frame scr_add hfr1 hP
  refine fragR_if o addDate_lower injYes_low (lowK_any _ (k := .skip) rfl) aout_clock
    (fun u y w h hy => by
      rw [decl_injYes] at hy; simp only [List.mem_singleton] at hy; subst hy; exact aout_restore h rfl w)
    (fun u y w h hy => by change y ∈ [] at hy; cases hy)
    (b := ArticleSpec.spec.injectionDate (firstP a L "Injection-Date").isSome (firstP a L "Message-ID").isSome
      (firstP a L "Date").isSome)
    (fun u ⟨M, hr, _, hfr⟩ => addE_eval (flag_read rfl hT hsz hr hfr hfr1 hL hok hlen hf1)
      (flag_read rfl hT hsz hr hfr hfr1 hL hok hlen hf2) (flag_read rfl hT hsz hr hfr hfr1 hL hok hlen hf3))
    (fun hs => ?_) (fun hs => ?_)
  · have hdt : injText ctx a L = DN.News.CommandSpec.ascii "Injection-Date: " ++ ArticleSpec.formatDate ctx.wall ++
        DN.News.CommandSpec.crlf := if_pos hs
    rw [hdt] at hfit ⊢
    have h16 : "Injection-Date: ".length = 16 := rfl
    have h2 : "\r\n".length = 2 := rfl
    have hcr : DN.News.CommandSpec.crlf.length = 2 := rfl
    simp only [List.length_append, ascii_length, h16, hcr] at hfit
    refine fragR_append (fragR_append (add_const o scr_out hD hA8 rfl rfl (ascii_lit _ rfl) (by
      simp only [h16]; omega)) (add_fmt o scr_out hA hD hcode hP1 hb1 rfl (name := "oc") (by decide)
      (by decide) rfl rfl hw1 hw1' (by simp only [List.length_append, ascii_length, h16]; omega)))
      (fragR_conseq (add_const o scr_out hD hA8 rfl rfl (ascii_lit _ rfl) (by
        simp only [List.length_append, ascii_length, h16, h2]; omega)) (fun _ h => h) fun u h => ?_)
    have e : OUT4 ++ DN.News.CommandSpec.ascii "Injection-Date: " ++ ArticleSpec.formatDate ctx.wall ++
        DN.News.CommandSpec.ascii "\r\n" = OUT4 ++ (DN.News.CommandSpec.ascii "Injection-Date: " ++
        ArticleSpec.formatDate ctx.wall ++ DN.News.CommandSpec.crlf) := by simp only [List.append_assoc, ascii_crlf]
    rw [e] at h
    exact aout_of h fun q hq => by
      simp only [outL, List.mem_cons, List.mem_nil_iff, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl <;> rfl
  · have hdt : injText ctx a L = [] := if_neg (by simp [hs])
    rw [hdt, List.append_nil]
    exact fragR_of (frag_nil o fun u h => h)

/-! ## The head and the whole -/

/-- **The head**: the area, the output's place, the lengths checked, and the server's part of Path. -/
theorem head_frag (o : Oracle σ) {R : Ret} {A : Word} {s1 : PancakeState σ} (hA : Area ArticleProg.ofs A s1)
    (hD : ArtDom A s1.memaddrs) (hcode : ArtCode s1.code) (hsz : ArticleProg.size esP < 2 ^ 40)
    (hb : s1.memory (at_ A aBroken) = 0) {ctx : ArticleSpec.Context}
    (hctx : CtxAt A s1.memaddrs s1.be ctx s1.memory) :
    FragR o R (([areaAt ArticleProg.ofs, .dec "o" (n 0), .dec "idl" (wd xIdLen), kept "idl" 200,
      .dec "rl" (wd xRandLen), kept "rl" 16] : Ss) ++ putConst "Path: " ++ guardL (copyS "o1" (n xId) (v "idl")) ++
      putConst "!.POSTED")
      (RunF s1 [] (· = s1.memory))
      (AOut (AddScr A) s1 A s1.memory (outL A ctx.random.length ctx.identity.length (pathHead ctx).length)
        (pathHead ctx)) := by
  have hA8 := hA.hA
  obtain ⟨hi1, hi2, hi3, hr1, hr2, -, -, -, -, -, -, -, -, -⟩ := hctx
  have hX := xOut_eq; have hXm := xMsg_eq; have hXd := xDec_eq; have hXi := xId_eq; have hXg := xGroups_eq
  have h6 : "Path: ".length = 6 := rfl
  have h8 : "!.POSTED".length = 8 := rfl
  have hom : ArticleProg.outMax = 69632 := rfl
  have e0 : ([] : Bytes).length = 0 := rfl
  have e1 : ([] : List DN.News.FrameSpec.Byte).length = 0 := rfl
  obtain ⟨EA, hEA⟩ := atOff_lower ArticleProg.ofs
  refine fragR_append (fragR_append (fragR_append ?_ (add_const o scr_add hD hA8
    (L := [("rl", BitVec.ofNat 64 ctx.random.length), ("idl", BitVec.ofNat 64 ctx.identity.length),
      ("o", BitVec.ofNat 64 0), ("a", A)]) rfl (P := []) rfl (ascii_lit _ rfl) (by simp only [h6]; decide)))
    (add_copy o scr_add hA hD hcode hsz hb rfl (name := "o1") (by decide)
    (by decide) rfl (SRC := ctx.identity) rfl (S0 := ArticleProg.xId) hi3
    (fun i hi => mid_add hA8 (by omega) (by omega)) (by omega)
    (by simp only [List.length_append, ascii_length, h6]; omega) (lowK_any _ (k := .skip) rfl) rfl
    rfl (fun u M h _ => rfl) fun u M h _ => ev_var (vals_lookup h.1.vals rfl)))
    (fragR_conseq (add_const o scr_add hD hA8 rfl rfl (ascii_lit _ rfl) (by
      simp only [List.length_append, ascii_length, h6, h8]; omega)) (fun _ h => h) fun u h => ?_)
  · refine fragR_append (xs := [_]) (fragR_of (runF_dec o hEA rfl (v := A) fun u h => areaAt_eval hA h.1.base hEA)) ?_
    refine fragR_append (xs := [_]) (fragR_of (runF_dec o rfl rfl (v := BitVec.ofNat 64 0) fun u h => rfl)) ?_
    refine fragR_append (xs := [_]) (fragR_of (runF_dec o (wd_lower 6) rfl
      (v := BitVec.ofNat 64 ctx.identity.length) fun u h => by
        rw [loadA_eval h.1.memaddrs (artDom_w hD (i := 6) (by decide)) (atA_eval (vals_lookup h.1.vals rfl)), h.2]
        exact congrArg some hi2)) ?_
    refine fragR_append (xs := [_]) (fragR_of (kept_frag o (by decide) (runF_clock _ _ _) fun u h =>
      ⟨_, vals_lookup h.1.vals rfl, hi1⟩)) ?_
    refine fragR_append (xs := [_]) (fragR_of (runF_dec o (wd_lower 7) rfl
      (v := BitVec.ofNat 64 ctx.random.length) fun u h => by
        rw [loadA_eval h.1.memaddrs (artDom_w hD (i := 7) (by decide)) (atA_eval (vals_lookup h.1.vals rfl)), h.2]
        exact congrArg some hr2)) ?_
    refine fragR_conseq (fragR_of (kept_frag o (by decide) (runF_clock _ _ _) fun u h =>
      ⟨_, vals_lookup h.1.vals rfl, hr1⟩)) (fun _ h => h) fun u h => ?_
    exact ⟨s1.memory, h, fun _ _ hi => absurd hi (Nat.not_lt_zero _), fun _ _ => rfl⟩
  · have e : [] ++ DN.News.CommandSpec.ascii "Path: " ++ ctx.identity ++ DN.News.CommandSpec.ascii "!.POSTED" =
        pathHead ctx := by rw [List.nil_append]; rfl
    rw [e] at h
    exact aout_of h (outL_next _ _ rfl rfl rfl)

/-- The header section `artAdded` writes, piece by piece. -/
def addedText (ctx : ArticleSpec.Context) (a : Bytes) (L : List (Nat × Nat)) : Bytes :=
  ArticleSpec.pathField ArticleSpec.spec ctx (ArticleSpec.find? ((groups a L).map (fieldOf a)) "Path") ++
    keptT a (groups a L) ++ midText ctx a L ++ dateText ctx a L ++ infoText ctx ++ injText ctx a L

theorem firstP_some {a : Bytes} {L : List (Nat × Nat)} {nm : String} {g : List (Nat × Nat)}
    (h : firstG a L nm = some g) : (firstP a L nm).isSome = true := by unfold firstP; rw [h]; rfl

theorem firstP_none {a : Bytes} {L : List (Nat × Nat)} {nm : String} (h : firstG a L nm = none) :
    (firstP a L nm).isSome = false := by unfold firstP; rw [h]; rfl

/-- **The message identifier the rules keep** is `midOf`'s. -/
theorem added_mid (ctx : ArticleSpec.Context) (a : Bytes) (L : List (Nat × Nat)) :
    (ArticleSpec.added ArticleSpec.spec ctx ((groups a L).map (fieldOf a))).messageId = midOf ctx a L := by
  have hrep : ArticleSpec.spec.replace = false := rfl
  simp only [ArticleSpec.added, has_fields, find_fields, hrep, Bool.or_false]
  unfold midOf
  cases hg : firstG a L "Message-ID" with
  | none => rw [firstP_none hg]; rfl
  | some g => rw [firstP_some hg]; rfl

/-- **The header section the rules make** is `addedText`. -/
theorem added_header (ctx : ArticleSpec.Context) (a : Bytes) (L : List (Nat × Nat)) :
    (ArticleSpec.added ArticleSpec.spec ctx ((groups a L).map (fieldOf a))).header = addedText ctx a L := by
  have hrep : ArticleSpec.spec.replace = false := rfl
  have hkept : ∀ fs : List Field, ((fs.filter fun f => !ArticleSpec.named f.name "Path" &&
      !(false && (ArticleSpec.named f.name "Message-ID" || ArticleSpec.named f.name "Date"))).map
        (·.text)).flatten = ((fs.filter keepF).map (·.text)).flatten := fun fs => by
    congr 2; apply List.filter_congr; intro f _; simp [keepF]
  have hd : ∀ p : Option Nat, (!p.isSome) = p.isNone := fun p => by cases p <;> rfl
  simp only [ArticleSpec.added, has_fields, find_fields, hrep, Bool.or_false, hkept, hd]
  unfold addedText keptT midText dateText infoText injText
  cases hg : firstG a L "Message-ID" with
  | none =>
    simp only [first_none hg, Option.isNone_none, Option.isSome_none, if_true, newIdText, List.append_assoc,
      find_fields, Option.map_none]
  | some g =>
    have hp : firstP a L "Message-ID" = some (g.headD (0, 0)).1 := by unfold firstP; rw [hg]; rfl
    simp only [hp, Option.isNone_some, Option.isSome_some, Bool.false_eq_true, if_false, List.append_assoc,
      List.nil_append, find_fields]

theorem artAdded_parts : guardL (ArticleProg.artAdded ArticleSpec.spec esP .none).body =
    (([areaAt ArticleProg.ofs, .dec "o" (n 0), .dec "idl" (wd xIdLen), kept "idl" 200, .dec "rl" (wd xRandLen),
      kept "rl" 16] : Ss) ++ putConst "Path: " ++ guardL (copyS "o1" (n xId) (v "idl")) ++ putConst "!.POSTED") ++
    (([.dec "pp" (firstOf esP "Path"), .ite (eLe (n 0) (v "pp")) (guardL pathYes) (putConst "!not-for-mail\r\n"),
      .dec "sep" (wd xSep), .dec "p" (n 0), .while (eLt (v "p") (v "sep")) (guardL keptBody),
      .dec "hid" (firstOf esP "Message-ID"), .ite (eLt (v "hid") (n 0)) (guardL newIdS) (guardL oldIdS),
      .ite (eLt (firstOf esP "Date") (n 0)) (putConst "Date: " ++ guardL (fmtS "o8") ++ putConst "\r\n") []] : Ss) ++
    ((putConst "Injection-Info: " ++ guardL (copyS "o9" (n xId) (v "idl")) ++ putConst "; logging-data=" ++
      guardL (numS "oa" (wd xRun)) ++ putConst "." ++ guardL (numS "ob" (wd xConn)) ++ putConst "\r\n") ++
    ([.ite addDateE (putConst "Injection-Date: " ++ guardL (fmtS "oc") ++ putConst "\r\n") [],
     setW xOutLen (v "o"), .ret (n 0)] : Ss))) := by
  rw [artAdded_body]; simp only [List.append_assoc]

/-- What `artAdded` leaves: 0, and the header section `H` and the message identifier `MID` with their lengths. Every
word outside `AddScr` is as before. -/
def AddRet (A : Word) (dm : Word → Bool) (be : Bool) (H MID : Bytes) (m0 : Word → Word) : Ret := fun w m =>
  w = 0 ∧ (∀ x, ¬AddScr A x → m x = m0 x) ∧ BytesAt A dm be ArticleProg.xOut ArticleProg.outMax H m ∧
    m (at_ A xOutLen) = BitVec.ofNat 64 H.length ∧ BytesAt A dm be ArticleProg.xMsg ArticleProg.msgCap MID m ∧
    m (at_ A ArticleProg.xMsgLen) = BitVec.ofNat 64 MID.length

/-- The message identifier's bytes kept where only output words and the output's length change. -/
theorem msg_keep {A : Word} (hA8 : A.toNat % 8 = 0) {dm : Word → Bool} {be : Bool} {MID : Bytes}
    {M M1 : Word → Word} (hfr : ∀ x, ¬OutScr A x → M x = M1 x)
    (h : BytesAt A dm be ArticleProg.xMsg ArticleProg.msgCap MID M1) (val : Word) :
    BytesAt A dm be ArticleProg.xMsg ArticleProg.msgCap MID (upd M (at_ A xOutLen) val) :=
  bytesAt_frame h fun i hi _ => by
    have hm := xMsg_eq; have hd := xDec_eq; have hX := X_val; have hmc : ArticleProg.msgCap = 256 := rfl
    rw [DN.News.ScanRun.align_at hA8]
    have hne : at_ A ((ArticleProg.xMsg + i) / 8 * 8) ≠ at_ A xOutLen :=
      DN.News.ScanRun.at_ne (by omega) (w_lt64 (i := 12) (by decide)) (by simp only [xOutLen, ArticleProg.w]; omega)
    rw [upd_ne _ hne]
    exact hfr _ fun ⟨z, h1, h2, e⟩ => by
      have := DN.News.ScanRun.at_inj (by omega) (by rw [xFirst_eq] at h2; omega) e
      omega

/-- **`artAdded` writes the header section and the message identifier the rules make**, if it returns. It needs the
lines `L` of a section with no malformed line and the first fields' places. It needs the context and room. -/
theorem artAdded_ok (o : Oracle σ) {A : Word} {s1 : PancakeState σ} (hA : Area ArticleProg.ofs A s1)
    (hD : ArtDom A s1.memaddrs) (hcode : ArtCode s1.code) (hT : TabDom A s1.memaddrs esP)
    (htab : TablesAt A s1.memaddrs s1.be s1.memory esP) (hes : ∀ s ∈ esP, s.length ≤ 64)
    (hsz : ArticleProg.size esP < 2 ^ 40) (hP : Pows s1.memory A) (hb : s1.memory (at_ A aBroken) = 0)
    {ctx : ArticleSpec.Context} (hctx : CtxAt A s1.memaddrs s1.be ctx s1.memory) {a : Bytes}
    (hlen : a.length ≤ artMax) (hin : InputAt s1.memory s1.memaddrs s1.be A a) {SEP : Nat}
    (hsep : s1.memory (at_ A xSep) = BitVec.ofNat 64 SEP) {L : List (Nat × Nat)} (hL : Lines a 0 L SEP)
    (hok : L.any (DN.News.ArticleLines.malLine a) = false) (hf1 : FirstW A s1.memory a L "Path")
    (hf2 : FirstW A s1.memory a L "Message-ID") (hf3 : FirstW A s1.memory a L "Date")
    (hf4 : FirstW A s1.memory a L "Injection-Date")
    (hfit : (ArticleSpec.added ArticleSpec.spec ctx ((groups a L).map (fieldOf a))).header.length ≤
      ArticleProg.outMax)
    (hmidl : (ArticleSpec.added ArticleSpec.spec ctx ((groups a L).map (fieldOf a))).messageId.length <
      ArticleProg.msgCap) :
    ∃ body, Lower.lower (gd (ArticleProg.artAdded ArticleSpec.spec esP .none)) = some body ∧
      SafeR o (fun s => s = s1) body (AddRet A s1.memaddrs s1.be
        (ArticleSpec.added ArticleSpec.spec ctx ((groups a L).map (fieldOf a))).header
        (ArticleSpec.added ArticleSpec.spec ctx ((groups a L).map (fieldOf a))).messageId s1.memory)
        fun _ => False := by
  have hA8 := hA.hA
  have hid := hctx.1
  rw [added_header] at hfit ⊢
  rw [added_mid] at hmidl ⊢
  have hfit' := hfit
  simp only [addedText, List.length_append] at hfit'
  refine body_of ?_
  show FragR o _ (guardL (ArticleProg.artAdded ArticleSpec.spec esP .none).body) _ _
  rw [artAdded_parts]
  refine fragR_conseq (P0 := RunF s1 [] (· = s1.memory)) ?_ (entry_run (l := []) (fun q hq => nomatch hq) rfl)
    fun _ h => h
  refine fragR_append (head_frag o hA hD hcode hsz hb hctx) ?_
  refine fragR_append (xs := [_, _]) (path_sel o hA hD hcode hsz hlen hin hb hsep hT hL hok hf1 ctx hid
    (by omega)) ?_
  refine fragR_append (xs := [_]) (fragR_of (add_dec o (wd_lower 16) rfl (val := BitVec.ofNat 64 SEP)
    fun u M h hfr => by
      rw [loadA_eval h.1.memaddrs (artDom_w hD (i := 16) (by decide)) (atA_eval (vals_lookup h.1.vals rfl)), h.2]
      exact congrArg some ((hfr _ (not_addScr_w (i := 16) (by decide) (by decide))).trans hsep))) ?_
  refine fragR_append (xs := [_]) (fragR_of (add_dec o rfl rfl (val := BitVec.ofNat 64 0) fun _ _ _ _ => rfl)) ?_
  refine fragR_append (xs := [_]) (fragR_conseq (loop_frag o hA hD hcode hlen hin hb hsep hT htab hes hsz hL hok
    (RL := ctx.random.length) (IDL := ctx.identity.length)
    (OUT0 := ArticleSpec.pathField ArticleSpec.spec ctx (ArticleSpec.find? ((groups a L).map (fieldOf a)) "Path"))
    (by simp only [List.length_append]; omega)) (fun u h => aout_of h fun q hq => by
      simp only [loopL, baseL, List.mem_cons, List.mem_nil_iff, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl) fun _ h => h) ?_
  refine fragR_append (xs := [_, _]) (msg_sel o hA hD hcode hsz hlen hin hb hsep hT hL hok hf2 hctx
    (by simp only [List.length_append]; omega) hmidl) ?_
  refine fragR_append (xs := [_]) (date_step o hA hD hcode hT hsz hP hb hctx hL hok hlen hf3
    (by simp only [List.length_append]; omega)) ?_
  refine fragR_append (info_step o hA hD hcode hsz hb hctx (by simp only [List.length_append]; omega)) ?_
  refine fragR_append (xs := [_]) (inj_step o hA hD hcode hT hsz hP hb hctx hL hok hlen hf4 hf2 hf3
    (by simp only [List.length_append]; omega)) ?_
  -- the output's length stored, and the return
  refine fragR_exists (lowK_any _ (k := .skip) rfl) fun M1 => ?_
  refine fragR_pure (MsgF A s1.memaddrs s1.be (midOf ctx a L) s1.memory M1) (fun u h => h.1)
    (lowK_any _ (k := .skip) rfl) fun hm => ?_
  refine fragR_conseq ?_ (fun u h => h.2) fun _ h => h
  refine fragR_exists (lowK_any _ (k := .skip) rfl) fun M => ?_
  refine fragR_pure (BytesAt A s1.memaddrs s1.be ArticleProg.xOut ArticleProg.outMax (addedText ctx a L) M ∧
    ∀ x, ¬OutScr A x → M x = M1 x) (fun u h => h.2) (lowK_any _ (k := .skip) rfl) fun ⟨hO, hfr⟩ => ?_
  refine fragR_conseq ?_ (fun u h => h.1) fun _ h => h
  refine fragR_append (xs := [_]) (fragR_of (runF_storeA o
    (D := .op .add (.var "a") (.const (BitVec.ofNat 64 (ArticleProg.w 12)))) (E := .var "o")
    (by simp only [Syntax.atOff]; rfl) rfl (y := ArticleProg.w 12) (artDom_w hD (by decide))
    (fun u h => atA_eval (vals_lookup h.1.vals rfl)) (val := fun _ => BitVec.ofNat 64 (addedText ctx a L).length)
    (fun u h => ev_var (vals_lookup h.1.vals rfl))
    (G := (· = upd M (at_ A xOutLen) (BitVec.ofNat 64 (addedText ctx a L).length))) fun m h => by rw [h]; rfl)) ?_
  refine fragR_ret o rfl fun u h => ⟨0, rfl, rfl, fun x hx => ?_, ?_, ?_, ?_, ?_⟩
  · rw [h.2, upd_ne _ fun e => hx (.inr (.inr (.inr (.inr (.inr (.inr e))))))]
    exact (hfr x fun ho => hx (.inl ho)).trans (hm.2.2 x hx)
  · rw [h.2]
    exact bytesAt_frame hO fun i hi _ => upd_ne _ (out_ne_w (out_at hA8 hi) (k := 12) (by decide))
  · rw [h.2]; exact upd_eq _ _ _
  · rw [h.2]; exact msg_keep hA8 hfr hm.1 _
  · rw [h.2]
    exact (upd_ne _ (w_ne (i := 13) (j := 12) (by decide) (by decide) (by decide) A)).trans
      ((hfr _ fun ho => out_ne_w ho (k := 13) (by decide) rfl).trans hm.2.1)

/-! ## The premises can hold -/

theorem scr_witness : Scr 0 (AddScr 0) := scr_add

theorem outScr_witness : OutScr 0 (at_ 0 ArticleProg.xDec) :=
  ⟨_, Nat.le_refl _, by rw [xDec_eq, xFirst_eq]; decide, rfl⟩

/-- A context: the identity `a`, the random value `0`, the sequence number, run, connection and clock 1. -/
def wCtx : ArticleSpec.Context := ⟨[], DN.News.CommandSpec.ascii "a", 1, 1, DN.News.CommandSpec.ascii "0", 1, 1⟩

/-- An area holding `wCtx`: the identity's and the random value's bytes, every other word 1. -/
def wCtxMem : Word → Word := fun x =>
  if x = at_ 0 ArticleProg.xId then 97 else if x = at_ 0 ArticleProg.xRand then 48 else 1

theorem ctxAt_witness : CtxAt 0 (fun _ => true) false wCtx wCtxMem := by
  refine ⟨by decide, by decide, fun i hi _ => ?_, by decide, by decide, fun i hi _ => ?_, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩
  · obtain rfl : i = 0 := by have : wCtx.identity.length = 1 := rfl; omega
    decide
  · obtain rfl : i = 0 := by have : wCtx.random.length = 1 := rfl; omega
    decide

/-- An article of one field, Path, and the empty line. -/
def wPath : Bytes := DN.News.CommandSpec.ascii "Path: x\r\n\r\n"

theorem firstW_witness : Lines wPath 0 [(0, 7)] 9 ∧ [(0, 7)].any (DN.News.ArticleLines.malLine wPath) = false ∧
    FirstW 0 (fun _ => 0) wPath [(0, 7)] "Path" := by
  refine ⟨.line (by decide) (by decide) (by decide) (.sep (by decide) (by decide)), by decide, ?_⟩
  unfold FirstW firstP firstG
  rw [groups_cons, List.takeWhile_nil, List.dropWhile_nil, show groups wPath [] = [] by rw [groups]]
  decide

theorem loopF_witness : LoopF DN.News.ArticleLines.wArt [(0, 2)] 4 (0, [(0, 2)], []) :=
  ⟨DN.News.ArticleLines.lines_witness, fun _ h => h, fun q r h => by cases h; decide, rfl⟩

theorem aout_witness : AOut (σ := Unit) (AddScr 0) (bareState ()) 0 (bareState ()).memory [] [] (bareState ()) :=
  ⟨(bareState ()).memory, ⟨run_witness, rfl⟩, fun _ _ h => absurd h (Nat.not_lt_zero _), fun _ _ => rfl⟩

theorem mout_witness : MOut (σ := Unit) (bareState ()) 0 (bareState ()).memory [] [] [] (bareState ()) :=
  ⟨(bareState ()).memory, ⟨fun _ _ h => absurd h (Nat.not_lt_zero _), rfl, fun _ _ => rfl⟩,
    (bareState ()).memory, ⟨run_witness, rfl⟩, fun _ _ h => absurd h (Nat.not_lt_zero _), fun _ _ => rfl⟩

end DN.News.ArticleAdded
