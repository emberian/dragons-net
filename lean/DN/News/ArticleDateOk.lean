-- SPDX-License-Identifier: AGPL-3.0-or-later
import DN.News.ArticleDateRun

/-!
# DN.News.ArticleDateOk

`artDate` proven to read a date-time as `DN.News.ArticleSpec.dateValue` does, if it returns. None is 0; the seconds
are 1, with them in `xValue`; 2 says they are past `2 ^ 41`.
-/

namespace DN.News.ArticleDateOk

open DN.Compiler DN.Compiler.Wp DN.Compiler.WpRet DN.Compiler.Frag DN.News.AbnfProg
open DN.News.AbnfSets DN.News.FunRun DN.News.AbnfLeaves DN.News.ArticleRun DN.News.ArticleScan DN.News.ArticleCal
open DN.News.ArticleDate DN.News.ArticleDateRun
open DN.News.ScanRun (at_ at_add vals_lookup without Fresh)
open DN.News.FramerCode (bw ev_var bw_ne0 bw_eq0)
open DN.News.AbnfComment (ev_inc)
open DN.News.ArticleProg (artMax guardL guardS ifs readIn wd tokIn isGap isDig lowerE setW)
open DN.News.ArticleLines (seg seg_succ seg_length seg_app)
open DN.News.ArticleSpec (Bytes tokens number? indexOf monthNames dayNames)
open Syntax (v n eEq eLt eLe eAnd eAdd eSub eMul)

variable {σ : Type}

/-- What `artDate` from `S` to `E` gives back. 0 if the date says none; 1, its seconds in `xValue`; 2 if past `2 ^ 41`.
Only the scratch words change. -/
def DateRet (A : Word) (a : Bytes) (S E : Nat) (m0 : Word → Word) : Ret := fun v m =>
  DFrame A m0 m ∧ (v = 0 ∧ ArticleSpec.dateValue (seg a S E) = none ∨
    v = 1 ∧ (∃ t, ArticleSpec.dateValue (seg a S E) = some t ∧ -2 ^ 42 < t ∧ t < 2 ^ 42 ∧
      m (at_ A ArticleProg.xValue) = BitVec.ofInt 64 t) ∨
    v = 2 ∧ ∃ t, ArticleSpec.dateValue (seg a S E) = some t ∧ 2 ^ 41 ≤ t)

/-- **A return of 0 on a condition**, which says the date means none. -/
theorem ret0_frag (o : Oracle σ) {R : Ret} {c : Syntax.PExpr} {C : PancakeExp} (hc : Lower.lowerExp c = some C)
    {P : Assn σ} (hP : Safe.ClockFree P) {b : Bool} (hv : ∀ u, P u → eval u C = some (bw b))
    (hR : b = true → ∀ u, P u → R 0 u.memory) :
    FragR o R [ifs c [.ret (n 0)]] P (fun u => P u ∧ b = false) :=
  fragR_if o hc (lowK_any _ (k := .skip) rfl) lowKK_nil (fun u k h => ⟨hP u k h.1, h.2⟩) (noDecl _ rfl)
    (noDecl _ rfl) hv (fun hb => fragR_ret o rfl fun u h => ⟨0, rfl, hR hb u h⟩)
    fun hb => fragR_of (frag_nil o fun _ h => ⟨h, hb⟩)

/-- The bytes before the comment's `(`. -/
theorem paren_tw (a : Bytes) {S E : Nat} (hSE : S ≤ E) (hE : E ≤ a.length) :
    (seg a S E).takeWhile (· != ArticleSpec.LPAREN) = seg a S (parenAt a S E) := by
  show (seg a S E).takeWhile notParen = _
  rw [DN.News.ArticleLines.takeWhile_take, DN.News.ArticleLines.seg_take a _ (by
    have := tw_le (p := notParen) (seg a S E); rw [seg_length a hSE hE] at this; exact this)]
  rfl

/-! ## The words the calls leave -/

theorem load_putB_other {A : Word} {dm : Word → Bool} {be : Bool} :
    ∀ {m : Word → Word} {x : Nat} {bs : Bytes} {y : Nat}, (y < x ∨ x + bs.length ≤ y) → x + bs.length < 2 ^ 63 →
      y < 2 ^ 63 → memLoadByte (putB m be A x bs) dm be (at_ A y) = memLoadByte m dm be (at_ A y)
  | _, _, [], _, _, _, _ => rfl
  | m, x, b :: bs, y, hy, hx, hy' => by
    simp only [List.length_cons] at hy hx
    simp only [putB]
    rw [load_putB_other (by omega) (by omega) hy',
      DN.Compiler.Bytes.load_putByte_diff _ _ _ _ _ _ (DN.News.ScanRun.at_ne (by omega) (by omega) (by omega))]

theorem load_putB {A : Word} {dm : Word → Bool} {be : Bool} :
    ∀ {m : Word → Word} {x : Nat} {bs : Bytes}, x + bs.length < 2 ^ 63 → ∀ i (hi : i < bs.length),
      dm (byteAlign (at_ A (x + i))) = true → memLoadByte (putB m be A x bs) dm be (at_ A (x + i)) = some bs[i]
  | m, x, b :: bs, hx, 0, _, hd => by
    simp only [List.length_cons] at hx
    simp only [putB, Nat.add_zero, List.getElem_cons_zero] at hd ⊢
    rw [load_putB_other (.inl (by omega)) (by omega) (by omega), DN.Compiler.Bytes.load_putByte_same _ _ _ _ _ hd]
  | m, x, b :: bs, hx, i + 1, hi, hd => by
    simp only [List.length_cons] at hx hi
    simp only [putB, List.getElem_cons_succ]
    rw [show x + (i + 1) = x + 1 + i by omega] at hd ⊢
    exact load_putB (by omega) i (by omega) hd

/-- The word found from `P`, before `E`. -/
abbrev tokW (a : Bytes) (P E : Nat) : Bytes := seg a (wordStart a P E) (wordEnd a (wordStart a P E) E)

theorem tokMem_len {A : Word} {be : Bool} {a : Bytes} {P E : Nat} {m : Word → Word} :
    tokMem A be a P E m (at_ A ArticleProg.xTokLen) =
      BitVec.ofNat 64 (wordEnd a (wordStart a P E) E - wordStart a P E) :=
  upd_eq _ _ _

theorem tokS_lt : ArticleProg.xTokS < ArticleProg.xTok / 8 * 8 := by decide

theorem tokMem_start {A : Word} (hA8 : A.toNat % 8 = 0) {be : Bool} {a : Bytes} {P E : Nat} {m : Word → Word} :
    tokMem A be a P E m (at_ A ArticleProg.xTokS) = BitVec.ofNat 64 (wordStart a P E) := by
  have hne : at_ A ArticleProg.xTokS ≠ at_ A ArticleProg.xTokLen :=
    DN.News.ScanRun.at_ne (w_lt64 (by decide)) (w_lt64 (by decide)) (by decide)
  unfold tokMem
  rw [upd_ne _ hne, putB_other be hA8 _ _ _ _ tokS_lt (by rw [List.length_take, xTok_eq]; omega), upd_eq]

theorem tok_align {A : Word} (hA8 : A.toNat % 8 = 0) {i : Nat} (hi : i < 8) :
    byteAlign (at_ A (ArticleProg.xTok + i)) = at_ A ArticleProg.xTok := by
  rw [DN.News.ScanRun.align_at hA8, show (ArticleProg.xTok + i) / 8 * 8 = ArticleProg.xTok by rw [xTok_eq]; omega]

/-- **The word's bytes from `xTok`**, its first eight. -/
theorem tokMem_byte {A : Word} (hA8 : A.toNat % 8 = 0) {dm : Word → Bool} (hd : dm (at_ A ArticleProg.xTok) = true)
    {be : Bool} {a : Bytes} {P E : Nat} {m : Word → Word} {i : Nat} (hi : i < 8) (hl : i < (tokW a P E).length) :
    memLoadByte (tokMem A be a P E m) dm be (at_ A (ArticleProg.xTok + i)) = some (tokW a P E)[i] := by
  have hne : at_ A ArticleProg.xTok ≠ at_ A ArticleProg.xTokLen :=
    DN.News.ScanRun.at_ne (by rw [xTok_eq]; decide) (w_lt64 (by decide)) (by decide)
  have e : memLoadByte (tokMem A be a P E m) dm be (at_ A (ArticleProg.xTok + i)) =
      memLoadByte (putB (upd m (at_ A ArticleProg.xTokS) (BitVec.ofNat 64 (wordStart a P E))) be A ArticleProg.xTok
        ((tokW a P E).take 8)) dm be (at_ A (ArticleProg.xTok + i)) := by
    simp only [memLoadByte, tok_align hA8 hi, tokMem, upd_ne _ hne]
  rw [e, load_putB (by rw [List.length_take, xTok_eq]; omega) i (by rw [List.length_take]; omega)
    (by rw [tok_align hA8 hi]; exact hd), List.getElem_take]

theorem tok_dom {A : Word} {dm : Word → Bool} (hD : ArtDom A dm) : dm (at_ A ArticleProg.xTok) = true :=
  hD _ (by have := sets_le_X; rw [xTok_eq]; rw [X_val] at this; omega) (by rw [xTok_eq, xFirst_eq]; decide)
    (by rw [xTok_eq])

/-! ## Locals read off -/

theorem lookups_nil {l : List (String × Value)} : ∀ q ∈ ([] : List (String × Value)), l.lookup q.1 = some q.2 :=
  fun _ h => nomatch h

theorem lookups_cons {l l' : List (String × Value)} {x : String} {w : Value} (h1 : l.lookup x = some w)
    (h2 : ∀ q ∈ l', l.lookup q.1 = some q.2) : ∀ q ∈ (x, w) :: l', l.lookup q.1 = some q.2 := by
  intro q hq
  rcases List.mem_cons.1 hq with rfl | hq
  · exact h1
  · exact h2 q hq

/-- Locals read off by their names. -/
theorem runF_of {s0 u : PancakeState σ} {l l' : List (String × Value)} {F : (Word → Word) → Prop}
    (h : RunF s0 l F u) (hl : ∀ q ∈ l', l.lookup q.1 = some q.2) : RunF s0 l' F u :=
  ⟨⟨fun q hq => vals_lookup h.1.vals (hl q hq), h.1.memaddrs, h.1.base, h.1.code, h.1.be⟩, h.2⟩

theorem paren_le (a : Bytes) {S E : Nat} (hSE : S ≤ E) (hE : E ≤ a.length) : parenAt a S E ≤ E := by
  unfold parenAt; have := tw_le (p := notParen) (seg a S E); rw [seg_length a hSE hE] at this; omega

/-- The word found is empty only when none is left. -/
theorem tok_empty {a : Bytes} {P E : Nat} (hPE : P ≤ E) (hE : E ≤ a.length) :
    wordEnd a (wordStart a P E) E - wordStart a P E = 0 ↔ wordStart a P E = E := by
  constructor
  · intro h
    refine Decidable.byContradiction fun hne => ?_
    have := wordEnd_gt hE (Nat.lt_of_le_of_ne (wordStart_le hPE hE) hne)
    omega
  · intro h; rw [h]; unfold wordEnd; rw [DN.News.ArticleLines.seg_self]; simp

/-! ## The lowering of `tokIn` -/

theorem spells_lower {o : Nat} (ho : 0 < o) : ∀ (cs : List Nat) (k0 : Nat) (acc : Syntax.PExpr),
    (Lower.lowerExp acc).isSome = true → (Lower.lowerExp ((cs.zipIdx k0).foldl (spellG o) acc)).isSome = true
  | [], _, _, h => h
  | c :: cs, k0, acc, h => by
    obtain ⟨Eacc, hacc⟩ := Option.isSome_iff_exists.1 h
    have hx : (o + k0 == 0) = false := by simp; omega
    have := spells_lower ho cs (k0 + 1) (spellG o acc (c, k0)) (by
      show (Lower.lowerExp (eAnd acc (eEq (lowerE (byte (Syntax.atOff (v "a") (o + k0)))) (n c)))).isSome = true
      rw [atOff_eq hx]; simp [Lower.lowerExp, hacc, lowerE, byte, eAnd, eEq, eAdd, eMul, eLe, n, v])
    simpa [List.zipIdx_cons] using this

theorem tokIn_lower : ∀ (names : List String) (k0 : Nat) (acc : Syntax.PExpr),
    (Lower.lowerExp acc).isSome = true → (Lower.lowerExp ((names.zipIdx k0).foldl tokF acc)).isSome = true
  | [], _, _, h => h
  | s :: names, k0, acc, h => by
    obtain ⟨Eacc, hacc⟩ := Option.isSome_iff_exists.1 h
    obtain ⟨Es, hEs⟩ := Option.isSome_iff_exists.1 (spells_lower (o := ArticleProg.xTok) (by rw [xTok_eq]; decide)
      (ArticleProg.codes (ArticleProg.lowerS s)) 0 (n 1) rfl)
    have hEs' : Lower.lowerExp (ArticleProg.spells ArticleProg.xTok (ArticleProg.lowerS s)) = some Es := hEs
    have hlen : Lower.lowerExp (wd ArticleProg.xTokLen) = some (.loadWord (.op .add (.var "a")
        (.const (BitVec.ofNat 64 ArticleProg.xTokLen)))) := wd_lower 20
    have := tokIn_lower names (k0 + 1) (tokF acc (s, k0)) (by
      show (Lower.lowerExp (eAdd acc (eMul (n (k0 + 1)) (eAnd (eEq (wd ArticleProg.xTokLen) (n s.length))
        (ArticleProg.spells ArticleProg.xTok (ArticleProg.lowerS s)))))).isSome = true
      simp only [eAdd, eMul, eAnd, eEq, n, Lower.lowerExp, hacc, hlen, hEs', Option.isSome_some])
    simpa [List.zipIdx_cons] using this

theorem tokIn_lowers (names : List String) : ∃ E, Lower.lowerExp (tokIn names) = some E := by
  rw [tokIn_def]; exact Option.isSome_iff_exists.1 (tokIn_lower names 0 (n 0) rfl)

theorem lowKK_tokIn (x : String) (names : List String) : LowKK [.assign x (tokIn names)] := by
  obtain ⟨E, hE⟩ := tokIn_lowers names
  exact lowKK_one rfl (a := .assign x E) (by simp only [Lower.lowerStmt1, hE])

theorem lowKK_tokDec (x : String) (names : List String) : LowKK [.dec x (tokIn names)] := by
  obtain ⟨E, hE⟩ := tokIn_lowers names
  exact lowKK_dec hE

/-- The day of the week's statements: the word before the comma, and no second. -/
def dayS : List Syntax.PStmt :=
  toksS "t1" (v "s") (v "cp") ++
    [.assign "wk" (tokIn ArticleSpec.dayNames), .assign "hw" (n 1),
     .call "t2" "artTok" [v "t1", v "cp"], brk, ifs (ne (wd ArticleProg.xTokLen) (n 0)) [.ret (n 0)],
     .assign "ts" (eAdd (v "cp") (n 1))]

theorem lowKK_dayS : LowKK dayS :=
  lowKK_append (lowK_any _ (k := .skip) rfl) (lowKK_append (xs := [_]) (lowKK_tokIn _ _) (lowK_any _ (k := .skip) rfl))

/-! ## A word read after `artTok` -/

theorem wordEnd_le {a : Bytes} {S E : Nat} (hSE : S ≤ E) (hE : E ≤ a.length) : wordEnd a S E ≤ E := by
  unfold wordEnd; have := tw_le (p := (!gap ·)) (seg a S E); rw [seg_length a hSE hE] at this; omega

theorem tokW_length {a : Bytes} {P E : Nat} (hPE : P ≤ E) (hE : E ≤ a.length) :
    (tokW a P E).length = wordEnd a (wordStart a P E) E - wordStart a P E :=
  seg_length a (Nat.le_add_right _ _) (Nat.le_trans (wordEnd_le (wordStart_le hPE hE) hE) hE)

/-- A scalar word of the article's read. -/
theorem wordAt_eval {A : Word} {s1 u : PancakeState σ} (hD : ArtDom A s1.memaddrs) {l : List (String × Value)}
    {M : Word → Word} (h : RunF s1 l (· = M) u) (hla : l.lookup "a" = some A) {i : Nat} (hi : i < 32) :
    eval u (.loadWord (.op .add (.var "a") (.const (BitVec.ofNat 64 (ArticleProg.w i))))) =
      some (M (at_ A (ArticleProg.w i))) := by
  rw [loadA_eval (y := ArticleProg.w i) h.1.memaddrs (artDom_w hD hi) (atA_eval (vals_lookup h.1.vals hla)), h.2]

/-- The length of the word found, in `xTokLen`. -/
theorem tokLen_eval {A : Word} {s1 u : PancakeState σ} (hD : ArtDom A s1.memaddrs) {l : List (String × Value)}
    {M : Word → Word} (h : RunF s1 l (· = M) u) (hla : l.lookup "a" = some A) :
    eval u (.loadWord (.op .add (.var "a") (.const (BitVec.ofNat 64 ArticleProg.xTokLen)))) =
      some (M (at_ A ArticleProg.xTokLen)) := wordAt_eval hD h hla (i := 20) (by decide)

/-- **`tokIn` read after `artTok`**: the word's place among the names, counted from one, or 0. -/
theorem tokIn_val {A : Word} {s1 : PancakeState σ} (hA8 : A.toNat % 8 = 0) (hD : ArtDom A s1.memaddrs) {a : Bytes}
    {P E : Nat} (hPE : P ≤ E) (hE : E ≤ a.length) (hEM : E ≤ artMax) {M0 : Word → Word}
    {l : List (String × Value)} (hla : l.lookup "a" = some A) {names : List String}
    (hn : names = dayNames ∨ names = monthNames) :
    ∃ Ex, Lower.lowerExp (tokIn names) = some Ex ∧ ∀ u, RunF s1 l (· = tokMem A s1.be a P E M0) u →
      eval u Ex = some (BitVec.ofNat 64 (((indexOf (tokW a P E) names 0).map (· + 1)).getD 0)) := by
  have hM := artMax_eq
  let tb : Nat → BitVec 8 := fun i =>
    (memLoadByte (tokMem A s1.be a P E M0) s1.memaddrs s1.be (at_ A (ArticleProg.xTok + i))).getD 0
  have htl := tokW_length hPE hE
  have hwe := wordEnd_le (wordStart_le hPE hE) hE
  obtain ⟨Ex, hEx, hEv⟩ := tokIn_fold (P := RunF s1 l (· = tokMem A s1.be a P E M0))
    (fun u h => vals_lookup h.1.vals hla)
    (L := (tokW a P E).length) (by omega) (fun u h => by rw [tokLen_eval hD h hla, tokMem_len, htl]) tb
    (fun i u hi h => by
      rw [h.2, h.1.memaddrs, h.1.be]
      simp only [tb, memLoadByte, tok_align hA8 hi, tok_dom hD, if_true, Option.getD_some])
    names 0 (n 0) (.const (BitVec.ofNat 64 0)) 0 rfl (fun _ _ => rfl) (by rcases hn with rfl | rfl <;> decide +kernel)
  refine ⟨Ex, hEx, fun u h => ?_⟩
  rw [hEv u h, Nat.zero_add, tokSum_names hn _ tb fun i hi3 hil => ?_]
  simp only [tb]
  rw [tokMem_byte hA8 (tok_dom hD) (by omega) hil, Option.getD_some, getElem!_pos _ i hil]

/-- Where the word from `P` before `E` starts and ends, and what `tokens` makes of the rest. -/
theorem tok_split {a : Bytes} {P E ws we : Nat} (hPE : P ≤ E) (hE : E ≤ a.length) (hws : wordStart a P E = ws)
    (hwe : wordEnd a ws E = we) : ws ≤ E ∧ we ≤ E ∧ ws ≤ we ∧ (we - ws = 0 ↔ ws = E) ∧
      tokens (seg a P E) = if ws = E then [] else seg a ws we :: tokens (seg a we E) := by
  have h1 := wordStart_le hPE hE
  rw [hws] at h1
  have h2 := wordEnd_le h1 hE
  rw [hwe] at h2
  have h3 : ws ≤ we := by rw [← hwe]; exact Nat.le_add_right _ _
  have h4 := tok_empty hPE hE
  rw [hws, hwe] at h4
  refine ⟨h1, h2, h3, h4, ?_⟩
  rw [tokens_next hPE hE, hws, hwe]

theorem indexOf_lt {w : Bytes} : ∀ {names : List String} {k i : Nat}, indexOf w names k = some i →
    i < k + names.length
  | [], _, _, h => by cases h
  | s :: names, k, i, h => by
    unfold indexOf at h
    split at h
    · cases h; simp
    · have := indexOf_lt h; simp only [List.length_cons]; omega

/-! ## A number read by `artNum` -/

/-- What `artNum` gives back for digits `o` read. -/
def numV : Option Nat → Value
  | some n => BitVec.ofNat 64 (min ArticleProg.yearBig n)
  | none => BitVec.ofNat 64 (2 ^ 64 - 1)

/-- The memory `artNum` leaves. -/
def numM (A : Word) (M : Word → Word) : Option Nat → Word → Word
  | some n => upd M (at_ A ArticleProg.xNumMod) (BitVec.ofNat 64 (n % 400))
  | none => M

theorem numM_frame (A : Word) (M : Word → Word) (o : Option Nat) : DFrame A M (numM A M o) := by
  cases o with
  | none => exact dframe_refl _ _
  | some k => exact dframe_upd (.inr (.inr (.inl rfl))) _

theorem mem_artNum : gd ArticleProg.artNum ∈
    ArticleProg.functions ArticleSpec.spec (ArticleProg.entries ArticleSpec.spec) .none :=
  List.mem_append_right _ (List.mem_map.2 ⟨ArticleProg.artNum, by simp, rfl⟩)

/-- **A call of `artNum`**, the check after it passed: the number the digits from `S` to `E` write, if any. -/
theorem numCall_frag (o : Oracle σ) {R : Ret} {A : Word} {s0 : PancakeState σ} (hA : Area ArticleProg.ofs A s0)
    (hD : ArtDom A s0.memaddrs) (hcode : ArtCode s0.code) {a : Bytes} (hlen : a.length ≤ artMax) {rt : String}
    (hra : rt ≠ "a") {l : List (String × Value)} (hla : l.lookup "a" = some A) (hrt : Fresh rt l = true)
    {m0 : Word → Word} (hin : InputAt m0 s0.memaddrs s0.be A a) (hb : m0 (at_ A aBroken) = 0) {e1 e2 : Syntax.PExpr}
    {E1 E2 : PancakeExp} (he1 : Lower.lowerExp e1 = some E1) (he2 : Lower.lowerExp e2 = some E2) {S E : Nat}
    (hS : S ≤ artMax) (hE : E ≤ a.length) (hv1 : ∀ u, RunF s0 l (· = m0) u → eval u E1 = some (BitVec.ofNat 64 S))
    (hv2 : ∀ u, RunF s0 l (· = m0) u → eval u E2 = some (BitVec.ofNat 64 E)) :
    FragR o R (guardS (.call rt "artNum" [e1, e2])) (RunF s0 l (· = m0))
      (RunF s0 ((rt, numV (number? (seg a S E))) :: l) (· = numM A m0 (number? (seg a S E)))) := by
  refine fragR_conseq (gcall_frag o hA hcode hra (f := ArticleProg.artNum) mem_artNum (by decide)
    (DN.News.AbnfGen.lowerArgs_two he1 he2) hla (vs := [BitVec.ofNat 64 S, BitVec.ofNat 64 E]) rfl
    (fun u h => by simp only [evalArgs, hv1 u h, hv2 u h]) (Rf := NumRet A a S E)
    (fun s1 hA1 _ hm hbe hloc hF => artNum_ok o hA1 (by rw [hm]; exact hD) hlen (by rw [hF, hm, hbe]; exact hin) hS hE
      ((hloc "s").trans rfl) ((hloc "e").trans rfl)) hrt
    (G := fun v m => m = numM A m0 (number? (seg a S E)) ∧ v = numV (number? (seg a S E)))
    (fun m m' v hm hr => by
      subst hm
      unfold NumRet at hr
      cases hn : number? (seg a S E) <;> rw [hn] at hr <;> exact ⟨hr.2, hr.1⟩)
    fun v m h => by rw [h.1, dframe_low (numM_frame _ _ _) DN.News.ArticleGrammar.broken_low]; exact hb) (fun u h => h)
    fun u ⟨v, h⟩ => ?_
  obtain ⟨hm, hv⟩ := h.2
  subst hv; exact ⟨h.1, hm⟩

/-- A number's test against 0, signed: below when the digits are none. -/
theorem numLt_eval {u : PancakeState σ} {x : String} {o : Option Nat} (h : u.locals x = some (numV o)) :
    eval u (.cmp .less (.var x) (.const (BitVec.ofNat 64 0))) = some (bw o.isNone) := by
  cases o with
  | none => simp only [eval, h]; rfl
  | some k =>
    rw [FramerCode.eval_lt (x := min ArticleProg.yearBig k) (y := 0)
      (by have := Nat.min_le_left ArticleProg.yearBig k; have : ArticleProg.yearBig = 100000 := rfl; omega)
      (by decide) (ev_var h) rfl]
    simp

/-! ## The front: the comment cut off, the day of the week read -/

/-- `artDate`'s statements up to the date's words. -/
def frontS : List Syntax.PStmt :=
  [areaAt ArticleProg.ofs, .dec "c" (v "s"), .dec "go" (n 1), .while (v "go") parenBody,
   .dec "nc" (n 0), .dec "cp" (n 0), .dec "i" (v "s"), .while (eLt (v "i") (v "c")) commaBody,
   ifs (eLt (n 1) (v "nc")) [.ret (n 0)],
   .dec "wk" (n 0), .dec "hw" (n 0), .dec "ts" (v "s"),
   ifs (eEq (v "nc") (n 1)) dayS]

/-- `artDate`'s state past its front. -/
structure FrontSt where
  nc : Nat
  cp : Nat
  ts : Nat
  hw : Nat
  wk : Nat
  m : Word → Word

/-- The locals past the front. -/
def frontL (S E : Nat) (A : Word) (C : Nat) (f : FrontSt) : List (String × Value) :=
  [("ts", BitVec.ofNat 64 f.ts), ("hw", BitVec.ofNat 64 f.hw), ("wk", BitVec.ofNat 64 f.wk)] ++
    commaL S E A C f.nc f.cp C

/-- What the front leaves: the words from `ts` on to read, and the day of the week if named. -/
def FrontOk (a : Bytes) (S E ts hw wk : Nat) : Prop :=
  S ≤ ts ∧ ts ≤ parenAt a S E ∧
    (hw = 0 ∧ wk = 0 ∧ ArticleSpec.dateValue (seg a S E) = dvRest none (tokens (seg a ts (parenAt a S E))) ∨
     hw = 1 ∧ ∃ name, wk = ((indexOf name dayNames 0).map (· + 1)).getD 0 ∧
       ArticleSpec.dateValue (seg a S E) = dvRest (some name) (tokens (seg a ts (parenAt a S E))))

/-- The date's front with no comma, or one. -/
theorem front_spec {a : Bytes} {S E nc cp : Nat} (hSE : S ≤ E) (hE : E ≤ a.length)
    (hci : CommaInv a S (parenAt a S E) nc cp (parenAt a S E)) :
    (2 ≤ nc → ArticleSpec.dateValue (seg a S E) = none) ∧
    (nc = 0 → ArticleSpec.dateValue (seg a S E) = dvRest none (tokens (seg a S (parenAt a S E)))) ∧
    (nc = 1 → (seg a S (parenAt a S E)).splitOn ArticleSpec.COMMA = [seg a S cp, seg a (cp + 1) (parenAt a S E)]) := by
  obtain ⟨-, -, hcnt, hcp⟩ := hci
  have htw := paren_tw a hSE hE
  refine ⟨fun h2 => ?_, fun h0 => ?_, fun h1 => ?_⟩
  · obtain ⟨x, y, z, r, hs⟩ := comma_many (l := seg a S (parenAt a S E)) (by rw [← hcnt]; exact h2)
    exact dv_commas (by rw [htw]; exact hs)
  · have hs := comma_none (l := seg a S (parenAt a S E)) (by rw [← hcnt]; exact h0)
    rw [dv_one (by rw [htw]; exact hs), htw]
  · rcases hcp with ⟨h0, -⟩ | ⟨-, hScp, hcpC, hc, hall⟩
    · omega
    have hC := paren_le a hSE hE
    have hsplit : seg a S (parenAt a S E) = seg a S cp ++ a[cp]! :: seg a (cp + 1) (parenAt a S E) := by
      rw [seg_app a hScp (Nat.le_of_lt hcpC), seg_cons a hcpC (by omega)]
    have hcnt' := hcnt
    rw [hsplit, List.filter_append, List.length_append, List.filter_cons] at hcnt'
    have hn1 : ((seg a S cp).filter isComma).length = 0 := by
      rw [List.length_eq_zero_iff, List.filter_eq_nil_iff]
      intro x hx; have := List.all_eq_true.1 hall x hx; simpa using this
    rw [hn1, if_pos hc, List.length_cons] at hcnt'
    rw [hsplit]
    exact comma_one hall hc (by omega)

/-- What the front ends in. -/
def FrontPost (s1 : PancakeState σ) (A : Word) (a : Bytes) (S E : Nat) : Assn σ := fun u =>
  ∃ f : FrontSt, RunF s1 (frontL S E A (parenAt a S E) f) (· = f.m) u ∧ DFrame A s1.memory f.m ∧
    FrontOk a S E f.ts f.hw f.wk

theorem frontPost_clock {s1 : PancakeState σ} {A : Word} {a : Bytes} {S E : Nat} :
    Safe.ClockFree (FrontPost s1 A a S E) :=
  fun u k ⟨f, h, h1, h2⟩ => ⟨f, runF_clock _ _ _ u k h, h1, h2⟩

/-- **The front**: the comment cut off, the commas counted, the day of the week read if one is named. -/
theorem front_frag (o : Oracle σ) {A : Word} {s1 : PancakeState σ} (hA : Area ArticleProg.ofs A s1)
    (hD : ArtDom A s1.memaddrs) (hcode : ArtCode s1.code) {a : Bytes} (hlen : a.length ≤ artMax)
    (hin : InputAt s1.memory s1.memaddrs s1.be A a) (hb : s1.memory (at_ A aBroken) = 0) {S E : Nat} (hSE : S ≤ E)
    (hE : E ≤ a.length) :
    FragR o (DateRet A a S E s1.memory) frontS
      (RunF s1 [("s", BitVec.ofNat 64 S), ("e", BitVec.ofNat 64 E)] (· = s1.memory)) (FrontPost s1 A a S E) := by
  have hM := artMax_eq
  have hEM : E ≤ artMax := by omega
  have hCE := paren_le a hSE hE
  have hSC : S ≤ parenAt a S E := Nat.le_add_right _ _
  obtain ⟨EA, hEA⟩ := atOff_lower ArticleProg.ofs
  refine fragR_append (xs := [_]) (fragR_of (runF_dec o hEA rfl (v := A) fun u h => areaAt_eval hA h.1.base hEA)) ?_
  refine fragR_append (xs := [_]) (fragR_of (runF_dec o rfl rfl (v := BitVec.ofNat 64 S) fun u h =>
    ev_var (vals_lookup h.1.vals rfl))) ?_
  refine fragR_append (xs := [_]) (fragR_of (runF_dec o rfl rfl (v := BitVec.ofNat 64 1) fun _ _ => rfl)) ?_
  refine fragR_append (xs := [_]) (fragR_of (paren_loop o hin hSE hE hEM)) ?_
  refine fragR_append (xs := [_]) (fragR_of (runF_dec o rfl rfl (v := BitVec.ofNat 64 0) fun _ _ => rfl)) ?_
  refine fragR_append (xs := [_]) (fragR_of (runF_dec o rfl rfl (v := BitVec.ofNat 64 0) fun _ _ => rfl)) ?_
  refine fragR_append (xs := [_]) (fragR_of (runF_dec o rfl rfl (v := BitVec.ofNat 64 S) fun u h =>
    ev_var (vals_lookup h.1.vals rfl))) ?_
  refine fragR_append (xs := [_]) (fragR_of (comma_loop o hin hSC hCE hE hEM)) ?_
  have hR2 : LowKK [.dec "wk" (n 0), .dec "hw" (n 0), .dec "ts" (v "s"), ifs (eEq (v "nc") (n 1)) dayS] :=
    lowKK_append (xs := [_, _, _]) (lowK_any _ (k := .skip) rfl) (lowKK_ite rfl lowKK_dayS lowKK_nil)
  have hR1 := lowKK_append (xs := [ifs (eLt (n 1) (v "nc")) [.ret (n 0)]]) (lowK_any _ (k := .skip) rfl) hR2
  refine fragR_exists hR1 fun nc => fragR_exists hR1 fun cp => ?_
  refine fragR_pure (CommaInv a S (parenAt a S E) nc cp (parenAt a S E)) (fun u h => h.2) hR1 fun hci => ?_
  refine fragR_conseq (P0 := RunF s1 (commaL S E A (parenAt a S E) nc cp (parenAt a S E)) (· = s1.memory)) ?_
    (fun u h => h.1) fun _ h => h
  obtain ⟨sp2, sp0, sp1⟩ := front_spec hSE hE hci
  have hnc : nc ≤ parenAt a S E - S := by
    have := List.length_filter_le isComma (seg a S (parenAt a S E))
    rw [seg_length a hSC (by omega)] at this; rw [hci.2.2.1]; omega
  refine fragR_append (xs := [_]) (ret0_frag o rfl (runF_clock _ _ _) (b := decide (1 < nc))
    (fun u h => FramerCode.eval_lt (by decide) (by omega) rfl (ev_var (vals_lookup h.1.vals rfl)))
    fun hb u h => ⟨by rw [h.2]; exact dframe_refl _ _, .inl ⟨rfl, sp2 (of_decide_eq_true hb)⟩⟩) ?_
  refine fragR_pure (nc ≤ 1) (fun u h => by have := h.2; simp at this; omega) hR2 fun hn1 => ?_
  refine fragR_conseq (P0 := RunF s1 (commaL S E A (parenAt a S E) nc cp (parenAt a S E)) (· = s1.memory)) ?_
    (fun u h => h.1) fun _ h => h
  refine fragR_append (xs := [_]) (fragR_of (runF_dec o rfl rfl (v := BitVec.ofNat 64 0) fun _ _ => rfl)) ?_
  refine fragR_append (xs := [_]) (fragR_of (runF_dec o rfl rfl (v := BitVec.ofNat 64 0) fun _ _ => rfl)) ?_
  refine fragR_append (xs := [_]) (fragR_of (runF_dec o rfl rfl (v := BitVec.ofNat 64 S) fun u h =>
    ev_var (vals_lookup h.1.vals rfl))) ?_
  refine fragR_if o rfl lowKK_dayS lowKK_nil frontPost_clock
    (fun u y w ⟨f, h, h1, h2⟩ hy => ⟨f, runF_restore h (by
      change y ∈ ["t1", "t2"] at hy
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
      rcases hy with rfl | rfl <;> rfl) w, h1, h2⟩) (noDecl _ rfl) (b := decide (nc = 1))
    (fun u h => FramerCode.eval_eq (by omega) (by decide) (ev_var (vals_lookup h.1.vals rfl)) rfl) (fun h1 => ?_)
    fun h0 => fragR_of (frag_nil o fun u h => ⟨⟨nc, cp, S, 0, 0, s1.memory⟩, runF_of h (by
      repeat (refine lookups_cons rfl ?_)
      exact lookups_nil), dframe_refl _ _, Nat.le_refl _, hSC, .inl ⟨rfl, rfl, sp0 (by
        have := of_decide_eq_false h0; omega)⟩⟩)
  have hnc1 : nc = 1 := of_decide_eq_true h1
  have hsp := sp1 hnc1
  have htw := paren_tw a hSE hE
  obtain ⟨-, -, -, hcp⟩ := hci
  rcases hcp with ⟨h0, -⟩ | ⟨-, hScp, hcpC, -, -⟩
  · omega
  have hcpa : cp ≤ a.length := by omega
  have hA8 := hA.hA
  -- the day of the week's word
  obtain ⟨ws1, hws1⟩ : ∃ x, wordStart a S cp = x := ⟨_, rfl⟩
  obtain ⟨we1, hwe1⟩ : ∃ x, wordEnd a ws1 cp = x := ⟨_, rfl⟩
  obtain ⟨-, h1b, -, h1d, htok1⟩ := tok_split hScp hcpa hws1 hwe1
  have hf1 := tokMem_frame hA8 s1.be a S cp s1.memory
  have hM1L : tokMem A s1.be a S cp s1.memory (at_ A ArticleProg.xTokLen) = BitVec.ofNat 64 (we1 - ws1) := by
    rw [tokMem_len, hws1, hwe1]
  refine fragR_append (xs := [_, _]) (tokCall_frag o hA hD hcode hlen (rt := "t1") (by decide) rfl rfl hin hb hScp hcpa
    hws1 hwe1 rfl rfl) ?_
  refine fragR_append (xs := [_]) (ret0_frag o rfl (runF_clock _ _ _) (b := decide (we1 - ws1 = 0))
    (fun u h => FramerCode.eval_eq (by omega) (by decide) (by rw [tokLen_eval hD h rfl, hM1L]) rfl)
    fun hb0 u h => ⟨by rw [h.2]; exact hf1, .inl ⟨rfl, dv_two_bad (by rw [htw]; exact hsp) fun name => by
      rw [htok1, if_pos (h1d.1 (of_decide_eq_true hb0))]; intro e; cases e⟩⟩) ?_
  have hL3 := lowKK_drop 3 lowKK_dayS
  refine fragR_pure (we1 - ws1 ≠ 0) (fun u h => by have := h.2; simpa using this) hL3 fun hl1 => ?_
  have hw1 : ws1 ≠ cp := fun e => hl1 (h1d.2 e)
  refine fragR_conseq (P0 := RunF s1 (("t1", BitVec.ofNat 64 we1) :: ("ts", BitVec.ofNat 64 S) ::
    ("hw", BitVec.ofNat 64 0) :: ("wk", BitVec.ofNat 64 0) :: commaL S E A (parenAt a S E) nc cp (parenAt a S E))
    (· = tokMem A s1.be a S cp s1.memory)) ?_ (fun u h => h.1) fun _ h => h
  obtain ⟨wk1, hwk1⟩ : ∃ x, ((indexOf (seg a ws1 we1) dayNames 0).map (· + 1)).getD 0 = x := ⟨_, rfl⟩
  obtain ⟨Ex, hEx, hEv⟩ := tokIn_val hA8 hD hScp hcpa (by omega) (M0 := s1.memory)
    (l := ("t1", BitVec.ofNat 64 we1) :: ("ts", BitVec.ofNat 64 S) :: ("hw", BitVec.ofNat 64 0) ::
      ("wk", BitVec.ofNat 64 0) :: commaL S E A (parenAt a S E) nc cp (parenAt a S E)) rfl (names := dayNames)
    (.inl rfl)
  refine fragR_append (xs := [_]) (fragR_of (set_to o hEx rfl (v := BitVec.ofNat 64 wk1)
    (fun u h => by rw [hEv u h, ← hwk1]; simp only [tokW, hws1, hwe1])
    (l' := ("t1", BitVec.ofNat 64 we1) :: ("ts", BitVec.ofNat 64 S) :: ("hw", BitVec.ofNat 64 0) ::
      ("wk", BitVec.ofNat 64 wk1) :: commaL S E A (parenAt a S E) nc cp (parenAt a S E))
    fun u h => runF_of h (by
      repeat (refine lookups_cons rfl ?_)
      exact lookups_nil))) ?_
  refine fragR_append (xs := [_]) (fragR_of (set_to o rfl rfl (v := BitVec.ofNat 64 1) (fun _ _ => rfl)
    (l' := ("t1", BitVec.ofNat 64 we1) :: ("ts", BitVec.ofNat 64 S) :: ("hw", BitVec.ofNat 64 1) ::
      ("wk", BitVec.ofNat 64 wk1) :: commaL S E A (parenAt a S E) nc cp (parenAt a S E))
    fun u h => runF_of h (by
      repeat (refine lookups_cons rfl ?_)
      exact lookups_nil))) ?_
  generalize tokMem A s1.be a S cp s1.memory = M1 at hf1 ⊢
  -- no second word before the comma
  obtain ⟨ws2, hws2⟩ : ∃ x, wordStart a we1 cp = x := ⟨_, rfl⟩
  obtain ⟨we2, hwe2⟩ : ∃ x, wordEnd a ws2 cp = x := ⟨_, rfl⟩
  obtain ⟨h2a, h2b, -, h2d, htok2⟩ := tok_split h1b hcpa hws2 hwe2
  have hf2 := tokMem_frame hA8 s1.be a we1 cp M1
  have hM2L : tokMem A s1.be a we1 cp M1 (at_ A ArticleProg.xTokLen) = BitVec.ofNat 64 (we2 - ws2) := by
    rw [tokMem_len, hws2, hwe2]
  refine fragR_append (xs := [_, _]) (tokCall_frag o hA hD hcode hlen (rt := "t2") (by decide) rfl rfl
    (dframe_input hA8 hlen hin hf1) (by rw [dframe_low hf1 DN.News.ArticleGrammar.broken_low]; exact hb) h1b hcpa
      hws2 hwe2 rfl rfl) ?_
  refine fragR_append (xs := [_]) (ret0_frag o rfl (runF_clock _ _ _) (b := decide (we2 - ws2 ≠ 0))
    (fun u h => by
      rw [DN.News.AbnfLeaves.ne_eval (tokLen_eval hD h rfl) rfl, hM2L, ofNat_ne_iff (by omega) (by decide)])
    fun hb2 u h => ⟨by rw [h.2]; exact dframe_trans hf1 hf2, .inl ⟨rfl, dv_two_bad (by rw [htw]; exact hsp)
      fun name => by
        rw [htok1, if_neg hw1, htok2, if_neg fun e => of_decide_eq_true hb2 (h2d.2 e)]; intro e; cases e⟩⟩) ?_
  refine fragR_pure (we2 - ws2 = 0) (fun u h => by have := h.2; simpa using this) (lowK_any _ (k := .skip) rfl)
    fun hl2 => ?_
  refine fragR_of (frag_conseq (set_to o rfl rfl (v := BitVec.ofNat 64 (cp + 1))
    (fun u h => ev_inc (vals_lookup h.1.vals rfl)) fun u h => h) (fun u h => h.1) fun u h => ?_)
  refine ⟨⟨nc, cp, cp + 1, 1, wk1, tokMem A s1.be a we1 cp M1⟩, runF_of h (by
      repeat (refine lookups_cons rfl ?_)
      exact lookups_nil), dframe_trans hf1 hf2, by show S ≤ cp + 1; omega,
    by show cp + 1 ≤ parenAt a S E; omega, .inr ⟨rfl, seg a ws1 we1, hwk1.symm, ?_⟩⟩
  refine dv_two_name (by rw [htw]; exact hsp) ?_
  rw [htok1, if_neg hw1, htok2, if_pos (h2d.1 hl2)]

/-! ## The date's three words and their numbers -/

/-- `artDate`'s statements over the date's words. -/
def wordsS : List Syntax.PStmt :=
  toksS "p1" (v "ts") (v "c") ++ [.dec "ds" (wd ArticleProg.xTokS)] ++
    toksS "p2" (v "p1") (v "c") ++ [.dec "mo" (tokIn ArticleSpec.monthNames)] ++
    toksS "p3" (v "p2") (v "c") ++
    [.dec "ys" (wd ArticleProg.xTokS),
     .call "dy" "artNum" [v "ds", v "p1"], brk, ifs (eLt (v "dy") (n 0)) [.ret (n 0)],
     ifs (eEq (v "mo") (n 0)) [.ret (n 0)],
     .call "yr" "artNum" [v "ys", v "p3"], brk, ifs (eLt (v "yr") (n 0)) [.ret (n 0)],
     .dec "y4" (wd ArticleProg.xNumMod),
     ifs (eAnd (n 0) (eLe (n ArticleProg.yearBig) (v "yr"))) [.assign "y4" (n 0)]]

/-- `artDate`'s state past the date's words. -/
structure WordsSt where
  p1 : Nat
  ds : Nat
  p2 : Nat
  mo : Nat
  p3 : Nat
  ys : Nat
  day : Nat
  year : Nat
  m : Word → Word

/-- The locals the words add. -/
def wordsL (g : WordsSt) : List (String × Value) :=
  [("y4", BitVec.ofNat 64 (g.year % 400)), ("yr", BitVec.ofNat 64 (min ArticleProg.yearBig g.year)),
   ("dy", BitVec.ofNat 64 (min ArticleProg.yearBig g.day)), ("ys", BitVec.ofNat 64 g.ys), ("p3", BitVec.ofNat 64 g.p3),
   ("mo", BitVec.ofNat 64 g.mo), ("p2", BitVec.ofNat 64 g.p2), ("ds", BitVec.ofNat 64 g.ds),
   ("p1", BitVec.ofNat 64 g.p1)]

/-- What the words leave: the day, month and year read, the rest from `p3` on to read. -/
def WordsOk (a : Bytes) (S E C : Nat) (f : FrontSt) (g : WordsSt) : Prop :=
  g.p3 ≤ C ∧ 1 ≤ g.mo ∧ g.mo ≤ 12 ∧
  ∃ (W : Option Bytes) (d mth y : Bytes),
    (W = none ∧ f.hw = 0 ∨ ∃ name, W = some name ∧ f.hw = 1 ∧ f.wk = ((indexOf name dayNames 0).map (· + 1)).getD 0) ∧
    number? d = some g.day ∧ indexOf mth monthNames 0 = some (g.mo - 1) ∧ number? y = some g.year ∧
    ArticleSpec.dateValue (seg a S E) = dvC W d mth y ((seg a g.p3 C).filter (fun b => !gap b))

/-- What the words end in. -/
def WordsPost (s1 : PancakeState σ) (A : Word) (a : Bytes) (S E C : Nat) (f : FrontSt) : Assn σ := fun u =>
  ∃ g : WordsSt, RunF s1 (wordsL g ++ frontL S E A C f) (· = g.m) u ∧ DFrame A s1.memory g.m ∧ WordsOk a S E C f g

theorem wordsPost_clock {s1 : PancakeState σ} {A : Word} {a : Bytes} {S E C : Nat} {f : FrontSt} :
    Safe.ClockFree (WordsPost s1 A a S E C f) :=
  fun u k ⟨g, h, h1, h2⟩ => ⟨g, runF_clock _ _ _ u k h, h1, h2⟩

theorem lowKK_wordsS : LowKK wordsS :=
  lowKK_append (lowKK_append (lowKK_append (lowK_any _ (k := .skip) rfl) (lowKK_tokDec _ _))
    (lowK_any _ (k := .skip) rfl)) (lowK_any _ (k := .skip) rfl)

/-- **The date's three words**: the day's and the year's numbers, the month's place. -/
theorem words_frag (o : Oracle σ) {A : Word} {s1 : PancakeState σ} (hA : Area ArticleProg.ofs A s1)
    (hD : ArtDom A s1.memaddrs) (hcode : ArtCode s1.code) {a : Bytes} (hlen : a.length ≤ artMax)
    (hin : InputAt s1.memory s1.memaddrs s1.be A a) (hb : s1.memory (at_ A aBroken) = 0) {S E C : Nat}
    (hCa : C ≤ a.length) (f : FrontSt) (hf : DFrame A s1.memory f.m) (hTC : f.ts ≤ C) {W : Option Bytes}
    (hWr : W = none ∧ f.hw = 0 ∨ ∃ name, W = some name ∧ f.hw = 1 ∧
      f.wk = ((indexOf name dayNames 0).map (· + 1)).getD 0)
    (hdv : ArticleSpec.dateValue (seg a S E) = dvRest W (tokens (seg a f.ts C))) :
    FragR o (DateRet A a S E s1.memory) wordsS (RunF s1 (frontL S E A C f) (· = f.m)) (WordsPost s1 A a S E C f) := by
  have hM := artMax_eq
  have hA8 := hA.hA
  have hW := lowKK_wordsS
  -- the first word
  obtain ⟨ws1, hws1⟩ : ∃ x, wordStart a f.ts C = x := ⟨_, rfl⟩
  obtain ⟨p1, hp1⟩ : ∃ x, wordEnd a ws1 C = x := ⟨_, rfl⟩
  obtain ⟨h1a, h1b, h1c, h1d, htok1⟩ := tok_split hTC hCa hws1 hp1
  have hf1 := tokMem_frame hA8 s1.be a f.ts C f.m
  have hM1S : tokMem A s1.be a f.ts C f.m (at_ A ArticleProg.xTokS) = BitVec.ofNat 64 ws1 := by
    rw [tokMem_start hA8, hws1]
  have hM1L : tokMem A s1.be a f.ts C f.m (at_ A ArticleProg.xTokLen) = BitVec.ofNat 64 (p1 - ws1) := by
    rw [tokMem_len, hws1, hp1]
  refine fragR_append (xs := [_, _]) (tokCall_frag o hA hD hcode hlen (rt := "p1") (by decide) rfl rfl
    (dframe_input hA8 hlen hin hf) (by rw [dframe_low hf DN.News.ArticleGrammar.broken_low]; exact hb) hTC hCa
      hws1 hp1 rfl rfl) ?_
  generalize tokMem A s1.be a f.ts C f.m = M1 at hf1 hM1S hM1L ⊢
  have hf1' := dframe_trans hf hf1
  refine fragR_append (xs := [_]) (ret0_frag o rfl (runF_clock _ _ _) (b := decide (p1 - ws1 = 0))
    (fun u h => FramerCode.eval_eq (by omega) (by decide) (by rw [tokLen_eval hD h rfl, hM1L]) rfl)
    fun hb0 u h => ⟨by rw [h.2]; exact hf1', .inl ⟨rfl, by
      rw [hdv, htok1, if_pos (h1d.1 (of_decide_eq_true hb0))]; exact dvRest_short (by simp)⟩⟩) ?_
  refine fragR_pure (p1 - ws1 ≠ 0) (fun u h => by have := h.2; simpa using this) (lowKK_drop 3 hW) fun hl1 => ?_
  refine fragR_conseq (P0 := RunF s1 (("p1", BitVec.ofNat 64 p1) :: frontL S E A C f) (· = M1)) ?_
    (fun u h => h.1) fun _ h => h
  have hw1C : ws1 ≠ C := fun e => hl1 (h1d.2 e)
  refine fragR_append (xs := [_]) (fragR_of (runF_dec o (wd_lower 19) rfl (v := BitVec.ofNat 64 ws1) fun u h => by
    rw [wordAt_eval hD h rfl (i := 19) (by decide)]; exact congrArg some hM1S)) ?_
  -- the second word, the month
  obtain ⟨ws2, hws2⟩ : ∃ x, wordStart a p1 C = x := ⟨_, rfl⟩
  obtain ⟨p2, hp2⟩ : ∃ x, wordEnd a ws2 C = x := ⟨_, rfl⟩
  obtain ⟨h2a, h2b, h2c, h2d, htok2⟩ := tok_split h1b hCa hws2 hp2
  have hf2 := tokMem_frame hA8 s1.be a p1 C M1
  have hM2L : tokMem A s1.be a p1 C M1 (at_ A ArticleProg.xTokLen) = BitVec.ofNat 64 (p2 - ws2) := by
    rw [tokMem_len, hws2, hp2]
  refine fragR_append (xs := [_, _]) (tokCall_frag o hA hD hcode hlen (rt := "p2") (by decide) rfl rfl
    (dframe_input hA8 hlen hin hf1') (by rw [dframe_low hf1' DN.News.ArticleGrammar.broken_low]; exact hb) h1b hCa
      hws2 hp2 rfl rfl) ?_
  have hf2' := dframe_trans hf1' hf2
  refine fragR_append (xs := [_]) (ret0_frag o rfl (runF_clock _ _ _) (b := decide (p2 - ws2 = 0))
    (fun u h => FramerCode.eval_eq (by omega) (by decide) (by rw [tokLen_eval hD h rfl, hM2L]) rfl)
    fun hb0 u h => ⟨by rw [h.2]; exact hf2', .inl ⟨rfl, by
      rw [hdv, htok1, if_neg hw1C, htok2, if_pos (h2d.1 (of_decide_eq_true hb0))]
      exact dvRest_short (by simp)⟩⟩) ?_
  refine fragR_pure (p2 - ws2 ≠ 0) (fun u h => by have := h.2; simpa using this) (lowKK_drop 7 hW) fun hl2 => ?_
  have hw2C : ws2 ≠ C := fun e => hl2 (h2d.2 e)
  refine fragR_conseq (P0 := RunF s1 (("p2", BitVec.ofNat 64 p2) :: ("ds", BitVec.ofNat 64 ws1) ::
    ("p1", BitVec.ofNat 64 p1) :: frontL S E A C f) (· = tokMem A s1.be a p1 C M1)) ?_ (fun u h => h.1) fun _ h => h
  obtain ⟨mo, hmo⟩ : ∃ x, ((indexOf (seg a ws2 p2) monthNames 0).map (· + 1)).getD 0 = x := ⟨_, rfl⟩
  obtain ⟨Ex, hEx, hEv⟩ := tokIn_val hA8 hD h1b hCa (by omega) (M0 := M1)
    (l := ("p2", BitVec.ofNat 64 p2) :: ("ds", BitVec.ofNat 64 ws1) :: ("p1", BitVec.ofNat 64 p1) ::
      frontL S E A C f) rfl (names := monthNames) (.inr rfl)
  refine fragR_append (xs := [_]) (fragR_of (runF_dec o hEx rfl (v := BitVec.ofNat 64 mo) fun u h => by
    rw [hEv u h, ← hmo]; simp only [tokW, hws2, hp2])) ?_
  generalize tokMem A s1.be a p1 C M1 = M2 at hf2 hf2' ⊢
  -- the third word
  obtain ⟨ws3, hws3⟩ : ∃ x, wordStart a p2 C = x := ⟨_, rfl⟩
  obtain ⟨p3, hp3⟩ : ∃ x, wordEnd a ws3 C = x := ⟨_, rfl⟩
  obtain ⟨h3a, h3b, h3c, h3d, htok3⟩ := tok_split h2b hCa hws3 hp3
  have hf3 := tokMem_frame hA8 s1.be a p2 C M2
  have hM3S : tokMem A s1.be a p2 C M2 (at_ A ArticleProg.xTokS) = BitVec.ofNat 64 ws3 := by
    rw [tokMem_start hA8, hws3]
  have hM3L : tokMem A s1.be a p2 C M2 (at_ A ArticleProg.xTokLen) = BitVec.ofNat 64 (p3 - ws3) := by
    rw [tokMem_len, hws3, hp3]
  refine fragR_append (xs := [_, _]) (tokCall_frag o hA hD hcode hlen (rt := "p3") (by decide) rfl rfl
    (dframe_input hA8 hlen hin hf2') (by rw [dframe_low hf2' DN.News.ArticleGrammar.broken_low]; exact hb) h2b hCa
      hws3 hp3 rfl rfl) ?_
  generalize tokMem A s1.be a p2 C M2 = M3 at hf3 hM3S hM3L ⊢
  have hf3' := dframe_trans hf2' hf3
  refine fragR_append (xs := [_]) (ret0_frag o rfl (runF_clock _ _ _) (b := decide (p3 - ws3 = 0))
    (fun u h => FramerCode.eval_eq (by omega) (by decide) (by rw [tokLen_eval hD h rfl, hM3L]) rfl)
    fun hb0 u h => ⟨by rw [h.2]; exact hf3', .inl ⟨rfl, by
      rw [hdv, htok1, if_neg hw1C, htok2, if_neg hw2C, htok3, if_pos (h3d.1 (of_decide_eq_true hb0))]
      exact dvRest_short (by simp)⟩⟩) ?_
  refine fragR_pure (p3 - ws3 ≠ 0) (fun u h => by have := h.2; simpa using this) (lowKK_drop 11 hW) fun hl3 => ?_
  have hw3C : ws3 ≠ C := fun e => hl3 (h3d.2 e)
  refine fragR_conseq (P0 := RunF s1 (("p3", BitVec.ofNat 64 p3) :: ("mo", BitVec.ofNat 64 mo) ::
    ("p2", BitVec.ofNat 64 p2) :: ("ds", BitVec.ofNat 64 ws1) :: ("p1", BitVec.ofNat 64 p1) :: frontL S E A C f)
    (· = M3)) ?_ (fun u h => h.1) fun _ h => h
  refine fragR_append (xs := [_]) (fragR_of (runF_dec o (wd_lower 19) rfl (v := BitVec.ofNat 64 ws3) fun u h => by
    rw [wordAt_eval hD h rfl (i := 19) (by decide)]; exact congrArg some hM3S)) ?_
  have hdv' : ArticleSpec.dateValue (seg a S E) =
      dvC W (seg a ws1 p1) (seg a ws2 p2) (seg a ws3 p3) ((seg a p3 C).filter (fun b => !gap b)) := by
    rw [hdv, htok1, if_neg hw1C, htok2, if_neg hw2C, htok3, if_neg hw3C, dvRest_cons, tokens_flatten]
  have hmo' : (mo = 0 ∧ indexOf (seg a ws2 p2) monthNames 0 = none) ∨
      (1 ≤ mo ∧ mo ≤ 12 ∧ indexOf (seg a ws2 p2) monthNames 0 = some (mo - 1)) := by
    rw [← hmo]
    cases hi : indexOf (seg a ws2 p2) monthNames 0 with
    | none => exact .inl ⟨rfl, rfl⟩
    | some i =>
      have := indexOf_lt hi
      have hl : monthNames.length = 12 := rfl
      simp only [Option.map_some, Option.getD_some]
      exact .inr ⟨by omega, by omega, by simp⟩
  have hmo12 : mo ≤ 12 := by rcases hmo' with ⟨h, -⟩ | ⟨-, h, -⟩ <;> omega
  -- the day's number
  have hin3 := dframe_input hA8 hlen hin hf3'
  have hb3 : M3 (at_ A aBroken) = 0 := by rw [dframe_low hf3' DN.News.ArticleGrammar.broken_low]; exact hb
  refine fragR_append (xs := [_, _]) (numCall_frag o hA hD hcode hlen (rt := "dy") (by decide) rfl rfl hin3 hb3 rfl rfl
    (S := ws1) (E := p1) (by omega) (by omega) (fun u h => ev_var (vals_lookup h.1.vals rfl))
    fun u h => ev_var (vals_lookup h.1.vals rfl)) ?_
  rcases hd1 : number? (seg a ws1 p1) with _ | day
  · refine fragR_append (xs := [_]) (ret0_frag o rfl (runF_clock _ _ _) (b := true)
      (fun u h => numLt_eval (o := none) (vals_lookup h.1.vals rfl)) fun _ u h => ⟨by
        rw [h.2]; exact dframe_trans hf3' (numM_frame _ _ _), .inl ⟨rfl, by rw [hdv']; exact dvC_none (.inl hd1)⟩⟩) ?_
    exact fragR_of (frag_unsat (lowKK_drop 15 hW) fun u h => absurd h.2 (by decide))
  refine fragR_append (xs := [_]) (ret0_frag o rfl (runF_clock _ _ _) (b := false)
    (fun u h => numLt_eval (o := some day) (vals_lookup h.1.vals rfl)) fun hb => absurd hb (by decide)) ?_
  refine fragR_conseq (P0 := RunF s1 (("dy", numV (some day)) :: ("ys", BitVec.ofNat 64 ws3) ::
    ("p3", BitVec.ofNat 64 p3) :: ("mo", BitVec.ofNat 64 mo) :: ("p2", BitVec.ofNat 64 p2) ::
    ("ds", BitVec.ofNat 64 ws1) :: ("p1", BitVec.ofNat 64 p1) :: frontL S E A C f) (· = numM A M3 (some day))) ?_
    (fun u h => h.1) fun _ h => h
  -- the month's place
  refine fragR_append (xs := [_]) (ret0_frag o rfl (runF_clock _ _ _) (b := decide (mo = 0))
    (fun u h => FramerCode.eval_eq (by omega) (by decide) (ev_var (vals_lookup h.1.vals rfl)) rfl)
    fun hb0 u h => ⟨by rw [h.2]; exact dframe_trans hf3' (numM_frame _ _ _), .inl ⟨rfl, by
      rw [hdv']; refine dvC_none (.inr (.inl ?_))
      rcases hmo' with ⟨-, h⟩ | ⟨h, -⟩
      · exact h
      · have := of_decide_eq_true hb0; omega⟩⟩) ?_
  refine fragR_pure (mo ≠ 0) (fun u h => by have := h.2; simpa using this) (lowKK_drop 16 hW) fun hm0 => ?_
  obtain ⟨hmo1, -, hmoi⟩ : 1 ≤ mo ∧ mo ≤ 12 ∧ indexOf (seg a ws2 p2) monthNames 0 = some (mo - 1) := by
    rcases hmo' with ⟨h, -⟩ | h
    · exact absurd h hm0
    · exact h
  refine fragR_conseq (P0 := RunF s1 (("dy", numV (some day)) :: ("ys", BitVec.ofNat 64 ws3) ::
    ("p3", BitVec.ofNat 64 p3) :: ("mo", BitVec.ofNat 64 mo) :: ("p2", BitVec.ofNat 64 p2) ::
    ("ds", BitVec.ofNat 64 ws1) :: ("p1", BitVec.ofNat 64 p1) :: frontL S E A C f) (· = numM A M3 (some day))) ?_
    (fun u h => h.1) fun _ h => h
  -- the year's number
  have hf4 := dframe_trans hf3' (numM_frame A M3 (some day))
  refine fragR_append (xs := [_, _]) (numCall_frag o hA hD hcode hlen (rt := "yr") (by decide) rfl rfl
    (dframe_input hA8 hlen hin hf4) (by rw [dframe_low hf4 DN.News.ArticleGrammar.broken_low]; exact hb) rfl rfl
    (S := ws3) (E := p3) (by omega) (by omega) (fun u h => ev_var (vals_lookup h.1.vals rfl))
    fun u h => ev_var (vals_lookup h.1.vals rfl)) ?_
  rcases hd3 : number? (seg a ws3 p3) with _ | year
  · refine fragR_append (xs := [_]) (ret0_frag o rfl (runF_clock _ _ _) (b := true)
      (fun u h => numLt_eval (o := none) (vals_lookup h.1.vals rfl)) fun _ u h => ⟨by
        rw [h.2]; exact dframe_trans hf4 (numM_frame _ _ _), .inl ⟨rfl, by
          rw [hdv']; exact dvC_none (.inr (.inr (.inl hd3)))⟩⟩) ?_
    exact fragR_of (frag_unsat (lowKK_drop 19 hW) fun u h => absurd h.2 (by decide))
  refine fragR_append (xs := [_]) (ret0_frag o rfl (runF_clock _ _ _) (b := false)
    (fun u h => numLt_eval (o := some year) (vals_lookup h.1.vals rfl)) fun hb => absurd hb (by decide)) ?_
  have hf5 := dframe_trans hf4 (numM_frame A (numM A M3 (some day)) (some year))
  refine fragR_conseq (P0 := RunF s1 (("yr", numV (some year)) :: ("dy", numV (some day)) ::
    ("ys", BitVec.ofNat 64 ws3) :: ("p3", BitVec.ofNat 64 p3) :: ("mo", BitVec.ofNat 64 mo) ::
    ("p2", BitVec.ofNat 64 p2) :: ("ds", BitVec.ofNat 64 ws1) :: ("p1", BitVec.ofNat 64 p1) :: frontL S E A C f)
    (· = numM A (numM A M3 (some day)) (some year))) ?_ (fun u h => h.1) fun _ h => h
  refine fragR_append (xs := [_]) (fragR_of (runF_dec o (wd_lower 25) rfl (v := BitVec.ofNat 64 (year % 400))
    fun u h => by rw [wordAt_eval hD h rfl (i := 25) (by decide)]; exact congrArg some (upd_eq _ _ _))) ?_
  have hyb : min ArticleProg.yearBig year ≤ 100000 := Nat.min_le_left _ _
  refine fragR_ifF o rfl (lowK_any _ (k := .skip) rfl) lowKK_nil rfl rfl wordsPost_clock
    (fun u h => FramerCode.eval_and (p := false) rfl (FramerCode.eval_le (by decide) (by omega) rfl
      (ev_var (vals_lookup h.1.vals rfl)))) (fragR_of (frag_nil o fun u h => ?_))
  refine ⟨⟨p1, ws1, p2, mo, p3, ws3, day, year, numM A (numM A M3 (some day)) (some year)⟩, runF_of h (by
    repeat (refine lookups_cons rfl ?_)
    exact lookups_nil), hf5, h3b, hmo1, hmo12, W, seg a ws1 p1, seg a ws2 p2, seg a ws3 p3, hWr, hd1, hmoi, hd3, hdv'⟩

/-! ## The time and the zone -/

theorem names_fr {P : List (String × Value)} {ns T : List String} (hP : P.map Prod.fst = ns) (h : ∀ x ∈ ns, x ∉ T) :
    ∀ q ∈ P, q.1 ∉ T :=
  fun _ hq => h _ (hP ▸ List.mem_map_of_mem hq)

/-- `artDate`'s statements over the time and the zone. -/
def tzS : List Syntax.PStmt :=
  [.dec "j" (v "p3"), .dec "ph" (n 0), .dec "np" (n 0), .dec "cv" (n 0), .dec "cd" (n 0),
   .dec "hh" (n 0), .dec "mi" (n 0), .dec "se" (n 0), .dec "bad" (n 0),
   .dec "zl" (n 0), .dec "z0" (n 0), .dec "zd" (n 1), .dec "zv" (n 0), .dec "zg" (n 1),
   .while (eLt (v "j") (v "c")) tzBody,
   ifs (eEq (v "ph") (n 0)) finishS,
   ifs (or2 (v "bad") (or2 (eLt (v "np") (n 2)) (eLt (n 3) (v "np")))) [.ret (n 0)],
   .dec "off" (n 0)] ++ zoneS

/-- The date's value from its parts, checked: `dvC`'s last step. -/
def dvEnd (W : Option Bytes) (year mo day h mi s : Nat) (off : Int) : Option Int :=
  if 1900 ≤ year ∧ 1 ≤ day ∧ day ≤ ArticleSpec.daysIn year mo ∧ h ≤ 23 ∧ mi ≤ 59 ∧ s ≤ 60 then
    (if W.all fun w => indexOf w dayNames 0 == some (ArticleSpec.weekday (ArticleSpec.daysFromCivil year mo day)) then
      some (ArticleSpec.daysFromCivil year mo day * 86400 + ((h * 3600 + mi * 60 + s : Nat) : Int) - off) else none)
  else none

/-- The time read and the zone's offset. -/
structure TzSt where
  h : Nat
  mi : Nat
  s : Nat
  off : Int

/-- What the time and the zone end in: the date's value, its checks left. -/
def TzPost (s1 : PancakeState σ) (A : Word) (a : Bytes) (S E C : Nat) (f : FrontSt) (g : WordsSt)
    (W : Option Bytes) : Assn σ := fun u =>
  ∃ q : TzSt, RunF s1 (("off", BitVec.ofInt 64 q.off) ::
      (tzL (tzEnd ((seg a g.p3 C).filter fun b => !gap b)) C ++ (wordsL g ++ frontL S E A C f))) (· = g.m) u ∧
    (tzEnd ((seg a g.p3 C).filter fun b => !gap b)).hh = min 1000 q.h ∧
    (tzEnd ((seg a g.p3 C).filter fun b => !gap b)).mi = min 1000 q.mi ∧
    (tzEnd ((seg a g.p3 C).filter fun b => !gap b)).se = min 1000 q.s ∧ -359940 ≤ q.off ∧ q.off ≤ 359940 ∧
    ArticleSpec.dateValue (seg a S E) = dvEnd W g.year g.mo g.day q.h q.mi q.s q.off

theorem tzPost_clock {s1 : PancakeState σ} {A : Word} {a : Bytes} {S E C : Nat} {f : FrontSt} {g : WordsSt}
    {W : Option Bytes} : Safe.ClockFree (TzPost s1 A a S E C f g W) :=
  fun u k ⟨q, h, h1⟩ => ⟨q, runF_clock _ _ _ u k h, h1⟩

/-- **The time and the zone**, read in one loop and checked. -/
theorem tz_frag (o : Oracle σ) {A : Word} {s1 : PancakeState σ} (hA : Area ArticleProg.ofs A s1)
    (hcode : ArtCode s1.code) {a : Bytes} (hlen : a.length ≤ artMax) (hin : InputAt s1.memory s1.memaddrs s1.be A a)
    (hb : s1.memory (at_ A aBroken) = 0) (hP : Pows s1.memory A) {S E C : Nat} (hCa : C ≤ a.length)
    (f : FrontSt) (g : WordsSt) (hg : DFrame A s1.memory g.m) (hp3 : g.p3 ≤ C) {W : Option Bytes} {d mth y : Bytes}
    (hd : number? d = some g.day) (hm : indexOf mth monthNames 0 = some (g.mo - 1)) (hmo : 1 ≤ g.mo)
    (hy : number? y = some g.year)
    (hdv : ArticleSpec.dateValue (seg a S E) = dvC W d mth y ((seg a g.p3 C).filter fun b => !gap b)) :
    FragR o (DateRet A a S E s1.memory) tzS (RunF s1 (wordsL g ++ frontL S E A C f) (· = g.m))
      (TzPost s1 A a S E C f g W) := by
  have hM := artMax_eq
  have hA8 := hA.hA
  let ns := ["y4", "yr", "dy", "ys", "p3", "mo", "p2", "ds", "p1", "ts", "hw", "wk", "i", "cp", "nc", "go", "c", "a",
    "s", "e"]
  have hfr := names_fr (P := wordsL g ++ frontL S E A C f) (T := tzNames) (ns := ns) rfl (by decide)
  have hfr0 := names_fr (P := wordsL g ++ frontL S E A C f) (T := tzNames0) (ns := ns) rfl (by decide)
  have hing := dframe_input hA8 hlen hin hg
  refine fragR_append (xs := [_]) (fragR_of (runF_dec o rfl rfl (v := BitVec.ofNat 64 g.p3) fun u h =>
    ev_var (vals_lookup h.1.vals rfl))) ?_
  refine fragR_append (xs := [_]) (fragR_of (runF_dec o rfl rfl (v := BitVec.ofNat 64 0) fun _ _ => rfl)) ?_
  refine fragR_append (xs := [_]) (fragR_of (runF_dec o rfl rfl (v := BitVec.ofNat 64 0) fun _ _ => rfl)) ?_
  refine fragR_append (xs := [_]) (fragR_of (runF_dec o rfl rfl (v := BitVec.ofNat 64 0) fun _ _ => rfl)) ?_
  refine fragR_append (xs := [_]) (fragR_of (runF_dec o rfl rfl (v := BitVec.ofNat 64 0) fun _ _ => rfl)) ?_
  refine fragR_append (xs := [_]) (fragR_of (runF_dec o rfl rfl (v := BitVec.ofNat 64 0) fun _ _ => rfl)) ?_
  refine fragR_append (xs := [_]) (fragR_of (runF_dec o rfl rfl (v := BitVec.ofNat 64 0) fun _ _ => rfl)) ?_
  refine fragR_append (xs := [_]) (fragR_of (runF_dec o rfl rfl (v := BitVec.ofNat 64 0) fun _ _ => rfl)) ?_
  refine fragR_append (xs := [_]) (fragR_of (runF_dec o rfl rfl (v := BitVec.ofNat 64 0) fun _ _ => rfl)) ?_
  refine fragR_append (xs := [_]) (fragR_of (runF_dec o rfl rfl (v := BitVec.ofNat 64 0) fun _ _ => rfl)) ?_
  refine fragR_append (xs := [_]) (fragR_of (runF_dec o rfl rfl (v := BitVec.ofNat 64 0) fun _ _ => rfl)) ?_
  refine fragR_append (xs := [_]) (fragR_of (runF_dec o rfl rfl (v := BitVec.ofNat 64 1) fun _ _ => rfl)) ?_
  refine fragR_append (xs := [_]) (fragR_of (runF_dec o rfl rfl (v := BitVec.ofNat 64 0) fun _ _ => rfl)) ?_
  refine fragR_append (xs := [_]) (fragR_of (runF_dec o rfl rfl (v := BitVec.ofNat 64 1) fun _ _ => rfl)) ?_
  refine fragR_append (xs := [_]) (fragR_of (frag_conseq (tz_loop o hfr hing rfl rfl hp3 hCa (by omega))
    (fun u h => h) fun _ h => h)) ?_
  -- the spec's reading of the rest
  generalize hrest : (seg a g.p3 C).filter (fun b => !gap b) = rest at hdv
  have hfold : tzFold (seg a g.p3 C) = rest.foldl (fun t b => tzStep t b.toNat) tz0 := by rw [← hrest]; rfl
  have hTB := tb_fold (seg a g.p3 C)
  rw [seg_length a hp3 hCa] at hTB
  obtain ⟨tb1, tb2, tb3, tb4, tb5⟩ := hTB
  obtain ⟨t', hTI, htf, hzf⟩ := tz_end rest
  have hparts : ∀ p ∈ (rest.takeWhile timeByte).splitOn ArticleSpec.COLON,
      p.all DN.News.CommandSpec.isDigit = true := by
    have e : (rest.takeWhile timeByte).splitOn ArticleSpec.COLON =
        List.splitOnPPrepend (· == ArticleSpec.COLON) (rest.takeWhile timeByte) [] := List.splitOnP_eq_splitOnPPrepend
    rw [e]; exact parts_digits _ [] List.all_takeWhile rfl
  obtain ⟨tnone, tsome⟩ := time_of hTI hparts
  simp only [tfOf, Prod.mk.injEq] at htf
  obtain ⟨enp, ehh, emi, ese, ebad⟩ := htf
  have hE : tzEnd rest = if (tzFold (seg a g.p3 C)).ph = 0 then tzFinish (tzFold (seg a g.p3 C))
      else tzFold (seg a g.p3 C) := by rw [hfold]; rfl
  have hnpE : (tzEnd rest).np ≤ C - g.p3 + 1 := by rw [hE]; split <;> (try simp only [tzFinish]) <;> omega
  have hbadE : (tzEnd rest).bad ≤ 1 := by rw [ebad]; exact hTI.2.2.1
  refine fragR_append (xs := [_]) (fragR_of (P' := RunF s1 (tzL (tzEnd rest) C ++ (wordsL g ++ frontL S E A C f))
    (· = g.m)) ?_) ?_
  · by_cases hph : (tzFold (seg a g.p3 C)).ph = 0
    · rw [hE, if_pos hph]
      exact DN.News.ArticleScan.frag_ifT o rfl (lowK_any _ (k := .skip) rfl) lowKK_nil rfl rfl (runF_clock _ _ _)
        (fun u h => (FramerCode.eval_eq (by omega) (by decide) (ev_var (vals_lookup h.1.vals rfl)) rfl).trans
          (by rw [bw_t hph])) (tz_finish0 o hfr0 (by omega) (by omega))
    · rw [hE, if_neg hph]
      exact DN.News.ArticleScan.frag_ifF o rfl (lowK_any _ (k := .skip) rfl) lowKK_nil rfl rfl (runF_clock _ _ _)
        (fun u h => (FramerCode.eval_eq (by omega) (by decide) (ev_var (vals_lookup h.1.vals rfl)) rfl).trans
          (by rw [bw_f hph])) (frag_nil o fun _ h => h)
  refine fragR_append (xs := [_]) (ret0_frag o rfl (runF_clock _ _ _)
    (b := decide ((tzEnd rest).bad ≠ 0) || (decide ((tzEnd rest).np < 2) || decide (3 < (tzEnd rest).np)))
    (fun u h => FramerCode.eval_or2 (by
        rw [ev_var (vals_lookup h.1.vals rfl)]; congr 1
        rcases (by omega : (tzEnd rest).bad = 0 ∨ (tzEnd rest).bad = 1) with e | e <;> rw [e] <;> rfl)
      (FramerCode.eval_or2 (FramerCode.eval_lt (by omega) (by decide) (ev_var (vals_lookup h.1.vals rfl)) rfl)
        (FramerCode.eval_lt (by decide) (by omega) rfl (ev_var (vals_lookup h.1.vals rfl)))))
    fun hb0 u h => ⟨by rw [h.2]; exact hg, .inl ⟨rfl, by
      rw [hdv]; refine dvC_none (.inr (.inr (.inr (.inl (tnone ?_)))))
      have := hb0; simp only [Bool.or_eq_true, decide_eq_true_eq] at this
      rw [← ebad, ← enp]; omega⟩⟩) ?_
  refine fragR_pure ((tzEnd rest).bad = 0 ∧ 2 ≤ (tzEnd rest).np ∧ (tzEnd rest).np ≤ 3) (fun u h => by
    have := h.2; simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not] at this; omega)
    (lowK_any _ (k := .skip) rfl) fun hok => ?_
  obtain ⟨hr, mn, sc, ht, hhh, hmi, hse⟩ := tsome (by rw [← ebad, ← enp]; exact hok)
  refine fragR_conseq (P0 := RunF s1 (tzL (tzEnd rest) C ++ (wordsL g ++ frontL S E A C f)) (· = g.m)) ?_
    (fun u h => h.1) fun _ h => h
  refine fragR_append (xs := [_]) (fragR_of (runF_dec o rfl rfl (v := BitVec.ofNat 64 0) fun _ _ => rfl)) ?_
  -- the zone
  have hzone : progZone (zfOf (tzEnd rest)) = specZone (rest.drop (rest.takeWhile timeByte).length) := by
    rw [hzf, zone_eq]
  have hZB : ZB (zfOf (tzEnd rest)) := by rw [hzf]; exact zb_zOf _
  have hzlE : (tzEnd rest).zl ≤ C - g.p3 := by rw [hE]; split <;> (try simp only [tzFinish]) <;> omega
  have hval : ∀ off, specZone (rest.drop (rest.takeWhile timeByte).length) = some off →
      ArticleSpec.dateValue (seg a S E) = dvEnd W g.year g.mo g.day hr mn sc off := fun off hz => by
    rw [hdv, dvC_some hd hm hy ht hz, Nat.sub_add_cancel hmo]; rfl
  have hnone : specZone (rest.drop (rest.takeWhile timeByte).length) = none →
      ArticleSpec.dateValue (seg a S E) = none := fun hz => by rw [hdv]; exact dvC_none (.inr (.inr (.inr (.inr hz))))
  generalize hT : tzEnd rest = T at hzone hZB hzlE ehh emi ese ⊢
  have hpost : ∀ (off : Int) u, RunF s1 (("off", BitVec.ofInt 64 off) :: (tzL T C ++ (wordsL g ++ frontL S E A C f)))
      (· = g.m) u → progZone (zfOf T) = some off → TzPost s1 A a S E C f g W u := by
    intro off u h hz
    have hb := progZone_bound hZB hz
    rw [hzone] at hz
    have hv := hval off hz
    subst hT; subst hrest
    exact ⟨⟨hr, mn, sc, off⟩, h, ehh.trans hhh, emi.trans hmi, ese.trans hse, hb.1, hb.2, hv⟩
  obtain ⟨zb1, zb2, zb3, zb4⟩ := hZB
  have zg1 : T.zg ≤ 1 := zb1
  have zd1 : T.zd ≤ 1 := zb2
  have z0b : T.z0 < 256 := zb3
  have zvb : T.zv < zcap T.zl := zb4
  have hzl64 : T.zl < 2 ^ 64 := Nat.lt_of_le_of_lt hzlE (Nat.lt_of_le_of_lt (Nat.sub_le _ _)
    (Nat.lt_of_le_of_lt hCa (Nat.lt_of_le_of_lt hlen (by decide))))
  have hzd64 : T.zd < 2 ^ 64 := Nat.lt_of_le_of_lt zd1 (by decide)
  have hz064 : T.z0 < 2 ^ 64 := Nat.lt_trans z0b (by decide)
  have hPg : Pows g.m A := fun j hj => by
    rw [dframe_low hg (by have := DN.News.AbnfLayout.pow_lt; omega)]; exact hP j hj
  have hbg : g.m (at_ A aBroken) = 0 := by rw [dframe_low hg DN.News.ArticleGrammar.broken_low]; exact hb
  refine fragR_if o rfl lowKK_nil (lowK_any _ (k := .skip) rfl) tzPost_clock (noDecl _ rfl)
    (fun u y w ⟨q, h, hq⟩ hy => ⟨q, runF_restore h (by
      change y ∈ ["zh", "zm"] at hy
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
      rcases hy with rfl | rfl <;> rfl) w, hq⟩)
    (b := decide (T.zl = 3) && decide (T.zg = 1))
    (fun u h => FramerCode.eval_and (FramerCode.eval_eq hzl64 (by decide) (ev_var (vals_lookup h.1.vals rfl)) rfl)
      (by
        rw [ev_var (vals_lookup h.1.vals rfl)]; congr 1
        rcases Nat.le_one_iff_eq_zero_or_eq_one.1 zg1 with e | e <;> rw [e] <;> rfl)) (fun hg3 => ?_) fun hg3 => ?_
  · -- GMT
    have e : T.zl = 3 ∧ T.zg = 1 := by simpa using hg3
    refine fragR_of (frag_nil o fun u h => hpost 0 u (runF_of h (by
      repeat (refine lookups_cons rfl ?_)
      exact lookups_nil)) ?_)
    simp only [progZone, zfOf]; rw [if_pos e]
  have hng : ¬(T.zl = 3 ∧ T.zg = 1) := fun e => by simp [e.1, e.2] at hg3
  refine fragR_append (xs := [_]) (ret0_frag o rfl (runF_clock _ _ _) (b := decide (T.zl ≠ 5) || decide (T.zd = 0))
    (fun u h => FramerCode.eval_or2 (by
        rw [DN.News.AbnfLeaves.ne_eval (ev_var (vals_lookup h.1.vals rfl)) rfl, ofNat_ne_iff hzl64 (by decide)])
      (FramerCode.eval_eq hzd64 (by decide) (ev_var (vals_lookup h.1.vals rfl)) rfl))
    fun hb0 u h => ⟨by rw [h.2]; exact hg, .inl ⟨rfl, hnone (by
      rw [← hzone]; simp only [progZone, zfOf]; rw [if_neg hng, if_pos (by simpa using hb0)])⟩⟩) ?_
  refine fragR_pure (T.zl = 5 ∧ T.zd ≠ 0) (fun u h => by
    have := h.2; simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not, Decidable.not_not] at this; exact this)
    (lowK_any _ (k := .skip) rfl) fun h5 => ?_
  have hzv : T.zv < 10000 := by have := zvb; rw [h5.1] at this; exact this
  have hzv62 : T.zv < 2 ^ 62 := Nat.lt_trans hzv (by decide)
  have hzv64 : T.zv < 2 ^ 64 := Nat.lt_trans hzv (by decide)
  have hmod : T.zv - T.zv / 100 * 100 = T.zv % 100 := by rw [Nat.mod_def, Nat.mul_comm]
  have hm63 : T.zv % 100 < 2 ^ 63 := Nat.lt_trans (Nat.mod_lt _ (by decide)) (by decide)
  have hn5 : ¬(T.zl ≠ 5 ∨ T.zd = 0) := fun e => e.elim (· h5.1) (h5.2 ·)
  refine fragR_conseq (P0 := RunF s1 (("off", BitVec.ofNat 64 0) :: (tzL T C ++ (wordsL g ++ frontL S E A C f)))
    (· = g.m)) ?_ (fun u h => h.1) fun _ h => h
  refine fragR_append (xs := [_, _]) (divCall_frag o hA hcode (rt := "zh") (by decide) rfl rfl hPg hbg rfl (X := T.zv)
    (D := 100) hzv62 (by decide) (by decide) fun u h => ev_var (vals_lookup h.1.vals rfl)) ?_
  refine fragR_append (xs := [_]) (fragR_of (runF_dec o rfl rfl (v := BitVec.ofNat 64 (T.zv % 100)) fun u h => by
    rw [ev_subE (ev_var (vals_lookup h.1.vals rfl)) (ev_mulc (vals_lookup h.1.vals rfl)) (Nat.div_mul_le_self _ _)
      hzv64, hmod])) ?_
  refine fragR_append (xs := [_]) (ret0_frag o rfl (runF_clock _ _ _) (b := decide (60 ≤ T.zv % 100))
    (fun u h => FramerCode.eval_le (by decide) hm63 rfl (ev_var (vals_lookup h.1.vals rfl)))
    fun hb0 u h => ⟨by rw [h.2]; exact hg, .inl ⟨rfl, hnone (by
      rw [← hzone]; simp only [progZone, zfOf]
      rw [if_neg hng, if_neg hn5, if_pos (of_decide_eq_true hb0)])⟩⟩) ?_
  refine fragR_pure (¬60 ≤ T.zv % 100) (fun u h => by have := h.2; simpa using this)
    (lowK_any _ (k := .skip) rfl) fun h60 => ?_
  have hpz : ∀ x, progZone (zfOf T) = x ↔ (if T.z0 = 43 then some ((T.zv / 100 * 3600 + T.zv % 100 * 60 : Nat) : Int)
      else if T.z0 = 45 then some (-((T.zv / 100 * 3600 + T.zv % 100 * 60 : Nat) : Int)) else none) = x := by
    intro x; simp only [progZone, zfOf]; rw [if_neg hng, if_neg hn5, if_neg h60]
  refine fragR_conseq (P0 := RunF s1 (("zm", BitVec.ofNat 64 (T.zv % 100)) :: ("zh", BitVec.ofNat 64 (T.zv / 100)) ::
    ("off", BitVec.ofNat 64 0) :: (tzL T C ++ (wordsL g ++ frontL S E A C f))) (· = g.m)) ?_ (fun u h => h.1)
    fun _ h => h
  refine fragR_append (xs := [_]) (fragR_of (runF_set o rfl rfl
    (v := BitVec.ofNat 64 (T.zv / 100 * 3600 + T.zv % 100 * 60)) fun u h =>
      WpBytes.eval_add (ev_mulc (vals_lookup h.1.vals rfl)) (ev_mulc (vals_lookup h.1.vals rfl)))) ?_
  refine fragR_if o rfl lowKK_nil (lowK_any _ (k := .skip) rfl) tzPost_clock (noDecl _ rfl) (noDecl _ rfl)
    (b := decide (T.z0 = 43)) (fun u h => FramerCode.eval_eq hz064 (by decide)
      (ev_var (vals_lookup h.1.vals rfl)) rfl) (fun h43 => ?_) fun h43 => ?_
  · refine fragR_of (frag_nil o fun u h => hpost ((T.zv / 100 * 3600 + T.zv % 100 * 60 : Nat) : Int) u
      (runF_of h (by
        refine lookups_cons (by rw [BitVec.ofInt_natCast]; rfl) ?_
        repeat (refine lookups_cons rfl ?_)
        exact lookups_nil)) ?_)
    rw [hpz, if_pos (of_decide_eq_true h43)]
  refine fragR_if o rfl (lowK_any _ (k := .skip) rfl) (lowK_any _ (k := .skip) rfl) tzPost_clock (noDecl _ rfl)
    (noDecl _ rfl) (b := decide (T.z0 = 45)) (fun u h => FramerCode.eval_eq hz064 (by decide)
      (ev_var (vals_lookup h.1.vals rfl)) rfl) (fun h45 => ?_) fun h45 => ?_
  · refine fragR_of (frag_conseq (runF_set o rfl rfl
      (v := BitVec.ofNat 64 0 - BitVec.ofNat 64 (T.zv / 100 * 3600 + T.zv % 100 * 60)) fun u h => by
        simp only [eval, vals_lookup (x := "off") h.1.vals rfl]) (fun _ h => h) fun u h =>
      hpost (-((T.zv / 100 * 3600 + T.zv % 100 * 60 : Nat) : Int)) u (runF_of h (by
        refine lookups_cons (by rw [BitVec.ofInt_neg, BitVec.ofInt_natCast]; simp) ?_
        repeat (refine lookups_cons rfl ?_)
        exact lookups_nil)) ?_)
    rw [hpz, if_neg (of_decide_eq_false h43), if_pos (of_decide_eq_true h45)]
  exact fragR_ret o rfl fun u h => ⟨0, rfl, by rw [h.2]; exact hg, .inl ⟨rfl, hnone (by
    rw [← hzone, hpz, if_neg (of_decide_eq_false h43), if_neg (of_decide_eq_false h45)])⟩⟩

/-! ## The checks and the value -/

theorem mem_artCivil : gd ArticleProg.artCivil ∈
    ArticleProg.functions ArticleSpec.spec (ArticleProg.entries ArticleSpec.spec) .none :=
  List.mem_append_right _ (List.mem_map.2 ⟨ArticleProg.artCivil, by simp, rfl⟩)

/-- **A call of `artCivil`**, the check after it passed: the days since 1970, the memory as it was. -/
theorem civilCall_frag (o : Oracle σ) {R : Ret} {A : Word} {s0 : PancakeState σ} (hA : Area ArticleProg.ofs A s0)
    (hcode : ArtCode s0.code) {rt : String} (hra : rt ≠ "a") {l : List (String × Value)}
    (hla : l.lookup "a" = some A) (hrt : Fresh rt l = true) {m0 : Word → Word} (hP : Pows m0 A)
    (hb : m0 (at_ A aBroken) = 0) {x y z : String} {Y M Dd : Nat} (hY1 : 1 ≤ Y) (hY : Y < 2 ^ 40) (hM : M ≤ 12)
    (hD1 : 1 ≤ Dd) (hD : Dd < 2 ^ 40) (hx : l.lookup x = some (BitVec.ofNat 64 Y))
    (hy : l.lookup y = some (BitVec.ofNat 64 M)) (hz : l.lookup z = some (BitVec.ofNat 64 Dd)) :
    FragR o R (guardS (.call rt "artCivil" [v x, v y, v z])) (RunF s0 l (· = m0))
      (RunF s0 ((rt, BitVec.ofInt 64 (ArticleSpec.daysFromCivil Y M Dd)) :: l) (· = m0)) := by
  refine fragR_conseq (gcall_frag o hA hcode hra (f := ArticleProg.artCivil) mem_artCivil (by decide)
    (args := [.var x, .var y, .var z]) rfl hla
    (vs := [BitVec.ofNat 64 Y, BitVec.ofNat 64 M, BitVec.ofNat 64 Dd]) rfl
    (fun u h => by simp only [evalArgs, ev_var (vals_lookup h.1.vals hx), ev_var (vals_lookup h.1.vals hy),
      ev_var (vals_lookup h.1.vals hz)])
    (Rf := fun m v m' => v = BitVec.ofInt 64 (ArticleSpec.daysFromCivil Y M Dd) ∧ m' = m)
    (fun s1 hA1 hc _ _ hloc hF => artCivil_ok o hA1 (by rw [hc]; exact hcode) (by rw [hF]; exact hP)
      (by rw [hF]; exact hb) hY1 hY hM hD1 hD ((hloc "y").trans rfl) ((hloc "mo").trans rfl) ((hloc "d").trans rfl))
    hrt (G := fun v m => m = m0 ∧ v = BitVec.ofInt 64 (ArticleSpec.daysFromCivil Y M Dd))
    (fun m m' v hm ⟨e1, e2⟩ => ⟨e2.trans hm, e1⟩)
    fun v m h => by rw [h.1]; exact hb) (fun u h => h) fun u ⟨v, h⟩ => ?_
  obtain ⟨hm, hv⟩ := h.2
  subst hv; exact ⟨h.1, hm⟩

theorem and3_eval {u : PancakeState σ} {x : String} {X : Nat} (hX : X < 2 ^ 64)
    (h : u.locals x = some (BitVec.ofNat 64 X)) :
    eval u (.op .and_ (.var x) (.const (BitVec.ofNat 64 3))) = some (BitVec.ofNat 64 (X % 4)) := by
  simp only [eval, h]
  rw [show (BitVec.ofNat 64 3 : Word) = BitVec.ofNat 64 (2 ^ 2 - 1) from rfl, DN.News.Calendar.and_mask X 2 hX
    (by decide)]

theorem value_ofInt (D : Int) (N : Nat) (off : Int) : BitVec.ofInt 64 (D * 86400 + (N : Int) - off) =
    BitVec.ofInt 64 D * BitVec.ofNat 64 86400 + BitVec.ofNat 64 N - BitVec.ofInt 64 off := by
  rw [Int.sub_eq_add_neg, BitVec.ofInt_add, BitVec.ofInt_add, BitVec.ofInt_mul, BitVec.ofInt_neg, BitVec.ofInt_natCast,
    BitVec.sub_eq_add_neg]; rfl

theorem days_shift (D : Int) (h : -700004 ≤ D) :
    BitVec.ofInt 64 D + BitVec.ofNat 64 700004 = BitVec.ofNat 64 (D + 700004).toNat := by
  have e : BitVec.ofNat 64 (D + 700004).toNat = BitVec.ofInt 64 ((D + 700004).toNat : Int) :=
    (BitVec.ofInt_natCast _ _).symm
  rw [e, Int.toNat_of_nonneg (by omega), BitVec.ofInt_add]; rfl

theorem sub7 (X : Nat) : X - X / 7 * 7 = X % 7 := by omega

theorem time_le {h mi s : Nat} (h1 : h ≤ 23) (h2 : mi ≤ 59) (h3 : s ≤ 60) : h * 3600 + mi * 60 + s ≤ 86400 := by
  omega

/-- A value from a year past `yearBig`, past `2 ^ 41`. -/
theorem big_value {D off : Int} {N : Nat} (hD : 35780167 ≤ D) (ho : off ≤ 359940) :
    2 ^ 41 ≤ D * 86400 + (N : Int) - off := by omega

/-- A value from a year below `yearBig` within `2 ^ 42` either way. -/
theorem small_value {D off : Int} {N : Nat} (h1 : -26333 ≤ D) (h2 : D < 36600000) (hN : N ≤ 86400)
    (ho1 : -359940 ≤ off) (ho2 : off ≤ 359940) :
    -2 ^ 42 < D * 86400 + (N : Int) - off ∧ D * 86400 + (N : Int) - off < 2 ^ 42 := by omega

/-- Whether the year is leap, from its place in the 400 years. -/
def leapN (y4 : Nat) : Nat := if y4 % 4 = 0 ∧ y4 ≠ 100 ∧ y4 ≠ 200 ∧ y4 ≠ 300 then 1 else 0

/-- **The last statements**: the month's days, the checks, the days since 1970, the day of the week, the value. -/
theorem check_frag (o : Oracle σ) {A : Word} {s1 : PancakeState σ} (hA : Area ArticleProg.ofs A s1)
    (hD : ArtDom A s1.memaddrs) (hcode : ArtCode s1.code) (hb : s1.memory (at_ A aBroken) = 0) (hP : Pows s1.memory A)
    {a : Bytes} {S E C : Nat} (f : FrontSt) (g : WordsSt) (hg : DFrame A s1.memory g.m) (hmo1 : 1 ≤ g.mo)
    (hmo12 : g.mo ≤ 12) {W : Option Bytes} (hWr : W = none ∧ f.hw = 0 ∨ ∃ name, W = some name ∧ f.hw = 1 ∧
      f.wk = ((indexOf name dayNames 0).map (· + 1)).getD 0) (T : TZ) (q : TzSt) (hh : T.hh = min 1000 q.h)
    (hmi : T.mi = min 1000 q.mi) (hse : T.se = min 1000 q.s) (ho1 : -359940 ≤ q.off) (ho2 : q.off ≤ 359940)
    (hdv : ArticleSpec.dateValue (seg a S E) = dvEnd W g.year g.mo g.day q.h q.mi q.s q.off) :
    FragR o (DateRet A a S E s1.memory) (monthS ++ checkS)
      (RunF s1 (("off", BitVec.ofInt 64 q.off) :: (tzL T C ++ (wordsL g ++ frontL S E A C f))) (· = g.m))
      fun _ => False := by
  have hyb : ArticleProg.yearBig = 100000 := rfl
  have hy4 : g.year % 400 < 400 := Nat.mod_lt _ (by decide)
  -- the month's days
  refine fragR_append (xs := [_]) (fragR_of (runF_dec o rfl rfl (v := BitVec.ofNat 64 (leapN (g.year % 400)))
    fun u h => by
      have e := vals_lookup (x := "y4") h.1.vals rfl
      have ne : ∀ k : Nat, k < 400 → eval u (.cmp .equal (.cmp .equal (.var "y4") (.const (BitVec.ofNat 64 k)))
          (.const (BitVec.ofNat 64 0))) = some (bw (decide (g.year % 400 ≠ k))) := fun k hk => by
        rw [DN.News.AbnfLeaves.ne_eval (ev_var e) rfl, ofNat_ne_iff (by omega) (by omega)]
      rw [FramerCode.eval_and (FramerCode.eval_eq (by omega) (by decide) (and3_eval (by omega) e) rfl)
        (FramerCode.eval_and (ne 100 (by decide)) (FramerCode.eval_and (ne 200 (by decide)) (ne 300 (by decide)))),
        bw_ofNat]
      unfold leapN
      simp only [Bool.and_eq_true, decide_eq_true_eq])) ?_
  refine fragR_append (xs := [_]) (fragR_of (runF_dec o rfl rfl (v := BitVec.ofNat 64 31) fun _ _ => rfl)) ?_
  refine fragR_append (xs := [_]) (fragR_of (P' := RunF s1 (("dm", BitVec.ofNat 64 (dmOf (g.year % 400) g.mo)) ::
    ("lp", BitVec.ofNat 64 (leapN (g.year % 400))) :: ("off", BitVec.ofInt 64 q.off) ::
      (tzL T C ++ (wordsL g ++ frontL S E A C f))) (· = g.m)) ?_) ?_
  · have hmo64 : g.mo < 2 ^ 64 := by omega
    have evm : ∀ k, k < 2 ^ 64 → ∀ u, RunF s1 (("dm", BitVec.ofNat 64 31) ::
        ("lp", BitVec.ofNat 64 (leapN (g.year % 400))) :: ("off", BitVec.ofInt 64 q.off) ::
        (tzL T C ++ (wordsL g ++ frontL S E A C f))) (· = g.m) u →
        eval u (.cmp .equal (.var "mo") (.const (BitVec.ofNat 64 k))) = some (bw (decide (g.mo = k))) :=
      fun k hk u h => FramerCode.eval_eq hmo64 hk (ev_var (vals_lookup h.1.vals rfl)) rfl
    by_cases h2 : g.mo = 2
    · have hdm : dmOf (g.year % 400) g.mo = 28 + leapN (g.year % 400) := by unfold dmOf leapN; rw [if_pos h2]
      refine DN.News.ArticleScan.frag_ifT o rfl (lowK_any _ (k := .skip) rfl) (lowK_any _ (k := .skip) rfl) rfl rfl
        (runF_clock _ _ _) (fun u h => (evm 2 (by decide) u h).trans (by rw [bw_t h2])) ?_
      exact set_to o rfl rfl (v := BitVec.ofNat 64 (28 + leapN (g.year % 400)))
        (fun u h => WpBytes.eval_add rfl (ev_var (vals_lookup h.1.vals rfl))) fun u h => runF_of h (by
          refine lookups_cons (by rw [hdm]; rfl) ?_
          repeat (refine lookups_cons rfl ?_)
          exact lookups_nil)
    refine DN.News.ArticleScan.frag_ifF o rfl (lowK_any _ (k := .skip) rfl) (lowK_any _ (k := .skip) rfl) rfl rfl
      (runF_clock _ _ _) (fun u h => (evm 2 (by decide) u h).trans (by rw [bw_f h2])) ?_
    refine cond_set o rfl rfl rfl
      (b := (decide (g.mo = 4) || decide (g.mo = 6)) || (decide (g.mo = 9) || decide (g.mo = 11)))
      (fun u h => FramerCode.eval_or2 (FramerCode.eval_or2 (evm 4 (by decide) u h) (evm 6 (by decide) u h))
        (FramerCode.eval_or2 (evm 9 (by decide) u h) (evm 11 (by decide) u h))) (vx := BitVec.ofNat 64 30)
      (fun _ _ => rfl) (fun hb u h => runF_of h (by
        have hdm : dmOf (g.year % 400) g.mo = 30 := by
          unfold dmOf; rw [if_neg h2, if_pos (by simpa [or_assoc] using hb)]
        refine lookups_cons (by rw [hdm]; rfl) ?_
        repeat (refine lookups_cons rfl ?_)
        exact lookups_nil)) fun hb u h => runF_of h (by
        have hdm : dmOf (g.year % 400) g.mo = 31 := by
          unfold dmOf; rw [if_neg h2, if_neg (by simpa [or_assoc, and_assoc] using hb)]
        refine lookups_cons (by rw [hdm]; rfl) ?_
        repeat (refine lookups_cons rfl ?_)
        exact lookups_nil)
  -- the checks of the day and the time
  have hdm31 : dmOf (g.year % 400) g.mo ≤ 31 := by unfold dmOf; split <;> (try split) <;> (try split) <;> omega
  have hTh : T.hh ≤ 1000 := by rw [hh]; exact Nat.min_le_left _ _
  have hTm : T.mi ≤ 1000 := by rw [hmi]; exact Nat.min_le_left _ _
  have hTs : T.se ≤ 1000 := by rw [hse]; exact Nat.min_le_left _ _
  have hyr : min ArticleProg.yearBig g.year ≤ 100000 := Nat.min_le_left _ _
  have hdy : min ArticleProg.yearBig g.day ≤ 100000 := Nat.min_le_left _ _
  have hlt : ∀ {x y : String} {X Y : Nat}, X < 2 ^ 63 → Y < 2 ^ 63 → ∀ {u : PancakeState σ},
      u.locals x = some (BitVec.ofNat 64 X) → u.locals y = some (BitVec.ofNat 64 Y) →
        eval u (.cmp .less (.var x) (.var y)) = some (bw (decide (X < Y))) :=
    fun hX hY _ hx hy => FramerCode.eval_lt hX hY (ev_var hx) (ev_var hy)
  refine fragR_append (xs := [_]) (ret0_frag o rfl (runF_clock _ _ _)
    (b := (decide (min ArticleProg.yearBig g.year < 1900) || (decide (min ArticleProg.yearBig g.day < 1) ||
      decide (dmOf (g.year % 400) g.mo < min ArticleProg.yearBig g.day))) ||
      (decide (23 < T.hh) || (decide (59 < T.mi) || decide (60 < T.se))))
    (fun u h => FramerCode.eval_or2 (FramerCode.eval_or2
        (FramerCode.eval_lt (Nat.lt_of_le_of_lt hyr (by decide)) (by decide) (ev_var (vals_lookup h.1.vals rfl)) rfl)
        (FramerCode.eval_or2
          (FramerCode.eval_lt (Nat.lt_of_le_of_lt hdy (by decide)) (by decide) (ev_var (vals_lookup h.1.vals rfl)) rfl)
          (hlt (Nat.lt_of_le_of_lt hdm31 (by decide)) (Nat.lt_of_le_of_lt hdy (by decide)) (vals_lookup h.1.vals rfl)
            (vals_lookup h.1.vals rfl))))
      (FramerCode.eval_or2
        (FramerCode.eval_lt (by decide) (Nat.lt_of_le_of_lt hTh (by decide)) rfl (ev_var (vals_lookup h.1.vals rfl)))
        (FramerCode.eval_or2
          (FramerCode.eval_lt (by decide) (Nat.lt_of_le_of_lt hTm (by decide)) rfl (ev_var (vals_lookup h.1.vals rfl)))
          (FramerCode.eval_lt (by decide) (Nat.lt_of_le_of_lt hTs (by decide)) rfl
            (ev_var (vals_lookup h.1.vals rfl))))))
    fun hb0 u h => ⟨by rw [h.2]; exact hg, .inl ⟨rfl, by
      rw [hdv, dvEnd, if_neg]
      have := hb0; simp only [Bool.or_eq_true, decide_eq_true_eq] at this
      rw [daysIn_eq]; omega⟩⟩) ?_
  refine fragR_pure (1900 ≤ g.year ∧ 1 ≤ g.day ∧ g.day ≤ ArticleSpec.daysIn g.year g.mo ∧ q.h ≤ 23 ∧ q.mi ≤ 59 ∧
    q.s ≤ 60) (fun u h => by
      have := h.2; simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not, Nat.not_lt] at this
      rw [daysIn_eq]; omega) (lowK_any _ (k := .skip) rfl) fun hcnd => ?_
  have hday31 : g.day ≤ 31 := Nat.le_trans hcnd.2.2.1 (daysIn_le _ _)
  have hdday : min ArticleProg.yearBig g.day = g.day := Nat.min_eq_right (Nat.le_trans hday31 (by decide))
  have hN := time_le hcnd.2.2.2.1 hcnd.2.2.2.2.1 hcnd.2.2.2.2.2
  clear hdm31 hTh hTm hTs hlt
  refine fragR_conseq (P0 := RunF s1 (("dm", BitVec.ofNat 64 (dmOf (g.year % 400) g.mo)) ::
    ("lp", BitVec.ofNat 64 (leapN (g.year % 400))) :: ("off", BitVec.ofInt 64 q.off) ::
      (tzL T C ++ (wordsL g ++ frontL S E A C f))) (· = g.m)) ?_ (fun u h => h.1) fun _ h => h
  -- the year counted in full
  let Ye := if ArticleProg.yearBig ≤ g.year then 2000 + g.year % 400 else g.year
  have hYe : 1900 ≤ Ye ∧ Ye < 100000 := by
    show 1900 ≤ (if ArticleProg.yearBig ≤ g.year then 2000 + g.year % 400 else g.year) ∧
      (if ArticleProg.yearBig ≤ g.year then 2000 + g.year % 400 else g.year) < 100000
    split <;> omega
  refine fragR_append (xs := [_]) (fragR_of (runF_dec o rfl rfl (v := BitVec.ofNat 64 (min ArticleProg.yearBig g.year))
    fun u h => ev_var (vals_lookup h.1.vals rfl))) ?_
  refine fragR_append (xs := [_]) (fragR_of (cond_set o rfl rfl rfl
    (L' := ("ye", BitVec.ofNat 64 Ye) :: ("dm", BitVec.ofNat 64 (dmOf (g.year % 400) g.mo)) ::
      ("lp", BitVec.ofNat 64 (leapN (g.year % 400))) :: ("off", BitVec.ofInt 64 q.off) ::
      (tzL T C ++ (wordsL g ++ frontL S E A C f)))
    (b := decide (100000 ≤ min ArticleProg.yearBig g.year))
    (fun u h => FramerCode.eval_le (by decide) (by omega) rfl (ev_var (vals_lookup h.1.vals rfl)))
    (vx := BitVec.ofNat 64 (2000 + g.year % 400)) (fun u h => WpBytes.eval_add rfl (ev_var (vals_lookup h.1.vals rfl)))
    (fun hb u h => runF_of h (by
      have e : Ye = 2000 + g.year % 400 := by
        show (if ArticleProg.yearBig ≤ g.year then 2000 + g.year % 400 else g.year) = _
        rw [if_pos (by have := of_decide_eq_true hb; omega)]
      refine lookups_cons (by rw [e]; rfl) ?_
      repeat (refine lookups_cons rfl ?_)
      exact lookups_nil))
    fun hb u h => runF_of h (by
      have e : Ye = min ArticleProg.yearBig g.year := by
        show (if ArticleProg.yearBig ≤ g.year then 2000 + g.year % 400 else g.year) = _
        have := of_decide_eq_false hb
        rw [if_neg (by omega)]; omega
      refine lookups_cons (by rw [e]; rfl) ?_
      repeat (refine lookups_cons rfl ?_)
      exact lookups_nil))) ?_
  -- the days since 1970
  have hPg : Pows g.m A := fun j hj => by
    rw [dframe_low hg (by have := DN.News.AbnfLayout.pow_lt; omega)]; exact hP j hj
  have hbg : g.m (at_ A aBroken) = 0 := by rw [dframe_low hg DN.News.ArticleGrammar.broken_low]; exact hb
  refine fragR_append (xs := [_, _]) (civilCall_frag o hA hcode (rt := "days") (by decide) rfl rfl hPg hbg
    (Y := Ye) (M := g.mo) (Dd := min ArticleProg.yearBig g.day) (Nat.le_trans (by decide) hYe.1)
    (Nat.lt_trans hYe.2 (by decide)) hmo12 (by rw [hdday]; exact hcnd.2.1) (Nat.lt_of_le_of_lt hdy (by decide))
    rfl rfl rfl) ?_
  rw [hdday]
  have hDr := civil_range hYe.1 hYe.2 hmo1 hmo12 hday31
  have hX62 : (ArticleSpec.daysFromCivil Ye g.mo g.day + 700004).toNat < 2 ^ 62 := by omega
  -- the day of the week
  refine fragR_append (xs := [_]) (M := fun u => RunF s1 (("days", BitVec.ofInt 64
      (ArticleSpec.daysFromCivil Ye g.mo g.day)) :: ("ye", BitVec.ofNat 64 Ye) ::
      ("dm", BitVec.ofNat 64 (dmOf (g.year % 400) g.mo)) :: ("lp", BitVec.ofNat 64 (leapN (g.year % 400))) ::
      ("off", BitVec.ofInt 64 q.off) :: (tzL T C ++ (wordsL g ++ frontL S E A C f))) (· = g.m) u ∧
      (W.all fun w => indexOf w dayNames 0 ==
        some (ArticleSpec.weekday (ArticleSpec.daysFromCivil g.year g.mo g.day))) = true) ?_ ?_
  · rcases hWr with ⟨hW0, hhw⟩ | ⟨name, hWn, hhw, hwk⟩
    · refine fragR_if o rfl (lowK_any _ (k := .skip) rfl) lowKK_nil
        (fun u k h => ⟨runF_clock _ _ _ u k h.1, h.2⟩)
        (fun u y w h hy => ⟨runF_restore h.1 (by
          change y ∈ ["q7"] at hy
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hy; subst hy; rfl) w, h.2⟩) (noDecl _ rfl)
        (b := false) (fun u h => by rw [ev_var (vals_lookup h.1.vals rfl), hhw]; rfl)
        (fun hb => absurd hb (by decide)) fun _ => fragR_of (frag_nil o fun _ h => ⟨h, by rw [hW0]; rfl⟩)
    have hwk7 : f.wk ≤ 7 := by
      rw [hwk]; cases hi : indexOf name dayNames 0 with
      | none => simp
      | some i => have := indexOf_lt hi; simp only [Option.map_some, Option.getD_some]; simp [dayNames] at this; omega
    refine fragR_if o rfl (lowK_any _ (k := .skip) rfl) lowKK_nil
      (fun u k h => ⟨runF_clock _ _ _ u k h.1, h.2⟩)
      (fun u y w h hy => ⟨runF_restore h.1 (by
        change y ∈ ["q7"] at hy
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hy; subst hy; rfl) w, h.2⟩) (noDecl _ rfl)
      (b := true) (fun u h => by rw [ev_var (vals_lookup h.1.vals rfl), hhw]; rfl)
      (fun _ => ?_) fun hb => absurd hb (by decide)
    refine fragR_append (xs := [_]) (ret0_frag o rfl (runF_clock _ _ _) (b := decide (f.wk = 0))
      (fun u h => FramerCode.eval_eq (Nat.lt_of_le_of_lt hwk7 (by decide)) (by decide)
        (ev_var (vals_lookup h.1.vals rfl)) rfl)
      fun hb0 u h => ⟨by rw [h.2]; exact hg, .inl ⟨rfl, by
        rw [hdv, dvEnd, if_pos hcnd, if_neg]
        rw [hWn]
        have h0 := of_decide_eq_true hb0
        rw [hwk] at h0
        cases hi : indexOf name dayNames 0 with
        | none => simp [hi]
        | some i => rw [hi] at h0; simp at h0⟩⟩) ?_
    refine fragR_pure (f.wk ≠ 0) (fun u h => by have := h.2; simpa using this) (lowK_any _ (k := .skip) rfl)
      fun hw0 => ?_
    obtain ⟨i, hi, hwki⟩ : ∃ i, indexOf name dayNames 0 = some i ∧ f.wk = i + 1 := by
      rw [hwk] at hw0 ⊢
      cases hi : indexOf name dayNames 0 with
      | none => rw [hi] at hw0; exact absurd rfl hw0
      | some i => exact ⟨i, rfl, rfl⟩
    refine fragR_conseq (P0 := RunF s1 (("days", BitVec.ofInt 64 (ArticleSpec.daysFromCivil Ye g.mo g.day)) ::
      ("ye", BitVec.ofNat 64 Ye) :: ("dm", BitVec.ofNat 64 (dmOf (g.year % 400) g.mo)) ::
      ("lp", BitVec.ofNat 64 (leapN (g.year % 400))) :: ("off", BitVec.ofInt 64 q.off) ::
      (tzL T C ++ (wordsL g ++ frontL S E A C f))) (· = g.m)) ?_ (fun u h => h.1) fun _ h => h
    have hadd : ∀ u, RunF s1 (("days", BitVec.ofInt 64 (ArticleSpec.daysFromCivil Ye g.mo g.day)) ::
        ("ye", BitVec.ofNat 64 Ye) :: ("dm", BitVec.ofNat 64 (dmOf (g.year % 400) g.mo)) ::
        ("lp", BitVec.ofNat 64 (leapN (g.year % 400))) :: ("off", BitVec.ofInt 64 q.off) ::
        (tzL T C ++ (wordsL g ++ frontL S E A C f))) (· = g.m) u →
        eval u (.op .add (.var "days") (.const (BitVec.ofNat 64 700004))) =
          some (BitVec.ofNat 64 (ArticleSpec.daysFromCivil Ye g.mo g.day + 700004).toNat) := fun u h => by
      simp only [eval, vals_lookup (x := "days") h.1.vals rfl]
      rw [days_shift _ (Int.le_trans (by decide) hDr.1)]
    refine fragR_append (xs := [_, _]) (divCall_frag o hA hcode (rt := "q7") (by decide) rfl rfl hPg hbg rfl
      (X := (ArticleSpec.daysFromCivil Ye g.mo g.day + 700004).toNat) (D := 7) hX62 (by decide) (by decide)
      (hadd)) ?_
    have hX64 : (ArticleSpec.daysFromCivil Ye g.mo g.day + 700004).toNat < 2 ^ 64 := Nat.lt_trans hX62 (by decide)
    have hwk64 : f.wk < 2 ^ 64 := Nat.lt_of_le_of_lt hwk7 (by decide)
    have hwd : ArticleSpec.weekday (ArticleSpec.daysFromCivil g.year g.mo g.day) =
        ArticleSpec.weekday (ArticleSpec.daysFromCivil Ye g.mo g.day) := by
      show _ = ArticleSpec.weekday (ArticleSpec.daysFromCivil
        (if ArticleProg.yearBig ≤ g.year then 2000 + g.year % 400 else g.year) g.mo g.day)
      split
      · have hs := civil_shift (2000 + g.year % 400) g.mo g.day (g.year / 400 - 5) (by omega)
        rw [show 2000 + g.year % 400 + 400 * (g.year / 400 - 5) = g.year by omega] at hs
        rw [hs, weekday_shift]
      · rfl
    have hX := weekday_nat (x := ArticleSpec.daysFromCivil Ye g.mo g.day)
      (Int.le_trans (by decide) hDr.1)
    refine fragR_append (xs := [_]) (ret0_frag o rfl (runF_clock _ _ _)
      (b := decide (f.wk - 1 ≠ (ArticleSpec.daysFromCivil Ye g.mo g.day + 700004).toNat -
        (ArticleSpec.daysFromCivil Ye g.mo g.day + 700004).toNat / 7 * 7))
      (fun u h => by
        have hd : eval u (.op .add (.var "days") (.const (BitVec.ofNat 64 700004))) =
            some (BitVec.ofNat 64 (ArticleSpec.daysFromCivil Ye g.mo g.day + 700004).toNat) := by
          simp only [eval, vals_lookup (x := "days") h.1.vals rfl]; rw [days_shift _ (Int.le_trans (by decide) hDr.1)]
        rw [DN.News.AbnfLeaves.ne_eval (ev_subE (ev_var (vals_lookup h.1.vals rfl)) rfl
            (by rw [hwki]; exact Nat.le_add_left 1 i) hwk64)
          (ev_subE hd (ev_mulc (vals_lookup h.1.vals rfl)) (Nat.div_mul_le_self _ _) hX64),
          ofNat_ne_iff (Nat.lt_of_le_of_lt (Nat.sub_le _ _) hwk64) (Nat.lt_of_le_of_lt (Nat.sub_le _ _) hX64)])
      fun hb0 u h => ⟨by rw [h.2]; exact hg, .inl ⟨rfl, by
        rw [hdv, dvEnd, if_pos hcnd, if_neg]
        rw [hWn]
        have h0 := of_decide_eq_true hb0
        show ¬(indexOf name dayNames 0 ==
          some (ArticleSpec.weekday (ArticleSpec.daysFromCivil g.year g.mo g.day))) = true
        rw [hi, hwd, hX]
        simp only [beq_iff_eq, Option.some.injEq]
        rw [hwki, Nat.add_sub_cancel, sub7] at h0; exact h0⟩⟩) ?_
    refine fragR_pure (f.wk - 1 = (ArticleSpec.daysFromCivil Ye g.mo g.day + 700004).toNat -
      (ArticleSpec.daysFromCivil Ye g.mo g.day + 700004).toNat / 7 * 7) (fun u h => by
        have := h.2; simpa using this) lowKK_nil fun hw7 => ?_
    refine fragR_of (frag_nil o fun u h => ⟨runF_of h.1 (by
      repeat (refine lookups_cons rfl ?_)
      exact lookups_nil), ?_⟩)
    rw [hWn]
    show (indexOf name dayNames 0 == some (ArticleSpec.weekday (ArticleSpec.daysFromCivil g.year g.mo g.day))) = true
    rw [hi, hwd, hX]
    simp only [beq_iff_eq, Option.some.injEq]
    rw [hwki, Nat.add_sub_cancel, sub7] at hw7; exact hw7
  -- the value
  refine fragR_pure ((W.all fun w => indexOf w dayNames 0 ==
    some (ArticleSpec.weekday (ArticleSpec.daysFromCivil g.year g.mo g.day))) = true) (fun u h => h.2)
    (lowK_any _ (k := .skip) rfl) fun hwall => ?_
  refine fragR_conseq (P0 := RunF s1 (("days", BitVec.ofInt 64 (ArticleSpec.daysFromCivil Ye g.mo g.day)) ::
    ("ye", BitVec.ofNat 64 Ye) :: ("dm", BitVec.ofNat 64 (dmOf (g.year % 400) g.mo)) ::
    ("lp", BitVec.ofNat 64 (leapN (g.year % 400))) :: ("off", BitVec.ofInt 64 q.off) ::
    (tzL T C ++ (wordsL g ++ frontL S E A C f))) (· = g.m)) ?_ (fun u h => h.1) fun _ h => h
  have hval : ArticleSpec.dateValue (seg a S E) = some (ArticleSpec.daysFromCivil g.year g.mo g.day * 86400 +
      ((q.h * 3600 + q.mi * 60 + q.s : Nat) : Int) - q.off) := by
    rw [hdv, dvEnd, if_pos hcnd, if_pos hwall]
  refine fragR_append (xs := [_]) (fragR_if o rfl (lowK_any _ (k := .skip) rfl) lowKK_nil
    (Q := fun u => RunF s1 (("days", BitVec.ofInt 64 (ArticleSpec.daysFromCivil Ye g.mo g.day)) ::
      ("ye", BitVec.ofNat 64 Ye) :: ("dm", BitVec.ofNat 64 (dmOf (g.year % 400) g.mo)) ::
      ("lp", BitVec.ofNat 64 (leapN (g.year % 400))) :: ("off", BitVec.ofInt 64 q.off) ::
      (tzL T C ++ (wordsL g ++ frontL S E A C f))) (· = g.m) u ∧ g.year < ArticleProg.yearBig)
    (fun u k h => ⟨runF_clock _ _ _ u k h.1, h.2⟩) (noDecl _ rfl) (noDecl _ rfl)
    (b := decide (100000 ≤ min ArticleProg.yearBig g.year))
    (fun u h => FramerCode.eval_le (by decide) (Nat.lt_of_le_of_lt hyr (by decide)) rfl
      (ev_var (vals_lookup h.1.vals rfl)))
    (fun hbig => fragR_ret o rfl fun u h => ⟨2, rfl, by rw [h.2]; exact hg, .inr (.inr ⟨rfl, _, hval,
      big_value (civil_big (M := g.mo) (D := g.day) (Nat.le_trans (of_decide_eq_true hbig) (Nat.min_le_right _ _)))
        ho2⟩)⟩)
    fun hbig => fragR_of (frag_nil o fun u h => ⟨h, Nat.lt_of_not_le fun e => of_decide_eq_false hbig
      (by rw [Nat.min_eq_left e]; exact Nat.le_refl _)⟩)) ?_
  refine fragR_pure (g.year < ArticleProg.yearBig) (fun u h => h.2) (lowK_any _ (k := .skip) rfl) fun hsmall => ?_
  refine fragR_conseq (P0 := RunF s1 (("days", BitVec.ofInt 64 (ArticleSpec.daysFromCivil Ye g.mo g.day)) ::
    ("ye", BitVec.ofNat 64 Ye) :: ("dm", BitVec.ofNat 64 (dmOf (g.year % 400) g.mo)) ::
    ("lp", BitVec.ofNat 64 (leapN (g.year % 400))) :: ("off", BitVec.ofInt 64 q.off) ::
    (tzL T C ++ (wordsL g ++ frontL S E A C f))) (· = g.m)) ?_ (fun u h => h.1) fun _ h => h
  have hYe' : Ye = g.year := by
    show (if ArticleProg.yearBig ≤ g.year then 2000 + g.year % 400 else g.year) = _
    rw [if_neg (Nat.not_le_of_lt hsmall)]
  have hDr' := civil_range (Y := g.year) (M := g.mo) (D := g.day) hcnd.1 hsmall hmo1 hmo12 hday31
  have hhq : T.hh = q.h := by rw [hh]; exact Nat.min_eq_right (Nat.le_trans hcnd.2.2.2.1 (by decide))
  have hmq : T.mi = q.mi := by rw [hmi]; exact Nat.min_eq_right (Nat.le_trans hcnd.2.2.2.2.1 (by decide))
  have hsq : T.se = q.s := by rw [hse]; exact Nat.min_eq_right (Nat.le_trans hcnd.2.2.2.2.2 (by decide))
  refine fragR_append (xs := [_]) (fragR_of (runF_storeA o (atOffW_lower 15) rfl (y := ArticleProg.w 15)
    (artDom_w hD (by decide)) (fun u h => atA_eval (vals_lookup h.1.vals rfl))
    (val := fun _ => BitVec.ofInt 64 (ArticleSpec.daysFromCivil g.year g.mo g.day * 86400 +
      ((q.h * 3600 + q.mi * 60 + q.s : Nat) : Int) - q.off))
    (fun u h => by
      have hn : eval u (.op .add (.op .add (.mul (.var "hh") (.const (BitVec.ofNat 64 3600)))
          (.mul (.var "mi") (.const (BitVec.ofNat 64 60)))) (.var "se")) =
          some (BitVec.ofNat 64 (q.h * 3600 + q.mi * 60 + q.s)) := by
        rw [← hhq, ← hmq, ← hsq]
        exact WpBytes.eval_add (WpBytes.eval_add (ev_mulc (vals_lookup h.1.vals rfl))
          (ev_mulc (vals_lookup h.1.vals rfl))) (ev_var (vals_lookup h.1.vals rfl))
      rw [DN.Compiler.eval_sub u (DN.News.AbnfLeaves.ev_add
        (DN.News.AbnfLeaves.ev_mul (ev_var (vals_lookup (x := "days") h.1.vals rfl)) rfl) hn)
        (ev_var (vals_lookup (x := "off") h.1.vals rfl)), value_ofInt, hYe'])
    (G := (· = upd g.m (at_ A ArticleProg.xValue) (BitVec.ofInt 64 (ArticleSpec.daysFromCivil g.year g.mo g.day *
      86400 + ((q.h * 3600 + q.mi * 60 + q.s : Nat) : Int) - q.off)))) fun m hm => by subst hm; rfl)) ?_
  exact fragR_ret o rfl fun u h => ⟨1, rfl, by
    rw [h.2]; exact dframe_trans hg (dframe_upd (.inr (.inr (.inr (.inl rfl)))) _),
    .inr (.inl ⟨rfl, _, hval, (small_value hDr'.1 hDr'.2 hN ho1 ho2).1, (small_value hDr'.1 hDr'.2 hN ho1 ho2).2,
      by rw [h.2]; exact upd_eq _ _ _⟩)⟩

/-! ## The whole -/

theorem artDate_split :
    guardL (ArticleProg.artDate .none).body = frontS ++ (wordsS ++ (tzS ++ (monthS ++ checkS))) := by
  rw [artDate_body]; rfl

/-- **`artDate` reads a date-time as `dateValue` does**, if it returns. 0 for none, 1 with the seconds in `xValue`, 2
only for seconds past `2 ^ 41`. Only the scratch words change. -/
theorem artDate_ok (o : Oracle σ) {A : Word} {s1 : PancakeState σ} (hA : Area ArticleProg.ofs A s1)
    (hD : ArtDom A s1.memaddrs) (hcode : ArtCode s1.code) (hP : Pows s1.memory A) (hb : s1.memory (at_ A aBroken) = 0)
    {a : Bytes} (hlen : a.length ≤ artMax) (hin : InputAt s1.memory s1.memaddrs s1.be A a) {S E : Nat} (hSE : S ≤ E)
    (hE : E ≤ a.length) (hs : s1.locals "s" = some (BitVec.ofNat 64 S))
    (he : s1.locals "e" = some (BitVec.ofNat 64 E)) :
    ∃ body, Lower.lower (gd (ArticleProg.artDate .none)) = some body ∧
      SafeR o (fun s => s = s1) body (DateRet A a S E s1.memory) fun _ => False := by
  refine body_of ?_
  show FragR o _ (guardL (ArticleProg.artDate .none).body) _ _
  rw [artDate_split]
  refine fragR_conseq (P0 := RunF s1 [("s", BitVec.ofNat 64 S), ("e", BitVec.ofNat 64 E)] (· = s1.memory)) ?_
    (entry_two hs he) fun _ h => h
  have hCa : parenAt a S E ≤ a.length := Nat.le_trans (paren_le a hSE hE) hE
  have hL3 : LowKK (monthS ++ checkS) := lowK_any _ (k := .skip) rfl
  have hL2 : LowKK (tzS ++ (monthS ++ checkS)) := lowK_any _ (k := .skip) rfl
  have hL1 : LowKK (wordsS ++ (tzS ++ (monthS ++ checkS))) := lowKK_append lowKK_wordsS hL2
  refine fragR_append (front_frag o hA hD hcode hlen hin hb hSE hE) (fragR_exists hL1 fun f => ?_)
  refine fragR_pure (DFrame A s1.memory f.m ∧ FrontOk a S E f.ts f.hw f.wk) (fun u h => h.2) hL1 fun ⟨hf, hok⟩ => ?_
  refine fragR_conseq (P0 := RunF s1 (frontL S E A (parenAt a S E) f) (· = f.m)) ?_ (fun u h => h.1) fun _ h => h
  obtain ⟨-, hTC, hW⟩ := hok
  obtain ⟨W, hWr, hdv⟩ : ∃ W : Option Bytes, (W = none ∧ f.hw = 0 ∨ ∃ name, W = some name ∧ f.hw = 1 ∧
      f.wk = ((indexOf name dayNames 0).map (· + 1)).getD 0) ∧
      ArticleSpec.dateValue (seg a S E) = dvRest W (tokens (seg a f.ts (parenAt a S E))) := by
    rcases hW with ⟨h0, -, e⟩ | ⟨h1, name, hwk, e⟩
    · exact ⟨none, .inl ⟨rfl, h0⟩, e⟩
    · exact ⟨some name, .inr ⟨name, rfl, h1, hwk⟩, e⟩
  refine fragR_append (words_frag o hA hD hcode hlen hin hb hCa f hf hTC hWr hdv) (fragR_exists hL2 fun g => ?_)
  refine fragR_pure (DFrame A s1.memory g.m ∧ WordsOk a S E (parenAt a S E) f g) (fun u h => h.2) hL2
    fun ⟨hg, hwo⟩ => ?_
  refine fragR_conseq (P0 := RunF s1 (wordsL g ++ frontL S E A (parenAt a S E) f) (· = g.m)) ?_ (fun u h => h.1)
    fun _ h => h
  obtain ⟨hp3, hmo1, hmo12, W', d, mth, y, hWr', hd, hm, hy, hdv'⟩ := hwo
  refine fragR_append (tz_frag o hA hcode hlen hin hb hP hCa f g hg hp3 hd hm hmo1 hy hdv')
    (fragR_exists hL3 fun q => ?_)
  refine fragR_pure _ (fun u h => h.2) hL3 fun ⟨hh, hmi, hse, ho1, ho2, hdq⟩ => ?_
  exact fragR_conseq (check_frag o hA hD hcode hb hP f g hg hmo1 hmo12 hWr' _ q hh hmi hse ho1 ho2 hdq)
    (fun u h => h.1) fun _ h => h

end DN.News.ArticleDateOk
