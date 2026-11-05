-- SPDX-License-Identifier: AGPL-3.0-or-later
import DN.News.ArticleList
import DN.News.ArticleDateOk

/-!
# DN.News.ArticleListRun

The article's list functions as the program holds them. If they return, they read Newsgroups', Distribution's and
Path's elements as `DN.News.ArticleList` models them.
-/

namespace DN.News.ArticleListRun

open DN.Compiler DN.Compiler.Wp DN.Compiler.WpRet DN.Compiler.Frag DN.News.AbnfProg
open DN.News.AbnfSets DN.News.FunRun DN.News.AbnfLeaves DN.News.ArticleRun DN.News.ArticleScan
open DN.News.ArticleList DN.News.ArticleDateRun DN.News.ArticleDateOk
open DN.News.ScanRun (at_ at_add vals_lookup without Fresh)
open DN.News.FramerCode (bw ev_var bw_ne0 bw_eq0)
open DN.News.AbnfComment (ev_inc)
open DN.News.ArticleCal (ev_mulc)
open DN.News.ArticleProg (artMax guardL guardS ifs readIn wd isGap setW codes)
open DN.News.ArticleLines (seg seg_succ seg_length)
open DN.News.ArticleSpec (Bytes reserved)
open Syntax (v n eEq eLt eLe eAnd eAdd eSub eMul)

variable {σ : Type}

/-! ## Bytes compared -/

/-- One byte's test of a name compared as written. -/
def byteG (o : Nat) : Syntax.PExpr → Nat × Nat → Syntax.PExpr := testG id o

/-- **The bytes' tests**, the bytes from `o` known: true when each is the letter. -/
theorem bytes_fold {P : PancakeState σ → Prop} {A : Word} (hA : ∀ u, P u → u.locals "a" = some A) {o : Nat}
    (ho : 0 < o) (tb : Nat → BitVec 8) {K : Nat}
    (hb : ∀ i u, i < K → P u → memLoadByte u.memory u.memaddrs u.be (at_ A (o + i)) = some (tb i))
    (cs : List Nat) (k0 : Nat) (acc : Syntax.PExpr) (Eacc : PancakeExp) (b0 : Bool)
    (hl : Lower.lowerExp acc = some Eacc) (hv : ∀ u, P u → eval u Eacc = some (bw b0)) (hc : ∀ c ∈ cs, c < 2 ^ 64)
    (hK : k0 + cs.length ≤ K) : ∃ E, Lower.lowerExp ((cs.zipIdx k0).foldl (byteG o) acc) = some E ∧ ∀ u, P u →
      eval u E = some (bw (b0 && (cs.zipIdx k0).all fun ci => decide ((tb ci.2).toNat = ci.1))) :=
  tests_fold hA ho tb hb (wrap := id) (W := id) (f := fun B => B) (fun _ _ h => h) (fun _ _ _ _ h => h)
    (fun _ hB => Nat.lt_trans hB (by decide)) cs k0 acc Eacc b0 hl hv hc hK

/-- A name's test as `artElem` writes it: the length in local `x`, then the bytes from `o`. -/
def cmpE (x : String) (o : Nat) (s : String) : Syntax.PExpr :=
  eAnd (eEq (v x) (n s.length)) ((codes s).zipIdx.foldl (byteG o) (n 1))

/-- The name's bytes as `ascii` makes them: each code below 256. -/
def Ascii (s : String) : Prop := ∀ c ∈ codes s, c < 256

theorem codes_ascii (s : String) :
    DN.News.CommandSpec.ascii s = (codes s).map (BitVec.ofNat 8 ·) := by
  simp [DN.News.CommandSpec.ascii, codes]

/-- **A name's test**: true exactly when the bytes `C` are the name. `C`'s length is kept as at most `K + 1`, its
first `K` bytes from `o`. -/
theorem cmp_eval {P : PancakeState σ → Prop} {A : Word} (hA : ∀ u, P u → u.locals "a" = some A) {o : Nat}
    (ho : 0 < o) {x : String} {K : Nat} {C : Bytes} (hK : K < 2 ^ 63)
    (hx : ∀ u, P u → u.locals x = some (BitVec.ofNat 64 (min (K + 1) C.length))) (tb : Nat → BitVec 8)
    (hb : ∀ i u, i < K → P u → memLoadByte u.memory u.memaddrs u.be (at_ A (o + i)) = some (tb i))
    (htb : ∀ i, i < K → i < C.length → tb i = C[i]!) {s : String} (hs : Ascii s) (hsK : (codes s).length ≤ K) :
    ∃ E, Lower.lowerExp (cmpE x o s) = some E ∧ ∀ u, P u →
      eval u E = some (bw (C == DN.News.CommandSpec.ascii s)) := by
  have hcs : ∀ c ∈ codes s, c < 2 ^ 64 := fun c hc => Nat.lt_trans (hs c hc) (by decide)
  obtain ⟨Eb, hEb, hEbv⟩ := bytes_fold hA ho tb hb (codes s) 0 (n 1) (.const (BitVec.ofNat 64 1)) true rfl
    (fun _ _ => rfl) hcs (by omega)
  have hl : (codes s).length = s.length := by simp [codes]
  have hEb' : Lower.lowerExp (List.foldl (byteG o) (Syntax.PExpr.const 1) (codes s).zipIdx) = some Eb := hEb
  refine ⟨.op .and_ (.cmp .equal (.var x) (.const (BitVec.ofNat 64 s.length))) Eb, by
    simp only [cmpE, eAnd, eEq, v, n, Lower.lowerExp]; rw [hEb'], fun u h => ?_⟩
  rw [FramerCode.eval_and (FramerCode.eval_eq (by omega) (by omega) (ev_var (hx u h)) rfl) (hEbv u h)]
  congr 2
  rw [codes_ascii s, Bool.true_and]
  by_cases hlen : C.length = s.length
  · rw [decide_eq_true (by omega)]
    simp only [Bool.true_and]
    apply Bool.eq_iff_iff.2
    rw [List.all_eq_true, beq_iff_eq]
    constructor
    · intro hall
      apply List.ext_getElem (by simp [hlen, hl]) fun i h1 h2 => ?_
      have hi : i < (codes s).length := by simpa using h2
      have := hall ((codes s)[i], i) (List.mem_zipIdx_iff_getElem?.2 (by simp [hi]))
      simp only [decide_eq_true_eq] at this
      rw [List.getElem_map, ← this, ← getElem!_pos C i h1, ← htb i (by omega) h1]
      simp
    · intro heq ci hci
      obtain ⟨c, i⟩ := ci
      have hci' := List.mem_zipIdx_iff_getElem?.1 hci
      have hi : i < (codes s).length := by
        rcases List.getElem?_eq_some_iff.1 hci' with ⟨h, -⟩; exact h
      have hc : (codes s)[i] = c := by rw [List.getElem?_eq_getElem hi] at hci'; exact Option.some.inj hci'
      have hiC : i < C.length := by omega
      simp only [decide_eq_true_eq]
      rw [htb i (by omega) hiC, getElem!_pos C i hiC]
      have : C[i] = ((codes s).map (BitVec.ofNat 8 ·))[i]'(by simpa using hi) := by
        simp only [heq]
      have hcm : c ∈ codes s := by rw [← hc]; exact List.getElem_mem hi
      rw [this, List.getElem_map, hc, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (hs c hcm)]
  · have h1 : decide (min (K + 1) C.length = s.length) = false := decide_eq_false (by omega)
    rw [h1, Bool.false_and]
    symm; rw [beq_eq_false_iff_ne]
    intro e; apply hlen; rw [e]; simp [hl]

/-! ## `artElem`'s memory -/

theorem xElem_eq : ArticleProg.xElem = 506680 := rfl
theorem xComp_eq : ArticleProg.xComp = 506744 := rfl

/-- `artElem`'s state over an element's bytes: the memory, the bytes taken, the check of reserved names. -/
structure MS where
  m : Word → Word
  len : Nat
  r : RS

/-- One byte of the element: its first 64 bytes from `xElem`, its component's first 8 from `xComp`. -/
def msStep (A : Word) (be : Bool) (s : MS) (b : BitVec 8) : MS :=
  let m1 := if s.len < 64 then DN.Compiler.Bytes.putByte s.m be (at_ A (ArticleProg.xElem + s.len)) b else s.m
  let m2 := if b == DN.News.FrameSpec.DOT then m1
    else if s.r.comp.length < 8 then DN.Compiler.Bytes.putByte m1 be (at_ A (ArticleProg.xComp + s.r.comp.length)) b
    else m1
  ⟨m2, s.len + 1, rsStep s.r b⟩

/-- The state after the element's bytes `E`. -/
def msOf (A : Word) (be : Bool) (m0 : Word → Word) (E : Bytes) : MS := E.foldl (msStep A be) ⟨m0, 0, rs0⟩

theorem msOf_snoc (A : Word) (be : Bool) (m0 : Word → Word) (E : Bytes) (b : BitVec 8) :
    msOf A be m0 (E ++ [b]) = msStep A be (msOf A be m0 E) b := by
  unfold msOf; rw [List.foldl_append]; rfl

theorem fold_len (A : Word) (be : Bool) : ∀ (E : Bytes) (t : MS), (E.foldl (msStep A be) t).len = t.len + E.length
  | [], _ => rfl
  | b :: E, t => by rw [List.foldl_cons, fold_len A be E]; simp [msStep]; omega

theorem fold_r (A : Word) (be : Bool) : ∀ (E : Bytes) (t : MS), (E.foldl (msStep A be) t).r = E.foldl rsStep t.r
  | [], _ => rfl
  | b :: E, t => by rw [List.foldl_cons, fold_r A be E]; rfl

theorem msOf_len (A : Word) (be : Bool) (m0 : Word → Word) (E : Bytes) : (msOf A be m0 E).len = E.length := by
  unfold msOf; rw [fold_len]; simp

theorem msOf_r (A : Word) (be : Bool) (m0 : Word → Word) (E : Bytes) : (msOf A be m0 E).r = E.foldl rsStep rs0 :=
  fold_r A be E _

/-- The words `artElem` writes. -/
def elemScratch (A : Word) (x : Word) : Prop :=
  (∃ k, k < 9 ∧ x = at_ A (ArticleProg.xElem + 8 * k)) ∨ x = at_ A ArticleProg.xElemLen ∨
    x = at_ A ArticleProg.xElemRes

theorem step_frame {A : Word} (hA8 : A.toNat % 8 = 0) (be : Bool) {x : Word} (hx : ¬elemScratch A x) (t : MS)
    (b : BitVec 8) : (msStep A be t b).m x = t.m x := by
  have hput : ∀ (m : Word → Word) (k : Nat), k < 72 →
      DN.Compiler.Bytes.putByte m be (at_ A (ArticleProg.xElem + k)) b x = m x := fun m k hk => by
    simp only [DN.Compiler.Bytes.putByte, DN.News.ScanRun.align_at hA8]
    rw [if_neg]; intro e; apply hx; refine .inl ⟨k / 8, by omega, ?_⟩
    rw [e]; congr 1; rw [xElem_eq]; omega
  have hcomp : ∀ k, ArticleProg.xComp + k = ArticleProg.xElem + (64 + k) := fun k => by
    rw [xComp_eq, xElem_eq]; omega
  simp only [msStep]
  split <;> split <;> (try split) <;>
    (try simp only [hcomp]) <;> (repeat rw [hput _ _ (by omega)])

theorem fold_frame {A : Word} (hA8 : A.toNat % 8 = 0) (be : Bool) {x : Word} (hx : ¬elemScratch A x) :
    ∀ (E : Bytes) (t : MS), (E.foldl (msStep A be) t).m x = t.m x
  | [], _ => rfl
  | b :: E, t => by rw [List.foldl_cons, fold_frame hA8 be hx E, step_frame hA8 be hx]

theorem get!_snoc_lt {P : Bytes} {b : BitVec 8} {i : Nat} (h : i < P.length) : (P ++ [b])[i]! = P[i]! := by
  rw [getElem!_pos (P ++ [b]) i (by simp; omega), getElem!_pos P i h, List.getElem_append_left h]

theorem get!_snoc_eq {P : Bytes} {b : BitVec 8} : (P ++ [b])[P.length]! = b := by
  rw [getElem!_pos (P ++ [b]) P.length (by simp)]; simp

/-- Bytes put, read back: the element's from `xElem`, the component's from `xComp`. -/
def BytesAt (A : Word) (dm : Word → Bool) (be : Bool) (o K : Nat) (B : Bytes) (m : Word → Word) : Prop :=
  ∀ i, i < K → i < B.length → memLoadByte m dm be (at_ A (o + i)) = some B[i]!

theorem bytesAt_put {A : Word} {dm : Word → Bool} {be : Bool} {o K : Nat} {B : Bytes} {m : Word → Word}
    (h : BytesAt A dm be o K B m) {w : Word} (hw : ∀ i, i < K → i < B.length → at_ A (o + i) ≠ w) (b : BitVec 8) :
    BytesAt A dm be o K B (DN.Compiler.Bytes.putByte m be w b) := fun i hi hl => by
  rw [DN.Compiler.Bytes.load_putByte_diff _ _ _ _ _ _ (hw i hi hl)]; exact h i hi hl

theorem bytesAt_snoc {A : Word} {dm : Word → Bool} {be : Bool} {o K : Nat} {B : Bytes} {m : Word → Word}
    (h : BytesAt A dm be o K B m) (hk : B.length < K) (hK : o + K < 2 ^ 64)
    (hd : dm (byteAlign (at_ A (o + B.length))) = true) (b : BitVec 8) :
    BytesAt A dm be o K (B ++ [b]) (DN.Compiler.Bytes.putByte m be (at_ A (o + B.length)) b) := fun i hi hl => by
  by_cases hi' : i < B.length
  · rw [DN.Compiler.Bytes.load_putByte_diff _ _ _ _ _ _ (DN.News.ScanRun.at_ne (by omega) (by omega) (by omega)),
      get!_snoc_lt hi']
    exact h i hi hi'
  · have e : i = B.length := by simp at hl; omega
    subst e; rw [DN.Compiler.Bytes.load_putByte_same _ _ _ _ _ hd, get!_snoc_eq]

theorem bytesAt_full {A : Word} {dm : Word → Bool} {be : Bool} {o K : Nat} {B : Bytes} {m : Word → Word}
    (h : BytesAt A dm be o K B m) (hk : K ≤ B.length) (b : BitVec 8) : BytesAt A dm be o K (B ++ [b]) m :=
  fun i hi hl => by rw [get!_snoc_lt (by omega)]; exact h i hi (by omega)

/-- **One byte of the element**: its bytes from `xElem` and its component's from `xComp` kept so. -/
theorem step_mem {A : Word} {dm : Word → Bool} {be : Bool}
    (hdm : ∀ i, i < 72 → dm (byteAlign (at_ A (ArticleProg.xElem + i))) = true) {t : MS} {P : Bytes}
    (hl : t.len = P.length) (hE : BytesAt A dm be ArticleProg.xElem 64 P t.m)
    (hC : BytesAt A dm be ArticleProg.xComp 8 t.r.comp t.m) (b : BitVec 8) :
    BytesAt A dm be ArticleProg.xElem 64 (P ++ [b]) (msStep A be t b).m ∧
      BytesAt A dm be ArticleProg.xComp 8 (msStep A be t b).r.comp (msStep A be t b).m := by
  have hcomp : ∀ k, ArticleProg.xComp + k = ArticleProg.xElem + (64 + k) := fun k => by
    rw [xComp_eq, xElem_eq]; omega
  have hX := xElem_eq
  have hne : ∀ i j, i < 72 → j < 72 → i ≠ j → at_ A (ArticleProg.xElem + i) ≠ at_ A (ArticleProg.xElem + j) :=
    fun i j hi hj e => DN.News.ScanRun.at_ne (by omega) (by omega) (by omega)
  -- the element's byte
  let m1 := if t.len < 64 then DN.Compiler.Bytes.putByte t.m be (at_ A (ArticleProg.xElem + t.len)) b else t.m
  have hE1 : BytesAt A dm be ArticleProg.xElem 64 (P ++ [b]) m1 := by
    show BytesAt _ _ _ _ _ _ (if t.len < 64 then _ else _)
    split
    · rw [hl]; exact bytesAt_snoc hE (by omega) (by omega) (hdm _ (by omega)) b
    · exact bytesAt_full hE (by omega) b
  have hC1 : BytesAt A dm be ArticleProg.xComp 8 t.r.comp m1 := by
    show BytesAt _ _ _ _ _ _ (if t.len < 64 then _ else _)
    split
    · refine bytesAt_put hC (fun i hi _ => ?_) b
      rw [hcomp]; exact hne _ _ (by omega) (by omega) (by omega)
    · exact hC
  show BytesAt _ _ _ _ _ _ (if b == DN.News.FrameSpec.DOT then m1 else _) ∧
    BytesAt _ _ _ _ _ (rsStep t.r b).comp (if b == DN.News.FrameSpec.DOT then m1 else _)
  unfold rsStep
  cases hb : b == DN.News.FrameSpec.DOT
  · simp only [Bool.false_eq_true, if_false]
    split
    · rename_i hc8
      refine ⟨bytesAt_put hE1 (fun i hi _ => ?_) b, ?_⟩
      · rw [hcomp]; exact hne _ _ (by omega) (by omega) (by omega)
      · exact bytesAt_snoc hC1 hc8 (by rw [xComp_eq]; decide) (by rw [hcomp]; exact hdm _ (by omega)) b
    · exact ⟨hE1, bytesAt_full hC1 (by omega) b⟩
  · simp only [if_true]
    exact ⟨hE1, fun i _ hi => by simp at hi⟩

theorem fold_mem {A : Word} {dm : Word → Bool} {be : Bool}
    (hdm : ∀ i, i < 72 → dm (byteAlign (at_ A (ArticleProg.xElem + i))) = true) :
    ∀ (E P : Bytes) (t : MS), t.len = P.length → BytesAt A dm be ArticleProg.xElem 64 P t.m →
      BytesAt A dm be ArticleProg.xComp 8 t.r.comp t.m →
      BytesAt A dm be ArticleProg.xElem 64 (P ++ E) (E.foldl (msStep A be) t).m ∧
        BytesAt A dm be ArticleProg.xComp 8 (E.foldl (msStep A be) t).r.comp (E.foldl (msStep A be) t).m
  | [], P, t, _, h1, h2 => by simpa using And.intro h1 h2
  | b :: E, P, t, hl, h1, h2 => by
    obtain ⟨g1, g2⟩ := step_mem hdm hl h1 h2 b
    have := fold_mem hdm E (P ++ [b]) (msStep A be t b) (by simp [msStep, hl]) g1 g2
    rw [List.foldl_cons]; simpa using this

/-- **The element's state read back**: its first 64 bytes from `xElem`, its last component's first 8 from `xComp`. -/
theorem msOf_mem {A : Word} {dm : Word → Bool} {be : Bool}
    (hdm : ∀ i, i < 72 → dm (byteAlign (at_ A (ArticleProg.xElem + i))) = true) (m0 : Word → Word) (E : Bytes) :
    BytesAt A dm be ArticleProg.xElem 64 E (msOf A be m0 E).m ∧
      BytesAt A dm be ArticleProg.xComp 8 (msOf A be m0 E).r.comp (msOf A be m0 E).m := by
  have := fold_mem (be := be) hdm E [] ⟨m0, 0, rs0⟩ rfl (fun _ _ h => by simp at h) (fun _ _ h => by simp [rs0] at h)
  simpa using this

/-! ## `artElem`'s body -/

/-- A name's test of the component, from `xComp`. -/
abbrev compE (s : String) : Syntax.PExpr := cmpE "cl" ArticleProg.xComp s

/-- A component ended: the name reserved if it says so, the next component's start. -/
def doneS : List Syntax.PStmt :=
  [ifs (or2 (or2 (compE "all") (compE "ctl"))
      (eAnd (v "first") (or2 (compE "example") (or2 (compE "to") (compE "control"))))) [.assign "res" (n 1)],
   .assign "first" (n 0), .assign "cl" (n 0)]

/-- A byte of the element taken: its first 64 kept, and its component's first 8, or the component ended. -/
def takeS : List Syntax.PStmt :=
  [ifs (eLt (v "ln") (n 64)) [.storeb (eAdd (Syntax.atOff (v "a") ArticleProg.xElem) (v "ln")) (v "b")],
   ifs (eLt (v "ln") (n 65)) [inc "ln"],
   .ite (eEq (v "b") (n 46)) doneS
     [ifs (eLt (v "cl") (n 8)) [.storeb (eAdd (Syntax.atOff (v "a") ArticleProg.xComp) (v "cl")) (v "b")],
      ifs (eLt (v "cl") (n 9)) [inc "cl"]],
   inc "i"]

/-- `artElem`'s loop body. -/
def elemBody : List Syntax.PStmt :=
  [.ite (eLt (v "i") (v "e"))
    (readIn "b" "i" ++ [.ite (eEq (v "b") (v "sep")) [.assign "go" (n 0), inc "i"]
      [.ite (isGap (v "b")) [inc "i"] takeS]])
    [.assign "go" (n 0)]]

theorem artElem_body : guardL ArticleProg.artElem.body =
    [areaAt ArticleProg.ofs, .dec "i" (v "p"), .dec "ln" (n 0), .dec "cl" (n 0), .dec "first" (n 1),
     .dec "res" (n 0), .dec "go" (n 1), .while (v "go") elemBody] ++ doneS ++
    [ifs (or2 (cmpE "ln" ArticleProg.xElem "poster") (cmpE "ln" ArticleProg.xElem "junk")) [.assign "res" (n 1)],
     setW ArticleProg.xElemLen (v "ln"), setW ArticleProg.xElemRes (v "res"), .ret (v "i")] := by
  rfl

/-! ## A component ended -/

theorem bnat_bw (b : Bool) : BitVec.ofNat 64 (bnat b) = bw b := by cases b <;> rfl

/-- A local set to the value it holds. -/
theorem runF_same {s0 u : PancakeState σ} {L : List (String × Value)} {F : (Word → Word) → Prop} (h : RunF s0 L F u)
    {x : String} {w : Value} (hx : L.lookup x = some w) : RunF s0 ((x, w) :: without x L) F u :=
  ⟨⟨fun q hq => by
      rcases List.mem_cons.1 hq with rfl | hq
      · exact vals_lookup h.1.vals hx
      · exact h.1.vals q (List.mem_filter.1 hq).1, h.1.memaddrs, h.1.base, h.1.code, h.1.be⟩, h.2⟩

theorem lower_or2 {x y : Syntax.PExpr} {X Y : PancakeExp} (hx : Lower.lowerExp x = some X)
    (hy : Lower.lowerExp y = some Y) : Lower.lowerExp (or2 x y) = some (FramerCode.or2E X Y) := by
  simp only [or2, eLt, eAdd, n, Lower.lowerExp, hx, hy]; rfl

theorem lower_and {x y : Syntax.PExpr} {X Y : PancakeExp} (hx : Lower.lowerExp x = some X)
    (hy : Lower.lowerExp y = some Y) : Lower.lowerExp (eAnd x y) = some (.op .and_ X Y) := by
  simp only [eAnd, Lower.lowerExp, hx, hy]

/-- The bytes from `o` as one read loads them, each in the domain. -/
def loadsAt (m : Word → Word) (dm : Word → Bool) (be : Bool) (A : Word) (o : Nat) : Nat → BitVec 8 :=
  fun i => (memLoadByte m dm be (at_ A (o + i))).getD 0

theorem loadsAt_eq {s1 u : PancakeState σ} {L : List (String × Value)} {M : Word → Word} (h : RunF s1 L (· = M) u)
    {A : Word} {o : Nat} {i : Nat} (hd : s1.memaddrs (byteAlign (at_ A (o + i))) = true) :
    memLoadByte u.memory u.memaddrs u.be (at_ A (o + i)) = some (loadsAt M s1.memaddrs s1.be A o i) := by
  rw [h.2, h.1.memaddrs, h.1.be]; simp only [loadsAt, memLoadByte, hd, if_true, Option.getD_some]

theorem loadsAt_bytes {M : Word → Word} {dm : Word → Bool} {be : Bool} {A : Word} {o K : Nat} {C : Bytes}
    (h : BytesAt A dm be o K C M) : ∀ i, i < K → i < C.length → loadsAt M dm be A o i = C[i]! :=
  fun i hi hl => by simp only [loadsAt, h i hi hl, Option.getD_some]

/-- A local's value read past another's setting. -/
theorem lk_set {L : List (String × Value)} {x y : String} {v w : Value} (hne : y ≠ x) (h : L.lookup y = some w) :
    ((x, v) :: without x L).lookup y = some w := by
  rw [DN.News.ScanRun.lookup_cons_ne hne, DN.News.ScanRun.lookup_without hne L, h]

/-- **A component ended**: the name reserved if the component says so, the next component's start. -/
theorem done_frag (o : Oracle σ) {s1 : PancakeState σ} {L : List (String × Value)} {M : Word → Word} {A : Word}
    (hla : L.lookup "a" = some A) {C : Bytes} {fst res : Bool}
    (hcl : L.lookup "cl" = some (BitVec.ofNat 64 (min 9 C.length)))
    (hf : L.lookup "first" = some (BitVec.ofNat 64 (bnat fst)))
    (hr : L.lookup "res" = some (BitVec.ofNat 64 (bnat res)))
    (hC : BytesAt A s1.memaddrs s1.be ArticleProg.xComp 8 C M)
    (hdm : ∀ i, i < 8 → s1.memaddrs (byteAlign (at_ A (ArticleProg.xComp + i))) = true) :
    Frag o doneS (RunF s1 L (· = M))
      (RunF s1 (("cl", BitVec.ofNat 64 0) :: without "cl" (("first", BitVec.ofNat 64 0) :: without "first"
        (("res", BitVec.ofNat 64 (bnat (res || compRes fst C))) :: without "res" L))) (· = M)) := by
  have hb : ∀ i u, i < 8 → RunF s1 L (· = M) u → memLoadByte u.memory u.memaddrs u.be
      (at_ A (ArticleProg.xComp + i)) = some (loadsAt M s1.memaddrs s1.be A ArticleProg.xComp i) :=
    fun i u hi h => loadsAt_eq h (hdm i hi)
  have hce : ∀ s : String, Ascii s → (codes s).length ≤ 8 → ∃ E, Lower.lowerExp (compE s) = some E ∧
      ∀ u, RunF s1 L (· = M) u → eval u E = some (bw (C == DN.News.CommandSpec.ascii s)) := fun s hs hl =>
    cmp_eval (fun u h => vals_lookup h.1.vals hla) (by decide) (K := 8) (by decide)
      (fun u h => vals_lookup h.1.vals hcl)
      _ hb (loadsAt_bytes hC) hs hl
  obtain ⟨E1, h1, v1⟩ := hce "all" (by unfold Ascii; decide) (by decide)
  obtain ⟨E2, h2, v2⟩ := hce "ctl" (by unfold Ascii; decide) (by decide)
  obtain ⟨E3, h3, v3⟩ := hce "example" (by unfold Ascii; decide) (by decide)
  obtain ⟨E4, h4, v4⟩ := hce "to" (by unfold Ascii; decide) (by decide)
  obtain ⟨E5, h5, v5⟩ := hce "control" (by unfold Ascii; decide) (by decide)
  have hcond := lower_or2 (lower_or2 h1 h2) (lower_and (x := v "first") rfl (lower_or2 h3 (lower_or2 h4 h5)))
  refine frag_append (xs := [_]) (cond_set o hr hcond rfl (b := compRes fst C)
    (L' := ("res", BitVec.ofNat 64 (bnat (res || compRes fst C))) :: without "res" L)
    (fun u h => by
      rw [FramerCode.eval_or2 (FramerCode.eval_or2 (v1 u h) (v2 u h)) (FramerCode.eval_and
        (by rw [ev_var (vals_lookup h.1.vals hf), bnat_bw])
        (FramerCode.eval_or2 (v3 u h) (FramerCode.eval_or2 (v4 u h) (v5 u h))))]
      unfold compRes; simp only [Bool.or_assoc])
    (vx := BitVec.ofNat 64 1) (fun _ _ => rfl)
    (fun hb u h => by rw [hb, Bool.or_true]; exact h)
    fun hb u h => by rw [hb, Bool.or_false]; exact runF_same h hr) ?_
  refine frag_append (xs := [_]) (runF_set o rfl (lk_set (by decide) hf) (v := BitVec.ofNat 64 0) fun _ _ => rfl) ?_
  exact runF_set o rfl (lk_set (by decide) (lk_set (by decide) hcl)) (v := BitVec.ofNat 64 0) fun _ _ => rfl

/-! ## Bounded writes and counts -/

/-- **A byte put below a bound**: at `off + n` if the count `n` is below `K`. The local keeps at most `K + 1`. -/
theorem storeCap_frag (o : Oracle σ) {s1 : PancakeState σ} {L : List (String × Value)} {M : Word → Word} {A : Word}
    (hla : L.lookup "a" = some A) {x : String} {K cnt off : Nat} (hK : K < 2 ^ 62)
    (hoff0 : (off == 0) = false) (hx : L.lookup x = some (BitVec.ofNat 64 (min (K + 1) cnt))) {b : BitVec 8}
    (hbv : L.lookup "b" = some (BitVec.ofNat 64 b.toNat))
    (hdm : ∀ i, i < K → s1.memaddrs (byteAlign (at_ A (off + i))) = true) :
    Frag o [ifs (eLt (v x) (n K)) [.storeb (eAdd (Syntax.atOff (v "a") off) (v x)) (v "b")]] (RunF s1 L (· = M))
      (RunF s1 L (· = if cnt < K then DN.Compiler.Bytes.putByte M s1.be (at_ A (off + cnt)) b else M)) := by
  have hlt : ∀ u, RunF s1 L (· = M) u →
      eval u (.cmp .less (.var x) (.const (BitVec.ofNat 64 K))) = some (bw (decide (cnt < K))) := fun u h => by
    rw [FramerCode.eval_lt (by omega) (by omega) (ev_var (vals_lookup h.1.vals hx)) rfl]
    congr 2; apply decide_eq_decide.2; omega
  have hst : Lower.lowerExp (eAdd (Syntax.atOff (v "a") off) (v x)) =
      some (.op .add (.op .add (.var "a") (.const (BitVec.ofNat 64 off))) (.var x)) := by
    rw [atOff_eq hoff0]; rfl
  have hlk : LowKK [.storeb (eAdd (Syntax.atOff (v "a") off) (v x)) (v "b")] :=
    lowKK_one rfl (a := .storeByte _ (.var "b")) (by simp only [Lower.lowerStmt1]; rw [hst]; rfl)
  by_cases hc : cnt < K
  · refine DN.News.ArticleScan.frag_ifT o rfl hlk lowKK_nil rfl rfl (runF_clock _ _ _)
      (fun u h => (hlt u h).trans (by rw [bw_t hc])) ?_
    refine storeb_frag o hst rfl (runF_clock _ _ _) fun u h => ⟨at_ A (off + cnt), _, by
      simp only [eval, vals_lookup h.1.vals hla, vals_lookup h.1.vals hx]
      rw [← at_add, Nat.min_eq_right (by omega)]; rfl, ev_var (vals_lookup h.1.vals hbv), ?_, ?_⟩
    · rw [h.1.memaddrs]; exact hdm cnt hc
    · refine ⟨⟨h.1.vals, h.1.memaddrs, h.1.base, h.1.code, h.1.be⟩, ?_⟩
      show DN.Compiler.Bytes.putByte u.memory u.be (at_ A (off + cnt)) _ = _
      rw [h.2, h.1.be, DN.News.ArticleRun.setWidth_byte, if_pos hc]
  · exact DN.News.ArticleScan.frag_ifF o rfl hlk lowKK_nil rfl rfl (runF_clock _ _ _)
      (fun u h => (hlt u h).trans (by rw [bw_f hc])) (frag_nil o fun u h => by rw [if_neg hc]; exact h)

/-- **A count kept as at most `K`**, one more. -/
theorem incCap_frag (o : Oracle σ) {s1 : PancakeState σ} {L : List (String × Value)} {F : (Word → Word) → Prop}
    {x : String} {K cnt : Nat} (hK : K < 2 ^ 63) (hx : L.lookup x = some (BitVec.ofNat 64 (min K cnt))) :
    Frag o [ifs (eLt (v x) (n K)) [inc x]] (RunF s1 L F)
      (RunF s1 ((x, BitVec.ofNat 64 (min K (cnt + 1))) :: without x L) F) := by
  refine cond_set o hx rfl rfl (b := decide (cnt < K)) (fun u h => by
      rw [FramerCode.eval_lt (by omega) hK (ev_var (vals_lookup h.1.vals hx)) rfl]
      congr 2; apply decide_eq_decide.2; omega)
    (vx := BitVec.ofNat 64 (min K cnt + 1)) (fun u h => ev_inc (vals_lookup h.1.vals hx))
    (fun hb u h => by rw [show min K (cnt + 1) = min K cnt + 1 by have := of_decide_eq_true hb; omega]; exact h)
    fun hb u h => by
      rw [show min K (cnt + 1) = min K cnt by have := of_decide_eq_false hb; omega]; exact runF_same h hx

/-! ## A byte of the element taken -/

/-- `artElem`'s locals in its loop: the flag, the check of reserved names, the counts, the place. -/
def elemL (P E S : Nat) (A : Word) (g i : Nat) (t : MS) : List (String × Value) :=
  [("go", BitVec.ofNat 64 g), ("res", BitVec.ofNat 64 (bnat t.r.res)), ("first", BitVec.ofNat 64 (bnat t.r.first)),
   ("cl", BitVec.ofNat 64 (min 9 t.r.comp.length)), ("ln", BitVec.ofNat 64 (min 65 t.len)), ("i", BitVec.ofNat 64 i),
   ("a", A), ("p", BitVec.ofNat 64 P), ("e", BitVec.ofNat 64 E), ("sep", BitVec.ofNat 64 S)]

theorem xElem_ne0 : (ArticleProg.xElem == 0) = false := by rw [xElem_eq]; rfl
theorem xComp_ne0 : (ArticleProg.xComp == 0) = false := by rw [xComp_eq]; rfl

theorem comp_dm {A : Word} {dm : Word → Bool}
    (hdm : ∀ i, i < 72 → dm (byteAlign (at_ A (ArticleProg.xElem + i))) = true) :
    ∀ i, i < 8 → dm (byteAlign (at_ A (ArticleProg.xComp + i))) = true := fun i hi => by
  rw [show ArticleProg.xComp + i = ArticleProg.xElem + (64 + i) by rw [xComp_eq, xElem_eq]; omega]
  exact hdm _ (by omega)

/-- **A byte of the element taken**, neither a gap nor the separator. -/
theorem take_frag (o : Oracle σ) {s1 : PancakeState σ} {P E S : Nat} {A : Word} {j : Nat} {t : MS} {b : BitVec 8}
    (hdm : ∀ i, i < 72 → s1.memaddrs (byteAlign (at_ A (ArticleProg.xElem + i))) = true)
    (hC : BytesAt A s1.memaddrs s1.be ArticleProg.xComp 8 t.r.comp t.m) :
    Frag o takeS (RunF s1 (("b", BitVec.ofNat 64 b.toNat) :: elemL P E S A 1 j t) (· = t.m))
      (RunF s1 (("b", BitVec.ofNat 64 b.toNat) :: elemL P E S A 1 (j + 1) (msStep A s1.be t b))
        (· = (msStep A s1.be t b).m)) := by
  have hX := xElem_eq
  have hcomp : ∀ k, ArticleProg.xComp + k = ArticleProg.xElem + (64 + k) := fun k => by
    rw [xComp_eq, xElem_eq]; omega
  let m1 := if t.len < 64 then DN.Compiler.Bytes.putByte t.m s1.be (at_ A (ArticleProg.xElem + t.len)) b else t.m
  have hC1 : BytesAt A s1.memaddrs s1.be ArticleProg.xComp 8 t.r.comp m1 := by
    show BytesAt _ _ _ _ _ _ (if t.len < 64 then _ else _)
    split
    · refine bytesAt_put hC (fun i hi _ => ?_) b
      rw [hcomp]; exact DN.News.ScanRun.at_ne (by omega) (by omega) (by omega)
    · exact hC
  refine frag_append (xs := [_]) (storeCap_frag o (M := t.m) rfl (x := "ln") (K := 64) (cnt := t.len)
    (by decide) xElem_ne0 rfl rfl fun i hi => hdm i (by omega)) ?_
  refine frag_append (xs := [_]) (incCap_frag o (x := "ln") (K := 65) (cnt := t.len) (by decide) rfl) ?_
  have hev : ∀ (L : List (String × Value)) (F : (Word → Word) → Prop) u,
      L.lookup "b" = some (BitVec.ofNat 64 b.toNat) → RunF s1 L F u →
      eval u (.cmp .equal (.var "b") (.const (BitVec.ofNat 64 46))) = some (bw (decide (b.toNat = 46))) :=
    fun L F u hl h => FramerCode.eval_eq (Nat.lt_trans b.isLt (by decide)) (by decide)
      (ev_var (vals_lookup h.1.vals hl)) rfl
  by_cases hd : b.toNat = 46
  · have hbD : (b == DN.News.FrameSpec.DOT) = true := by
      rw [ArticleScan.beq_byte]; simpa [DN.News.FrameSpec.DOT] using hd
    refine frag_append (xs := [_]) (DN.News.ArticleScan.frag_ifT o rfl (lowK_any _ (k := .skip) rfl)
      (lowK_any _ (k := .skip) rfl) rfl rfl (runF_clock _ _ _) (fun u h => (hev _ _ u rfl h).trans (by rw [bw_t hd]))
      (done_frag o rfl (C := t.r.comp) (fst := t.r.first) (res := t.r.res) rfl rfl rfl hC1 (comp_dm hdm))) ?_
    have hm : (msStep A s1.be t b).m = m1 := by simp only [msStep, hbD, if_true]; rfl
    have hr : (msStep A s1.be t b).r = ⟨false, t.r.res || compRes t.r.first t.r.comp, []⟩ := by
      simp only [msStep, rsStep, hbD, if_true]
    have hl : (msStep A s1.be t b).len = t.len + 1 := rfl
    refine frag_conseq (set_to o rfl rfl (v := BitVec.ofNat 64 (j + 1)) (fun u h => ev_inc (vals_lookup h.1.vals rfl))
      (l' := ("b", BitVec.ofNat 64 b.toNat) :: elemL P E S A 1 (j + 1) (msStep A s1.be t b)) fun u h => runF_of h (by
        simp only [elemL, hr, hl]
        repeat (refine lookups_cons rfl ?_)
        exact lookups_nil)) (fun _ h => h) fun u h => ⟨h.1, by rw [hm]; exact h.2⟩
  · have hbD : (b == DN.News.FrameSpec.DOT) = false := by
      rw [ArticleScan.beq_byte]; simpa [DN.News.FrameSpec.DOT] using hd
    refine frag_append (xs := [_]) (DN.News.ArticleScan.frag_ifF o rfl (lowK_any _ (k := .skip) rfl)
      (lowK_any _ (k := .skip) rfl) rfl rfl (runF_clock _ _ _) (fun u h => (hev _ _ u rfl h).trans (by rw [bw_f hd]))
      (frag_append (xs := [_]) (storeCap_frag o (M := m1) rfl (x := "cl") (K := 8) (cnt := t.r.comp.length)
        (by decide) xComp_ne0 rfl rfl fun i hi => comp_dm hdm i hi)
        (incCap_frag o (x := "cl") (K := 9) (cnt := t.r.comp.length) (by decide) rfl))) ?_
    have hm : (msStep A s1.be t b).m = if t.r.comp.length < 8 then
        DN.Compiler.Bytes.putByte m1 s1.be (at_ A (ArticleProg.xComp + t.r.comp.length)) b else m1 := by
      simp only [msStep, hbD, Bool.false_eq_true, if_false]; rfl
    have hr : (msStep A s1.be t b).r = { t.r with comp := t.r.comp ++ [b] } := by
      simp only [msStep, rsStep, hbD, Bool.false_eq_true, if_false]
    have hl : (msStep A s1.be t b).len = t.len + 1 := rfl
    refine frag_conseq (set_to o rfl rfl (v := BitVec.ofNat 64 (j + 1)) (fun u h => ev_inc (vals_lookup h.1.vals rfl))
      (l' := ("b", BitVec.ofNat 64 b.toNat) :: elemL P E S A 1 (j + 1) (msStep A s1.be t b)) fun u h => runF_of h (by
        simp only [elemL, hr, hl, List.length_append, List.length_singleton]
        repeat (refine lookups_cons rfl ?_)
        exact lookups_nil)) (fun _ h => h) fun u h => ⟨h.1, by rw [hm]; exact h.2⟩

/-! ## `artElem`'s loop -/

/-- The element's bytes so far, from `P` to `j`. -/
abbrev elemTo (a : Bytes) (P j : Nat) : Bytes := (seg a P j).filter (!gap ·)

theorem not_scratch_low {A : Word} {y : Nat} (hy : y < aSets) : ¬elemScratch A (at_ A y) := by
  have hX := X_lt; have hs := sets_le_X; have hE := xElem_eq; have hXv := X_val
  intro h
  rcases h with ⟨k, hk, h⟩ | h | h
  · exact DN.News.ScanRun.at_ne (by omega) (by omega) (by omega) h
  · exact DN.News.ScanRun.at_ne (by omega) (w_lt64 (i := 21) (by decide)) (by have := w_ge 21; omega) h
  · exact DN.News.ScanRun.at_ne (by omega) (w_lt64 (i := 22) (by decide)) (by have := w_ge 22; omega) h

theorem elem_input {A : Word} (hA8 : A.toNat % 8 = 0) {a : Bytes} (hlen : a.length ≤ artMax) {m0 : Word → Word}
    {dm : Word → Bool} {be : Bool} (hin : InputAt m0 dm be A a) (E : Bytes) :
    InputAt (msOf A be m0 E).m dm be A a :=
  input_keep hA8 hlen hin fun _ hx => fold_frame hA8 be (not_scratch_low hx) E _

/-- **`artElem`'s loop reads the element** to the separator or the end, its state `msOf` of its bytes. -/
theorem elem_loop (o : Oracle σ) {A : Word} {s1 : PancakeState σ} (hA8 : A.toNat % 8 = 0) {a : Bytes}
    (hlen : a.length ≤ artMax) {m0 : Word → Word} (hin : InputAt m0 s1.memaddrs s1.be A a)
    (hdm : ∀ i, i < 72 → s1.memaddrs (byteAlign (at_ A (ArticleProg.xElem + i))) = true) {P E : Nat} {sep : BitVec 8}
    (hPE : P ≤ E) (hE : E ≤ a.length) :
    Frag o [.while (v "go") elemBody]
      (RunF s1 (elemL P E sep.toNat A 1 P (msOf A s1.be m0 [])) (· = (msOf A s1.be m0 []).m))
      (RunF s1 (elemL P E sep.toNat A 0 (elemNext a P E sep) (msOf A s1.be m0 (elem a P E sep)))
        (· = (msOf A s1.be m0 (elem a P E sep)).m)) := by
  have hM := artMax_eq
  let St : Nat → Nat → Assn σ := fun g j => RunF s1 (elemL P E sep.toNat A g (if g = 1 then j else elemNext a P E sep)
    (msOf A s1.be m0 (elemTo a P j))) (· = (msOf A s1.be m0 (elemTo a P j)).m)
  let I : Assn σ := fun u => ∃ t : Nat × Nat, St t.1 t.2 u ∧ P ≤ t.2 ∧ t.2 ≤ E ∧ (seg a P t.2).all (· != sep) = true ∧
    (t.1 = 1 ∨ t.1 = 0 ∧ t.2 = elemEnd a P E sep)
  have hIc : Safe.ClockFree I := fun u k ⟨t, h, hv⟩ => ⟨t, runF_clock _ _ _ u k h, hv⟩
  have hlow : LowKK elemBody := lowK_any _ (k := .skip) rfl
  refine frag_conseq (frag_while o rfl hlow hIc (noDecl _ rfl)
    (fun u ⟨t, h, _⟩ => ⟨_, ev_var (vals_lookup h.1.vals rfl)⟩) ?_)
    (fun u h => ⟨(1, P), by
      show RunF s1 _ (· = (msOf A s1.be m0 (elemTo a P P)).m) u
      simp only [elemTo, DN.News.ArticleLines.seg_self, List.filter_nil, if_true]; exact h, Nat.le_refl _, hPE,
      by simp [DN.News.ArticleLines.seg_self], .inl rfl⟩) ?_
  · refine frag_conseq (P0 := fun u => ∃ t : Nat × Nat, (fun t u => St t.1 t.2 u ∧ P ≤ t.2 ∧ t.2 ≤ E ∧
      (seg a P t.2).all (· != sep) = true ∧ t.1 = 1) t u) (frag_exists hlow fun t => ?_)
      (fun u ⟨⟨t, h, h1, h2, h3, h4⟩, h0⟩ => ⟨t, h, h1, h2, h3, flag01 (h4.imp_right fun h => h.1) (by
        rw [ev_var (vals_lookup h.1.vals rfl)] at h0; exact fun e => h0 (by rw [e]))⟩) fun _ h => h
    refine frag_pure (P ≤ t.2 ∧ t.2 ≤ E ∧ (seg a P t.2).all (· != sep) = true ∧ t.1 = 1) (fun u h => h.2) hlow
      fun ⟨h1, h2, h3, h4⟩ => ?_
    obtain ⟨g, j⟩ := t
    simp only at h1 h2 h3 h4; subst h4
    refine frag_conseq (P0 := St 1 j) ?_ (fun u h => h.1) fun _ h => h
    have hinj := elem_input hA8 hlen hin (elemTo a P j)
    refine DN.News.ArticleRun.frag_ifR o rfl (lowK_any _ (k := .skip) rfl) (lowK_any _ (k := .skip) rfl) hIc
      (fun u y w ⟨t, h, hv⟩ hy => by
        change y ∈ ["b"] at hy
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hy; subst hy
        exact ⟨t, runF_restore h rfl w, hv⟩) (fun _ _ _ _ hy => by cases hy) (b := decide (j < E))
      (fun u h => FramerCode.eval_lt (by omega) (by omega) (ev_var (vals_lookup h.1.vals rfl))
        (ev_var (vals_lookup h.1.vals rfl))) (fun hj => ?_) fun hj => ?_
    · have hj' : j < E := of_decide_eq_true hj
      have hja : j < a.length := by omega
      refine frag_append (xs := [_, _]) (frag_append (xs := [_]) (kept_frag o (by decide) (runF_clock _ _ _)
        fun u h => ⟨j, vals_lookup h.1.vals rfl, by omega⟩)
        (runF_dec o rfl rfl (v := BitVec.ofNat 64 (a[j]!).toNat) fun u h =>
          inByte_eval (input_run hinj h) (vals_lookup h.1.vals rfl) hja (vals_lookup h.1.vals rfl))) ?_
      have hseg : seg a P (j + 1) = seg a P j ++ [a[j]!] := by rw [seg_succ a h1 hja, getElem!_pos a j hja]
      refine DN.News.ScanRun.frag_if o rfl (lowK_any _ (k := .skip) rfl) (lowK_any _ (k := .skip) rfl) rfl rfl hIc
        (b := decide ((a[j]!).toNat = sep.toNat)) (fun u h => FramerCode.eval_eq (Nat.lt_trans (a[j]!).isLt
          (by decide)) (Nat.lt_trans sep.isLt (by decide)) (ev_var (vals_lookup h.1.vals rfl))
          (ev_var (vals_lookup h.1.vals rfl))) (fun hs => ?_) fun hs => ?_
      · -- the separator: the element ends here
        have hsep : (a[j]! != sep) = false := by
          have := of_decide_eq_true hs; simp [BitVec.eq_of_toNat_eq this]
        have hend : elemEnd a P E sep = j := seg_tw hE h1 (Nat.le_of_lt hj') h3 (.inr hsep)
        have hn : elemNext a P E sep = j + 1 := by unfold elemNext; rw [hend, if_pos hj']
        refine frag_append (xs := [_]) (runF_set o rfl rfl (v := BitVec.ofNat 64 0) fun _ _ => rfl) ?_
        refine frag_conseq (runF_set o rfl rfl (v := BitVec.ofNat 64 (j + 1))
          fun u h => ev_inc (vals_lookup h.1.vals rfl)) (fun _ h => h) fun u h => ⟨(0, j), ?_, h1, Nat.le_of_lt hj',
            h3, .inr ⟨rfl, hend.symm⟩⟩
        show RunF s1 (elemL P E sep.toNat A 0 (if (0 : Nat) = 1 then j else elemNext a P E sep) _) _ u
        rw [if_neg (by decide), hn]
        exact runF_of h (by
          repeat (refine lookups_cons rfl ?_)
          exact lookups_nil)
      have hns : (a[j]! != sep) = true := by
        have := of_decide_eq_false hs; simp only [bne_iff_ne, ne_eq]; intro e; exact this (by rw [e])
      have h3' : (seg a P (j + 1)).all (· != sep) = true := by
        rw [hseg, List.all_append, h3]; simp only [List.all_cons, List.all_nil, hns, Bool.and_self]
      refine DN.News.ScanRun.frag_if o rfl (lowK_any _ (k := .skip) rfl) (lowK_any _ (k := .skip) rfl) rfl rfl hIc
        (b := gap a[j]!) (fun u h => gap_eval (vals_lookup h.1.vals rfl)) (fun hg => ?_) fun hg => ?_
      · -- a gap: left out
        have he : elemTo a P (j + 1) = elemTo a P j := by
          simp only [elemTo, hseg, List.filter_append, List.filter_cons, List.filter_nil, hg, Bool.not_true,
            Bool.false_eq_true, if_false, List.append_nil]
        refine frag_conseq (runF_set o rfl rfl (v := BitVec.ofNat 64 (j + 1))
          fun u h => ev_inc (vals_lookup h.1.vals rfl)) (fun _ h => h) fun u h => ⟨(1, j + 1), ?_, by omega, by omega,
            h3', .inl rfl⟩
        show RunF s1 (elemL P E sep.toNat A 1 (if (1 : Nat) = 1 then j + 1 else elemNext a P E sep) _)
          (· = (msOf A s1.be m0 (elemTo a P (j + 1))).m) u
        rw [if_pos rfl, he]
        exact runF_of h (by
          repeat (refine lookups_cons rfl ?_)
          exact lookups_nil)
      · -- a byte of the element
        have he : elemTo a P (j + 1) = elemTo a P j ++ [a[j]!] := by
          simp only [elemTo, hseg, List.filter_append, List.filter_cons, List.filter_nil, hg, Bool.not_false, if_true]
        obtain ⟨-, hC⟩ := msOf_mem (be := s1.be) hdm m0 (elemTo a P j)
        refine frag_conseq (take_frag o (P := P) (E := E) (S := sep.toNat) (j := j) hdm hC) (fun _ h => h)
          fun u h => ⟨(1, j + 1), ?_, by omega, by omega, h3', .inl rfl⟩
        show RunF s1 (elemL P E sep.toNat A 1 (if (1 : Nat) = 1 then j + 1 else elemNext a P E sep) _)
          (· = (msOf A s1.be m0 (elemTo a P (j + 1))).m) u
        rw [if_pos rfl, he, msOf_snoc]
        exact runF_mono h (fun q hq => List.mem_cons_of_mem _ hq) fun _ e => e
    · -- the end: the element ends there
      have hj' : ¬j < E := fun e => by simp [e] at hj
      have hjE : j = E := by omega
      have hend : elemEnd a P E sep = j := seg_tw hE h1 h2 h3 (.inl hjE)
      have hn : elemNext a P E sep = j := by unfold elemNext; rw [hend, if_neg hj', hjE]
      refine frag_conseq (runF_set o rfl rfl (v := BitVec.ofNat 64 0) fun _ _ => rfl) (fun _ h => h)
        fun u h => ⟨(0, j), ?_, h1, h2, h3, .inr ⟨rfl, hend.symm⟩⟩
      show RunF s1 (elemL P E sep.toNat A 0 (if (0 : Nat) = 1 then j else elemNext a P E sep) _) _ u
      rw [if_neg (by decide), hn]
      exact runF_of h (by
        repeat (refine lookups_cons rfl ?_)
        exact lookups_nil)
  · intro u ⟨⟨t, h, h1, h2, h3, h4⟩, h0⟩
    rw [ev_var (vals_lookup h.1.vals rfl)] at h0
    rcases h4 with e | ⟨e, hj⟩
    · rw [e] at h0; exact absurd (Option.some.inj h0) (by decide)
    · obtain ⟨g, j⟩ := t
      simp only at e hj h; subst e
      have he : elemTo a P j = elem a P E sep := by rw [hj]; rfl
      change RunF s1 (elemL P E sep.toNat A 0 (if (0 : Nat) = 1 then j else elemNext a P E sep)
        (msOf A s1.be m0 (elemTo a P j))) (· = (msOf A s1.be m0 (elemTo a P j)).m) u at h
      rw [he, if_neg (by decide)] at h; exact h

/-! ## `artElem` -/

/-- What `artElem` leaves of element `E`: its first 64 bytes, its length up to 65, whether it is reserved. Every
other word stays as in `m0`. -/
def ElemOut (A : Word) (dm : Word → Bool) (be : Bool) (m0 : Word → Word) (E : Bytes) (m : Word → Word) : Prop :=
  (∀ x, ¬elemScratch A x → m x = m0 x) ∧ BytesAt A dm be ArticleProg.xElem 64 E m ∧
    m (at_ A ArticleProg.xElemLen) = BitVec.ofNat 64 (min 65 E.length) ∧
    m (at_ A ArticleProg.xElemRes) = BitVec.ofNat 64 (bnat (reserved E))

/-- What `artElem` from `P` before `E` gives back: where the next element starts; the element in `ElemOut`. -/
def ElemRet (A : Word) (dm : Word → Bool) (be : Bool) (a : Bytes) (P E : Nat) (sep : BitVec 8) (m0 : Word → Word) :
    Ret := fun v m => v = BitVec.ofNat 64 (elemNext a P E sep) ∧ ElemOut A dm be m0 (elem a P E sep) m

theorem elem_dm {A : Word} {dm : Word → Bool} (hD : ArtDom A dm) (hA8 : A.toNat % 8 = 0) :
    ∀ i, i < 72 → dm (byteAlign (at_ A (ArticleProg.xElem + i))) = true := fun i hi => by
  have := sets_le_X; have := X_val; have := xFirst_eq; have := xElem_eq
  rw [DN.News.ScanRun.align_at hA8]
  exact hD _ (by omega) (by omega) (by omega)

theorem bytesAt_upd {A : Word} {dm : Word → Bool} {be : Bool} (hA8 : A.toNat % 8 = 0) {B : Bytes} {m : Word → Word}
    (h : BytesAt A dm be ArticleProg.xElem 64 B m) {i : Nat} (hi : i < 32) (w : Word) :
    BytesAt A dm be ArticleProg.xElem 64 B (upd m (at_ A (ArticleProg.w i)) w) := fun k hk hl => by
  have := X_val; have := xElem_eq
  have hne : byteAlign (at_ A (ArticleProg.xElem + k)) ≠ at_ A (ArticleProg.w i) := by
    rw [DN.News.ScanRun.align_at hA8]
    exact DN.News.ScanRun.at_ne (by omega) (w_lt64 hi) (by simp only [ArticleProg.w]; omega)
  simp only [memLoadByte, upd_ne _ hne]; exact h k hk hl

/-- **`artElem` reads the next element** from `P` before `E`, if it returns. -/
theorem artElem_ok (o : Oracle σ) {A : Word} {s1 : PancakeState σ} (hA : Area ArticleProg.ofs A s1)
    (hD : ArtDom A s1.memaddrs) {a : Bytes} (hlen : a.length ≤ artMax) (hin : InputAt s1.memory s1.memaddrs s1.be A a)
    {P E : Nat} {sep : BitVec 8} (hPE : P ≤ E) (hE : E ≤ a.length) (hp : s1.locals "p" = some (BitVec.ofNat 64 P))
    (he : s1.locals "e" = some (BitVec.ofNat 64 E)) (hs : s1.locals "sep" = some (BitVec.ofNat 64 sep.toNat)) :
    ∃ body, Lower.lower (gd ArticleProg.artElem) = some body ∧
      SafeR o (fun s => s = s1) body (ElemRet A s1.memaddrs s1.be a P E sep s1.memory) fun _ => False := by
  have hM := artMax_eq
  have hA8 := hA.hA
  have hdm := elem_dm hD hA8
  refine body_of ?_
  show FragR o _ (guardL ArticleProg.artElem.body) _ _
  rw [artElem_body]
  obtain ⟨EA, hEA⟩ := atOff_lower ArticleProg.ofs
  refine fragR_conseq (P0 := RunF s1 [("p", BitVec.ofNat 64 P), ("e", BitVec.ofNat 64 E),
    ("sep", BitVec.ofNat 64 sep.toNat)] (· = s1.memory)) ?_ (entry_run (fun q hq => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl
      · exact hp
      · exact he
      · exact hs) rfl) fun _ h => h
  refine fragR_append (xs := [_]) (fragR_of (runF_dec o hEA rfl (v := A) fun u h => areaAt_eval hA h.1.base hEA)) ?_
  refine fragR_append (xs := [_]) (fragR_of (runF_dec o rfl rfl (v := BitVec.ofNat 64 P) fun u h =>
    ev_var (vals_lookup h.1.vals rfl))) ?_
  refine fragR_append (xs := [_]) (fragR_of (runF_dec o rfl rfl (v := BitVec.ofNat 64 0) fun _ _ => rfl)) ?_
  refine fragR_append (xs := [_]) (fragR_of (runF_dec o rfl rfl (v := BitVec.ofNat 64 0) fun _ _ => rfl)) ?_
  refine fragR_append (xs := [_]) (fragR_of (runF_dec o rfl rfl (v := BitVec.ofNat 64 1) fun _ _ => rfl)) ?_
  refine fragR_append (xs := [_]) (fragR_of (runF_dec o rfl rfl (v := BitVec.ofNat 64 0) fun _ _ => rfl)) ?_
  refine fragR_append (xs := [_]) (fragR_of (runF_dec o rfl rfl (v := BitVec.ofNat 64 1) fun _ _ => rfl)) ?_
  refine fragR_append (xs := [_]) (fragR_of (elem_loop o (m0 := s1.memory) hA8 hlen hin hdm (sep := sep) hPE hE)) ?_
  -- the last component, the whole name
  let t := msOf A s1.be s1.memory (elem a P E sep)
  obtain ⟨hEb, hCb⟩ := msOf_mem (be := s1.be) hdm s1.memory (elem a P E sep)
  refine fragR_append (fragR_of (done_frag o rfl (C := t.r.comp) (fst := t.r.first) (res := t.r.res) rfl rfl rfl hCb
    (comp_dm hdm))) ?_
  let L2 : List (String × Value) := ("cl", BitVec.ofNat 64 0) :: without "cl" (("first", BitVec.ofNat 64 0) ::
    without "first" (("res", BitVec.ofNat 64 (bnat (t.r.res || compRes t.r.first t.r.comp))) ::
      without "res" (elemL P E sep.toNat A 0 (elemNext a P E sep) t)))
  have hb : ∀ i u, i < 64 → RunF s1 L2 (· = t.m) u → memLoadByte u.memory u.memaddrs u.be
      (at_ A (ArticleProg.xElem + i)) = some (loadsAt t.m s1.memaddrs s1.be A ArticleProg.xElem i) :=
    fun i u hi h => loadsAt_eq h (hdm i (by omega))
  have hwe : ∀ w : String, Ascii w → (codes w).length ≤ 64 → ∃ X, Lower.lowerExp (cmpE "ln" ArticleProg.xElem w) =
      some X ∧ ∀ u, RunF s1 L2 (· = t.m) u → eval u X = some (bw (elem a P E sep == DN.News.CommandSpec.ascii w)) :=
    fun w hw hl => cmp_eval (fun u h => vals_lookup h.1.vals rfl) (by rw [xElem_eq]; decide) (K := 64) (by decide)
      (fun u h => (vals_lookup h.1.vals rfl).trans (by rw [msOf_len])) _ hb (loadsAt_bytes hEb) hw hl
  obtain ⟨X1, h1, v1⟩ := hwe "poster" (by unfold Ascii; decide) (by decide)
  obtain ⟨X2, h2, v2⟩ := hwe "junk" (by unfold Ascii; decide) (by decide)
  let wh := elem a P E sep == DN.News.CommandSpec.ascii "poster" || elem a P E sep == DN.News.CommandSpec.ascii "junk"
  refine fragR_append (xs := [_]) (fragR_of (cond_set o rfl (lower_or2 h1 h2) rfl (b := wh)
    (L' := ("res", BitVec.ofNat 64 (bnat (rsEnd t.r || wh))) :: without "res" L2)
    (fun u h => FramerCode.eval_or2 (v1 u h) (v2 u h)) (vx := BitVec.ofNat 64 1) (fun _ _ => rfl)
    (fun hw u h => by rw [hw, Bool.or_true]; exact h)
    fun hw u h => by rw [hw, Bool.or_false]; exact runF_same h rfl)) ?_
  have hlenE : t.len = (elem a P E sep).length := msOf_len _ _ _ _
  refine fragR_append (xs := [_]) (fragR_of (runF_storeA o (atOffW_lower 21) rfl (y := ArticleProg.w 21)
    (artDom_w hD (by decide)) (fun u h => atA_eval (vals_lookup h.1.vals rfl))
    (val := fun _ => BitVec.ofNat 64 (min 65 t.len)) (fun u h => ev_var (vals_lookup h.1.vals rfl))
    (G := (· = upd t.m (at_ A ArticleProg.xElemLen) (BitVec.ofNat 64 (min 65 t.len)))) fun m hm => by subst hm; rfl)) ?_
  refine fragR_append (xs := [_]) (fragR_of (runF_storeA o (atOffW_lower 22) rfl (y := ArticleProg.w 22)
    (artDom_w hD (by decide)) (fun u h => atA_eval (vals_lookup h.1.vals rfl))
    (val := fun _ => BitVec.ofNat 64 (bnat (rsEnd t.r || wh))) (fun u h => ev_var (vals_lookup h.1.vals rfl))
    (G := (· = upd (upd t.m (at_ A ArticleProg.xElemLen) (BitVec.ofNat 64 (min 65 t.len)))
      (at_ A ArticleProg.xElemRes) (BitVec.ofNat 64 (bnat (rsEnd t.r || wh))))) fun m hm => by subst hm; rfl)) ?_
  refine fragR_ret o rfl fun u h => ⟨_, ev_var (vals_lookup h.1.vals rfl), rfl, ?_, ?_, ?_, ?_⟩
  · intro x hx
    have h21 : x ≠ at_ A ArticleProg.xElemLen := fun e => hx (.inr (.inl e))
    have h22 : x ≠ at_ A ArticleProg.xElemRes := fun e => hx (.inr (.inr e))
    rw [h.2, upd_ne _ h22, upd_ne _ h21]
    exact fold_frame hA8 s1.be hx _ _
  · rw [h.2]; exact bytesAt_upd hA8 (bytesAt_upd hA8 hEb (i := 21) (by decide) _) (i := 22) (by decide) _
  · have hne : at_ A ArticleProg.xElemLen ≠ at_ A ArticleProg.xElemRes :=
      DN.News.ScanRun.at_ne (w_lt64 (i := 21) (by decide)) (w_lt64 (i := 22) (by decide))
        (by simp only [ArticleProg.xElemLen, ArticleProg.xElemRes, ArticleProg.w]; omega)
    rw [h.2, upd_ne _ hne, upd_eq, hlenE]
  · rw [h.2, upd_eq, reserved_rs, ← msOf_r A s1.be s1.memory]

/-! ## A call of `artElem` -/

theorem mem_artElem : gd ArticleProg.artElem ∈
    ArticleProg.functions ArticleSpec.spec (ArticleProg.entries ArticleSpec.spec) .none :=
  List.mem_append_right _ (List.mem_map.2 ⟨ArticleProg.artElem, by simp, rfl⟩)

theorem broken_scr {A : Word} : ¬elemScratch A (at_ A aBroken) := not_scratch_low broken_low

/-- **A call of `artElem`**, the check after it passed: where the next element starts, the element in `ElemOut`. -/
theorem elemCall_frag (o : Oracle σ) {R : Ret} {A : Word} {s0 : PancakeState σ} (hA : Area ArticleProg.ofs A s0)
    (hD : ArtDom A s0.memaddrs) (hcode : ArtCode s0.code) {a : Bytes} (hlen : a.length ≤ artMax) {rt : String}
    (hra : rt ≠ "a") {l : List (String × Value)} (hla : l.lookup "a" = some A) (hrt : Fresh rt l = true)
    {m0 : Word → Word} (hin : InputAt m0 s0.memaddrs s0.be A a) (hb : m0 (at_ A aBroken) = 0) {x y : String}
    {P E : Nat} {sep : BitVec 8} (hPE : P ≤ E) (hE : E ≤ a.length) (hx : l.lookup x = some (BitVec.ofNat 64 P))
    (hy : l.lookup y = some (BitVec.ofNat 64 E)) :
    FragR o R (guardS (.call rt "artElem" [v x, v y, n sep.toNat])) (RunF s0 l (· = m0))
      (fun u => ∃ m, RunF s0 ((rt, BitVec.ofNat 64 (elemNext a P E sep)) :: l) (· = m) u ∧
        ElemOut A s0.memaddrs s0.be m0 (elem a P E sep) m) := by
  refine fragR_conseq (gcall_frag o hA hcode hra (f := ArticleProg.artElem) mem_artElem (by decide)
    (args := [.var x, .var y, .const (BitVec.ofNat 64 sep.toNat)]) rfl hla
    (vs := [BitVec.ofNat 64 P, BitVec.ofNat 64 E, BitVec.ofNat 64 sep.toNat]) rfl
    (fun u h => by simp only [evalArgs, ev_var (vals_lookup h.1.vals hx), ev_var (vals_lookup h.1.vals hy)]; rfl)
    (Rf := ElemRet A s0.memaddrs s0.be a P E sep)
    (fun s1 hA1 _ hm hbe hloc hF => by
      have := artElem_ok o hA1 (by rw [hm]; exact hD) hlen (by rw [hF, hm, hbe]; exact hin) hPE hE
        ((hloc "p").trans rfl) ((hloc "e").trans rfl) ((hloc "sep").trans rfl)
      rw [hm, hbe] at this; exact this) hrt
    (G := fun v m => v = BitVec.ofNat 64 (elemNext a P E sep) ∧ ElemOut A s0.memaddrs s0.be m0 (elem a P E sep) m)
    (fun m m' v hm hr => by subst hm; exact hr)
    fun v m h => by rw [h.2.1 _ broken_scr]; exact hb) (fun u h => h) fun u ⟨v, h⟩ => ?_
  obtain ⟨hv, hout⟩ := h.2
  subst hv; exact ⟨u.memory, ⟨h.1, rfl⟩, hout⟩

/-! ## A loop over a list's elements -/

/-- A list function's loop body: the next element read, `pre` and `test`, 1 back if it passes. -/
def listBody (sep : Nat) (pre : List Syntax.PStmt) (test : Syntax.PExpr) : List Syntax.PStmt :=
  guardS (.call "q" "artElem" [v "p", v "e", n sep]) ++ (pre ++ [ifs test [.ret (n 1)], .assign "p" (v "q")])

/-- A list function from `s` to `e`: 1 if an element passes `test`, else 0. -/
def listFn (sep : Nat) (pre : List Syntax.PStmt) (test : Syntax.PExpr) : List Syntax.PStmt :=
  [areaAt ArticleProg.ofs, .dec "p" (v "s"), .while (eLt (v "p") (v "e")) (listBody sep pre test), .ret (n 0)]

/-- A list function's locals in its loop. -/
def listL (S E : Nat) (A : Word) (p : Nat) : List (String × Value) :=
  [("p", BitVec.ofNat 64 p), ("a", A), ("s", BitVec.ofNat 64 S), ("e", BitVec.ofNat 64 E)]

/-- The list loop's knowledge at `p`: the elements still to come pass `T` as those from `S` do. Words
outside the element's scratch stay as in `m0`. -/
def ListInv (A : Word) (a : Bytes) (S E : Nat) (sep : BitVec 8) (T : Bytes → Bool) (p : Nat) (m0 m : Word → Word) :
    Prop :=
  p ≤ E ∧ (∀ x, ¬elemScratch A x → m x = m0 x) ∧ (elems a E sep S).any T = (elems a E sep p).any T

/-- **A list function answers whether an element passes `T`**, if it returns. `test` says so of each, after `pre`
added locals. Words outside the element's scratch are kept. -/
theorem list_frag (o : Oracle σ) {R : Ret} {A : Word} {s1 : PancakeState σ} (hA : Area ArticleProg.ofs A s1)
    (hD : ArtDom A s1.memaddrs) (hcode : ArtCode s1.code) (hb : s1.memory (at_ A aBroken) = 0) {a : Bytes}
    (hlen : a.length ≤ artMax) (hin : InputAt s1.memory s1.memaddrs s1.be A a) {S E : Nat} (hSE : S ≤ E)
    (hE : E ≤ a.length) {sep : BitVec 8} {pre : List Syntax.PStmt} {test : Syntax.PExpr} {T : Bytes → Bool}
    (hlow : LowKK (listBody sep.toNat pre test))
    (hlow2 : LowKK (pre ++ [ifs test [.ret (n 1)], .assign "p" (v "q")]))
    (hdecl : ∀ y ∈ declared pre, y ≠ "q" ∧ ∀ p, Fresh y (listL S E A p) = true)
    (htest : ∀ (l : List (String × Value)) (m m' : Word → Word) (B : Bytes), l.lookup "a" = some A →
      (∀ y ∈ declared pre, Fresh y l = true) → ElemOut A s1.memaddrs s1.be m B m' →
      ∃ (l' : List (String × Value)) (X : PancakeExp),
        Frag o pre (RunF s1 l (· = m')) (RunF s1 (l' ++ l) (· = m')) ∧ Lower.lowerExp test = some X ∧
        ∀ u, RunF s1 (l' ++ l) (· = m') u → eval u X = some (bw (T B)))
    (hR : ∀ w m, w = bw ((elems a E sep S).any T) → (∀ x, ¬elemScratch A x → m x = s1.memory x) → R w m) :
    FragR o R (listFn sep.toNat pre test) (RunF s1 [("s", BitVec.ofNat 64 S), ("e", BitVec.ofNat 64 E)]
      (· = s1.memory)) fun _ => False := by
  have hM := artMax_eq
  have hA8 := hA.hA
  obtain ⟨EA, hEA⟩ := atOff_lower ArticleProg.ofs
  refine fragR_append (xs := [_]) (fragR_of (runF_dec o hEA rfl (v := A) fun u h => areaAt_eval hA h.1.base hEA)) ?_
  refine fragR_append (xs := [_]) (fragR_of (runF_dec o rfl rfl (v := BitVec.ofNat 64 S) fun u h =>
    ev_var (vals_lookup h.1.vals rfl))) ?_
  let I : Assn σ := fun u => ∃ t : Nat × (Word → Word), RunF s1 (listL S E A t.1) (· = t.2) u ∧
    ListInv A a S E sep T t.1 s1.memory t.2
  have hIc : Safe.ClockFree I := fun u k ⟨t, h, hv⟩ => ⟨t, runF_clock _ _ _ u k h, hv⟩
  have hcond : ∀ u (t : Nat × (Word → Word)), RunF s1 (listL S E A t.1) (· = t.2) u → t.1 ≤ E →
      eval u (.cmp .less (.var "p") (.var "e")) = some (bw (decide (t.1 < E))) := fun u t h hq =>
    FramerCode.eval_lt (by omega) (by omega) (ev_var (vals_lookup h.1.vals rfl)) (ev_var (vals_lookup h.1.vals rfl))
  have hdb : ∀ y ∈ declared (listBody sep.toNat pre test), ∀ p, Fresh y (listL S E A p) = true := fun y hy p => by
    simp only [listBody, declared_append, List.mem_append] at hy
    rcases hy with hy | hy | hy
    · change y ∈ ["q"] at hy
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hy; subst hy; rfl
    · exact (hdecl y hy).2 p
    · cases hy
  refine fragR_append (xs := [_]) (fragR_conseq (fragR_while o rfl hlow hIc
    (fun u z w ⟨t, h, hv⟩ hz => ⟨t, runF_restore h (hdb z hz t.1) w, hv⟩)
    (fun u ⟨t, h, hv⟩ => ⟨_, hcond u t h hv.1⟩) ?_)
    (fun u h => ⟨(S, s1.memory), h, hSE, fun _ _ => rfl, rfl⟩) fun _ h => h) ?_
  · refine fragR_conseq (P0 := fun u => ∃ t : Nat × (Word → Word), (fun t u => RunF s1 (listL S E A t.1) (· = t.2) u ∧
      ListInv A a S E sep T t.1 s1.memory t.2 ∧ t.1 < E) t u) (fragR_exists hlow fun t => ?_)
      (fun u ⟨⟨t, h, hv⟩, h0⟩ => ⟨t, h, hv, by
        rw [hcond u t h hv.1] at h0; exact of_decide_eq_true (bw_ne0 h0)⟩) fun _ h => h
    refine fragR_pure (ListInv A a S E sep T t.1 s1.memory t.2 ∧ t.1 < E) (fun u h => h.2) hlow fun ⟨hq, hp⟩ => ?_
    obtain ⟨p, m⟩ := t
    obtain ⟨hpE, hfr, hany⟩ := hq
    simp only at hpE hfr hany hp
    have hinm : InputAt m s1.memaddrs s1.be A a := input_keep hA8 hlen hin fun _ hx => hfr _ (not_scratch_low hx)
    have hbm : m (at_ A aBroken) = 0 := (hfr _ broken_scr).trans hb
    refine fragR_append (fragR_conseq (elemCall_frag o hA hD hcode hlen (rt := "q") (by decide) (l := listL S E A p)
      rfl rfl hinm hbm (x := "p") (y := "e") (sep := sep) (Nat.le_of_lt hp) hE rfl rfl)
      (fun u h => h.1) fun _ h => h) ?_
    refine fragR_exists hlow2 fun m' => ?_
    let B := elem a p E sep
    let nq := elemNext a p E sep
    refine fragR_pure (ElemOut A s1.memaddrs s1.be m B m') (fun u h => h.2) hlow2 fun hout => ?_
    obtain ⟨l', X, hpre, hX, hXv⟩ := htest (("q", BitVec.ofNat 64 nq) :: listL S E A p) m m' B rfl
      (fun y hy => DN.News.ScanRun.fresh_cons (hdecl y hy).1.symm ((hdecl y hy).2 p)) hout
    refine fragR_append (fragR_conseq (fragR_of hpre) (fun u h => h.1) fun _ h => h) ?_
    have hcons : (elems a E sep p).any T = (T B || (elems a E sep nq).any T) := by
      rw [elems_eq, if_pos hp, List.any_cons]
    by_cases hn : T B = true
    · refine fragR_append (xs := [_]) (fragR_ifT o hX (lowKK_ret rfl) lowKK_nil rfl rfl (Q := fun _ => False)
        (fun _ _ h => h) (fun u h => (hXv u h).trans (by rw [hn])) ?_)
        (fragR_of (frag_unsat (lowK_any _ (k := .skip) rfl) fun _ h => h))
      refine fragR_ret o rfl fun u h => ⟨_, rfl, hR _ _ ?_ fun x hx => ?_⟩
      · rw [hany, hcons, hn, Bool.true_or]; rfl
      · rw [h.2, hout.1 x hx, hfr x hx]
    · have hn' : T B = false := Bool.eq_false_iff.2 hn
      refine fragR_append (xs := [_]) (fragR_ifF o hX (lowKK_ret rfl) lowKK_nil rfl rfl (runF_clock _ _ _)
        (fun u h => (hXv u h).trans (by rw [hn'])) (fragR_of (frag_nil o fun _ h => h))) ?_
      refine fragR_conseq (fragR_of (runF_set o rfl rfl (v := BitVec.ofNat 64 nq)
        fun u h => ev_var (vals_lookup h.1.vals rfl))) (fun u h => runF_mono h (l' := ("q", BitVec.ofNat 64 nq) ::
          listL S E A p) (fun q hq => List.mem_append_right _ hq) fun _ e => e)
        fun u h => ⟨(nq, m'), runF_of h (by
          repeat (refine lookups_cons rfl ?_)
          exact lookups_nil), elemNext_le, fun x hx => (hout.1 x hx).trans (hfr x hx), ?_⟩
      show _ = _
      rw [hany, hcons, hn', Bool.false_or]
  refine fragR_ret o rfl fun u ⟨⟨t, h, hq⟩, h0⟩ => ⟨_, rfl, hR _ _ ?_ fun x hx => by rw [h.2]; exact hq.2.1 x hx⟩
  rw [hcond u t h hq.1] at h0
  have hpE : t.1 = E := by have := of_decide_eq_false (bw_eq0 h0); have := hq.1; omega
  rw [hq.2.2, hpE, elems_eq, if_neg (Nat.lt_irrefl _)]; rfl

/-! ## `artDistAll` -/

/-- What `artDistAll` from `S` to `E` gives back: whether Distribution's body names `all`. Words outside the
element's scratch stay as in `m0`. -/
def DistRet (A : Word) (a : Bytes) (S E : Nat) (m0 : Word → Word) : Ret := fun v m =>
  v = bw ((ArticleSpec.listed (seg a S E)).any (ArticleSpec.named · "all")) ∧ ∀ x, ¬elemScratch A x → m x = m0 x

/-- `artDistAll`'s test of an element. -/
def allE : Syntax.PExpr :=
  eAnd (eEq (wd ArticleProg.xElemLen) (n 3)) (ArticleProg.spells ArticleProg.xElem "all")

theorem artDistAll_body : guardL ArticleProg.artDistAll.body = listFn ArticleSpec.COMMA.toNat [] allE := rfl

theorem min65_eq {k c : Nat} (hc : c < 65) : decide (min 65 k = c) = decide (k = c) := by
  simp only [decide_eq_decide]; omega

/-- **The test of `all`** after `artElem`: whether the element is named `all`. -/
theorem allE_eval {A : Word} {s1 : PancakeState σ} (hD : ArtDom A s1.memaddrs) (hA8 : A.toNat % 8 = 0)
    {l : List (String × Value)} (hla : l.lookup "a" = some A) {m0 M : Word → Word} {B : Bytes}
    (hout : ElemOut A s1.memaddrs s1.be m0 B M) :
    ∃ X, Lower.lowerExp allE = some X ∧
      ∀ u, RunF s1 l (· = M) u → eval u X = some (bw (ArticleSpec.named B "all")) := by
  have hdm := elem_dm hD hA8
  obtain ⟨Es, hEs, hv⟩ := spells_fold (P := RunF s1 l (· = M)) (A := A) (fun u h => vals_lookup h.1.vals hla)
    (o := ArticleProg.xElem) (by rw [xElem_eq]; decide) (loadsAt M s1.memaddrs s1.be A ArticleProg.xElem)
    (fun i u hi h => loadsAt_eq h (hdm i (by omega))) (codes "all") 0 (n 1) (.const (BitVec.ofNat 64 1)) true rfl
    (fun _ _ => rfl) (by decide) (by decide)
  refine ⟨_, lower_and (x := eEq (wd ArticleProg.xElemLen) (n 3)) rfl hEs, fun u h => ?_⟩
  have hl : min 65 B.length < 2 ^ 64 := by omega
  refine (FramerCode.eval_and (FramerCode.eval_eq hl (by decide)
    ((wordAt_eval hD h hla (i := 21) (by decide)).trans (congrArg some hout.2.2.1)) rfl) (hv u h)).trans ?_
  congr 2
  have hcs : codes (ArticleProg.lowerS "all") = (DN.News.CommandSpec.ascii "all").map (fun b => lowN b.toNat) := by
    decide +kernel
  have hlow : codes (ArticleProg.lowerS "all") = codes "all" := by decide +kernel
  rw [Bool.true_and, min65_eq (by decide), ← spells_named hcs (L := 3) rfl B _
    fun i hi hl => loadsAt_bytes hout.2.1 i (by omega) hl]
  unfold spellsOK; rw [hlow]

/-- **`artDistAll` finds whether Distribution's body names `all`**, if it returns. -/
theorem artDistAll_ok (o : Oracle σ) {A : Word} {s1 : PancakeState σ} (hA : Area ArticleProg.ofs A s1)
    (hD : ArtDom A s1.memaddrs) (hcode : ArtCode s1.code) (hb : s1.memory (at_ A aBroken) = 0) {a : Bytes}
    (hlen : a.length ≤ artMax) (hin : InputAt s1.memory s1.memaddrs s1.be A a) {S E : Nat} (hSE : S ≤ E)
    (hE : E ≤ a.length) (hs : s1.locals "s" = some (BitVec.ofNat 64 S))
    (he : s1.locals "e" = some (BitVec.ofNat 64 E)) :
    ∃ body, Lower.lower (gd ArticleProg.artDistAll) = some body ∧
      SafeR o (fun s => s = s1) body (DistRet A a S E s1.memory) fun _ => False := by
  refine body_of ?_
  show FragR o _ (guardL ArticleProg.artDistAll.body) _ _
  rw [artDistAll_body]
  refine fragR_conseq (list_frag o hA hD hcode hb hlen hin hSE hE (sep := ArticleSpec.COMMA)
    (T := (ArticleSpec.named · "all")) (lowK_any _ (k := .skip) rfl) (lowK_any _ (k := .skip) rfl)
    (fun _ hy => by cases hy) (fun l m m' B hla _ hout => ?_) fun w m hw hf => ⟨?_, hf⟩) (entry_two hs he)
    fun _ h => h
  · obtain ⟨X, hX, hXv⟩ := allE_eval hD hA.hA hla hout
    exact ⟨[], X, frag_nil o fun _ h => h, hX, hXv⟩
  · rw [listed_any hSE hE rfl]; exact hw

/-! ## `artPosted` -/

/-- What `artPosted` from `S` to `E` gives back: whether Path's body holds the diagnostic `.POSTED`. Words
outside the element's scratch stay as in `m0`. -/
def PostRet (A : Word) (a : Bytes) (S E : Nat) (m0 : Word → Word) : Ret := fun v m =>
  v = bw ((ArticleSpec.pathElements (seg a S E)).any ArticleSpec.isPosted) ∧ ∀ x, ¬elemScratch A x → m x = m0 x

/-- `artPosted`'s test of an element. -/
def postedE : Syntax.PExpr :=
  eAnd (eAnd (eLt (n 6) (v "ln")) (eEq (byte (Syntax.atOff (v "a") ArticleProg.xElem)) (n 46)))
    (eAnd (ArticleProg.spells (ArticleProg.xElem + 1) "posted")
      (or2 (eEq (v "ln") (n 7)) (eEq (byte (Syntax.atOff (v "a") (ArticleProg.xElem + 7))) (n 46))))

theorem artPosted_body : guardL ArticleProg.artPosted.body =
    listFn ArticleSpec.BANG.toNat [.dec "ln" (wd ArticleProg.xElemLen)] postedE := rfl

/-- **`artPosted`'s test as a function of the element's bytes**: `tb` from its start, `tb'` from its second. -/
theorem posted_test (B : Bytes) (tb tb' : Nat → BitVec 8) (h0 : ∀ i, i < 8 → i < B.length → tb i = B[i]!)
    (h1 : ∀ i, i < 6 → 1 + i < B.length → tb' i = B[1 + i]!) :
    ((decide (6 < min 65 B.length) && decide ((tb 0).toNat = 46)) &&
      (spellsOK tb' "posted" && (decide (min 65 B.length = 7) || decide ((tb 7).toNat = 46)))) =
      ArticleSpec.isPosted B := by
  rw [isPosted_eq]
  by_cases h6 : 6 < B.length
  · have hw : ((B.drop 1).take 6).length = 6 := by simp only [List.length_take, List.length_drop]; omega
    have hcs : codes (ArticleProg.lowerS "posted") =
        (DN.News.CommandSpec.ascii "posted").map (fun b => lowN b.toNat) := by decide +kernel
    have hsp : spellsOK tb' "posted" = ArticleSpec.named ((B.drop 1).take 6) "posted" := by
      have := spells_named hcs (L := 6) rfl ((B.drop 1).take 6) tb' fun i hi hl => by
        rw [h1 i hi (by omega), getElem!_pos _ i hl, List.getElem_take, List.getElem_drop,
          getElem!_pos B (1 + i) (by omega)]
      rwa [hw, show decide (6 = 6) = true from rfl, Bool.true_and] at this
    have hb0 : decide ((tb 0).toNat = 46) = (B[0]! == DN.News.FrameSpec.DOT) := by
      rw [h0 0 (by decide) (by omega), ArticleScan.beq_byte]; rfl
    have hl6 : decide (6 < min 65 B.length) = decide (6 < B.length) := by simp only [decide_eq_decide]; omega
    rw [hl6, hsp, hb0, min65_eq (by decide)]
    by_cases h7 : B.length = 7
    · simp [h7]
    · rw [show decide ((tb 7).toNat = 46) = (B[7]! == DN.News.FrameSpec.DOT) by
        rw [h0 7 (by decide) (by omega), ArticleScan.beq_byte]; rfl]
      simp only [Bool.and_assoc]
  · have hl6 : decide (6 < min 65 B.length) = false := by simp only [decide_eq_false_iff_not]; omega
    rw [hl6, decide_eq_false h6]; rfl

/-- **The test of `.POSTED`** after `artElem`, its length in `ln`: whether the element is the diagnostic. -/
theorem postedE_eval {A : Word} {s1 : PancakeState σ} (hD : ArtDom A s1.memaddrs) (hA8 : A.toNat % 8 = 0)
    {l : List (String × Value)} (hla : l.lookup "a" = some A) {m0 M : Word → Word} {B : Bytes}
    (hout : ElemOut A s1.memaddrs s1.be m0 B M) (hln : l.lookup "ln" = some (BitVec.ofNat 64 (min 65 B.length))) :
    ∃ X, Lower.lowerExp postedE = some X ∧
      ∀ u, RunF s1 l (· = M) u → eval u X = some (bw (ArticleSpec.isPosted B)) := by
  have hdm := elem_dm hD hA8
  have hX := xElem_eq
  let tb := loadsAt M s1.memaddrs s1.be A ArticleProg.xElem
  let tb' := loadsAt M s1.memaddrs s1.be A (ArticleProg.xElem + 1)
  obtain ⟨Es, hEs, hv⟩ := spells_fold (P := RunF s1 l (· = M)) (A := A) (fun u h => vals_lookup h.1.vals hla)
    (o := ArticleProg.xElem + 1) (by omega) tb'
    (fun i u hi h => loadsAt_eq h (by rw [Nat.add_assoc]; exact hdm (1 + i) (by omega))) (codes "posted") 0 (n 1)
    (.const (BitVec.ofNat 64 1)) true rfl (fun _ _ => rfl) (by decide) (by decide)
  refine ⟨_, lower_and (x := eAnd (eLt (n 6) (v "ln")) (eEq (byte (Syntax.atOff (v "a") ArticleProg.xElem)) (n 46)))
    (lower_and rfl rfl) (lower_and hEs (lower_or2 (x := eEq (v "ln") (n 7)) rfl rfl)), fun u h => ?_⟩
  have hl : min 65 B.length < 2 ^ 63 := by omega
  have hb : ∀ i, i < 8 → eval u (.loadByte (.op .add (.var "a") (.const (BitVec.ofNat 64 (ArticleProg.xElem + i))))) =
      some (BitVec.ofNat 64 (tb i).toNat) := fun i hi =>
    loadByte_eval (atA_eval (vals_lookup h.1.vals hla)) (loadsAt_eq h (hdm i (by omega)))
  have hvl := ev_var (vals_lookup h.1.vals hln)
  refine (FramerCode.eval_and (FramerCode.eval_and (FramerCode.eval_lt (by decide) hl rfl hvl)
    (FramerCode.eval_eq (Nat.lt_trans (tb 0).isLt (by decide)) (by decide) (hb 0 (by decide)) rfl))
    (FramerCode.eval_and (hv u h) (FramerCode.eval_or2 (FramerCode.eval_eq (by omega) (by decide) hvl rfl)
      (FramerCode.eval_eq (Nat.lt_trans (tb 7).isLt (by decide)) (by decide) (hb 7 (by decide)) rfl)))).trans ?_
  have hlow : codes (ArticleProg.lowerS "posted") = codes "posted" := by decide +kernel
  have := posted_test B tb tb' (fun i hi hl => loadsAt_bytes hout.2.1 i (by omega) hl) fun i hi hl => by
    show (memLoadByte M s1.memaddrs s1.be (at_ A (ArticleProg.xElem + 1 + i))).getD 0 = _
    rw [Nat.add_assoc]; exact loadsAt_bytes hout.2.1 (1 + i) (by omega) hl
  unfold spellsOK at this; rw [hlow] at this
  rw [Bool.true_and, this]

/-- **`artPosted` finds whether Path's body holds the diagnostic `.POSTED`**, if it returns. -/
theorem artPosted_ok (o : Oracle σ) {A : Word} {s1 : PancakeState σ} (hA : Area ArticleProg.ofs A s1)
    (hD : ArtDom A s1.memaddrs) (hcode : ArtCode s1.code) (hb : s1.memory (at_ A aBroken) = 0) {a : Bytes}
    (hlen : a.length ≤ artMax) (hin : InputAt s1.memory s1.memaddrs s1.be A a) {S E : Nat} (hSE : S ≤ E)
    (hE : E ≤ a.length) (hs : s1.locals "s" = some (BitVec.ofNat 64 S))
    (he : s1.locals "e" = some (BitVec.ofNat 64 E)) :
    ∃ body, Lower.lower (gd ArticleProg.artPosted) = some body ∧
      SafeR o (fun s => s = s1) body (PostRet A a S E s1.memory) fun _ => False := by
  refine body_of ?_
  show FragR o _ (guardL ArticleProg.artPosted.body) _ _
  rw [artPosted_body]
  refine fragR_conseq (list_frag o hA hD hcode hb hlen hin hSE hE (sep := ArticleSpec.BANG)
    (T := ArticleSpec.isPosted) (lowK_any _ (k := .skip) rfl) (lowK_any _ (k := .skip) rfl)
    (fun y hy => by
      change y ∈ ["ln"] at hy
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hy; subst hy; exact ⟨by decide, fun _ => rfl⟩)
    (fun l m m' B hla hfl hout => ?_) fun w m hw hf => ⟨?_, hf⟩) (entry_two hs he) fun _ h => h
  · obtain ⟨X, hX, hXv⟩ := postedE_eval hD hA.hA (l := ("ln", BitVec.ofNat 64 (min 65 B.length)) :: l) hla hout rfl
    refine ⟨[("ln", BitVec.ofNat 64 (min 65 B.length))], X, runF_dec o (wd_lower 21) (hfl "ln" (by decide))
      fun u h => ?_, hX, hXv⟩
    rw [wordAt_eval hD h hla (i := 21) (by decide)]; exact congrArg some hout.2.2.1
  · rw [path_any hSE hE rfl]; exact hw

/-! ## The groups the server carries -/

/-- Where group `j`'s entry lies: its length, then its bytes from 8 on. -/
def gAt (j : Nat) : Nat := ArticleProg.xGroups + j * ArticleProg.groupSize

theorem xGroups_eq : ArticleProg.xGroups = 498704 := rfl

theorem gAt_dom {A : Word} {dm : Word → Bool} (hD : ArtDom A dm) {j : Nat} (hj : j < 64) : dm (at_ A (gAt j)) = true :=
  hD _ (by have := sets_le_X; have := X_val; simp only [gAt, xGroups_eq, ArticleProg.groupSize]; omega)
    (by simp only [gAt, xGroups_eq, xFirst_eq, ArticleProg.groupSize]; omega)
    (by simp only [gAt, xGroups_eq, ArticleProg.groupSize]; omega)

/-- The groups `gs` in the context's table, at most 64, each of at most 64 bytes. -/
def GroupsAt (A : Word) (dm : Word → Bool) (be : Bool) (gs : List Bytes) (m : Word → Word) : Prop :=
  gs.length ≤ 64 ∧ m (at_ A ArticleProg.xGroupsN) = BitVec.ofNat 64 gs.length ∧
    ∀ j, j < gs.length → gs[j]!.length ≤ 64 ∧ m (at_ A (gAt j)) = BitVec.ofNat 64 gs[j]!.length ∧
      BytesAt A dm be (gAt j + 8) 64 gs[j]! m

/-- The place of the first group that is `B`, or -1. -/
def knownW (gs : List Bytes) (B : Bytes) : Word :=
  match gs.findIdx? (· == B) with
  | some j => BitVec.ofNat 64 j
  | none => BitVec.ofNat 64 (2 ^ 64 - 1)

/-- What `artKnown` gives back: the place of the name among the groups, the memory as it was. -/
def KnownRet (gs : List Bytes) (B : Bytes) (m0 : Word → Word) : Ret := fun v m => m = m0 ∧ v = knownW gs B

/-- Whether the first `i` bytes of `B` and `G` agree. -/
def okUp (B G : Bytes) (i : Nat) : Bool := (List.range i).all fun k => B[k]! == G[k]!

theorem okUp_succ (B G : Bytes) (i : Nat) : okUp B G (i + 1) = (okUp B G i && B[i]! == G[i]!) := by
  simp [okUp, List.range_succ, List.all_append]

theorem okUp_full {B G : Bytes} (h : G.length = B.length) : okUp B G B.length = (G == B) := by
  apply Bool.eq_iff_iff.2
  rw [beq_iff_eq]
  unfold okUp
  rw [List.all_eq_true]
  constructor
  · intro hk
    refine List.ext_getElem h fun k h1 h2 => ?_
    have := hk k (List.mem_range.2 h2)
    rw [beq_iff_eq, getElem!_pos B k h2, getElem!_pos G k h1] at this
    exact this.symm
  · rintro rfl k _; exact beq_self_eq_true _

/-- `artKnown`'s comparison loop body. -/
def cmpBody : List Syntax.PStmt :=
  [kept "i" 63, ifs (ne (byte (eAdd (Syntax.atOff (v "a") ArticleProg.xElem) (v "i")))
      (byte (eAdd (Syntax.atOff (v "t") 8) (v "i")))) [.assign "ok" (n 0)], inc "i"]

/-- `artKnown`'s loop body. -/
def knownBody : List Syntax.PStmt :=
  [.dec "t" (eAdd (Syntax.atOff (v "a") ArticleProg.xGroups) (eMul (v "j") (n ArticleProg.groupSize))),
   ifs (eEq (.loadw 1 (v "t")) (v "ln"))
     [.dec "i" (n 0), .dec "ok" (n 1), .while (eLt (v "i") (v "ln")) cmpBody, ifs (v "ok") [.ret (v "j")]],
   inc "j"]

theorem artKnown_body : guardL ArticleProg.artKnown.body =
    [areaAt ArticleProg.ofs, kept "ln" 64, .dec "gn" (wd ArticleProg.xGroupsN), kept "gn" 64, .dec "j" (n 0),
     .while (eLt (v "j") (v "gn")) knownBody, .ret ArticleProg.neg1] := rfl

/-- `artKnown`'s locals in its loop. -/
def knownL (A : Word) (N L j : Nat) : List (String × Value) :=
  [("j", BitVec.ofNat 64 j), ("gn", BitVec.ofNat 64 N), ("a", A), ("ln", BitVec.ofNat 64 L)]

/-- `artKnown`'s locals in its comparison. -/
def cmpL (A : Word) (N L j i : Nat) (ok : Bool) : List (String × Value) :=
  ("ok", BitVec.ofNat 64 (bnat ok)) :: ("i", BitVec.ofNat 64 i) :: ("t", at_ A (gAt j)) :: knownL A N L j

theorem bytesAt_run {s1 u : PancakeState σ} {L : List (String × Value)} {M : Word → Word} (h : RunF s1 L (· = M) u)
    {A : Word} {o K : Nat} {B : Bytes} (hb : BytesAt A s1.memaddrs s1.be o K B M) {i : Nat} (hi : i < K)
    (hl : i < B.length) : memLoadByte u.memory u.memaddrs u.be (at_ A (o + i)) = some B[i]! := by
  rw [h.2, h.1.memaddrs, h.1.be]; exact hb i hi hl

theorem ne_bytes (b c : BitVec 8) : decide (BitVec.ofNat 64 b.toNat ≠ BitVec.ofNat 64 c.toNat) = !(b == c) := by
  by_cases h : b = c
  · subst h; simp
  · have : BitVec.ofNat 64 b.toNat ≠ BitVec.ofNat 64 c.toNat := fun e =>
      h (BitVec.eq_of_toNat_eq (DN.Compiler.NatToDec.ofNat64_inj (Nat.lt_trans b.isLt (by decide))
        (Nat.lt_trans c.isLt (by decide)) e))
    rw [decide_eq_true this, beq_eq_false_iff_ne.2 h]; rfl

/-- **`artKnown`'s comparison**: `ok` stays set exactly when group `G` at entry `j` agrees with `B`. -/
theorem cmp_loop (o : Oracle σ) {A : Word} {s1 : PancakeState σ} {m0 : Word → Word} {N j : Nat} {B G : Bytes}
    (hBG : G.length = B.length) (hB : B.length ≤ 64)
    (hEl : BytesAt A s1.memaddrs s1.be ArticleProg.xElem 64 B m0)
    (hGb : BytesAt A s1.memaddrs s1.be (gAt j + 8) 64 G m0) :
    Frag o [.while (eLt (v "i") (v "ln")) cmpBody] (RunF s1 (cmpL A N B.length j 0 true) (· = m0))
      (RunF s1 (cmpL A N B.length j B.length (okUp B G B.length)) (· = m0)) := by
  let I : Assn σ := fun u => ∃ i, RunF s1 (cmpL A N B.length j i (okUp B G i)) (· = m0) u ∧ i ≤ B.length
  have hIc : Safe.ClockFree I := fun u k ⟨i, h, hv⟩ => ⟨i, runF_clock _ _ _ u k h, hv⟩
  have hcond : ∀ u i, RunF s1 (cmpL A N B.length j i (okUp B G i)) (· = m0) u → i ≤ B.length →
      eval u (.cmp .less (.var "i") (.var "ln")) = some (bw (decide (i < B.length))) := fun u i h hi =>
    FramerCode.eval_lt (by omega) (by omega) (ev_var (vals_lookup h.1.vals rfl)) (ev_var (vals_lookup h.1.vals rfl))
  have hlow : LowKK cmpBody := lowK_any _ (k := .skip) rfl
  refine frag_conseq (frag_while o rfl hlow hIc (noDecl _ rfl) (fun u ⟨i, h, hv⟩ => ⟨_, hcond u i h hv⟩) ?_)
    (fun u h => ⟨0, h, Nat.zero_le _⟩) fun u ⟨⟨i, h, hv⟩, h0⟩ => ?_
  · refine frag_conseq (P0 := fun u => ∃ i, (fun i u => RunF s1 (cmpL A N B.length j i (okUp B G i)) (· = m0) u ∧
      i < B.length) i u) (frag_exists hlow fun i => ?_)
      (fun u ⟨⟨i, h, hv⟩, h0⟩ => ⟨i, h, by rw [hcond u i h hv] at h0; exact of_decide_eq_true (bw_ne0 h0)⟩)
      fun _ h => h
    refine frag_pure (i < B.length) (fun u h => h.2) hlow fun hi => ?_
    refine frag_conseq (P0 := RunF s1 (cmpL A N B.length j i (okUp B G i)) (· = m0)) ?_ (fun u h => h.1)
      fun _ h => h
    refine frag_append (xs := [_]) (kept_frag o (by decide) (runF_clock _ _ _)
      fun u h => ⟨i, vals_lookup h.1.vals rfl, by omega⟩) ?_
    refine frag_append (xs := [_]) (cond_set o rfl rfl rfl (b := !(B[i]! == G[i]!))
      (L' := cmpL A N B.length j i (okUp B G i && B[i]! == G[i]!)) (fun u h => by
        rw [← ne_bytes]
        refine ne_eval (loadByte_eval (by
          rw [ev_add (atA_eval (vals_lookup h.1.vals rfl)) (ev_var (vals_lookup h.1.vals rfl)), at_add])
          (bytesAt_run h hEl (by omega) (by omega))) (loadByte_eval (by
          rw [ev_add (ev_add (ev_var (vals_lookup h.1.vals rfl)) rfl) (ev_var (vals_lookup h.1.vals rfl)), at_add,
            at_add])
          (bytesAt_run h hGb (by omega) (by omega)))) (vx := BitVec.ofNat 64 0) (fun _ _ => rfl)
      (fun hb u h => runF_of h (by
        rw [show (B[i]! == G[i]!) = false by simpa using hb, Bool.and_false]
        repeat (refine lookups_cons rfl ?_)
        exact lookups_nil))
      fun hb u h => by rw [show (B[i]! == G[i]!) = true by simpa using hb, Bool.and_true]; exact h) ?_
    refine frag_conseq (set_to o rfl rfl (v := BitVec.ofNat 64 (i + 1)) (fun u h => ev_inc (vals_lookup h.1.vals rfl))
      (l' := cmpL A N B.length j (i + 1) (okUp B G (i + 1))) fun u h => runF_of h (by
        rw [okUp_succ]
        repeat (refine lookups_cons rfl ?_)
        exact lookups_nil)) (fun _ h => h) fun u h => ⟨i + 1, h, by omega⟩
  · rw [hcond u i h hv] at h0
    have hi : i = B.length := by have := of_decide_eq_false (bw_eq0 h0); omega
    rw [hi] at h; exact h

theorem knownW_some {gs : List Bytes} {B : Bytes} {j : Nat} (hj : j < gs.length) (he : gs[j]! = B)
    (hb : ∀ k, k < j → gs[k]! ≠ B) : knownW gs B = BitVec.ofNat 64 j := by
  have : gs.findIdx? (· == B) = some j := List.findIdx?_eq_some_iff_getElem.2 ⟨hj, by
    rw [← getElem!_pos gs j hj, he]; exact beq_self_eq_true _, fun k hk => by
    rw [← getElem!_pos gs k (by omega)]; simpa using hb k hk⟩
  simp only [knownW, this]

theorem knownW_none {gs : List Bytes} {B : Bytes} (hb : ∀ k, k < gs.length → gs[k]! ≠ B) :
    knownW gs B = BitVec.ofNat 64 (2 ^ 64 - 1) := by
  have : gs.findIdx? (· == B) = none := List.findIdx?_eq_none_iff.2 fun x hx => by
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hx
    have := hb k hk; rw [getElem!_pos gs k hk] at this; simpa using this
  simp only [knownW, this]

/-- **`artKnown` finds the name in `xElem`, of `ln` bytes, among the groups**, if it returns. -/
theorem artKnown_ok (o : Oracle σ) {A : Word} {s1 : PancakeState σ} (hA : Area ArticleProg.ofs A s1)
    (hD : ArtDom A s1.memaddrs) {gs : List Bytes} (hG : GroupsAt A s1.memaddrs s1.be gs s1.memory) {B : Bytes}
    (hB : B.length ≤ 64) (hEl : BytesAt A s1.memaddrs s1.be ArticleProg.xElem 64 B s1.memory)
    (hl : s1.locals "ln" = some (BitVec.ofNat 64 B.length)) :
    ∃ body, Lower.lower (gd ArticleProg.artKnown) = some body ∧
      SafeR o (fun s => s = s1) body (KnownRet gs B s1.memory) fun _ => False := by
  obtain ⟨hgl, hgn, hgj⟩ := hG
  refine body_of ?_
  show FragR o _ (guardL ArticleProg.artKnown.body) _ _
  rw [artKnown_body]
  obtain ⟨EA, hEA⟩ := atOff_lower ArticleProg.ofs
  refine fragR_conseq (P0 := RunF s1 [("ln", BitVec.ofNat 64 B.length)] (· = s1.memory)) ?_ (entry_one hl)
    fun _ h => h
  refine fragR_append (xs := [_]) (fragR_of (runF_dec o hEA rfl (v := A) fun u h => areaAt_eval hA h.1.base hEA)) ?_
  refine fragR_append (xs := [_]) (fragR_of (kept_frag o (by decide) (runF_clock _ _ _)
    fun u h => ⟨_, vals_lookup h.1.vals rfl, hB⟩)) ?_
  refine fragR_append (xs := [_]) (fragR_of (runF_dec o (wd_lower 8) rfl (v := BitVec.ofNat 64 gs.length)
    fun u h => by rw [wordAt_eval hD h rfl (i := 8) (by decide)]; exact congrArg some hgn)) ?_
  refine fragR_append (xs := [_]) (fragR_of (kept_frag o (by decide) (runF_clock _ _ _)
    fun u h => ⟨_, vals_lookup h.1.vals rfl, hgl⟩)) ?_
  refine fragR_append (xs := [_]) (fragR_of (runF_dec o rfl rfl (v := BitVec.ofNat 64 0) fun _ _ => rfl)) ?_
  let I : Assn σ := fun u => ∃ j, RunF s1 (knownL A gs.length B.length j) (· = s1.memory) u ∧ j ≤ gs.length ∧
    ∀ k, k < j → gs[k]! ≠ B
  have hIc : Safe.ClockFree I := fun u k ⟨j, h, hv⟩ => ⟨j, runF_clock _ _ _ u k h, hv⟩
  have hcond : ∀ u j, RunF s1 (knownL A gs.length B.length j) (· = s1.memory) u → j ≤ gs.length →
      eval u (.cmp .less (.var "j") (.var "gn")) = some (bw (decide (j < gs.length))) := fun u j h hj =>
    FramerCode.eval_lt (by omega) (by omega) (ev_var (vals_lookup h.1.vals rfl)) (ev_var (vals_lookup h.1.vals rfl))
  have hlow : LowKK knownBody := lowK_any _ (k := .skip) rfl
  refine fragR_append (xs := [_]) (fragR_conseq (fragR_while o rfl hlow hIc
    (fun u z w ⟨j, h, hv⟩ hz => by
      change z ∈ ["t"] at hz
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hz; subst hz
      exact ⟨j, runF_restore h rfl w, hv⟩) (fun u ⟨j, h, hv⟩ => ⟨_, hcond u j h hv.1⟩) ?_)
    (fun u h => ⟨0, h, Nat.zero_le _, fun _ hk => absurd hk (Nat.not_lt_zero _)⟩) fun _ h => h) ?_
  · refine fragR_conseq (P0 := fun u => ∃ j, (fun j u => RunF s1 (knownL A gs.length B.length j) (· = s1.memory) u ∧
      (∀ k, k < j → gs[k]! ≠ B) ∧ j < gs.length) j u) (fragR_exists hlow fun j => ?_)
      (fun u ⟨⟨j, h, hv⟩, h0⟩ => ⟨j, h, hv.2, by
        rw [hcond u j h hv.1] at h0; exact of_decide_eq_true (bw_ne0 h0)⟩) fun _ h => h
    refine fragR_pure ((∀ k, k < j → gs[k]! ≠ B) ∧ j < gs.length) (fun u h => h.2) hlow fun ⟨hb, hj⟩ => ?_
    refine fragR_conseq (P0 := RunF s1 (knownL A gs.length B.length j) (· = s1.memory)) ?_ (fun u h => h.1)
      fun _ h => h
    obtain ⟨hG64, hGw, hGb⟩ := hgj j hj
    refine fragR_append (xs := [_]) (fragR_of (runF_dec o rfl rfl (v := at_ A (gAt j)) fun u h => by
      rw [ev_add (atA_eval (vals_lookup h.1.vals rfl)) (ev_mulc (vals_lookup h.1.vals rfl)), at_add]; rfl)) ?_
    let Lt := ("t", at_ A (gAt j)) :: knownL A gs.length B.length j
    let Q : Assn σ := fun u => RunF s1 Lt (· = s1.memory) u ∧ gs[j]! ≠ B
    have hQc : Safe.ClockFree Q := fun u k h => ⟨runF_clock _ _ _ u k h.1, h.2⟩
    refine fragR_append (xs := [_]) (fragR_if o rfl (lowK_any _ (k := .skip) rfl) lowKK_nil hQc
      (fun u y w h hy => by
        change y ∈ ["i", "ok"] at hy
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
        rcases hy with rfl | rfl
        · exact ⟨runF_restore h.1 rfl w, h.2⟩
        · exact ⟨runF_restore h.1 rfl w, h.2⟩) (fun _ _ _ _ hy => by cases hy)
      (b := decide (gs[j]!.length = B.length)) (fun u h => FramerCode.eval_eq (by omega) (by omega)
        ((loadA_eval h.1.memaddrs (gAt_dom hD (by omega)) (ev_var (vals_lookup h.1.vals rfl))).trans
          (by rw [h.2, hGw])) (ev_var (vals_lookup h.1.vals rfl))) (fun hb' => ?_) fun hb' => ?_) ?_
    · have hlen : gs[j]!.length = B.length := of_decide_eq_true hb'
      refine fragR_append (xs := [_]) (fragR_of (runF_dec o rfl rfl (v := BitVec.ofNat 64 0) fun _ _ => rfl)) ?_
      refine fragR_append (xs := [_]) (fragR_of (runF_dec o rfl rfl (v := BitVec.ofNat 64 1) fun _ _ => rfl)) ?_
      refine fragR_append (xs := [_]) (fragR_of (cmp_loop o (N := gs.length) hlen hB hEl hGb)) ?_
      rw [okUp_full hlen]
      by_cases he : gs[j]! = B
      · refine fragR_ifT o rfl (lowKK_ret rfl) lowKK_nil rfl rfl hQc
          (fun u h => (ev_var (vals_lookup h.1.vals rfl)).trans (by rw [he, beq_self_eq_true]; rfl)) ?_
        refine fragR_ret o rfl fun u h => ⟨_, ev_var (vals_lookup h.1.vals rfl), h.2, ?_⟩
        rw [knownW_some hj he hb]
      · refine fragR_ifF o rfl (lowKK_ret rfl) lowKK_nil rfl rfl hQc
          (fun u h => (ev_var (vals_lookup h.1.vals rfl)).trans (by
            rw [show (gs[j]! == B) = false by simpa using he]; rfl))
          (fragR_of (frag_nil o fun u h => ⟨runF_mono h (fun q hq => List.mem_cons_of_mem _
            (List.mem_cons_of_mem _ hq)) fun _ e => e, he⟩))
    · have hne : gs[j]! ≠ B := fun e => by rw [e] at hb'; simp at hb'
      exact fragR_of (frag_nil o fun u h => ⟨h, hne⟩)
    refine fragR_of (frag_pure (gs[j]! ≠ B) (fun u h => h.2) (lowK_any _ (k := .skip) rfl) fun hne =>
      frag_conseq (set_to o rfl rfl (v := BitVec.ofNat 64 (j + 1)) (fun u h => ev_inc (vals_lookup h.1.vals rfl))
        (l' := knownL A gs.length B.length (j + 1)) fun u h => runF_of h (by
          repeat (refine lookups_cons rfl ?_)
          exact lookups_nil)) (fun u h => h.1) fun u h => ⟨j + 1, h, hj, fun k hk => ?_⟩)
    rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk | rfl
    · exact hb k hk
    · exact hne
  refine fragR_ret o rfl fun u ⟨⟨j, h, hj, hb⟩, h0⟩ => ⟨_, rfl, h.2, ?_⟩
  rw [hcond u j h hj] at h0
  have hjE : j = gs.length := by have := of_decide_eq_false (bw_eq0 h0); omega
  subst hjE
  rw [knownW_none hb]

/-! ## The groups an article names -/

/-- The groups of `F` the server carries, each once, in order. -/
def Kf (gs F : List Bytes) : List Bytes := (F.filter (gs.contains ·)).eraseDups

theorem Kf_snoc (gs F : List Bytes) (x : Bytes) : Kf gs (F ++ [x]) =
    if gs.contains x && !(Kf gs F).contains x then Kf gs F ++ [x] else Kf gs F := by
  unfold Kf
  rw [List.filter_append, List.eraseDups_append, List.filter_cons, List.filter_nil]
  have hm : (F.filter (gs.contains ·)).contains x = ((F.filter (gs.contains ·)).eraseDups).contains x := by
    rw [Bool.eq_iff_iff, List.contains_iff_mem, List.contains_iff_mem, List.mem_eraseDups]
  cases hx : gs.contains x
  · simp
  · rw [if_pos rfl, List.cons_removeAll, List.nil_removeAll, ← hm]
    cases (F.filter (gs.contains ·)).contains x
    · rfl
    · simp

theorem Kf_mem {gs F : List Bytes} {g : Bytes} (h : g ∈ Kf gs F) : g ∈ gs := by
  unfold Kf at h
  rw [List.mem_eraseDups, List.mem_filter] at h
  exact List.contains_iff_mem.1 h.2

/-- A list with no repeats, all of whose members are in `m`, is no longer than `m`. -/
theorem nodup_len {α : Type} [BEq α] [LawfulBEq α] : ∀ {l m : List α}, l.Nodup → (∀ x ∈ l, x ∈ m) →
    l.length ≤ m.length
  | [], _, _, _ => Nat.zero_le _
  | a :: l, m, hn, hs => by
    rw [List.nodup_cons] at hn
    have ha : a ∈ m := hs a List.mem_cons_self
    have := nodup_len (m := m.erase a) hn.2 fun x hx =>
      (List.mem_erase_of_ne (fun (e : x = a) => hn.1 (e ▸ hx))).2 (hs x (List.mem_cons_of_mem _ hx))
    rw [List.length_erase_of_mem ha] at this
    have := List.length_pos_of_mem ha
    simp only [List.length_cons]; omega

/-- Group `g`'s place among the groups. -/
def gIdx (gs : List Bytes) (g : Bytes) : Nat := (gs.findIdx? (· == g)).getD 0

theorem gIdx_mem {gs : List Bytes} {g : Bytes} (hg : g ∈ gs) :
    gs.findIdx? (· == g) = some (gIdx gs g) ∧ gIdx gs g < gs.length ∧ gs[gIdx gs g]! = g := by
  cases hf : gs.findIdx? (· == g) with
  | none =>
    have := List.findIdx?_eq_none_iff.1 hf g hg
    simp at this
  | some j =>
    obtain ⟨hj, he, -⟩ := List.findIdx?_eq_some_iff_getElem.1 hf
    have hgj : gIdx gs g = j := by simp only [gIdx, hf, Option.getD_some]
    rw [hgj, getElem!_pos gs j hj]
    exact ⟨rfl, hj, by simpa using he⟩

theorem gIdx_inj {gs : List Bytes} {g h : Bytes} (hg : g ∈ gs) (hh : h ∈ gs) (e : gIdx gs g = gIdx gs h) : g = h := by
  rw [← (gIdx_mem hg).2.2, ← (gIdx_mem hh).2.2, e]

theorem knownW_in {gs : List Bytes} {g : Bytes} (hg : g ∈ gs) : knownW gs g = BitVec.ofNat 64 (gIdx gs g) := by
  simp only [knownW, (gIdx_mem hg).1]

theorem knownW_out {gs : List Bytes} {g : Bytes} (hg : g ∉ gs) : knownW gs g = BitVec.ofNat 64 (2 ^ 64 - 1) := by
  have : gs.findIdx? (· == g) = none := List.findIdx?_eq_none_iff.2 fun x hx => by
    simp only [beq_eq_false_iff_ne, ne_eq]; rintro rfl; exact hg hx
  simp only [knownW, this]

/-- The known groups' places, `K`'s, in `xKnown`, their count in `xKnownN`. -/
def KnownAt (A : Word) (gs K : List Bytes) (m : Word → Word) : Prop :=
  m (at_ A ArticleProg.xKnownN) = BitVec.ofNat 64 K.length ∧
    ∀ i, i < K.length → m (at_ A (ArticleProg.xKnown + i * 8)) = BitVec.ofNat 64 (gIdx gs K[i]!)

/-- The words `artGroups` writes but `artElem`'s. -/
def gWrites (y : Nat) : Prop :=
  y = ArticleProg.xKnownN ∨ y = ArticleProg.xGCount ∨ y = ArticleProg.xGRes ∨ y = ArticleProg.xGKnown ∨
    ArticleProg.xKnown ≤ y ∧ y < ArticleProg.xGroups

/-- The words `artGroups` and the `artElem` it calls write. -/
def gScratch (A : Word) (x : Word) : Prop := elemScratch A x ∨ ∃ y, gWrites y ∧ x = at_ A y

theorem gWrites_lt {y : Nat} (h : gWrites y) : y < ArticleProg.xGroups := by
  simp only [gWrites, ArticleProg.xKnownN, ArticleProg.xGCount, ArticleProg.xGRes, ArticleProg.xGKnown,
    ArticleProg.w, X_val, xGroups_eq] at h ⊢
  omega

/-- A word of the article's outside both scratches: below `xKnownN`, or among the groups and past them below
`xElem`. -/
theorem not_gscr {A : Word} {z : Nat} (hz : z < ArticleProg.xKnownN ∨ ArticleProg.xGroups ≤ z ∧ z < ArticleProg.xElem) :
    ¬gScratch A (at_ A z) := by
  have hE := xElem_eq; have hX := X_val; have hG := xGroups_eq
  simp only [ArticleProg.xKnownN, ArticleProg.w] at hz
  rintro (h | ⟨y, hy, e⟩)
  · rcases h with ⟨k, hk, h⟩ | h | h
    · exact DN.News.ScanRun.at_ne (by omega) (by omega) (by omega) h
    · exact DN.News.ScanRun.at_ne (by omega) (w_lt64 (i := 21) (by decide)) (by
        simp only [ArticleProg.w]; omega) h
    · exact DN.News.ScanRun.at_ne (by omega) (w_lt64 (i := 22) (by decide)) (by
        simp only [ArticleProg.w]; omega) h
  · have hyl := gWrites_lt hy
    have := DN.News.ScanRun.at_inj (by omega) (by omega) e
    subst this
    simp only [gWrites, ArticleProg.xKnownN, ArticleProg.xGCount, ArticleProg.xGRes, ArticleProg.xGKnown,
      ArticleProg.xKnown, ArticleProg.w] at hy
    omega

theorem bytesAt_frame {A : Word} {dm : Word → Bool} {be : Bool} {o K : Nat} {B : Bytes} {m m' : Word → Word}
    (h : BytesAt A dm be o K B m) (hk : ∀ i, i < K → i < B.length → m' (byteAlign (at_ A (o + i))) =
      m (byteAlign (at_ A (o + i)))) : BytesAt A dm be o K B m' := fun i hi hl => by
  have := h i hi hl
  unfold memLoadByte at this ⊢; rw [hk i hi hl]; exact this

theorem groupsAt_frame {A : Word} (hA8 : A.toNat % 8 = 0) {dm : Word → Bool} {be : Bool} {gs : List Bytes}
    {m m' : Word → Word} (hfr : ∀ x, ¬gScratch A x → m' x = m x) (hG : GroupsAt A dm be gs m) :
    GroupsAt A dm be gs m' := by
  have hG8 := xGroups_eq; have hE := xElem_eq
  have h8 : ArticleProg.xGroupsN < ArticleProg.xKnownN := by
    simp only [ArticleProg.xGroupsN, ArticleProg.xKnownN, ArticleProg.w]; omega
  refine ⟨hG.1, ?_, fun j hj => ?_⟩
  · rw [hfr _ (not_gscr (.inl h8))]; exact hG.2.1
  have hj64 : j < 64 := by have := hG.1; omega
  obtain ⟨h1, h2, h3⟩ := hG.2.2 j hj
  refine ⟨h1, by rw [hfr _ (not_gscr (.inr (by simp only [gAt, ArticleProg.groupSize]; omega)))]; exact h2,
    bytesAt_frame h3 fun i hi _ => ?_⟩
  rw [DN.News.ScanRun.align_at hA8]
  exact hfr _ (not_gscr (.inr (by simp only [gAt, ArticleProg.groupSize]; omega)))

theorem knownAt_frame {A : Word} {gs K : List Bytes} {m m' : Word → Word} (hK : KnownAt A gs K m)
    (hl : K.length ≤ 64) (hfr : ∀ x, ¬elemScratch A x → m' x = m x) : KnownAt A gs K m' := by
  have hE := xElem_eq; have hX := X_val
  have hne : ∀ z, z = ArticleProg.xKnownN ∨ ArticleProg.xKnown ≤ z ∧ z < ArticleProg.xGroups →
      ¬elemScratch A (at_ A z) := fun z hz => by
    simp only [ArticleProg.xKnownN, ArticleProg.xKnown, ArticleProg.w, xGroups_eq] at hz
    rintro (⟨k, hk, h⟩ | h | h)
    · exact DN.News.ScanRun.at_ne (by omega) (by omega) (by omega) h
    · exact DN.News.ScanRun.at_ne (by omega) (w_lt64 (i := 21) (by decide)) (by
        simp only [ArticleProg.w]; omega) h
    · exact DN.News.ScanRun.at_ne (by omega) (w_lt64 (i := 22) (by decide)) (by
        simp only [ArticleProg.w]; omega) h
  constructor
  · rw [hfr _ (hne _ (.inl rfl))]; exact hK.1
  · intro i hi
    rw [hfr _ (hne _ (.inr (by simp only [ArticleProg.xKnown, ArticleProg.w, xGroups_eq]; omega)))]
    exact hK.2 i hi

theorem mem_artKnown : gd ArticleProg.artKnown ∈
    ArticleProg.functions ArticleSpec.spec (ArticleProg.entries ArticleSpec.spec) .none :=
  List.mem_append_right _ (List.mem_map.2 ⟨ArticleProg.artKnown, by simp, rfl⟩)

/-- **A call of `artKnown`**, the check after it passed: the name's place among the groups, the memory as it was. -/
theorem knownCall_frag (o : Oracle σ) {R : Ret} {A : Word} {s0 : PancakeState σ} (hA : Area ArticleProg.ofs A s0)
    (hD : ArtDom A s0.memaddrs) (hcode : ArtCode s0.code) {rt : String} (hra : rt ≠ "a") {l : List (String × Value)}
    (hla : l.lookup "a" = some A) (hrt : Fresh rt l = true) {m : Word → Word} {gs : List Bytes}
    (hG : GroupsAt A s0.memaddrs s0.be gs m) {B : Bytes} (hB : B.length ≤ 64)
    (hEl : BytesAt A s0.memaddrs s0.be ArticleProg.xElem 64 B m) (hb : m (at_ A aBroken) = 0)
    (hln : l.lookup "ln" = some (BitVec.ofNat 64 B.length)) :
    FragR o R (guardS (.call rt "artKnown" [v "ln"])) (RunF s0 l (· = m))
      (RunF s0 ((rt, knownW gs B) :: l) (· = m)) := by
  refine fragR_conseq (gcall_frag o hA hcode hra (f := ArticleProg.artKnown) mem_artKnown (by decide)
    (args := [.var "ln"]) rfl hla (vs := [BitVec.ofNat 64 B.length]) rfl
    (fun u h => by simp only [evalArgs, ev_var (vals_lookup h.1.vals hln)]) (Rf := KnownRet gs B)
    (fun s1 hA1 _ hm hbe hloc hF => artKnown_ok o hA1 (by rw [hm]; exact hD) (by rw [hF, hm, hbe]; exact hG) hB
      (by rw [hF, hm, hbe]; exact hEl) ((hloc "ln").trans rfl)) hrt
    (G := fun v m' => v = knownW gs B ∧ m' = m) (fun m1 m' v hm hr => ⟨hr.2, hr.1.trans hm⟩)
    fun v m' h => by rw [h.2]; exact hb) (fun u h => h) fun u ⟨v, h⟩ => ?_
  obtain ⟨hv, hm⟩ := h.2
  subst hv; exact ⟨h.1, hm⟩

/-- `artGroups`' locals in its loop. -/
def grpL (S E : Nat) (A : Word) (p cnt : Nat) (rs kn : Bool) : List (String × Value) :=
  [("p", BitVec.ofNat 64 p), ("kn", BitVec.ofNat 64 (bnat kn)), ("rs", BitVec.ofNat 64 (bnat rs)),
   ("cnt", BitVec.ofNat 64 cnt), ("a", A), ("s", BitVec.ofNat 64 S), ("e", BitVec.ofNat 64 E)]

/-- `artGroups`' locals once the group is found: its place, the element's length, where the next starts. -/
def foundL (S E : Nat) (A : Word) (p cnt : Nat) (rs : Bool) (J ln nq : Nat) : List (String × Value) :=
  ("j", BitVec.ofNat 64 J) :: ("ln", BitVec.ofNat 64 ln) :: ("q", BitVec.ofNat 64 nq) :: grpL S E A p cnt rs true

/-- `artGroups`' search of a place among those kept. -/
def dupBody : List Syntax.PStmt :=
  [kept "x" (ArticleProg.knownMax - 1),
   ifs (eEq (.loadw 1 (eAdd (Syntax.atOff (v "a") ArticleProg.xKnown) (eMul (v "x") (n 8)))) (v "j"))
     [.assign "dup" (n 1)],
   inc "x"]

/-- Whether one of the first `x` groups kept has place `J`. -/
def dupUp (gs K : List Bytes) (J x : Nat) : Bool := (List.range x).any fun i => decide (gIdx gs K[i]! = J)

theorem dupUp_succ (gs K : List Bytes) (J x : Nat) :
    dupUp gs K J (x + 1) = (dupUp gs K J x || decide (gIdx gs K[x]! = J)) := by
  simp [dupUp, List.range_succ, List.any_append]

/-- With every group kept carried, the search finds `g`'s place exactly when `g` is kept. -/
theorem dupUp_full {gs K : List Bytes} (hKs : ∀ g ∈ K, g ∈ gs) {g : Bytes} (hg : g ∈ gs) :
    dupUp gs K (gIdx gs g) K.length = K.contains g := by
  apply Bool.eq_iff_iff.2
  rw [List.contains_iff_mem]
  unfold dupUp
  rw [List.any_eq_true]
  constructor
  · rintro ⟨i, hi, he⟩
    have hi' := List.mem_range.1 hi
    have hm : K[i]! ∈ K := by rw [getElem!_pos K i hi']; exact List.getElem_mem hi'
    rw [← gIdx_inj (hKs _ hm) hg (of_decide_eq_true he)]; exact hm
  · intro hk
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hk
    exact ⟨i, List.mem_range.2 hi, by rw [getElem!_pos K i hi]; exact decide_eq_true rfl⟩

/-- **The search among the places kept**: `dup` ends set exactly when one of them is `J`. -/
theorem dup_loop (o : Oracle σ) {A : Word} {s1 : PancakeState σ} (hD : ArtDom A s1.memaddrs) {gs K : List Bytes}
    {M : Word → Word} (hK : KnownAt A gs K M) (hKl : K.length ≤ 64) (hgs : ∀ g ∈ K, gIdx gs g < 64)
    {S E p cnt J ln nq : Nat} {rs : Bool} (hJ : J < 64) :
    let L := fun x d => ("dup", BitVec.ofNat 64 (bnat d)) :: ("x", BitVec.ofNat 64 x) ::
      ("kc", BitVec.ofNat 64 K.length) :: foundL S E A p cnt rs J ln nq
    Frag o [.while (eLt (v "x") (v "kc")) dupBody] (RunF s1 (L 0 false) (· = M))
      (RunF s1 (L K.length (dupUp gs K J K.length)) (· = M)) := by
  intro L
  let I : Assn σ := fun u => ∃ x, RunF s1 (L x (dupUp gs K J x)) (· = M) u ∧ x ≤ K.length
  have hIc : Safe.ClockFree I := fun u k ⟨x, h, hv⟩ => ⟨x, runF_clock _ _ _ u k h, hv⟩
  have hcond : ∀ u x, RunF s1 (L x (dupUp gs K J x)) (· = M) u → x ≤ K.length →
      eval u (.cmp .less (.var "x") (.var "kc")) = some (bw (decide (x < K.length))) := fun u x h hx =>
    FramerCode.eval_lt (by omega) (by omega) (ev_var (vals_lookup h.1.vals rfl)) (ev_var (vals_lookup h.1.vals rfl))
  have hlow : LowKK dupBody := lowK_any _ (k := .skip) rfl
  refine frag_conseq (frag_while o rfl hlow hIc (noDecl _ rfl) (fun u ⟨x, h, hv⟩ => ⟨_, hcond u x h hv⟩) ?_)
    (fun u h => ⟨0, h, Nat.zero_le _⟩) fun u ⟨⟨x, h, hv⟩, h0⟩ => ?_
  · refine frag_conseq (P0 := fun u => ∃ x, (fun x u => RunF s1 (L x (dupUp gs K J x)) (· = M) u ∧
      x < K.length) x u) (frag_exists hlow fun x => ?_)
      (fun u ⟨⟨x, h, hv⟩, h0⟩ => ⟨x, h, by rw [hcond u x h hv] at h0; exact of_decide_eq_true (bw_ne0 h0)⟩)
      fun _ h => h
    refine frag_pure (x < K.length) (fun u h => h.2) hlow fun hx => ?_
    refine frag_conseq (P0 := RunF s1 (L x (dupUp gs K J x)) (· = M)) ?_ (fun u h => h.1) fun _ h => h
    refine frag_append (xs := [_]) (kept_frag o (by decide) (runF_clock _ _ _)
      fun u h => ⟨x, vals_lookup h.1.vals rfl, by simp only [ArticleProg.knownMax]; omega⟩) ?_
    have hgx : gIdx gs K[x]! < 64 := hgs _ (by rw [getElem!_pos K x hx]; exact List.getElem_mem hx)
    have hdm : s1.memaddrs (at_ A (ArticleProg.xKnown + x * 8)) = true :=
      hD _ (by have := sets_le_X; have := X_val; simp only [ArticleProg.xKnown, ArticleProg.w]; omega)
        (by simp only [ArticleProg.xKnown, ArticleProg.w, X_val, xFirst_eq]; omega)
        (by simp only [ArticleProg.xKnown, ArticleProg.w, X_val]; omega)
    refine frag_append (xs := [_]) (cond_set o rfl rfl rfl (b := decide (gIdx gs K[x]! = J))
      (L' := L x (dupUp gs K J x || decide (gIdx gs K[x]! = J))) (fun u h => FramerCode.eval_eq (by omega)
        (by omega) ((loadA_eval h.1.memaddrs hdm (by
          rw [ev_add (atA_eval (vals_lookup h.1.vals rfl)) (ev_mulc (vals_lookup h.1.vals rfl)),
            at_add])).trans (by rw [h.2, hK.2 x hx])) (ev_var (vals_lookup h.1.vals rfl)))
      (vx := BitVec.ofNat 64 1) (fun _ _ => rfl)
      (fun hb u h => runF_of h (by
        rw [hb, Bool.or_true]
        repeat (refine lookups_cons rfl ?_)
        exact lookups_nil))
      fun hb u h => by rw [hb, Bool.or_false]; exact h) ?_
    refine frag_conseq (set_to o rfl rfl (v := BitVec.ofNat 64 (x + 1)) (fun u h => ev_inc (vals_lookup h.1.vals rfl))
      (l' := L (x + 1) (dupUp gs K J (x + 1))) fun u h => runF_of h (by
        rw [dupUp_succ]
        repeat (refine lookups_cons rfl ?_)
        exact lookups_nil)) (fun _ h => h) fun u h => ⟨x + 1, h, by omega⟩
  · rw [hcond u x h hv] at h0
    have hx : x = K.length := by have := of_decide_eq_false (bw_eq0 h0); omega
    rw [hx] at h; exact h

/-- `artGroups` with a group found: its place kept, if not kept before. -/
def addS : List Syntax.PStmt :=
  [.assign "kn" (n 1), .dec "kc" (wd ArticleProg.xKnownN), kept "kc" ArticleProg.knownMax, .dec "x" (n 0),
   .dec "dup" (n 0), .while (eLt (v "x") (v "kc")) dupBody,
   ifs (eAnd (eEq (v "dup") (n 0)) (eLt (v "kc") (n ArticleProg.knownMax)))
     [.store (eAdd (Syntax.atOff (v "a") ArticleProg.xKnown) (eMul (v "kc") (n 8))) (v "j"),
      setW ArticleProg.xKnownN (eAdd (v "kc") (n 1))]]

/-- The groups kept after group `x`. -/
def kAdd (K : List Bytes) (x : Bytes) : List Bytes := if K.contains x then K else K ++ [x]

theorem kAdd_len {gs K : List Bytes} (hKn : K.Nodup) (hKs : ∀ g ∈ K, g ∈ gs) {x : Bytes} (hx : x ∈ gs)
    (hk : K.contains x = false) : K.length < gs.length := by
  have hn : (K ++ [x]).Nodup := List.nodup_append.2 ⟨hKn, List.nodup_cons.2 ⟨List.not_mem_nil, List.nodup_nil⟩,
    fun a ha b hb e => by
      simp only [List.mem_singleton] at hb; subst hb; subst e
      exact absurd (List.contains_iff_mem.2 ha) (by rw [hk]; decide)⟩
  have := nodup_len hn fun g hg => by
    rcases List.mem_append.1 hg with hg | hg
    · exact hKs g hg
    · rw [List.mem_singleton.1 hg]; exact hx
  simp only [List.length_append, List.length_singleton] at this; omega

/-- **A group found, its place kept** if it was not, the words `artGroups` writes changed only. -/
theorem add_frag (o : Oracle σ) {A : Word} {s1 : PancakeState σ} (hD : ArtDom A s1.memaddrs) {gs K : List Bytes}
    (hgl : gs.length ≤ 64) {M : Word → Word} (hK : KnownAt A gs K M) (hKn : K.Nodup) (hKs : ∀ g ∈ K, g ∈ gs)
    {x : Bytes} (hx : x ∈ gs) {S E p cnt ln nq : Nat} {rs kn : Bool} :
    Frag o addS (RunF s1 (("j", BitVec.ofNat 64 (gIdx gs x)) :: ("ln", BitVec.ofNat 64 ln) ::
        ("q", BitVec.ofNat 64 nq) :: grpL S E A p cnt rs kn) (· = M))
      (fun u => ∃ M', RunF s1 (foundL S E A p cnt rs (gIdx gs x) ln nq) (· = M') u ∧
        (∀ y, ¬gScratch A y → M' y = M y) ∧ KnownAt A gs (kAdd K x) M') := by
  have hKl : K.length ≤ 64 := Nat.le_trans (nodup_len hKn hKs) hgl
  have hgs : ∀ g ∈ K, gIdx gs g < 64 := fun g hg => Nat.lt_of_lt_of_le (gIdx_mem (hKs g hg)).2.1 hgl
  have hJ : gIdx gs x < 64 := Nat.lt_of_lt_of_le (gIdx_mem hx).2.1 hgl
  let J := gIdx gs x
  let L := fun x d => ("dup", BitVec.ofNat 64 (bnat d)) :: ("x", BitVec.ofNat 64 x) ::
    ("kc", BitVec.ofNat 64 K.length) :: foundL S E A p cnt rs J ln nq
  refine frag_append (xs := [_]) (set_to o rfl rfl (v := BitVec.ofNat 64 1) (fun _ _ => rfl)
    (l' := foundL S E A p cnt rs J ln nq) fun u h => runF_of h (by
      repeat (refine lookups_cons rfl ?_)
      exact lookups_nil)) ?_
  refine frag_append (xs := [_]) (runF_dec o (wd_lower 14) rfl (v := BitVec.ofNat 64 K.length) fun u h => by
    rw [wordAt_eval hD h rfl (i := 14) (by decide)]; exact congrArg some hK.1) ?_
  refine frag_append (xs := [_]) (kept_frag o (by decide) (runF_clock _ _ _)
    fun u h => ⟨_, vals_lookup h.1.vals rfl, hKl⟩) ?_
  refine frag_append (xs := [_]) (runF_dec o rfl rfl (v := BitVec.ofNat 64 0) fun _ _ => rfl) ?_
  refine frag_append (xs := [_]) (runF_dec o rfl rfl (v := BitVec.ofNat 64 0) fun _ _ => rfl) ?_
  refine frag_append (xs := [_]) (dup_loop o (S := S) (E := E) (p := p) (cnt := cnt) (rs := rs) (ln := ln) (nq := nq)
    hD hK hKl hgs hJ) ?_
  rw [dupUp_full hKs hx]
  have hQc : Safe.ClockFree (fun u => ∃ M', RunF s1 (foundL S E A p cnt rs J ln nq) (· = M') u ∧
      (∀ y, ¬gScratch A y → M' y = M y) ∧ KnownAt A gs (kAdd K x) M') :=
    fun u k ⟨M', h, hv⟩ => ⟨M', runF_clock _ _ _ u k h, hv⟩
  have hdrop : ∀ u (d : Bool) (F : (Word → Word) → Prop), RunF s1 (L K.length d) F u →
      RunF s1 (foundL S E A p cnt rs J ln nq) F u := fun u d F h =>
    runF_mono h (fun q hq => List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hq))) fun _ e => e
  cases hk : K.contains x
  · -- not kept: kept now
    have hKlt : K.length < 64 := Nat.lt_of_lt_of_le (kAdd_len hKn hKs hx hk) hgl
    have hy : ArticleProg.xKnown ≤ ArticleProg.xKnown + K.length * 8 ∧
        ArticleProg.xKnown + K.length * 8 < ArticleProg.xGroups := by
      simp only [ArticleProg.xKnown, ArticleProg.w, X_val, xGroups_eq]; omega
    have hdm : s1.memaddrs (at_ A (ArticleProg.xKnown + K.length * 8)) = true :=
      hD _ (by have := sets_le_X; have := X_val; simp only [ArticleProg.xKnown, ArticleProg.w]; omega)
        (by simp only [ArticleProg.xKnown, ArticleProg.w, X_val, xFirst_eq]; omega)
        (by simp only [ArticleProg.xKnown, ArticleProg.w, X_val]; omega)
    let M1 := upd M (at_ A (ArticleProg.xKnown + K.length * 8)) (BitVec.ofNat 64 J)
    let M2 := upd M1 (at_ A ArticleProg.xKnownN) (BitVec.ofNat 64 (K.length + 1))
    refine DN.News.ArticleScan.frag_ifT o rfl (lowK_any _ (k := .skip) rfl) lowKK_nil rfl rfl hQc
      (fun u h => (FramerCode.eval_and (FramerCode.eval_eq (by decide) (by decide) (ev_var (vals_lookup h.1.vals rfl))
        rfl) (FramerCode.eval_lt (by omega) (by decide) (ev_var (vals_lookup h.1.vals rfl)) rfl)).trans
        (by rw [show decide (K.length < ArticleProg.knownMax) = true from decide_eq_true hKlt]; rfl)) ?_
    refine frag_append (xs := [_]) (runF_storeA o rfl rfl (y := ArticleProg.xKnown + K.length * 8) hdm
      (fun u h => by
        rw [ev_add (atA_eval (vals_lookup h.1.vals rfl)) (ev_mulc (vals_lookup h.1.vals rfl)), at_add])
      (val := fun _ => BitVec.ofNat 64 J) (fun u h => ev_var (vals_lookup h.1.vals rfl)) (G := (· = M1))
      fun m hm => by subst hm; rfl) ?_
    refine frag_conseq (runF_storeA o (atOffW_lower 14) rfl (y := ArticleProg.w 14) (artDom_w hD (by decide))
      (fun u h => atA_eval (vals_lookup h.1.vals rfl)) (val := fun _ => BitVec.ofNat 64 (K.length + 1))
      (fun u h => ev_inc (vals_lookup h.1.vals rfl)) (G := (· = M2)) fun m hm => by subst hm; rfl) (fun _ h => h)
      fun u h => ⟨M2, hdrop u _ _ h, fun y hy' => ?_, ?_⟩
    · have h1 : y ≠ at_ A ArticleProg.xKnownN := fun e => hy' (.inr ⟨_, .inl rfl, e⟩)
      have h2 : y ≠ at_ A (ArticleProg.xKnown + K.length * 8) := fun e =>
        hy' (.inr ⟨_, .inr (.inr (.inr (.inr hy))), e⟩)
      show upd M1 _ _ y = M y
      rw [upd_ne _ h1]
      exact upd_ne _ h2
    · have hka : kAdd K x = K ++ [x] := by simp only [kAdd, hk, Bool.false_eq_true, if_false]
      rw [hka]
      have hne : ∀ i, i < 64 → at_ A (ArticleProg.xKnown + i * 8) ≠ at_ A ArticleProg.xKnownN := fun i hi =>
        DN.News.ScanRun.at_ne (by simp only [ArticleProg.xKnown, ArticleProg.w, X_val]; omega)
          (w_lt64 (i := 14) (by decide)) (by simp only [ArticleProg.xKnown, ArticleProg.xKnownN, ArticleProg.w]; omega)
      refine ⟨by simp only [M2, upd_eq, List.length_append, List.length_singleton], fun i hi => ?_⟩
      simp only [List.length_append, List.length_singleton] at hi
      show upd M1 _ _ _ = _
      rw [upd_ne _ (hne i (by omega))]
      by_cases hiK : i < K.length
      · have hne2 : at_ A (ArticleProg.xKnown + i * 8) ≠ at_ A (ArticleProg.xKnown + K.length * 8) :=
          DN.News.ScanRun.at_ne (by simp only [ArticleProg.xKnown, ArticleProg.w, X_val]; omega)
            (by simp only [ArticleProg.xKnown, ArticleProg.w, X_val]; omega) (by omega)
        show upd M _ _ _ = _
        rw [upd_ne _ hne2, hK.2 i hiK, getElem!_pos (K ++ [x]) i (by simp; omega), List.getElem_append_left hiK,
          ← getElem!_pos K i hiK]
      · have hiK' : i = K.length := by omega
        subst hiK'
        show upd M _ _ _ = _
        rw [upd_eq, getElem!_pos (K ++ [x]) K.length (by simp), List.getElem_append_right (Nat.le_refl _)]
        simp [J]
  · -- kept before: nothing changes
    refine DN.News.ArticleScan.frag_ifF o rfl (lowK_any _ (k := .skip) rfl) lowKK_nil rfl rfl hQc
      (fun u h => (FramerCode.eval_and (FramerCode.eval_eq (by decide) (by decide) (ev_var (vals_lookup h.1.vals rfl))
        rfl) (FramerCode.eval_lt (by omega) (by decide) (ev_var (vals_lookup h.1.vals rfl)) rfl)).trans rfl)
      (frag_nil o fun u h => ⟨M, hdrop u _ _ h, fun _ _ => rfl, by simp only [kAdd, hk, if_true]; exact hK⟩)

theorem kAdd_nodup {K : List Bytes} (hKn : K.Nodup) (x : Bytes) : (kAdd K x).Nodup := by
  unfold kAdd
  cases hk : K.contains x
  · exact List.nodup_append.2 ⟨hKn, List.nodup_cons.2 ⟨List.not_mem_nil, List.nodup_nil⟩, fun a ha b hb e => by
      simp only [List.mem_singleton] at hb; subst hb; subst e
      exact absurd (List.contains_iff_mem.2 ha) (by rw [hk]; decide)⟩
  · exact hKn

theorem Kf_in {gs F : List Bytes} {x : Bytes} (hx : x ∈ gs) : Kf gs (F ++ [x]) = kAdd (Kf gs F) x := by
  rw [Kf_snoc, List.contains_iff_mem.2 hx, Bool.true_and]
  unfold kAdd
  cases (Kf gs F).contains x <;> rfl

theorem Kf_out {gs F : List Bytes} {x : Bytes} (hx : x ∉ gs) : Kf gs (F ++ [x]) = Kf gs F := by
  rw [Kf_snoc, show gs.contains x = false from Bool.eq_false_iff.2 fun h => hx (List.contains_iff_mem.1 h),
    Bool.false_and]; rfl

/-- What `artGroups` keeps of the groups `F` read so far: the places of those the server carries, each once.
Every other word stays as in `m0`. -/
def GMem (A : Word) (gs : List Bytes) (m0 : Word → Word) (F : List Bytes) (m : Word → Word) : Prop :=
  (∀ y, ¬gScratch A y → m y = m0 y) ∧ KnownAt A gs (Kf gs F) m ∧ (Kf gs F).Nodup

/-- The groups read with element `x`: an empty element names none. -/
def fAdd (F : List Bytes) (x : Bytes) : List Bytes := if x.isEmpty then F else F ++ [x]

/-- `artGroups` with a name read. -/
def countS : List Syntax.PStmt :=
  [inc "cnt", ifs (wd ArticleProg.xElemRes) [.assign "rs" (n 1)],
   ifs (eLe (v "ln") (n 64)) (guardS (.call "j" "artKnown" [v "ln"]) ++ [ifs (eLe (n 0) (v "j")) addS])]

theorem neg_le_eval {u : PancakeState σ} {b : PancakeExp} (hb : eval u b = some (BitVec.ofNat 64 (2 ^ 64 - 1))) :
    eval u (FramerCode.leE (.const (BitVec.ofNat 64 0)) b) = some (bw false) := by
  simp only [FramerCode.leE, eval, hb]; decide

/-- **One element of Newsgroups' body**: counted, checked, and its place kept if the server carries it. -/
theorem gstep (o : Oracle σ) {R : Ret} {A : Word} {s1 : PancakeState σ} (hA : Area ArticleProg.ofs A s1)
    (hD : ArtDom A s1.memaddrs) (hcode : ArtCode s1.code) {gs : List Bytes}
    (hG : GroupsAt A s1.memaddrs s1.be gs s1.memory) (hb : s1.memory (at_ A aBroken) = 0) {F : List Bytes}
    {x : Bytes} {m m' : Word → Word} (hmem : GMem A gs s1.memory F m) (hout : ElemOut A s1.memaddrs s1.be m x m')
    {S E p nq : Nat} :
    FragR o R [.dec "ln" (wd ArticleProg.xElemLen), ifs (eLt (n 0) (v "ln")) countS]
      (RunF s1 (("q", BitVec.ofNat 64 nq) :: grpL S E A p F.length (F.any reserved) (F.any (gs.contains ·)))
        (· = m'))
      (fun u => ∃ m'', RunF s1 (("ln", BitVec.ofNat 64 (min 65 x.length)) :: ("q", BitVec.ofNat 64 nq) ::
        grpL S E A p (fAdd F x).length ((fAdd F x).any reserved) ((fAdd F x).any (gs.contains ·))) (· = m'') u ∧
        GMem A gs s1.memory (fAdd F x) m'') := by
  have hA8 := hA.hA
  have hgl := hG.1
  obtain ⟨hfr, hK, hKn⟩ := hmem
  have hKs : ∀ g ∈ Kf gs F, g ∈ gs := fun g hg => Kf_mem hg
  have hKl : (Kf gs F).length ≤ 64 := Nat.le_trans (nodup_len hKn hKs) hgl
  have hfr' : ∀ y, ¬gScratch A y → m' y = s1.memory y := fun y hy =>
    (hout.1 y fun h => hy (.inl h)).trans (hfr y hy)
  have hK' : KnownAt A gs (Kf gs F) m' := knownAt_frame hK hKl hout.1
  have hG' : GroupsAt A s1.memaddrs s1.be gs m' := groupsAt_frame hA8 hfr' hG
  have hb' : m' (at_ A aBroken) = 0 := (hfr' _ (not_gscr (.inl (by
    have := broken_low; have := sets_le_X; simp only [ArticleProg.xKnownN, ArticleProg.w]; omega)))).trans hb
  let lnv := min 65 x.length
  let cont : Bytes → Bool := (gs.contains ·)
  refine fragR_append (xs := [_]) (fragR_of (runF_dec o (wd_lower 21) rfl (v := BitVec.ofNat 64 lnv) fun u h => by
    rw [wordAt_eval hD h rfl (i := 21) (by decide)]; exact congrArg some hout.2.2.1)) ?_
  let Qx : Nat → Bool → Bool → List Bytes → Assn σ := fun c r k F2 u => ∃ m'',
    RunF s1 (("ln", BitVec.ofNat 64 lnv) :: ("q", BitVec.ofNat 64 nq) :: grpL S E A p c r k) (· = m'') u ∧
      GMem A gs s1.memory F2 m''
  have hQc : ∀ c r k F2, Safe.ClockFree (Qx c r k F2) := fun c r k F2 u q ⟨m'', h, hv⟩ =>
    ⟨m'', runF_clock _ _ _ u q h, hv⟩
  refine fragR_if o rfl (lowK_any _ (k := .skip) rfl) lowKK_nil (hQc _ _ _ _) (fun _ _ _ _ hy => by cases hy)
    (fun _ _ _ _ hy => by cases hy) (b := decide (0 < lnv)) (fun u h => FramerCode.eval_lt (by decide) (by omega) rfl
      (ev_var (vals_lookup h.1.vals rfl))) (fun h0 => ?_) fun h0 => ?_
  · have hx0 : x.isEmpty = false := by
      have := of_decide_eq_true h0; cases x
      · simp [lnv] at this
      · rfl
    have hfa : fAdd F x = F ++ [x] := by simp only [fAdd, hx0, Bool.false_eq_true, if_false]
    rw [hfa, List.length_append, List.length_singleton, List.any_append, List.any_append, List.any_cons,
      List.any_cons, List.any_nil, List.any_nil, Bool.or_false, Bool.or_false]
    refine fragR_append (xs := [_]) (fragR_of (set_to o rfl rfl (v := BitVec.ofNat 64 (F.length + 1))
      (fun u h => ev_inc (vals_lookup h.1.vals rfl))
      (l' := ("ln", BitVec.ofNat 64 lnv) :: ("q", BitVec.ofNat 64 nq) ::
        grpL S E A p (F.length + 1) (F.any reserved) (F.any cont)) fun u h => runF_of h (by
        repeat (refine lookups_cons rfl ?_)
        exact lookups_nil))) ?_
    refine fragR_append (xs := [_]) (fragR_of (cond_set o rfl (wd_lower 22) rfl (b := reserved x)
      (L' := ("ln", BitVec.ofNat 64 lnv) :: ("q", BitVec.ofNat 64 nq) ::
        grpL S E A p (F.length + 1) (F.any reserved || reserved x) (F.any cont))
      (fun u h => (wordAt_eval hD h rfl (i := 22) (by decide)).trans ((congrArg some hout.2.2.2).trans
        (congrArg some (bnat_bw _))))
      (vx := BitVec.ofNat 64 1) (fun _ _ => rfl)
      (fun hr u h => runF_of h (by
        rw [hr, Bool.or_true]
        repeat (refine lookups_cons rfl ?_)
        exact lookups_nil))
      fun hr u h => by rw [hr, Bool.or_false]; exact h)) ?_
    have hfrj : ∀ u y w, Qx (F.length + 1) (F.any reserved || reserved x) (F.any cont || cont x) (F ++ [x]) u →
        y ∈ ["j"] → Qx (F.length + 1) (F.any reserved || reserved x) (F.any cont || cont x) (F ++ [x])
          (restore u y w) := fun u y w ⟨m'', h, hv⟩ hy => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hy; subst hy
      exact ⟨m'', runF_restore h rfl w, hv⟩
    have hfrA : ∀ c r k F2 u y w, Qx c r k F2 u → y ∈ ["kc", "x", "dup"] → Qx c r k F2 (restore u y w) :=
      fun c r k F2 u y w ⟨m'', h, hv⟩ hy => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
        rcases hy with rfl | rfl | rfl
        · exact ⟨m'', runF_restore h rfl w, hv⟩
        · exact ⟨m'', runF_restore h rfl w, hv⟩
        · exact ⟨m'', runF_restore h rfl w, hv⟩
    refine fragR_if o rfl (lowK_any _ (k := .skip) rfl) lowKK_nil (hQc _ _ _ _) hfrj (fun _ _ _ _ hy => by cases hy)
      (b := decide (lnv ≤ 64)) (fun u h => FramerCode.eval_le (by omega) (by decide)
        (ev_var (vals_lookup h.1.vals rfl)) rfl) (fun h6 => ?_) fun h6 => ?_
    · have hl64 : x.length ≤ 64 := by have := of_decide_eq_true h6; simp only [lnv] at this; omega
      have hlnv : lnv = x.length := by simp only [lnv]; omega
      refine fragR_append (knownCall_frag o hA hD hcode (rt := "j") (by decide) rfl rfl hG' hl64 hout.2.1 hb'
        (by show some _ = _; rw [hlnv])) ?_
      by_cases hx : x ∈ gs
      · have hc : gs.contains x = true := List.contains_iff_mem.2 hx
        rw [knownW_in hx, hc, Bool.or_true]
        refine fragR_if o rfl (lowK_any _ (k := .skip) rfl) lowKK_nil (hQc _ _ _ _) (hfrA _ _ _ _)
          (fun _ _ _ _ hy => by cases hy) (b := true)
          (fun u h => (FramerCode.eval_le (by decide) (by have := (gIdx_mem hx).2.1; omega) rfl
            (ev_var (vals_lookup h.1.vals rfl))).trans (by rw [decide_eq_true (Nat.zero_le _)]; rfl))
          (fun _ => fragR_of (frag_conseq (add_frag o (S := S) (E := E) (p := p) (cnt := F.length + 1) (ln := lnv)
            (nq := nq)
            (rs := F.any reserved || reserved x) (kn := F.any cont) hD hgl hK' hKn hKs hx)
            (fun _ h => h) fun u ⟨M', h, hfr2, hK2⟩ => ⟨M', runF_mono h (fun q hq => List.mem_cons_of_mem _ hq)
              fun _ e => e, fun y hy => (hfr2 y hy).trans (hfr' y hy), by rw [Kf_in hx]; exact hK2,
              by rw [Kf_in hx]; exact kAdd_nodup hKn x⟩)) fun h => absurd h (by decide)
      · have hc : gs.contains x = false := Bool.eq_false_iff.2 fun h => hx (List.contains_iff_mem.1 h)
        rw [knownW_out hx, hc, Bool.or_false]
        refine fragR_if o rfl (lowK_any _ (k := .skip) rfl) lowKK_nil (hQc _ _ _ _) (hfrA _ _ _ _)
          (fun _ _ _ _ hy => by cases hy) (b := false)
          (fun u h => neg_le_eval (ev_var (vals_lookup h.1.vals rfl))) (fun h => absurd h (by decide))
          fun _ => fragR_of (frag_nil o fun u h => ⟨m', runF_mono h (fun q hq => List.mem_cons_of_mem _ hq)
            fun _ e => e, hfr', by rw [Kf_out hx]; exact hK', by rw [Kf_out hx]; exact hKn⟩)
    · have hx : x ∉ gs := fun hx => by
        obtain ⟨k, hk, e⟩ := List.getElem_of_mem hx
        have := (hG.2.2 k hk).1
        rw [getElem!_pos gs k hk, e] at this
        have := of_decide_eq_false h6; simp only [lnv] at this; omega
      have hc : gs.contains x = false := Bool.eq_false_iff.2 fun h => hx (List.contains_iff_mem.1 h)
      rw [hc, Bool.or_false]
      exact fragR_of (frag_nil o fun u h => ⟨m', h, hfr', by rw [Kf_out hx]; exact hK', by rw [Kf_out hx]; exact hKn⟩)
  · have hx0 : x = [] := by
      have := of_decide_eq_false h0; cases x
      · rfl
      · simp [lnv] at this
    have hfa : fAdd F x = F := by simp only [fAdd, hx0, List.isEmpty_nil, if_true]
    rw [hfa]
    exact fragR_of (frag_nil o fun u h => ⟨m', h, hfr', hK', hKn⟩)

/-- What `artGroups` from `S` to `E` leaves: how many groups Newsgroups' body names, whether one is reserved. Then
whether the server carries one, and the places of those it carries, each once. Other words stay as in `m0`. -/
def GroupsRet (A : Word) (gs : List Bytes) (a : Bytes) (S E : Nat) (m0 : Word → Word) : Ret := fun _ m =>
  (∀ y, ¬gScratch A y → m y = m0 y) ∧
    m (at_ A ArticleProg.xGCount) = BitVec.ofNat 64 (ArticleSpec.listed (seg a S E)).length ∧
    m (at_ A ArticleProg.xGRes) = bw ((ArticleSpec.listed (seg a S E)).any reserved) ∧
    m (at_ A ArticleProg.xGKnown) = bw ((ArticleSpec.listed (seg a S E)).any (gs.contains ·)) ∧
    KnownAt A gs (Kf gs (ArticleSpec.listed (seg a S E))) m

/-- `artGroups`' loop body. -/
def groupsBody : List Syntax.PStmt :=
  guardS (.call "q" "artElem" [v "p", v "e", n 44]) ++
    [.dec "ln" (wd ArticleProg.xElemLen), ifs (eLt (n 0) (v "ln")) countS, .assign "p" (v "q")]

theorem artGroups_body : guardL ArticleProg.artGroups.body =
    [areaAt ArticleProg.ofs, setW ArticleProg.xKnownN (n 0), .dec "cnt" (n 0), .dec "rs" (n 0), .dec "kn" (n 0),
     .dec "p" (v "s"), .while (eLt (v "p") (v "e")) groupsBody, setW ArticleProg.xGCount (v "cnt"),
     setW ArticleProg.xGRes (v "rs"), setW ArticleProg.xGKnown (v "kn"), .ret (n 0)] := rfl

theorem fAdd_filter (F : List Bytes) (x : Bytes) (rest : List Bytes) :
    F ++ (x :: rest).filter (!·.isEmpty) = fAdd F x ++ rest.filter (!·.isEmpty) := by
  unfold fAdd
  cases x <;> simp

/-- **`artGroups` reads Newsgroups' body from `S` to `E`**, if it returns. -/
theorem artGroups_ok (o : Oracle σ) {A : Word} {s1 : PancakeState σ} (hA : Area ArticleProg.ofs A s1)
    (hD : ArtDom A s1.memaddrs) (hcode : ArtCode s1.code) (hb : s1.memory (at_ A aBroken) = 0) {gs : List Bytes}
    (hG : GroupsAt A s1.memaddrs s1.be gs s1.memory) {a : Bytes} (hlen : a.length ≤ artMax)
    (hin : InputAt s1.memory s1.memaddrs s1.be A a) {S E : Nat} (hSE : S ≤ E) (hE : E ≤ a.length)
    (hs : s1.locals "s" = some (BitVec.ofNat 64 S)) (he : s1.locals "e" = some (BitVec.ofNat 64 E)) :
    ∃ body, Lower.lower (gd ArticleProg.artGroups) = some body ∧
      SafeR o (fun s => s = s1) body (GroupsRet A gs a S E s1.memory) fun _ => False := by
  have hM := artMax_eq
  have hA8 := hA.hA
  refine body_of ?_
  show FragR o _ (guardL ArticleProg.artGroups.body) _ _
  rw [artGroups_body]
  obtain ⟨EA, hEA⟩ := atOff_lower ArticleProg.ofs
  refine fragR_conseq (P0 := RunF s1 [("s", BitVec.ofNat 64 S), ("e", BitVec.ofNat 64 E)] (· = s1.memory))
    ?_ (entry_two hs he) fun _ h => h
  refine fragR_append (xs := [_]) (fragR_of (runF_dec o hEA rfl (v := A) fun u h => areaAt_eval hA h.1.base hEA)) ?_
  let m1 := upd s1.memory (at_ A ArticleProg.xKnownN) (BitVec.ofNat 64 0)
  refine fragR_append (xs := [_]) (fragR_of (runF_storeA o (atOffW_lower 14) rfl (y := ArticleProg.w 14)
    (artDom_w hD (by decide)) (fun u h => atA_eval (vals_lookup h.1.vals rfl)) (val := fun _ => BitVec.ofNat 64 0)
    (fun _ _ => rfl) (G := (· = m1)) fun m hm => by subst hm; rfl)) ?_
  refine fragR_append (xs := [_]) (fragR_of (runF_dec o rfl rfl (v := BitVec.ofNat 64 0) fun _ _ => rfl)) ?_
  refine fragR_append (xs := [_]) (fragR_of (runF_dec o rfl rfl (v := BitVec.ofNat 64 0) fun _ _ => rfl)) ?_
  refine fragR_append (xs := [_]) (fragR_of (runF_dec o rfl rfl (v := BitVec.ofNat 64 0) fun _ _ => rfl)) ?_
  refine fragR_append (xs := [_]) (fragR_of (runF_dec o rfl rfl (v := BitVec.ofNat 64 S) fun u h =>
    ev_var (vals_lookup h.1.vals rfl))) ?_
  let ne : Bytes → Bool := (!·.isEmpty)
  let cont : Bytes → Bool := (gs.contains ·)
  let St : Nat × List Bytes × (Word → Word) → Assn σ := fun t =>
    RunF s1 (grpL S E A t.1 t.2.1.length (t.2.1.any reserved) (t.2.1.any cont)) (· = t.2.2)
  let Inv : Nat × List Bytes × (Word → Word) → Prop := fun t => t.1 ≤ E ∧
    (elems a E ArticleSpec.COMMA S).filter ne = t.2.1 ++ (elems a E ArticleSpec.COMMA t.1).filter ne ∧
    GMem A gs s1.memory t.2.1 t.2.2
  let I : Assn σ := fun u => ∃ t, St t u ∧ Inv t
  have hIc : Safe.ClockFree I := fun u k ⟨t, h, hv⟩ => ⟨t, runF_clock _ _ _ u k h, hv⟩
  have hcond : ∀ u t, St t u → t.1 ≤ E →
      eval u (.cmp .less (.var "p") (.var "e")) = some (bw (decide (t.1 < E))) := fun u t h hq =>
    FramerCode.eval_lt (by omega) (by omega) (ev_var (vals_lookup h.1.vals rfl)) (ev_var (vals_lookup h.1.vals rfl))
  have hlow : LowKK groupsBody := lowK_any _ (k := .skip) rfl
  have hm1 : GMem A gs s1.memory [] m1 := ⟨fun y hy => upd_ne _ fun e => hy (.inr ⟨_, .inl rfl, e⟩),
    ⟨upd_eq _ _ _, fun _ hi => absurd hi (Nat.not_lt_zero _)⟩, List.nodup_nil⟩
  refine fragR_append (xs := [_]) (fragR_conseq (fragR_while o rfl hlow hIc
    (fun u z w ⟨t, h, hv⟩ hz => by
      change z ∈ ["q", "ln"] at hz
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
      rcases hz with rfl | rfl
      · exact ⟨t, runF_restore h rfl w, hv⟩
      · exact ⟨t, runF_restore h rfl w, hv⟩) (fun u ⟨t, h, hv⟩ => ⟨_, hcond u t h hv.1⟩) ?_)
    (fun u h => ⟨(S, [], m1), h, hSE, rfl, hm1⟩) fun _ h => h) ?_
  · refine fragR_conseq (P0 := fun u => ∃ t, (fun t u => St t u ∧ Inv t ∧ t.1 < E) t u) (fragR_exists hlow fun t => ?_)
      (fun u ⟨⟨t, h, hv⟩, h0⟩ => ⟨t, h, hv, by
        rw [hcond u t h hv.1] at h0; exact of_decide_eq_true (bw_ne0 h0)⟩) fun _ h => h
    refine fragR_pure (Inv t ∧ t.1 < E) (fun u h => h.2) hlow fun ⟨hq, hp⟩ => ?_
    obtain ⟨p, F, m⟩ := t
    obtain ⟨hpE, hF, hmem⟩ := hq
    simp only at hpE hF hmem hp
    have hinm : InputAt m s1.memaddrs s1.be A a := input_keep hA8 hlen hin fun _ hx => hmem.1 _ (not_gscr (.inl (by
      have := sets_le_X; simp only [ArticleProg.xKnownN, ArticleProg.w]; omega)))
    have hbm : m (at_ A aBroken) = 0 := (hmem.1 _ (not_gscr (.inl (by
      have := broken_low; have := sets_le_X; simp only [ArticleProg.xKnownN, ArticleProg.w]; omega)))).trans hb
    refine fragR_append (fragR_conseq (elemCall_frag o hA hD hcode hlen (rt := "q") (by decide)
      (l := grpL S E A p F.length (F.any reserved) (F.any cont)) rfl rfl hinm hbm (x := "p") (y := "e")
      (sep := ArticleSpec.COMMA) (Nat.le_of_lt hp) hE rfl rfl) (fun u h => h.1) fun _ h => h) ?_
    have hlow2 : LowKK [.dec "ln" (wd ArticleProg.xElemLen), ifs (eLt (n 0) (v "ln")) countS,
        .assign "p" (v "q")] := lowK_any _ (k := .skip) rfl
    refine fragR_exists hlow2 fun m' => ?_
    let x := elem a p E ArticleSpec.COMMA
    let nq := elemNext a p E ArticleSpec.COMMA
    refine fragR_pure (ElemOut A s1.memaddrs s1.be m x m') (fun u h => h.2) hlow2 fun hout => ?_
    refine fragR_append (xs := [_, _]) (fragR_conseq (gstep o (S := S) (E := E) (p := p) (nq := nq) hA hD hcode hG hb
      hmem hout) (fun u h => h.1) fun _ h => h) ?_
    refine fragR_exists (lowK_any _ (k := .skip) rfl) fun m'' => ?_
    refine fragR_pure (GMem A gs s1.memory (fAdd F x) m'') (fun u h => h.2) (lowK_any _ (k := .skip) rfl)
      fun hmem2 => ?_
    refine fragR_of (frag_conseq (set_to o rfl rfl (v := BitVec.ofNat 64 nq)
      (fun u h => ev_var (vals_lookup h.1.vals rfl))
      (l' := grpL S E A nq (fAdd F x).length ((fAdd F x).any reserved) ((fAdd F x).any cont)) fun u h => runF_of h (by
        repeat (refine lookups_cons rfl ?_)
        exact lookups_nil)) (fun u h => h.1) fun u h => ⟨(nq, fAdd F x, m''), h, elemNext_le, ?_, hmem2⟩)
    show _ = _
    rw [hF, elems_eq a E ArticleSpec.COMMA p, if_pos hp, fAdd_filter]
  have hlowE : LowKK [setW ArticleProg.xGCount (v "cnt"), setW ArticleProg.xGRes (v "rs"),
      setW ArticleProg.xGKnown (v "kn"), .ret (n 0)] := lowK_any _ (k := .skip) rfl
  refine fragR_conseq (P0 := fun u => ∃ t, (fun t u => St t u ∧ Inv t ∧ E ≤ t.1) t u) (fragR_exists hlowE fun t => ?_)
    (fun u ⟨⟨t, h, hv⟩, h0⟩ => ⟨t, h, hv, by
      rw [hcond u t h hv.1] at h0; have := of_decide_eq_false (bw_eq0 h0); omega⟩) fun _ h => h
  refine fragR_pure (Inv t ∧ E ≤ t.1) (fun u h => h.2) hlowE fun ⟨hq, hge⟩ => ?_
  obtain ⟨p, F, m⟩ := t
  obtain ⟨hpE, hF, hmem⟩ := hq
  simp only at hpE hF hmem hge
  have hpe : p = E := by omega
  have hFl : ArticleSpec.listed (seg a S E) = F := by
    rw [listed_elems hSE hE]
    refine hF.trans ?_
    rw [hpe, elems_eq, if_neg (Nat.lt_irrefl _), List.filter_nil, List.append_nil]
  refine fragR_conseq (P0 := St (p, F, m)) ?_ (fun u h => h.1) fun _ h => h
  obtain ⟨hfr, hK, hKn⟩ := hmem
  let m2 := upd m (at_ A ArticleProg.xGCount) (BitVec.ofNat 64 F.length)
  let m3 := upd m2 (at_ A ArticleProg.xGRes) (BitVec.ofNat 64 (bnat (F.any reserved)))
  let m4 := upd m3 (at_ A ArticleProg.xGKnown) (BitVec.ofNat 64 (bnat (F.any cont)))
  refine fragR_append (xs := [_]) (fragR_of (runF_storeA o (atOffW_lower 26) rfl (y := ArticleProg.w 26)
    (artDom_w hD (by decide)) (fun u h => atA_eval (vals_lookup h.1.vals rfl))
    (val := fun _ => BitVec.ofNat 64 F.length)
    (fun u h => ev_var (vals_lookup h.1.vals rfl)) (G := (· = m2)) fun m hm => by subst hm; rfl)) ?_
  refine fragR_append (xs := [_]) (fragR_of (runF_storeA o (atOffW_lower 27) rfl (y := ArticleProg.w 27)
    (artDom_w hD (by decide)) (fun u h => atA_eval (vals_lookup h.1.vals rfl))
    (val := fun _ => BitVec.ofNat 64 (bnat (F.any reserved))) (fun u h => ev_var (vals_lookup h.1.vals rfl))
    (G := (· = m3)) fun m hm => by subst hm; rfl)) ?_
  refine fragR_append (xs := [_]) (fragR_of (runF_storeA o (atOffW_lower 28) rfl (y := ArticleProg.w 28)
    (artDom_w hD (by decide)) (fun u h => atA_eval (vals_lookup h.1.vals rfl))
    (val := fun _ => BitVec.ofNat 64 (bnat (F.any cont))) (fun u h => ev_var (vals_lookup h.1.vals rfl))
    (G := (· = m4)) fun m hm => by subst hm; rfl)) ?_
  have hw : ∀ i j, i < 32 → j < 32 → i ≠ j → at_ A (ArticleProg.w i) ≠ at_ A (ArticleProg.w j) :=
    fun i j hi hj hij => DN.News.ScanRun.at_ne (w_lt64 hi) (w_lt64 hj) (by simp only [ArticleProg.w]; omega)
  have hkw : ∀ z, z = ArticleProg.xKnownN ∨ ArticleProg.xKnown ≤ z ∧ z < ArticleProg.xGroups → ∀ i, 26 ≤ i → i < 29 →
      at_ A z ≠ at_ A (ArticleProg.w i) := fun z hz i h1 h2 =>
    DN.News.ScanRun.at_ne (by simp only [ArticleProg.xKnownN, ArticleProg.w, X_val, xGroups_eq] at hz; omega)
      (w_lt64 (by omega)) (by
        simp only [ArticleProg.xKnownN, ArticleProg.xKnown, ArticleProg.w, xGroups_eq] at hz ⊢; omega)
  have hKl : (Kf gs F).length < 65 := Nat.lt_succ_of_le (Nat.le_trans (nodup_len hKn fun g hg => Kf_mem hg) hG.1)
  refine fragR_ret o rfl fun u h => ⟨_, rfl, fun y hy => ?_, ?_, ?_, ?_, ?_⟩
  · rw [h.2]
    show upd m3 _ _ y = _
    rw [upd_ne _ fun e => hy (.inr ⟨_, .inr (.inr (.inr (.inl rfl))), e⟩)]
    show upd m2 _ _ y = _
    rw [upd_ne _ fun e => hy (.inr ⟨_, .inr (.inr (.inl rfl)), e⟩)]
    show upd m _ _ y = _
    rw [upd_ne _ fun e => hy (.inr ⟨_, .inr (.inl rfl), e⟩)]
    exact hfr y hy
  · rw [h.2, hFl]
    show upd m3 _ _ _ = _
    refine (upd_ne _ (hw 26 28 (by decide) (by decide) (by decide))).trans ?_
    show upd m2 _ _ _ = _
    refine (upd_ne _ (hw 26 27 (by decide) (by decide) (by decide))).trans ?_
    exact upd_eq _ _ _
  · rw [h.2, hFl]
    show upd m3 _ _ _ = _
    refine (upd_ne _ (hw 27 28 (by decide) (by decide) (by decide))).trans ?_
    exact (upd_eq _ _ _).trans (bnat_bw _)
  · rw [h.2, hFl]
    exact (upd_eq _ _ _).trans (bnat_bw _)
  · rw [h.2, hFl]
    refine ⟨?_, fun i hi => ?_⟩
    · show upd m3 _ _ _ = _
      refine (upd_ne _ (hkw _ (.inl rfl) 28 (by decide) (by decide))).trans ?_
      show upd m2 _ _ _ = _
      refine (upd_ne _ (hkw _ (.inl rfl) 27 (by decide) (by decide))).trans ?_
      show upd m _ _ _ = _
      refine (upd_ne _ (hkw _ (.inl rfl) 26 (by decide) (by decide))).trans ?_
      exact hK.1
    · have hz : ArticleProg.xKnown ≤ ArticleProg.xKnown + i * 8 ∧ ArticleProg.xKnown + i * 8 < ArticleProg.xGroups := by
        simp only [ArticleProg.xKnown, ArticleProg.w, X_val, xGroups_eq]; omega
      show upd m3 _ _ _ = _
      refine (upd_ne _ (hkw _ (.inr hz) 28 (by decide) (by decide))).trans ?_
      show upd m2 _ _ _ = _
      refine (upd_ne _ (hkw _ (.inr hz) 27 (by decide) (by decide))).trans ?_
      show upd m _ _ _ = _
      refine (upd_ne _ (hkw _ (.inr hz) 26 (by decide) (by decide))).trans ?_
      exact hK.2 i hi

/-! ## The premises hold of some arguments -/

theorem ascii_witness : Ascii "all" := by unfold Ascii; decide

theorem bytesAt_witness : BytesAt 0 (fun _ => true) false 0 1 [0] (fun _ => 0) := fun i hi _ => by
  have : i = 0 := by omega
  subst this; decide

/-- A memory holding 1 at the words `ys` of the area at 0, else 0. -/
def onesAt (ys : List Nat) : Word → Word := fun x => if ys.any (x == at_ 0 ·) then 1 else 0

theorem elemOut_witness :
    ElemOut 0 (fun _ => true) false (onesAt [ArticleProg.xElemLen]) [0] (onesAt [ArticleProg.xElemLen]) := by
  refine ⟨fun _ _ => rfl, fun i _ hl => ?_, by decide, by decide⟩
  have : i = 0 := by simpa using hl
  subst this; decide

theorem knownAt_witness : KnownAt 0 [[0]] [[0]] (onesAt [ArticleProg.xKnownN]) := by
  refine ⟨by decide, fun i hi => ?_⟩
  have : i = 0 := by simpa using hi
  subst this; decide

theorem gmem_witness : GMem 0 [[0]] (onesAt [ArticleProg.xKnownN]) [[0]] (onesAt [ArticleProg.xKnownN]) :=
  ⟨fun _ _ => rfl, knownAt_witness, by decide⟩

theorem groupsAt_witness : GroupsAt 0 (fun _ => true) false [[0]] (onesAt [ArticleProg.xGroupsN, gAt 0]) := by
  refine ⟨by decide, by decide, fun j hj => ?_⟩
  have : j = 0 := by simpa using hj
  subst this
  refine ⟨by decide, by decide, fun i _ hl => ?_⟩
  have : i = 0 := by simpa using hl
  subst this; decide

theorem gWrites_witness : gWrites ArticleProg.xKnownN := .inl rfl

end DN.News.ArticleListRun
