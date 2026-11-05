-- SPDX-License-Identifier: AGPL-3.0-or-later
import DN.News.ArticleListRun
import DN.News.DecimalRun
import DN.Compiler.NatToDec

/-!
# DN.News.ArticleOut

The article's output functions as the program holds them: digits, copies, the message identifier, the date. If they
return, they write what `DN.News.ArticleSpec.added` asks.
-/

namespace DN.News.ArticleOut

open DN.Compiler DN.Compiler.Wp DN.Compiler.WpRet DN.Compiler.Frag DN.News.AbnfProg
open DN.News.AbnfSets DN.News.FunRun DN.News.AbnfLeaves DN.News.ArticleRun DN.News.ArticleScan
open DN.News.ArticleDateRun DN.News.ArticleDateOk DN.News.ArticleListRun
open DN.News.ScanRun (at_ at_add vals_lookup without Fresh)
open DN.News.FramerCode (bw ev_var bw_ne0 bw_eq0)
open DN.News.AbnfComment (ev_inc)
open DN.News.ArticleCal (ev_mulc)
open DN.News.ArticleProg (artMax guardL guardS ifs wd setW codes)
open DN.News.ArticleSpec (Bytes)
open DN.Compiler.Decimal (digitByte)
open Syntax (v n eEq eLt eLe eAnd eAdd eSub eMul)

variable {σ : Type}

/-! ## A number's digits, the last first -/

/-- A number's decimal digits, the last first. -/
def revDigits (x : Nat) : Bytes := if x < 10 then [digitByte x] else digitByte (x % 10) :: revDigits (x / 10)
termination_by x
decreasing_by omega

theorem revDigits_eq (x : Nat) : revDigits x = (DN.News.CommandSpec.decimal x).reverse := by
  induction x using Nat.strongRecOn with
  | ind x ih =>
    rw [revDigits, DN.News.DecimalRun.decimal_eq x]
    split
    · rfl
    · rw [ih (x / 10) (by omega), List.reverse_append]; rfl

theorem revDigits_length_le (x : Nat) (hx : x < 2 ^ 64) : (revDigits x).length ≤ 20 := by
  rw [revDigits_eq, List.length_reverse]
  simp only [DN.News.CommandSpec.decimal, DN.News.CommandSpec.ascii, List.length_map, Nat.toString_eq_ofList_toDigits,
    String.toList_ofList]
  exact (Nat.length_toDigits_le_iff (by decide) (by decide)).mpr (by omega)

/-! ## Division by ten -/

theorem ev_shr {u : PancakeState σ} {a : PancakeExp} {X : Word} (ha : eval u a = some X) {k : Nat} (hk : k < 64) :
    eval u (.shiftR a (.const (BitVec.ofNat 64 k))) = some (X >>> k) := by
  have hk' : (BitVec.ofNat 64 k).toNat = k := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  simp only [eval, ha, hk']
  split
  · rename_i h; simp at h; omega
  · rfl

/-- `artNum10`'s quotient by ten, from `y`. -/
def divS : List Syntax.PStmt :=
  [.dec "hi" (.shr (v "y") (n 32)), .dec "lo" (eAnd (v "y") (n 4294967295)),
   .dec "qh" (.shr (eMul (v "hi") (n 3435973837)) (n 35)),
   .dec "rh" (eSub (v "hi") (eMul (v "qh") (n 10))),
   .dec "t" (eAdd (eMul (v "rh") (n 6)) (v "lo")),
   .dec "qt" (.shr (eMul (v "t") (n 3435973837)) (n 35)),
   .dec "q" (eAdd (eAdd (eMul (v "qh") (n 4294967296)) (eMul (v "rh") (n 429496729))) (v "qt"))]

/-- The words `divS` leaves in its locals, the quotient last. -/
def divL (Y : Word) : List (String × Value) :=
  let hi := Y >>> 32
  let lo := Y &&& 4294967295
  let qh := (hi * 3435973837) >>> 35
  let rh := hi - qh * 10
  let t := rh * 6 + lo
  let qt := (t * 3435973837) >>> 35
  [("q", qh * 4294967296 + rh * 429496729 + qt), ("qt", qt), ("t", t), ("rh", rh), ("qh", qh), ("lo", lo),
   ("hi", hi)]

theorem divL_q (Y : Word) : (divL Y).lookup "q" = some (DN.Compiler.Div10.div10w Y) := rfl

/-- **The quotient by ten**: `q` holds `y / 10`. -/
theorem div_frag (o : Oracle σ) {s1 : PancakeState σ} {L : List (String × Value)} {F : (Word → Word) → Prop}
    {Y : Word} (hy : L.lookup "y" = some Y)
    (hfr : ∀ x ∈ ["hi", "lo", "qh", "rh", "t", "qt", "q"], Fresh x L = true) :
    Frag o divS (RunF s1 L F) (RunF s1 (divL Y ++ L) F) := by
  have hf : ∀ x, x ∈ ["hi", "lo", "qh", "rh", "t", "qt", "q"] → Fresh x L = true := hfr
  let HI := Y >>> 32
  let LO := Y &&& 4294967295
  let QH := (HI * 3435973837) >>> 35
  let RH := HI - QH * 10
  let T := RH * 6 + LO
  let QT := (T * 3435973837) >>> 35
  let L1 := ("hi", HI) :: L
  let L2 := ("lo", LO) :: L1
  let L3 := ("qh", QH) :: L2
  let L4 := ("rh", RH) :: L3
  let L5 := ("t", T) :: L4
  let L6 := ("qt", QT) :: L5
  have fc := @DN.News.ScanRun.fresh_cons
  have s1' : Frag o [.dec "hi" (.shr (v "y") (n 32))] (RunF s1 L F) (RunF s1 L1 F) :=
    runF_dec o rfl (hf "hi" (by simp)) fun u h => ev_shr (ev_var (vals_lookup h.1.vals hy)) (by decide)
  have s2 : Frag o [.dec "lo" (eAnd (v "y") (n 4294967295))] (RunF s1 L1 F) (RunF s1 L2 F) :=
    runF_dec o rfl (fc (by decide) (hf "lo" (by simp))) fun u h => ev_and (ev_var (vals_lookup h.1.vals (by
      show (("hi", HI) :: L).lookup "y" = _
      rw [DN.News.ScanRun.lookup_cons_ne (by decide)]; exact hy))) rfl
  have s3 : Frag o [.dec "qh" (.shr (eMul (v "hi") (n 3435973837)) (n 35))] (RunF s1 L2 F) (RunF s1 L3 F) :=
    runF_dec o rfl (fc (by decide) (fc (by decide) (hf "qh" (by simp)))) fun u h =>
      ev_shr (ev_mul (ev_var (vals_lookup h.1.vals rfl)) rfl) (by decide)
  have s4 : Frag o [.dec "rh" (eSub (v "hi") (eMul (v "qh") (n 10)))] (RunF s1 L3 F) (RunF s1 L4 F) :=
    runF_dec o rfl (fc (by decide) (fc (by decide) (fc (by decide) (hf "rh" (by simp))))) fun u h =>
      eval_sub _ (ev_var (vals_lookup h.1.vals rfl)) (ev_mul (ev_var (vals_lookup h.1.vals rfl)) rfl)
  have s5 : Frag o [.dec "t" (eAdd (eMul (v "rh") (n 6)) (v "lo"))] (RunF s1 L4 F) (RunF s1 L5 F) :=
    runF_dec o rfl (fc (by decide) (fc (by decide) (fc (by decide) (fc (by decide) (hf "t" (by simp)))))) fun u h =>
      ev_add (ev_mul (ev_var (vals_lookup h.1.vals rfl)) rfl) (ev_var (vals_lookup h.1.vals rfl))
  have s6 : Frag o [.dec "qt" (.shr (eMul (v "t") (n 3435973837)) (n 35))] (RunF s1 L5 F) (RunF s1 L6 F) :=
    runF_dec o rfl (fc (by decide) (fc (by decide) (fc (by decide) (fc (by decide) (fc (by decide)
      (hf "qt" (by simp))))))) fun u h => ev_shr (ev_mul (ev_var (vals_lookup h.1.vals rfl)) rfl) (by decide)
  have s7 : Frag o [.dec "q" (eAdd (eAdd (eMul (v "qh") (n 4294967296)) (eMul (v "rh") (n 429496729))) (v "qt"))]
      (RunF s1 L6 F) (RunF s1 (divL Y ++ L) F) :=
    runF_dec o rfl (fc (by decide) (fc (by decide) (fc (by decide) (fc (by decide) (fc (by decide)
      (fc (by decide) (hf "q" (by simp)))))))) fun u h =>
      ev_add (ev_add (ev_mul (ev_var (vals_lookup h.1.vals rfl)) rfl) (ev_mul (ev_var (vals_lookup h.1.vals rfl)) rfl))
        (ev_var (vals_lookup h.1.vals rfl))
  exact frag_append (xs := [_]) s1' (frag_append (xs := [_]) s2 (frag_append (xs := [_]) s3
    (frag_append (xs := [_]) s4 (frag_append (xs := [_]) s5 (frag_append (xs := [_]) s6 s7)))))

/-! ## A byte put in the area -/

/-- **A byte put** at `off` plus local `x`, its value `b`'s. -/
theorem putAt_frag (o : Oracle σ) {s1 : PancakeState σ} {L : List (String × Value)} {M : Word → Word} {A : Word}
    (hla : L.lookup "a" = some A) {x : String} {off i : Nat} (hoff0 : (off == 0) = false)
    (hx : L.lookup x = some (BitVec.ofNat 64 i)) {e : Syntax.PExpr} {E : PancakeExp} (he : Lower.lowerExp e = some E)
    {b : BitVec 8} (hb : ∀ u, RunF s1 L (· = M) u → ∃ w, eval u E = some w ∧ w.setWidth 8 = b)
    (hdm : s1.memaddrs (byteAlign (at_ A (off + i))) = true) :
    Frag o [.storeb (eAdd (Syntax.atOff (v "a") off) (v x)) e] (RunF s1 L (· = M))
      (RunF s1 L (· = DN.Compiler.Bytes.putByte M s1.be (at_ A (off + i)) b)) := by
  have hst : Lower.lowerExp (eAdd (Syntax.atOff (v "a") off) (v x)) =
      some (.op .add (.op .add (.var "a") (.const (BitVec.ofNat 64 off))) (.var x)) := by
    rw [atOff_eq hoff0]; rfl
  refine storeb_frag o hst he (runF_clock _ _ _) fun u h => ?_
  obtain ⟨w, hw, hwb⟩ := hb u h
  refine ⟨at_ A (off + i), w, by
    simp only [eval, vals_lookup h.1.vals hla, vals_lookup h.1.vals hx]
    rw [← at_add]; rfl, hw, by rw [h.1.memaddrs]; exact hdm, ⟨h.1.vals, h.1.memaddrs, h.1.base, h.1.code, h.1.be⟩, ?_⟩
  show DN.Compiler.Bytes.putByte u.memory u.be (at_ A (off + i)) _ = _
  rw [h.2, h.1.be, hwb]

/-! ## `artNum10` -/

theorem xDec_eq : ArticleProg.xDec = 506752 := rfl
theorem xOut_eq : ArticleProg.xOut = 506776 := rfl
theorem outMax_eq : ArticleProg.outMax = 69632 := rfl
theorem xOut_dec : ArticleProg.xOut = ArticleProg.xDec + 24 := rfl

/-- The words the output functions write: the digits' and the output's. -/
def OutScr (A : Word) (x : Word) : Prop := ∃ z, ArticleProg.xDec ≤ z ∧ z < ArticleProg.xFirst ∧ x = at_ A z

theorem put_frame {A : Word} (hA8 : A.toNat % 8 = 0) {be : Bool} {M : Word → Word} {y : Nat}
    (h1 : ArticleProg.xDec ≤ y) (h2 : y < ArticleProg.xFirst) (b : BitVec 8) {x : Word} (hx : ¬OutScr A x) :
    DN.Compiler.Bytes.putByte M be (at_ A y) b x = M x := by
  simp only [DN.Compiler.Bytes.putByte, DN.News.ScanRun.align_at hA8]
  rw [if_neg]
  intro e
  exact hx ⟨y / 8 * 8, by rw [xDec_eq] at h1 ⊢; omega, by omega, e⟩

/-- What the output functions keep: every other word, the output so far `OUT`, the digits `done`. -/
def NumMem (A : Word) (dm : Word → Bool) (be : Bool) (m0 : Word → Word) (OUT done : Bytes) (m : Word → Word) :
    Prop :=
  (∀ x, ¬OutScr A x → m x = m0 x) ∧ BytesAt A dm be ArticleProg.xOut ArticleProg.outMax OUT m ∧
    BytesAt A dm be ArticleProg.xDec 24 done m

/-- `artNum10`'s loop over the digits. -/
def num10Body : List Syntax.PStmt :=
  divS ++ [kept "k" 23,
    .storeb (eAdd (Syntax.atOff (v "a") ArticleProg.xDec) (v "k")) (eAdd (n 48) (eSub (v "y") (eMul (v "q") (n 10)))),
    inc "k", .assign "y" (v "q"), ifs (eEq (v "y") (n 0)) [.assign "go" (n 0)]]

/-- `artNum10`'s loop over the output. -/
def revBody : List Syntax.PStmt :=
  [.assign "k" (eSub (v "k") (n 1)), kept "k" 23, kept "o" (ArticleProg.outMax - 1),
   .storeb (eAdd (Syntax.atOff (v "a") ArticleProg.xOut) (v "o"))
     (byte (eAdd (Syntax.atOff (v "a") ArticleProg.xDec) (v "k"))), inc "o"]

theorem artNum10_body : guardL ArticleProg.artNum10.body =
    [areaAt ArticleProg.ofs, .dec "k" (n 0), .dec "y" (v "x"), .dec "go" (n 1), .while (v "go") num10Body,
     .while (eLt (n 0) (v "k")) revBody, .ret (v "o")] := rfl

/-- `artNum10`'s locals in its loops. -/
def numL (A : Word) (O X : Nat) (go : Bool) (y k : Nat) : List (String × Value) :=
  [("go", BitVec.ofNat 64 (bnat go)), ("y", BitVec.ofNat 64 y), ("k", BitVec.ofNat 64 k), ("a", A),
   ("o", BitVec.ofNat 64 O), ("x", BitVec.ofNat 64 X)]

theorem digit_val {y : Nat} (hy : y < 2 ^ 64) :
    (BitVec.ofNat 64 48 +
      (BitVec.ofNat 64 y - DN.Compiler.Div10.div10w (BitVec.ofNat 64 y) * BitVec.ofNat 64 10)).setWidth 8
      = digitByte (y % 10) := by
  rw [BitVec.add_comm]; exact DN.Compiler.NatToDec.digit_byte_eq hy

theorem dec_dm {A : Word} {dm : Word → Bool} (hD : ArtDom A dm) (hA8 : A.toNat % 8 = 0) (i : Nat)
    (hi : i < 24 + ArticleProg.outMax) : dm (byteAlign (at_ A (ArticleProg.xDec + i))) = true := by
  have := sets_le_X; have := X_val
  rw [DN.News.ScanRun.align_at hA8]
  exact hD _ (by rw [xDec_eq]; omega) (by rw [xDec_eq, xFirst_eq]; rw [outMax_eq] at hi; omega) (by omega)

/-- **A digit taken**: the last of `y`'s put after `done`, `y` divided by ten. The loop goes on while it is not 0. -/
theorem digit_frag (o : Oracle σ) {s1 : PancakeState σ} {A : Word} (hD : ArtDom A s1.memaddrs)
    (hA8 : A.toNat % 8 = 0) {m0 : Word → Word} {OUT done : Bytes} {M : Word → Word}
    (hm : NumMem A s1.memaddrs s1.be m0 OUT done M) {O X y : Nat} (hy : y < 2 ^ 64) (hk : done.length < 23) :
    Frag o num10Body (RunF s1 (numL A O X true y done.length) (· = M))
      (fun u => ∃ M', RunF s1 (divL (BitVec.ofNat 64 y) ++ numL A O X (decide (y / 10 ≠ 0)) (y / 10)
        (done.length + 1)) (· = M') u ∧ NumMem A s1.memaddrs s1.be m0 OUT (done ++ [digitByte (y % 10)]) M') := by
  have hdm := dec_dm hD hA8
  have hq : (divL (BitVec.ofNat 64 y)).lookup "q" = some (BitVec.ofNat 64 (y / 10)) := by
    rw [divL_q, DN.Compiler.NatToDec.div10w_ofNat hy]
  refine frag_append (div_frag o (Y := BitVec.ofNat 64 y) rfl fun x hx => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl) ?_
  refine frag_append (xs := [_]) (kept_frag o (by decide) (runF_clock _ _ _)
    fun u h => ⟨done.length, vals_lookup h.1.vals rfl, by omega⟩) ?_
  let d := digitByte (y % 10)
  let M1 := DN.Compiler.Bytes.putByte M s1.be (at_ A (ArticleProg.xDec + done.length)) d
  refine frag_append (xs := [_]) (putAt_frag o rfl (by rw [xDec_eq]; rfl) rfl rfl (b := d) (fun u h => ⟨_,
    ev_add rfl (eval_sub _ (ev_var (vals_lookup h.1.vals rfl)) (ev_mul (ev_var (vals_lookup h.1.vals rfl)) rfl)),
    digit_val hy⟩) (hdm _ (by rw [outMax_eq]; omega))) ?_
  let Y := BitVec.ofNat 64 y
  refine frag_append (xs := [_]) (set_to o rfl rfl (v := BitVec.ofNat 64 (done.length + 1))
    (fun u h => ev_inc (vals_lookup h.1.vals rfl)) (l' := divL Y ++ numL A O X true y (done.length + 1))
    fun u h => runF_of h (by
      repeat (refine lookups_cons rfl ?_)
      exact lookups_nil)) ?_
  refine frag_append (xs := [_]) (set_to o rfl rfl (v := BitVec.ofNat 64 (y / 10))
    (fun u h => (ev_var (vals_lookup h.1.vals rfl)).trans (congrArg some (DN.Compiler.NatToDec.div10w_ofNat hy)))
    (l' := divL Y ++ numL A O X true (y / 10) (done.length + 1)) fun u h => runF_of h (by
      repeat (refine lookups_cons rfl ?_)
      exact lookups_nil)) ?_
  refine frag_conseq (cond_set o rfl rfl rfl (b := decide (y / 10 = 0))
    (L' := divL Y ++ numL A O X (decide (y / 10 ≠ 0)) (y / 10) (done.length + 1))
    (fun u h => FramerCode.eval_eq (by omega) (by decide) (ev_var (vals_lookup h.1.vals rfl)) rfl)
    (vx := BitVec.ofNat 64 0) (fun _ _ => rfl)
    (fun hb u h => runF_of h (by
      rw [show decide (y / 10 ≠ 0) = false by simpa using hb]
      repeat (refine lookups_cons rfl ?_)
      exact lookups_nil))
    fun hb u h => by rw [show decide (y / 10 ≠ 0) = true by simpa using hb]; exact h) (fun _ h => h)
    fun u h => ⟨M1, h, fun x hx => (put_frame hA8 (by omega) (by rw [xDec_eq, xFirst_eq]; omega) _ hx).trans
      (hm.1 x hx), bytesAt_put hm.2.1 (fun i _ _ => DN.News.ScanRun.at_ne (by rw [xOut_eq]; rw [outMax_eq] at *; omega)
        (by rw [xDec_eq]; omega) (by rw [xOut_eq, xDec_eq]; omega)) d,
      bytesAt_snoc hm.2.2 (by omega) (by rw [xDec_eq]; omega) (hdm _ (by rw [outMax_eq]; omega)) d⟩

/-- **A digit copied out**: the `k`-th of `done` put after the output. -/
theorem rev_frag (o : Oracle σ) {s1 : PancakeState σ} {A : Word} (hD : ArtDom A s1.memaddrs)
    (hA8 : A.toNat % 8 = 0) {m0 : Word → Word} {OUT done : Bytes} {M : Word → Word}
    (hm : NumMem A s1.memaddrs s1.be m0 OUT done M) {X k : Nat} (hk0 : 0 < k) (hkd : k ≤ done.length)
    (hd24 : done.length ≤ 24) (hout : OUT.length < ArticleProg.outMax) :
    Frag o revBody (RunF s1 (numL A OUT.length X false 0 k) (· = M))
      (fun u => ∃ M', RunF s1 (numL A (OUT.length + 1) X false 0 (k - 1)) (· = M') u ∧
        NumMem A s1.memaddrs s1.be m0 (OUT ++ [done[k - 1]!]) done M') := by
  have hdm := dec_dm hD hA8
  have hO := outMax_eq
  refine frag_append (xs := [_]) (set_to o rfl rfl (v := BitVec.ofNat 64 (k - 1))
    (fun u h => ev_sub (y := 1) ((ev_var (vals_lookup h.1.vals rfl)).trans (by rw [Nat.add_sub_cancel' hk0])) rfl)
    (l' := numL A OUT.length X false 0 (k - 1)) fun u h => runF_of h (by
      repeat (refine lookups_cons rfl ?_)
      exact lookups_nil)) ?_
  refine frag_append (xs := [_]) (kept_frag o (by decide) (runF_clock _ _ _)
    fun u h => ⟨k - 1, vals_lookup h.1.vals rfl, by omega⟩) ?_
  refine frag_append (xs := [_]) (kept_frag o (by decide) (runF_clock _ _ _)
    fun u h => ⟨OUT.length, vals_lookup h.1.vals rfl, by omega⟩) ?_
  let b := done[k - 1]!
  let M1 := DN.Compiler.Bytes.putByte M s1.be (at_ A (ArticleProg.xOut + OUT.length)) b
  have hxo := xOut_dec
  refine frag_append (xs := [_]) (putAt_frag o rfl (by rw [xOut_eq]; rfl) rfl rfl (b := b) (fun u h => ⟨_,
    loadByte_eval (by
      rw [ev_add (atA_eval (vals_lookup h.1.vals rfl)) (ev_var (vals_lookup h.1.vals rfl)), at_add])
      (bytesAt_run h hm.2.2 (by omega) (by omega)), DN.News.ArticleRun.setWidth_byte _⟩)
    (by rw [hxo, Nat.add_assoc]; exact hdm _ (by omega))) ?_
  refine frag_conseq (set_to o rfl rfl (v := BitVec.ofNat 64 (OUT.length + 1))
    (fun u h => ev_inc (vals_lookup h.1.vals rfl)) (l' := numL A (OUT.length + 1) X false 0 (k - 1))
    fun u h => runF_of h (by
      repeat (refine lookups_cons rfl ?_)
      exact lookups_nil)) (fun _ h => h)
    fun u h => ⟨M1, h, fun x hx =>
      (put_frame hA8 (by rw [hxo]; omega) (by rw [hxo, xDec_eq, xFirst_eq]; omega) _ hx).trans (hm.1 x hx),
      bytesAt_snoc hm.2.1 hout (by rw [xOut_eq]; omega) (by rw [hxo, Nat.add_assoc]; exact hdm _ (by omega)) b,
      bytesAt_put hm.2.2 (fun i hi _ => DN.News.ScanRun.at_ne (by rw [xDec_eq]; omega) (by rw [xOut_eq]; omega)
        (by rw [hxo]; omega)) b⟩

/-- What `artNum10` gives back: the output's place past `X`'s digits, written after `OUT`. Words outside the
digits' and the output's stay as in `m0`. -/
def Num10Ret (A : Word) (dm : Word → Bool) (be : Bool) (OUT : Bytes) (X : Nat) (m0 : Word → Word) : Ret :=
  fun w m => w = BitVec.ofNat 64 (OUT.length + (ArticleSpec.decimal X).length) ∧
    (∀ x, ¬OutScr A x → m x = m0 x) ∧
    BytesAt A dm be ArticleProg.xOut ArticleProg.outMax (OUT ++ ArticleSpec.decimal X) m

theorem revDigits_ne (y : Nat) : revDigits y ≠ [] := by
  rw [revDigits]; split <;> simp

theorem revDigits_step (y : Nat) : revDigits y =
    digitByte (y % 10) :: (if y / 10 ≠ 0 then revDigits (y / 10) else []) := by
  rw [revDigits]
  split
  · rw [Nat.mod_eq_of_lt (by omega), if_neg (by omega)]
  · rw [if_pos (by omega)]

/-- **`artNum10` writes `X`'s decimal digits** after the output, if it returns. -/
theorem artNum10_ok (o : Oracle σ) {A : Word} {s1 : PancakeState σ} (hA : Area ArticleProg.ofs A s1)
    (hD : ArtDom A s1.memaddrs) {OUT : Bytes} (hO : BytesAt A s1.memaddrs s1.be ArticleProg.xOut ArticleProg.outMax OUT
      s1.memory) {X : Nat} (hX : X < 2 ^ 64)
    (hfit : OUT.length + (ArticleSpec.decimal X).length ≤ ArticleProg.outMax)
    (ho : s1.locals "o" = some (BitVec.ofNat 64 OUT.length)) (hx : s1.locals "x" = some (BitVec.ofNat 64 X)) :
    ∃ body, Lower.lower (gd ArticleProg.artNum10) = some body ∧
      SafeR o (fun s => s = s1) body (Num10Ret A s1.memaddrs s1.be OUT X s1.memory) fun _ => False := by
  have hA8 := hA.hA
  have hlen := revDigits_length_le X hX
  have hrd := revDigits_eq X
  have hfit' : OUT.length + (DN.News.CommandSpec.decimal X).length ≤ ArticleProg.outMax := hfit
  refine body_of ?_
  show FragR o _ (guardL ArticleProg.artNum10.body) _ _
  rw [artNum10_body]
  obtain ⟨EA, hEA⟩ := atOff_lower ArticleProg.ofs
  refine fragR_conseq (P0 := RunF s1 [("o", BitVec.ofNat 64 OUT.length), ("x", BitVec.ofNat 64 X)] (· = s1.memory))
    ?_ (entry_two ho hx) fun _ h => h
  refine fragR_append (xs := [_]) (fragR_of (runF_dec o hEA rfl (v := A) fun u h => areaAt_eval hA h.1.base hEA)) ?_
  refine fragR_append (xs := [_]) (fragR_of (runF_dec o rfl rfl (v := BitVec.ofNat 64 0) fun _ _ => rfl)) ?_
  refine fragR_append (xs := [_]) (fragR_of (runF_dec o rfl rfl (v := BitVec.ofNat 64 X) fun u h =>
    ev_var (vals_lookup h.1.vals rfl))) ?_
  refine fragR_append (xs := [_]) (fragR_of (runF_dec o rfl rfl (v := BitVec.ofNat 64 1) fun _ _ => rfl)) ?_
  -- the digits, the last first
  let I : Assn σ := fun u => ∃ t : Bool × Nat × Bytes × (Word → Word),
    RunF s1 (numL A OUT.length X t.1 t.2.1 t.2.2.1.length) (· = t.2.2.2) u ∧
    NumMem A s1.memaddrs s1.be s1.memory OUT t.2.2.1 t.2.2.2 ∧
    t.2.2.1 ++ (if t.1 then revDigits t.2.1 else []) = revDigits X ∧ t.2.1 < 2 ^ 64 ∧ (t.1 = false → t.2.1 = 0)
  have hIc : Safe.ClockFree I := fun u k ⟨t, h, hv⟩ => ⟨t, runF_clock _ _ _ u k h, hv⟩
  have hlow : LowKK num10Body := lowK_any _ (k := .skip) rfl
  refine fragR_append (xs := [_]) (fragR_of (frag_conseq (frag_while o rfl hlow hIc
    (fun u z w ⟨t, h, hv⟩ hz => ⟨t, runF_restore h (by
      change z ∈ ["hi", "lo", "qh", "rh", "t", "qt", "q"] at hz
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
      rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl) w, hv⟩)
    (fun u ⟨t, h, _⟩ => ⟨_, ev_var (vals_lookup h.1.vals rfl)⟩) ?_)
    (fun u h => ⟨(true, X, [], s1.memory), h, ⟨fun _ _ => rfl, hO, fun _ _ hl => absurd hl (Nat.not_lt_zero _)⟩,
      by simp, hX, fun e => by cases e⟩) fun _ h => h)) ?_
  · refine frag_conseq (P0 := fun u => ∃ t : Bool × Nat × Bytes × (Word → Word), (fun t u =>
      RunF s1 (numL A OUT.length X true t.2.1 t.2.2.1.length) (· = t.2.2.2) u ∧
      NumMem A s1.memaddrs s1.be s1.memory OUT t.2.2.1 t.2.2.2 ∧ t.2.2.1 ++ revDigits t.2.1 = revDigits X ∧
      t.2.1 < 2 ^ 64) t u) (frag_exists hlow fun t => ?_) (fun u ⟨⟨t, h, hm, hr, hy, hz⟩, h0⟩ => ⟨t, ?_⟩) fun _ h => h
    · refine frag_pure (NumMem A s1.memaddrs s1.be s1.memory OUT t.2.2.1 t.2.2.2 ∧
        t.2.2.1 ++ revDigits t.2.1 = revDigits X ∧ t.2.1 < 2 ^ 64) (fun u h => h.2) hlow fun ⟨hm, hr, hy⟩ => ?_
      obtain ⟨g, y, done, M⟩ := t
      simp only at hm hr hy ⊢
      have hd : done.length < 20 := by
        have := congrArg List.length hr
        rw [List.length_append] at this
        have := List.length_pos_iff.2 (revDigits_ne y)
        omega
      refine frag_conseq (digit_frag o hD hA8 hm (O := OUT.length) (X := X) hy (by omega)) (fun u h => h.1)
        fun u ⟨M', h, hm'⟩ => ⟨(decide (y / 10 ≠ 0), y / 10, done ++ [digitByte (y % 10)], M'),
          by
            show RunF s1 (numL A OUT.length X _ _ (done ++ [_]).length) _ u
            rw [List.length_append, List.length_singleton]
            exact runF_mono h (fun q hq => List.mem_append_right _ hq) fun _ e => e,
          hm', ?_, show y / 10 < 2 ^ 64 by omega, fun e => by simpa using e⟩
      rw [← hr, revDigits_step y, List.append_assoc]
      by_cases h10 : y / 10 = 0 <;> simp [h10]
    · obtain ⟨g, y, done, M⟩ := t
      have hev : eval u (.var "go") = some (BitVec.ofNat 64 (bnat g)) := ev_var (vals_lookup h.1.vals rfl)
      cases g
      · exact absurd hev h0
      · exact ⟨h, hm, by simpa using hr, hy⟩
  -- the digits copied out, the first first
  let D := revDigits X
  have hDl : D.length = (DN.News.CommandSpec.decimal X).length := by simp only [D, hrd, List.length_reverse]
  have hD20 : D.length ≤ 20 := hlen
  let J : Nat × Bytes × (Word → Word) → Assn σ := fun t u =>
    RunF s1 (numL A t.2.1.length X false 0 t.1) (· = t.2.2) u ∧ NumMem A s1.memaddrs s1.be s1.memory t.2.1 D t.2.2 ∧
      t.1 ≤ D.length ∧ t.2.1 = OUT ++ (D.drop t.1).reverse
  have hJc : Safe.ClockFree (fun u => ∃ t, J t u) := fun u k ⟨t, h, hv⟩ => ⟨t, runF_clock _ _ _ u k h, hv⟩
  have hcond : ∀ u t, J t u → eval u (.cmp .less (.const (BitVec.ofNat 64 0)) (.var "k")) =
      some (bw (decide (0 < t.1))) := fun u t h =>
    FramerCode.eval_lt (by decide) (by have := h.2.2.1; omega) rfl (ev_var (vals_lookup h.1.1.vals rfl))
  have hlow2 : LowKK revBody := lowK_any _ (k := .skip) rfl
  refine fragR_conseq (P0 := fun u => ∃ t, J t u) ?_ (fun u ⟨⟨t, h, hm, hr, hy, hz⟩, h0⟩ => by
    obtain ⟨g, y, done, M⟩ := t
    have hev : eval u (.var "go") = some (BitVec.ofNat 64 (bnat g)) := ev_var (vals_lookup h.1.vals rfl)
    cases g
    · have hy0 : y = 0 := hz rfl
      have hr' : done = revDigits X := by simpa using hr
      subst hy0
      refine ⟨(done.length, OUT, M), h, ?_, ?_, ?_⟩
      · show NumMem A s1.memaddrs s1.be s1.memory OUT (revDigits X) M
        rw [← hr']; exact hm
      · show done.length ≤ (revDigits X).length
        rw [hr']; exact Nat.le_refl _
      · show OUT = OUT ++ ((revDigits X).drop done.length).reverse
        rw [hr', List.drop_length, List.reverse_nil, List.append_nil]
    · rw [hev] at h0; exact absurd (Option.some.inj h0) (by decide)) fun _ h => h
  refine fragR_append (xs := [_]) (fragR_of (frag_conseq (frag_while o rfl hlow2 hJc (noDecl _ rfl)
    (fun u ⟨t, h⟩ => ⟨_, hcond u t h⟩) ?_) (fun _ h => h) fun _ h => h)) ?_
  · refine frag_conseq (P0 := fun u => ∃ t, (fun t u => J t u ∧ 0 < t.1) t u) (frag_exists hlow2 fun t => ?_)
      (fun u ⟨⟨t, h⟩, h0⟩ => ⟨t, h, by rw [hcond u t h] at h0; exact of_decide_eq_true (bw_ne0 h0)⟩) fun _ h => h
    obtain ⟨k, OUT', M⟩ := t
    refine frag_pure (NumMem A s1.memaddrs s1.be s1.memory OUT' D M ∧ k ≤ D.length ∧ OUT' = OUT ++ (D.drop k).reverse ∧
      0 < k) (fun u h => ⟨h.1.2.1, h.1.2.2.1, h.1.2.2.2, h.2⟩) hlow2 fun ⟨hm, hk, he, hk0⟩ => ?_
    have hol : OUT'.length = OUT.length + (D.length - k) := by rw [he]; simp
    refine frag_conseq (rev_frag o hD hA8 hm (X := X) hk0 hk (by omega) (by omega)) (fun u h => h.1.1)
      fun u ⟨M', h, hm'⟩ => ⟨(k - 1, OUT' ++ [D[k - 1]!], M'), by
        show RunF s1 (numL A (OUT' ++ [_]).length X false 0 (k - 1)) _ u
        rw [List.length_append, List.length_singleton]; exact h, hm', by omega, ?_⟩
    show OUT' ++ [D[k - 1]!] = OUT ++ (D.drop (k - 1)).reverse
    rw [he, List.drop_eq_getElem_cons (by omega : k - 1 < D.length), Nat.sub_add_cancel hk0, List.reverse_cons,
      List.append_assoc, getElem!_pos D (k - 1) (by omega)]
  refine fragR_ret o rfl fun u ⟨⟨t, h, hm, hk, he⟩, h0⟩ => ?_
  rw [hcond u t ⟨h, hm, hk, he⟩] at h0
  have hk0 : t.1 = 0 := by have := of_decide_eq_false (bw_eq0 h0); omega
  rw [hk0, List.drop_zero] at he
  have hout : t.2.1 = OUT ++ ArticleSpec.decimal X := by
    rw [he]; show OUT ++ (revDigits X).reverse = _; rw [hrd, List.reverse_reverse]; rfl
  refine ⟨_, ev_var (vals_lookup h.1.vals rfl), by rw [hout, List.length_append], fun x hx => by
    rw [h.2]; exact hm.1 x hx, by rw [h.2, ← hout]; exact hm.2.1⟩

/-! ## `artCopy` -/

theorem first_le_size (es : List String) : ArticleProg.xFirst ≤ ArticleProg.size es := by
  simp only [ArticleProg.size, ArticleProg.xNameBytes, ArticleProg.xNameT, ArticleProg.xRuleT, ArticleProg.xFlags]
  omega

/-- `artCopy`'s loop body. -/
def copyBody (es : List String) : List Syntax.PStmt :=
  [.dec "f" (eAdd (v "src") (v "i")), kept "f" (ArticleProg.size es - 1), kept "o" (ArticleProg.outMax - 1),
   .storeb (eAdd (Syntax.atOff (v "a") ArticleProg.xOut) (v "o")) (byte (eAdd (v "a") (v "f"))), inc "i", inc "o"]

theorem artCopy_body (es : List String) : guardL (ArticleProg.artCopy es .none).body =
    [areaAt ArticleProg.ofs, .dec "i" (n 0), .while (eLt (v "i") (v "len")) (copyBody es), .ret (v "o")] := rfl

/-- `artCopy`'s locals in its loop. -/
def copyL (A : Word) (O S N i : Nat) : List (String × Value) :=
  [("i", BitVec.ofNat 64 i), ("a", A), ("o", BitVec.ofNat 64 O), ("src", BitVec.ofNat 64 S), ("len", BitVec.ofNat 64 N)]

/-- What `artCopy` gives back: the output's place past `SRC`, written after `OUT`. Words outside the digits' and the
output's stay as in `m0`. -/
def CopyRet (A : Word) (dm : Word → Bool) (be : Bool) (OUT SRC : Bytes) (m0 : Word → Word) : Ret := fun w m =>
  w = BitVec.ofNat 64 (OUT.length + SRC.length) ∧ (∀ x, ¬OutScr A x → m x = m0 x) ∧
    BytesAt A dm be ArticleProg.xOut ArticleProg.outMax (OUT ++ SRC) m

/-- A byte read the same in memory changed only in the words `Scr` names, its own word not among them. -/
theorem load_frame {A : Word} {Scr : Word → Prop} {dm : Word → Bool} {be : Bool} {m m0 : Word → Word}
    (hfr : ∀ x, ¬Scr x → m x = m0 x) {y : Nat} (hy : ¬Scr (byteAlign (at_ A y))) :
    memLoadByte m dm be (at_ A y) = memLoadByte m0 dm be (at_ A y) := by
  unfold memLoadByte; rw [hfr _ hy]

theorem below_out {A : Word} (hA8 : A.toNat % 8 = 0) {y : Nat} (hy : y < ArticleProg.xDec) :
    ¬OutScr A (byteAlign (at_ A y)) := fun ⟨z, h1, h2, e⟩ => by
  rw [DN.News.ScanRun.align_at hA8] at e
  have := DN.News.ScanRun.at_inj (by rw [xDec_eq] at hy; omega) (by rw [xFirst_eq] at h2; omega) e
  omega

/-- **`artCopy` copies `SRC`, from `S` below the digits', after the output**, if it returns. -/
theorem artCopy_ok (o : Oracle σ) {es : List String} (hsz : ArticleProg.size es < 2 ^ 40) {A : Word}
    {s1 : PancakeState σ} (hA : Area ArticleProg.ofs A s1) (hD : ArtDom A s1.memaddrs) {OUT SRC : Bytes}
    (hO : BytesAt A s1.memaddrs s1.be ArticleProg.xOut ArticleProg.outMax OUT s1.memory) {S : Nat}
    (hS : BytesAt A s1.memaddrs s1.be S SRC.length SRC s1.memory) (hSd : S + SRC.length ≤ ArticleProg.xDec)
    (hfit : OUT.length + SRC.length ≤ ArticleProg.outMax)
    (ho : s1.locals "o" = some (BitVec.ofNat 64 OUT.length)) (hs : s1.locals "src" = some (BitVec.ofNat 64 S))
    (hl : s1.locals "len" = some (BitVec.ofNat 64 SRC.length)) :
    ∃ body, Lower.lower (gd (ArticleProg.artCopy es .none)) = some body ∧
      SafeR o (fun s => s = s1) body (CopyRet A s1.memaddrs s1.be OUT SRC s1.memory) fun _ => False := by
  have hA8 := hA.hA
  have hOm := outMax_eq
  have hdx := xDec_eq
  have hfs := first_le_size es
  have hxf := xFirst_eq
  have hdm := dec_dm hD hA8
  have hxo := xOut_dec
  refine body_of ?_
  show FragR o _ (guardL (ArticleProg.artCopy es .none).body) _ _
  rw [artCopy_body]
  obtain ⟨EA, hEA⟩ := atOff_lower ArticleProg.ofs
  refine fragR_conseq (P0 := RunF s1 [("o", BitVec.ofNat 64 OUT.length), ("src", BitVec.ofNat 64 S),
    ("len", BitVec.ofNat 64 SRC.length)] (· = s1.memory)) ?_ (entry_run (fun q hq => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl
      · exact ho
      · exact hs
      · exact hl) rfl) fun _ h => h
  refine fragR_append (xs := [_]) (fragR_of (runF_dec o hEA rfl (v := A) fun u h => areaAt_eval hA h.1.base hEA)) ?_
  refine fragR_append (xs := [_]) (fragR_of (runF_dec o rfl rfl (v := BitVec.ofNat 64 0) fun _ _ => rfl)) ?_
  let I : Assn σ := fun u => ∃ t : Nat × (Word → Word),
    RunF s1 (copyL A (OUT.length + t.1) S SRC.length t.1) (· = t.2) u ∧ t.1 ≤ SRC.length ∧
      (∀ x, ¬OutScr A x → t.2 x = s1.memory x) ∧
      BytesAt A s1.memaddrs s1.be ArticleProg.xOut ArticleProg.outMax (OUT ++ SRC.take t.1) t.2
  have hIc : Safe.ClockFree I := fun u k ⟨t, h, hv⟩ => ⟨t, runF_clock _ _ _ u k h, hv⟩
  have hcond : ∀ u (t : Nat × (Word → Word)), RunF s1 (copyL A (OUT.length + t.1) S SRC.length t.1) (· = t.2) u →
      t.1 ≤ SRC.length → eval u (.cmp .less (.var "i") (.var "len")) = some (bw (decide (t.1 < SRC.length))) :=
    fun u t h ht => FramerCode.eval_lt (by omega) (by omega) (ev_var (vals_lookup h.1.vals rfl))
      (ev_var (vals_lookup h.1.vals rfl))
  have hlow : LowKK (copyBody es) := lowK_any _ (k := .skip) rfl
  refine fragR_append (xs := [_]) (fragR_of (frag_conseq (frag_while o rfl hlow hIc
    (fun u z w ⟨t, h, hv⟩ hz => by
      change z ∈ ["f"] at hz
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hz; subst hz
      exact ⟨t, runF_restore h rfl w, hv⟩) (fun u ⟨t, h, hv⟩ => ⟨_, hcond u t h hv.1⟩) ?_)
    (fun u h => ⟨(0, s1.memory), h, Nat.zero_le _, fun _ _ => rfl, by simpa using hO⟩) fun _ h => h)) ?_
  · refine frag_conseq (P0 := fun u => ∃ t : Nat × (Word → Word), (fun t u =>
      RunF s1 (copyL A (OUT.length + t.1) S SRC.length t.1) (· = t.2) u ∧ (t.1 < SRC.length ∧
      (∀ x, ¬OutScr A x → t.2 x = s1.memory x) ∧
      BytesAt A s1.memaddrs s1.be ArticleProg.xOut ArticleProg.outMax (OUT ++ SRC.take t.1) t.2)) t u)
      (frag_exists hlow fun t => ?_) (fun u ⟨⟨t, h, hv⟩, h0⟩ => ⟨t, h, by
        rw [hcond u t h hv.1] at h0; exact of_decide_eq_true (bw_ne0 h0), hv.2⟩) fun _ h => h
    obtain ⟨i, M⟩ := t
    refine frag_pure (i < SRC.length ∧ (∀ x, ¬OutScr A x → M x = s1.memory x) ∧
      BytesAt A s1.memaddrs s1.be ArticleProg.xOut ArticleProg.outMax (OUT ++ SRC.take i) M) (fun u h => h.2)
      hlow fun ⟨hi, hfr, hout⟩ => ?_
    refine frag_conseq (P0 := RunF s1 (copyL A (OUT.length + i) S SRC.length i) (· = M)) ?_ (fun u h => h.1)
      fun _ h => h
    refine frag_append (xs := [_]) (runF_dec o rfl rfl (v := BitVec.ofNat 64 (S + i)) fun u h =>
      (ev_add (ev_var (vals_lookup h.1.vals rfl)) (ev_var (vals_lookup h.1.vals rfl))).trans (by
        rw [← BitVec.ofNat_add])) ?_
    refine frag_append (xs := [_]) (kept_frag o (by omega) (runF_clock _ _ _)
      fun u h => ⟨S + i, vals_lookup h.1.vals rfl, by omega⟩) ?_
    refine frag_append (xs := [_]) (kept_frag o (by decide) (runF_clock _ _ _)
      fun u h => ⟨OUT.length + i, vals_lookup h.1.vals rfl, by
        have := List.length_take_of_le (Nat.le_of_lt hi) (l := SRC); omega⟩) ?_
    let b := SRC[i]!
    have hlen : (OUT ++ SRC.take i).length = OUT.length + i := by
      rw [List.length_append, List.length_take_of_le (Nat.le_of_lt hi)]
    let M1 := DN.Compiler.Bytes.putByte M s1.be (at_ A (ArticleProg.xOut + (OUT.length + i))) b
    refine frag_append (xs := [_]) (putAt_frag o rfl (by rw [xOut_eq]; rfl) rfl rfl (b := b) (fun u h => ⟨_,
      loadByte_eval ((ev_add (ev_var (vals_lookup h.1.vals rfl)) (ev_var (vals_lookup h.1.vals rfl))).trans rfl)
        (by
          show memLoadByte _ _ _ (at_ A (S + i)) = _
          rw [h.2, h.1.memaddrs, h.1.be, load_frame hfr (below_out hA8 (by omega))]; exact hS i (by omega) (by omega)),
      DN.News.ArticleRun.setWidth_byte _⟩)
      (by rw [hxo, Nat.add_assoc]; exact hdm _ (by omega))) ?_
    refine frag_append (xs := [_]) (set_to o rfl rfl (v := BitVec.ofNat 64 (i + 1))
      (fun u h => ev_inc (vals_lookup h.1.vals rfl))
      (l' := ("f", BitVec.ofNat 64 (S + i)) :: copyL A (OUT.length + i) S SRC.length (i + 1)) fun u h => runF_of h (by
        repeat (refine lookups_cons rfl ?_)
        exact lookups_nil)) ?_
    refine frag_conseq (set_to o rfl rfl (v := BitVec.ofNat 64 (OUT.length + (i + 1)))
      (fun u h => ev_inc (vals_lookup h.1.vals rfl))
      (l' := ("f", BitVec.ofNat 64 (S + i)) :: copyL A (OUT.length + (i + 1)) S SRC.length (i + 1))
      fun u h => runF_of h (by
        repeat (refine lookups_cons rfl ?_)
        exact lookups_nil)) (fun _ h => h)
      fun u h => ⟨(i + 1, M1), runF_mono h (fun q hq => List.mem_cons_of_mem _ hq) (fun _ e => e), hi,
        fun x hx => (put_frame hA8 (by omega) (by omega) _ hx).trans (hfr x hx), ?_⟩
    have hsnoc := bytesAt_snoc hout (by omega) (by rw [xOut_eq]; omega)
      (by rw [hlen, hxo, Nat.add_assoc]; exact hdm _ (by omega)) b
    rw [hlen] at hsnoc
    show BytesAt _ _ _ _ _ (OUT ++ SRC.take (i + 1)) M1
    rw [List.take_add_one, List.getElem?_eq_getElem hi, Option.toList_some, ← List.append_assoc,
      ← getElem!_pos SRC i hi]
    exact hsnoc
  refine fragR_ret o rfl fun u ⟨⟨t, h, ht, hfr, hout⟩, h0⟩ => ?_
  rw [hcond u t h ht] at h0
  have hi : t.1 = SRC.length := by have := of_decide_eq_false (bw_eq0 h0); omega
  rw [hi, List.take_length] at hout
  exact ⟨_, ev_var (vals_lookup h.1.vals rfl), by rw [hi], fun x hx => by rw [h.2]; exact hfr x hx,
    by rw [h.2]; exact hout⟩

/-! ## `artToMsg` -/

theorem xMsg_eq : ArticleProg.xMsg = 506416 := rfl

/-- The words `artToMsg` writes: the message identifier's and its length. -/
def MsgScr (A : Word) (x : Word) : Prop :=
  x = at_ A ArticleProg.xMsgLen ∨ ∃ z, ArticleProg.xMsg ≤ z ∧ z < ArticleProg.xMsg + ArticleProg.msgCap ∧ x = at_ A z

/-- `artToMsg`'s loop body. -/
def msgBody (es : List String) : List Syntax.PStmt :=
  [.dec "f" (eAdd (v "src") (v "i")), kept "f" (ArticleProg.size es - 1),
   .storeb (eAdd (Syntax.atOff (v "a") ArticleProg.xMsg) (v "i")) (byte (eAdd (v "a") (v "f"))), inc "i"]

theorem artToMsg_body (es : List String) : guardL (ArticleProg.artToMsg es).body =
    [areaAt ArticleProg.ofs, kept "len" (ArticleProg.msgCap - 1), .dec "i" (n 0),
     .while (eLt (v "i") (v "len")) (msgBody es), setW ArticleProg.xMsgLen (v "len"), .ret (n 0)] := rfl

/-- `artToMsg`'s locals in its loop. -/
def msgL (A : Word) (S N i : Nat) : List (String × Value) :=
  [("i", BitVec.ofNat 64 i), ("a", A), ("src", BitVec.ofNat 64 S), ("len", BitVec.ofNat 64 N)]

/-- What `artToMsg` leaves: `SRC` as the message identifier, its length in `xMsgLen`; every other word as `m0`
holds it. -/
def MsgRet (A : Word) (dm : Word → Bool) (be : Bool) (SRC : Bytes) (m0 : Word → Word) : Ret := fun _ m =>
  (∀ x, ¬MsgScr A x → m x = m0 x) ∧ BytesAt A dm be ArticleProg.xMsg ArticleProg.msgCap SRC m ∧
    m (at_ A ArticleProg.xMsgLen) = BitVec.ofNat 64 SRC.length

theorem msg_word {A : Word} (hA8 : A.toNat % 8 = 0) {y : Nat} (hy : y < 2 ^ 40)
    (h : ¬(ArticleProg.X ≤ y ∧ y < ArticleProg.xMsg + ArticleProg.msgCap)) :
    ¬MsgScr A (byteAlign (at_ A y)) := by
  have hm := xMsg_eq
  rw [DN.News.ScanRun.align_at hA8]
  rintro (e | ⟨z, h1, h2, e⟩)
  · have := DN.News.ScanRun.at_inj (by omega) (w_lt64 (i := 13) (by decide)) e
    simp only [ArticleProg.msgCap, X_val] at h; simp only [ArticleProg.w, X_val] at this; omega
  · have := DN.News.ScanRun.at_inj (by omega) (by simp only [ArticleProg.msgCap] at h2; omega) e
    simp only [ArticleProg.msgCap, X_val] at h h1 h2; omega

/-- **`artToMsg` copies `SRC` as the message identifier**, if it returns. `SRC` lies below the article's words or past
the message identifier's. -/
theorem artToMsg_ok (o : Oracle σ) {es : List String} (hsz : ArticleProg.size es < 2 ^ 40) {A : Word}
    {s1 : PancakeState σ} (hA : Area ArticleProg.ofs A s1) (hD : ArtDom A s1.memaddrs) {SRC : Bytes} {S : Nat}
    (hS : BytesAt A s1.memaddrs s1.be S SRC.length SRC s1.memory) (hSz : S + SRC.length ≤ ArticleProg.size es)
    (hSm : S + SRC.length ≤ ArticleProg.X ∨ ArticleProg.xMsg + ArticleProg.msgCap ≤ S)
    (hSl : SRC.length < ArticleProg.msgCap)
    (hs : s1.locals "src" = some (BitVec.ofNat 64 S)) (hl : s1.locals "len" = some (BitVec.ofNat 64 SRC.length)) :
    ∃ body, Lower.lower (gd (ArticleProg.artToMsg es)) = some body ∧
      SafeR o (fun s => s = s1) body (MsgRet A s1.memaddrs s1.be SRC s1.memory) fun _ => False := by
  have hA8 := hA.hA
  have hm := xMsg_eq
  have hmc : ArticleProg.msgCap = 256 := rfl
  have hX := X_val
  have hsets := sets_le_X
  refine body_of ?_
  show FragR o _ (guardL (ArticleProg.artToMsg es).body) _ _
  rw [artToMsg_body]
  obtain ⟨EA, hEA⟩ := atOff_lower ArticleProg.ofs
  refine fragR_conseq (P0 := RunF s1 [("src", BitVec.ofNat 64 S), ("len", BitVec.ofNat 64 SRC.length)]
    (· = s1.memory)) ?_ (entry_two hs hl) fun _ h => h
  refine fragR_append (xs := [_]) (fragR_of (runF_dec o hEA rfl (v := A) fun u h => areaAt_eval hA h.1.base hEA)) ?_
  refine fragR_append (xs := [_]) (fragR_of (kept_frag o (by decide) (runF_clock _ _ _)
    fun u h => ⟨SRC.length, vals_lookup h.1.vals rfl, by omega⟩)) ?_
  refine fragR_append (xs := [_]) (fragR_of (runF_dec o rfl rfl (v := BitVec.ofNat 64 0) fun _ _ => rfl)) ?_
  let I : Assn σ := fun u => ∃ t : Nat × (Word → Word),
    RunF s1 (msgL A S SRC.length t.1) (· = t.2) u ∧ t.1 ≤ SRC.length ∧ (∀ x, ¬MsgScr A x → t.2 x = s1.memory x) ∧
      BytesAt A s1.memaddrs s1.be ArticleProg.xMsg ArticleProg.msgCap (SRC.take t.1) t.2
  have hIc : Safe.ClockFree I := fun u k ⟨t, h, hv⟩ => ⟨t, runF_clock _ _ _ u k h, hv⟩
  have hcond : ∀ u (t : Nat × (Word → Word)), RunF s1 (msgL A S SRC.length t.1) (· = t.2) u →
      t.1 ≤ SRC.length → eval u (.cmp .less (.var "i") (.var "len")) = some (bw (decide (t.1 < SRC.length))) :=
    fun u t h ht => FramerCode.eval_lt (by omega) (by omega) (ev_var (vals_lookup h.1.vals rfl))
      (ev_var (vals_lookup h.1.vals rfl))
  have hlow : LowKK (msgBody es) := lowK_any _ (k := .skip) rfl
  have hdmM : ∀ i, i < ArticleProg.msgCap → s1.memaddrs (byteAlign (at_ A (ArticleProg.xMsg + i))) = true :=
    fun i hi => by
      rw [DN.News.ScanRun.align_at hA8]
      exact hD _ (by omega) (by rw [xFirst_eq]; omega) (by omega)
  refine fragR_append (xs := [_]) (fragR_of (frag_conseq (frag_while o rfl hlow hIc
    (fun u z w ⟨t, h, hv⟩ hz => by
      change z ∈ ["f"] at hz
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hz; subst hz
      exact ⟨t, runF_restore h rfl w, hv⟩) (fun u ⟨t, h, hv⟩ => ⟨_, hcond u t h hv.1⟩) ?_)
    (fun u h => ⟨(0, s1.memory), h, Nat.zero_le _, fun _ _ => rfl, fun _ _ hl => by simp at hl⟩) fun _ h => h)) ?_
  · refine frag_conseq (P0 := fun u => ∃ t : Nat × (Word → Word), (fun t u =>
      RunF s1 (msgL A S SRC.length t.1) (· = t.2) u ∧ (t.1 < SRC.length ∧ (∀ x, ¬MsgScr A x → t.2 x = s1.memory x) ∧
      BytesAt A s1.memaddrs s1.be ArticleProg.xMsg ArticleProg.msgCap (SRC.take t.1) t.2)) t u)
      (frag_exists hlow fun t => ?_) (fun u ⟨⟨t, h, hv⟩, h0⟩ => ⟨t, h, by
        rw [hcond u t h hv.1] at h0; exact of_decide_eq_true (bw_ne0 h0), hv.2⟩) fun _ h => h
    obtain ⟨i, M⟩ := t
    refine frag_pure (i < SRC.length ∧ (∀ x, ¬MsgScr A x → M x = s1.memory x) ∧
      BytesAt A s1.memaddrs s1.be ArticleProg.xMsg ArticleProg.msgCap (SRC.take i) M) (fun u h => h.2)
      hlow fun ⟨hi, hfr, hmsg⟩ => ?_
    refine frag_conseq (P0 := RunF s1 (msgL A S SRC.length i) (· = M)) ?_ (fun u h => h.1) fun _ h => h
    refine frag_append (xs := [_]) (runF_dec o rfl rfl (v := BitVec.ofNat 64 (S + i)) fun u h =>
      (ev_add (ev_var (vals_lookup h.1.vals rfl)) (ev_var (vals_lookup h.1.vals rfl))).trans (by
        rw [← BitVec.ofNat_add])) ?_
    refine frag_append (xs := [_]) (kept_frag o (by omega) (runF_clock _ _ _)
      fun u h => ⟨S + i, vals_lookup h.1.vals rfl, by omega⟩) ?_
    let b := SRC[i]!
    let M1 := DN.Compiler.Bytes.putByte M s1.be (at_ A (ArticleProg.xMsg + i)) b
    have hsrc : ¬(ArticleProg.X ≤ S + i ∧ S + i < ArticleProg.xMsg + ArticleProg.msgCap) := by omega
    refine frag_append (xs := [_]) (putAt_frag o rfl (by rw [hm]; rfl) rfl rfl (b := b) (fun u h => ⟨_,
      loadByte_eval ((ev_add (ev_var (vals_lookup h.1.vals rfl)) (ev_var (vals_lookup h.1.vals rfl))).trans rfl)
        (by
          show memLoadByte _ _ _ (at_ A (S + i)) = _
          rw [h.2, h.1.memaddrs, h.1.be, load_frame hfr (msg_word hA8 (by omega) hsrc)]
          exact hS i (by omega) (by omega)),
      DN.News.ArticleRun.setWidth_byte _⟩) (hdmM i (by omega))) ?_
    refine frag_conseq (set_to o rfl rfl (v := BitVec.ofNat 64 (i + 1)) (fun u h => ev_inc (vals_lookup h.1.vals rfl))
      (l' := msgL A S SRC.length (i + 1)) fun u h => runF_of h (by
        repeat (refine lookups_cons rfl ?_)
        exact lookups_nil)) (fun _ h => h)
      fun u h => ⟨(i + 1, M1), h, hi, fun x hx => ?_, ?_⟩
    · show DN.Compiler.Bytes.putByte M s1.be (at_ A (ArticleProg.xMsg + i)) b x = _
      simp only [DN.Compiler.Bytes.putByte, DN.News.ScanRun.align_at hA8]
      rw [if_neg fun e => hx (.inr ⟨_, by omega, by omega, e⟩)]
      exact hfr x hx
    · have hsnoc := bytesAt_snoc hmsg (by simp; omega) (by omega)
        (by rw [List.length_take_of_le (Nat.le_of_lt hi)]; exact hdmM i (by omega)) b
      rw [List.length_take_of_le (Nat.le_of_lt hi)] at hsnoc
      show BytesAt _ _ _ _ _ (SRC.take (i + 1)) M1
      rw [List.take_add_one, List.getElem?_eq_getElem hi, Option.toList_some, ← getElem!_pos SRC i hi]
      exact hsnoc
  have hlowE : LowKK [setW ArticleProg.xMsgLen (v "len"), .ret (n 0)] := lowK_any _ (k := .skip) rfl
  refine fragR_conseq (P0 := fun u => ∃ t : Nat × (Word → Word), (fun t u =>
    RunF s1 (msgL A S SRC.length t.1) (· = t.2) u ∧ (t.1 = SRC.length ∧ (∀ x, ¬MsgScr A x → t.2 x = s1.memory x) ∧
    BytesAt A s1.memaddrs s1.be ArticleProg.xMsg ArticleProg.msgCap (SRC.take t.1) t.2)) t u)
    (fragR_exists hlowE fun t => ?_) (fun u ⟨⟨t, h, hv⟩, h0⟩ => ⟨t, h, by
      rw [hcond u t h hv.1] at h0; have := of_decide_eq_false (bw_eq0 h0); have := hv.1; omega, hv.2⟩) fun _ h => h
  obtain ⟨i, M⟩ := t
  refine fragR_pure (i = SRC.length ∧ (∀ x, ¬MsgScr A x → M x = s1.memory x) ∧
    BytesAt A s1.memaddrs s1.be ArticleProg.xMsg ArticleProg.msgCap (SRC.take i) M) (fun u h => h.2) hlowE
    fun ⟨hi, hfr, hmsg⟩ => ?_
  subst hi
  rw [List.take_length] at hmsg
  let M2 := upd M (at_ A ArticleProg.xMsgLen) (BitVec.ofNat 64 SRC.length)
  refine fragR_append (xs := [_]) (fragR_of (frag_conseq (runF_storeA o (atOffW_lower 13) rfl (y := ArticleProg.w 13)
    (l := msgL A S SRC.length SRC.length) (F := (· = M))
    (artDom_w hD (by decide)) (fun u h => atA_eval (vals_lookup h.1.vals rfl))
    (val := fun _ => BitVec.ofNat 64 SRC.length) (fun u h => ev_var (vals_lookup h.1.vals rfl))
    (G := (· = M2)) fun m hm => by subst hm; rfl) (fun u h => h.1) fun _ h => h)) ?_
  refine fragR_ret o rfl fun u h => ⟨_, rfl, fun x hx => ?_, ?_, ?_⟩
  · rw [h.2]; show upd M _ _ x = _; rw [upd_ne _ fun e => hx (.inl e)]; exact hfr x hx
  · rw [h.2]
    refine bytesAt_frame hmsg fun i hi _ => ?_
    show upd M _ _ _ = _
    refine upd_ne _ fun e => ?_
    rw [DN.News.ScanRun.align_at hA8] at e
    have := DN.News.ScanRun.at_inj (by omega) (w_lt64 (i := 13) (by decide)) e
    simp only [ArticleProg.w] at this; omega
  · rw [h.2]; exact upd_eq _ _ _

/-! ## Calls -/

theorem mem_artCivilOf : gd ArticleProg.artCivilOf ∈
    ArticleProg.functions ArticleSpec.spec (ArticleProg.entries ArticleSpec.spec) .none :=
  List.mem_append_right _ (List.mem_map.2 ⟨ArticleProg.artCivilOf, by simp, rfl⟩)

/-- **A call of `artCivilOf`**, the check after it passed: the day of the calendar in one word, the memory kept. -/
theorem civilOfCall_frag (o : Oracle σ) {R : Ret} {A : Word} {s0 : PancakeState σ} (hA : Area ArticleProg.ofs A s0)
    (hcode : ArtCode s0.code) {rt : String} (hra : rt ≠ "a") {l : List (String × Value)}
    (hla : l.lookup "a" = some A) (hrt : Fresh rt l = true) {m0 : Word → Word} (hP : Pows m0 A)
    (hb : m0 (at_ A aBroken) = 0) {x : String} {z : Nat} (hz : z < 2 ^ 30)
    (hx : l.lookup x = some (BitVec.ofNat 64 z)) :
    FragR o R (guardS (.call rt "artCivilOf" [v x])) (RunF s0 l (· = m0))
      (RunF s0 ((rt, BitVec.ofNat 64 (DN.News.Calendar.civilWord z)) :: l) (· = m0)) := by
  refine fragR_conseq (gcall_frag o hA hcode hra (f := ArticleProg.artCivilOf) mem_artCivilOf (by decide)
    (args := [.var x]) rfl hla (vs := [BitVec.ofNat 64 z]) rfl
    (fun u h => by simp only [evalArgs, ev_var (vals_lookup h.1.vals hx)])
    (Rf := fun m0 v m => v = BitVec.ofNat 64 (DN.News.Calendar.civilWord z) ∧ m = m0)
    (fun s1 hA1 _ _ _ hloc hF => DN.News.ArticleCal.artCivilOf_ok o hA1 (by rw [‹s1.code = s0.code›]; exact hcode)
      (by rw [hF]; exact hP) (by rw [hF]; exact hb) hz ((hloc "days").trans rfl)) hrt
    (G := fun v m => m = m0 ∧ v = BitVec.ofNat 64 (DN.News.Calendar.civilWord z))
    (fun m m' v hm ⟨e1, e2⟩ => ⟨e2.trans hm, e1⟩)
    fun v m h => by rw [h.1]; exact hb) (fun u h => h) fun u ⟨v, h⟩ => ?_
  obtain ⟨hm, hv⟩ := h.2
  subst hv; exact ⟨h.1, hm⟩

theorem mem_artNum10 : gd ArticleProg.artNum10 ∈
    ArticleProg.functions ArticleSpec.spec (ArticleProg.entries ArticleSpec.spec) .none :=
  List.mem_append_right _ (List.mem_map.2 ⟨ArticleProg.artNum10, by simp, rfl⟩)

theorem broken_out {A : Word} : ¬OutScr A (at_ A aBroken) := fun ⟨z, h1, h2, e⟩ => by
  have := broken_low; have := sets_le_X; have := X_val
  have := DN.News.ScanRun.at_inj (by omega) (by rw [xFirst_eq] at h2; omega) e
  rw [xDec_eq] at h1; omega

/-- **A call of `artNum10`**, the check after it passed: `X`'s digits after the output `OUT`, the place past them.
The other words are kept. -/
theorem num10Call_frag (o : Oracle σ) {R : Ret} {A : Word} {s0 : PancakeState σ} (hA : Area ArticleProg.ofs A s0)
    (hD : ArtDom A s0.memaddrs) (hcode : ArtCode s0.code) {rt : String} (hra : rt ≠ "a") {l : List (String × Value)}
    (hla : l.lookup "a" = some A) (hrt : Fresh rt l = true) {m0 : Word → Word} (hb : m0 (at_ A aBroken) = 0)
    {OUT : Bytes} (hO : BytesAt A s0.memaddrs s0.be ArticleProg.xOut ArticleProg.outMax OUT m0) {ox : String}
    {X : Nat} (hX : X < 2 ^ 64) (hfit : OUT.length + (ArticleSpec.decimal X).length ≤ ArticleProg.outMax)
    (ho : l.lookup ox = some (BitVec.ofNat 64 OUT.length)) {e2 : Syntax.PExpr} {E2 : PancakeExp}
    (he2 : Lower.lowerExp e2 = some E2) (hv2 : ∀ u, RunF s0 l (· = m0) u → eval u E2 = some (BitVec.ofNat 64 X)) :
    FragR o R (guardS (.call rt "artNum10" [v ox, e2])) (RunF s0 l (· = m0))
      (fun u => ∃ m, RunF s0 ((rt, BitVec.ofNat 64 (OUT.length + (ArticleSpec.decimal X).length)) :: l)
        (· = m) u ∧ (∀ x, ¬OutScr A x → m x = m0 x) ∧
        BytesAt A s0.memaddrs s0.be ArticleProg.xOut ArticleProg.outMax (OUT ++ ArticleSpec.decimal X) m) := by
  refine fragR_conseq (gcall_frag o hA hcode hra (f := ArticleProg.artNum10) mem_artNum10 (by decide)
    (DN.News.AbnfGen.lowerArgs_two (a := v ox) rfl he2) hla (vs := [BitVec.ofNat 64 OUT.length, BitVec.ofNat 64 X])
    rfl (fun u h => by simp only [evalArgs, ev_var (vals_lookup h.1.vals ho), hv2 u h])
    (Rf := Num10Ret A s0.memaddrs s0.be OUT X)
    (fun s1 hA1 _ hm hbe hloc hF => by
      have := artNum10_ok o hA1 (by rw [hm]; exact hD) (by rw [hF, hm, hbe]; exact hO) hX hfit
        ((hloc "o").trans rfl) ((hloc "x").trans rfl)
      rw [hm, hbe] at this; exact this) hrt
    (G := fun w m => w = BitVec.ofNat 64 (OUT.length + (ArticleSpec.decimal X).length) ∧
      (∀ x, ¬OutScr A x → m x = m0 x) ∧
      BytesAt A s0.memaddrs s0.be ArticleProg.xOut ArticleProg.outMax (OUT ++ ArticleSpec.decimal X) m)
    (fun m m' w hm hr => by subst hm; exact hr)
    fun w m h => by rw [h.2.1 _ broken_out]; exact hb) (fun u h => h) fun u ⟨w, h⟩ => ?_
  obtain ⟨hw, hfr, hout⟩ := h.2
  subst hw; exact ⟨u.memory, ⟨h.1, rfl⟩, hfr, hout⟩

/-! ## A text written out -/

/-- One code of a text put after the output. -/
def storeG (k : Nat × Nat) : Syntax.PStmt :=
  .storeb (eAdd (Syntax.atOff (v "a") (ArticleProg.xOut + k.2)) (v "o")) (n k.1)

/-- **A text's codes put after the output**, from its `k0`-th, the output's place in `o` kept. -/
theorem stores_frag (o : Oracle σ) {s1 : PancakeState σ} {L : List (String × Value)} {A : Word}
    (hD : ArtDom A s1.memaddrs) (hA8 : A.toNat % 8 = 0) (hla : L.lookup "a" = some A) {O : Nat}
    (ho : L.lookup "o" = some (BitVec.ofNat 64 O)) {m0 : Word → Word} :
    ∀ (cs : List Nat) (k0 : Nat) (M : Word → Word) (OUT : Bytes), OUT.length = O + k0 →
      O + k0 + cs.length ≤ ArticleProg.outMax → (∀ c ∈ cs, c < 256) →
      BytesAt A s1.memaddrs s1.be ArticleProg.xOut ArticleProg.outMax OUT M → (∀ x, ¬OutScr A x → M x = m0 x) →
      Frag o ((cs.zipIdx k0).map storeG) (RunF s1 L (· = M)) (fun u => ∃ M', RunF s1 L (· = M') u ∧
        BytesAt A s1.memaddrs s1.be ArticleProg.xOut ArticleProg.outMax (OUT ++ cs.map (BitVec.ofNat 8 ·)) M' ∧
        ∀ x, ¬OutScr A x → M' x = m0 x)
  | [], _, M, OUT, _, _, _, hO, hfr => frag_nil o fun u h => ⟨M, h, by simpa using hO, hfr⟩
  | c :: cs, k0, M, OUT, hl, hfit, hc, hO, hfr => by
    have hOm := outMax_eq
    have hxo := xOut_dec
    have hdm := dec_dm hD hA8
    simp only [List.length_cons] at hfit
    have hc0 : c < 256 := hc c List.mem_cons_self
    let b := BitVec.ofNat 8 c
    have hpos : at_ A (ArticleProg.xOut + k0 + O) = at_ A (ArticleProg.xOut + OUT.length) := by
      rw [hl, Nat.add_assoc, Nat.add_comm k0 O]
    refine frag_append (xs := [_]) (frag_conseq (putAt_frag o hla (off := ArticleProg.xOut + k0) (i := O)
      (by rw [xOut_eq]; simp) ho rfl (b := b) (fun u h => ⟨_, rfl, DN.Compiler.Bytes.setWidth_ofNat_8 c⟩)
      (by rw [hpos, hxo, Nat.add_assoc]; exact hdm _ (by omega))) (fun _ h => h) fun _ h => h) ?_
    have hsnoc := bytesAt_snoc hO (by omega) (by rw [xOut_eq]; omega)
      (by rw [hxo, Nat.add_assoc]; exact hdm _ (by omega)) b
    have h' := stores_frag o hD hA8 hla ho cs (k0 + 1)
      (DN.Compiler.Bytes.putByte M s1.be (at_ A (ArticleProg.xOut + k0 + O)) b) (OUT ++ [b]) (by simp [hl]; omega)
      (by omega)
      (fun c' h' => hc c' (List.mem_cons_of_mem _ h')) (by rw [hpos]; exact hsnoc)
      (fun x hx => (put_frame hA8 (by rw [hxo]; omega) (by rw [hxo, xDec_eq, xFirst_eq]; omega) _ hx).trans (hfr x hx))
    simpa [List.zipIdx_cons] using h'

theorem codes_length (s : String) : (codes s).length = s.length := by simp [codes]

theorem putConst_eq (s : String) : ArticleProg.putConst s =
    [kept "o" (ArticleProg.outMax - s.length)] ++ ((codes s).zipIdx 0).map storeG ++
      [.assign "o" (eAdd (v "o") (n s.length))] := rfl

/-- **A text written out**: `s`'s bytes after the output, `o` past them. -/
theorem putConst_frag (o : Oracle σ) {s1 : PancakeState σ} {L : List (String × Value)} {A : Word}
    (hD : ArtDom A s1.memaddrs) (hA8 : A.toNat % 8 = 0) (hla : L.lookup "a" = some A) {OUT : Bytes}
    (ho : L.lookup "o" = some (BitVec.ofNat 64 OUT.length)) {s : String} (hs : Ascii s)
    (hfit : OUT.length + s.length ≤ ArticleProg.outMax) {M m0 : Word → Word}
    (hO : BytesAt A s1.memaddrs s1.be ArticleProg.xOut ArticleProg.outMax OUT M) (hfr : ∀ x, ¬OutScr A x → M x = m0 x) :
    Frag o (ArticleProg.putConst s) (RunF s1 L (· = M)) (fun u => ∃ M', RunF s1
      (("o", BitVec.ofNat 64 (OUT.length + s.length)) :: without "o" L) (· = M') u ∧
      BytesAt A s1.memaddrs s1.be ArticleProg.xOut ArticleProg.outMax (OUT ++ DN.News.CommandSpec.ascii s) M' ∧
      ∀ x, ¬OutScr A x → M' x = m0 x) := by
  have hOm := outMax_eq
  have hcl := codes_length s
  rw [putConst_eq]
  refine frag_append (xs := [_]) (kept_frag o (by rw [hOm]; omega) (runF_clock _ _ _)
    fun u h => ⟨OUT.length, vals_lookup h.1.vals ho, by omega⟩) ?_
  refine frag_append (stores_frag o hD hA8 hla ho (codes s) 0 M OUT rfl (by omega) hs hO hfr) ?_
  have hlow : LowKK [.assign "o" (eAdd (v "o") (n s.length))] := lowK_any _ (k := .skip) rfl
  refine frag_exists hlow fun M' => ?_
  refine frag_pure (BytesAt A s1.memaddrs s1.be ArticleProg.xOut ArticleProg.outMax
    (OUT ++ (codes s).map (BitVec.ofNat 8 ·)) M' ∧ ∀ x, ¬OutScr A x → M' x = m0 x) (fun u h => h.2) hlow
    fun ⟨hO', hfr'⟩ => ?_
  refine frag_conseq (runF_set o rfl ho (v := BitVec.ofNat 64 (OUT.length + s.length)) fun u h => by
    rw [ev_add (ev_var (vals_lookup h.1.vals ho)) rfl, ← BitVec.ofNat_add]) (fun u h => h.1)
    fun u h => ⟨M', h, by rw [codes_ascii]; exact hO', hfr'⟩

/-! ## Two digits written out -/

theorem pad2_eq : ∀ X, X < 100 → ArticleSpec.pad2 X = [digitByte (X / 10), digitByte (X % 10)] := by
  decide +kernel

/-- `pad2` as guarded: the tens by `artDiv`, then both digits written out. -/
def pad2G (x : Syntax.PExpr) (k : Nat) : List Syntax.PStmt :=
  guardS (.call s!"t{k}" "artDiv" [x, n 10]) ++
    [kept "o" (ArticleProg.outMax - 2),
     .storeb (eAdd (Syntax.atOff (v "a") ArticleProg.xOut) (v "o")) (eAdd (n 48) (v s!"t{k}")),
     .storeb (eAdd (Syntax.atOff (v "a") (ArticleProg.xOut + 1)) (v "o"))
       (eAdd (n 48) (eSub x (eMul (v s!"t{k}") (n 10)))),
     .assign "o" (eAdd (v "o") (n 2))]

theorem guard_pad2 (x : Syntax.PExpr) (k : Nat) : guardL (ArticleProg.pad2 x k) = pad2G x k := rfl

theorem pows_keep {A : Word} {m m0 : Word → Word} (hfr : ∀ x, ¬OutScr A x → m x = m0 x) (hP : Pows m0 A) :
    Pows m A := fun j hj => by
  rw [hfr _ fun ⟨z, h1, h2, e⟩ => by
    have := sets_le_X; have := X_val; have hpw : aPow + 8 * j < aSets := (pow_in hj).2
    have := DN.News.ScanRun.at_inj (by omega) (by rw [xFirst_eq] at h2; omega) e
    rw [xDec_eq] at h1; omega]
  exact hP j hj

/-- **Two digits written out**: `X`, below 100, as `pad2` writes it after the output. -/
theorem pad2_frag (o : Oracle σ) {R : Ret} {s1 : PancakeState σ} {L : List (String × Value)} {A : Word}
    (hA : Area ArticleProg.ofs A s1) (hD : ArtDom A s1.memaddrs) (hcode : ArtCode s1.code) (hla : L.lookup "a" = some A)
    {k : Nat} (hrt : Fresh s!"t{k}" L = true) (hra : s!"t{k}" ≠ "a") (hro : s!"t{k}" ≠ "o") {OUT : Bytes}
    (ho : L.lookup "o" = some (BitVec.ofNat 64 OUT.length)) (hfit : OUT.length + 2 ≤ ArticleProg.outMax)
    {x : Syntax.PExpr} {E : PancakeExp} (he : Lower.lowerExp x = some E) {X : Nat} (hX : X < 100)
    (hv : ∀ u (l : List (String × Value)) (M : Word → Word), (∀ q ∈ L, q ∈ l) → RunF s1 l (· = M) u →
      eval u E = some (BitVec.ofNat 64 X))
    {M m0 : Word → Word} (hO : BytesAt A s1.memaddrs s1.be ArticleProg.xOut ArticleProg.outMax OUT M)
    (hfr : ∀ x, ¬OutScr A x → M x = m0 x) (hP : Pows m0 A) (hb : m0 (at_ A aBroken) = 0) :
    FragR o R (pad2G x k) (RunF s1 L (· = M)) (fun u => ∃ M', RunF s1
      (("o", BitVec.ofNat 64 (OUT.length + 2)) :: without "o" ((s!"t{k}", BitVec.ofNat 64 (X / 10)) :: L)) (· = M') u ∧
      BytesAt A s1.memaddrs s1.be ArticleProg.xOut ArticleProg.outMax (OUT ++ ArticleSpec.pad2 X) M' ∧
      ∀ x, ¬OutScr A x → M' x = m0 x) := by
  have hA8 := hA.hA
  have hOm := outMax_eq
  have hxo := xOut_dec
  have hdm := dec_dm hD hA8
  refine fragR_append (DN.News.ArticleCal.divCall_frag o hA hcode hra hla hrt (pows_keep hfr hP)
    (by rw [hfr _ broken_out]; exact hb) he (X := X) (D := 10) (by omega) (by decide) (by decide)
    fun u h => hv u L M (fun _ hq => hq) h) ?_
  let L1 := (s!"t{k}", BitVec.ofNat 64 (X / 10)) :: L
  have hlo : L1.lookup "o" = some (BitVec.ofNat 64 OUT.length) := by
    show ((s!"t{k}", _) :: L).lookup "o" = _
    rw [DN.News.ScanRun.lookup_cons_ne (Ne.symm hro)]; exact ho
  have hla1 : L1.lookup "a" = some A := by
    show ((s!"t{k}", _) :: L).lookup "a" = _
    rw [DN.News.ScanRun.lookup_cons_ne (Ne.symm hra)]; exact hla
  refine fragR_append (xs := [_]) (fragR_of (kept_frag o (by rw [hOm]; decide) (runF_clock _ _ _)
    fun u h => ⟨OUT.length, vals_lookup h.1.vals hlo, by omega⟩)) ?_
  let d1 := digitByte (X / 10)
  let d2 := digitByte (X % 10)
  let M1 := DN.Compiler.Bytes.putByte M s1.be (at_ A (ArticleProg.xOut + OUT.length)) d1
  let M2 := DN.Compiler.Bytes.putByte M1 s1.be (at_ A (ArticleProg.xOut + 1 + OUT.length)) d2
  refine fragR_append (xs := [_]) (fragR_of (putAt_frag o hla1 (by rw [xOut_eq]; rfl) hlo rfl (b := d1)
    (fun u h => ⟨_, ev_add rfl (ev_var (vals_lookup h.1.vals (by rw [List.lookup_cons, beq_self_eq_true]))), by
      rw [← BitVec.ofNat_add, DN.Compiler.Bytes.setWidth_ofNat_8]; rfl⟩)
    (by rw [hxo, Nat.add_assoc]; exact hdm _ (by omega)))) ?_
  refine fragR_append (xs := [_]) (fragR_of (putAt_frag o hla1 (off := ArticleProg.xOut + 1) (by rw [xOut_eq]; rfl)
    hlo (by
      show Lower.lowerExp (.binop .add (.const 48) (.binop .sub x (.binop .mul (.var s!"t{k}") (.const 10)))) = _
      simp only [Lower.lowerExp, he]; rfl) (b := d2) (fun u h => ⟨_,
      ev_add rfl (DN.News.ArticleCal.ev_subE (hv u L1 M1 (fun q hq => List.mem_cons_of_mem _ hq) h)
        (ev_mulc (vals_lookup h.1.vals (by rw [List.lookup_cons, beq_self_eq_true]))) (Nat.div_mul_le_self X 10)
        (by omega)), by
      rw [← BitVec.ofNat_add, DN.Compiler.Bytes.setWidth_ofNat_8, show X - X / 10 * 10 = X % 10 by omega]; rfl⟩)
    (by rw [hxo, Nat.add_assoc, Nat.add_assoc]; exact hdm _ (by omega)))) ?_
  refine fragR_of (frag_conseq (runF_set o rfl hlo (v := BitVec.ofNat 64 (OUT.length + 2)) fun u h => by
    rw [ev_add (ev_var (vals_lookup h.1.vals hlo)) rfl, ← BitVec.ofNat_add]) (fun _ h => h)
    fun u h => ⟨M2, h, ?_, fun y hy => ?_⟩)
  · have h1 := bytesAt_snoc hO (by omega) (by rw [xOut_eq]; omega)
      (by rw [hxo, Nat.add_assoc]; exact hdm _ (by omega)) d1
    have h2 := bytesAt_snoc h1 (by simp; omega) (by rw [xOut_eq]; omega)
      (by rw [List.length_append, List.length_singleton, hxo, Nat.add_assoc]; exact hdm _ (by omega)) d2
    rw [pad2_eq X hX]
    have e : at_ A (ArticleProg.xOut + 1 + OUT.length) = at_ A (ArticleProg.xOut + (OUT ++ [d1]).length) := by
      rw [List.length_append, List.length_singleton]; congr 1; omega
    rw [List.append_assoc] at h2
    show BytesAt _ _ _ _ _ (OUT ++ [d1, d2]) (DN.Compiler.Bytes.putByte M1 s1.be _ d2)
    rw [e]; exact h2
  · show DN.Compiler.Bytes.putByte M1 s1.be _ d2 y = _
    rw [put_frame hA8 (y := ArticleProg.xOut + 1 + OUT.length) (by rw [hxo]; omega)
      (by rw [hxo, xDec_eq, xFirst_eq]; omega) _ hy]
    show DN.Compiler.Bytes.putByte M s1.be _ d1 y = _
    rw [put_frame hA8 (y := ArticleProg.xOut + OUT.length) (by rw [hxo]; omega)
      (by rw [hxo, xDec_eq, xFirst_eq]; omega) _ hy]
    exact hfr y hy

/-! ## A name chosen out of a list -/

theorem storeG_low (k : Nat × Nat) : LowKK [storeG k] := by
  have hx : (ArticleProg.xOut + k.2 == 0) = false := by rw [xOut_eq]; simp
  refine lowKK_one rfl (a := .storeByte
    (.op .add (.op .add (.var "a") (.const (BitVec.ofNat 64 (ArticleProg.xOut + k.2))))
    (.var "o")) (.const (BitVec.ofNat 64 k.1))) ?_
  simp only [storeG]
  rw [atOff_eq hx]; rfl

theorem stores_low : ∀ ks : List (Nat × Nat), LowKK (ks.map storeG)
  | [] => lowKK_nil
  | k :: ks => lowKK_append (xs := [_]) (storeG_low k) (stores_low ks)

theorem putConst_low (s : String) : LowKK (ArticleProg.putConst s) := by
  rw [putConst_eq]
  exact lowKK_append (lowKK_append (lowK_any _ (k := .skip) rfl) (stores_low _)) (lowK_any _ (k := .skip) rfl)

theorem putConst_declared (s : String) : declared (ArticleProg.putConst s) = [] := by
  rw [putConst_eq, declared_append, declared_append]
  have : ∀ ks : List (Nat × Nat), declared (ks.map storeG) = [] := by
    intro ks; induction ks with
    | nil => rfl
    | cons k ks ih => exact ih
  rw [this]; rfl

/-- The branches choosing a name: the one whose number, `off` past its place, is `var`'s writes it. -/
def namesS (var : String) (off : Nat) (names : List String) (k0 : Nat) : List Syntax.PStmt :=
  (names.zipIdx k0).map fun sk => ifs (eEq (v var) (n (sk.2 + off))) (ArticleProg.putConst sk.1)

theorem names_low (var : String) (off : Nat) : ∀ (names : List String) (k0 : Nat), LowKK (namesS var off names k0)
  | [], _ => lowKK_nil
  | s :: names, k0 => by
    have h := names_low var off names (k0 + 1)
    simp only [namesS, List.zipIdx_cons, List.map_cons] at h ⊢
    exact lowKK_append (xs := [_]) (lowKK_ite rfl (putConst_low s) lowKK_nil) h

/-- **No name chosen**: `var`'s number is none of theirs. -/
theorem names_none (o : Oracle σ) {s1 : PancakeState σ} {L : List (String × Value)} {F : (Word → Word) → Prop}
    {var : String} {W : Nat} (hw : L.lookup var = some (BitVec.ofNat 64 W)) (hW : W < 2 ^ 64) {off : Nat} :
    ∀ (names : List String) (k0 : Nat), k0 + names.length + off < 2 ^ 64 →
      (∀ i, i < names.length → W ≠ k0 + i + off) →
      Frag o (namesS var off names k0) (RunF s1 L F) (RunF s1 L F)
  | [], _, _, _ => frag_nil o fun _ h => h
  | nm :: names, k0, hb, hne => by
    simp only [List.length_cons] at hb
    have h := names_none o (s1 := s1) (F := F) hw hW (off := off) names (k0 + 1) (by omega) fun i hi => by
      have := hne (i + 1) (by simp; omega); omega
    simp only [namesS, List.zipIdx_cons, List.map_cons] at h ⊢
    refine frag_append (xs := [_]) (DN.News.ArticleScan.frag_ifF o rfl (putConst_low nm) lowKK_nil
      (putConst_declared nm) rfl (runF_clock _ _ _) (fun u hu => (FramerCode.eval_eq (y := k0 + off) hW (by omega)
        (ev_var (vals_lookup hu.1.vals hw)) rfl).trans (by rw [bw_f (by have := hne 0 (by simp); omega)]))
        (frag_nil o fun _ h => h)) h

/-- **The name chosen**: the one whose number, `off` past its place, is `var`'s, written after the output. -/
theorem names_one (o : Oracle σ) {s1 : PancakeState σ} {L : List (String × Value)} {A : Word}
    (hD : ArtDom A s1.memaddrs) (hA8 : A.toNat % 8 = 0) (hla : L.lookup "a" = some A) {var : String}
    (hvo : var ≠ "o") {W : Nat} (hw : L.lookup var = some (BitVec.ofNat 64 W)) (hW : W < 2 ^ 64) {off : Nat}
    {OUT : Bytes} (ho : L.lookup "o" = some (BitVec.ofNat 64 OUT.length)) {m0 : Word → Word} :
    ∀ (names : List String) (k0 : Nat) (M : Word → Word), k0 + off ≤ W → W < k0 + off + names.length →
      k0 + names.length + off < 2 ^ 64 → (∀ s ∈ names, Ascii s) →
      OUT.length + (names[W - off - k0]!).length ≤ ArticleProg.outMax →
      BytesAt A s1.memaddrs s1.be ArticleProg.xOut ArticleProg.outMax OUT M → (∀ x, ¬OutScr A x → M x = m0 x) →
      Frag o (namesS var off names k0) (RunF s1 L (· = M)) (fun u => ∃ M', RunF s1
        (("o", BitVec.ofNat 64 (OUT.length + (names[W - off - k0]!).length)) :: without "o" L) (· = M') u ∧
        BytesAt A s1.memaddrs s1.be ArticleProg.xOut ArticleProg.outMax
          (OUT ++ DN.News.CommandSpec.ascii names[W - off - k0]!) M' ∧ ∀ x, ¬OutScr A x → M' x = m0 x)
  | [], _, _, h1, h2, _, _, _, _, _ => by simp at h2; omega
  | nm :: names, k0, M, h1, h2, hb, hasc, hfit, hO, hfr => by
    simp only [List.length_cons] at h2 hb
    have hQc : Safe.ClockFree (fun u => ∃ M', RunF s1
        (("o", BitVec.ofNat 64 (OUT.length + ((nm :: names)[W - off - k0]!).length)) :: without "o" L) (· = M') u ∧
        BytesAt A s1.memaddrs s1.be ArticleProg.xOut ArticleProg.outMax
          (OUT ++ DN.News.CommandSpec.ascii (nm :: names)[W - off - k0]!) M' ∧ ∀ x, ¬OutScr A x → M' x = m0 x) :=
      fun u k ⟨M', h, hv⟩ => ⟨M', runF_clock _ _ _ u k h, hv⟩
    simp only [namesS, List.zipIdx_cons, List.map_cons]
    by_cases hk : W = k0 + off
    · have hidx : W - off - k0 = 0 := by omega
      simp only [hidx, List.getElem!_cons_zero] at hfit hQc ⊢
      refine frag_append (xs := [_]) (DN.News.ArticleScan.frag_ifT o rfl (putConst_low nm) lowKK_nil
        (putConst_declared nm) rfl hQc (fun u hu => (FramerCode.eval_eq (y := k0 + off) hW (by omega)
          (ev_var (vals_lookup hu.1.vals hw)) rfl).trans (by rw [bw_t (by omega)]))
        (putConst_frag o hD hA8 hla ho (hasc nm List.mem_cons_self) hfit hO hfr)) ?_
      refine frag_exists (names_low var off names (k0 + 1)) fun M' => ?_
      refine frag_pure (BytesAt A s1.memaddrs s1.be ArticleProg.xOut ArticleProg.outMax
        (OUT ++ DN.News.CommandSpec.ascii nm) M' ∧ ∀ x, ¬OutScr A x → M' x = m0 x) (fun u h => h.2)
        (names_low var off names (k0 + 1)) fun hv => ?_
      exact frag_conseq (names_none o (s1 := s1) (F := (· = M')) (lk_set hvo (by exact hw)) hW (off := off) names
        (k0 + 1)
        (by omega)
        fun i hi => by omega) (fun u h => h.1) fun u h => ⟨M', h, hv⟩
    · have hidx : W - off - k0 = (W - off - (k0 + 1)) + 1 := by omega
      rw [hidx, List.getElem!_cons_succ] at hfit ⊢
      refine frag_append (xs := [_]) (DN.News.ArticleScan.frag_ifF o rfl (putConst_low nm) lowKK_nil
        (putConst_declared nm) rfl (runF_clock _ _ _) (fun u hu => (FramerCode.eval_eq (y := k0 + off) hW (by omega)
          (ev_var (vals_lookup hu.1.vals hw)) rfl).trans (by rw [bw_f hk])) (frag_nil o fun _ h => h)) ?_
      exact names_one o hD hA8 hla hvo hw hW ho names (k0 + 1) M (by omega) (by omega) (by omega)
        (fun s hs => hasc s (List.mem_cons_of_mem _ hs)) hfit hO hfr

/-! ## `artFormat` -/

/-- `artFormat`'s values: the day, the second of the day, the calendar's fields, the weekday, the hour's parts. -/
def fmtHead : List Syntax.PStmt :=
  [areaAt ArticleProg.ofs, .dec "wl" (wd ArticleProg.xWall)] ++ guardS (.call "dd" "artDiv" [v "wl", n 86400]) ++
  [.dec "sc" (eSub (v "wl") (eMul (v "dd") (n 86400)))] ++ guardS (.call "cv" "artCivilOf" [v "dd"]) ++
  [.dec "dy" (eAnd (v "cv") (n 31)), .dec "mo" (eAnd (.shr (v "cv") (n 5)) (n 15)), .dec "yr" (.shr (v "cv") (n 9))] ++
  guardS (.call "q7" "artDiv" [eAdd (v "dd") (n 4), n 7]) ++
  [.dec "wk" (eSub (eAdd (v "dd") (n 4)) (eMul (v "q7") (n 7)))] ++
  guardS (.call "hr" "artDiv" [v "sc", n 3600]) ++ [.dec "rest" (eSub (v "sc") (eMul (v "hr") (n 3600)))] ++
  guardS (.call "mn" "artDiv" [v "rest", n 60])

/-- `artFormat`'s writing of the date. -/
def fmtTail : List Syntax.PStmt :=
  namesS "wk" 0 ArticleSpec.dayNames 0 ++ ArticleProg.putConst ", " ++ pad2G (v "dy") 0 ++
  ArticleProg.putConst " " ++ namesS "mo" 1 ArticleSpec.monthNames 0 ++ ArticleProg.putConst " " ++
  guardS (.call "o1" "artNum10" [v "o", v "yr"]) ++ [.assign "o" (v "o1")] ++ ArticleProg.putConst " " ++
  pad2G (v "hr") 1 ++ ArticleProg.putConst ":" ++ pad2G (v "mn") 2 ++ ArticleProg.putConst ":" ++
  pad2G (eSub (v "rest") (eMul (v "mn") (n 60))) 3 ++ ArticleProg.putConst " +0000" ++ [.ret (v "o")]

theorem guardL_cons (x : Syntax.PStmt) (xs : List Syntax.PStmt) : guardL (x :: xs) = guardS x ++ guardL xs := rfl

theorem guardL_putConst (s : String) : guardL (ArticleProg.putConst s) = ArticleProg.putConst s := by
  rw [putConst_eq, DN.News.ArticleGrammar.guardL_append, DN.News.ArticleGrammar.guardL_append]
  have : ∀ ks : List (Nat × Nat), guardL (ks.map storeG) = ks.map storeG := by
    intro ks; induction ks with
    | nil => rfl
    | cons k ks ih => rw [List.map_cons, guardL_cons, ih]; rfl
  rw [this]; rfl

theorem guardL_names (var : String) (off : Nat) : ∀ (names : List String) (k0 : Nat),
    guardL (namesS var off names k0) = namesS var off names k0
  | [], _ => rfl
  | nm :: names, k0 => by
    simp only [namesS, List.zipIdx_cons, List.map_cons]
    rw [guardL_cons]
    have h := guardL_names var off names (k0 + 1)
    simp only [namesS] at h
    rw [h]
    show [Syntax.PStmt.ite _ (guardL (ArticleProg.putConst nm)) []] ++ _ = _
    rw [guardL_putConst]; rfl

theorem artFormat_split : ArticleProg.artFormat.body =
    [areaAt ArticleProg.ofs, .dec "wl" (wd ArticleProg.xWall), .call "dd" "artDiv" [v "wl", n 86400],
     .dec "sc" (eSub (v "wl") (eMul (v "dd") (n 86400))), .call "cv" "artCivilOf" [v "dd"],
     .dec "dy" (eAnd (v "cv") (n 31)), .dec "mo" (eAnd (.shr (v "cv") (n 5)) (n 15)), .dec "yr" (.shr (v "cv") (n 9)),
     .call "q7" "artDiv" [eAdd (v "dd") (n 4), n 7], .dec "wk" (eSub (eAdd (v "dd") (n 4)) (eMul (v "q7") (n 7))),
     .call "hr" "artDiv" [v "sc", n 3600], .dec "rest" (eSub (v "sc") (eMul (v "hr") (n 3600))),
     .call "mn" "artDiv" [v "rest", n 60]] ++
    namesS "wk" 0 ArticleSpec.dayNames 0 ++ ArticleProg.putConst ", " ++ ArticleProg.pad2 (v "dy") 0 ++
    ArticleProg.putConst " " ++ namesS "mo" 1 ArticleSpec.monthNames 0 ++ ArticleProg.putConst " " ++
    [.call "o1" "artNum10" [v "o", v "yr"], .assign "o" (v "o1")] ++ ArticleProg.putConst " " ++
    ArticleProg.pad2 (v "hr") 1 ++ ArticleProg.putConst ":" ++ ArticleProg.pad2 (v "mn") 2 ++
    ArticleProg.putConst ":" ++ ArticleProg.pad2 (eSub (v "rest") (eMul (v "mn") (n 60))) 3 ++
    ArticleProg.putConst " +0000" ++ [.ret (v "o")] := rfl

theorem artFormat_body : guardL ArticleProg.artFormat.body = fmtHead ++ fmtTail := by
  rw [artFormat_split]
  simp only [DN.News.ArticleGrammar.guardL_append, guardL_names, guardL_putConst, guard_pad2]
  rfl

/-- What `artFormat` gives back: the output's place past the wall clock's date, written after `OUT`. Words outside
the digits' and the output's stay as in `m0`. -/
def FmtRet (A : Word) (dm : Word → Bool) (be : Bool) (OUT : Bytes) (wall : Nat) (m0 : Word → Word) : Ret :=
  fun w m => w = BitVec.ofNat 64 (OUT.length + (ArticleSpec.formatDate wall).length) ∧
    (∀ x, ¬OutScr A x → m x = m0 x) ∧
    BytesAt A dm be ArticleProg.xOut ArticleProg.outMax (OUT ++ ArticleSpec.formatDate wall) m

/-- `artFormat`'s locals once its values are worked out. -/
def fmtL (A : Word) (O wall : Nat) : List (String × Value) :=
  let dd := wall / 86400
  let sc := wall % 86400
  let c := ArticleSpec.civilFromDays dd
  [("mn", BitVec.ofNat 64 (sc % 3600 / 60)), ("rest", BitVec.ofNat 64 (sc % 3600)), ("hr", BitVec.ofNat 64 (sc / 3600)),
   ("wk", BitVec.ofNat 64 ((dd + 4) % 7)), ("q7", BitVec.ofNat 64 ((dd + 4) / 7)), ("yr", BitVec.ofNat 64 c.1),
   ("mo", BitVec.ofNat 64 c.2.1), ("dy", BitVec.ofNat 64 c.2.2),
   ("cv", BitVec.ofNat 64 (DN.News.Calendar.civilWord dd)), ("sc", BitVec.ofNat 64 sc), ("dd", BitVec.ofNat 64 dd),
   ("wl", BitVec.ofNat 64 wall), ("a", A), ("o", BitVec.ofNat 64 O)]

/-- **`artFormat`'s values**: the day, the second of the day, the calendar's fields, the weekday, the hour's parts. -/
theorem fmtHead_frag (o : Oracle σ) {R : Ret} {A : Word} {s1 : PancakeState σ} (hA : Area ArticleProg.ofs A s1)
    (hD : ArtDom A s1.memaddrs) (hcode : ArtCode s1.code) (hP : Pows s1.memory A) (hb : s1.memory (at_ A aBroken) = 0)
    {wall O : Nat} (hwall : wall < ArticleProg.wallMax)
    (hw : s1.memory (at_ A ArticleProg.xWall) = BitVec.ofNat 64 wall) :
    FragR o R fmtHead (RunF s1 [("o", BitVec.ofNat 64 O)] (· = s1.memory))
      (RunF s1 (fmtL A O wall) (· = s1.memory)) := by
  have hwm : ArticleProg.wallMax = 2 ^ 40 := rfl
  let dd := wall / 86400
  let sc := wall % 86400
  have hdd : dd < 2 ^ 30 := by simp only [dd]; omega
  obtain ⟨y1, y2, m1, m2, d1, d2⟩ := DN.News.Calendar.civilFrom_range dd hdd
  have hcwd : DN.News.Calendar.civilWord dd = (ArticleSpec.civilFromDays dd).1 * 512 +
      (ArticleSpec.civilFromDays dd).2.1 * 32 + (ArticleSpec.civilFromDays dd).2.2 := rfl
  obtain ⟨EA, hEA⟩ := atOff_lower ArticleProg.ofs
  refine fragR_append (xs := [_]) (fragR_of (runF_dec o hEA rfl (v := A) fun u h => areaAt_eval hA h.1.base hEA)) ?_
  refine fragR_append (xs := [_]) (fragR_of (runF_dec o (wd_lower 2) rfl (v := BitVec.ofNat 64 wall) fun u h => by
    rw [wordAt_eval hD h rfl (i := 2) (by decide)]; exact congrArg some hw)) ?_
  refine fragR_append (DN.News.ArticleCal.divCall_frag o hA hcode (rt := "dd") (by decide) rfl rfl hP hb rfl
    (X := wall) (D := 86400) (by omega) (by decide) (by decide) fun u h => ev_var (vals_lookup h.1.vals rfl)) ?_
  refine fragR_append (xs := [_]) (fragR_of (runF_dec o rfl rfl (v := BitVec.ofNat 64 sc) fun u h =>
    (DN.News.ArticleCal.ev_subE (ev_var (vals_lookup h.1.vals rfl)) (ev_mulc (vals_lookup h.1.vals rfl))
      (Nat.div_mul_le_self wall 86400) (by omega)).trans (by simp only [sc]; congr 2; omega))) ?_
  refine fragR_append (civilOfCall_frag o hA hcode (rt := "cv") (by decide) rfl rfl hP hb hdd rfl) ?_
  refine fragR_append (xs := [_]) (fragR_of (runF_dec o rfl rfl
    (v := BitVec.ofNat 64 (ArticleSpec.civilFromDays dd).2.2)
    fun u h => by
      rw [ev_and (ev_var (vals_lookup h.1.vals rfl)) rfl, show (BitVec.ofNat 64 31 : Word) = BitVec.ofNat 64 (2 ^ 5 - 1)
        from rfl, DN.News.Calendar.and_mask _ 5 (by omega) (by decide), hcwd]
      congr 2; omega)) ?_
  refine fragR_append (xs := [_]) (fragR_of (runF_dec o rfl rfl
    (v := BitVec.ofNat 64 (ArticleSpec.civilFromDays dd).2.1)
    fun u h => by
      rw [ev_and (ev_shr (ev_var (vals_lookup h.1.vals rfl)) (by decide)) rfl,
        DN.News.Calendar.shift_word _ 5 (by omega),
        show (BitVec.ofNat 64 15 : Word) = BitVec.ofNat 64 (2 ^ 4 - 1) from rfl,
        DN.News.Calendar.and_mask _ 4 (by omega) (by decide), hcwd]
      congr 2; omega)) ?_
  refine fragR_append (xs := [_]) (fragR_of (runF_dec o rfl rfl (v := BitVec.ofNat 64 (ArticleSpec.civilFromDays dd).1)
    fun u h => by
      rw [ev_shr (ev_var (vals_lookup h.1.vals rfl)) (by decide), DN.News.Calendar.shift_word _ 9 (by omega), hcwd]
      congr 2; omega)) ?_
  refine fragR_append (DN.News.ArticleCal.divCall_frag o hA hcode (rt := "q7") (by decide) rfl rfl hP hb rfl
    (X := dd + 4) (D := 7) (by omega) (by decide) (by decide) fun u h =>
      (ev_add (ev_var (vals_lookup h.1.vals rfl)) rfl).trans (by rw [← BitVec.ofNat_add])) ?_
  refine fragR_append (xs := [_]) (fragR_of (runF_dec o rfl rfl (v := BitVec.ofNat 64 ((dd + 4) % 7)) fun u h =>
    (DN.News.ArticleCal.ev_subE ((ev_add (ev_var (vals_lookup h.1.vals rfl)) rfl).trans (by rw [← BitVec.ofNat_add]))
      (ev_mulc (vals_lookup h.1.vals rfl)) (Nat.div_mul_le_self (dd + 4) 7) (by omega)).trans (by congr 2; omega))) ?_
  refine fragR_append (DN.News.ArticleCal.divCall_frag o hA hcode (rt := "hr") (by decide) rfl rfl hP hb rfl
    (X := sc) (D := 3600) (by omega) (by decide) (by decide) fun u h => ev_var (vals_lookup h.1.vals rfl)) ?_
  refine fragR_append (xs := [_]) (fragR_of (runF_dec o rfl rfl (v := BitVec.ofNat 64 (sc % 3600)) fun u h =>
    (DN.News.ArticleCal.ev_subE (ev_var (vals_lookup h.1.vals rfl)) (ev_mulc (vals_lookup h.1.vals rfl))
      (Nat.div_mul_le_self sc 3600) (by omega)).trans (by congr 2; omega))) ?_
  exact DN.News.ArticleCal.divCall_frag o hA hcode (rt := "mn") (by decide) rfl rfl hP hb rfl
    (X := sc % 3600) (D := 60) (by omega) (by decide) (by decide) fun u h => ev_var (vals_lookup h.1.vals rfl)

theorem ascii_append (a b : String) :
    DN.News.CommandSpec.ascii (a ++ b) = DN.News.CommandSpec.ascii a ++ DN.News.CommandSpec.ascii b := by
  simp only [DN.News.CommandSpec.ascii, String.toList_append, List.map_append]

theorem ascii_length (s : String) : (DN.News.CommandSpec.ascii s).length = s.length := by
  simp [DN.News.CommandSpec.ascii]

theorem weekday_nat (dd : Nat) : ArticleSpec.weekday (dd : Int) = (dd + 4) % 7 := by
  unfold ArticleSpec.weekday; omega

theorem getD_get {l : List String} {i : Nat} (h : i < l.length) : l.getD i "" = l[i]! := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h, Option.getD_some, getElem!_pos l i h]

/-- **`formatDate` in the pieces `artFormat` writes**. -/
theorem formatDate_split (wall : Nat) : ArticleSpec.formatDate wall =
    DN.News.CommandSpec.ascii (ArticleSpec.dayNames.getD (ArticleSpec.weekday (wall / 86400 : Nat)) "") ++
    DN.News.CommandSpec.ascii ", " ++ ArticleSpec.pad2 (ArticleSpec.civilFromDays (wall / 86400)).2.2 ++
    DN.News.CommandSpec.ascii " " ++
    DN.News.CommandSpec.ascii (ArticleSpec.monthNames.getD ((ArticleSpec.civilFromDays (wall / 86400)).2.1 - 1) "") ++
    DN.News.CommandSpec.ascii " " ++ DN.News.CommandSpec.decimal (ArticleSpec.civilFromDays (wall / 86400)).1 ++
    DN.News.CommandSpec.ascii " " ++ ArticleSpec.pad2 (wall % 86400 / 3600) ++ DN.News.CommandSpec.ascii ":" ++
    ArticleSpec.pad2 (wall % 86400 % 3600 / 60) ++ DN.News.CommandSpec.ascii ":" ++
    ArticleSpec.pad2 (wall % 86400 % 60) ++
    DN.News.CommandSpec.ascii " +0000" := by
  simp only [ArticleSpec.formatDate, ascii_append, DN.News.CommandSpec.decimal, List.append_assoc]
  rfl

theorem day_len : ∀ i, i < 7 → (ArticleSpec.dayNames[i]!).length = 3 := by decide
theorem month_len : ∀ i, i < 12 → (ArticleSpec.monthNames[i]!).length = 3 := by decide
theorem pad2_len {X : Nat} (hX : X < 100) : (ArticleSpec.pad2 X).length = 2 := by rw [pad2_eq X hX]; rfl

theorem formatDate_length {wall : Nat} (hw : wall < 2 ^ 40) : (ArticleSpec.formatDate wall).length =
    27 + (ArticleSpec.decimal (ArticleSpec.civilFromDays (wall / 86400)).1).length := by
  have hdd : wall / 86400 < 2 ^ 30 := by omega
  obtain ⟨-, -, m1, m2, d1, d2⟩ := DN.News.Calendar.civilFrom_range (wall / 86400) hdd
  have hwk : (wall / 86400 + 4) % 7 < 7 := Nat.mod_lt _ (by decide)
  rw [formatDate_split, weekday_nat, getD_get (by simp [ArticleSpec.dayNames]; omega),
    getD_get (by simp [ArticleSpec.monthNames]; omega)]
  simp only [List.length_append, ascii_length, day_len _ hwk,
    month_len ((ArticleSpec.civilFromDays (wall / 86400)).2.1 - 1) (by omega),
    pad2_len (X := (ArticleSpec.civilFromDays (wall / 86400)).2.2) (by omega),
    pad2_len (by omega : wall % 86400 / 3600 < 100), pad2_len (by omega : wall % 86400 % 3600 / 60 < 100),
    pad2_len (by omega : wall % 86400 % 60 < 100), show ", ".length = 2 from rfl, show " ".length = 1 from rfl,
    show ":".length = 1 from rfl, show " +0000".length = 6 from rfl]
  show _ = 27 + (DN.News.CommandSpec.decimal _).length
  omega

/-- The output written so far, `P`, with the locals `L`; every word outside the output functions' as `m0` holds
it. -/
def OutA (s1 : PancakeState σ) (A : Word) (m0 : Word → Word) (L : List (String × Value)) (P : Bytes) : Assn σ :=
  fun u => ∃ M, RunF s1 L (· = M) u ∧ BytesAt A s1.memaddrs s1.be ArticleProg.xOut ArticleProg.outMax P M ∧
    ∀ x, ¬OutScr A x → M x = m0 x

theorem out_lift (o : Oracle σ) {R : Ret} {xs : List Syntax.PStmt} (hlow : LowKK xs) {s1 : PancakeState σ} {A : Word}
    {m0 : Word → Word} {L1 L2 : List (String × Value)} {P1 P2 : Bytes}
    (h : ∀ M, BytesAt A s1.memaddrs s1.be ArticleProg.xOut ArticleProg.outMax P1 M → (∀ x, ¬OutScr A x → M x = m0 x) →
      FragR o R xs (RunF s1 L1 (· = M)) (OutA s1 A m0 L2 P2)) :
    FragR o R xs (OutA s1 A m0 L1 P1) (OutA s1 A m0 L2 P2) := by
  refine fragR_exists hlow fun M => ?_
  exact fragR_pure (BytesAt A s1.memaddrs s1.be ArticleProg.xOut ArticleProg.outMax P1 M ∧
    ∀ x, ¬OutScr A x → M x = m0 x) (fun u h => h.2) hlow fun ⟨hO, hfr⟩ =>
      fragR_conseq (h M hO hfr) (fun u h => h.1) fun _ h => h

theorem fmt_const (o : Oracle σ) {R : Ret} {A : Word} {s1 : PancakeState σ} (hD : ArtDom A s1.memaddrs)
    (hA8 : A.toNat % 8 = 0) {m0 : Word → Word} {wall : Nat} {P : Bytes} {s : String} (hs : Ascii s)
    (hfit : P.length + s.length ≤ ArticleProg.outMax) :
    FragR o R (ArticleProg.putConst s) (OutA s1 A m0 (fmtL A P.length wall) P)
      (OutA s1 A m0 (fmtL A (P ++ DN.News.CommandSpec.ascii s).length wall) (P ++ DN.News.CommandSpec.ascii s)) :=
  out_lift o (putConst_low s) fun M hO hfr => fragR_of (frag_conseq (putConst_frag o hD hA8 rfl rfl hs hfit hO hfr)
    (fun _ h => h) fun u ⟨M', h, hv⟩ => ⟨M', by
      rw [List.length_append, ascii_length]
      exact runF_of h (by
        repeat (refine lookups_cons rfl ?_)
        exact lookups_nil), hv⟩)

theorem fmt_pad (o : Oracle σ) {R : Ret} {A : Word} {s1 : PancakeState σ} (hA : Area ArticleProg.ofs A s1)
    (hD : ArtDom A s1.memaddrs) (hcode : ArtCode s1.code) {m0 : Word → Word} (hP : Pows m0 A)
    (hb : m0 (at_ A aBroken) = 0) {wall : Nat} {P : Bytes} {k : Nat} {x : Syntax.PExpr} (hlow : LowKK (pad2G x k))
    (hrt : Fresh s!"t{k}" (fmtL A P.length wall) = true) (hra : s!"t{k}" ≠ "a") (hro : s!"t{k}" ≠ "o")
    {E : PancakeExp} (he : Lower.lowerExp x = some E) {X : Nat} (hX : X < 100)
    (hv : ∀ u (l : List (String × Value)) (M : Word → Word), (∀ q ∈ fmtL A P.length wall, q ∈ l) →
      RunF s1 l (· = M) u → eval u E = some (BitVec.ofNat 64 X))
    (hfit : P.length + 2 ≤ ArticleProg.outMax) :
    FragR o R (pad2G x k) (OutA s1 A m0 (fmtL A P.length wall) P)
      (OutA s1 A m0 (fmtL A (P ++ ArticleSpec.pad2 X).length wall) (P ++ ArticleSpec.pad2 X)) :=
  out_lift o hlow fun M hO hfr => fragR_conseq (pad2_frag o hA hD hcode rfl hrt hra hro rfl hfit he hX hv hO hfr hP hb)
    (fun _ h => h) fun u ⟨M', h, hv'⟩ => ⟨M', by
      rw [List.length_append, pad2_eq X hX]
      exact runF_of h (by
        repeat (refine lookups_cons rfl ?_)
        exact lookups_nil), hv'⟩

theorem fmt_names (o : Oracle σ) {R : Ret} {A : Word} {s1 : PancakeState σ} (hD : ArtDom A s1.memaddrs)
    (hA8 : A.toNat % 8 = 0) {m0 : Word → Word} {wall : Nat} {P : Bytes} {var : String} (hvo : var ≠ "o") {W : Nat}
    (hw : (fmtL A P.length wall).lookup var = some (BitVec.ofNat 64 W)) (hW : W < 2 ^ 64) {off : Nat}
    {names : List String} (h1 : off ≤ W) (h2 : W < off + names.length) (hsm : names.length + off < 2 ^ 64)
    (hasc : ∀ s ∈ names, Ascii s) (hfit : P.length + (names[W - off]!).length ≤ ArticleProg.outMax) :
    FragR o R (namesS var off names 0) (OutA s1 A m0 (fmtL A P.length wall) P)
      (OutA s1 A m0 (fmtL A (P ++ DN.News.CommandSpec.ascii names[W - off]!).length wall)
        (P ++ DN.News.CommandSpec.ascii names[W - off]!)) :=
  out_lift o (names_low var off names 0) fun M hO hfr => fragR_of (frag_conseq
    (names_one o hD hA8 rfl hvo hw hW rfl names 0 M (by omega) (by omega) (by omega) hasc (by simpa using hfit) hO hfr)
    (fun _ h => h) fun u ⟨M', h, hv⟩ => ⟨M', by
      rw [List.length_append, ascii_length]
      simp only [Nat.sub_zero] at h
      exact runF_of h (by
        repeat (refine lookups_cons rfl ?_)
        exact lookups_nil), by simpa using hv⟩)

theorem fmt_num (o : Oracle σ) {R : Ret} {A : Word} {s1 : PancakeState σ} (hA : Area ArticleProg.ofs A s1)
    (hD : ArtDom A s1.memaddrs) (hcode : ArtCode s1.code) {m0 : Word → Word} (hb : m0 (at_ A aBroken) = 0)
    {wall : Nat} {P : Bytes} (hY : (ArticleSpec.civilFromDays (wall / 86400)).1 < 2 ^ 64)
    (hfit : P.length + (ArticleSpec.decimal (ArticleSpec.civilFromDays (wall / 86400)).1).length ≤
      ArticleProg.outMax) :
    FragR o R (guardS (.call "o1" "artNum10" [v "o", v "yr"])) (OutA s1 A m0 (fmtL A P.length wall) P)
      (OutA s1 A m0 (("o1", BitVec.ofNat 64 (P.length +
        (ArticleSpec.decimal (ArticleSpec.civilFromDays (wall / 86400)).1).length)) :: fmtL A P.length wall)
        (P ++ ArticleSpec.decimal (ArticleSpec.civilFromDays (wall / 86400)).1)) :=
  out_lift o (lowK_any _ (k := .skip) rfl) fun M hO hfr => fragR_conseq
    (num10Call_frag o hA hD hcode (rt := "o1") (by decide) rfl rfl (by rw [hfr _ broken_out]; exact hb) hO hY hfit
      rfl (e2 := v "yr") rfl fun u h => ev_var (vals_lookup h.1.vals rfl))
    (fun _ h => h) fun u ⟨m, h, hfr2, hO2⟩ => ⟨m, h, hO2, fun x hx => (hfr2 x hx).trans (hfr x hx)⟩

theorem fmt_o (o : Oracle σ) {R : Ret} {A : Word} {s1 : PancakeState σ} {m0 : Word → Word} {wall : Nat} {P D : Bytes} :
    FragR o R [.assign "o" (v "o1")]
      (OutA s1 A m0 (("o1", BitVec.ofNat 64 (P.length + D.length)) :: fmtL A P.length wall) (P ++ D))
      (OutA s1 A m0 (fmtL A (P ++ D).length wall) (P ++ D)) :=
  out_lift o (lowK_any _ (k := .skip) rfl) fun M hO hfr => fragR_of (frag_conseq
    (runF_set o rfl rfl (v := BitVec.ofNat 64 (P.length + D.length)) fun u h => ev_var (vals_lookup h.1.vals rfl))
    (fun _ h => h) fun u h => ⟨M, by
      rw [List.length_append]
      exact runF_of h (by
        repeat (refine lookups_cons rfl ?_)
        exact lookups_nil), hO, hfr⟩)


/-- **`artFormat` writes the wall clock's date** after the output, as `formatDate` does, if it returns. -/
theorem artFormat_ok (o : Oracle σ) {A : Word} {s1 : PancakeState σ} (hA : Area ArticleProg.ofs A s1)
    (hD : ArtDom A s1.memaddrs) (hcode : ArtCode s1.code) (hP : Pows s1.memory A) (hb : s1.memory (at_ A aBroken) = 0)
    {OUT : Bytes} (hO : BytesAt A s1.memaddrs s1.be ArticleProg.xOut ArticleProg.outMax OUT s1.memory) {wall : Nat}
    (hwall : wall < ArticleProg.wallMax) (hw : s1.memory (at_ A ArticleProg.xWall) = BitVec.ofNat 64 wall)
    (hfit : OUT.length + (ArticleSpec.formatDate wall).length ≤ ArticleProg.outMax)
    (ho : s1.locals "o" = some (BitVec.ofNat 64 OUT.length)) :
    ∃ body, Lower.lower (gd ArticleProg.artFormat) = some body ∧
      SafeR o (fun s => s = s1) body (FmtRet A s1.memaddrs s1.be OUT wall s1.memory) fun _ => False := by
  have hA8 := hA.hA
  have hwm : ArticleProg.wallMax = 2 ^ 40 := rfl
  have hdd : wall / 86400 < 2 ^ 30 := by omega
  obtain ⟨y1, y2, m1, m2, d1, d2⟩ := DN.News.Calendar.civilFrom_range (wall / 86400) hdd
  have hwk : (wall / 86400 + 4) % 7 < 7 := Nat.mod_lt _ (by decide)
  have htot : OUT.length + (27 + (ArticleSpec.decimal (ArticleSpec.civilFromDays (wall / 86400)).1).length) ≤
      ArticleProg.outMax := by rw [← formatDate_length (by omega)]; exact hfit
  have hl1 : ", ".length = 2 := rfl
  have hl2 : " ".length = 1 := rfl
  have hl3 : ":".length = 1 := rfl
  have hl4 : " +0000".length = 6 := rfl
  refine body_of ?_
  show FragR o _ (guardL ArticleProg.artFormat.body) _ _
  rw [artFormat_body]
  refine fragR_conseq (P0 := RunF s1 [("o", BitVec.ofNat 64 OUT.length)] (· = s1.memory)) ?_ (entry_one ho)
    fun _ h => h
  refine fragR_append (fmtHead_frag o hA hD hcode hP hb hwall hw) ?_
  refine fragR_conseq (P0 := OutA s1 A s1.memory (fmtL A OUT.length wall) OUT) ?_
    (fun u h => ⟨s1.memory, h, hO, fun _ _ => rfl⟩) fun _ h => h
  unfold fmtTail
  simp only [List.append_assoc]
  have hasc : ∀ s, s = ", " ∨ s = " " ∨ s = ":" ∨ s = " +0000" → Ascii s := by
    intro s hs; rcases hs with rfl | rfl | rfl | rfl <;> (unfold Ascii; decide)
  refine fragR_append (fmt_names o hD hA8 (var := "wk") (by decide) (W := (wall / 86400 + 4) % 7) rfl (by omega)
    (off := 0) (names := ArticleSpec.dayNames) (by omega) (by simp [ArticleSpec.dayNames]; omega) (by decide)
    (by unfold Ascii; decide) (by simp only [Nat.sub_zero, day_len _ hwk]; omega)) ?_
  refine fragR_append (fmt_const o hD hA8 (s := ", ") (hasc _ (.inl rfl)) (by
    simp only [List.length_append, ascii_length, Nat.sub_zero, day_len _ hwk]; omega)) ?_
  refine fragR_append (fmt_pad o hA hD hcode hP hb (k := 0) (x := v "dy") (lowK_any _ (k := .skip) rfl) rfl
    (by decide) (by decide) rfl (X := (ArticleSpec.civilFromDays (wall / 86400)).2.2) (by omega)
    (fun u l M hl h => ev_var (h.1.vals _ (hl ("dy", BitVec.ofNat 64 (ArticleSpec.civilFromDays (wall / 86400)).2.2)
      (by simp [fmtL])))) (by
      simp only [List.length_append, ascii_length, Nat.sub_zero, day_len _ hwk]; omega)) ?_
  have hdl := day_len _ hwk
  have hml := month_len ((ArticleSpec.civilFromDays (wall / 86400)).2.1 - 1) (by omega)
  have hp1 := pad2_len (X := (ArticleSpec.civilFromDays (wall / 86400)).2.2) (by omega)
  have hp2 := pad2_len (by omega : wall % 86400 / 3600 < 100)
  have hp3 := pad2_len (by omega : wall % 86400 % 3600 / 60 < 100)
  have hp4 := pad2_len (by omega : wall % 86400 % 60 < 100)
  refine fragR_append (fmt_const o hD hA8 (s := " ") (hasc _ (.inr (.inl rfl))) (by
    simp only [List.length_append, ascii_length, Nat.sub_zero, hdl, hp1]; omega)) ?_
  refine fragR_append (fmt_names o hD hA8 (var := "mo") (by decide)
    (W := (ArticleSpec.civilFromDays (wall / 86400)).2.1)
    rfl (by omega) (off := 1) (names := ArticleSpec.monthNames) (by omega) (by simp [ArticleSpec.monthNames]; omega)
    (by decide) (by unfold Ascii; decide) (by
      simp only [List.length_append, ascii_length, Nat.sub_zero, hdl, hp1, hml]; omega)) ?_
  refine fragR_append (fmt_const o hD hA8 (s := " ") (hasc _ (.inr (.inl rfl))) (by
    simp only [List.length_append, ascii_length, Nat.sub_zero, hdl, hp1, hml]; omega)) ?_
  refine fragR_append (fmt_num o hA hD hcode hb (by omega) (by
    simp only [List.length_append, ascii_length, Nat.sub_zero, hdl, hp1, hml]; omega)) ?_
  refine fragR_append (fmt_o o) ?_
  refine fragR_append (fmt_const o hD hA8 (s := " ") (hasc _ (.inr (.inl rfl))) (by
    simp only [List.length_append, ascii_length, Nat.sub_zero, hdl, hp1, hml]; omega)) ?_
  refine fragR_append (fmt_pad o hA hD hcode hP hb (k := 1) (x := v "hr") (lowK_any _ (k := .skip) rfl) rfl
    (by decide) (by decide) rfl (X := wall % 86400 / 3600) (by omega)
    (fun u l M hl h => ev_var (h.1.vals _ (hl ("hr", BitVec.ofNat 64 (wall % 86400 / 3600)) (by simp [fmtL])))) (by
      simp only [List.length_append, ascii_length, Nat.sub_zero, hdl, hp1, hml]; omega)) ?_
  refine fragR_append (fmt_const o hD hA8 (s := ":") (hasc _ (.inr (.inr (.inl rfl)))) (by
    simp only [List.length_append, ascii_length, Nat.sub_zero, hdl, hp1, hml, hp2]; omega)) ?_
  refine fragR_append (fmt_pad o hA hD hcode hP hb (k := 2) (x := v "mn") (lowK_any _ (k := .skip) rfl) rfl
    (by decide) (by decide) rfl (X := wall % 86400 % 3600 / 60) (by omega)
    (fun u l M hl h => ev_var (h.1.vals _ (hl ("mn", BitVec.ofNat 64 (wall % 86400 % 3600 / 60)) (by simp [fmtL])))) (by
      simp only [List.length_append, ascii_length, Nat.sub_zero, hdl, hp1, hml, hp2]; omega)) ?_
  refine fragR_append (fmt_const o hD hA8 (s := ":") (hasc _ (.inr (.inr (.inl rfl)))) (by
    simp only [List.length_append, ascii_length, Nat.sub_zero, hdl, hp1, hml, hp2, hp3]; omega)) ?_
  refine fragR_append (fmt_pad o hA hD hcode hP hb (k := 3) (x := eSub (v "rest") (eMul (v "mn") (n 60)))
    (lowK_any _ (k := .skip) rfl) rfl (by decide) (by decide) rfl (X := wall % 86400 % 60) (by omega)
    (fun u l M hl h => (DN.News.ArticleCal.ev_subE
      (ev_var (h.1.vals _ (hl ("rest", BitVec.ofNat 64 (wall % 86400 % 3600)) (by simp [fmtL]))))
      (ev_mulc (h.1.vals _ (hl ("mn", BitVec.ofNat 64 (wall % 86400 % 3600 / 60)) (by simp [fmtL]))))
      (Nat.div_mul_le_self _ 60) (by omega)).trans (by congr 2; omega)) (by
      simp only [List.length_append, ascii_length, Nat.sub_zero, hdl, hp1, hml, hp2, hp3]; omega)) ?_
  refine fragR_append (fmt_const o hD hA8 (s := " +0000") (hasc _ (.inr (.inr (.inr rfl)))) (by
    simp only [List.length_append, ascii_length, Nat.sub_zero, hdl, hp1, hml, hp2, hp3, hp4]; omega)) ?_
  refine fragR_ret o rfl fun u ⟨M, h, hO', hfr'⟩ => ?_
  have hfd : OUT ++ ArticleSpec.formatDate wall = OUT ++
      DN.News.CommandSpec.ascii ArticleSpec.dayNames[(wall / 86400 + 4) % 7 - 0]! ++ DN.News.CommandSpec.ascii ", " ++
      ArticleSpec.pad2 (ArticleSpec.civilFromDays (wall / 86400)).2.2 ++ DN.News.CommandSpec.ascii " " ++
      DN.News.CommandSpec.ascii ArticleSpec.monthNames[(ArticleSpec.civilFromDays (wall / 86400)).2.1 - 1]! ++
      DN.News.CommandSpec.ascii " " ++ DN.News.CommandSpec.decimal (ArticleSpec.civilFromDays (wall / 86400)).1 ++
      DN.News.CommandSpec.ascii " " ++ ArticleSpec.pad2 (wall % 86400 / 3600) ++ DN.News.CommandSpec.ascii ":" ++
      ArticleSpec.pad2 (wall % 86400 % 3600 / 60) ++ DN.News.CommandSpec.ascii ":" ++
      ArticleSpec.pad2 (wall % 86400 % 60) ++ DN.News.CommandSpec.ascii " +0000" := by
    rw [formatDate_split, weekday_nat, getD_get (by simp [ArticleSpec.dayNames]; omega),
      getD_get (by simp [ArticleSpec.monthNames]; omega), Nat.sub_zero]
    simp only [List.append_assoc]
  refine ⟨_, ev_var (vals_lookup h.1.vals rfl), by rw [← List.length_append, hfd]; rfl, fun x hx => by
    rw [h.2]; exact hfr' x hx, ?_⟩
  rw [h.2, hfd]; exact hO'

/-! ## The premises hold of some arguments -/

theorem numMem_witness : NumMem 0 (fun _ => true) false (fun _ => 0) [0] [0] (fun _ => 0) := by
  refine ⟨fun _ _ => rfl, fun i _ hl => ?_, fun i _ hl => ?_⟩ <;>
    (have : i = 0 := by simpa using hl
     subst this; decide)

end DN.News.ArticleOut
