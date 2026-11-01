-- SPDX-License-Identifier: AGPL-3.0-or-later
import DN.Server.SessionCheck
import DN.Compiler.Frag
import DN.News.DecimalRun

/-!
# DN.Server.SessionAppend

The session's ways of putting octets in a connection's output, proven fragments: a copy (`copy_then`), a
number's decimal digits (`digits_then`), and, inside `connText`, a text of the session's, the revision, the
source's address, the Message-ID looked up last, a number and a space, a byte (`appendText_frag` and on). Each
writes its octets after those written, `o` past them, and changes no word outside the connection's output but the
session's return word (`TCtx`, `Wrote`). Where the layout's offsets lie is computed once, the table's start kept folded (`tOff`).
-/

namespace DN.Server.SessionAppend

open DN.Compiler DN.Compiler.Wp DN.Compiler.WpRet DN.Compiler.Bytes DN.Compiler.Preservation DN.Compiler.Frag DN.Server
  DN.News DN.News.DecimalRun

variable {σ : Type}

/-- A copy's octet: the source's into the destination, the place moved on. -/
def copyBody (j : String) (dst src : PancakeExp) : AProg σ :=
  .seq (.storeByte (.op .add dst (.var j)) (.loadByte (.op .add src (.var j))))
    (.assign j (.op .add (.var j) (.const 1)))

/-- What a copy asks: the octets `bs` at `S`, room for them at `D` apart from them, the counter `j`
bound, the places and the length read from neither memory nor `j`. -/
structure CopyPre (j : String) (dst src len : PancakeExp) (D S : Word) (bs : List (BitVec 8))
    (s : PancakeState σ) : Prop where
  hj : ∃ v, s.locals j = some v
  hdst : eval s dst = some D
  hsrc : eval s src = some S
  hlen : eval s len = some (BitVec.ofNat 64 bs.length)
  hshort : bs.length < 2 ^ 62
  hbytes : memBytesAt s.memory s.memaddrs s.be S bs
  hroom : ∀ i, i < bs.length → s.memaddrs (byteAlign (D + BitVec.ofNat 64 i)) = true
  hapart : ∀ i i', i < bs.length → i' < bs.length → D + BitVec.ofNat 64 i ≠ S + BitVec.ofNat 64 i'
  hnoLoad : NoLoad dst ∧ NoLoad src ∧ NoLoad len
  havoids : ExpAvoids (· = j) dst ∧ ExpAvoids (· = j) src ∧ ExpAvoids (· = j) len

/-- What a run from `s0` keeps: every local but `j`, the memory's domain, order, base, world and
code. -/
structure Kept (j : String) (s0 t : PancakeState σ) : Prop where
  locals : ∀ x, x ≠ j → t.locals x = s0.locals x
  memaddrs : t.memaddrs = s0.memaddrs
  be : t.be = s0.be
  base : t.baseAddr = s0.baseAddr
  ffi : t.ffi = s0.ffi
  code : t.code = s0.code

/-- After `k` octets: those at `D`, the source as it was, every word outside the destination's as it
was. -/
def CopyInv (j : String) (D S : Word) (bs : List (BitVec 8)) (s0 t : PancakeState σ) : Prop :=
  Kept j s0 t ∧ ∃ k, k ≤ bs.length ∧ t.locals j = some (BitVec.ofNat 64 k) ∧
    memBytesAt t.memory t.memaddrs t.be D (bs.take k) ∧ memBytesAt t.memory t.memaddrs t.be S bs ∧
    (∀ a, (∀ i, i < bs.length → a ≠ D + BitVec.ofNat 64 i) →
      memLoadByte t.memory t.memaddrs t.be a = memLoadByte s0.memory s0.memaddrs s0.be a) ∧
    ∀ w, (∀ i, i < bs.length → w ≠ byteAlign (D + BitVec.ofNat 64 i)) → t.memory w = s0.memory w

/-- What it leaves. -/
def CopyPost (j : String) (D : Word) (bs : List (BitVec 8)) (s0 t : PancakeState σ) : Prop :=
  Kept j s0 t ∧ t.locals j = some (BitVec.ofNat 64 bs.length) ∧
    memBytesAt t.memory t.memaddrs t.be D bs ∧
    (∀ a, (∀ i, i < bs.length → a ≠ D + BitVec.ofNat 64 i) →
      memLoadByte t.memory t.memaddrs t.be a = memLoadByte s0.memory s0.memaddrs s0.be a) ∧
    ∀ w, (∀ i, i < bs.length → w ≠ byteAlign (D + BitVec.ofNat 64 i)) → t.memory w = s0.memory w

/-- The copy, as it lowers, its loop carrying `CopyInv`. -/
def copyA (j : String) (dst src len : PancakeExp) (D S : Word) (bs : List (BitVec 8)) (s0 : PancakeState σ) :
    AProg σ :=
  .seq (.assign j (.const 0))
    (.while_ (CopyInv j D S bs s0) (.cmp .less (.var j) len) (copyBody j dst src))

theorem kept_refl (j : String) (s : PancakeState σ) : Kept j s s := ⟨fun _ _ => rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- **An octet copied**: the loop goes on. -/
theorem copy_step {j : String} {dst src len : PancakeExp} {D S : Word} {bs : List (BitVec 8)}
    {s0 t : PancakeState σ} (hpre : CopyPre j dst src len D S bs s0) (hk0 : Kept j s0 t) {k : Nat}
    (hk : k < bs.length) (hj : t.locals j = some (BitVec.ofNat 64 k))
    (hd : memBytesAt t.memory t.memaddrs t.be D (bs.take k)) (hs : memBytesAt t.memory t.memaddrs t.be S bs)
    (hb' : ∀ a, (∀ i, i < bs.length → a ≠ D + BitVec.ofNat 64 i) →
      memLoadByte t.memory t.memaddrs t.be a = memLoadByte s0.memory s0.memaddrs s0.be a)
    (hw : ∀ w, (∀ i, i < bs.length → w ≠ byteAlign (D + BitVec.ofNat 64 i)) → t.memory w = s0.memory w) :
    wp (copyBody j dst src) (CopyInv j D S bs s0) t := by
  have hl : ∀ x, ¬ (x = j) → t.locals x = s0.locals x := fun x hx => hk0.locals x hx
  have hD := (eval_noLoad hl hk0.base dst hpre.hnoLoad.1 hpre.havoids.1).trans hpre.hdst
  have hS := (eval_noLoad hl hk0.base src hpre.hnoLoad.2.1 hpre.havoids.2.1).trans hpre.hsrc
  have hb := hs k hk
  have hroom : t.memaddrs (byteAlign (D + BitVec.ofNat 64 k)) = true := by
    rw [hk0.memaddrs]; exact hpre.hroom k hk
  have hE : eval t (.loadByte (.op .add src (.var j))) = some ((bs[k]!).setWidth 64) := by
    simp only [eval, hS, hj, hb]
  have hA : eval t (.op .add dst (.var j)) = some (D + BitVec.ofNat 64 k) := by simp only [eval, hD, hj]
  have hst : memStoreByte t.memory t.memaddrs t.be (D + BitVec.ofNat 64 k) (((bs[k]!).setWidth 64).setWidth 8) =
      some (putByte t.memory t.be (D + BitVec.ofNat 64 k) bs[k]!) := by
    rw [setWidth64_8]; exact memStore_eq _ _ _ _ _ hroom
  simp only [copyBody, wp, hA, hE, hst]
  refine wp_assign (val := BitVec.ofNat 64 (k + 1)) (by simp [eval, hj, BitVec.ofNat_add]) hj ?_
  have htake : bs.take (k + 1) = bs.take k ++ [bs[k]!] := by
    rw [List.take_add_one, List.getElem?_eq_getElem hk]; simp [hk]
  have hlen : (bs.take k).length = k := by simp; omega
  refine ⟨⟨fun x hx => by simp [setLocal, hx, hk0.locals x hx], hk0.memaddrs, hk0.be, hk0.base, hk0.ffi, hk0.code⟩,
    k + 1, by omega, by simp [setLocal], ?_, ?_, ?_, ?_⟩
  · rw [htake]
    have := memBytesAt_snoc (b := bs[k]!) hd (by rw [hlen]; exact hroom)
      (Nat.lt_of_le_of_lt (List.length_take_le k bs) (by have := hpre.hshort; omega))
    rw [hlen] at this
    exact this
  · exact memBytesAt_putByte_other hs fun i hi e => hpre.hapart k i hk hi e.symm
  · intro a ha
    rw [load_putByte_diff _ _ _ _ _ _ (ha k hk)]
    exact hb' a ha
  · intro w hout
    simp only [putByte]
    rw [if_neg (hout k hk)]
    exact hw w hout

theorem copyInv_clock (j : String) (D S : Word) (bs : List (BitVec 8)) (s0 : PancakeState σ) :
    Safe.ClockFree (CopyInv j D S bs s0) :=
  fun _ _ ⟨hk, rest⟩ => ⟨{ hk with }, rest⟩

theorem copyPost_clock (j : String) (D : Word) (bs : List (BitVec 8)) (s0 : PancakeState σ) :
    Safe.ClockFree (CopyPost j D bs s0) :=
  fun _ _ ⟨hk, rest⟩ => ⟨{ hk with }, rest⟩

/-- What the copy's loop asks holds. -/
theorem copy_vc {j : String} {dst src len : PancakeExp} {D S : Word} {bs : List (BitVec 8)}
    {s0 : PancakeState σ} (hpre : CopyPre j dst src len D S bs s0) :
    vc (copyA j dst src len D S bs s0) (CopyPost j D bs s0) := by
  refine ⟨trivial, copyInv_clock _ _ _ _ _, ⟨trivial, trivial⟩, fun t ⟨hk0, k, hk, hj, hd, hs, hb', hw⟩ => ?_⟩
  have hl : ∀ x, ¬ (x = j) → t.locals x = s0.locals x := fun x hx => hk0.locals x hx
  have hL := (eval_noLoad hl hk0.base len hpre.hnoLoad.2.2 hpre.havoids.2.2).trans hpre.hlen
  have hsh := hpre.hshort
  simp only [eval, hj, hL, WpBytes.signedLt_small (a := k) (b := bs.length) (by omega) (by omega)]
  by_cases hkl : k < bs.length
  · simp only [hkl, decide_true, if_true, show ((1 : Word) = 0) = False by decide, if_false]
    exact copy_step hpre hk0 hkl hj hd hs hb' hw
  · have hkw : k = bs.length := by omega
    subst hkw
    simp only [hkl, decide_false, Bool.false_eq_true, if_false, if_true]
    rw [List.take_length] at hd
    exact ⟨hk0, hj, hd, hb', hw⟩

/-- The copy as it lowers, `k` after it. -/
def copyP (j : String) (dst src len : PancakeExp) (k : PancakeProg) : PancakeProg :=
  .seq (.assign j (.const 0)) (.seq (.while_ (.cmp .less (.var j) len) (copyBody (σ := Unit) j dst src).erase) k)

theorem copy_lowerK {j : String} {dst src len : Syntax.PExpr} {DST SRC LEN : PancakeExp}
    (hd : Lower.lowerExp dst = some DST) (hs : Lower.lowerExp src = some SRC) (hl : Lower.lowerExp len = some LEN)
    (k : PancakeProg) : Block.lowerK (SessionStore.copy j dst src len) k = some (copyP j DST SRC LEN k) := by
  simp [SessionStore.copy, SessionStore.copyLoop, SessionStore.inc, Block.lowerK, Lower.lowerStmt1,
    Lower.lowerStmtsFold, Lower.lowerExp, Syntax.eAdd, Syntax.eLt, Syntax.n, Syntax.v, hd, hs, hl, copyP, copyBody,
    AProg.erase]

/-- **The session's copy, then what follows**: the octets `bs` at `S` copied to `D`, `j` past them. -/
theorem copy_then (o : Oracle σ) {j : String} {dst src len : PancakeExp} {k : PancakeProg}
    {P P' Q : PancakeState σ → Prop} {R : Ret}
    (hpre : ∀ s, P s → ∃ D S bs, CopyPre j dst src len D S bs s ∧ ∀ u, CopyPost j D bs s u → P' u)
    (hk : SafeR o P' k R Q) : SafeR o P (copyP j dst src len k) R Q := by
  intro s0 hs0
  obtain ⟨D, S, bs, hpre, hnext⟩ := hpre s0 hs0
  refine (?_ : SafeR o (fun s => s = s0) _ R Q) s0 rfl
  obtain ⟨v, hv⟩ := hpre.hj
  refine seq (M := CopyInv j D S bs s0) (assign fun s hs => ⟨0, v, rfl, hs ▸ hv, ?_⟩) ?_
    (copyInv_clock j D S bs s0)
  · subst hs
    exact ⟨⟨fun x hx => by simp [setLocal, hx], rfl, rfl, rfl, rfl, rfl⟩, 0, Nat.zero_le _, by simp [setLocal],
      by simp [memBytesAt], hpre.hbytes, fun _ _ => rfl, fun _ _ => rfl⟩
  have hw : Safe.Safe o (CopyInv j D S bs s0) (.while_ (.cmp .less (.var j) len) (copyBody (σ := σ) j dst src).erase)
      (CopyPost j D bs s0) :=
    wp_sound o (.while_ (CopyInv j D S bs s0) (.cmp .less (.var j) len) (copyBody j dst src)) _
      (copyPost_clock j D bs s0) (copy_vc hpre).2
  exact seq (ofSafe R rfl hw) (conseq hk (fun u hu => hnext u hu) (fun _ _ h => h) (fun _ h => h))
    (copyPost_clock j D bs s0)

/-- `keptIn` of a word in range. -/
theorem frag_keptIn (o : Oracle σ) {e : Syntax.PExpr} {E : PancakeExp} (he : Lower.lowerExp e = some E) {hi : Nat}
    (hhi : hi < 2 ^ 63) {P : Assn σ} (hP : Safe.ClockFree P)
    (h : ∀ s, P s → ∃ k, k ≤ hi ∧ eval s E = some (BitVec.ofNat 64 k)) : Frag o [SessionStore.keptIn e hi] P P := by
  intro k R Q _ hk
  exact ⟨.seq (SessionRun.keptG E hi) k, lowerK_one (SessionRun.keptIn_lower he hi) rfl k,
    seq (SessionRun.keptG_pass o R hhi h) hk hP⟩

theorem div10_word (x : Nat) (hx : x < 2 ^ 32) :
    (BitVec.ofNat 64 x * 3435973837) >>> 35 = BitVec.ofNat 64 (x / 10) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_mul, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  rw [show (3435973837 : Word).toNat = 3435973837 from rfl]
  rw [Nat.mod_eq_of_lt (by omega : x < 2 ^ 64), Nat.mod_eq_of_lt (by omega : x * 3435973837 < 2 ^ 64),
    Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt (by omega : x / 10 < 2 ^ 64)]
  exact Div10.div10_of_lt x (by omega)

def div10E (e : PancakeExp) : PancakeExp := .shiftR (.mul e (.const 3435973837)) (.const 35)

theorem div10E_eval {t : PancakeState σ} {e : PancakeExp} {x : Nat} (hx : x < 2 ^ 32)
    (he : eval t e = some (BitVec.ofNat 64 x)) : eval t (div10E e) = some (BitVec.ofNat 64 (x / 10)) := by
  simp only [div10E, eval, he]
  rw [show (35 : Word).toNat = 35 from rfl]
  simp only [show (35 ≠ 0 && 35 ≥ 64) = false by decide, Bool.false_eq_true, if_false]
  rw [div10_word x hx]

/-- The digit `x` writes last, as the session computes it. -/
theorem digit_word (x : Nat) (hx : x < 2 ^ 32) :
    (48 : Word) + (BitVec.ofNat 64 x - BitVec.ofNat 64 (x / 10) * 10) = BitVec.ofNat 64 (48 + x % 10) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_mul, BitVec.toNat_ofNat]
  rw [show (48 : Word).toNat = 48 from rfl, show (10 : Word).toNat = 10 from rfl]
  rw [Nat.mod_eq_of_lt (by omega : x < 2 ^ 64), Nat.mod_eq_of_lt (by omega : x / 10 < 2 ^ 64),
    Nat.mod_eq_of_lt (by omega : x / 10 * 10 < 2 ^ 64), Nat.mod_eq_of_lt (by omega : 48 + x % 10 < 2 ^ 64)]
  omega

/-- The write loop's octet: one place back, its digit stored, the number divided. -/
def wrBody (t q off : String) (dst : PancakeExp) : AProg σ :=
  .seq (.assign q (.op .sub (.var q) (.const 1)))
  (.seq (SessionRun.keptA (.var q) 9)
  (.seq (.storeByte (.op .add (.op .add dst (.var off)) (.var q))
      (.op .add (.const 48) (.op .sub (.var t) (.mul (div10E (.var t)) (.const 10)))))
    (.assign t (div10E (.var t)))))

/-- What the write loop keeps of the state `s1` it starts in: every local but `t` and `q`, the
memory's domain, order, base, world and code. -/
structure WrKept (t q : String) (s1 u : PancakeState σ) : Prop where
  locals : ∀ y, y ≠ t → y ≠ q → u.locals y = s1.locals y
  memaddrs : u.memaddrs = s1.memaddrs
  be : u.be = s1.be
  base : u.baseAddr = s1.baseAddr
  ffi : u.ffi = s1.ffi
  code : u.code = s1.code

theorem wrKept_clock {t q : String} {s1 u : PancakeState σ} (h : WrKept t q s1 u) (k : Nat) :
    WrKept t q s1 { u with clock := k } := { h with }

/-- The write loop after the places from `q` on: their digits at `D0`, every other octet and word
as it was. -/
def WrInv (t q : String) (x : Nat) (D0 : Word) (s1 u : PancakeState σ) : Prop :=
  WrKept t q s1 u ∧ ∃ k, k ≤ numDigits x ∧ u.locals q = some (BitVec.ofNat 64 k) ∧
    u.locals t = some (BitVec.ofNat 64 (x / 10 ^ (numDigits x - k))) ∧
    (∀ i, k ≤ i → i < numDigits x →
      memLoadByte u.memory u.memaddrs u.be (D0 + BitVec.ofNat 64 i) = (CommandSpec.decimal x)[i]?) ∧
    (∀ a, (∀ i, i < numDigits x → a ≠ D0 + BitVec.ofNat 64 i) →
      memLoadByte u.memory u.memaddrs u.be a = memLoadByte s1.memory s1.memaddrs s1.be a) ∧
    (∀ w, (∀ i, i < numDigits x → w ≠ byteAlign (D0 + BitVec.ofNat 64 i)) → u.memory w = s1.memory w)

/-- **A digit written**: the write loop goes on. -/
theorem wr_step {t q off : String} {dst : PancakeExp} {x : Nat} {D offv : Word} {s1 u : PancakeState σ}
    {R : Ret}
    (hx : x < 2 ^ 32) (htq : t ≠ q) (hot : off ≠ t) (hoq : off ≠ q)
    (hdN : NoLoad dst) (hdA : ExpAvoids (fun y => y = t ∨ y = q) dst) (hd1 : eval s1 dst = some D)
    (hoff1 : s1.locals off = some offv)
    (hroom : ∀ i, i < numDigits x → s1.memaddrs (byteAlign (D + offv + BitVec.ofNat 64 i)) = true)
    (hkp : WrKept t q s1 u) {k : Nat} (hk : 0 < k) (hkN : k ≤ numDigits x)
    (hq : u.locals q = some (BitVec.ofNat 64 k))
    (ht : u.locals t = some (BitVec.ofNat 64 (x / 10 ^ (numDigits x - k))))
    (hw : ∀ i, k ≤ i → i < numDigits x →
      memLoadByte u.memory u.memaddrs u.be (D + offv + BitVec.ofNat 64 i) = (CommandSpec.decimal x)[i]?)
    (ho : ∀ a, (∀ i, i < numDigits x → a ≠ D + offv + BitVec.ofNat 64 i) →
      memLoadByte u.memory u.memaddrs u.be a = memLoadByte s1.memory s1.memaddrs s1.be a)
    (hwd : ∀ w, (∀ i, i < numDigits x → w ≠ byteAlign (D + offv + BitVec.ofNat 64 i)) → u.memory w = s1.memory w) :
    wpR (wrBody t q off dst) R (WrInv t q x (D + offv) s1) u := by
  have hN := numDigits_le_ten x hx
  obtain ⟨T, hT⟩ : ∃ T, T = x / 10 ^ (numDigits x - k) := ⟨_, rfl⟩
  rw [← hT] at ht
  have hTx : T < 2 ^ 32 := by rw [hT]; exact Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hx
  -- one place back
  refine SessionCheck.wpR_seq (M := fun u1 => u1 = { u with locals := setLocal u.locals q (BitVec.ofNat 64 (k - 1)) })
    (SessionCheck.wpR_assign (by simp only [eval, hq]; exact congrArg some (SessionCheck.sub_small k 1 hk (by omega)))
      hq rfl) ?_
  rintro u1 rfl
  refine SessionCheck.wpR_seq (M := fun u2 => u2 = { u with locals := setLocal u.locals q (BitVec.ofNat 64 (k - 1)) })
    (SessionRun.keptA_wp (k := k - 1) (by decide) (by omega) (by simp [eval, setLocal]) rfl) ?_
  rintro u2 rfl
  have hl : ∀ y, ¬ (y = t ∨ y = q) → ({ u with locals := setLocal u.locals q (BitVec.ofNat 64 (k - 1)) } :
      PancakeState σ).locals y = s1.locals y := fun y hy => by
    simp only [not_or] at hy
    simp [setLocal, hy.2, hkp.locals y hy.1 hy.2]
  have hD : eval ({ u with locals := setLocal u.locals q (BitVec.ofNat 64 (k - 1)) } : PancakeState σ) dst = some D :=
    (eval_noLoad hl hkp.base dst hdN hdA).trans hd1
  have hoffu : u.locals off = some offv := (hkp.locals off hot hoq).trans hoff1
  have hA : eval ({ u with locals := setLocal u.locals q (BitVec.ofNat 64 (k - 1)) } : PancakeState σ)
      (.op .add (.op .add dst (.var off)) (.var q)) = some (D + offv + BitVec.ofNat 64 (k - 1)) := by
    simp only [eval, hD]
    simp [setLocal, hoq, hoffu]
  have hTv : eval ({ u with locals := setLocal u.locals q (BitVec.ofNat 64 (k - 1)) } : PancakeState σ)
      (.op .add (.const 48) (.op .sub (.var t) (.mul (div10E (.var t)) (.const 10)))) =
      some (BitVec.ofNat 64 (48 + T % 10)) := by
    have htu : setLocal u.locals q (BitVec.ofNat 64 (k - 1)) t = some (BitVec.ofNat 64 T) := by
      simp [setLocal, htq, ht]
    have hdv := div10E_eval (t := ({ u with locals := setLocal u.locals q (BitVec.ofNat 64 (k - 1)) } :
      PancakeState σ)) (e := .var t) hTx htu
    simp only [eval] at hdv ⊢
    simp only [htu] at hdv ⊢
    rw [hdv]
    simp only
    rw [digit_word T hTx]
  have hroomu : u.memaddrs (byteAlign (D + offv + BitVec.ofNat 64 (k - 1))) = true := by
    rw [hkp.memaddrs]; exact hroom (k - 1) (by omega)
  have hst : memStoreByte u.memory u.memaddrs u.be (D + offv + BitVec.ofNat 64 (k - 1))
      ((BitVec.ofNat 64 (48 + T % 10)).setWidth 8) =
      some (putByte u.memory u.be (D + offv + BitVec.ofNat 64 (k - 1)) (Decimal.digitByte (T % 10))) := by
    rw [setWidth_ofNat_8]; exact memStore_eq _ _ _ _ _ hroomu
  refine SessionCheck.wpR_seq (M := fun u3 => u3 = { u with
    locals := setLocal u.locals q (BitVec.ofNat 64 (k - 1))
    memory := putByte u.memory u.be (D + offv + BitVec.ofNat 64 (k - 1)) (Decimal.digitByte (T % 10)) }) ?_ ?_
  · show wp (.storeByte _ _) _ _
    simp only [wp, hA, hTv, hst]
  rintro u3 rfl
  have htu3 : setLocal u.locals q (BitVec.ofNat 64 (k - 1)) t = some (BitVec.ofNat 64 T) := by
    simp [setLocal, htq, ht]
  have hdv : ∀ m : Word → Word, eval ({ u with locals := setLocal u.locals q (BitVec.ofNat 64 (k - 1)), memory := m } :
      PancakeState σ) (div10E (.var t)) = some (BitVec.ofNat 64 (T / 10)) := fun m =>
    div10E_eval hTx htu3
  refine SessionCheck.wpR_assign (R := R) (hdv _) htu3 ?_
  have hreg : ∀ i, i < numDigits x → i ≠ k - 1 →
      D + offv + BitVec.ofNat 64 i ≠ D + offv + BitVec.ofNat 64 (k - 1) := fun i hi hne =>
    region_addr_inj _ i (k - 1) (by omega) (by omega) hne
  refine ⟨⟨fun y h1 h2 => ?_, hkp.memaddrs, hkp.be, hkp.base, hkp.ffi, hkp.code⟩, k - 1, by omega,
    by simp [setLocal, Ne.symm htq], ?_, fun i hi hiN => ?_, fun a ha => ?_, fun w hw' => ?_⟩
  · simp [setLocal, h1, h2, hkp.locals y h1 h2]
  · simp only [setLocal, if_true]
    congr 2
    rw [hT, Nat.div_div_eq_div_mul, ← Nat.pow_succ]
    congr 2
    omega
  · simp only
    by_cases hik : i = k - 1
    · subst hik
      rw [load_putByte_same _ _ _ _ _ hroomu, decimal_get x (k - 1) hiN, hT,
        show numDigits x - 1 - (k - 1) = numDigits x - k by omega]
    · rw [load_putByte_diff _ _ _ _ _ _ (hreg i hiN hik)]
      exact hw i (by omega) hiN
  · simp only
    rw [load_putByte_diff _ _ _ _ _ _ (ha (k - 1) (by omega))]
    exact ho a ha
  · simp only [putByte]
    rw [if_neg (hw' (k - 1) (by omega))]
    exact hwd w hw'

/-- The count's octet: the number divided, one digit more. -/
def cntBody (t n : String) : AProg σ :=
  .seq (.assign t (div10E (.var t))) (.assign n (.op .add (.var n) (.const 1)))

/-- The count after `c` digits: the number divided `c - 1` times. -/
def CntInv (t n : String) (x : Nat) (s1 u : PancakeState σ) : Prop :=
  WrKept t n s1 u ∧ u.memory = s1.memory ∧ ∃ c, 1 ≤ c ∧ c ≤ numDigits x ∧
    u.locals n = some (BitVec.ofNat 64 c) ∧ u.locals t = some (BitVec.ofNat 64 (x / 10 ^ (c - 1)))

/-- What the count leaves. -/
def CntPost (t n : String) (x : Nat) (s1 u : PancakeState σ) : Prop :=
  WrKept t n s1 u ∧ u.memory = s1.memory ∧ u.locals n = some (BitVec.ofNat 64 (numDigits x)) ∧
    ∃ v, u.locals t = some v

def cntA (t n : String) (x : Nat) (s1 : PancakeState σ) : AProg σ :=
  .while_ (CntInv t n x s1) (.cmp .less (.const 9) (.var t)) (cntBody t n)

theorem cnt_vc {t n : String} (htn : t ≠ n) {x : Nat} (hx : x < 2 ^ 32) (s1 : PancakeState σ) :
    vc (cntA t n x s1) (CntPost t n x s1) := by
  refine ⟨fun _ k ⟨hk, rest⟩ => ⟨wrKept_clock hk k, rest⟩, ⟨trivial, trivial⟩,
    fun u ⟨hkp, hm, c, hc1, hcN, hn, ht⟩ => ?_⟩
  have hN := numDigits_le_ten x hx
  have hq : x / 10 ^ (c - 1) < 2 ^ 32 := Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hx
  simp only [eval, ht]
  rw [show (9 : Word) = BitVec.ofNat 64 9 from rfl,
      WpBytes.signedLt_small (a := 9) (b := x / 10 ^ (c - 1)) (by decide) (by omega)]
  by_cases hg : 9 < x / 10 ^ (c - 1)
  · simp only [hg, decide_true, if_true, show ((1 : Word) = 0) = False by decide, if_false]
    have hcN' : c < numDigits x := by
      refine Classical.byContradiction fun h => ?_
      have : c = numDigits x := by omega
      subst this
      have := quot_lt_ten x
      omega
    refine wp_seq
        (M := fun u1 => u1 = { u with locals := setLocal u.locals t (BitVec.ofNat 64 (x / 10 ^ (c - 1) / 10)) })
      (wp_assign (div10E_eval hq ht) ht rfl) ?_
    rintro u1 rfl
    refine wp_assign (val := BitVec.ofNat 64 (c + 1)) (old := BitVec.ofNat 64 c)
      (by simp [eval, setLocal, Ne.symm htn, hn, BitVec.ofNat_add])
      (by simp [setLocal, Ne.symm htn, hn]) ⟨⟨fun y h1 h2 => by simp [setLocal, h1, h2, hkp.locals y h1 h2],
        hkp.memaddrs, hkp.be, hkp.base, hkp.ffi, hkp.code⟩, hm, c + 1, by omega, by omega, by simp [setLocal], ?_⟩
    simp only [setLocal, htn, if_false, if_true, Nat.add_sub_cancel]
    rw [Nat.div_div_eq_div_mul, ← Nat.pow_succ, show (c - 1).succ = c by omega]
  · simp only [hg, decide_false, Bool.false_eq_true, if_false, if_true]
    exact ⟨hkp, hm, by rw [← count_exit hc1 hcN (by omega)]; exact hn, _, ht⟩

/-- The write loop, as it lowers, its invariant carried. -/
def wrA (t q off : String) (dst : PancakeExp) (x : Nat) (D0 : Word) (s1 : PancakeState σ) : AProg σ :=
  .while_ (WrInv t q x D0 s1) (.cmp .less (.const 0) (.var q)) (wrBody t q off dst)

/-- `digits`, as it lowers, `k` after it. -/
def digitsP (n t q off : String) (dst X : PancakeExp) (room : Nat) (k : PancakeProg) : PancakeProg :=
  .dec n (.const 1) (.dec t X (.seq (.while_ (.cmp .less (.const 9) (.var t)) (cntBody (σ := Unit) t n).erase)
    (.seq (SessionRun.keptG (.var off) (room - 10)) (.seq (.assign t X) (.dec q (.var n)
      (.seq (.while_ (.cmp .less (.const 0) (.var q)) (wrBody (σ := Unit) t q off dst).erase)
        (.seq (.assign off (.op .add (.var off) (.var n))) (.seq (SessionRun.keptG (.var off) room) k))))))))

theorem digits_lowerK {p off : String} {dst x : Syntax.PExpr} {DST X : PancakeExp} {room : Nat}
    (hd : Lower.lowerExp dst = some DST) (hx : Lower.lowerExp x = some X) (k : PancakeProg) :
    Block.lowerK (SessionStore.digits p dst off x room) k =
      some (digitsP (p ++ "n") (p ++ "t") (p ++ "q") off DST X room k) := by
  have k1 := SessionRun.keptIn_lower (e := Syntax.v off) rfl (room - 10)
  have k2 := SessionRun.keptIn_lower (e := Syntax.v off) rfl room
  have k3 := SessionRun.keptIn_lower (e := Syntax.v (p ++ "q")) rfl 9
  have hw1 : Lower.lowerStmt1 (.while (Syntax.eLt (Syntax.n 9) (Syntax.v (p ++ "t")))
      [.assign (p ++ "t") (SessionStore.div10 (Syntax.v (p ++ "t"))), SessionStore.inc (p ++ "n")]) =
      some (.while_ (.cmp .less (.const 9) (.var (p ++ "t"))) (cntBody (σ := Unit) (p ++ "t") (p ++ "n")).erase) := by
    rfl
  have hbody : Lower.lowerStmtsFold
      [.assign (p ++ "q") (Syntax.eSub (Syntax.v (p ++ "q")) (Syntax.n 1)), SessionStore.keptIn (Syntax.v (p ++ "q")) 9,
       .storeb (Syntax.eAdd (Syntax.eAdd dst (Syntax.v off)) (Syntax.v (p ++ "q")))
         (Syntax.eAdd (Syntax.n 48) (Syntax.eSub (Syntax.v (p ++ "t"))
           (Syntax.eMul (SessionStore.div10 (Syntax.v (p ++ "t"))) (Syntax.n 10)))),
       .assign (p ++ "t") (SessionStore.div10 (Syntax.v (p ++ "t")))] =
      some (wrBody (σ := Unit) (p ++ "t") (p ++ "q") off DST).erase := by
    have hs : Lower.lowerStmt1 (.storeb (Syntax.eAdd (Syntax.eAdd dst (Syntax.v off)) (Syntax.v (p ++ "q")))
         (Syntax.eAdd (Syntax.n 48) (Syntax.eSub (Syntax.v (p ++ "t"))
           (Syntax.eMul (SessionStore.div10 (Syntax.v (p ++ "t"))) (Syntax.n 10))))) =
        some (.storeByte (.op .add (.op .add DST (.var off)) (.var (p ++ "q")))
          (.op .add (.const 48) (.op .sub (.var (p ++ "t")) (.mul (div10E (.var (p ++ "t"))) (.const 10))))) := by
      simp [Lower.lowerStmt1, Lower.lowerExp, hd, Syntax.eAdd, Syntax.eSub, Syntax.eMul, Syntax.n, Syntax.v,
        SessionStore.div10, div10E]
    exact Block.fold_cons rfl rfl (by simp) (Block.fold_cons k3 rfl (by simp) (Block.fold_cons hs rfl (by simp) rfl))
  have hw2 : Lower.lowerStmt1 (.while (Syntax.eLt (Syntax.n 0) (Syntax.v (p ++ "q")))
      [.assign (p ++ "q") (Syntax.eSub (Syntax.v (p ++ "q")) (Syntax.n 1)), SessionStore.keptIn (Syntax.v (p ++ "q")) 9,
       .storeb (Syntax.eAdd (Syntax.eAdd dst (Syntax.v off)) (Syntax.v (p ++ "q")))
         (Syntax.eAdd (Syntax.n 48) (Syntax.eSub (Syntax.v (p ++ "t"))
           (Syntax.eMul (SessionStore.div10 (Syntax.v (p ++ "t"))) (Syntax.n 10)))),
       .assign (p ++ "t") (SessionStore.div10 (Syntax.v (p ++ "t")))]) =
      some (.while_ (.cmp .less (.const 0) (.var (p ++ "q"))) (wrBody (σ := Unit) (p ++ "t") (p ++ "q") off DST).erase) := by
    simp only [Lower.lowerStmt1, hbody]
    rfl
  have hx' : Lower.lowerStmt1 (.assign (p ++ "t") x) = some (.assign (p ++ "t") X) := by simp [Lower.lowerStmt1, hx]
  unfold SessionStore.digits
  exact lowerK_dec rfl (lowerK_dec hx (lowerK_cons hw1 rfl (lowerK_cons k1 rfl (lowerK_cons hx' rfl
    (lowerK_dec rfl (lowerK_cons hw2 rfl (lowerK_cons rfl rfl (lowerK_cons k2 rfl rfl))))))))

/-- What the write loop leaves: every digit at `D0`, every other octet and word as it was. -/
def WrPost (t q : String) (x : Nat) (D0 : Word) (s1 u : PancakeState σ) : Prop :=
  WrKept t q s1 u ∧ (∃ v, u.locals q = some v) ∧ (∃ v, u.locals t = some v) ∧
    (∀ i, i < numDigits x →
      memLoadByte u.memory u.memaddrs u.be (D0 + BitVec.ofNat 64 i) = (CommandSpec.decimal x)[i]?) ∧
    (∀ a, (∀ i, i < numDigits x → a ≠ D0 + BitVec.ofNat 64 i) →
      memLoadByte u.memory u.memaddrs u.be a = memLoadByte s1.memory s1.memaddrs s1.be a) ∧
    (∀ w, (∀ i, i < numDigits x → w ≠ byteAlign (D0 + BitVec.ofNat 64 i)) → u.memory w = s1.memory w)

theorem wrPost_clock (t q : String) (x : Nat) (D0 : Word) (s1 : PancakeState σ) :
    Safe.ClockFree (WrPost t q x D0 s1) := fun _ k ⟨hk, rest⟩ => ⟨wrKept_clock hk k, rest⟩

theorem wr_vc {t q off : String} {dst : PancakeExp} {x : Nat} {D offv : Word} {s1 : PancakeState σ}
    {R : Ret}
    (hx : x < 2 ^ 32) (htq : t ≠ q) (hot : off ≠ t) (hoq : off ≠ q)
    (hdN : NoLoad dst) (hdA : ExpAvoids (fun y => y = t ∨ y = q) dst) (hd1 : eval s1 dst = some D)
    (hoff1 : s1.locals off = some offv)
    (hroom : ∀ i, i < numDigits x → s1.memaddrs (byteAlign (D + offv + BitVec.ofNat 64 i)) = true) :
    vcR (wrA t q off dst x (D + offv) s1) R (WrPost t q x (D + offv) s1) := by
  have hN := numDigits_le_ten x hx
  refine ⟨fun _ k ⟨hk, rest⟩ => ⟨wrKept_clock hk k, rest⟩, by simp [vcR, wrBody, SessionRun.keptA],
    fun u ⟨hkp, k, hkN, hq, ht, hw, ho, hwd⟩ => ?_⟩
  simp only [eval, hq]
  rw [show (0 : Word) = BitVec.ofNat 64 0 from rfl,
    WpBytes.signedLt_small (a := 0) (b := k) (by decide) (by omega)]
  by_cases hk : 0 < k
  · simp only [hk, decide_true, if_true, show ((1 : Word) = BitVec.ofNat 64 0) = False by decide, if_false]
    exact wr_step hx htq hot hoq hdN hdA hd1 hoff1 hroom hkp hk hkN hq ht hw ho hwd
  · obtain rfl : k = 0 := by omega
    simp only [Nat.lt_irrefl, decide_false, Bool.false_eq_true, if_false, if_true]
    exact ⟨hkp, ⟨_, hq⟩, ⟨_, ht⟩, fun i hi => hw i (Nat.zero_le _) hi, ho, hwd⟩

/-- What `digits` asks: `x`, below 2^32, from `X`, and `D` from `dst`, neither reading the counters,
`dst` reading no memory; the offset `ov` in `off`, ten places of room before `room`, every digit's word
addressable; the names apart. -/
structure DigPre (n t q off : String) (dst X : PancakeExp) (room x ov : Nat) (D : Word)
    (s : PancakeState σ) : Prop where
  nt : n ≠ t
  nq : n ≠ q
  tq : t ≠ q
  on : off ≠ n
  ot : off ≠ t
  oq : off ≠ q
  hx : x < 2 ^ 32
  hroom : room < 2 ^ 63
  hov : ov + 10 ≤ room
  hoff : s.locals off = some (BitVec.ofNat 64 ov)
  hX : eval s X = some (BitVec.ofNat 64 x)
  hXav : ExpAvoids (fun y => y = n ∨ y = t ∨ y = q) X
  hdst : eval s dst = some D
  hdstN : NoLoad dst
  hdstA : ExpAvoids (fun y => y = n ∨ y = t ∨ y = q) dst
  hroom8 : ∀ i, i < numDigits x → s.memaddrs (byteAlign (D + BitVec.ofNat 64 ov + BitVec.ofNat 64 i)) = true

/-- What it leaves: `x`'s digits at `D + ov`, `off` past them, every other octet, word and local but the
counters as they were. -/
structure DigPost (n t q off : String) (x ov : Nat) (D : Word) (s u : PancakeState σ) : Prop where
  locals : ∀ y, y ≠ n → y ≠ t → y ≠ q → y ≠ off → u.locals y = s.locals y
  hoff : u.locals off = some (BitVec.ofNat 64 (ov + numDigits x))
  memaddrs : u.memaddrs = s.memaddrs
  be : u.be = s.be
  base : u.baseAddr = s.baseAddr
  ffi : u.ffi = s.ffi
  code : u.code = s.code
  digits : ∀ i, i < numDigits x → memLoadByte u.memory u.memaddrs u.be
    (D + BitVec.ofNat 64 ov + BitVec.ofNat 64 i) = (CommandSpec.decimal x)[i]?
  bytes : ∀ a, (∀ i, i < numDigits x → a ≠ D + BitVec.ofNat 64 ov + BitVec.ofNat 64 i) →
    memLoadByte u.memory u.memaddrs u.be a = memLoadByte s.memory s.memaddrs s.be a
  words : ∀ w, (∀ i, i < numDigits x → w ≠ byteAlign (D + BitVec.ofNat 64 ov + BitVec.ofNat 64 i)) →
    u.memory w = s.memory w

/-- Between the loops: the digits counted, the number again in `t`. -/
structure DigMid (n t q : String) (x : Nat) (s v : PancakeState σ) : Prop where
  locals : ∀ y, y ≠ n → y ≠ t → y ≠ q → v.locals y = s.locals y
  memory : v.memory = s.memory
  memaddrs : v.memaddrs = s.memaddrs
  be : v.be = s.be
  base : v.baseAddr = s.baseAddr
  ffi : v.ffi = s.ffi
  code : v.code = s.code
  hn : v.locals n = some (BitVec.ofNat 64 (numDigits x))
  ht : v.locals t = some (BitVec.ofNat 64 x)

theorem cntPost_clock (t n : String) (x : Nat) (s1 : PancakeState σ) : Safe.ClockFree (CntPost t n x s1) :=
  fun _ k ⟨hk, hm, rest⟩ => ⟨wrKept_clock hk k, hm, rest⟩

theorem digMid_clock (n t q : String) (x : Nat) (s : PancakeState σ) : Safe.ClockFree (DigMid n t q x s) :=
  fun _ _ h => { h with }

theorem digPost_clock (n t q off : String) (x ov : Nat) (D : Word) (s : PancakeState σ) :
    Safe.ClockFree (DigPost n t q off x ov D s) :=
  fun _ _ h => { h with }

/-- **The session's decimal digits, then whatever follows**: `x`'s digits written at `D + ov`, `off`
moved past them, the counters declared for what follows and their ends left to it. -/
theorem digits_then (o : Oracle σ) {n t q off : String} {dst X : PancakeExp} {room : Nat} {k : PancakeProg}
    {P P' Q : PancakeState σ → Prop} {R : Ret}
    (hpre : ∀ s, P s → ∃ x ov D, DigPre n t q off dst X room x ov D s ∧
      ∀ u, DigPost n t q off x ov D s u → P' u)
    (hQ : ∀ u y v, Q u → y ∈ [n, t, q] → Q (restore u y v))
    (hk : SafeR o P' k R Q) : SafeR o P (digitsP n t q off dst X room k) R Q := by
  intro s hs
  obtain ⟨x, ov, D, hd, hnext⟩ := hpre s hs
  have hN := numDigits_le_ten x hd.hx
  have hroom := hd.hroom
  have hov := hd.hov
  refine (?_ : SafeR o (fun u => u = s) _ R Q) s rfl
  -- the count
  obtain ⟨s1, hs1⟩ : ∃ s1 : PancakeState σ, s1 = { s with locals := setLocal s.locals n 1 } := ⟨_, rfl⟩
  obtain ⟨s2, hs2⟩ : ∃ s2 : PancakeState σ,
      s2 = { s1 with locals := setLocal s1.locals t (BitVec.ofNat 64 x) } := ⟨_, rfl⟩
  have hl2 : ∀ y, y ≠ n → y ≠ t → s2.locals y = s.locals y := fun y h1 h2 => by
    simp [hs2, hs1, setLocal, h1, h2]
  refine dec (P' := fun u => u = s1) (Q' := Q) (fun u hu => ⟨1, rfl, by rw [hu, hs1]⟩) ?_
    (fun _ u _ hq => hQ u n _ hq (by simp))
  refine dec (P' := fun u => u = s2) (Q' := Q) (fun u hu => ⟨BitVec.ofNat 64 x, ?_, by rw [hu, hs2]⟩) ?_
    (fun _ u _ hq => hQ u t _ hq (by simp))
  · rw [hu]
    have ha : Agree (fun y => y = n ∨ y = t ∨ y = q) s s1 :=
      ⟨fun y hy => by simp only [not_or] at hy; simp [hs1, setLocal, hy.1], fun _ h => by simp [hs1, h],
        fun _ _ => by simp [hs1], by simp [hs1], by simp [hs1], by simp [hs1], by simp [hs1], by simp [hs1]⟩
    exact eval_agree' ha hd.hXav hd.hX
  have hcnt : Safe.Safe o (fun u => u = s2) (.while_ (.cmp .less (.const 9) (.var t)) (cntBody (σ := Unit) t n).erase)
      (CntPost t n x s2) := by
    refine Safe.conseq (wp_sound o (cntA t n x s2) (CntPost t n x s2) (cntPost_clock t n x s2)
      (cnt_vc hd.nt.symm hd.hx s2)) (fun u hu => ?_) (fun _ h => h)
    rw [hu]
    refine ⟨⟨fun _ _ _ => rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl, 1, Nat.le_refl _, numDigits_pos x,
      by simp [hs2, hs1, setLocal, hd.nt], by simp [hs2, setLocal]⟩
  refine seq (ofSafe R rfl hcnt) ?_ (cntPost_clock t n x s2)
  have hoff2 : ∀ u, CntPost t n x s2 u → u.locals off = some (BitVec.ofNat 64 ov) := fun u hu =>
    (hu.1.locals off hd.ot hd.on).trans ((hl2 off hd.on hd.ot).trans hd.hoff)
  -- the room before the digits
  refine seq (SessionRun.keptG_pass o R (by omega) fun u hu => ⟨ov, by omega, hoff2 u hu⟩) ?_
    (cntPost_clock t n x s2)
  -- the number again
  refine seq (M := DigMid n t q x s) (assign fun u hu => ?_) ?_ (digMid_clock n t q x s)
  · obtain ⟨hkp, hm, hn, ⟨tv, ht⟩⟩ := hu
    have ha : Agree (fun y => y = n ∨ y = t ∨ y = q) s { u with clock := s.clock } :=
      ⟨fun y hy => by simp only [not_or] at hy; exact (hkp.locals y hy.2.1 hy.1).trans (hl2 y hy.1 hy.2.1),
        fun a h => by simp [hkp.memaddrs, hs2, hs1, h], fun _ _ => by simp [hm, hs2, hs1],
        by simp [hkp.be, hs2, hs1], rfl, by simp [hkp.ffi, hs2, hs1], by simp [hkp.base, hs2, hs1],
        by simp [hkp.code, hs2, hs1]⟩
    have hX : eval u X = some (BitVec.ofNat 64 x) := by
      have := eval_agree' ha hd.hXav hd.hX
      rwa [Safe.eval_clock] at this
    refine ⟨BitVec.ofNat 64 x, tv, hX, ht, fun y h1 h2 h3 => ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, by simp [setLocal]⟩
    · simp [setLocal, h2, hkp.locals y h2 h1, hl2 y h1 h2]
    · simp [hm, hs2, hs1]
    · simp [hkp.memaddrs, hs2, hs1]
    · simp [hkp.be, hs2, hs1]
    · simp [hkp.base, hs2, hs1]
    · simp [hkp.ffi, hs2, hs1]
    · simp [hkp.code, hs2, hs1]
    · simp [setLocal, hd.nt, hn]
  -- the place of the last digit
  refine dec (P' := fun v => DigMid n t q x s v ∧ v.locals q = some (BitVec.ofNat 64 (numDigits x))) (Q' := Q)
    (fun v hv => ⟨_, hv.hn, ⟨fun y h1 h2 h3 => by simp [setLocal, h3, hv.locals y h1 h2 h3], hv.memory,
      hv.memaddrs, hv.be, hv.base, hv.ffi, hv.code, by simp [setLocal, hd.nq, hv.hn],
      by simp [setLocal, hd.tq, hv.ht]⟩, by simp [setLocal]⟩) ?_ (fun _ u _ hq => hQ u q _ hq (by simp))
  -- the digits written
  have hdA : ExpAvoids (fun y => y = t ∨ y = q) dst :=
    SessionCheck.avoids_mono (fun y hy => Or.inr hy) dst hd.hdstA
  refine seq (M := fun w => ∃ v, (DigMid n t q x s v ∧ v.locals q = some (BitVec.ofNat 64 (numDigits x))) ∧
      WrPost t q x (D + BitVec.ofNat 64 ov) v w) (fun v hv => ?_) ?_
    (fun _ k ⟨v, hv, hw⟩ => ⟨v, hv, wrPost_clock t q x _ v _ k hw⟩)
  · obtain ⟨hm, hq⟩ := hv
    have hl : ∀ y, ¬ (y = n ∨ y = t ∨ y = q) → v.locals y = s.locals y := fun y hy => by
      simp only [not_or] at hy; exact hm.locals y hy.1 hy.2.1 hy.2.2
    have hD : eval v dst = some D := (eval_noLoad hl hm.base dst hd.hdstN hd.hdstA).trans hd.hdst
    have hoffv : v.locals off = some (BitVec.ofNat 64 ov) :=
      (hm.locals off hd.on hd.ot hd.oq).trans hd.hoff
    refine conseq (wpR_sound o (wrA t q off dst x (D + BitVec.ofNat 64 ov) v) R _ (wrPost_clock t q x _ v)
      (wr_vc hd.hx hd.tq hd.ot hd.oq hd.hdstN hdA hD hoffv (fun i hi => by rw [hm.memaddrs]; exact hd.hroom8 i hi)))
      (fun w hw => ?_) (fun _ _ h => h) (fun w hw => ⟨v, ⟨hm, hq⟩, hw⟩) v rfl
    subst hw
    refine ⟨⟨fun _ _ _ => rfl, rfl, rfl, rfl, rfl, rfl⟩, numDigits x, Nat.le_refl _, hq, by simp [hm.ht],
      fun i h1 h2 => absurd h2 (by omega), fun _ _ => rfl, fun _ _ => rfl⟩
  -- the place moved past them
  refine seq (M := DigPost n t q off x ov D s) (assign fun w ⟨v, ⟨hm, hq⟩, hw⟩ => ?_) ?_ (digPost_clock _ _ _ _ _ _ _ _)
  · obtain ⟨hkp, _, _, hdig, hbytes, hwords⟩ := hw
    have hoffw : w.locals off = some (BitVec.ofNat 64 ov) :=
      (hkp.locals off hd.ot hd.oq).trans ((hm.locals off hd.on hd.ot hd.oq).trans hd.hoff)
    have hnw : w.locals n = some (BitVec.ofNat 64 (numDigits x)) :=
      (hkp.locals n hd.nt hd.nq).trans hm.hn
    refine ⟨BitVec.ofNat 64 (ov + numDigits x), _, by simp [eval, hoffw, hnw, BitVec.ofNat_add], hoffw, ?_⟩
    refine ⟨fun y h1 h2 h3 h4 => ?_, by simp [setLocal], ?_, ?_, ?_, ?_, ?_, fun i hi => ?_, fun a ha => ?_,
      fun a ha => ?_⟩
    · simp [setLocal, h4, hkp.locals y h2 h3, hm.locals y h1 h2 h3]
    · simp [hkp.memaddrs, hm.memaddrs]
    · simp [hkp.be, hm.be]
    · simp [hkp.base, hm.base]
    · simp [hkp.ffi, hm.ffi]
    · simp [hkp.code, hm.code]
    · exact hdig i hi
    · simp only
      rw [hbytes a ha, hm.memory, hm.memaddrs, hm.be]
    · simp only
      rw [hwords a ha, hm.memory]
  -- the place checked, then what follows
  exact seq (SessionRun.keptG_pass o R hroom fun u hu => ⟨ov + numDigits x, by omega, hu.hoff⟩)
    (conseq hk (fun u hu => hnext u hu) (fun _ _ h => h) (fun _ h => h)) (digPost_clock _ _ _ _ _ _ _ _)

/-! ## The session's output -/

section Output

open SessionLayout

/-- Connection `c`'s output octets. -/
def outAt (b : Word) (c : Nat) : Word := SessionFrame.recordAt b c + BitVec.ofNat 64 cOut

/-- A word holding some of connection `c`'s output. -/
def OutWord (b : Word) (c : Nat) (w : Word) : Prop :=
  ∃ i, i < data ∧ w = byteAlign (outAt b c + BitVec.ofNat 64 i)

theorem outAt_eq (b : Word) (c : Nat) : outAt b c = b + BitVec.ofNat 64 (tableOff + c * connSlot + cOut) := by
  simp only [outAt, SessionFrame.recordAt, add_ofNat]

/-- Where the connections' records start, kept folded: unfolding it evaluates every text. -/
@[irreducible] def tOff : Nat := tableOff

theorem tOff_eq : tOff = tableOff := by unfold tOff; rfl

/-- The connections' records and the recovery's area end within the session's words. -/
theorem table_end : tOff + conns * connSlot + News.RecoverProg.size ≤ SessionLayout.size := by
  rw [tOff_eq]
  exact areas_disjoint.2.2.2.2.2.2.1

/-- The texts end below the records. -/
theorem texts_end : ownOff + ownTexts + textAt texts.length ≤ tOff := by
  rw [tOff_eq]
  exact areas_disjoint.2.2.2.2.1

/-- Recovery's area starts past the records: a projection of `areas_disjoint`, since `rfl` makes the kernel
evaluate both sides. -/
theorem rec_off : recOff = tOff + conns * connSlot := by
  rw [tOff_eq]
  exact areas_disjoint.2.2.2.2.2.2.2

theorem table_aligned : tOff % 8 = 0 := by
  rw [tOff_eq]
  exact offsets_aligned.2.2.2.2.2.2.2.2.2.2.1

/-- The layout's fixed numbers these proofs read. -/
structure Nums : Prop where
  slot : connSlot = 2712
  out : cOut = 2200
  outLen : cOutLen = 64
  dataLen : data = 512
  count : conns = 64
  own64 : 64 ≤ ownOff
  ownAl : ownOff % 8 = 0
  retAl : ownRet % 8 = 0
  ret8 : ownRet + 8 ≤ ownTexts

theorem nums : Nums := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ : connSlot = 2712 ∧ cOut = 2200 ∧ cOutLen = 64 ∧ data = 512 ∧
    conns = 64 ∧ 64 ≤ ownOff ∧ ownOff % 8 = 0 ∧ ownRet % 8 = 0 ∧ ownRet + 8 ≤ ownTexts := by decide +kernel
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

/-- Where the connections' records start, as a variable `T`. `omega` meeting `tOff` itself can reach the recursion
limit, so the facts are stated of `T`. -/
structure Lay (T : Nat) : Prop where
  eq : tOff = T
  aligned : T % 8 = 0
  room : T + 1904360 ≤ 4194304
  above : ownOff + ownTexts ≤ T

theorem lay : ∃ T, Lay T := by
  have h1 := table_end
  have h2 := size_fits
  have hA := texts_end
  have h4 := table_aligned
  have hn : conns = 64 ∧ connSlot = 2712 ∧ heapBytes = 4194304 ∧ News.RecoverProg.size = 1730792 := by decide +kernel
  obtain ⟨hc, hs, hh, hr⟩ := hn
  rw [hc, hs, hr] at h1
  rw [hh] at h2
  generalize SessionLayout.size = S at h1 h2
  generalize textAt texts.length = E at hA
  refine ⟨tOff, rfl, h4, ?_, ?_⟩ <;> generalize tOff = T at * <;> omega

/-- The return word lies in the session's own area, below the records. -/
theorem ret_in : (ownOff + ownRet) % 8 = 0 ∧ 64 ≤ ownOff + ownRet ∧ ownOff + ownRet < tOff ∧ ownOff + ownRet ≠ 0 := by
  obtain ⟨T, hT, -, -, hown⟩ := lay
  have := nums.own64; have := nums.ownAl; have := nums.retAl; have := nums.ret8
  rw [hT]; omega

/-- Connection `c`'s output lies within the session's words. -/
theorem out_in {c i : Nat} (hc : c < conns) (hi : i < data) :
    64 ≤ tOff + c * 2712 + 2200 + i ∧ tOff + c * 2712 + 2200 + i < SessionLayout.size := by
  have h1 := table_end
  obtain ⟨T, hT, -, -, hown⟩ := lay
  obtain ⟨hs, -, -, hd, hn, h64⟩ := nums
  rw [hn, hs] at h1
  rw [hn] at hc
  rw [hd] at hi
  rw [hT] at h1 ⊢
  generalize SessionLayout.size = S at *
  generalize News.RecoverProg.size = RS at *
  omega

theorem outAt_off (b : Word) (c : Nat) : outAt b c = b + BitVec.ofNat 64 (tOff + c * 2712 + 2200) := by
  rw [outAt_eq, ← tOff_eq, nums.slot, nums.out]

/-- A word outside connection `c`'s output: one below the table, from an aligned base. -/
theorem below_table {b : Word} (hb : b.toNat % 8 = 0) {c x : Nat} (hc : c < conns) (hx : x < tOff) :
    ¬ OutWord b c (byteAlign (b + BitVec.ofNat 64 x)) := by
  obtain ⟨T, hT, h8, hend, -⟩ := lay
  obtain ⟨-, -, -, hd, hn, -⟩ := nums
  rintro ⟨i, hi, e⟩
  rw [outAt_off, add_ofNat] at e
  exact words_apart hb (by omega) (by omega) (by omega) e

/-- What `connText`'s statements keep from its entry `s0`: the locals it sets up, the memory's
domain, order, base and code, and every word but connection `c`'s output's and the return word. -/
structure TCtx (b : Word) (c t rl sl : Nat) (s0 s : PancakeState σ) : Prop where
  hc : s.locals "c" = some (BitVec.ofNat 64 c)
  ht : s.locals "t" = some (BitVec.ofNat 64 t)
  hcb : s.locals "cb" = some (SessionFrame.recordAt b c)
  hob : s.locals "ob" = some (outAt b c)
  hj : ∃ v, s.locals "j" = some v
  hrl : s.locals "rl" = some (BitVec.ofNat 64 rl)
  hsl : s.locals "sl" = some (BitVec.ofNat 64 sl)
  base : s.baseAddr = b
  memaddrs : s.memaddrs = s0.memaddrs
  be : s.be = s0.be
  code : s.code = s0.code
  words : ∀ w, ¬ OutWord b c w → w ≠ SessionCheck.retW b → s.memory w = s0.memory w

/-- …and the octets `acc` written so far, `o` their length. -/
def Wrote (b : Word) (c : Nat) (acc : List (BitVec 8)) (s : PancakeState σ) : Prop :=
  s.locals "o" = some (BitVec.ofNat 64 acc.length) ∧ memBytesAt s.memory s.memaddrs s.be (outAt b c) acc

/-- The locals `connText` sets up. -/
def ctxNames : List String := ["c", "t", "cb", "ob", "j", "rl", "sl", "o"]

theorem tctx_restore {b : Word} {c t rl sl : Nat} {s0 s : PancakeState σ} (h : TCtx b c t rl sl s0 s) {y : String}
    (hy : y ∉ ctxNames) (v : Option Value) : TCtx b c t rl sl s0 (restore s y v) := by
  simp only [ctxNames, List.mem_cons, List.mem_nil_iff, or_false, not_or] at hy
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, -⟩ := hy
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, h.base, h.memaddrs, h.be, h.code, h.words⟩ <;>
    simp only [restore, resVar] <;> first
    | (rw [if_neg (Ne.symm h1)]; exact h.hc) | (rw [if_neg (Ne.symm h2)]; exact h.ht)
    | (rw [if_neg (Ne.symm h3)]; exact h.hcb) | (rw [if_neg (Ne.symm h4)]; exact h.hob)
    | (rw [if_neg (Ne.symm h5)]; exact h.hj) | (rw [if_neg (Ne.symm h6)]; exact h.hrl)
    | (rw [if_neg (Ne.symm h7)]; exact h.hsl)

theorem wrote_restore {b : Word} {c : Nat} {acc : List (BitVec 8)} {s : PancakeState σ} (h : Wrote b c acc s)
    {y : String}
    (hy : y ∉ ctxNames) (v : Option Value) : Wrote b c acc (restore s y v) := by
  have : y ≠ "o" := fun e => hy (by simp [ctxNames, e])
  refine ⟨?_, h.2⟩
  simp only [restore, resVar]
  rw [if_neg (Ne.symm this)]
  exact h.1

/-- The texts of the replies in the session's words, as `textsSet` lays them out. -/
def TextsIn (b : Word) (m : Word → Word) (dm : Word → Bool) (be : Bool) : Prop :=
  ∀ k, k < texts.length →
    memBytesAt m dm be (b + BitVec.ofNat 64 (ownOff + ownTexts + textAt k)) (texts.getD k [])

theorem textAt_add (m k : Nat) : textAt (m + k) = textAt m + (((texts.drop m).take k).map List.length).sum := by
  simp only [textAt, List.take_add, List.map_append, List.sum_append]

theorem textAt_succ {k : Nat} (hk : k < texts.length) : textAt (k + 1) = textAt k + Session.textLen k := by
  simp only [textAt, List.take_add_one, List.map_append, List.sum_append, List.getElem?_eq_getElem hk,
    Option.toList_some, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero, Session.textLen,
    List.getD_eq_getElem?_getD, Option.getD_some]

/-- A text ends where the texts do, or before. -/
theorem text_end {k : Nat} (hk : k < texts.length) : textAt k + Session.textLen k ≤ textAt texts.length := by
  rw [← textAt_succ hk]
  obtain ⟨r, hr⟩ : ∃ r, texts.length = k + 1 + r := ⟨texts.length - (k + 1), by omega⟩
  rw [hr, textAt_add (k + 1) r]
  omega

/-- A text lies below the connections' records. -/
theorem text_below {k : Nat} (hk : k < texts.length) :
    ownOff + ownTexts + textAt k + Session.textLen k ≤ tOff := by
  have h1 := text_end hk
  have h3 := texts_end
  generalize textAt texts.length = E at h1 h3
  omega

/-- The locals `TCtx` names. -/
def tNames : List String := ["c", "t", "cb", "ob", "rl", "sl"]

theorem TCtx.carry {b : Word} {c t rl sl : Nat} {s0 s u : PancakeState σ} (h : TCtx b c t rl sl s0 s)
    (hl : ∀ y ∈ tNames, u.locals y = s.locals y) (hj : ∃ v, u.locals "j" = some v)
    (hm : ∀ w, ¬ OutWord b c w → w ≠ SessionCheck.retW b → u.memory w = s.memory w)
    (hdm : u.memaddrs = s.memaddrs) (hbe : u.be = s.be) (hbase : u.baseAddr = s.baseAddr) (hcode : u.code = s.code) :
    TCtx b c t rl sl s0 u :=
  ⟨by rw [hl _ (by simp [tNames])]; exact h.hc, by rw [hl _ (by simp [tNames])]; exact h.ht,
    by rw [hl _ (by simp [tNames])]; exact h.hcb, by rw [hl _ (by simp [tNames])]; exact h.hob, hj,
    by rw [hl _ (by simp [tNames])]; exact h.hrl, by rw [hl _ (by simp [tNames])]; exact h.hsl, hbase.trans h.base,
    hdm.trans h.memaddrs, hbe.trans h.be, hcode.trans h.code, fun w hw hr => by rw [hm w hw hr]; exact h.words w hw hr⟩

/-- …a local outside them set. -/
theorem TCtx.set {b : Word} {c t rl sl : Nat} {s0 s : PancakeState σ} (h : TCtx b c t rl sl s0 s) {y : String}
    (hy : y ∉ tNames) (v : Value) : TCtx b c t rl sl s0 { s with locals := setLocal s.locals y v } :=
  h.carry (fun x hx => by simp only [setLocal]; rw [if_neg (fun (e : x = y) => hy (e ▸ hx))])
    (by obtain ⟨w, hw⟩ := h.hj; simp only [setLocal]; split
        · exact ⟨_, rfl⟩
        · exact ⟨w, hw⟩) (fun _ _ _ => rfl) rfl rfl rfl rfl

/-- **Octets `bs` put after those written**, every other octet and every word outside the output as
they were, the context's locals kept: the output is `acc ++ bs`. -/
theorem wrote_put {b : Word} {c t rl sl : Nat} {s0 s u : PancakeState σ}
    {acc bs : List (BitVec 8)} (hc : c < conns) (hroom : acc.length + bs.length ≤ data)
    (hx : TCtx b c t rl sl s0 s) (hw : Wrote b c acc s)
    (hloc : ∀ y ∈ tNames, u.locals y = s.locals y) (hj : ∃ v, u.locals "j" = some v)
    (hdm : u.memaddrs = s.memaddrs) (hbe : u.be = s.be) (hbase : u.baseAddr = s.baseAddr) (hcode : u.code = s.code)
    (hput : memBytesAt u.memory u.memaddrs u.be (outAt b c + BitVec.ofNat 64 acc.length) bs)
    (hbytes : ∀ a, (∀ i, i < bs.length → a ≠ outAt b c + BitVec.ofNat 64 acc.length + BitVec.ofNat 64 i) →
      memLoadByte u.memory u.memaddrs u.be a = memLoadByte s.memory s.memaddrs s.be a)
    (hwords : ∀ w, (∀ i, i < bs.length → w ≠ byteAlign (outAt b c + BitVec.ofNat 64 acc.length + BitVec.ofNat 64 i)) →
      u.memory w = s.memory w) :
    TCtx b c t rl sl s0 u ∧ memBytesAt u.memory u.memaddrs u.be (outAt b c) (acc ++ bs) := by
  obtain ⟨T, hT, -, hend, -⟩ := lay
  obtain ⟨-, -, -, hd, hn, -⟩ := nums
  refine ⟨hx.carry hloc hj (fun w hw' _ => ?_) hdm hbe hbase hcode, memBytesAt_append (fun i hi => ?_) hput⟩
  · exact hwords w fun i hi e => hw' ⟨acc.length + i, by omega, by rw [e, add_ofNat]⟩
  · rw [hbytes _ fun i' hi' => ?_]
    · exact hw.2 i hi
    · rw [outAt_off, add_ofNat, add_ofNat, add_ofNat]
      exact region_addr_inj b _ _ (by omega) (by omega) (by omega)

theorem TCtx.clock {b : Word} {c t rl sl : Nat} {s0 s : PancakeState σ} (h : TCtx b c t rl sl s0 s) (k : Nat) :
    TCtx b c t rl sl s0 { s with clock := k } := { h with }

theorem tw_clock (b : Word) (c t rl sl : Nat) (s0 : PancakeState σ) (acc : List (BitVec 8)) :
    Safe.ClockFree (fun s => TCtx b c t rl sl s0 s ∧ Wrote b c acc s) :=
  fun _ k ⟨h, hw⟩ => ⟨h.clock k, hw⟩

/-- The session's return word is no octet's word from an offset apart from it. -/
theorem apart_ret {b : Word} (hb : b.toNat % 8 = 0) {X n : Nat}
    (hX : X + n ≤ ownOff + ownRet ∨ ownOff + ownRet + 8 ≤ X) (hXe : X + n < 2 ^ 62) :
    ∀ i, i < n → byteAlign (b + BitVec.ofNat 64 X + BitVec.ofNat 64 i) ≠ SessionCheck.retW b := by
  intro i hi e
  have hr : (ownOff + ownRet) % 8 = 0 ∧ ownOff + ownRet < 2 ^ 62 := by
    obtain ⟨T, -, -, hroom, hown⟩ := lay; have := nums.ret8; have := nums.ownAl; have := nums.retAl
    omega
  rw [SessionCheck.retW, ← byteAlign_of_aligned hb hr.1, add_ofNat] at e
  exact words_apart hb (by omega) (by omega) (by omega) e

/-- A copy after the octets written, `o` moved past it, as it lowers. -/
theorem copyAppend_lowerK {src len : Syntax.PExpr} {SRC LEN : PancakeExp} (hs : Lower.lowerExp src = some SRC)
    (hl : Lower.lowerExp len = some LEN) (k : PancakeProg) :
    Block.lowerK (SessionStore.copy "j" (Syntax.eAdd (Syntax.v "ob") (Syntax.v "o")) src len ++
      [.assign "o" (Syntax.eAdd (Syntax.v "o") len)]) k =
      some (copyP "j" (.op .add (.var "ob") (.var "o")) SRC LEN (.seq (.assign "o" (.op .add (.var "o") LEN)) k)) := by
  rw [lowerK_append]
  have h1 : Block.lowerK [.assign "o" (Syntax.eAdd (Syntax.v "o") len)] k =
      some (.seq (.assign "o" (.op .add (.var "o") LEN)) k) := by
    simp [Block.lowerK, Lower.lowerStmt1, Lower.lowerExp, Syntax.eAdd, Syntax.v, hl]
  rw [h1, Option.bind_some]
  exact copy_lowerK rfl hs hl _

/-- The octets `bs` at offset `X` of the session's words, below the table or past the connections'
records, copied after those written, `o` moved past them. -/
theorem appendFrom_frag (o : Oracle σ) {b : Word} (hb : b.toNat % 8 = 0) {c t rl sl : Nat}
    {s0 : PancakeState σ} {acc bs : List (BitVec 8)} {X : Nat} {src len : Syntax.PExpr} {SRC LEN : PancakeExp}
    {P : Assn σ} (hc : c < conns) (hcov : Analyzer.Covers SessionLayout.size s0.memaddrs b)
    (hsrc : Lower.lowerExp src = some SRC) (hlen : Lower.lowerExp len = some LEN)
    (hSn : NoLoad SRC ∧ ExpAvoids (· = "j") SRC) (hLn : NoLoad LEN ∧ ExpAvoids (· = "j") LEN ∧ ExpAvoids (· = "o") LEN)
    (hP : ∀ s, P s → TCtx b c t rl sl s0 s ∧ Wrote b c acc s ∧ eval s SRC = some (b + BitVec.ofNat 64 X) ∧
      eval s LEN = some (BitVec.ofNat 64 bs.length))
    (hin : memBytesAt s0.memory s0.memaddrs s0.be (b + BitVec.ofNat 64 X) bs)
    (hX : X + bs.length ≤ tOff ∨ tOff + 173568 ≤ X) (hXe : X + bs.length < 2 ^ 62)
    (hXr : X + bs.length ≤ ownOff + ownRet ∨ ownOff + ownRet + 8 ≤ X) (hroom : acc.length + bs.length ≤ data) :
    Frag o (SessionStore.copy "j" (Syntax.eAdd (Syntax.v "ob") (Syntax.v "o")) src len ++
      [.assign "o" (Syntax.eAdd (Syntax.v "o") len)]) P
      (fun s => TCtx b c t rl sl s0 s ∧ Wrote b c (acc ++ bs) s) := by
  obtain ⟨T, hT, h8, hend, hown⟩ := lay
  obtain ⟨hslot, hout, -, hd, hn, h64⟩ := nums
  intro k' R Q _ hk'
  refine ⟨_, copyAppend_lowerK hsrc hlen k', ?_⟩
  refine copy_then o (P' := fun u => TCtx b c t rl sl s0 u ∧ u.locals "o" = some (BitVec.ofNat 64 acc.length) ∧
      memBytesAt u.memory u.memaddrs u.be (outAt b c) (acc ++ bs) ∧ eval u LEN = some (BitVec.ofNat 64 bs.length))
    (fun s hs => ?_) ?_
  · obtain ⟨hx, hw, hS, hL⟩ := hP s hs
    refine ⟨outAt b c + BitVec.ofNat 64 acc.length, b + BitVec.ofNat 64 X, bs, ⟨hx.hj,
      by simp [eval, hx.hob, hw.1], hS, hL, by omega, fun i hi => ?_, fun i hi => ?_, fun i i' hi hi' => ?_,
      ⟨⟨trivial, trivial⟩, hSn.1, hLn.1⟩, ⟨by simp [ExpAvoids], hSn.2, hLn.2.1⟩⟩, fun u hu => ?_⟩
    · rw [hx.memaddrs, hx.be, load_of_word (hx.words _ ?_ (apart_ret hb hXr hXe i hi))]
      · exact hin i hi
      · rw [add_ofNat]
        rintro ⟨i', hi', e⟩
        rw [outAt_off, add_ofNat] at e
        exact words_apart hb (by omega) (by omega) (by omega) e
    · rw [hx.memaddrs, outAt_off, add_ofNat, add_ofNat]
      have := out_in hc (show acc.length + i < data by omega)
      exact hcov.1 _ (by simp only [Analyzer.floor]; omega) (by omega)
    · rw [outAt_off, add_ofNat, add_ofNat, add_ofNat]
      exact region_addr_inj b _ _ (by omega) (by omega) (by omega)
    · obtain ⟨hkp, hju, hput, hbytes, hwords⟩ := hu
      have hl : ∀ y ∈ tNames, u.locals y = s.locals y := fun y hy => hkp.locals y (by
        intro e; subst e; simp [tNames] at hy)
      obtain ⟨hx', hput'⟩ := wrote_put hc hroom hx hw hl ⟨_, hju⟩ hkp.memaddrs hkp.be hkp.base hkp.code hput
        hbytes hwords
      refine ⟨hx', by rw [hkp.locals "o" (by decide)]; exact hw.1, hput', ?_⟩
      have := eval_noLoad (hide := (· = "j")) (fun y hy => hkp.locals y hy) hkp.base LEN hLn.1 hLn.2.1
      rw [this, hL]
  · refine seq (assign fun u ⟨hx, ho, hput, hL⟩ => ⟨BitVec.ofNat 64 (acc ++ bs).length, _,
      by simp [eval, ho, hL, BitVec.ofNat_add], ho, hx.set (by decide) _, by simp [setLocal], hput⟩)
      hk' (tw_clock b c t rl sl s0 _)

/-- **A text of the session's appended** to the output. -/
theorem appendText_frag (o : Oracle σ) {b : Word} (hb : b.toNat % 8 = 0) {c t rl sl k : Nat}
    {s0 : PancakeState σ} {acc : List (BitVec 8)} (hc : c < conns)
    (hcov : Analyzer.Covers SessionLayout.size s0.memaddrs b) (htx : TextsIn b s0.memory s0.memaddrs s0.be)
    (hk : k < texts.length) (hroom : acc.length + Session.textLen k ≤ data) :
    Frag o (Session.appendText k) (fun s => TCtx b c t rl sl s0 s ∧ Wrote b c acc s)
      (fun s => TCtx b c t rl sl s0 s ∧ Wrote b c (acc ++ texts.getD k []) s) := by
  obtain ⟨T, hT, h8, hend, hown⟩ := lay
  obtain ⟨-, -, -, hd, hn, h64⟩ := nums
  have hT := text_below hk
  have hpos : (ownOff + ownTexts + textAt k == 0) = false := by
    rw [beq_eq_false_iff_ne]; omega
  have hTA : Lower.lowerExp (Session.textAddr k) =
      some (.op .add .base (.const (BitVec.ofNat 64 (ownOff + ownTexts + textAt k)))) := by
    simp [Session.textAddr, SessionStore.at_, Syntax.atOff, hpos, Lower.lowerExp, Syntax.eAdd, Syntax.n]
  have hlen : (texts.getD k []).length = Session.textLen k := rfl
  have hr8 := nums.ret8
  exact appendFrom_frag o hb hc hcov (X := ownOff + ownTexts + textAt k) (bs := texts.getD k []) hTA rfl
    ⟨⟨trivial, trivial⟩, ⟨trivial, trivial⟩⟩ ⟨trivial, trivial, trivial⟩
    (fun s ⟨hx, hw⟩ => ⟨hx, hw, by simp [eval, hx.base], by rw [hlen]; rfl⟩) (htx k hk) (Or.inl (by omega))
    (by omega) (Or.inr (by omega)) (by omega)

/-- A word of the session's own below the connections' records, as it was at entry. -/
theorem own_word {b : Word} (hb : b.toNat % 8 = 0) {c t rl sl X : Nat} {s0 s : PancakeState σ} (hc : c < conns)
    (hx : TCtx b c t rl sl s0 s) (hX : X % 8 = 0) (hXt : X < tOff) (hXr : X ≠ ownOff + ownRet) :
    s.memory (b + BitVec.ofNat 64 X) = s0.memory (b + BitVec.ofNat 64 X) := by
  obtain ⟨T, hT, -, hroom, hown⟩ := lay
  have hr := nums.ret8
  have e := byteAlign_of_aligned hb hX
  exact hx.words _ (e ▸ below_table hb hc hXt) (region_addr_inj b _ _ (by omega) (by omega) hXr)

/-- …and addressable. -/
theorem own_addr {b : Word} {dm : Word → Bool} (hcov : Analyzer.Covers SessionLayout.size dm b) {X : Nat}
    (hX : X % 8 = 0) (h64 : 64 ≤ X) (hXt : X < tOff) : dm (b + BitVec.ofNat 64 X) = true := by
  have := table_end
  revert hcov
  generalize SessionLayout.size = S at this
  intro hcov
  exact hcov.2 X (by simp only [Analyzer.floor]; omega) (by omega) hX

/-- The return word is no word of the output's. -/
theorem retW_out {b : Word} (hb : b.toNat % 8 = 0) {c : Nat} (hc : c < conns) : ¬ OutWord b c
    (SessionCheck.retW b) := by
  obtain ⟨T, hT, -, hend, hown⟩ := lay
  have := nums.ownAl; have := nums.retAl; have := nums.ret8
  have e := byteAlign_of_aligned hb (X := ownOff + ownRet) (by omega)
  rw [SessionCheck.retW, ← e]
  exact below_table hb hc (by rw [hT]; omega)

theorem Wrote.set {b : Word} {c : Nat} {acc : List (BitVec 8)} {s : PancakeState σ} (h : Wrote b c acc s)
    {y : String} (hy : y ≠ "o") (v : Value) : Wrote b c acc { s with locals := setLocal s.locals y v } :=
  ⟨by simp only [setLocal]; rw [if_neg (Ne.symm hy)]; exact h.1, h.2⟩

/-- A word the session keeps of its own below the texts, its value from `s0`, read. -/
theorem eval_own {b : Word} (hb : b.toNat % 8 = 0) {c t rl sl X : Nat} {s0 s : PancakeState σ} (hc : c < conns)
    (hcov : Analyzer.Covers SessionLayout.size s0.memaddrs b) (hx : TCtx b c t rl sl s0 s) (hX : X % 8 = 0)
    (h64 : 64 ≤ X) (hXt : X < tOff) (hXr : X ≠ ownOff + ownRet) :
    eval s (.loadWord (.op .add .base (.const (BitVec.ofNat 64 X)))) = some (s0.memory (b + BitVec.ofNat 64 X)) := by
  simp only [eval, hx.base, hx.memaddrs, own_addr hcov hX h64 hXt, if_true, own_word hb hc hx hX hXt hXr]

/-- A place `k` past a pointer lowers as the pointer does, `k` added; no lowered subterm is unfolded. -/
theorem atOff_lower {p : Syntax.PExpr} {P : PancakeExp} (hp : Lower.lowerExp p = some P) {k : Nat} (hk : k ≠ 0) :
    Lower.lowerExp (Syntax.atOff p k) = some (.op .add P (.const (BitVec.ofNat 64 k))) := by
  have : (k == 0) = false := by rw [beq_eq_false_iff_ne]; exact hk
  rw [Syntax.atOff, this]
  simp [Lower.lowerExp, Syntax.eAdd, Syntax.n, hp]

/-- `at_ X` as it lowers, for an offset past zero. -/
theorem at_lower {X : Nat} (hX : X ≠ 0) :
    Lower.lowerExp (SessionStore.at_ X) = some (.op .add .base (.const (BitVec.ofNat 64 X))) := by
  have : (X == 0) = false := by rw [beq_eq_false_iff_ne]; exact hX
  simp [SessionStore.at_, Syntax.atOff, this, Lower.lowerExp, Syntax.eAdd, Syntax.n]

theorem at_add_lower {X : Nat} (hX : X ≠ 0) {B : Syntax.PExpr} {B' : PancakeExp} (hB : Lower.lowerExp B = some B') :
    Lower.lowerExp (Syntax.eAdd (SessionStore.at_ X) B) =
      some (.op .add (.op .add .base (.const (BitVec.ofNat 64 X))) B') := by
  simp only [Syntax.eAdd, Lower.lowerExp, at_lower hX, hB]

/-- **The revision appended.** -/
theorem appendRevision_frag (o : Oracle σ) {b : Word} (hb : b.toNat % 8 = 0) {c t rl sl : Nat}
    {s0 : PancakeState σ} {acc rev : List (BitVec 8)} (hc : c < conns)
    (hcov : Analyzer.Covers SessionLayout.size s0.memaddrs b)
    (hrev : memBytesAt s0.memory s0.memaddrs s0.be (b + BitVec.ofNat 64 (ownOff + ownRev)) rev)
    (hrl : rev.length = rl) (hmax : rl ≤ revMax) (hroom : acc.length + rl ≤ data) :
    Frag o Session.appendRevision (fun s => TCtx b c t rl sl s0 s ∧ Wrote b c acc s)
      (fun s => TCtx b c t rl sl s0 s ∧ Wrote b c (acc ++ rev) s) := by
  obtain ⟨T, hT, -, hend, hown⟩ := lay
  obtain ⟨-, -, -, hd, hn, h64⟩ := nums
  have hr : ownRev + revMax ≤ ownTexts := by decide
  have hr2 : ownRev + revMax ≤ ownRet := by decide
  exact appendFrom_frag o hb hc hcov (X := ownOff + ownRev) (bs := rev) (at_lower (by omega)) rfl
    ⟨⟨trivial, trivial⟩, by simp [ExpAvoids]⟩
    ⟨trivial, by simp [ExpAvoids], by simp [ExpAvoids]⟩
    (fun s ⟨hx, hw⟩ => ⟨hx, hw, by simp [eval, hx.base], by rw [hrl]; exact hx.hrl⟩) hrev
    (Or.inl (by omega)) (by omega) (Or.inl (by omega)) (by omega)

/-- **The address of the source appended.** -/
theorem appendSource_frag (o : Oracle σ) {b : Word} (hb : b.toNat % 8 = 0) {c t rl sl : Nat}
    {s0 : PancakeState σ} {acc src : List (BitVec 8)} (hc : c < conns)
    (hcov : Analyzer.Covers SessionLayout.size s0.memaddrs b)
    (hsrc : memBytesAt s0.memory s0.memaddrs s0.be (b + BitVec.ofNat 64 (ownOff + ownSrc)) src)
    (hsl : src.length = sl) (hmax : sl ≤ srcMax) (hroom : acc.length + sl ≤ data) :
    Frag o Session.appendSource (fun s => TCtx b c t rl sl s0 s ∧ Wrote b c acc s)
      (fun s => TCtx b c t rl sl s0 s ∧ Wrote b c (acc ++ src) s) := by
  obtain ⟨T, hT, -, hend, hown⟩ := lay
  obtain ⟨-, -, -, hd, hn, h64⟩ := nums
  have hr : ownSrc + srcMax ≤ ownTexts := by decide
  have hr2 : ownSrc + srcMax ≤ ownRet := by decide
  exact appendFrom_frag o hb hc hcov (X := ownOff + ownSrc) (bs := src) (at_lower (by omega)) rfl
    ⟨⟨trivial, trivial⟩, by simp [ExpAvoids]⟩
    ⟨trivial, by simp [ExpAvoids], by simp [ExpAvoids]⟩
    (fun s ⟨hx, hw⟩ => ⟨hx, hw, by simp [eval, hx.base], by rw [hsl]; exact hx.hsl⟩) hsrc
    (Or.inl (by omega)) (by omega) (Or.inl (by omega)) (by omega)

theorem tw_il_clock (b : Word) (c t rl sl : Nat) (s0 : PancakeState σ) (acc : List (BitVec 8)) (n : Nat) :
    Safe.ClockFree (fun s => (TCtx b c t rl sl s0 s ∧ Wrote b c acc s) ∧ s.locals "il" = some (BitVec.ofNat 64 n)) :=
  fun s k ⟨h, hil⟩ => ⟨tw_clock b c t rl sl s0 acc s k h, hil⟩

/-- `appendId`'s statements: the length read and bounded, the octets copied. -/
theorem appendId_eq : Session.appendId = [.dec "il" (SessionStore.ld (SessionStore.at_ (ownOff + ownIdLen)))] ++
    ([SessionStore.keptIn (Syntax.v "il") 250] ++ (SessionStore.copy "j" (Syntax.eAdd (Syntax.v "ob") (Syntax.v "o"))
      (SessionStore.at_ (ownOff + ownId))
      (Syntax.v "il") ++ [.assign "o" (Syntax.eAdd (Syntax.v "o") (Syntax.v "il"))])) :=
  rfl

/-- **The Message-ID looked up last appended.** -/
theorem appendId_frag (o : Oracle σ) {b : Word} (hb : b.toNat % 8 = 0) {c t rl sl : Nat}
    {s0 : PancakeState σ} {acc id : List (BitVec 8)} (hc : c < conns)
    (hcov : Analyzer.Covers SessionLayout.size s0.memaddrs b)
    (hlen : s0.memory (b + BitVec.ofNat 64 (ownOff + ownIdLen)) = BitVec.ofNat 64 id.length)
    (hid : memBytesAt s0.memory s0.memaddrs s0.be (b + BitVec.ofNat 64 (ownOff + ownId)) id)
    (hmax : id.length ≤ 250) (hroom : acc.length + id.length ≤ data) :
    Frag o Session.appendId (fun s => TCtx b c t rl sl s0 s ∧ Wrote b c acc s)
      (fun s => TCtx b c t rl sl s0 s ∧ Wrote b c (acc ++ id) s) := by
  obtain ⟨T, hT, h8, hend, hown⟩ := lay
  obtain ⟨-, -, -, hd, hn, h64⟩ := nums
  have hr : ownIdLen % 8 = 0 ∧ ownId + 250 ≤ ownTexts ∧ ownIdLen < ownId ∧ ownOff % 8 = 0 := by decide
  have hL : Lower.lowerExp (SessionStore.ld (SessionStore.at_ (ownOff + ownIdLen))) =
      some (.loadWord (.op .add .base (.const (BitVec.ofNat 64 (ownOff + ownIdLen))))) := by
    simp [SessionStore.ld, Lower.lowerExp, at_lower (show ownOff + ownIdLen ≠ 0 by omega)]
  let P1 : Assn σ := fun s => (TCtx b c t rl sl s0 s ∧ Wrote b c acc s) ∧
    s.locals "il" = some (BitVec.ofNat 64 id.length)
  have h1 : Frag o [.dec "il" (SessionStore.ld (SessionStore.at_ (ownOff + ownIdLen)))]
      (fun s => TCtx b c t rl sl s0 s ∧ Wrote b c acc s) P1 :=
    frag_dec o hL fun s ⟨hx, hw⟩ => ⟨_, eval_own hb hc hcov hx (by omega) (by omega) (by omega)
      (by have : ownIdLen ≠ ownRet := (by decide)
          omega),
      ⟨hx.set (by decide) _, hw.set (by decide) _⟩, by rw [hlen]; simp [setLocal]⟩
  have h2 : Frag o [SessionStore.keptIn (Syntax.v "il") 250] P1 P1 :=
    frag_keptIn o (e := Syntax.v "il") rfl (by decide) (tw_il_clock b c t rl sl s0 acc id.length)
      fun s h => ⟨id.length, hmax, h.2⟩
  have hri : ownRet + 8 ≤ ownId := by decide
  have h3 := appendFrom_frag o hb hc hcov (P := P1) (bs := id) (X := ownOff + ownId)
      (src := SessionStore.at_ (ownOff + ownId))
    (len := Syntax.v "il") (at_lower (show ownOff + ownId ≠ 0 by omega)) rfl
    ⟨⟨trivial, trivial⟩, by simp [ExpAvoids]⟩ ⟨trivial, by simp [ExpAvoids], by simp [ExpAvoids]⟩
    (fun s ⟨⟨hx, hw⟩, hil⟩ => ⟨hx, hw, by simp [eval, hx.base], hil⟩) hid (Or.inl (by omega)) (by omega)
    (Or.inr (by omega)) hroom
  rw [appendId_eq]
  exact frag_append h1 (frag_append h2 h3)

theorem digits_frag (o : Oracle σ) {p off : String} {dst x : Syntax.PExpr} {DST X : PancakeExp} {room : Nat}
    (hd : Lower.lowerExp dst = some DST) (hx : Lower.lowerExp x = some X) {P P' : Assn σ}
    (hpre : ∀ s, P s → ∃ v ov D, DigPre (p ++ "n") (p ++ "t") (p ++ "q") off DST X room v ov D s ∧
      ∀ u, DigPost (p ++ "n") (p ++ "t") (p ++ "q") off v ov D s u → P' u) :
    Frag o (SessionStore.digits p dst off x room) P P' := by
  intro k R Q hQ hk
  exact ⟨_, digits_lowerK hd hx k, digits_then o hpre (fun u y v hq hy => hQ u y v hq (by
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hy
    rcases hy with rfl | rfl | rfl <;> simp [declared, SessionStore.digits, SessionStore.keptIn, SessionStore.inc])) hk⟩

theorem TCtx.put {b : Word} {c t rl sl : Nat} {s0 s : PancakeState σ} (h : TCtx b c t rl sl s0 s) {A : Word}
    (hA : OutWord b c (byteAlign A)) (y : BitVec 8) :
    TCtx b c t rl sl s0 { s with memory := putByte s.memory s.be A y } :=
  ⟨h.hc, h.ht, h.hcb, h.hob, h.hj, h.hrl, h.hsl, h.base, h.memaddrs, h.be, h.code, fun w hw hr => by
    simp only [putByte]
    rw [if_neg (fun (e : w = byteAlign A) => hw (e ▸ hA))]
    exact h.words w hw hr⟩

/-- A byte `y` put after those written, `o` moved past it. -/
theorem appendByte_frag (o : Oracle σ) {b : Word} {c t rl sl : Nat}
    {s0 : PancakeState σ} {acc : List (BitVec 8)} (hc : c < conns)
    (hcov : Analyzer.Covers SessionLayout.size s0.memaddrs b) {y : Nat} (hroom : acc.length < data) :
    Frag o [.storeb (Syntax.eAdd (Syntax.v "ob") (Syntax.v "o")) (Syntax.n y), SessionStore.inc "o"]
      (fun s => TCtx b c t rl sl s0 s ∧ Wrote b c acc s)
      (fun s => TCtx b c t rl sl s0 s ∧ Wrote b c (acc ++ [BitVec.ofNat 8 y]) s) := by
  obtain ⟨T, hT, h8, hend, hown⟩ := lay
  obtain ⟨-, -, -, hd, hn, h64⟩ := nums
  have hA : ∀ s, TCtx b c t rl sl s0 s →
      s.memaddrs (byteAlign (outAt b c + BitVec.ofNat 64 acc.length)) = true := fun s hx => by
    rw [hx.memaddrs, outAt_off, add_ofNat]
    have := out_in hc hroom
    exact hcov.1 _ (by simp only [Analyzer.floor]; omega) this.2
  have hW : OutWord b c (byteAlign (outAt b c + BitVec.ofNat 64 acc.length)) := ⟨acc.length, hroom, rfl⟩
  let M : Assn σ := fun s => TCtx b c t rl sl s0 s ∧ s.locals "o" = some (BitVec.ofNat 64 acc.length) ∧
    memBytesAt s.memory s.memaddrs s.be (outAt b c) (acc ++ [BitVec.ofNat 8 y])
  have hM : Safe.ClockFree M := fun _ k ⟨h, rest⟩ => ⟨h.clock k, rest⟩
  have h1 : Frag o [.storeb (Syntax.eAdd (Syntax.v "ob") (Syntax.v "o")) (Syntax.n y)]
      (fun s => TCtx b c t rl sl s0 s ∧ Wrote b c acc s) M :=
    frag_one rfl rfl rfl hM (Safe.storeByte fun s ⟨hx, hw⟩ => ⟨outAt b c + BitVec.ofNat 64 acc.length,
      BitVec.ofNat 64 y, _, by simp [eval, hx.hob, hw.1], rfl, memStore_eq _ _ _ _ _ (hA s hx),
      by rw [setWidth_ofNat_8]; exact ⟨hx.put hW _, hw.1, memBytesAt_snoc hw.2 (hA s hx) (by omega)⟩⟩)
  have h2 : Frag o [SessionStore.inc "o"] M
      (fun s => TCtx b c t rl sl s0 s ∧ Wrote b c (acc ++ [BitVec.ofNat 8 y]) s) :=
    frag_one rfl rfl rfl (tw_clock b c t rl sl s0 _) (Safe.assign fun s ⟨hx, ho, hput⟩ =>
      ⟨BitVec.ofNat 64 (acc.length + 1), _, by simp [eval, ho, BitVec.ofNat_add], ho, hx.set (by decide) _,
        by simp [setLocal], hput⟩)
  exact frag_append h1 h2

/-- **A number, below 2^32, and a space appended**, the locals named from `p` counting. -/
theorem appendNumber_frag (o : Oracle σ) {b : Word} {c t rl sl : Nat}
    {s0 : PancakeState σ} {acc : List (BitVec 8)} (hc : c < conns)
    (hcov : Analyzer.Covers SessionLayout.size s0.memaddrs b) {p : String} {x : Syntax.PExpr} {X : PancakeExp}
    (hx : Lower.lowerExp x = some X)
    (hp : p ++ "n" ≠ p ++ "t" ∧ p ++ "n" ≠ p ++ "q" ∧ p ++ "t" ≠ p ++ "q" ∧ p ++ "n" ∉ ctxNames ∧
      p ++ "t" ∉ ctxNames ∧ p ++ "q" ∉ ctxNames)
    (hXav : ExpAvoids (fun y => y = p ++ "n" ∨ y = p ++ "t" ∨ y = p ++ "q") X) {v : Nat} (hv : v < 2 ^ 32)
    (hX : ∀ s, TCtx b c t rl sl s0 s → Wrote b c acc s → eval s X = some (BitVec.ofNat 64 v))
    (hroom : acc.length + 11 ≤ data) :
    Frag o (Session.appendNumber p x) (fun s => TCtx b c t rl sl s0 s ∧ Wrote b c acc s)
      (fun s => TCtx b c t rl sl s0 s ∧ Wrote b c (acc ++ CommandSpec.decimal v ++ [BitVec.ofNat 8 32]) s) := by
  obtain ⟨T, hT, h8, hend, hown⟩ := lay
  obtain ⟨-, -, -, hd, hn, h64⟩ := nums
  obtain ⟨hnt, hnq, htq, hn', ht', hq'⟩ := hp
  have hN := numDigits_le_ten v hv
  have hlen := decimal_length v
  have hne : ∀ z, z ∈ ctxNames → z ≠ p ++ "n" ∧ z ≠ p ++ "t" ∧ z ≠ p ++ "q" := fun z hz =>
    ⟨fun e => hn' (e ▸ hz), fun e => ht' (e ▸ hz), fun e => hq' (e ▸ hz)⟩
  have ho := hne "o" (by simp [ctxNames])
  have hob := hne "ob" (by simp [ctxNames])
  have hd1 : Frag o (SessionStore.digits p (Syntax.v "ob") "o" x (data - 1))
      (fun s => TCtx b c t rl sl s0 s ∧ Wrote b c acc s)
      (fun s => TCtx b c t rl sl s0 s ∧ Wrote b c (acc ++ CommandSpec.decimal v) s) := by
    refine digits_frag o (DST := .var "ob") rfl hx fun s ⟨hx', hw⟩ => ⟨v, acc.length, outAt b c,
      ⟨hnt, hnq, htq, ho.1, ho.2.1, ho.2.2,
      hv, by omega, by omega, hw.1, hX s hx' hw, hXav, by simp [eval, hx'.hob], trivial,
      by simp only [ExpAvoids, not_or]; exact hob, fun i hi => ?_⟩, fun u hu => ?_⟩
    · rw [hx'.memaddrs, outAt_off, add_ofNat, add_ofNat]
      have := out_in hc (show acc.length + i < data by omega)
      exact hcov.1 _ (by simp only [Analyzer.floor]; omega) this.2
    · have hloc : ∀ y ∈ tNames, u.locals y = s.locals y := by
        intro y hy
        have hy' : y ∈ ctxNames ∧ y ≠ "o" := by
          simp only [tNames, List.mem_cons, List.mem_nil_iff, or_false] at hy
          rcases hy with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [ctxNames]
        have h1 := hne y hy'.1
        exact hu.locals y h1.1 h1.2.1 h1.2.2 hy'.2
      have hj := hne "j" (by simp [ctxNames])
      obtain ⟨hx2, hput⟩ := wrote_put hc (bs := CommandSpec.decimal v) (by omega) hx' hw hloc
        (by rw [hu.locals "j" hj.1 hj.2.1 hj.2.2 (by decide)]; exact hx'.hj) hu.memaddrs hu.be hu.base hu.code
        (fun i hi => by rw [hu.digits i (by omega)]; simp [List.getElem?_eq_getElem hi])
        (fun a ha => hu.bytes a fun i hi => ha i (by omega)) (fun w hw' => hu.words w fun i hi => hw' i (by omega))
      exact ⟨hx2, by rw [hu.hoff]; simp [hlen], hput⟩
  exact frag_append hd1 (appendByte_frag o hc hcov (by simp only [List.length_append]; omega))

/-! ### The premises can hold -/

/-- The witnesses' base. -/
def wb : Word := 4096

/-- All the texts' octets, as many as `textAt` counts. -/
theorem texts_len : (texts.flatten).length = textAt texts.length := by
  simp [textAt, List.length_flatten]

theorem wb_off (x : Nat) (hx : x < 2 ^ 63) : (wb + BitVec.ofNat 64 x - wb).toNat = x := by
  rw [BitVec.add_comm, BitVec.add_sub_cancel, BitVec.toNat_ofNat]
  omega

theorem wb_aligned : wb.toNat % 8 = 0 := by decide

/-- A word at `Y` past the base keeps its value through bytes stored at `X` past it, a word or more away. -/
theorem putAll_far {b : Word} (hb : b.toNat % 8 = 0) {be : Bool} {X Y : Nat} {xs : List (BitVec 8)}
    (m : Word → Word) (hY : Y % 8 = 0) (hX : X + xs.length < 2 ^ 63) (hY' : Y < 2 ^ 63)
    (h : Y + 8 ≤ X ∨ X + xs.length ≤ Y) :
    putAll m be (b + BitVec.ofNat 64 X) 0 xs (b + BitVec.ofNat 64 Y) = m (b + BitVec.ofNat 64 Y) :=
  putAll_word xs 0 m fun j _ hj => by
    rw [add_ofNat, ← byteAlign_of_aligned hb hY]
    exact words_apart hb (by omega) (by omega) (by omega)

/-- …and an octet at `Y` through bytes stored elsewhere. -/
theorem putAll_away {b : Word} {dm : Word → Bool} {be : Bool} {X Y : Nat} {xs : List (BitVec 8)}
    (m : Word → Word) (hX : X + xs.length < 2 ^ 63) (hY : Y < 2 ^ 63) (h : Y < X ∨ X + xs.length ≤ Y) :
    memLoadByte (putAll m be (b + BitVec.ofNat 64 X) 0 xs) dm be (b + BitVec.ofNat 64 Y) =
      memLoadByte m dm be (b + BitVec.ofNat 64 Y) :=
  putAll_load xs 0 m fun j _ hj => by
    rw [add_ofNat]
    exact region_addr_inj b _ _ (by omega) (by omega) (by omega)

theorem memBytesAt_away {b : Word} {dm : Word → Bool} {be : Bool} {X Y : Nat} {xs ys : List (BitVec 8)}
    {m : Word → Word} (h : memBytesAt m dm be (b + BitVec.ofNat 64 Y) ys) (hX : X + xs.length < 2 ^ 63)
    (hY : Y + ys.length < 2 ^ 63) (hd : Y + ys.length ≤ X ∨ X + xs.length ≤ Y) :
    memBytesAt (putAll m be (b + BitVec.ofNat 64 X) 0 xs) dm be (b + BitVec.ofNat 64 Y) ys := fun i hi => by
  rw [add_ofNat, putAll_away m hX (by omega) (by omega), ← add_ofNat, h i hi]

/-- Bytes stored where the heap covers read back. -/
theorem putAll_in {b : Word} {dm : Word → Bool} {be : Bool} {X : Nat} {xs : List (BitVec 8)} (m : Word → Word)
    (hcov : Analyzer.Covers SessionLayout.size dm b) (hX : 64 ≤ X) (hXs : X + xs.length ≤ SessionLayout.size) :
    memBytesAt (putAll m be (b + BitVec.ofNat 64 X) 0 xs) dm be (b + BitVec.ofNat 64 X) xs := by
  have := putAll_bytes (dm := dm) (be := be) (a := b + BitVec.ofNat 64 X) xs [] m (fun _ h => by simp at h)
    (fun i hi => by
      rw [add_ofNat]
      exact hcov.1 _ (by simp [Analyzer.floor]; omega) (by simp at hi; omega))
    (by have := size_fits; have : heapBytes = 4194304 := by decide +kernel
        simp; omega)
  simpa using this

/-- The digit `0` at address zero, a counter `j` and `t` at zero, `n` and `o` at one. -/
def digState : PancakeState Unit :=
  { bareState () with
    memory := fun a => if a = 0 then 48 else 0
    locals := fun x => if x = "j" ∨ x = "t" then some 0 else if x = "n" ∨ x = "o" then some 1 else none }

theorem copyPre_witness : CopyPre "j" (.const 8) (.const 0) (.const 1) 8 0 [48#8] digState where
  hj := ⟨_, rfl⟩
  hdst := rfl
  hsrc := rfl
  hlen := rfl
  hshort := by decide
  hbytes := fun i h => by
    obtain rfl : i = 0 := by simp at h; omega
    decide
  hroom := fun _ _ => rfl
  hapart := fun i i' h h' => by
    obtain rfl : i = 0 := by simp at h; omega
    obtain rfl : i' = 0 := by simp at h'; omega
    decide
  hnoLoad := ⟨trivial, trivial, trivial⟩
  havoids := ⟨trivial, trivial, trivial⟩

theorem kept_witness : Kept "j" digState digState := kept_refl _ _

theorem wrKept_witness : WrKept "t" "q" digState digState := ⟨fun _ _ _ => rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem digPre_witness : DigPre "n" "t" "q" "j" (.const 0) (.const 0) 10 0 0 0 digState where
  nt := by decide
  nq := by decide
  tq := by decide
  on := by decide
  ot := by decide
  oq := by decide
  hx := by decide
  hroom := by decide
  hov := by decide
  hoff := rfl
  hX := rfl
  hXav := trivial
  hdst := rfl
  hdstN := trivial
  hdstA := trivial
  hroom8 := fun _ _ => rfl

theorem digPost_witness : DigPost "n" "t" "q" "o" 0 0 0 digState digState where
  locals := fun _ _ _ _ _ => rfl
  hoff := by rw [numDigits_zero]; rfl
  memaddrs := rfl
  be := rfl
  base := rfl
  ffi := rfl
  code := rfl
  digits := fun i h => by
    obtain rfl : i = 0 := by rw [numDigits_zero] at h; omega
    decide
  bytes := fun _ _ => rfl
  words := fun _ _ => rfl

theorem digMid_witness : DigMid "n" "t" "q" 0 digState digState :=
  ⟨fun _ _ _ _ => rfl, rfl, rfl, rfl, rfl, rfl, rfl, by rw [numDigits_zero]; rfl, rfl⟩

theorem outWord_witness : OutWord wb 0 (byteAlign (outAt wb 0 + BitVec.ofNat 64 0)) :=
  ⟨0, by rw [nums.dataLen]; decide, rfl⟩

end Output

end DN.Server.SessionAppend
