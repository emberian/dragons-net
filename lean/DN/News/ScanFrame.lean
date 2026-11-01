-- SPDX-License-Identifier: AGPL-3.0-or-later
import DN.News.ScanRun

/-!
# DN.News.ScanFrame

If it goes on, the scanner's check of a frame, `ScanProg.frameWhy`, gives the code of what
`DN.News.ScanRun.fault` finds, from the area and the window as `FwIn` says (`frameWhy_frag`).
-/

namespace DN.News.ScanRun

open DN.Compiler DN.Compiler.Wp DN.Compiler.Frag DN.Compiler.Bytes DN.News DN.News.Journal DN.News.ScanProg
open DN.News.FramerCode (bw bw_ne0 bw_eq0 eval_lt eval_eq eval_and)

variable {σ : Type}

/-! ## The area -/

/-- The area's numbers. -/
theorem nums : sKey = 520 ∧ sMessage = 536 ∧ sWindow = 1928 ∧ windowMax = 17776 ∧ windowRoom = 19168 ∧
    ScanProg.size = 21096 ∧ maxPayload = 1376 ∧ maxFrame = 1390 ∧ firstFrame = 50 ∧ headerLength = 13 ∧
    magic.length = 20 ∧ journalTitle.length = 19 ∧ chunk = 16384 ∧ messageMax = 1385 ∧ keyLength = 16 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The place `x` octets into the area at `A`. -/
def at_ (A : Word) (x : Nat) : Word := A + BitVec.ofNat 64 x

/-- The area's words addressable. -/
def Dom (A : Word) (dm : Word → Bool) : Prop := ∀ x, x < ScanProg.size → dm (byteAlign (at_ A x)) = true

/-- The words of the message a tag is computed over. -/
def MsgW (A : Word) (a : Word) : Prop := ∃ x, sMessage ≤ x ∧ x < sWindow ∧ a = at_ A x

theorem at_add (A : Word) (x y : Nat) : at_ A x + BitVec.ofNat 64 y = at_ A (x + y) := add_ofNat A x y

theorem at_ne {A : Word} {x y : Nat} (hx : x < 2 ^ 64) (hy : y < 2 ^ 64) (h : x ≠ y) : at_ A x ≠ at_ A y :=
  region_addr_inj A x y hx hy h

theorem at_inj {A : Word} {x y : Nat} (hx : x < 2 ^ 64) (hy : y < 2 ^ 64) (h : at_ A x = at_ A y) : x = y :=
  Classical.byContradiction fun hne => at_ne hx hy hne h

theorem align_at {A : Word} (hA : A.toNat % 8 = 0) (x : Nat) : byteAlign (at_ A x) = at_ A (x / 8 * 8) := by
  rw [at_, byteAlign_base hA, at_]

theorem msg_align {A : Word} (hA : A.toNat % 8 = 0) {j : Nat} (hj : j < sWindow - sMessage) :
    MsgW A (byteAlign (at_ A (sMessage + j))) :=
  ⟨sMessage + j / 8 * 8, Nat.le_add_right _ _, by
    simp only [sWindow, sMessage, sKey, sGroups, groupsMax, groupSlot, keyLength, messageMax, maxPayload] at hj ⊢
    omega, by rw [at_, byteAlign_base hA]; congr 2; simp only [sMessage, sKey, sGroups, groupsMax, groupSlot,
      keyLength]; omega⟩

theorem not_msg {A : Word} (hA : A.toNat % 8 = 0) {x : Nat} (hx : x < sMessage ∨ sWindow ≤ x) (h64 : x < 2 ^ 63) :
    ¬ MsgW A (byteAlign (at_ A x)) := by
  rintro ⟨y, h1, h2, e⟩
  rw [at_, byteAlign_base hA, at_] at e
  simp only [sWindow, sMessage, sKey, sGroups, groupsMax, groupSlot, keyLength, messageMax, maxPayload] at hx h1 h2
  exact region_addr_inj A _ _ (by omega) (by omega) (by omega) e

/-! ## Numbers as octets -/

theorem le_get : ∀ (k v i : Nat) (h : i < (le k v).length), (le k v)[i] = BitVec.ofNat 8 (v / 256 ^ i % 256)
  | 0, _, _, h => by simp [le] at h
  | k + 1, v, 0, _ => by simp [le]
  | k + 1, v, i + 1, h => by
    simp only [le, List.getElem_cons_succ]
    rw [le_get k (v / 256) i (by simp [le, le_length] at h ⊢; omega), Nat.div_div_eq_div_mul, Nat.pow_succ,
      Nat.mul_comm 256]

theorem byteOf_eq (q i : Nat) (hq : q < 2 ^ 64) :
    ((BitVec.ofNat 64 q >>> (8 * i)) &&& BitVec.ofNat 64 255).setWidth 8 = BitVec.ofNat 8 (q / 256 ^ i % 256) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_and, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt hq, Nat.shiftRight_eq_div_pow]
  rw [show 255 % 2 ^ 64 = 2 ^ 8 - 1 by decide, Nat.and_two_pow_sub_one_eq_mod, Nat.pow_mul]

/-! ## Statements -/

theorem kept_put {xs : List String} {w : Word → Prop} {s t : PancakeState σ} (h : Kept xs w s t) {a : Word}
    (ha : w (byteAlign a)) (be : Bool) (b : BitVec 8) :
    Kept xs w s { t with memory := putByte t.memory be a b } :=
  ⟨h.locals, fun x hx => by
    simp only [putByte]
    rw [if_neg (fun e : x = byteAlign a => hx (e ▸ ha))]
    exact h.memory x hx, h.memaddrs, h.be, h.base, h.ffi, h.code, fun y hy => h.keeps y hy⟩

/-- A predicate that what `Kept xs w` allows does not change. -/
def Stable (xs : List String) (w : Word → Prop) (F : Assn σ) : Prop := ∀ u u', F u → Kept xs w u u' → F u'

/-! ## The message a tag is computed over -/

/-- The locals `frameWhy` sets. -/
def fwNames : List String :=
  ["jwhy", "jpl", "jt", "k", "jhk", "p", "ji", "n", "r", "m", "v0", "v1", "v2", "v3", "off", "j", "jtag"]

section Message

variable {A : Word} {s0 : PancakeState σ} {F : Assn σ} {t len : Nat}

/-- Before the message: the frame of `frameWhy`, what `F` says, the type and the payload's length. -/
def MBase (A : Word) (s0 : PancakeState σ) (F : Assn σ) (t len : Nat) (u : PancakeState σ) : Prop :=
  Kept fwNames (MsgW A) s0 u ∧ F u ∧ u.locals "jt" = some (BitVec.ofNat 64 t) ∧
    u.locals "jpl" = some (BitVec.ofNat 64 len)

theorem mbase_clock (hF : Safe.ClockFree F) : Safe.ClockFree (MBase A s0 F t len) :=
  fun _ _ ⟨h1, h2, h3, h4⟩ => ⟨{ h1 with }, hF _ _ h2, h3, h4⟩

theorem mbase_set (hF : Stable ["p", "ji", "n"] (MsgW A) F) {u : PancakeState σ} (h : MBase A s0 F t len u)
    {x : String} (hx : x ∈ ["p", "ji", "n"]) (v : Value) : MBase A s0 F t len (setL u x v) := by
  have hx' : x ∈ fwNames := by simp at hx; rcases hx with rfl | rfl | rfl <;> decide
  have ht : "jt" ≠ x := by simp at hx; rcases hx with rfl | rfl | rfl <;> decide
  have hl : "jpl" ≠ x := by simp at hx; rcases hx with rfl | rfl | rfl <;> decide
  exact ⟨kept_set h.1 hx' v, hF _ _ h.2.1 (kept_set (kept_refl _ _ u) hx v),
    by simp [setL, setLocal, ht, h.2.2.1], by simp [setL, setLocal, hl, h.2.2.2]⟩

theorem mbase_put (hF : Stable ["p", "ji", "n"] (MsgW A) F) {u : PancakeState σ} (h : MBase A s0 F t len u)
    {a : Word} (ha : MsgW A (byteAlign a)) (b : BitVec 8) :
    MBase A s0 F t len { u with memory := putByte u.memory u.be a b } :=
  ⟨kept_put h.1 ha _ _, hF _ _ h.2.1 (kept_put (kept_refl _ _ u) ha _ _), h.2.2.1, h.2.2.2⟩

/-- **The message a tag is computed over**, written where the area keeps it: the frame's offset in eight
octets, its type and its payload. -/
theorem message_frag (o : Oracle σ) (hA : A.toNat % 8 = 0) (hdom : Dom A s0.memaddrs)
    (hsp : s0.locals "jsc" = some A) (hjz : s0.locals "jz" = some 0) {q : Nat} (hq : q < 2 ^ 62)
    (hjq : s0.locals "jq" = some (BitVec.ofNat 64 q)) {o' : Nat}
    (hjf : s0.locals "jf" = some (at_ A (sWindow + o'))) {pl : Bytes} (hroom : o' + 13 + pl.length ≤ windowRoom)
    (hlen : pl.length ≤ maxPayload)
    (hb : ∀ i (h : i < pl.length),
      memLoadByte s0.memory s0.memaddrs s0.be (at_ A (sWindow + o' + 13 + i)) = some pl[i])
    (hbound : ∀ y ∈ fwNames, ∃ v, s0.locals y = some v)
    (hF : Stable ["p", "ji", "n"] (MsgW A) F) (hFc : Safe.ClockFree F) :
    Frag o ScanProg.message (MBase A s0 F t pl.length)
      (fun u => MBase A s0 F t pl.length u ∧ u.locals "p" = some (at_ A sMessage) ∧
        u.locals "n" = some (BitVec.ofNat 64 (pl.length + 9)) ∧
        memBytesAt u.memory u.memaddrs u.be (at_ A sMessage) (le 8 q ++ BitVec.ofNat 8 t :: pl)) := by
  have hroom' : sWindow + o' + 13 + pl.length ≤ ScanProg.size := by have := nums; omega
  let Q (j : Nat) (u : PancakeState σ) : Prop := MBase A s0 F t pl.length u ∧
    u.locals "p" = some (at_ A sMessage) ∧ memBytesAt u.memory u.memaddrs u.be (at_ A sMessage) ((le 8 q).take j)
  have hQc : ∀ j, Safe.ClockFree (Q j) := fun _ _ _ ⟨h1, h2, h3⟩ => ⟨mbase_clock hFc _ _ h1, h2, h3⟩
  have hdm : ∀ u, MBase A s0 F t pl.length u → ∀ x, x < ScanProg.size → u.memaddrs (byteAlign (at_ A x)) = true :=
    fun u h x hx => by rw [h.1.memaddrs]; exact hdom x hx
  have hlocal : ∀ u, MBase A s0 F t pl.length u → ∀ y, y ∉ fwNames → u.locals y = s0.locals y :=
    fun u h y hy => h.1.locals y hy
  -- `p` names the message's place
  have f1 : Frag o [.assign "p" (Syntax.atOff sp sMessage)] (MBase A s0 F t pl.length) (Q 0) :=
    set_frag o (E := .op .add (.var "jsc") (.const (BitVec.ofNat 64 sMessage))) rfl (hQc 0) fun u h => by
      refine ⟨at_ A sMessage, by simp [eval, hlocal u h "jsc" (by decide), hsp, at_],
        kept_has h.1 (hbound _ (by decide)), mbase_set hF h (by decide) _, by simp [setL, setLocal],
        fun i hi => by simp at hi⟩
  -- its first eight octets, the offset
  have f2 : ∀ j, j ≤ 8 → Frag o ((List.range j).map fun i =>
      .storeb (Syntax.atOff (Syntax.v "p") i) (Syntax.eAnd (.shr (Syntax.v "jq") (Syntax.n (8 * i))) (Syntax.n 255)))
      (Q 0) (Q j) := by
    intro j
    induction j with
    | zero => intro _; exact frag_nil o fun _ h => h
    | succ j ih =>
      intro hj
      rw [List.range_succ, List.map_append]
      refine frag_append (ih (by omega)) (storeb_frag o (atOff_lower rfl j) (E := .op .and_
        (.shiftR (.var "jq") (.const (BitVec.ofNat 64 (8 * j)))) (.const (BitVec.ofNat 64 255))) rfl
        (hQc (j + 1)) fun u h => ?_)
      have hA0 : eval u (if j = 0 then .var "p" else .op .add (.var "p") (.const (BitVec.ofNat 64 j))) =
          some (at_ A sMessage + BitVec.ofNat 64 j) := by
        by_cases h0 : j = 0
        · subst h0; simp [eval, h.2.1]
        · simp [h0, eval, h.2.1]
      have hsh : (decide ((BitVec.ofNat 64 (8 * j)).toNat ≠ 0) && decide ((BitVec.ofNat 64 (8 * j)).toNat ≥ 64))
          = false := by
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; simp; omega
      have hv : eval u (.op .and_ (.shiftR (.var "jq") (.const (BitVec.ofNat 64 (8 * j))))
          (.const (BitVec.ofNat 64 255))) = some ((BitVec.ofNat 64 q >>> (8 * j)) &&& BitVec.ofNat 64 255) := by
        simp only [eval, hlocal u h.1 "jq" (by decide), hjq, hsh, Bool.false_eq_true, if_false]
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      have hin : sMessage + j < ScanProg.size := by have := nums; omega
      have hmw : MsgW A (byteAlign (at_ A (sMessage + j))) := msg_align hA (by have := nums; omega)
      rw [at_add] at hA0
      refine ⟨_, _, hA0, hv, hdm u h.1 _ hin, mbase_put hF h.1 hmw _, h.2.1, ?_⟩
      have hl : ((le 8 q).take j).length = j := by simp [le_length]; omega
      have hlt : j < (le 8 q).length := by simp [le_length]; omega
      have e := memBytesAt_snoc (b := (le 8 q)[j]) h.2.2 (by rw [hl, at_add]; exact hdm u h.1 _ hin) (by omega)
      rw [hl, at_add] at e
      rw [List.take_add_one, List.getElem?_eq_getElem hlt, Option.toList_some, byteOf_eq q j (by omega),
        ← le_get 8 q j hlt]
      exact e
  -- the type, after the offset
  let R (u : PancakeState σ) : Prop := MBase A s0 F t pl.length u ∧ u.locals "p" = some (at_ A sMessage) ∧
    memBytesAt u.memory u.memaddrs u.be (at_ A sMessage) (le 8 q ++ [BitVec.ofNat 8 t])
  have hRc : Safe.ClockFree R := fun _ _ ⟨h1, h2, h3⟩ => ⟨mbase_clock hFc _ _ h1, h2, h3⟩
  have h8in : sMessage + 8 < ScanProg.size := by decide
  have f3 : Frag o [.storeb (Syntax.atOff (Syntax.v "p") 8) (Syntax.v "jt")] (Q 8) R :=
    storeb_frag o (D := .op .add (.var "p") (.const (BitVec.ofNat 64 8))) rfl rfl hRc fun u h => by
      have hmw : MsgW A (byteAlign (at_ A (sMessage + 8))) := msg_align hA (by decide)
      refine ⟨_, _, by simp only [eval, h.2.1, at_add], by simp only [eval]; exact h.1.2.2.1,
        hdm u h.1 _ h8in, mbase_put hF h.1 hmw _, h.2.1, ?_⟩
      have hl8 : (le 8 q).take 8 = le 8 q := List.take_of_length_le (by simp [le_length])
      have hm := h.2.2
      rw [hl8] at hm
      have hd8 : u.memaddrs (byteAlign (at_ A sMessage + BitVec.ofNat 64 (le 8 q).length)) = true := by
        rw [le_length, at_add]; exact hdm u h.1 _ h8in
      have e := memBytesAt_snoc (b := BitVec.ofNat 8 t) hm hd8 (by simp [le_length])
      rw [le_length, at_add] at e
      rw [setWidth_ofNat_8]
      exact e
  -- the payload, octet by octet
  let I (i : Nat) (u : PancakeState σ) : Prop := MBase A s0 F t pl.length u ∧ u.locals "p" = some (at_ A sMessage) ∧
    u.locals "ji" = some (BitVec.ofNat 64 i) ∧ i ≤ pl.length ∧
    memBytesAt u.memory u.memaddrs u.be (at_ A sMessage) (le 8 q ++ BitVec.ofNat 8 t :: pl.take i)
  have hIc : ∀ i, Safe.ClockFree (I i) := fun _ _ _ ⟨h1, h2, h3, h4, h5⟩ => ⟨mbase_clock hFc _ _ h1, h2, h3, h4, h5⟩
  have f4 : Frag o [.assign "ji" (lit 0)] R (I 0) :=
    set_frag o (E := .op .add (.var "jz") (.const 0)) rfl (hIc 0) fun u h => by
      refine ⟨0, by simp [eval, hlocal u h.1 "jz" (by decide), hjz], kept_has h.1.1 (hbound _ (by decide)),
        mbase_set hF h.1 (by decide) _, by simp [setL, setLocal, h.2.1], by simp [setL, setLocal],
        Nat.zero_le _, by simpa [setL] using h.2.2⟩
  have hbody : ∀ i, decide (i < pl.length) = true → Frag o [.storeb (Syntax.eAdd (Syntax.atOff (Syntax.v "p") 9)
      (Syntax.v "ji")) (ScanProg.byte (Syntax.eAdd (Syntax.atOff (Syntax.v "jf") headerLength) (Syntax.v "ji"))),
      ScanProg.inc "ji"] (I i) (I (i + 1)) := fun i hi => by
    simp only [decide_eq_true_eq] at hi
    let M (u : PancakeState σ) : Prop := MBase A s0 F t pl.length u ∧ u.locals "p" = some (at_ A sMessage) ∧
      u.locals "ji" = some (BitVec.ofNat 64 i) ∧
      memBytesAt u.memory u.memaddrs u.be (at_ A sMessage) (le 8 q ++ BitVec.ofNat 8 t :: pl.take (i + 1))
    have hMc : Safe.ClockFree M := fun _ _ ⟨h1, h2, h3, h4⟩ => ⟨mbase_clock hFc _ _ h1, h2, h3, h4⟩
    have hin : sMessage + (9 + i) < ScanProg.size := by have := nums; omega
    have g1 : Frag o [.storeb (Syntax.eAdd (Syntax.atOff (Syntax.v "p") 9) (Syntax.v "ji"))
        (ScanProg.byte (Syntax.eAdd (Syntax.atOff (Syntax.v "jf") headerLength) (Syntax.v "ji")))] (I i) M :=
      storeb_frag o (D := .op .add (.op .add (.var "p") (.const (BitVec.ofNat 64 9))) (.var "ji"))
        (E := .loadByte (.op .add (.op .add (.var "jf") (.const (BitVec.ofNat 64 headerLength))) (.var "ji"))) rfl rfl
        hMc fun u h => by
      have hmw : MsgW A (byteAlign (at_ A (sMessage + (9 + i)))) := msg_align hA (by have := nums; omega)
      have hwin : sWindow + o' + 13 + i < 2 ^ 63 := by have := nums; omega
      have hbyte : memLoadByte u.memory u.memaddrs u.be (at_ A (sWindow + o' + 13 + i)) = some pl[i] := by
        rw [kept_load h.1.1 (not_msg hA (Or.inr (by omega)) hwin)]; exact hb i hi
      have hd : eval u (.op .add (.op .add (.var "p") (.const (BitVec.ofNat 64 9))) (.var "ji")) =
          some (at_ A (sMessage + (9 + i))) := by
        simp only [eval, h.2.1, h.2.2.1, at_add, Nat.add_assoc]
      have hv : eval u (.loadByte (.op .add (.op .add (.var "jf") (.const (BitVec.ofNat 64 headerLength)))
          (.var "ji"))) = some ((pl[i]).setWidth 64) := by
        simp only [eval, hlocal u h.1 "jf" (by decide), hjf, h.2.2.1, at_add, headerLength, hbyte]
      refine ⟨_, _, hd, hv, hdm u h.1 _ hin, mbase_put hF h.1 hmw _, h.2.1, h.2.2.1, ?_⟩
      have hl : (le 8 q ++ BitVec.ofNat 8 t :: pl.take i).length = 9 + i := by
        simp [le_length]; omega
      have e := memBytesAt_snoc (b := pl[i]) h.2.2.2.2 (by rw [hl, at_add]; exact hdm u h.1 _ hin) (by omega)
      rw [hl, at_add] at e
      rw [Bytes.setWidth64_8, List.take_add_one, List.getElem?_eq_getElem hi, Option.toList_some]
      simpa using e
    have g2 : Frag o [ScanProg.inc "ji"] M (I (i + 1)) :=
      set_frag o (E := .op .add (.var "ji") (.const 1)) rfl (hIc (i + 1)) fun u h => by
        refine ⟨BitVec.ofNat 64 (i + 1), by simp only [eval, h.2.2.1]; rw [BitVec.ofNat_add]; rfl, ⟨_, h.2.2.1⟩,
          mbase_set hF h.1 (by decide) _, by simp [setL, setLocal, h.2.1], by simp [setL, setLocal], by omega,
          by simpa [setL] using h.2.2.2⟩
    exact frag_append (xs := [_]) g1 g2
  have hlowb : LowKK [.storeb (Syntax.eAdd (Syntax.atOff (Syntax.v "p") 9) (Syntax.v "ji"))
      (ScanProg.byte (Syntax.eAdd (Syntax.atOff (Syntax.v "jf") headerLength) (Syntax.v "ji"))), ScanProg.inc "ji"] :=
    lowK_any _ (k := .skip) (c := _) rfl
  have f5 := frag_count o (c := Syntax.eLt (Syntax.v "ji") (Syntax.v "jpl")) (C := .cmp .less (.var "ji") (.var "jpl"))
    rfl hlowb hIc (fun _ _ _ _ _ hy => by simp [declared, ScanProg.inc] at hy) (g := fun i => decide (i < pl.length))
    (fun i u h => by
      rw [eval_lt (x := i) (y := pl.length) (by have := nums; omega) (by have := nums; omega)
        (by simp only [eval]; exact h.2.2.1)
        (by simp only [eval]; exact h.1.2.2.2)]
      simp [bw]) hbody 0
  -- and the message's length
  have f6 : Frag o [.assign "n" (Syntax.eAdd (Syntax.v "jpl") (Syntax.n 9))] (fun u => ∃ i, I i u ∧
      decide (i < pl.length) = false)
      (fun u => MBase A s0 F t pl.length u ∧ u.locals "p" = some (at_ A sMessage) ∧
        u.locals "n" = some (BitVec.ofNat 64 (pl.length + 9)) ∧
        memBytesAt u.memory u.memaddrs u.be (at_ A sMessage) (le 8 q ++ BitVec.ofNat 8 t :: pl)) :=
    set_frag o (E := .op .add (.var "jpl") (.const 9)) rfl
      (fun _ _ ⟨h1, h2, h3, h4⟩ => ⟨mbase_clock hFc _ _ h1, h2, h3, h4⟩) fun u ⟨i, h, hz⟩ => by
      have hi : i = pl.length := by simp only [decide_eq_false_iff_not] at hz; omega
      subst hi
      refine ⟨BitVec.ofNat 64 (pl.length + 9), by simp only [eval, h.1.2.2.2, BitVec.ofNat_add]; rfl,
        kept_has h.1.1 (hbound _ (by decide)),
        mbase_set hF h.1 (by decide) _, by simp [setL, setLocal, h.2.1], by simp [setL, setLocal], ?_⟩
      have := h.2.2.2.2
      rw [List.take_length] at this
      simpa [setL] using this
  exact frag_append (frag_append f1 (f2 8 (Nat.le_refl _)))
    (frag_append (xs := [_]) f3 (frag_append (xs := [_]) f4 (frag_append (xs := [_]) f5 f6)))

end Message

/-! ## The tag -/

/-- The locals the hash sets. -/
def sipNames : List String := ["r", "m", "v0", "v1", "v2", "v3", "off", "j"]

/-- The hash's program is one, whatever its annotations say. -/
theorem sip_erase (kv pv : Word) (key msg : Bytes) :
    (SipHashCode.sipA (σ := σ) kv pv key msg).erase = (SipHashCode.sipA (σ := Unit) 0 0 [] []).erase :=
  Option.some.inj ((SipHashCode.sip_lowering kv pv key msg).symm.trans (SipHashCode.sip_lowering 0 0 [] []))

theorem sip_assigned (kv pv : Word) (key msg : Bytes) :
    ∀ y ∈ WpRet.assigned (SipHashCode.sipA (σ := σ) kv pv key msg).erase, y ∈ sipNames :=
  WpRet.setsOnly_sound _ _ (by rw [sip_erase]; decide +kernel)

/-- **The hash, run from one state**: if it goes on, `r` holds the tag, and what `Kept sipNames` allows keeps `G`. -/
theorem sip_run (o : Oracle σ) {kv pv : Word} {key msg : Bytes} (hlen : msg.length < 2 ^ 62) {G : Assn σ}
    (hG : Stable sipNames (fun _ => False) G) {s : PancakeState σ} (hs : SipHashCode.SipPre kv pv key msg s)
    (hg : G s) (hGc : Safe.ClockFree G) :
    Safe.Safe o (Like s) (SipHashCode.sipA (σ := σ) kv pv key msg).erase
      (fun t => G t ∧ t.locals "r" = some (SipHash.tag key msg).toBitVec) := by
  intro u hu
  have hu' : SipHashCode.SipPre kv pv key msg u := by rw [like_eq hu]; exact hs
  have hgu : G u := by rw [like_eq hu]; exact hGc _ _ hg
  have k := SipHashCode.sip_safe o kv pv key msg hlen u hu'
  have hnw : WpRet.noWrite (SipHashCode.sipA (σ := σ) kv pv key msg).erase = true := by
    rw [sip_erase]
    decide +kernel
  have hm := WpRet.noWrite_run o u.clock _ u (Nat.le_refl _) hnw
  have hl := WpRet.noWrite_locals o u.clock _ u (Nat.le_refl _) hnw
  have hsame := Safe.sem_same o u.clock (SipHashCode.sipA (σ := σ) kv pv key msg).erase u (Nat.le_refl _)
  have hk := Safe.sem_keeps o u.clock (SipHashCode.sipA (σ := σ) kv pv key msg).erase u (Nat.le_refl _)
  revert k hm hl hsame hk
  rcases PancakeSem o (SipHashCode.sipA (σ := σ) kv pv key msg).erase u with ⟨_ | r, t⟩
  · intro k hm hl hsame hk
    obtain ⟨hf, hloc⟩ := hl trivial
    refine ⟨hG u t hgu ⟨fun x hx => hloc x fun h => hx (sip_assigned kv pv key msg x h), fun a _ => by
      simp only at hm; rw [hm], hsame.1, hsame.2.2.1, hsame.2.1, hf, hsame.2.2.2, hk trivial⟩, k⟩
  · intro k _ _ _ _; exact k

theorem sip_ne : SipProg.sipSrc ≠ [] := fun h => by cases h

theorem sip_noDec : ∀ x ∈ SipProg.sipSrc, x.isDec = false := by
  have h : SipProg.sipSrc.all (fun x => !x.isDec) = true := by decide +kernel
  intro x hx
  simpa using List.all_eq_true.mp h x hx

/-- The hash lowers before whatever follows, as `SipHashCode.sip_lowering` lowers it. -/
theorem lowKK_sip : LowKK SipProg.sipSrc := fun k =>
  match lowerK_fold (σ := Unit) Oracle.idle SipProg.sipSrc sip_ne sip_noDec
    (SipHashCode.sip_lowering (σ := Unit) 0 0 [] []) k with
  | ⟨c, hc, _⟩ => ⟨c, hc⟩

/-- **The hash as a fragment.** -/
theorem sip_frag (o : Oracle σ) {kv pv : Word} {key msg : Bytes} (hlen : msg.length < 2 ^ 62) {G : Assn σ}
    (hG : Stable sipNames (fun _ => False) G) (hGc : Safe.ClockFree G) :
    Frag o SipProg.sipSrc (fun u => SipHashCode.SipPre kv pv key msg u ∧ G u)
      (fun t => G t ∧ t.locals "r" = some (SipHash.tag key msg).toBitVec) :=
  frag_each o lowKK_sip fun s ⟨hs, hg⟩ =>
    frag_fold o sip_ne sip_noDec (SipHashCode.sip_lowering kv pv key msg)
      (fun _ _ ⟨h1, h2⟩ => ⟨hGc _ _ h1, h2⟩) fun R => WpRet.ofSafe R (by
        rw [sip_erase]
        decide +kernel) (sip_run o hlen hG hs hg hGc)

/-! ## Octets compared with a text -/

theorem foldAnd_eval {u : PancakeState σ} : ∀ (es : List Syntax.PExpr) (qs : List Bool) (acc : Syntax.PExpr)
    (ACC : PancakeExp) (pa : Bool), Lower.lowerExp acc = some ACC → eval u ACC = some (bw pa) →
    es.length = qs.length →
    (∀ i (h : i < es.length) (h' : i < qs.length), ∃ E, Lower.lowerExp es[i] = some E ∧ eval u E = some (bw qs[i])) →
    ∃ E, Lower.lowerExp (es.foldl Syntax.eAnd acc) = some E ∧ eval u E = some (bw (pa && qs.all id))
  | [], [], _, ACC, pa, hacc, hev, _, _ => ⟨ACC, hacc, by simpa using hev⟩
  | [], _ :: _, _, _, _, _, _, hl, _ => by simp at hl
  | _ :: _, [], _, _, _, _, _, hl, _ => by simp at hl
  | e :: es, q :: qs, acc, ACC, pa, hacc, hev, hl, he => by
    obtain ⟨E, hE, hEv⟩ := he 0 (by simp) (by simp)
    have hE' : Lower.lowerExp e = some E := by simpa using hE
    have hEv' : eval u E = some (bw q) := by simpa using hEv
    obtain ⟨F, hF, hFv⟩ := foldAnd_eval es qs (Syntax.eAnd acc e) (.op .and_ ACC E) (pa && q)
      (by simp [Syntax.eAnd, Lower.lowerExp, hacc, hE']) (eval_and hev hEv') (by simpa using hl)
      fun i h h' => he (i + 1) (by simp; omega) (by simp; omega)
    refine ⟨F, by simpa using hF, ?_⟩
    rw [hFv]
    simp [Bool.and_assoc]

theorem all_zipWith_eq : ∀ (ys bs : List (BitVec 8)), ys.length = bs.length →
    (List.zipWith (fun y b => decide (y = b)) ys bs).all id = decide (ys = bs)
  | [], [], _ => rfl
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | y :: ys, b :: bs, h => by
    simp only [List.zipWith_cons_cons, List.all_cons, id, all_zipWith_eq ys bs (by simpa using h),
      List.cons.injEq]
    by_cases e : y = b <;> simp [e]

/-- **Octets in memory compared with a text**, as `bytesAre` makes the test. -/
theorem bytesAre_eval {u : PancakeState σ} {p : Syntax.PExpr} {P : PancakeExp} (hp : Lower.lowerExp p = some P)
    {a : Word} (hP : eval u P = some a) {ys bs : Bytes} (hl : ys.length = bs.length)
    (hy : ∀ i (h : i < ys.length), memLoadByte u.memory u.memaddrs u.be (a + BitVec.ofNat 64 i) = some ys[i]) :
    ∃ E, Lower.lowerExp (ScanProg.bytesAre p bs) = some E ∧ eval u E = some (bw (decide (ys = bs))) := by
  obtain ⟨E, hE, hv⟩ := foldAnd_eval (u := u) (bs.zipIdx.map fun (b, i) => Syntax.eEq (ScanProg.byte (Syntax.atOff p i))
    (Syntax.n b.toNat)) (List.zipWith (fun y b => decide (y = b)) ys bs) (Syntax.n 1) (.const 1) true rfl rfl
    (by simp [hl]) fun i h h' => by
      have hi : i < bs.length := by simpa using h
      have hiy : i < ys.length := by omega
      have hA : eval u (if i = 0 then P else .op .add P (.const (BitVec.ofNat 64 i))) =
          some (a + BitVec.ofNat 64 i) := by
        by_cases h0 : i = 0
        · subst h0; simp [hP]
        · simp [h0, eval, hP]
      refine ⟨.cmp .equal (.loadByte (if i = 0 then P else .op .add P (.const (BitVec.ofNat 64 i))))
        (.const (BitVec.ofNat 64 bs[i].toNat)), ?_, ?_⟩
      · simp [Syntax.eEq, ScanProg.byte, Syntax.n, Lower.lowerExp, atOff_lower hp i]
      · simp only [List.getElem_zipWith, eval, hA, hy i hiy]
        have hk := bs[i].isLt
        have hb : BitVec.ofNat 8 bs[i].toNat = bs[i] := by simp
        rw [show (if (ys[i]).setWidth 64 = BitVec.ofNat 64 bs[i].toNat then (1 : Word) else 0) =
          bw (decide (ys[i] = bs[i])) by
            by_cases e : ys[i] = bs[i]
            · rw [if_pos ((FramerCode.widen_eq _ _ hk).mpr (e.trans hb.symm))]; simp [bw, e]
            · rw [if_neg (fun h => e (((FramerCode.widen_eq _ _ hk).mp h).trans hb))]; simp [bw, e]]
  exact ⟨E, hE, by rw [hv, Bool.true_and, all_zipWith_eq ys bs hl]⟩

/-- Octets in words a run left alone read as they did. -/
theorem read_kept {xs : List String} {w : Word → Prop} {u u' : PancakeState σ} (h : Kept xs w u u') (n : Nat) (a : Word)
    (hw : ∀ i, i < n → ¬ w (byteAlign (a + BitVec.ofNat 64 i))) :
    readByteArray u'.memory u'.memaddrs u'.be a n = readByteArray u.memory u.memaddrs u.be a n := by
  rw [← h.memaddrs, ← h.be]
  exact readByteArray_congr n a fun j hj => by
    have e := kept_load h (hw j hj); rwa [h.memaddrs, h.be] at e ⊢

/-! ## The key a frame is checked under -/

theorem keyIn_eq (t : Nat) (pl : Bytes) : keyIn spec t pl =
    if t = formatType ∧ pl.length = 36 ∧ pl.take 19 = journalTitle then some (pl.drop 20) else none := by
  have hm : magic.length = 20 := rfl
  have hk : keyLength = 16 := rfl
  have ht : journalTitle.length = 19 := rfl
  simp only [keyIn, spec_shaped, Bool.not_true, Bool.false_eq_true, if_false, hm, hk, ht, beq_iff_eq, Bool.and_eq_true,
    and_assoc]

/-- What the key a frame is checked under leaves: `jhk` one when there is one, and `k` naming it, in the area's
key or the frame's payload at `F`. -/
def KeyOut (A F : Word) (eff : Option Bytes) (u : PancakeState σ) : Prop :=
  u.locals "jhk" = some (bw eff.isSome) ∧
    ∀ kk, eff = some kk → ∃ kv, u.locals "k" = some kv ∧ (kv = at_ A sKey ∨ kv = F + BitVec.ofNat 64 33) ∧
      readByteArray u.memory u.memaddrs u.be kv 16 = some kk

/-- What `keySel` reads, each from a state the premise holds in. -/
structure KeyIn (A F : Word) (key : Option Bytes) (t : Nat) (pl : Bytes) (u : PancakeState σ) : Prop where
  sp : u.locals "jsc" = some A
  jz : u.locals "jz" = some 0
  key : ∀ kk, key = some kk → readByteArray u.memory u.memaddrs u.be (at_ A sKey) 16 = some kk
  jt : u.locals "jt" = some (BitVec.ofNat 64 t)
  jpl : u.locals "jpl" = some (BitVec.ofNat 64 pl.length)
  jf : u.locals "jf" = some F
  payload : ∀ i (h : i < pl.length), memLoadByte u.memory u.memaddrs u.be (F + BitVec.ofNat 64 (13 + i)) = some pl[i]
  k : ∃ v, u.locals "k" = some v
  jhk : ∃ v, u.locals "jhk" = some v
  short : pl.length < 2 ^ 62

/-- **The key a frame is checked under**: the journal's, or before it is read, the key a frame of the
format's shape carries. -/
theorem keySel_frag (o : Oracle σ) {A F : Word} {key : Option Bytes} {t : Nat} {pl : Bytes} {P : Assn σ}
    (hPc : Safe.ClockFree P) (hPs : ∀ u x v, P u → x ∈ ["k", "jhk"] → P (setL u x v))
    (hin : ∀ u, P u → KeyIn A F key t pl u) (hjky : ∀ u, P u → u.locals "jky" = some (bw key.isSome))
    (ht : t < 256) :
    Frag o (ScanProg.keySel false) P (fun u => P u ∧ KeyOut A F (key <|> keyIn spec t pl) u) := by
  have hQc : Safe.ClockFree (fun u => P u ∧ KeyOut A F (key <|> keyIn spec t pl) u) :=
    fun _ _ ⟨h1, h2⟩ => ⟨hPc _ _ h1, h2⟩
  -- the journal's key, and whether there is one
  let M (u : PancakeState σ) : Prop := P u ∧ u.locals "k" = some (at_ A sKey) ∧
    u.locals "jhk" = some (bw key.isSome)
  have hMc : Safe.ClockFree M := fun _ _ ⟨h1, h2, h3⟩ => ⟨hPc _ _ h1, h2, h3⟩
  have f1 : Frag o [.assign "k" (Syntax.atOff sp sKey), .assign "jhk" (Syntax.v "jky")] P M := by
    refine frag_append (xs := [_]) (set_frag o (E := .op .add (.var "jsc") (.const (BitVec.ofNat 64 sKey))) rfl
      (P' := fun u => P u ∧ u.locals "k" = some (at_ A sKey))
      (fun _ _ ⟨h1, h2⟩ => ⟨hPc _ _ h1, h2⟩) fun u h => ⟨at_ A sKey, by simp [eval, (hin u h).sp, at_],
        (hin u h).k, hPs u _ _ h (by decide), by simp [setL, setLocal]⟩)
      (set_frag o (E := .var "jky") rfl hMc fun u h => ⟨bw key.isSome, by simp [eval, hjky u h.1],
        (hin u h.1).jhk, hPs u _ _ h.1 (by decide), by simp [setL, setLocal, h.2], by simp [setL, setLocal]⟩)
  have hrest : Frag o [.ite (Syntax.v "jky") [] [.ite (Syntax.eAnd (Syntax.eEq (Syntax.v "jt") (Syntax.n formatType))
      (Syntax.eEq (Syntax.v "jpl") (Syntax.n (magic.length + keyLength))))
      [.ite (ScanProg.bytesAre (Syntax.atOff (Syntax.v "jf") headerLength) journalTitle)
        [.assign "k" (Syntax.atOff (Syntax.v "jf") (headerLength + magic.length)), .assign "jhk" (lit 1)] []] []]]
      M (fun u => P u ∧ KeyOut A F (key <|> keyIn spec t pl) u) := by
    refine frag_ite o (C := .var "jky") rfl hQc (fun s h => ⟨_, hjky s h.1⟩) ?_
      (fun _ _ _ _ h => by simp [declared] at h) ?_ (fun _ _ _ _ h => by simp [declared] at h)
    · -- the journal's key is known
      refine frag_nil o fun u ⟨h, hne⟩ => ?_
      simp only [eval] at hne
      rw [hjky u h.1] at hne
      cases hk : key with
      | none => rw [hk] at hne; exact absurd rfl hne
      | some kk =>
        refine ⟨h.1, by rw [h.2.2, hk]; rfl, fun k' e => ?_⟩
        rw [show (some kk <|> keyIn spec t pl) = some kk from rfl, Option.some.injEq] at e
        subst e
        exact ⟨_, h.2.1, Or.inl rfl, (hin u h.1).key kk hk⟩
    · -- before the journal's key: a frame of the format's shape carries one
      have hnone : ∀ u, M u → eval u (.var "jky") = some 0 → key = none := fun u h h0 => by
        simp only [eval] at h0
        rw [hjky u h.1] at h0
        cases hk : key with
        | none => rfl
        | some _ => rw [hk] at h0; simp [bw] at h0
      have hshort := fun u (h : M u) => (hin u h.1).short
      have hjl : journalTitle.length = 19 := rfl
      have htest : ∀ u, M u → eval u (.op .and_ (.cmp .equal (.var "jt") (.const (BitVec.ofNat 64 1)))
          (.cmp .equal (.var "jpl") (.const (BitVec.ofNat 64 36)))) =
        some (bw (decide (t = 1) && decide (pl.length = 36)))
          := fun u h =>
        eval_and (eval_eq (x := t) (y := 1) (by omega) (by decide) (by simp only [eval]; exact (hin u h.1).jt) rfl)
          (eval_eq (x := pl.length) (y := 36) (by have := hshort u h; omega) (by decide)
            (by simp only [eval]; exact (hin u h.1).jpl) rfl)
      have hkeyIn : ∀ u, M u → eval u (.var "jky") = some 0 → (key <|> keyIn spec t pl) = keyIn spec t pl :=
        fun u h h0 => by rw [hnone u h h0]; rfl
      refine frag_ite o (C := .op .and_ (.cmp .equal (.var "jt") (.const (BitVec.ofNat 64 1)))
        (.cmp .equal (.var "jpl") (.const (BitVec.ofNat 64 36)))) rfl hQc (fun s h => ⟨_, htest s h.1⟩) ?_
        (fun _ _ _ _ h => by simp [declared] at h) (frag_nil o fun u ⟨⟨h, h0⟩, hz⟩ => ?_)
        (fun _ _ _ _ h => by simp [declared] at h)
      · refine frag_pure (t = 1 ∧ pl.length = 36) (fun u ⟨⟨h, h0⟩, hne⟩ => by
          rw [htest u h] at hne
          simpa using bw_ne0 hne) (lowK_any _ (k := .skip) (c := _) rfl) fun ⟨h1, h36⟩ => ?_
        have hev : ∀ u, M u → ∃ E, Lower.lowerExp (ScanProg.bytesAre (Syntax.atOff (Syntax.v "jf") headerLength)
            journalTitle) = some E ∧ eval u E = some (bw (decide (pl.take 19 = journalTitle))) := fun u h =>
          bytesAre_eval (P := .op .add (.var "jf") (.const (BitVec.ofNat 64 13))) rfl
            (by simp only [eval, (hin u h.1).jf]; rfl) (by simp [h36, hjl]) fun i hi => by
              have hi' : i < pl.length := by simp at hi; omega
              rw [add_ofNat, (hin u h.1).payload i hi', List.getElem_take]
        obtain ⟨E, hE⟩ : ∃ E, Lower.lowerExp (ScanProg.bytesAre (Syntax.atOff (Syntax.v "jf") headerLength)
            journalTitle) = some E := ⟨_, rfl⟩
        have hEv : ∀ u, M u → eval u E = some (bw (decide (pl.take 19 = journalTitle))) := fun u h => by
          obtain ⟨E', hE', hv⟩ := hev u h
          rw [hE] at hE'; cases hE'; exact hv
        have hshape : key = none →
            (key <|> keyIn spec t pl) = if pl.take 19 = journalTitle then some (pl.drop 20) else none :=
          fun hn => by
            rw [hn, show (none <|> keyIn spec t pl) = keyIn spec t pl from rfl, keyIn_eq]
            by_cases e : pl.take 19 = journalTitle
            · rw [if_pos ⟨h1, h36, e⟩, if_pos e]
            · rw [if_neg (fun ⟨_, _, e'⟩ => e e'), if_neg e]
        refine frag_ite o (C := E) hE hQc (fun s h => ⟨_, hEv s h.1.1⟩) ?_
          (fun _ _ _ _ h => by simp [declared] at h) (frag_nil o fun u ⟨⟨⟨h, h0⟩, _⟩, hz⟩ => ?_)
          (fun _ _ _ _ h => by simp [declared] at h)
        · refine frag_append (xs := [_]) (set_frag o (E := .op .add (.var "jf")
            (.const (BitVec.ofNat 64 (headerLength + magic.length)))) rfl
            (P' := fun u => P u ∧ key = none ∧ pl.take 19 = journalTitle ∧
              u.locals "k" = some (F + BitVec.ofNat 64 33))
            (fun _ _ ⟨h1, h2, h3, h4⟩ => ⟨hPc _ _ h1, h2, h3, h4⟩) fun u ⟨⟨⟨h, h0⟩, _⟩, hne⟩ => ?_)
            (set_frag o (E := .op .add (.var "jz") (.const 1)) rfl hQc fun u ⟨h, hn, ht19, hk⟩ => ?_)
          · rw [hEv u h] at hne
            have ht19 := bw_ne0 hne
            simp only [decide_eq_true_eq] at ht19
            refine ⟨F + BitVec.ofNat 64 33, by simp only [eval, (hin u h.1).jf]; rfl, (hin u h.1).k,
              hPs u _ _ h.1 (by decide), hnone u h h0, ht19, by simp [setL, setLocal]⟩
          · refine ⟨1, by simp [eval, (hin u h).jz], (hin u h).jhk, hPs u _ _ h (by decide), ?_⟩
            rw [hshape hn, if_pos ht19]
            refine ⟨by simp [setL, setLocal, bw], fun kk e => ?_⟩
            rw [Option.some.injEq] at e
            subst e
            refine ⟨F + BitVec.ofNat 64 33, by simp [setL, setLocal, hk], Or.inr rfl, ?_⟩
            have hd : (pl.drop 20).length = 16 := by simp [h36]
            rw [← hd]
            refine read_of_bytes _ _ fun i hi => ?_
            have hi' : 20 + i < pl.length := by simp at hi; omega
            simp only [setL]
            rw [add_ofNat, show 33 + i = 13 + (20 + i) by omega, (hin u h).payload _ hi', List.getElem_drop]
        · -- the title is not the journal's: no key
          rw [hEv u h] at hz
          have hf := bw_eq0 hz
          simp only [decide_eq_false_iff_not] at hf
          rw [hshape (hnone u h h0), if_neg hf]
          exact ⟨h.1, by rw [h.2.2, hnone u h h0], fun _ e => by cases e⟩
      · -- not of the format's shape: no key
        have hk := hkeyIn u h h0
        rw [htest u h] at hz
        have hf := bw_eq0 hz
        have hn : keyIn spec t pl = none := by
          rw [keyIn_eq, if_neg (fun ⟨e1, e2, _⟩ => by simp [e1, e2, formatType] at hf)]
        refine ⟨h.1, ?_, fun kk e => ?_⟩
        · rw [hk, hn, h.2.2, hnone u h h0]
        · rw [hk, hn] at e
          cases e
  exact frag_append (xs := [_, _]) f1 hrest

/-- …and with the journal's key known, that key. -/
theorem keySelK_frag (o : Oracle σ) (keyed : Bool) {A F : Word} {key : Option Bytes} {t : Nat} {pl : Bytes}
    {P : Assn σ} (hPc : Safe.ClockFree P) (hPs : ∀ u x v, P u → x ∈ ["k", "jhk"] → P (setL u x v))
    (hin : ∀ u, P u → KeyIn A F key t pl u) (hjky : keyed = false → ∀ u, P u → u.locals "jky" = some (bw key.isSome))
    (hkeyed : keyed = true → key.isSome = true) (ht : t < 256) :
    Frag o (ScanProg.keySel keyed) P (fun u => P u ∧ KeyOut A F (key <|> keyIn spec t pl) u) := by
  cases keyed with
  | false => exact keySel_frag o hPc hPs hin (hjky rfl) ht
  | true =>
    obtain ⟨kk, hk⟩ := Option.isSome_iff_exists.mp (hkeyed rfl)
    have hQc : Safe.ClockFree (fun u => P u ∧ KeyOut A F (key <|> keyIn spec t pl) u) :=
      fun _ _ ⟨h1, h2⟩ => ⟨hPc _ _ h1, h2⟩
    refine frag_append (xs := [_]) (set_frag o (E := .op .add (.var "jsc") (.const (BitVec.ofNat 64 sKey))) rfl
      (P' := fun u => P u ∧ u.locals "k" = some (at_ A sKey))
      (fun _ _ ⟨h1, h2⟩ => ⟨hPc _ _ h1, h2⟩) fun u h => ⟨at_ A sKey, by simp [eval, (hin u h).sp, at_],
        (hin u h).k, hPs u _ _ h (by decide), by simp [setL, setLocal]⟩)
      (set_frag o (E := .op .add (.var "jz") (.const 1)) rfl hQc fun u h => ⟨1, by simp [eval, (hin u h.1).jz],
        (hin u h.1).jhk, hPs u _ _ h.1 (by decide), ?_⟩)
    rw [hk, show (some kk <|> keyIn spec t pl) = some kk from rfl]
    refine ⟨by simp [setL, setLocal, bw], fun k' e => ?_⟩
    rw [Option.some.injEq] at e
    subst e
    exact ⟨at_ A sKey, by simp [setL, setLocal, h.2], Or.inl rfl, by simpa [setL] using (hin u h.1).key kk hk⟩

/-! ## The check of a frame -/

/-- What `frameWhy` gives for what `fault` finds: zero, or the code of the reason. -/
def codeOf : Option Why → Nat
  | none => 0
  | some w => whyCode w

theorem codeOf_zero {f : Option Why} : codeOf f = 0 ↔ f = none := by
  cases f with
  | none => simp [codeOf]
  | some w => cases w <;> simp [codeOf, whyCode]

theorem codeOf_lt {f : Option Why} : codeOf f < 2 ^ 64 := by
  cases f with
  | none => simp [codeOf]
  | some w => cases w <;> simp [codeOf, whyCode]

/-- What `frameWhy` reads: the area at `A`, the frame at journal offset `q` and `o'` octets into the window, the
journal's octets from it `bs`, the first `maxFrame` of them in the window, and the journal's key once read. -/
structure FwIn (keyed : Bool) (A : Word) (key : Option Bytes) (q o' : Nat) (bs : Bytes) (s : PancakeState σ) :
    Prop where
  hA : A.toNat % 8 = 0
  dom : Dom A s.memaddrs
  sp : s.locals "jsc" = some A
  jz : s.locals "jz" = some 0
  jq : s.locals "jq" = some (BitVec.ofNat 64 q)
  jf : s.locals "jf" = some (at_ A (sWindow + o'))
  jr : s.locals "jr" = some (BitVec.ofNat 64 bs.length)
  jky : keyed = false → s.locals "jky" = some (bw key.isSome)
  keyed : keyed = true → key.isSome = true
  key : ∀ kk, key = some kk → readByteArray s.memory s.memaddrs s.be (at_ A sKey) 16 = some kk
  bytes : ∀ i (h : i < bs.length), i < maxFrame →
    memLoadByte s.memory s.memaddrs s.be (at_ A (sWindow + o' + i)) = some bs[i]
  room : o' + maxFrame ≤ windowRoom
  q : q < 2 ^ 62
  len : bs.length < 2 ^ 62
  bound : ∀ y ∈ fwNames, ∃ v, s.locals y = some v

/-- What `frameWhy` leaves: `jwhy` the code of what `fault` finds, and of a frame that checks, the payload's
length in `jpl` and the type in `jt`; the other locals as they were, and the memory but the message. -/
structure FwOut (A : Word) (key : Option Bytes) (q : Nat) (bs : Bytes) (s0 u : PancakeState σ) : Prop where
  kept : Kept fwNames (MsgW A) s0 u
  why : u.locals "jwhy" = some (BitVec.ofNat 64 (codeOf (fault key q bs)))
  len : fault key q bs = none → u.locals "jpl" = some (BitVec.ofNat 64 (readLE (bs.take 4)))
  type : fault key q bs = none → u.locals "jt" = some (BitVec.ofNat 64 (typeOf bs))

theorem fwOut_clock {A : Word} {key : Option Bytes} {q : Nat} {bs : Bytes} {s0 : PancakeState σ} :
    Safe.ClockFree (FwOut A key q bs s0) := fun _ _ h => { h with kept := { h.kept with } }

/-- `jwhy` given a code. -/
theorem why_frag (o : Oracle σ) {P Q : Assn σ} (hQ : Safe.ClockFree Q) (c : Nat)
    (h : ∀ u, P u → u.locals "jz" = some 0 ∧ (∃ v, u.locals "jwhy" = some v) ∧
      Q (setL u "jwhy" (BitVec.ofNat 64 c))) : Frag o [.assign "jwhy" (lit c)] P Q :=
  set_frag o (E := .op .add (.var "jz") (.const (BitVec.ofNat 64 c))) rfl hQ fun u hu => by
    obtain ⟨h1, h2, h3⟩ := h u hu
    exact ⟨_, by simp [eval, h1], h2, h3⟩

theorem kept_widen {xs ys : List String} {w w' : Word → Prop} {u u' : PancakeState σ} (h : Kept xs w u u')
    (hx : ∀ x ∈ xs, x ∈ ys) (hw : ∀ a, w a → w' a) : Kept ys w' u u' :=
  ⟨fun x hx' => h.locals x fun e => hx' (hx x e), fun a ha => h.memory a fun e => ha (hw a e), h.memaddrs, h.be,
    h.base, h.ffi, h.code, h.keeps⟩

theorem payload_length {bs : Bytes} (h : 13 + readLE (bs.take 4) + 1 ≤ bs.length) :
    (payloadOf bs).length = readLE (bs.take 4) := by
  simp only [payloadOf, headerLength, List.length_take, List.length_drop]; omega

theorem payload_get {bs : Bytes} (i : Nat) (h : i < (payloadOf bs).length) (h' : 13 + i < bs.length) :
    (payloadOf bs)[i] = bs[13 + i] := by
  simp only [payloadOf, headerLength, List.getElem_take, List.getElem_drop]

/-- What `fault` finds of a frame whose header checks: the tag, or nothing. -/
theorem fault_tag {key : Option Bytes} {q : Nat} {bs : Bytes} (h13 : 13 ≤ bs.length)
    (hmax : readLE (bs.take 4) ≤ maxPayload) (hend : 13 + readLE (bs.take 4) + 1 ≤ bs.length)
    (hmark : bs.getD (13 + readLE (bs.take 4)) 0 = endMark) :
    fault key q bs = if tagWrong (key <|> keyIn spec (typeOf bs) (payloadOf bs)) (readLE ((bs.drop 4).take 8)) q
      (typeOf bs) (payloadOf bs) then some .tag else none := by
  simp only [fault, headerLength]
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (fun h => h hmark)]

/-- The words of the key at `kv` are not the message's. -/
theorem key_apart {A F : Word} (hA : A.toNat % 8 = 0) {o' : Nat} (hF : F = at_ A (sWindow + o'))
    (ho : o' + maxFrame ≤ windowRoom) {kv : Word} (hkv : kv = at_ A sKey ∨ kv = F + BitVec.ofNat 64 33) :
    ∀ i, i < 16 → ¬ MsgW A (byteAlign (kv + BitVec.ofNat 64 i)) := fun i hi => by
  have := nums
  rcases hkv with rfl | rfl
  · rw [at_add]; exact not_msg hA (Or.inl (by omega)) (by omega)
  · rw [hF, at_add, at_add]; exact not_msg hA (Or.inr (by omega)) (by omega)

section Tag

variable {A : Word} {key : Option Bytes} {q o' : Nat} {bs : Bytes} {s0 : PancakeState σ} {keyed : Bool}

/-- Before the tag: the header checked, `jwhy` zero, the type and the length read, the key chosen. -/
def TagPre (A : Word) (key : Option Bytes) (o' : Nat) (bs : Bytes) (s0 u : PancakeState σ) : Prop :=
  Kept fwNames (MsgW A) s0 u ∧ u.locals "jwhy" = some 0 ∧ u.locals "jt" = some (BitVec.ofNat 64 (typeOf bs)) ∧
    u.locals "jpl" = some (BitVec.ofNat 64 (readLE (bs.take 4))) ∧
    KeyOut A (at_ A (sWindow + o')) (key <|> keyIn spec (typeOf bs) (payloadOf bs)) u

/-- **The tag**: none without a key; with one, the message written, its SipHash under the key, and the stored
tag compared with it. -/
theorem tag_frag (o : Oracle σ) (h : FwIn keyed A key q o' bs s0) (h13 : 13 ≤ bs.length)
    (hmax : readLE (bs.take 4) ≤ maxPayload) (hend : 13 + readLE (bs.take 4) + 1 ≤ bs.length)
    (hmark : bs.getD (13 + readLE (bs.take 4)) 0 = endMark) :
    Frag o ScanProg.tagPart (TagPre A key o' bs s0) (FwOut A key q bs s0) := by
  have hn := nums
  have hft := fault_tag (key := key) (q := q) h13 hmax hend hmark
  have hpl := payload_length hend
  have ht : typeOf bs < 256 := (bs.getD 12 0).isLt
  have hlocal : ∀ u, Kept fwNames (MsgW A) s0 u → ∀ y, y ∉ fwNames → u.locals y = s0.locals y :=
    fun u h y hy => h.locals y hy
  refine frag_ite o (C := .cmp .equal (.var "jhk") (.const 0)) rfl fwOut_clock
    (fun u hu => ⟨_, by simp only [eval, hu.2.2.2.2.1]; rfl⟩) ?_ (fun _ _ _ _ h => by simp [declared] at h) ?_
    (noDecl _ rfl)
  · -- no key: the tag cannot be checked
    refine why_frag o fwOut_clock _ fun u ⟨hu, hne⟩ => ?_
    simp only [eval, hu.2.2.2.2.1] at hne
    have hnone : (key <|> keyIn spec (typeOf bs) (payloadOf bs)) = none := by
      cases he : (key <|> keyIn spec (typeOf bs) (payloadOf bs)) with
      | none => rfl
      | some _ => rw [he] at hne; simp [bw] at hne
    have hf : fault key q bs = some .tag := by rw [hft, hnone]; rfl
    refine ⟨(hlocal u hu.1 "jz" (by decide)).trans h.jz, ⟨_, hu.2.1⟩, kept_set hu.1 (by decide) _, ?_,
      fun e => ?_, fun e => ?_⟩
    · simp [setL, setLocal, hf, codeOf, whyCode]
    · rw [hf] at e; cases e
    · rw [hf] at e; cases e
  · -- the key: the message, its tag, and the stored one
    have lall : LowKK (ScanProg.message ++ SipProg.sipSrc ++ ScanProg.leS "jtag" (Syntax.atOff (Syntax.v "jf") 4) 8 ++
        [.ite (ScanProg.ne (Syntax.v "r") (Syntax.v "jtag")) [.assign "jwhy" (lit (whyCode .tag))] []]) :=
      lowKK_append (lowKK_append (lowKK_append (lowK_any _ (k := .skip) (c := _) rfl) lowKK_sip)
        (lowK_any _ (k := .skip) (c := _) rfl)) (lowK_any _ (k := .skip) (c := _) rfl)
    cases heff : (key <|> keyIn spec (typeOf bs) (payloadOf bs)) with
    | none =>
      refine frag_unsat lall fun u ⟨hu, h0⟩ => ?_
      simp only [eval, hu.2.2.2.2.1, heff] at h0
      simp [bw] at h0
    | some kk =>
    have hroom : o' + 13 + (payloadOf bs).length ≤ windowRoom := by have := h.room; omega
    have hplb : (payloadOf bs).length ≤ maxPayload := by omega
    refine frag_conseq (P0 := fun u => ∃ kv, Kept fwNames (MsgW A) s0 u ∧ u.locals "jwhy" = some 0 ∧
        u.locals "jt" = some (BitVec.ofNat 64 (typeOf bs)) ∧
        u.locals "jpl" = some (BitVec.ofNat 64 (payloadOf bs).length) ∧
        u.locals "k" = some kv ∧ (kv = at_ A sKey ∨ kv = at_ A (sWindow + o') + BitVec.ofNat 64 33) ∧
        readByteArray u.memory u.memaddrs u.be kv 16 = some kk)
      (frag_exists lall fun kv => ?_) (fun u ⟨hu, _⟩ => match hu.2.2.2.2.2 kk heff with
        | ⟨kv, hk, hloc, hrd⟩ => ⟨kv, hu.1, hu.2.1, hu.2.2.1, hpl ▸ hu.2.2.2.1, hk, hloc, hrd⟩) (fun _ h => h)
    refine frag_pure (kv = at_ A sKey ∨ kv = at_ A (sWindow + o') + BitVec.ofNat 64 33)
      (fun u hu => hu.2.2.2.2.2.1) lall fun hloc => ?_
    have hapart := key_apart h.hA rfl h.room hloc
    -- the message
    let Fm : Assn σ := fun u => u.locals "jwhy" = some 0 ∧ u.locals "k" = some kv ∧
      readByteArray u.memory u.memaddrs u.be kv 16 = some kk
    have hFs : Stable ["p", "ji", "n"] (MsgW A) Fm := fun u u' ⟨h1, h2, h3⟩ hk =>
      ⟨(hk.locals "jwhy" (by decide)).trans h1, (hk.locals "k" (by decide)).trans h2,
        (read_kept hk 16 kv hapart).trans h3⟩
    have hFc : Safe.ClockFree Fm := fun _ _ h => h
    have hb : ∀ i (hi : i < (payloadOf bs).length), memLoadByte s0.memory s0.memaddrs s0.be
        (at_ A (sWindow + o' + 13 + i)) = some (payloadOf bs)[i] := fun i hi => by
      rw [payload_get i hi (by omega), show sWindow + o' + 13 + i = sWindow + o' + (13 + i) by omega]
      exact h.bytes (13 + i) (by omega) (by omega)
    have fm := message_frag o (F := Fm) (t := typeOf bs) h.hA h.dom h.sp h.jz h.q h.jq h.jf hroom hplb hb h.bound
      hFs hFc
    -- its tag
    let msg := le 8 q ++ BitVec.ofNat 8 (typeOf bs) :: payloadOf bs
    have hmsg : msg.length = (payloadOf bs).length + 9 := by simp [msg, le_length]; omega
    have hlen : msg.length < 2 ^ 62 := by omega
    let G : Assn σ := MBase A s0 Fm (typeOf bs) (payloadOf bs).length
    have hG : Stable sipNames (fun _ => False) G := fun u u' ⟨k1, f, jt, jpl⟩ hk =>
      ⟨kept_trans k1 (kept_widen hk (by decide) fun _ h => h.elim), ⟨(hk.locals "jwhy" (by decide)).trans f.1,
        (hk.locals "k" (by decide)).trans f.2.1, (read_kept hk 16 kv fun _ _ h => h).trans f.2.2⟩,
        (hk.locals "jt" (by decide)).trans jt, (hk.locals "jpl" (by decide)).trans jpl⟩
    have fs := sip_frag o (kv := kv) (pv := at_ A sMessage) (key := kk) (msg := msg) hlen hG (mbase_clock hFc)
    have fms := frag_append fm (frag_conseq fs (fun u ⟨hu, hp, hn, hmem⟩ => ⟨⟨⟨hu.2.1.2.1, hp,
      by rw [hn, hmsg], kept_has hu.1 (h.bound _ (by decide)), hu.2.1.2.2,
      read_of_bytes msg _ (memBytesAt_get hmem)⟩, fun y hy => kept_has hu.1 (h.bound y (by
        simp [SipHashCode.work] at hy; rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide))⟩, hu⟩)
      (fun _ h => h))
    -- the stored tag
    have h8 : ((bs.drop 4).take 8).length = 8 := by simp; omega
    have hst : readLE ((bs.drop 4).take 8) < 2 ^ 64 := readLE_take_lt _ 8
    let H : Assn σ := fun u => G u ∧ u.locals "r" = some (SipHash.tag kk msg).toBitVec ∧
      u.locals "jtag" = some (BitVec.ofNat 64 (readLE ((bs.drop 4).take 8)))
    have hHc : Safe.ClockFree H := fun _ _ ⟨h1, h2, h3⟩ => ⟨mbase_clock hFc _ _ h1, h2, h3⟩
    have fl : Frag o (ScanProg.leS "jtag" (Syntax.atOff (Syntax.v "jf") 4) 8)
        (fun u => G u ∧ u.locals "r" = some (SipHash.tag kk msg).toBitVec) H := by
      refine frag_each o (lowK_any _ (k := .skip) (c := _) rfl) fun s ⟨hg, hr⟩ => ?_
      have hjf : s.locals "jf" = some (at_ A (sWindow + o')) := (hg.1.locals "jf" (by decide)).trans h.jf
      have e := leS_frag o (x := "jtag") (p := Syntax.atOff (Syntax.v "jf") 4)
        (P := .op .add (.var "jf") (.const (BitVec.ofNat 64 4))) rfl (s := s)
        (a := at_ A (sWindow + o') + BitVec.ofNat 64 4) (bs := (bs.drop 4).take 8) (by omega)
        (fun w => by simp [eval, setL, setLocal, hjf]) (fun i hi => by
          have hi8 : i < 8 := h8 ▸ hi
          rw [at_add, at_add, kept_load hg.1 (not_msg h.hA (Or.inr (by omega)) (by have := h.room; omega)),
            show sWindow + o' + 4 + i = sWindow + o' + (4 + i) by omega, h.bytes (4 + i) (by omega) (by omega)]
          simp [List.getElem_take, List.getElem_drop])
        (kept_has hg.1 (h.bound _ (by decide)))
      rw [h8] at e
      refine frag_conseq e (fun _ h => h) fun u hu => ?_
      rw [like_eq hu]
      refine hHc _ _ ⟨⟨kept_set hg.1 (by decide) _, ⟨by simp [setL, setLocal, hg.2.1.1], by simp [setL, setLocal,
        hg.2.1.2.1], by simpa [setL] using hg.2.1.2.2⟩, by simp [setL, setLocal, hg.2.2.1],
        by simp [setL, setLocal, hg.2.2.2]⟩, by simp [setL, setLocal, hr], by simp [setL, setLocal]⟩
    -- compared
    have htv : (SipHash.tag kk msg).toBitVec = BitVec.ofNat 64 (SipHash.tag kk msg).toNat := by
      apply BitVec.eq_of_toNat_eq; simp
    have htl : (SipHash.tag kk msg).toNat < 2 ^ 64 := (SipHash.tag kk msg).toNat_lt
    have hev : ∀ u, H u → eval u (.cmp .equal (.cmp .equal (.var "r") (.var "jtag")) (.const 0)) =
        some (bw (decide ((SipHash.tag kk msg).toNat ≠ readLE ((bs.drop 4).take 8)))) := fun u hu =>
      e_ne htl hst (by simp only [eval]; rw [hu.2.1, htv]) (by simp only [eval]; exact hu.2.2)
    have hwrong : tagWrong (key <|> keyIn spec (typeOf bs) (payloadOf bs)) (readLE ((bs.drop 4).take 8)) q
        (typeOf bs) (payloadOf bs) = decide ((SipHash.tag kk msg).toNat ≠ readLE ((bs.drop 4).take 8)) := by
      rw [heff]
      show (readLE ((bs.drop 4).take 8) != (SipHash.tag kk msg).toNat) =
        decide ((SipHash.tag kk msg).toNat ≠ readLE ((bs.drop 4).take 8))
      by_cases e : (SipHash.tag kk msg).toNat = readLE ((bs.drop 4).take 8)
      · rw [e]; simp
      · have e' : readLE ((bs.drop 4).take 8) ≠ (SipHash.tag kk msg).toNat := fun h => e h.symm
        simp [e, e']
    have fi : Frag o [.ite (ScanProg.ne (Syntax.v "r") (Syntax.v "jtag")) [.assign "jwhy" (lit (whyCode .tag))] []]
        H (FwOut A key q bs s0) := by
      refine frag_ite o (C := .cmp .equal (.cmp .equal (.var "r") (.var "jtag")) (.const 0)) rfl fwOut_clock
        (fun u hu => ⟨_, hev u hu⟩) ?_ (noDecl _ rfl) (frag_nil o fun u ⟨hu, hz⟩ => ?_) (noDecl _ rfl)
      · refine why_frag o fwOut_clock _ fun u ⟨hu, hne⟩ => ?_
        rw [hev u hu] at hne
        have hw := bw_ne0 hne
        have hf : fault key q bs = some .tag := by rw [hft, hwrong, hw]; rfl
        refine ⟨(hu.1.1.locals "jz" (by decide)).trans h.jz, ⟨_, hu.1.2.1.1⟩, kept_set hu.1.1 (by decide) _, ?_,
          fun e => by simp [hf] at e, fun e => by simp [hf] at e⟩
        simp [setL, setLocal, hf, codeOf, whyCode]
      · rw [hev u hu] at hz
        have hw := bw_eq0 hz
        have hf : fault key q bs = none := by rw [hft, hwrong, hw]; rfl
        have hj : u.locals "jpl" = some (BitVec.ofNat 64 (readLE (bs.take 4))) := by rw [← hpl]; exact hu.1.2.2.2
        have hw0 : u.locals "jwhy" = some (BitVec.ofNat 64 (codeOf (fault key q bs))) := by
          rw [hf, hu.1.2.1.1]; rfl
        exact ⟨hu.1.1, hw0, fun _ => hj, fun _ => hu.1.2.2.1⟩
    exact frag_conseq (frag_append (frag_append fms fl) fi)
      (fun u hu => ⟨hu.1, ⟨hu.2.1, hu.2.2.2.2.1, hu.2.2.2.2.2.2⟩, hu.2.2.1, hu.2.2.2.1⟩) (fun _ h => h)

theorem kept_of_like {xs : List String} {w : Word → Prop} {s u : PancakeState σ} (h : Like s u) : Kept xs w s u :=
  ⟨fun x _ => by rw [h.locals], fun a _ => by rw [h.memory], h.memaddrs, h.be, h.base, h.ffi, h.code,
    fun y hy => by rw [h.locals]; exact hy⟩

theorem fault_short {key : Option Bytes} {q : Nat} {bs : Bytes} (h : bs.length < 13) :
    fault key q bs = some .short := by
  simp only [fault, headerLength]; rw [if_pos h]

theorem fault_long {key : Option Bytes} {q : Nat} {bs : Bytes} (h13 : 13 ≤ bs.length)
    (h : maxPayload < readLE (bs.take 4)) : fault key q bs = some .tooLong := by
  simp only [fault, headerLength]; rw [if_neg (by omega), if_pos h]

theorem fault_cut {key : Option Bytes} {q : Nat} {bs : Bytes} (h13 : 13 ≤ bs.length)
    (hmax : readLE (bs.take 4) ≤ maxPayload) (h : bs.length < 13 + readLE (bs.take 4) + 1) :
    fault key q bs = some .short := by
  simp only [fault, headerLength]; rw [if_neg (by omega), if_neg (by omega), if_pos h]

theorem fault_unended {key : Option Bytes} {q : Nat} {bs : Bytes} (h13 : 13 ≤ bs.length)
    (hmax : readLE (bs.take 4) ≤ maxPayload) (hend : 13 + readLE (bs.take 4) + 1 ≤ bs.length)
    (h : bs.getD (13 + readLE (bs.take 4)) 0 ≠ endMark) : fault key q bs = some .unterminated := by
  simp only [fault, headerLength]; rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos h]

/-! ### The check's parts, each after a test passed -/

theorem declared_markPart (keyed : Bool) : declared (markPart keyed) = [] := by cases keyed <;> rfl

theorem lowKK_tagPart : LowKK tagPart :=
  lowKK_ite rfl (lowK_any _ (k := .skip) (c := _) rfl) (lowKK_append (lowKK_append (lowKK_append
    (lowK_any _ (k := .skip) (c := _) rfl) lowKK_sip) (lowK_any _ (k := .skip) (c := _) rfl))
    (lowK_any _ (k := .skip) (c := _) rfl))

theorem lowKK_markPart (keyed : Bool) : LowKK (markPart keyed) :=
  lowKK_append (lowKK_append (lowK_any _ (k := .skip) (c := _) rfl)
    (by cases keyed <;> exact lowK_any _ (k := .skip) (c := _) rfl)) lowKK_tagPart

theorem lowKK_endPart (keyed : Bool) : LowKK (endPart keyed) :=
  lowKK_ite rfl (lowK_any _ (k := .skip) (c := _) rfl) (lowKK_markPart keyed)

theorem lowKK_cutPart (keyed : Bool) : LowKK (cutPart keyed) :=
  lowKK_ite rfl (lowK_any _ (k := .skip) (c := _) rfl) (lowKK_endPart keyed)

theorem lowKK_longPart (keyed : Bool) : LowKK (longPart keyed) :=
  lowKK_ite rfl (lowK_any _ (k := .skip) (c := _) rfl) (lowKK_cutPart keyed)

theorem lowKK_lenPart (keyed : Bool) : LowKK (ScanProg.leS "jpl" (Syntax.v "jf") 4 ++ longPart keyed) :=
  lowKK_append (lowK_any _ (k := .skip) (c := _) rfl) (lowKK_longPart keyed)

/-- **The scanner's check of a frame is `fault`**: if it goes on, `jwhy` holds the code of what `fault` finds,
and of a frame that checks, `jpl` the payload's length and `jt` the type; locals but `fwNames` and memory but
the message as they were. -/
theorem frameWhy_frag (o : Oracle σ) (h : FwIn keyed A key q o' bs s0) :
    Frag o (ScanProg.frameWhy keyed) (Like s0) (FwOut A key q bs s0) := by
  have hn := nums
  have hwin : ∀ u, Kept fwNames (MsgW A) s0 u → ∀ i (hi : i < bs.length), i < maxFrame →
      memLoadByte u.memory u.memaddrs u.be (at_ A (sWindow + o') + BitVec.ofNat 64 i) = some bs[i] :=
    fun u hu i hi hm => by
      rw [at_add, kept_load hu (not_msg h.hA (Or.inr (by omega)) (by have := h.room; omega))]
      exact h.bytes i hi hm
  have hjr : ∀ u, Kept fwNames (MsgW A) s0 u → eval u (.var "jr") = some (BitVec.ofNat 64 bs.length) :=
    fun u hu => by simp only [eval]; rw [hu.locals "jr" (by decide)]; exact h.jr
  have hjf : ∀ u, Kept fwNames (MsgW A) s0 u → u.locals "jf" = some (at_ A (sWindow + o')) :=
    fun u hu => (hu.locals "jf" (by decide)).trans h.jf
  have hjz : ∀ u, Kept fwNames (MsgW A) s0 u → u.locals "jz" = some 0 :=
    fun u hu => (hu.locals "jz" (by decide)).trans h.jz
  have hbd : ∀ u, Kept fwNames (MsgW A) s0 u → ∀ y, y ∈ fwNames → ∃ v, u.locals y = some v :=
    fun u hu y hy => kept_has hu (h.bound y hy)
  -- a reason found: `jwhy` gets its code
  have why : ∀ (w : Why) (P : Assn σ), (∀ u, P u → Kept fwNames (MsgW A) s0 u) → fault key q bs = some w →
      Frag o [.assign "jwhy" (lit (whyCode w))] P (FwOut A key q bs s0) := fun w P hP hf =>
    why_frag o fwOut_clock _ fun u hu => ⟨hjz u (hP u hu), hbd u (hP u hu) "jwhy" (by decide),
      kept_set (hP u hu) (by decide) _, by simp [setL, setLocal, hf, codeOf], fun e => by simp [hf] at e,
      fun e => by simp [hf] at e⟩
  let P0 : Assn σ := fun u => Kept fwNames (MsgW A) s0 u ∧ u.locals "jwhy" = some 0
  have hP0c : Safe.ClockFree P0 := fun _ _ ⟨h1, h2⟩ => ⟨{ h1 with }, h2⟩
  have f0 : Frag o [.assign "jwhy" (lit 0)] (Like s0) P0 :=
    set_frag o (E := .op .add (.var "jz") (.const 0)) rfl hP0c fun u hu => ⟨0, by simp [eval, hjz u
      (kept_of_like hu)], hbd u (kept_of_like hu) "jwhy" (by decide), kept_set (kept_of_like hu) (by decide) _,
      by simp [setL, setLocal]⟩
  unfold ScanProg.frameWhy
  refine frag_append (xs := [_]) f0 ?_
  refine frag_ite o (C := .cmp .less (.var "jr") (.const (BitVec.ofNat 64 headerLength))) rfl fwOut_clock
    (fun u hu => ⟨_, eval_lt (by have := h.len; omega) (by decide) (hjr u hu.1) rfl⟩) ?_ (noDecl _ rfl) ?_
    (noDecl _ rfl)
  · -- shorter than a header
    refine frag_pure (bs.length < 13) (fun u ⟨hu, hne⟩ => ?_) (lowK_any _ (k := .skip) (c := _) rfl)
      fun hs => why .short _ (fun u hu => hu.1.1) (fault_short hs)
    rw [eval_lt (by have := h.len; omega) (by decide) (hjr u hu.1) rfl] at hne
    simpa [headerLength] using bw_ne0 hne
  refine frag_pure (13 ≤ bs.length) (fun u ⟨hu, h0⟩ => ?_) (lowKK_lenPart keyed) fun h13 => ?_
  · rw [eval_lt (by have := h.len; omega) (by decide) (hjr u hu.1) rfl] at h0
    have := bw_eq0 h0
    simp [headerLength] at this; omega
  -- the length
  have h4 : (bs.take 4).length = 4 := by simp; omega
  have hl32 : readLE (bs.take 4) < 2 ^ 32 := readLE_take_lt _ 4
  let P1 : Assn σ := fun u => P0 u ∧ u.locals "jpl" = some (BitVec.ofNat 64 (readLE (bs.take 4)))
  have hP1c : Safe.ClockFree P1 := fun _ _ ⟨h1, h2⟩ => ⟨hP0c _ _ h1, h2⟩
  have fl : Frag o (ScanProg.leS "jpl" (Syntax.v "jf") 4)
      (fun u => P0 u ∧ eval u (.cmp .less (.var "jr") (.const (BitVec.ofNat 64 headerLength))) = some 0) P1 := by
    refine frag_each o (lowK_any _ (k := .skip) (c := _) rfl) fun s ⟨hs, _⟩ => ?_
    have e := leS_frag o (x := "jpl") (p := Syntax.v "jf") (P := .var "jf") rfl (s := s)
      (a := at_ A (sWindow + o')) (bs := bs.take 4) (by omega) (fun w => by simp [eval, setL, setLocal, hjf s hs.1])
      (fun i hi => by rw [hwin s hs.1 i (by omega) (by omega)]; simp [List.getElem_take])
      (hbd s hs.1 "jpl" (by decide))
    rw [h4] at e
    refine frag_conseq e (fun _ h => h) fun u hu => ?_
    rw [like_eq hu]
    exact hP1c _ _ ⟨⟨kept_set hs.1 (by decide) _, by simp [setL, setLocal, hs.2]⟩, by simp [setL, setLocal]⟩
  refine frag_append fl ?_
  -- longer than any payload
  have hev2 : ∀ u, P1 u → eval u (.cmp .less (.const 0) (.op .add (.cmp .less (.const (BitVec.ofNat 64 maxPayload))
      (.var "jpl")) (.cmp .less (.var "jpl") (.const 0)))) =
        some (bw (decide (maxPayload < readLE (bs.take 4)) || decide (readLE (bs.take 4) < 0))) := fun u hu =>
    e_or2 (eval_lt (by omega) (by omega) rfl (by simp only [eval]; exact hu.2))
      (eval_lt (by omega) (by decide) (by simp only [eval]; exact hu.2) rfl)
  refine frag_ite o (C := .cmp .less (.const 0) (.op .add (.cmp .less (.const (BitVec.ofNat 64 maxPayload))
      (.var "jpl")) (.cmp .less (.var "jpl") (.const 0)))) rfl fwOut_clock (fun u hu => ⟨_, hev2 u hu⟩) ?_
    (noDecl _ rfl) ?_ (noDecl _ rfl)
  · refine frag_pure (maxPayload < readLE (bs.take 4)) (fun u ⟨hu, hne⟩ => ?_)
      (lowK_any _ (k := .skip) (c := _) rfl) fun hm => why .tooLong _ (fun u hu => hu.1.1.1) (fault_long h13 hm)
    rw [hev2 u hu] at hne
    simpa using bw_ne0 hne
  refine frag_pure (readLE (bs.take 4) ≤ maxPayload) (fun u ⟨hu, h0⟩ => ?_)
    (lowKK_cutPart keyed) fun hmax => ?_
  · rw [hev2 u hu] at h0
    have := bw_eq0 h0
    simp at this; omega
  -- shorter than its length says
  have hev3 : ∀ u, P1 u → eval u (.cmp .less (.var "jr") (.op .add (.var "jpl") (.const (BitVec.ofNat 64 14)))) =
      some (bw (decide (bs.length < readLE (bs.take 4) + 14))) := fun u hu =>
    eval_lt (by have := h.len; omega) (by omega) (hjr u hu.1.1)
      (by simp only [eval, hu.2]; rw [BitVec.ofNat_add])
  refine frag_ite o (C := .cmp .less (.var "jr") (.op .add (.var "jpl") (.const (BitVec.ofNat 64 14))))
    rfl fwOut_clock (fun u hu => ⟨_, hev3 u hu.1⟩) ?_ (noDecl _ rfl) ?_ (noDecl _ rfl)
  · refine frag_pure (bs.length < 13 + readLE (bs.take 4) + 1) (fun u ⟨hu, hne⟩ => ?_)
      (lowK_any _ (k := .skip) (c := _) rfl) fun hc => why .short _ (fun u hu => hu.1.1.1.1)
        (fault_cut h13 hmax hc)
    rw [hev3 u hu.1] at hne
    have := bw_ne0 hne
    simp at this; omega
  refine frag_pure (13 + readLE (bs.take 4) + 1 ≤ bs.length) (fun u ⟨hu, h0⟩ => ?_)
    (lowKK_endPart keyed) fun hend => ?_
  · rw [hev3 u hu.1] at h0
    have := bw_eq0 h0
    simp at this; omega
  -- not ended by the mark
  have hidx : 13 + readLE (bs.take 4) < bs.length := by omega
  have hev4 : ∀ u, P1 u → eval u (.cmp .equal (.cmp .equal (.loadByte (.op .add (.var "jf") (.op .add (.var "jpl")
      (.const (BitVec.ofNat 64 13))))) (.const (BitVec.ofNat 64 0xA5))) (.const 0)) =
        some (bw (decide ((bs[13 + readLE (bs.take 4)]).toNat ≠ 0xA5))) := fun u hu => by
    have hb := hwin u hu.1.1 (13 + readLE (bs.take 4)) hidx (by omega)
    have hb' : memLoadByte u.memory u.memaddrs u.be (at_ A (sWindow + o') +
        (BitVec.ofNat 64 (readLE (bs.take 4)) + BitVec.ofNat 64 13)) = some bs[13 + readLE (bs.take 4)] := by
      rw [← BitVec.ofNat_add, Nat.add_comm (readLE _) 13]; exact hb
    have hl : eval u (.loadByte (.op .add (.var "jf") (.op .add (.var "jpl") (.const (BitVec.ofNat 64 13))))) =
        some (BitVec.ofNat 64 (bs[13 + readLE (bs.take 4)]).toNat) := by
      simp only [eval, hjf u hu.1.1, hu.2, hb']
      rw [Bytes.setWidth8_64]
    exact e_ne (Nat.lt_trans (bs[13 + readLE (bs.take 4)]).isLt (by decide)) (by decide) hl rfl
  have hmark' : ∀ u, P1 u → eval u (.cmp .equal (.cmp .equal (.loadByte (.op .add (.var "jf") (.op .add (.var "jpl")
      (.const (BitVec.ofNat 64 13))))) (.const (BitVec.ofNat 64 0xA5))) (.const 0)) =
        some (bw (decide (bs.getD (13 + readLE (bs.take 4)) 0 ≠ endMark))) := fun u hu => by
    have hiff : (bs[13 + readLE (bs.take 4)]).toNat ≠ 0xA5 ↔ bs[13 + readLE (bs.take 4)] ≠ endMark :=
      ⟨fun h e => h (by rw [e]; rfl), fun h e => h (BitVec.eq_of_toNat_eq (by rw [e]; rfl))⟩
    rw [hev4 u hu, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hidx, Option.getD_some,
      decide_eq_decide.mpr hiff]
  refine frag_ite o (C := .cmp .equal (.cmp .equal (.loadByte (.op .add (.var "jf") (.op .add (.var "jpl")
      (.const (BitVec.ofNat 64 13))))) (.const (BitVec.ofNat 64 0xA5))) (.const 0)) rfl fwOut_clock
    (fun u hu => ⟨_, hmark' u hu.1.1⟩) ?_ (noDecl _ rfl) ?_ (noDecl _ (declared_markPart keyed))
  · refine frag_pure (bs.getD (13 + readLE (bs.take 4)) 0 ≠ endMark) (fun u ⟨hu, hne⟩ => ?_)
      (lowK_any _ (k := .skip) (c := _) rfl) fun hm => why .unterminated _ (fun u hu => hu.1.1.1.1.1)
        (fault_unended h13 hmax hend hm)
    rw [hmark' u hu.1.1] at hne
    simpa using bw_ne0 hne
  refine frag_pure (bs.getD (13 + readLE (bs.take 4)) 0 = endMark) (fun u ⟨hu, h0⟩ => ?_)
    (lowKK_markPart keyed) fun hm => ?_
  · rw [hmark' u hu.1.1] at h0
    simpa using bw_eq0 h0
  -- the type, the key, the tag
  have hpl := payload_length hend
  have h12 : 12 < bs.length := by omega
  let P2 : Assn σ := fun u => Kept fwNames (MsgW A) s0 u ∧ u.locals "jwhy" = some 0 ∧
    u.locals "jpl" = some (BitVec.ofNat 64 (readLE (bs.take 4))) ∧ u.locals "jt" = some (BitVec.ofNat 64 (typeOf bs))
  have hP2c : Safe.ClockFree P2 := fun _ _ ⟨h1, h2, h3, h4⟩ => ⟨{ h1 with }, h2, h3, h4⟩
  have fjt : Frag o [.assign "jt" (ScanProg.byte (Syntax.atOff (Syntax.v "jf") 12))] P1 P2 :=
    set_frag o (E := .loadByte (.op .add (.var "jf") (.const (BitVec.ofNat 64 12)))) rfl hP2c fun u hu => by
      obtain ⟨⟨hk, hw⟩, hj⟩ := hu
      have hb := hwin u hk 12 h12 (by omega)
      refine ⟨BitVec.ofNat 64 (typeOf bs), by simp only [eval, hjf u hk, hb, Bytes.setWidth8_64, typeOf,
        List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h12, Option.getD_some],
        hbd u hk "jt" (by decide), kept_set hk (by decide) _, by simp [setL, setLocal, hw],
        by simp [setL, setLocal, hj], by simp [setL, setLocal]⟩
  have hin : ∀ u, P2 u → KeyIn A (at_ A (sWindow + o')) key (typeOf bs) (payloadOf bs) u := fun u hu =>
    { sp := (hu.1.locals "jsc" (by decide)).trans h.sp
      jz := hjz u hu.1
      key := fun kk hk => by
        rw [read_kept hu.1 16 _ fun i hi => by rw [at_add]; exact not_msg h.hA (Or.inl (by omega)) (by omega)]
        exact h.key kk hk
      jt := hu.2.2.2
      jpl := by rw [hpl]; exact hu.2.2.1
      jf := hjf u hu.1
      payload := fun i hi => by
        rw [hwin u hu.1 (13 + i) (by omega) (by omega), payload_get i hi (by omega)]
      k := hbd u hu.1 "k" (by decide)
      jhk := hbd u hu.1 "jhk" (by decide)
      short := by omega }
  have fks := keySelK_frag o keyed (A := A) (F := at_ A (sWindow + o')) (key := key) (t := typeOf bs)
    (pl := payloadOf bs) hP2c (fun u x v hu hx => by
      have hx' : x ∈ fwNames := by simp at hx; rcases hx with rfl | rfl <;> decide
      have h1 : "jwhy" ≠ x := by simp at hx; rcases hx with rfl | rfl <;> decide
      have h2 : "jpl" ≠ x := by simp at hx; rcases hx with rfl | rfl <;> decide
      have h3 : "jt" ≠ x := by simp at hx; rcases hx with rfl | rfl <;> decide
      exact ⟨kept_set hu.1 hx' v, by simp [setL, setLocal, h1, hu.2.1], by simp [setL, setLocal, h2, hu.2.2.1],
        by simp [setL, setLocal, h3, hu.2.2.2]⟩) hin
    (fun hk u hu => (hu.1.locals "jky" (by decide)).trans (h.jky hk)) h.keyed (bs.getD 12 0).isLt
  unfold markPart
  exact frag_conseq (frag_append (frag_append fjt fks) (frag_conseq (tag_frag o h h13 hmax hend hm)
    (fun u ⟨hu, hk⟩ => ⟨hu.1, hu.2.1, hu.2.2.2, hu.2.2.1, hk⟩) (fun _ h => h))) (fun _ hu => hu.1.1.1)
    (fun _ h => h)

end Tag

end DN.News.ScanRun
