-- SPDX-License-Identifier: AGPL-3.0-or-later
import DN.News.ScanProg
import DN.News.SipHashCode
import DN.News.FramerCode
import DN.Compiler.FragRules
import DN.Compiler.NatToDec

/-!
# DN.News.ScanRun

What `DN.News.Journal.next` decides of a frame before reading a record (`fault`, `next_fault`, `checks_fault`). What a
scanner fragment keeps (`Kept`), its tests (`e_ne`, `e_or2`), and its numeric reads (`leS_frag`).
-/

namespace DN.News.ScanRun

open DN.Compiler DN.Compiler.Wp DN.Compiler.Frag DN.News.Journal
open DN.News.FramerCode (bw eq_word eval_lt eval_or2)

variable {σ : Type}

/-! ## A frame, as `next` reads it -/

/-- The payload of the frame at the start of `bs`, as long as its length says. -/
def payloadOf (bs : Bytes) : Bytes := (bs.drop headerLength).take (readLE (bs.take 4))

/-- The frame's type. -/
def typeOf (bs : Bytes) : Nat := (bs.getD 12 0).toNat

/-- Why the frame at `offset`, the start of `bs`, does not check, as `next` finds it before reading a record. None when
it checks. -/
def fault (key : Option Bytes) (offset : Nat) (bs : Bytes) : Option Why :=
  if bs.length < headerLength then some .short
  else if maxPayload < readLE (bs.take 4) then some .tooLong
  else if bs.length < headerLength + readLE (bs.take 4) + 1 then some .short
  else if bs.getD (headerLength + readLE (bs.take 4)) 0 ≠ endMark then some .unterminated
  else if tagWrong (key <|> keyIn spec (typeOf bs) (payloadOf bs)) (readLE ((bs.drop 4).take 8)) offset
      (typeOf bs) (payloadOf bs) then some .tag
  else none

theorem frame_split {bs : Bytes} {len : Nat} (h : 13 ≤ bs.length) :
    (bs.drop 12).take (1 + len) = bs.getD 12 0 :: (bs.drop 13).take len := by
  rw [Nat.add_comm, List.drop_eq_getElem_cons (by omega : 12 < bs.length), List.take_succ_cons,
    List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega : 12 < bs.length)]
  rfl

/-- **`next` is `fault`, then the record the frame holds.** -/
theorem next_fault (key : Option Bytes) (offset : Nat) {bs : Bytes} (h : bs ≠ []) :
    next spec key offset bs = match fault key offset bs with
      | some w => .bad w
      | none => match recordOf spec (typeOf bs) (payloadOf bs) with
        | some rec => .record rec (headerLength + readLE (bs.take 4) + 1)
            (bs.drop (headerLength + readLE (bs.take 4) + 1))
        | none => .bad .notARecord := by
  have he : bs.isEmpty = false := by cases bs <;> simp_all
  simp only [next, he, atLeast_eq, fault, spec_maxPayload, spec_ended, spec_tagged, Bool.false_eq_true, if_false]
  simp only [typeOf, payloadOf, headerLength]
  by_cases h1 : bs.length < 13
  · rw [if_pos (by simp; omega), if_pos h1]
  rw [if_neg (by simp; omega), if_neg h1]
  by_cases h2 : maxPayload < readLE (List.take 4 bs)
  · rw [if_pos h2, if_pos h2]
  rw [if_neg h2, if_neg h2]
  by_cases h3 : bs.length < 13 + readLE (List.take 4 bs) + 1
  · rw [if_pos (by simp; omega), if_pos h3]
  rw [if_neg (by simp; omega), if_neg h3]
  by_cases h4 : bs.getD (13 + readLE (List.take 4 bs)) 0 = endMark
  · rw [if_neg (by rw [h4]; decide), if_neg (fun h => h h4), frame_split (len := readLE (List.take 4 bs)) (by omega)]
    simp only [Bool.true_and]
    by_cases h5 : tagWrong (key <|> keyIn spec (bs.getD 12 0).toNat ((bs.drop 13).take (readLE (List.take 4 bs))))
        (readLE ((bs.drop 4).take 8)) offset (bs.getD 12 0).toNat ((bs.drop 13).take (readLE (List.take 4 bs))) = true
    · rw [if_pos h5, if_pos h5]
    · rw [if_neg h5, if_neg h5]; rfl
  · rw [if_pos (by simp only [Bool.true_and, bne_iff_ne, ne_eq]; exact h4), if_pos h4]

theorem fault_ne (key : Option Bytes) (offset : Nat) (bs : Bytes) : fault key offset bs ≠ some .notARecord := by
  unfold fault
  repeat' split
  all_goals simp

/-- …so a frame checks under a key when `fault` finds nothing. -/
theorem checks_fault (key : Bytes) (offset : Nat) (bs : Bytes) :
    checks spec key offset bs = (fault (some key) offset bs).isNone := by
  cases bs with
  | nil => simp [checks, next, fault, headerLength]
  | cons b bs =>
    rw [checks, next_fault _ _ (List.cons_ne_nil b bs)]
    have hn := fault_ne (some key) offset (b :: bs)
    revert hn
    cases fault (some key) offset (b :: bs) with
    | some w => cases w <;> simp
    | none =>
      intro _
      cases recordOf spec (typeOf (b :: bs)) (payloadOf (b :: bs)) <;> simp

/-! ## Numbers in octets -/

theorem readLE_lt : ∀ bs : Bytes, readLE bs < 2 ^ (8 * bs.length)
  | [] => by simp [readLE]
  | c :: cs => by
    have := readLE_lt cs
    have := c.isLt
    simp only [readLE, List.length_cons]
    rw [show 8 * (cs.length + 1) = 8 * cs.length + 8 by omega, Nat.pow_add]
    omega

/-- A number of `k` octets is less than `2 ^ (8 * k)`. -/
theorem readLE_take_lt (bs : Bytes) (k : Nat) : readLE (bs.take k) < 2 ^ (8 * k) :=
  Nat.lt_of_lt_of_le (readLE_lt _) (Nat.pow_le_pow_right (by decide) (by simp; omega))

theorem word_toNat : ∀ bs : Bytes, bs.length ≤ 8 → (SipHash.word bs).toBitVec.toNat = readLE bs
  | [] , _ => rfl
  | b :: bs, h => by
    have ih := word_toNat bs (by simp at h; omega)
    have h56 : readLE bs < 2 ^ 56 :=
      Nat.lt_of_lt_of_le (readLE_lt bs) (Nat.pow_le_pow_right (by decide) (by simp at h; omega))
    have hbl := b.isLt
    rw [SipHashCode.word_cons, BitVec.toNat_or, BitVec.toNat_shiftLeft, ih, BitVec.toNat_setWidth,
      Nat.mod_eq_of_lt (by omega : b.toNat < 2 ^ 64), Nat.mod_eq_of_lt (by rw [Nat.shiftLeft_eq]; omega),
      ← Nat.shiftLeft_add_eq_or_of_lt (by omega : b.toNat < 2 ^ 8), Nat.shiftLeft_eq]
    simp only [readLE]
    omega

theorem word_eq {bs : Bytes} (h : bs.length ≤ 8) : (SipHash.word bs).toBitVec = BitVec.ofNat 64 (readLE bs) := by
  apply BitVec.eq_of_toNat_eq
  have := readLE_lt bs
  rw [word_toNat bs h, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le this
    (Nat.pow_le_pow_right (by decide) (by omega)))]

theorem atOff_lower {p : Syntax.PExpr} {P : PancakeExp} (hp : Lower.lowerExp p = some P) (i : Nat) :
    Lower.lowerExp (Syntax.atOff p i) = some (if i = 0 then P else .op .add P (.const (BitVec.ofNat 64 i))) := by
  by_cases h : i = 0
  · subst h; simp [Syntax.atOff, hp]
  · simp [Syntax.atOff, h, Syntax.eAdd, Syntax.n, Lower.lowerExp, hp]

/-- The step of `leS` that takes octet `i`. -/
def leStep (x : String) (p : Syntax.PExpr) (i : Nat) : Syntax.PStmt :=
  .assign x (Syntax.eOr (.shl (Syntax.v x) (Syntax.n 8)) (ScanProg.byte (Syntax.atOff p i)))

theorem leS_eq (x : String) (p : Syntax.PExpr) (k : Nat) :
    ScanProg.leS x p k = .assign x (Syntax.n 0) :: (List.range k).reverse.map (leStep x p) := rfl

/-- **`leS` reads `k` octets as a number**, least significant first, into `x`. -/
theorem leS_frag (o : Oracle σ) {x : String} {p : Syntax.PExpr} {P : PancakeExp} (hp : Lower.lowerExp p = some P)
    {s : PancakeState σ} {a : Word} {bs : Bytes} (hk : bs.length ≤ 8)
    (hP : ∀ w, eval (setL s x w) P = some a)
    (hb : ∀ i (h : i < bs.length), memLoadByte s.memory s.memaddrs s.be (a + BitVec.ofNat 64 i) = some bs[i])
    (hx : ∃ old, s.locals x = some old) :
    Frag o (ScanProg.leS x p bs.length) (Like s) (Like (setL s x (BitVec.ofNat 64 (readLE bs)))) := by
  rw [leS_eq, ← word_eq hk]
  have step : ∀ j, j ≤ bs.length → Frag o ((List.range j).reverse.map (leStep x p))
      (Like (setL s x (SipHash.word (bs.drop j)).toBitVec)) (Like (setL s x (SipHash.word bs).toBitVec)) := by
    intro j
    induction j with
    | zero => intro _; exact frag_nil o fun _ h => by simpa using h
    | succ j ih =>
      intro hj
      rw [List.range_succ, List.reverse_append, List.reverse_singleton, List.singleton_append, List.map_cons]
      refine frag_append (xs := [_]) ?_ (ih (by omega))
      have hlt : j < bs.length := by omega
      have hd : bs.drop j = bs[j] :: bs.drop (j + 1) := List.drop_eq_getElem_cons hlt
      have e := assign_frag o (s := setL s x (SipHash.word (bs.drop (j + 1))).toBitVec) (x := x)
        (e := Syntax.eOr (.shl (Syntax.v x) (Syntax.n 8)) (ScanProg.byte (Syntax.atOff p j)))
        (by simp [Syntax.eOr, Syntax.v, Syntax.n, ScanProg.byte, Lower.lowerExp, atOff_lower hp j]; rfl)
        (v := (SipHash.word (bs.drop j)).toBitVec) ?_
        ⟨(SipHash.word (bs.drop (j + 1))).toBitVec, by simp [setL, setLocal]⟩
      · rw [setL_setL] at e; exact e
      · have hA : eval (setL s x (SipHash.word (bs.drop (j + 1))).toBitVec)
            (if j = 0 then P else .op .add P (.const (BitVec.ofNat 64 j))) = some (a + BitVec.ofNat 64 j) := by
          by_cases h0 : j = 0
          · subst h0; simp [hP]
          · simp [h0, eval, hP]
        have hm := hb j hlt
        simp only [setL] at hA
        have h8 : (decide ((8#64).toNat ≠ 0) && decide ((8#64).toNat ≥ 64)) = false := by decide
        simp only [eval, setL, hA, hm, setLocal, if_true, h8, Bool.false_eq_true, if_false]
        rw [hd, SipHashCode.word_cons]
        rfl
  have f0 := assign_frag o (s := s) (x := x) (e := Syntax.n 0) rfl (v := 0) rfl hx
  refine frag_append (xs := [_]) (frag_conseq f0 (fun _ h => h) fun u h => ?_) (step bs.length (Nat.le_refl _))
  rw [List.drop_length]
  exact h

/-! ## Tests the scanner makes -/

section

variable {t : PancakeState σ}

/-- Either of two flags, as the scanner writes it. -/
theorem e_or2 {a b : PancakeExp} {p q : Bool} (ha : eval t a = some (bw p)) (hb : eval t b = some (bw q)) :
    eval t (.cmp .less (.const 0) (.op .add a b)) = some (bw (p || q)) := eval_or2 ha hb

/-- Whether two numbers differ. -/
theorem e_ne {a b : PancakeExp} {x y : Nat} (hx : x < 2 ^ 64) (hy : y < 2 ^ 64)
    (ha : eval t a = some (BitVec.ofNat 64 x)) (hb : eval t b = some (BitVec.ofNat 64 y)) :
    eval t (.cmp .equal (.cmp .equal a b) (.const 0)) = some (bw (decide (x ≠ y))) := by
  simp only [eval, ha, hb]
  rw [eq_word rfl rfl hx hy]
  by_cases h : x = y <;> simp [h, bw]

end

/-! ## What a fragment leaves as it was -/

/-- `t` is `s` but for the locals `xs` and the words `w`. -/
structure Kept (xs : List String) (w : Word → Prop) (s t : PancakeState σ) : Prop where
  locals : ∀ x, x ∉ xs → t.locals x = s.locals x
  memory : ∀ a, ¬ w a → t.memory a = s.memory a
  memaddrs : t.memaddrs = s.memaddrs
  be : t.be = s.be
  base : t.baseAddr = s.baseAddr
  ffi : t.ffi = s.ffi
  code : t.code = s.code
  keeps : Safe.Keeps s t

theorem kept_refl (xs : List String) (w : Word → Prop) (s : PancakeState σ) : Kept xs w s s :=
  ⟨fun _ _ => rfl, fun _ _ => rfl, rfl, rfl, rfl, rfl, rfl, Safe.keeps_refl s⟩

theorem kept_trans {xs : List String} {w : Word → Prop} {s t u : PancakeState σ} (h1 : Kept xs w s t)
    (h2 : Kept xs w t u) : Kept xs w s u :=
  ⟨fun x hx => (h2.locals x hx).trans (h1.locals x hx), fun a ha => (h2.memory a ha).trans (h1.memory a ha),
    h2.memaddrs.trans h1.memaddrs, h2.be.trans h1.be, h2.base.trans h1.base, h2.ffi.trans h1.ffi,
    h2.code.trans h1.code, Safe.keeps_trans h1.keeps h2.keeps⟩

/-- A local bound stays bound. -/
theorem kept_has {xs : List String} {w : Word → Prop} {s t : PancakeState σ} (h : Kept xs w s t) {y : String}
    (hb : ∃ v, s.locals y = some v) : ∃ v, t.locals y = some v :=
  Option.isSome_iff_exists.mp (h.keeps y (by obtain ⟨v, hv⟩ := hb; simp [hv]))

theorem kept_set {xs : List String} {w : Word → Prop} {s t : PancakeState σ} (h : Kept xs w s t) {x : String}
    (hx : x ∈ xs) (v : Value) : Kept xs w s (setL t x v) :=
  ⟨fun y hy => by simp [setL, setLocal, show y ≠ x from fun e => hy (e ▸ hx), h.locals y hy], h.memory,
    h.memaddrs, h.be, h.base, h.ffi, h.code, Safe.keeps_trans h.keeps (Safe.keeps_set t x v)⟩

theorem kept_word {xs : List String} {w : Word → Prop} {s t : PancakeState σ} (h : Kept xs w s t) {a : Word}
    (ha : w a) (v : Word) : Kept xs w s { t with memory := fun k => if k = a then v else t.memory k } :=
  ⟨h.locals, fun x hx => by
    show (if x = a then v else t.memory x) = s.memory x
    rw [if_neg (fun e : x = a => hx (e ▸ ha))]
    exact h.memory x hx, h.memaddrs, h.be, h.base, h.ffi, h.code, fun y hy => h.keeps y hy⟩

/-- …so an octet in no word of `w` reads as it did. -/
theorem kept_load {xs : List String} {w : Word → Prop} {s t : PancakeState σ} (h : Kept xs w s t) {a : Word}
    (ha : ¬ w (byteAlign a)) : memLoadByte t.memory t.memaddrs t.be a = memLoadByte s.memory s.memaddrs s.be a := by
  simp only [memLoadByte, h.memaddrs, h.be, h.memory _ ha]

/-- **A word checked in range**: in it, `fail` is not run. -/
theorem kept_skip (o : Oracle σ) {fail : List Syntax.PStmt} (hfl : LowKK fail) (hfd : declared fail = [])
    {x : String} {hi : Nat} (hhi : hi < 2 ^ 63) {P : Assn σ} (hP : Safe.ClockFree P)
    (h : ∀ u, P u → ∃ n, u.locals x = some (BitVec.ofNat 64 n) ∧ n ≤ hi) :
    Frag o [ScanProg.kept fail x hi] P P :=
  frag_skip o (C := .cmp .less (.const 0) (.op .add (.cmp .less (.var x) (.const 0))
    (.cmp .less (.const (BitVec.ofNat 64 hi)) (.var x)))) rfl hfl hP (fun u hu => by
      obtain ⟨n, hn, hle⟩ := h u hu
      have hv : eval u (.var x) = some (BitVec.ofNat 64 n) := hn
      rw [e_or2 (eval_lt (x := n) (y := 0) (by omega) (by decide) hv rfl)
        (eval_lt (x := hi) (y := n) hhi (by omega) rfl hv)]
      simp [bw]; omega) (noDecl _ hfd)

/-- **A branch on a verdict**: its arm when the verdict holds, nothing when it does not. -/
theorem flagIf_frag (o : Oracle σ) {x : String} {body : List Syntax.PStmt} (hl : LowKK body)
    (hd : declared body = []) {b : Bool} {P Q : Assn σ} (hQ : Safe.ClockFree Q)
    (hx : ∀ u, P u → u.locals x = some (bw b)) (ht : b = true → Frag o body P Q) (he : b = false → ∀ u, P u → Q u) :
    Frag o [.ite (Syntax.v x) body []] P Q :=
  frag_ite o (C := .var x) rfl hQ (fun u hu => ⟨_, by simp only [eval]; exact hx u hu⟩)
    (by
      cases b with
      | true => exact frag_conseq (ht rfl) (fun u h => h.1) fun _ h => h
      | false => exact frag_unsat hl fun u ⟨hu, hne⟩ => hne (by simp only [eval]; rw [hx u hu]; rfl))
    (noDecl _ hd)
    (frag_nil o fun u ⟨hu, h0⟩ => by
      cases b with
      | true => simp only [eval] at h0; rw [hx u hu] at h0; cases h0
      | false => exact he rfl u hu)
    (noDecl _ rfl)

/-- **A branch on a flag known**: its arm when the flag is set, the other when not. -/
theorem frag_if (o : Oracle σ) {c : Syntax.PExpr} {C : PancakeExp} (hc : Lower.lowerExp c = some C)
    {t e : List Syntax.PStmt} (hlt : LowKK t) (hle : LowKK e) (hdt : declared t = []) (hde : declared e = [])
    {P Q : Assn σ} (hQ : Safe.ClockFree Q) {b : Bool} (hv : ∀ u, P u → eval u C = some (bw b))
    (ht : b = true → Frag o t P Q) (he : b = false → Frag o e P Q) : Frag o [.ite c t e] P Q := by
  refine frag_ite o hc hQ (fun u hu => ⟨_, hv u hu⟩) ?_ (noDecl _ hdt) ?_ (noDecl _ hde)
  · cases b with
    | true => exact frag_conseq (ht rfl) (fun u h => h.1) fun _ h => h
    | false => exact frag_unsat hlt fun u ⟨hu, hne⟩ => hne (by rw [hv u hu]; rfl)
  · cases b with
    | true => exact frag_unsat hle fun u ⟨hu, h0⟩ =>
        absurd (Option.some.inj ((hv u hu).symm.trans h0)) (by decide)
    | false => exact frag_conseq (he rfl) (fun u h => h.1) fun _ h => h

end DN.News.ScanRun
