-- SPDX-License-Identifier: AGPL-3.0-or-later
import DN.Compiler.Safe
import DN.Compiler.Region
import DN.Server.Skeleton

/-!
# DN.Server.SkeletonSafe

**The server loop never fails, whatever its host does.** For every FFI oracle, every clock and
every content of the heap, a run of `Skeleton.main` from a state whose heap covers the layout
ends only as a run may end — out of clock, a call the host ended, or a return — and never in
`Fail` (`Entry.Fails`). `printed_never_fails` ties this to the text the gate prints: a `main`
without parameters that is not exported, whose lowering is `mainP`. That the Pancake parser reads
the text as that lowering, up to the canonical form it is compared in, is checked of this program
by `scripts/parser_contract.py`, not proved.

The premise `Covers` says, in the terms the semantics checks, that every word of the layout is in
the program's memory: the word holding each of its bytes, and each of its words. It holds of a heap
of just the layout's aligned words from an aligned `@base` (`covers_heap`); `@base` being aligned
is what the compiler's own theorem assumes of the heap, not something proved here.
-/

namespace DN.Server.SkeletonSafe

open DN.Compiler DN.Compiler.Region DN.Compiler.Safe DN.Server Layout

variable {σ : Type}

/-! ## The program, as it lowers -/

private def c (k : Nat) : PancakeExp := .const (BitVec.ofNat 64 k)
private def add (a b : PancakeExp) : PancakeExp := .op .add a b
private def at' (k : Nat) : PancakeExp := add .base (c k)
private def x (name : String) : PancakeExp := .var name

def copyP : PancakeProg :=
  .dec "j" (c 0)
    (.seq (.while_ (.cmp .less (x "j") (x "len"))
        (.seq (.storeByte (add (add (x "ac") (c actionHead)) (x "j"))
            (.loadByte (add (add (x "ev") (c eventHead)) (x "j"))))
          (.assign "j" (add (x "j") (c 1)))))
      (.assign "m" (add (x "m") (c 1))))

def echoP : PancakeProg :=
  .seq (.cond (.cmp .less (x "len") (c 0)) (.ret (c 2)) .skip)
    (.seq (.cond (.cmp .less (c data) (x "len")) (.ret (c 2)) .skip)
      (.dec "ac" (add (at' (emitOff + 16)) (.mul (x "m") (c actionSlot)))
        (.seq (.store (x "ac") (c send))
          (.seq (.store (add (x "ac") (c 8)) (.loadWord (add (x "ev") (c 8))))
            (.seq (.store (add (x "ac") (c 16)) (.loadWord (add (x "ev") (c 16))))
              (.seq (.store (add (x "ac") (c 24)) (x "len"))
                (.seq (.store (add (x "ac") (c 32)) (c 1))
                  (.seq (.store (add (x "ac") (c 40)) (c 0)) copyP))))))))

def eventP : PancakeProg :=
  .dec "ev" (add (at' (nextOff + 16)) (.mul (x "i") (c eventSlot)))
    (.dec "len" (.loadWord (add (x "ev") (c 24)))
      (.seq (.cond (.cmp .equal (.loadWord (x "ev")) (c received)) echoP .skip)
        (.assign "i" (add (x "i") (c 1)))))

def fetchP : PancakeProg := .extCall nextName (at' confOff) (c confLen) (at' nextOff) (c nextLen)
def handP : PancakeProg := .extCall emitName (at' confOff) (c confLen) (at' emitOff) (c emitLen)

def turnP : PancakeProg :=
  .seq fetchP
    (.dec "k" (.loadWord (at' nextOff))
      (.seq (.cond (.cmp .less (x "k") (c 0)) (.ret (c 1)) .skip)
        (.seq (.cond (.cmp .less (c batch) (x "k")) (.ret (c 1)) .skip)
          (.dec "i" (c 0)
            (.dec "m" (c 0)
              (.seq (.while_ (.cmp .less (x "i") (x "k")) eventP)
                (.seq (.store (at' emitOff) (x "m"))
                  (.seq (.store (at' (emitOff + 8)) (c 0)) handP))))))))

def mainP : PancakeProg :=
  .seq (.store (at' confOff) (c version))
    (.dec "going" (c 1) (.seq (.while_ (x "going") turnP) (.ret (c 0))))

theorem lower_main : Lower.lower Skeleton.main = some mainP := rfl

/-! ## The premise, and the arithmetic of addresses -/

/-- The heap covers the layout: from `b`, the word that holds each byte of the layout, and each
word of it, is in the program's memory `dm`. -/
def Covers (dm : Word → Bool) (b : Word) : Prop :=
  (∀ off, off < size → dm (byteAlign (b + BitVec.ofNat 64 off)) = true) ∧
  (∀ off, off < size → off % 8 = 0 → dm (b + BitVec.ofNat 64 off) = true)

theorem add_ofNat (b : Word) (p q : Nat) :
    b + BitVec.ofNat 64 p + BitVec.ofNat 64 q = b + BitVec.ofNat 64 (p + q) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

theorem ofNat_mul (p q : Nat) : BitVec.ofNat 64 p * BitVec.ofNat 64 q = BitVec.ofNat 64 (p * q) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_mul, BitVec.toNat_ofNat]
  rw [← Nat.mul_mod]

/-- A byte array is read in full when the word of each of its bytes is in memory. -/
theorem readByteArray_some (m : Word → Word) (dm : Word → Bool) (be : Bool) :
    ∀ (n : Nat) (a : Word), (∀ j, j < n → dm (byteAlign (a + BitVec.ofNat 64 j)) = true) →
      ∃ bs, readByteArray m dm be a n = some bs := by
  intro n
  induction n with
  | zero => intro a _; exact ⟨[], rfl⟩
  | succ n ih =>
    intro a h
    have h0 : dm (byteAlign a) = true := by simpa using h 0 (by omega)
    obtain ⟨bs, hbs⟩ := ih (a + 1) fun j hj => by
      have := h (j + 1) (by omega)
      rwa [show a + 1 + BitVec.ofNat 64 j = a + BitVec.ofNat 64 (j + 1) by
        rw [show (1 : Word) = BitVec.ofNat 64 1 from rfl, add_ofNat, Nat.add_comm]]
    exact ⟨getByte a (m (byteAlign a)) be :: bs, by
      simp only [readByteArray, memLoadByte, h0, if_true, hbs]⟩

/-- The layout's bytes from `off`, `len` of them, are read in full. -/
theorem read_layout {m : Word → Word} {dm : Word → Bool} {be : Bool} {b : Word} (hc : Covers dm b)
    {off len : Nat} (h : off + len ≤ size) :
    ∃ bs, readByteArray m dm be (b + BitVec.ofNat 64 off) len = some bs :=
  readByteArray_some m dm be len _ fun j hj => by
    rw [add_ofNat]; exact hc.1 _ (by omega)

/-- A word that is neither negative nor above `bound`, as signed words, is `bound` or less. -/
theorem le_of_signed {w : Word} {bound : Nat} (hb : bound < 2 ^ 63)
    (h0 : signedLt w 0 = false) (h1 : signedLt (BitVec.ofNat 64 bound) w = false) :
    w = BitVec.ofNat 64 w.toNat ∧ w.toNat ≤ bound := by
  refine ⟨BitVec.eq_of_toNat_eq (by simp), ?_⟩
  unfold signedLt BitVec.slt at h0 h1
  simp only [decide_eq_false_iff_not, Int.not_lt] at h0 h1
  rw [toInt_ofNat_small bound hb] at h1
  have hz : (0 : Word).toInt = 0 := rfl
  rw [hz] at h0
  have hw := BitVec.toInt_eq_toNat_bmod w
  have hlt := w.isLt
  simp only [Int.bmod] at hw
  split at hw <;> omega

/-! ## What holds where

Every assertion below is about locals, `@base` and the memory domain only, never about the
clock, so each is `ClockFree` by definition. -/

/-- The loop's own invariant. -/
def Loop (s : PancakeState σ) : Prop :=
  Covers s.memaddrs s.baseAddr ∧ s.locals "going" = some 1

/-- In a turn, after the count of events is checked: `kv` events, `iv` of them taken, `mv`
answers made. -/
def Counted (s : PancakeState σ) (kv iv mv : Nat) : Prop :=
  Loop s ∧ kv ≤ batch ∧ mv ≤ iv ∧ iv ≤ kv ∧
  s.locals "k" = some (BitVec.ofNat 64 kv) ∧ s.locals "i" = some (BitVec.ofNat 64 iv) ∧
  s.locals "m" = some (BitVec.ofNat 64 mv)

/-- In one event: the `iv`-th, whose slot `ev` names, with its length checked to be `lv`. -/
def InEvent (s : PancakeState σ) (kv iv mv lv : Nat) : Prop :=
  Counted s kv iv mv ∧ iv < kv ∧ lv ≤ data ∧
  s.locals "ev" = some (s.baseAddr + BitVec.ofNat 64 (nextOff + 16 + iv * eventSlot)) ∧
  s.locals "len" = some (BitVec.ofNat 64 lv)

/-- Answering it: `ac` names the `mv`-th action slot, and `jv` of its bytes are copied. -/
def InCopy (s : PancakeState σ) (kv iv mv lv jv : Nat) : Prop :=
  InEvent s kv iv mv lv ∧ jv ≤ lv ∧
  s.locals "ac" = some (s.baseAddr + BitVec.ofNat 64 (emitOff + 16 + mv * actionSlot)) ∧
  s.locals "j" = some (BitVec.ofNat 64 jv)

theorem nums : nextOff = 128 ∧ eventSlot = 544 ∧ emitOff = 8848 ∧ actionSlot = 560 ∧
    size = 17824 ∧ batch = 16 ∧ data = 512 ∧ eventHead = 32 ∧ actionHead = 48 := by decide

/-- A small number compared with another, as signed words, is compared as a number. -/
theorem lt_small {p q : Nat} (hp : p < 2 ^ 63) (hq : q < 2 ^ 63) :
    signedLt (BitVec.ofNat 64 p) (BitVec.ofNat 64 q) = decide (p < q) :=
  signedLt_ofNat p q hp hq

theorem ofNat_add (p q : Nat) : BitVec.ofNat 64 p + BitVec.ofNat 64 q = BitVec.ofNat 64 (p + q) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

/-! ## Copying the bytes of an event -/

theorem copy_loop (o : Oracle σ) :
    Safe o (fun s => ∃ kv iv mv lv jv, InCopy s kv iv mv lv jv)
      (.while_ (.cmp .less (x "j") (x "len"))
        (.seq (.storeByte (add (add (x "ac") (c actionHead)) (x "j"))
            (.loadByte (add (add (x "ev") (c eventHead)) (x "j"))))
          (.assign "j" (add (x "j") (c 1)))))
      (fun s => ∃ kv iv mv lv jv, InCopy s kv iv mv lv jv) := by
  obtain ⟨n1, n2, n3, n4, n5, n6, n7, n8, n9⟩ := nums
  apply Safe.conseq (Safe.while_ ?_ ?_ ?_) (fun _ h => h) (fun _ h => h.1)
  · rintro s ⟨kv, iv, mv, lv, jv, h⟩
    simp only [x, eval, h.2.2.2, h.1.2.2.2.2]
    exact ⟨_, rfl⟩
  · apply Safe.seq (M := fun s => ∃ kv iv mv lv jv, InCopy s kv iv mv lv jv ∧ jv < lv)
    · apply Safe.storeByte
      rintro s ⟨⟨kv, iv, mv, lv, jv, h⟩, hne⟩
      obtain ⟨⟨⟨⟨hcov, hgo⟩, hk16, hmi, hik, hk, hi, hm⟩, hik', hl512, hev, hlen⟩, hjl, hac, hj⟩ := h
      have hjl' : jv < lv := by
        have h1 : jv < 2 ^ 63 := by omega
        have h2 : lv < 2 ^ 63 := by omega
        simp only [x, eval, hj, hlen, lt_small h1 h2] at hne
        by_cases hc : jv < lv
        · exact hc
        · simp [hc] at hne
      have hsrc : nextOff + 16 + iv * eventSlot + eventHead + jv < size := by
        rw [n1, n2, n5, n8]; omega
      have hdst : emitOff + 16 + mv * actionSlot + actionHead + jv < size := by
        rw [n3, n4, n5, n9]; omega
      have e1 : eval s (add (add (x "ac") (c actionHead)) (x "j")) =
          some (s.baseAddr + BitVec.ofNat 64 (emitOff + 16 + mv * actionSlot + actionHead + jv)) := by
        simp only [x, c, add, eval, hac, hj, add_ofNat]
      have e2 : ∃ w, eval s (.loadByte (add (add (x "ev") (c eventHead)) (x "j"))) = some w := by
        simp only [x, c, add, eval, hev, hj, add_ofNat, memLoadByte, hcov.1 _ hsrc, if_true]
        exact ⟨_, rfl⟩
      obtain ⟨w, e2⟩ := e2
      exact ⟨_, w, _, e1, e2, Bytes.memStore_eq _ _ _ _ _ (hcov.1 _ hdst),
        kv, iv, mv, lv, jv, ⟨⟨⟨⟨hcov, hgo⟩, hk16, hmi, hik, hk, hi, hm⟩, hik', hl512, hev, hlen⟩,
          hjl, hac, hj⟩, hjl'⟩
    · apply Safe.assign
      rintro s ⟨kv, iv, mv, lv, jv, h, hjl⟩
      obtain ⟨⟨⟨⟨hcov, hgo⟩, hk16, hmi, hik, hk, hi, hm⟩, hik', hl512, hev, hlen⟩, hjl0, hac, hj⟩ := h
      refine ⟨BitVec.ofNat 64 (jv + 1), BitVec.ofNat 64 jv, ?_, hj, kv, iv, mv, lv, jv + 1, ?_⟩
      · simp only [x, c, add, eval, hj, ofNat_add]
      · simp only [InCopy, InEvent, Counted, Loop, setLocal]
        simp only [hcov, hgo, hk, hi, hm, hev, hlen, hac]
        exact ⟨⟨⟨⟨trivial, rfl⟩, hk16, hmi, hik, rfl, rfl, rfl⟩, hik', hl512, rfl, rfl⟩, hjl, rfl, rfl⟩
    · intro s k h; exact h
  · intro s k h; exact h

/-- A word stored inside the layout: the address is `@base` and an aligned offset in it, and
what holds does not depend on memory. -/
theorem store_word (o : Oracle σ) {P : PancakeState σ → Prop} {a v : PancakeExp}
    (h : ∀ s, P s → Covers s.memaddrs s.baseAddr ∧ ∃ off w, off < size ∧ off % 8 = 0 ∧
      eval s a = some (s.baseAddr + BitVec.ofNat 64 off) ∧ eval s v = some w)
    (hmem : ∀ s m, P s → P { s with memory := m }) : Safe o P (.store a v) P := by
  apply Safe.store
  intro s hs
  obtain ⟨hcov, off, w, hoff, h8, ha, hv⟩ := h s hs
  exact ⟨_, w, fun k => if k = s.baseAddr + BitVec.ofNat 64 off then w else s.memory k, ha, hv,
    by simp only [memStoreWord, hcov.2 _ hoff h8, if_true], hmem s _ hs⟩

/-! ## Answering an event -/

/-- After an event is answered or passed over: `mv` answers, at most one more than `iv`. -/
def Passed (s : PancakeState σ) (kv iv mv : Nat) : Prop :=
  Loop s ∧ kv ≤ batch ∧ mv ≤ iv + 1 ∧ iv < kv ∧
  s.locals "k" = some (BitVec.ofNat 64 kv) ∧ s.locals "i" = some (BitVec.ofNat 64 iv) ∧
  s.locals "m" = some (BitVec.ofNat 64 mv)

/-- The action slot `ac` is named for the event. -/
def Answering (s : PancakeState σ) : Prop :=
  ∃ kv iv mv lv, InEvent s kv iv mv lv ∧
    s.locals "ac" = some (s.baseAddr + BitVec.ofNat 64 (emitOff + 16 + mv * actionSlot))

theorem copy_safe (o : Oracle σ) :
    Safe o Answering copyP (fun s => ∃ kv iv mv, Passed s kv iv mv) := by
  apply Safe.dec (P' := fun s => ∃ kv iv mv lv jv, InCopy s kv iv mv lv jv)
    (Q' := fun s => ∃ kv iv mv, Passed s kv iv mv)
  · rintro s ⟨kv, iv, mv, lv, h, hac⟩
    obtain ⟨⟨⟨hcov, hgo⟩, hk16, hmi, hik, hk, hi, hm⟩, hik', hl512, hev, hlen⟩ := h
    refine ⟨BitVec.ofNat 64 0, rfl, kv, iv, mv, lv, 0, ?_⟩
    simp only [InCopy, InEvent, Counted, Loop, setLocal]
    simp only [hgo, hk, hi, hm, hev, hlen, hac]
    exact ⟨⟨⟨⟨hcov, rfl⟩, hk16, hmi, hik, rfl, rfl, rfl⟩, hik', hl512, rfl, rfl⟩, Nat.zero_le _,
      rfl, rfl⟩
  · apply Safe.seq (copy_loop o) _ (fun s k h => h)
    apply Safe.assign
    rintro s ⟨kv, iv, mv, lv, jv, h⟩
    obtain ⟨⟨⟨⟨hcov, hgo⟩, hk16, hmi, hik, hk, hi, hm⟩, hik', hl512, hev, hlen⟩, hjl, hac, hj⟩ := h
    refine ⟨BitVec.ofNat 64 (mv + 1), BitVec.ofNat 64 mv, ?_, hm, kv, iv, mv + 1, ?_⟩
    · simp only [x, c, add, eval, hm, ofNat_add]
    · simp only [Passed, Loop, setLocal]
      simp only [hgo, hk, hi]
      exact ⟨⟨hcov, rfl⟩, hk16, by omega, hik', rfl, rfl, rfl⟩
  · rintro s t _ ⟨kv, iv, mv, ⟨hcov, hgo⟩, hk16, hmi, hik, hk, hi, hm⟩
    refine ⟨kv, iv, mv, ?_⟩
    simp only [Passed, Loop, resVar]
    simp only [hgo, hk, hi, hm]
    exact ⟨⟨hcov, rfl⟩, hk16, hmi, hik, rfl, rfl, rfl⟩

/-- An event taken: its slot `ev` named and its length `lenw` read, not yet checked. -/
def Taken (s : PancakeState σ) : Prop :=
  ∃ kv iv mv lenw, Counted s kv iv mv ∧ iv < kv ∧
    s.locals "ev" = some (s.baseAddr + BitVec.ofNat 64 (nextOff + 16 + iv * eventSlot)) ∧
    s.locals "len" = some lenw

/-- A word of the answer's slot, at `ac + off`. -/
theorem answer_word (o : Oracle σ) {a v : PancakeExp} (off : Nat) (hoff : off ≤ 40)
    (h8 : off % 8 = 0)
    (ha : ∀ (s : PancakeState σ) (p : Word), s.locals "ac" = some p →
      eval s a = some (p + BitVec.ofNat 64 off))
    (hv : ∀ s : PancakeState σ, Answering s → ∃ w, eval s v = some w) :
    Safe o Answering (.store a v) Answering := by
  obtain ⟨n1, n2, n3, n4, n5, n6, n7, n8, n9⟩ := nums
  apply store_word o _ (fun s m h => h)
  intro s hs
  obtain ⟨kv, iv, mv, lv, h, hac⟩ := hs
  obtain ⟨⟨⟨hcov, hgo⟩, hk16, hmi, hik, hk, hi, hm⟩, hik', hl512, hev, hlen⟩ := h
  obtain ⟨w, hw⟩ := hv s ⟨kv, iv, mv, lv, ⟨⟨⟨hcov, hgo⟩, hk16, hmi, hik, hk, hi, hm⟩, hik', hl512, hev, hlen⟩, hac⟩
  refine ⟨hcov, emitOff + 16 + mv * actionSlot + off, w, ?_, ?_, ?_, hw⟩
  · rw [n3, n4, n5]; rw [n6] at hk16; omega
  · rw [n3, n4]; omega
  · rw [ha s _ hac, add_ofNat]

/-- A word of the event's slot, at `ev + off`, can be read. -/
theorem event_word {s : PancakeState σ} {kv iv mv lv : Nat} (h : InEvent s kv iv mv lv)
    (off : Nat) (hoff : off ≤ 24) (h8 : off % 8 = 0) :
    ∃ w, eval s (.loadWord (add (x "ev") (c off))) = some w := by
  obtain ⟨n1, n2, n3, n4, n5, n6, n7, n8, n9⟩ := nums
  obtain ⟨⟨⟨hcov, hgo⟩, hk16, hmi, hik, hk, hi, hm⟩, hik', hl512, hev, hlen⟩ := h
  have hd := hcov.2 (nextOff + 16 + iv * eventSlot + off)
    (by rw [n1, n2, n5]; rw [n6] at hk16; omega) (by rw [n1, n2]; omega)
  simp only [x, c, add, eval, hev, add_ofNat, hd, if_true]
  exact ⟨_, rfl⟩

theorem echo_safe (o : Oracle σ) :
    Safe o Taken echoP (fun s => ∃ kv iv mv, Passed s kv iv mv) := by
  obtain ⟨n1, n2, n3, n4, n5, n6, n7, n8, n9⟩ := nums
  -- The two checks of the length: afterwards it is a number no larger than a slot's data.
  apply Safe.seq (M := fun s => ∃ kv iv mv lenw, Counted s kv iv mv ∧ iv < kv ∧
      s.locals "ev" = some (s.baseAddr + BitVec.ofNat 64 (nextOff + 16 + iv * eventSlot)) ∧
      s.locals "len" = some lenw ∧ signedLt lenw 0 = false) _ _ (fun s k h => h)
  · apply Safe.cond
    · rintro s ⟨kv, iv, mv, lenw, h, hik, hev, hlen⟩
      simp only [x, c, eval, hlen]
      exact ⟨_, rfl⟩
    · exact Safe.ret fun s _ => ⟨_, rfl⟩
    · apply Safe.conseq (Safe.skip o _) (fun s h => h)
      rintro s ⟨⟨kv, iv, mv, lenw, h, hik, hev, hlen⟩, hz⟩
      refine ⟨kv, iv, mv, lenw, h, hik, hev, hlen, ?_⟩
      simp only [x, c, eval, hlen] at hz
      by_cases hb : signedLt lenw (BitVec.ofNat 64 0) = true
      · simp [hb] at hz
      · simpa using hb
  apply Safe.seq (M := fun s => ∃ kv iv mv lv, InEvent s kv iv mv lv) _ _ (fun s k h => h)
  · apply Safe.cond
    · rintro s ⟨kv, iv, mv, lenw, h, hik, hev, hlen, _⟩
      simp only [x, c, eval, hlen]
      exact ⟨_, rfl⟩
    · exact Safe.ret fun s _ => ⟨_, rfl⟩
    · apply Safe.conseq (Safe.skip o _) (fun s h => h)
      rintro s ⟨⟨kv, iv, mv, lenw, h, hik, hev, hlen, h0⟩, hz⟩
      simp only [x, c, eval, hlen] at hz
      have h1 : signedLt (BitVec.ofNat 64 data) lenw = false := by
        by_cases hb : signedLt (BitVec.ofNat 64 data) lenw = true
        · simp [hb] at hz
        · simpa using hb
      obtain ⟨heq, hle⟩ := le_of_signed (by rw [n7]; omega) h0 h1
      exact ⟨kv, iv, mv, lenw.toNat, h, hik, hle, hev, by rw [hlen, ← heq]⟩
  -- The answer's slot, its six words, then the bytes.
  apply Safe.dec (P' := Answering) (Q' := fun s => ∃ kv iv mv, Passed s kv iv mv)
  · rintro s ⟨kv, iv, mv, lv, h, hik', hl512, hev, hlen⟩
    obtain ⟨⟨hcov, hgo⟩, hk16, hmi, hik, hk, hi, hm⟩ := h
    refine ⟨s.baseAddr + BitVec.ofNat 64 (emitOff + 16 + mv * actionSlot), ?_, kv, iv, mv, lv, ?_, ?_⟩
    · simp only [x, c, add, at', eval, hm, ofNat_mul, add_ofNat]
    · simp only [InEvent, Counted, Loop, setLocal]
      simp only [hgo, hk, hi, hm, hev, hlen]
      exact ⟨⟨⟨hcov, rfl⟩, hk16, hmi, hik, rfl, rfl, rfl⟩, hik', hl512, rfl, rfl⟩
    · simp only [setLocal, if_true]
  · have hac0 : ∀ (s : PancakeState σ) (p : Word), s.locals "ac" = some p →
        eval s (x "ac") = some (p + BitVec.ofNat 64 0) := by
      intro s p h; simp only [x, eval, h, BitVec.add_zero]
    have hacn : ∀ n, ∀ (s : PancakeState σ) (p : Word), s.locals "ac" = some p →
        eval s (add (x "ac") (c n)) = some (p + BitVec.ofNat 64 n) := by
      intro n s p h; simp only [x, c, add, eval, h]
    refine Safe.seq (answer_word o 0 (by decide) (by decide) hac0 fun s _ => ⟨_, rfl⟩) ?_
      (fun s k h => h)
    refine Safe.seq (answer_word o 8 (by decide) (by decide) (hacn 8) ?_) ?_ (fun s k h => h)
    · rintro s ⟨kv, iv, mv, lv, h, _⟩; exact event_word h 8 (by decide) (by decide)
    refine Safe.seq (answer_word o 16 (by decide) (by decide) (hacn 16) ?_) ?_ (fun s k h => h)
    · rintro s ⟨kv, iv, mv, lv, h, _⟩; exact event_word h 16 (by decide) (by decide)
    refine Safe.seq (answer_word o 24 (by decide) (by decide) (hacn 24) ?_) ?_ (fun s k h => h)
    · rintro s ⟨kv, iv, mv, lv, h, _⟩
      simp only [x, eval, h.2.2.2.2]
      exact ⟨_, rfl⟩
    refine Safe.seq (answer_word o 32 (by decide) (by decide) (hacn 32) fun s _ => ⟨_, rfl⟩) ?_
      (fun s k h => h)
    exact Safe.seq (answer_word o 40 (by decide) (by decide) (hacn 40) fun s _ => ⟨_, rfl⟩)
      (copy_safe o) (fun s k h => h)
  · rintro s t _ ⟨kv, iv, mv, ⟨hcov, hgo⟩, hk16, hmi, hik, hk, hi, hm⟩
    refine ⟨kv, iv, mv, ?_⟩
    simp only [Passed, Loop, resVar]
    simp only [hgo, hk, hi, hm]
    exact ⟨⟨hcov, rfl⟩, hk16, hmi, hik, rfl, rfl, rfl⟩

/-! ## One event, and every event of a batch -/

theorem event_safe (o : Oracle σ) :
    Safe o (fun s => ∃ kv iv mv, Counted s kv iv mv ∧ iv < kv) eventP
      (fun s => ∃ kv iv mv, Counted s kv iv mv) := by
  obtain ⟨n1, n2, n3, n4, n5, n6, n7, n8, n9⟩ := nums
  apply Safe.dec (P' := fun s => ∃ kv iv mv, Counted s kv iv mv ∧ iv < kv ∧
      s.locals "ev" = some (s.baseAddr + BitVec.ofNat 64 (nextOff + 16 + iv * eventSlot)))
    (Q' := fun s => ∃ kv iv mv, Counted s kv iv mv)
  · rintro s ⟨kv, iv, mv, ⟨⟨hcov, hgo⟩, hk16, hmi, hik, hk, hi, hm⟩, hik'⟩
    refine ⟨s.baseAddr + BitVec.ofNat 64 (nextOff + 16 + iv * eventSlot), ?_, kv, iv, mv, ?_, hik', ?_⟩
    · simp only [x, c, add, at', eval, hi, ofNat_mul, add_ofNat]
    · simp only [Counted, Loop, setLocal]
      simp only [hgo, hk, hi, hm]
      exact ⟨⟨hcov, rfl⟩, hk16, hmi, hik, rfl, rfl, rfl⟩
    · simp only [setLocal, if_true]
  · apply Safe.dec (P' := Taken) (Q' := fun s => ∃ kv iv mv, Counted s kv iv mv)
    · rintro s ⟨kv, iv, mv, ⟨⟨hcov, hgo⟩, hk16, hmi, hik, hk, hi, hm⟩, hik', hev⟩
      have hd := hcov.2 (nextOff + 16 + iv * eventSlot + 24)
        (by rw [n1, n2, n5]; rw [n6] at hk16; omega) (by rw [n1, n2]; omega)
      refine ⟨s.memory (s.baseAddr + BitVec.ofNat 64 (nextOff + 16 + iv * eventSlot + 24)), ?_,
        kv, iv, mv, s.memory (s.baseAddr + BitVec.ofNat 64 (nextOff + 16 + iv * eventSlot + 24)),
        ?_, hik', ?_, ?_⟩
      · simp only [x, c, add, eval, hev, add_ofNat, hd, if_true]
      · simp only [Counted, Loop, setLocal]
        simp only [hgo, hk, hi, hm]
        exact ⟨⟨hcov, rfl⟩, hk16, hmi, hik, rfl, rfl, rfl⟩
      · simp [setLocal, hev]
      · simp only [setLocal, if_true]
    · apply Safe.seq (M := fun s => ∃ kv iv mv, Passed s kv iv mv) _ _ (fun s k h => h)
      · apply Safe.cond
        · rintro s ⟨kv, iv, mv, lenw, ⟨⟨hcov, hgo⟩, hk16, hmi, hik, hk, hi, hm⟩, hik', hev, hlen⟩
          have hd := hcov.2 (nextOff + 16 + iv * eventSlot)
            (by rw [n1, n2, n5]; rw [n6] at hk16; omega) (by rw [n1, n2]; omega)
          simp only [x, c, eval, hev, hd, if_true]
          exact ⟨_, rfl⟩
        · exact Safe.conseq (echo_safe o) (fun s h => h.1) (fun s h => h)
        · apply Safe.conseq (Safe.skip o _) (fun s h => h.1)
          rintro s ⟨kv, iv, mv, lenw, ⟨⟨hcov, hgo⟩, hk16, hmi, hik, hk, hi, hm⟩, hik', hev, hlen⟩
          exact ⟨kv, iv, mv, ⟨hcov, hgo⟩, hk16, by omega, hik', hk, hi, hm⟩
      · apply Safe.assign
        rintro s ⟨kv, iv, mv, ⟨hcov, hgo⟩, hk16, hmi, hik', hk, hi, hm⟩
        refine ⟨BitVec.ofNat 64 (iv + 1), BitVec.ofNat 64 iv, ?_, hi, kv, iv + 1, mv, ?_⟩
        · simp only [x, c, add, eval, hi, ofNat_add]
        · simp only [Counted, Loop, setLocal]
          simp only [hgo, hk, hm]
          exact ⟨⟨hcov, rfl⟩, hk16, hmi, by omega, rfl, rfl, rfl⟩
    · rintro s t _ ⟨kv, iv, mv, ⟨hcov, hgo⟩, hk16, hmi, hik, hk, hi, hm⟩
      refine ⟨kv, iv, mv, ?_⟩
      simp only [Counted, Loop, resVar]
      simp only [hgo, hk, hi, hm]
      exact ⟨⟨hcov, rfl⟩, hk16, hmi, hik, rfl, rfl, rfl⟩
  · rintro s t _ ⟨kv, iv, mv, ⟨hcov, hgo⟩, hk16, hmi, hik, hk, hi, hm⟩
    refine ⟨kv, iv, mv, ?_⟩
    simp only [Counted, Loop, resVar]
    simp only [hgo, hk, hi, hm]
    exact ⟨⟨hcov, rfl⟩, hk16, hmi, hik, rfl, rfl, rfl⟩

theorem events_safe (o : Oracle σ) :
    Safe o (fun s => ∃ kv iv mv, Counted s kv iv mv) (.while_ (.cmp .less (x "i") (x "k")) eventP)
      (fun s => ∃ kv iv mv, Counted s kv iv mv) := by
  obtain ⟨n1, n2, n3, n4, n5, n6, n7, n8, n9⟩ := nums
  apply Safe.conseq (Safe.while_ ?_ ?_ (fun s k h => h)) (fun s h => h) (fun s h => h.1)
  · rintro s ⟨kv, iv, mv, h⟩
    simp only [x, eval, h.2.2.2.2.2.1, h.2.2.2.2.1]
    exact ⟨_, rfl⟩
  · apply Safe.conseq (event_safe o) _ (fun s h => h)
    rintro s ⟨⟨kv, iv, mv, h⟩, hne⟩
    refine ⟨kv, iv, mv, h, ?_⟩
    obtain ⟨_, hk16, _, hik, hk, hi, _⟩ := h
    rw [n6] at hk16
    simp only [x, eval, hi, hk, lt_small (by omega : iv < 2 ^ 63) (by omega : kv < 2 ^ 63)] at hne
    by_cases hc : iv < kv
    · exact hc
    · simp [hc] at hne

/-! ## A turn of the loop, and `main` -/

/-- An external call on the configuration word and one area of the layout. -/
theorem call_safe (o : Oracle σ) (name : String) {P : PancakeState σ → Prop} (off len : Nat)
    (hlen : off + len ≤ size) (hlen64 : len < 2 ^ 64)
    (hcov : ∀ s, P s → Covers s.memaddrs s.baseAddr)
    (hframe : ∀ s m f, P s → P { s with memory := m, ffi := f }) :
    Safe o P (.extCall name (at' confOff) (c confLen) (at' off) (c len)) P := by
  obtain ⟨n1, n2, n3, n4, n5, n6, n7, n8, n9⟩ := nums
  apply Safe.extCall
  intro s hs
  have hc := hcov s hs
  obtain ⟨conf, hconf⟩ := read_layout (m := s.memory) (be := s.be) hc
    (off := confOff) (len := confLen) (by rw [n5]; decide)
  obtain ⟨arr, harr⟩ := read_layout (m := s.memory) (be := s.be) hc (off := off) (len := len) hlen
  refine ⟨_, _, _, _, conf, arr, rfl, rfl, rfl, rfl, ?_, ?_, fun f bytes _ => hframe s _ f hs⟩
  · simpa [c, BitVec.toNat_ofNat] using hconf
  · simpa [c, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlen64] using harr

theorem turn_safe (o : Oracle σ) : Safe o Loop turnP Loop := by
  obtain ⟨n1, n2, n3, n4, n5, n6, n7, n8, n9⟩ := nums
  refine Safe.seq (call_safe o nextName nextOff nextLen (by decide) (by decide) (fun s h => h.1)
    (fun s m f h => h)) ?_ (fun s k h => h)
  apply Safe.dec (P' := fun s => Loop s ∧ ∃ kw, s.locals "k" = some kw) (Q' := Loop)
  · rintro s ⟨hcov, hgo⟩
    have hd := hcov.2 nextOff (by decide) (by decide)
    refine ⟨s.memory (s.baseAddr + BitVec.ofNat 64 nextOff), ?_, ⟨hcov, ?_⟩,
      s.memory (s.baseAddr + BitVec.ofNat 64 nextOff), ?_⟩
    · simp only [c, add, at', eval, hd, if_true]
    · simp [setLocal, hgo]
    · simp only [setLocal, if_true]
  · apply Safe.seq (M := fun s => Loop s ∧ ∃ kw, s.locals "k" = some kw ∧ signedLt kw 0 = false)
      _ _ (fun s k h => h)
    · apply Safe.cond
      · rintro s ⟨_, kw, hk⟩; simp only [x, c, eval, hk]; exact ⟨_, rfl⟩
      · exact Safe.ret fun s _ => ⟨_, rfl⟩
      · apply Safe.conseq (Safe.skip o _) (fun s h => h)
        rintro s ⟨⟨hl, kw, hk⟩, hz⟩
        refine ⟨hl, kw, hk, ?_⟩
        simp only [x, c, eval, hk] at hz
        by_cases hb : signedLt kw (BitVec.ofNat 64 0) = true
        · simp [hb] at hz
        · simpa using hb
    apply Safe.seq (M := fun s => Loop s ∧ ∃ kv, kv ≤ batch ∧ s.locals "k" = some (BitVec.ofNat 64 kv))
      _ _ (fun s k h => h)
    · apply Safe.cond
      · rintro s ⟨_, kw, hk, _⟩; simp only [x, c, eval, hk]; exact ⟨_, rfl⟩
      · exact Safe.ret fun s _ => ⟨_, rfl⟩
      · apply Safe.conseq (Safe.skip o _) (fun s h => h)
        rintro s ⟨⟨hl, kw, hk, h0⟩, hz⟩
        simp only [x, c, eval, hk] at hz
        have h1 : signedLt (BitVec.ofNat 64 batch) kw = false := by
          by_cases hb : signedLt (BitVec.ofNat 64 batch) kw = true
          · simp [hb] at hz
          · simpa using hb
        obtain ⟨heq, hle⟩ := le_of_signed (by rw [n6]; decide) h0 h1
        exact ⟨hl, kw.toNat, hle, by rw [hk, ← heq]⟩
    apply Safe.dec (P' := fun s => Loop s ∧ ∃ kv, kv ≤ batch ∧
        s.locals "k" = some (BitVec.ofNat 64 kv) ∧ s.locals "i" = some (BitVec.ofNat 64 0))
      (Q' := Loop)
    · rintro s ⟨⟨hcov, hgo⟩, kv, hk16, hk⟩
      refine ⟨_, rfl, ⟨hcov, ?_⟩, kv, hk16, ?_, ?_⟩
      · simp [setLocal, hgo]
      · simp [setLocal, hk]
      · simp only [setLocal, if_true]
    · apply Safe.dec (P' := fun s => ∃ kv iv mv, Counted s kv iv mv) (Q' := Loop)
      · rintro s ⟨⟨hcov, hgo⟩, kv, hk16, hk, hi⟩
        refine ⟨_, rfl, kv, 0, 0, ⟨hcov, ?_⟩, hk16, Nat.le_refl _, Nat.zero_le _, ?_, ?_, ?_⟩
        · simp [setLocal, hgo]
        · simp [setLocal, hk]
        · simp [setLocal, hi]
        · simp only [setLocal, if_true]
      · refine Safe.seq (events_safe o) ?_ (fun s k h => h)
        refine Safe.seq (store_word o ?_ (fun s m h => h)) ?_ (fun s k h => h)
        · rintro s ⟨kv, iv, mv, ⟨hcov, hgo⟩, hk16, hmi, hik, hk, hi, hm⟩
          exact ⟨hcov, emitOff, BitVec.ofNat 64 mv, by decide, by decide, rfl,
            by simp only [x, eval, hm]⟩
        refine Safe.seq (store_word o ?_ (fun s m h => h)) ?_ (fun s k h => h)
        · rintro s ⟨kv, iv, mv, ⟨hcov, hgo⟩, _⟩
          exact ⟨hcov, emitOff + 8, BitVec.ofNat 64 0, by decide, by decide, rfl, rfl⟩
        apply Safe.conseq (call_safe o emitName (P := fun s => ∃ kv iv mv, Counted s kv iv mv)
          emitOff emitLen (by decide) (by decide) (fun s h => by
            obtain ⟨_, _, _, h, _⟩ := h; exact h.1) (fun s m f h => h)) (fun s h => h)
        rintro s ⟨kv, iv, mv, h, _⟩
        exact h
      · rintro s t _ ⟨hcov, hgo⟩
        exact ⟨hcov, by simp [resVar, hgo]⟩
    · rintro s t _ ⟨hcov, hgo⟩
      exact ⟨hcov, by simp [resVar, hgo]⟩
  · rintro s t _ ⟨hcov, hgo⟩
    exact ⟨hcov, by simp [resVar, hgo]⟩

theorem main_safe (o : Oracle σ) :
    Safe o (fun s => Covers s.memaddrs s.baseAddr) mainP (fun _ => False) := by
  obtain ⟨n1, n2, n3, n4, n5, n6, n7, n8, n9⟩ := nums
  refine Safe.seq (store_word o ?_ (fun s m h => h)) ?_ (fun s k h => h)
  · intro s hcov
    exact ⟨hcov, confOff, _, by rw [n5]; decide, by decide, rfl, rfl⟩
  apply Safe.dec (P' := Loop) (Q' := fun _ => False)
  · intro s hcov
    exact ⟨BitVec.ofNat 64 1, rfl, hcov, by simp [setLocal]⟩
  · refine Safe.seq (Safe.while_ ?_ (Safe.conseq (turn_safe o) (fun s h => h.1) (fun s h => h))
      (fun s k h => h)) (Safe.ret fun s _ => ⟨_, rfl⟩) (fun s k h => h)
    rintro s ⟨_, hgo⟩
    simp only [x, eval, hgo]
    exact ⟨_, rfl⟩
  · intro s t _ h
    exact h.elim

/-- **The server loop never fails, whatever its host does.** -/
theorem never_fails (o : Oracle σ) (s : PancakeState σ) (h : Covers s.memaddrs s.baseAddr) :
    ¬ Entry.Fails o mainP s :=
  Safe.not_fails (main_safe o) (fun _ => h)

/-- The same of the text the gate prints: it is the loop's own, the entry has the shape the
semantics runs, and the lowering is the program `never_fails` is about. -/
theorem printed_never_fails (o : Oracle σ) (s : PancakeState σ) (h : Covers s.memaddrs s.baseAddr)
    {src : String} (hsrc : Skeleton.source = .ok src) :
    src = Syntax.ppFun Skeleton.main ∧ Skeleton.main.exported = false ∧
      Skeleton.main.name = "main" ∧ Skeleton.main.params = [] ∧
      Lower.lower Skeleton.main = some mainP ∧ ¬ Entry.Fails o mainP s := by
  obtain ⟨he, hn, hpar⟩ := Checked.emitMain_entry hsrc
  exact ⟨Checked.emitMain_prints hsrc, he, hn, hpar, lower_main, never_fails o s h⟩

/-- A heap of the aligned words from `b`, `n` bytes of them. -/
def heapWords (b : Word) (n : Nat) (a : Word) : Bool :=
  a.toNat % 8 = 0 && b.toNat ≤ a.toNat && a.toNat < b.toNat + n

/-- The premise holds of a heap of just the layout, from any aligned `@base` it fits above. -/
theorem covers_heap (b : Word) (hb : b.toNat % 8 = 0) (hfit : b.toNat + size < 2 ^ 64) :
    Covers (heapWords b size) b := by
  have e : ∀ off, off < size → (b + BitVec.ofNat 64 off).toNat = b.toNat + off := by
    intro off hoff
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  refine ⟨fun off hoff => ?_, fun off hoff h8 => ?_⟩
  · simp only [heapWords, Bytes.byteAlign_toNat, e off hoff, Bool.and_eq_true, decide_eq_true_eq]
    have : size % 8 = 0 := by decide
    omega
  · simp only [heapWords, e off hoff, Bool.and_eq_true, decide_eq_true_eq]
    omega

/-- The premise holds of a heap of just the layout, above the first page. -/
theorem covers_witness : Covers (heapWords 4096 size) 4096 := covers_heap _ (by decide) (by decide)

/-- The loop's theorem at a concrete oracle. -/
theorem main_safe_witness :
    Safe (Oracle.idle (σ := Unit)) (fun s => Covers s.memaddrs s.baseAddr) mainP (fun _ => False) :=
  main_safe _

/-- A state inside an event: the first of one, with an empty payload, in a heap that is all
memory. -/
def inEventState : PancakeState Unit :=
  { locals := fun name =>
      if name = "going" then some 1 else if name = "k" then some (BitVec.ofNat 64 1)
      else if name = "i" then some (BitVec.ofNat 64 0) else if name = "m" then some (BitVec.ofNat 64 0)
      else if name = "ev" then some (0 + BitVec.ofNat 64 (nextOff + 16 + 0 * eventSlot))
      else if name = "len" then some (BitVec.ofNat 64 0) else none,
    memory := fun _ => 0, memaddrs := fun _ => true, be := false, clock := 0, ffi := (),
    baseAddr := 0 }

theorem inEvent_witness : InEvent inEventState 1 0 0 0 :=
  ⟨⟨⟨⟨fun _ _ => rfl, fun _ _ _ => rfl⟩, rfl⟩, by decide, Nat.le_refl _, Nat.zero_le _, rfl, rfl,
    rfl⟩, by decide, Nat.zero_le _, rfl, rfl⟩

end DN.Server.SkeletonSafe
