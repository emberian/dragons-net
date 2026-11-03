-- SPDX-License-Identifier: AGPL-3.0-or-later
import DN.News.AbnfLayout
import DN.News.ScanArea
import DN.News.FramerCode
import DN.Compiler.FragRet
import DN.News.FunRun

/-!
# DN.News.AbnfSets

The operations on sets of `DN.News.AbnfProg`, proven to do what they are named for. A slot of the area holds a
set of positions (`SetAt`): the bits of its words are the set, and its window's ends bound the words holding one,
an empty set's window empty. Each operation, from the area at `@base + ofs` and slots holding sets, returns and
leaves its slot holding the set it names, every word outside it as it was (`setClear_ok` …), and a call of it
takes that (`setUnion_call` …). The area's sizes come from `AbnfLayout`, a run's bookkeeping from `FunRun`.
-/

namespace DN.News.AbnfSets

open DN.Compiler DN.Compiler.Wp DN.Compiler.WpRet DN.Compiler.Frag DN.News.AbnfProg DN.News.AbnfLayout
open DN.News.ScanRun (at_ at_add at_ne at_inj Vals vals_lookup vals_cons vals_set Fresh without lookup_head)
open DN.News.FramerCode (bw ev_var)
open DN.News.FunRun

variable {σ : Type}

/-! ## The area -/

theorem aPow_eq : aPow = 65896 := rfl

theorem setSize_eq : setSize = 8224 := rfl
theorem setWords_eq : setWords = 1026 := rfl
theorem inputMax_eq : inputMax = 65536 := rfl

/-- Where slot `k` starts. -/
def off (k : Nat) : Nat := aSets + k * setSize

theorem off_lt {k : Nat} (hk : k < slots) (i : Nat) (hi : i < setSize) : off k + i < aSets + slots * setSize := by
  have : (k + 1) * setSize ≤ slots * setSize := Nat.mul_le_mul_right _ hk
  simp only [off, Nat.add_mul, Nat.one_mul] at this ⊢
  omega

theorem off_small {k : Nat} (hk : k < slots) (i : Nat) (hi : i < setSize) : off k + i < 2 ^ 22 := by
  have h1 := slots_le
  have h2 := aSets_le
  have : k * setSize ≤ 256 * setSize := Nat.mul_le_mul_right _ (by omega)
  simp only [off, setSize_eq] at this hi ⊢
  omega

/-- Slot `k` lies past the tables; for a closed `k` this keeps `off k` folded (unfolding it, the kernel works out
`aSets`). -/
theorem aSets_le_off (k : Nat) : aSets ≤ off k := Nat.le_add_right _ _

theorem off_mod (k : Nat) : off k % 8 = 0 := by
  have := aSets_mod
  simp only [off, setSize_eq]
  omega

/-- The area at `A`, `@base` plus `ofs`: aligned, each of its words addressable. -/
structure Area (ofs : Nat) (A : Word) (s : PancakeState σ) : Prop where
  base : s.baseAddr + BitVec.ofNat 64 ofs = A
  hA : A.toNat % 8 = 0
  dom : ∀ x, x < aSets + slots * setSize → x % 8 = 0 → s.memaddrs (at_ A x) = true

/-- The area as it was, the locals changed. -/
theorem area_locals {ofs : Nat} {A : Word} {s : PancakeState σ} (hA : Area ofs A s) (L : String → Option Value) :
    Area ofs A { s with locals := L } := ⟨hA.base, hA.hA, hA.dom⟩

/-- Word `i` of slot `k`. -/
def slotW (A : Word) (k i : Nat) : Word := at_ A (off k + 8 * i)

/-- A word of slot `k`. -/
def InSlot (A : Word) (k : Nat) (a : Word) : Prop := ∃ i, i < setSize / 8 ∧ a = slotW A k i

/-- Every word outside slot `k` as in `m0`. -/
def Frame (A : Word) (k : Nat) (m0 m : Word → Word) : Prop := ∀ a, ¬InSlot A k a → m a = m0 a

theorem slotW_inj {A : Word} {k k' i i' : Nat} (hk : k < slots) (hk' : k' < slots) (hi : i < setSize / 8)
    (hi' : i' < setSize / 8) (h : slotW A k i = slotW A k' i') : k = k' ∧ i = i' := by
  have h1 := off_small hk (8 * i) (by rw [setSize_eq] at hi ⊢; omega)
  have h2 := off_small hk' (8 * i') (by rw [setSize_eq] at hi' ⊢; omega)
  have e := at_inj (by omega) (by omega) h
  simp only [off, setSize_eq] at e
  rw [setSize_eq] at hi hi'
  have hk2 : k = k' := by
    rcases Nat.lt_trichotomy k k' with hl | hl | hl
    · have : (k + 1) * 8224 ≤ k' * 8224 := Nat.mul_le_mul_right _ hl
      omega
    · exact hl
    · have : (k' + 1) * 8224 ≤ k * 8224 := Nat.mul_le_mul_right _ hl
      omega
  subst hk2
  exact ⟨rfl, by omega⟩

/-! ## A set in a slot -/

/-- Slot `k` of memory `m` holds the positions `S`: the window's ends below the words' count, the bits of word `w`
those of `S` from `64 * w`, every position of `S` in a word of the window, and a window holding a word only if the
set is not empty. It is weaker than what the program keeps (`AbnfProg.sLo`): a window need not be tight, nor an
empty one `[1, 0]`. -/
structure SetAt (m : Word → Word) (A : Word) (k : Nat) (S : Nat → Bool) : Prop where
  lo : (m (slotW A k 0)).toNat < setWords
  hi : (m (slotW A k 1)).toNat < setWords
  bits : ∀ w, w < setWords → ∀ j, j < 64 → (m (slotW A k (2 + w))).getLsbD j = S (64 * w + j)
  small : ∀ x, S x = true → x < 64 * setWords
  win : ∀ x, S x = true → (m (slotW A k 0)).toNat ≤ x / 64 ∧ x / 64 ≤ (m (slotW A k 1)).toNat
  some : (m (slotW A k 0)).toNat ≤ (m (slotW A k 1)).toNat → ∃ x, S x = true

/-- A slot's set kept where only words outside it changed. -/
theorem setAt_frame {m m' : Word → Word} {A : Word} {k : Nat} {S : Nat → Bool} (h : SetAt m A k S)
    (hm : ∀ i, i < setSize / 8 → m' (slotW A k i) = m (slotW A k i)) : SetAt m' A k S where
  lo := by rw [hm 0 (by decide)]; exact h.lo
  hi := by rw [hm 1 (by decide)]; exact h.hi
  bits := fun w hw j hj => by
    rw [hm (2 + w) (by rw [setSize_eq]; rw [setWords_eq] at hw; omega)]; exact h.bits w hw j hj
  small := h.small
  win := fun x hx => by rw [hm 0 (by decide), hm 1 (by decide)]; exact h.win x hx
  some := fun hl => h.some (by rwa [hm 0 (by decide), hm 1 (by decide)] at hl)

/-- Another slot's set kept by a frame. -/
theorem setAt_other {m m' : Word → Word} {A : Word} {k k' : Nat} {S : Nat → Bool} (h : SetAt m A k' S)
    (hk : k < slots) (hk' : k' < slots) (hne : k ≠ k') (hf : Frame A k m m') : SetAt m' A k' S :=
  setAt_frame h fun _ hi => hf _ fun ⟨_, hi', e⟩ => hne (slotW_inj hk hk' hi' hi e.symm).1

/-- A bit of a word outside slot `k`'s window is not in its set. -/
theorem setAt_out {m : Word → Word} {A : Word} {k : Nat} {S : Nat → Bool} (h : SetAt m A k S) {w j : Nat} (hj : j < 64)
    (hw : ¬((m (slotW A k 0)).toNat ≤ w ∧ w ≤ (m (slotW A k 1)).toNat)) : S (64 * w + j) = false := by
  cases e : S (64 * w + j)
  · rfl
  · have := h.win _ e
    rw [show (64 * w + j) / 64 = w by omega] at this
    exact absurd this hw

/-! ## A function's state -/

/-- **A word of the area stored**, at an address the same from every state, of a value of the memory. -/
theorem runF_store (o : Oracle σ) {ofs : Nat} {A : Word} {s0 : PancakeState σ} (hA : Area ofs A s0)
    {l : List (String × Value)} {F G : (Word → Word) → Prop} {d e : Syntax.PExpr} {D E : PancakeExp}
    (hd : Lower.lowerExp d = some D) (he : Lower.lowerExp e = some E) {y : Nat} (hy : y < aSets + slots * setSize)
        (hy8 : y % 8 = 0)
    (hD : ∀ u, RunF s0 l F u → eval u D = some (at_ A y)) {val : (Word → Word) → Word}
    (hE : ∀ u, RunF s0 l F u → eval u E = some (val u.memory)) (hG : ∀ m, F m → G (upd m (at_ A y) (val m))) :
    Frag o [.store d e] (RunF s0 l F) (RunF s0 l G) :=
  store_frag o hd he (runF_clock _ _ _) fun u h =>
    ⟨_, _, hD u h, hE u h, by rw [h.1.memaddrs]; exact hA.dom y hy hy8,
      ⟨h.1.vals, h.1.memaddrs, h.1.base, h.1.code, h.1.be⟩, hG _ h.2⟩

/-- A word of the area read. -/
theorem load_eval {ofs : Nat} {A : Word} {s0 u : PancakeState σ} (hA : Area ofs A s0)
    (hm : u.memaddrs = s0.memaddrs) {E : PancakeExp} {y : Nat} (hy : y < aSets + slots * setSize) (hy8 : y % 8 = 0)
    (hE : eval u E = some (at_ A y)) : eval u (.loadWord E) = some (u.memory (at_ A y)) := by
  exact WpBytes.eval_load hE (by rw [hm]; exact hA.dom y hy hy8) rfl

/-- The area's address from `@base`. -/
theorem areaAt_eval {ofs : Nat} {A : Word} {s0 u : PancakeState σ} (hA : Area ofs A s0)
    (hb : u.baseAddr = s0.baseAddr) {E : PancakeExp} (hE : Lower.lowerExp (Syntax.atOff .base ofs) = some E) :
    eval u E = some A := by
  by_cases h0 : ofs = 0
  · subst h0
    simp only [Syntax.atOff, beq_self_eq_true, if_true, Lower.lowerExp, Option.some.injEq] at hE
    subst hE
    rw [← hA.base]; simp [eval, hb]
  · have : (ofs == 0) = false := by simpa using h0
    simp only [Syntax.atOff, this, Bool.false_eq_true, if_false, Syntax.eAdd, Syntax.n, Lower.lowerExp,
      Option.some.injEq] at hE
    subst hE
    rw [← hA.base]; simp [eval, hb]

/-- Slot `x`'s address as the program computes it. -/
def slotE (x : String) : PancakeExp :=
  .op .add (.op .add (.var "a") (.const (BitVec.ofNat 64 aSets))) (.mul (.var x) (.const (BitVec.ofNat 64 setSize)))

/-- Slot `k`'s address, the area's in `a` and `k` in `x`. -/
theorem slot_eval {u : PancakeState σ} {A : Word} (ha : u.locals "a" = some A) {x : String} {k : Nat}
    (hx : u.locals x = some (BitVec.ofNat 64 k)) : eval u (slotE x) = some (at_ A (off k)) := by
  simp only [slotE, eval, ha, hx]
  rw [← BitVec.ofNat_mul, BitVec.add_assoc, ← BitVec.ofNat_add]; rfl

/-- **A check passed**: the local `x` in `[0, hi]`. -/
theorem kept_frag (o : Oracle σ) {x : String} {hi : Nat} (hhi : hi < 2 ^ 63) {P : Assn σ} (hP : Safe.ClockFree P)
    (h : ∀ u, P u → ∃ k, u.locals x = some (BitVec.ofNat 64 k) ∧ k ≤ hi) : Frag o [kept x hi] P P :=
  ScanRun.frag_if o rfl (lowK_any _ (k := .skip) rfl) (fun k => ⟨k, rfl⟩) rfl rfl hP (b := false) (fun u hu => by
      obtain ⟨k, hk, hkh⟩ := h u hu
      have e := FramerCode.eval_or2 (t := u)
        (FramerCode.eval_lt (a := .var x) (b := .const (BitVec.ofNat 64 0)) (x := k) (y := 0) (by omega) (by decide)
          (ev_var hk) rfl)
        (FramerCode.eval_lt (a := .const (BitVec.ofNat 64 hi)) (b := .var x) (x := hi) (y := k) hhi (by omega) rfl
          (ev_var hk))
      simp only [decide_eq_false (Nat.not_lt_zero k), decide_eq_false (Nat.not_lt.2 hkh), Bool.or_false] at e
      exact e)
    (fun e => absurd e (by decide)) fun _ => frag_nil o fun _ h => h

/-! ## The words of a slot -/

theorem slotW_zero (A : Word) (k : Nat) : slotW A k 0 = at_ A (off k) := by
  unfold slotW; rw [Nat.mul_zero, Nat.add_zero]

theorem slotW_lt {k : Nat} (hk : k < slots) {i : Nat} (hi : i < setSize / 8) : off k + 8 * i < aSets + slots *
    setSize :=
  off_lt hk _ (by rw [setSize_eq] at hi ⊢; omega)

theorem slotW_mod (k i : Nat) : (off k + 8 * i) % 8 = 0 := by have := off_mod k; omega

/-- The last word of slot `k`'s window, its address in `p`. -/
theorem hiAddr_eval {u : PancakeState σ} {E : PancakeExp} {p : String}
    (he : Lower.lowerExp (Syntax.atOff (Syntax.v p) sHi) = some E) {A : Word} {k : Nat}
    (hp : u.locals p = some (at_ A (off k))) : eval u E = some (slotW A k 1) := by
  cases he
  simp only [eval, hp, slotW, at_add]
  rfl

/-- Bit word `w` of slot `k`, its address in `p` and `w` in `x`. -/
theorem bit_eval {u : PancakeState σ} {E : PancakeExp} {p x : String}
    (he : Lower.lowerExp (bitWord p (Syntax.v x)) = some E) {A : Word} {k w : Nat}
    (hp : u.locals p = some (at_ A (off k))) (hx : u.locals x = some (BitVec.ofNat 64 w)) :
    eval u E = some (slotW A k (2 + w)) := by
  cases he
  simp only [eval, hp, hx]
  rw [← BitVec.ofNat_mul, at_add, at_add]
  exact congrArg (fun y => some (at_ A y)) (by simp only [sBits]; omega)

/-- A word of slot `k` read, its address in `p`. -/
theorem slotLoad_eval {ofs : Nat} {A : Word} {s0 u : PancakeState σ} (hA : Area ofs A s0)
    (hm : u.memaddrs = s0.memaddrs) {k : Nat} (hk : k < slots) {i : Nat} (hi : i < setSize / 8) {E : PancakeExp}
    (hE : eval u E = some (slotW A k i)) : eval u (.loadWord E) = some (u.memory (slotW A k i)) :=
  load_eval hA hm (slotW_lt hk hi) (slotW_mod k i) hE

/-- The first word of a slot's window read, its address in `p`. -/
theorem lo_eval {E : PancakeExp} {p : String} (he : Lower.lowerExp (word (Syntax.v p) sLo) = some E) {ofs : Nat}
    {A : Word} {s0 u : PancakeState σ} (hA : Area ofs A s0) (hm : u.memaddrs = s0.memaddrs) {k : Nat}
    (hk : k < slots) (hp : u.locals p = some (at_ A (off k))) :
    eval u E = some (BitVec.ofNat 64 (u.memory (slotW A k 0)).toNat) := by
  cases he
  rw [ofNat_toNat]
  exact slotLoad_eval hA hm hk (by rw [setSize_eq]; omega) (by rw [slotW_zero]; exact hp)

/-- The last word of a slot's window read, its address in `p`. -/
theorem hi_eval {E : PancakeExp} {p : String} (he : Lower.lowerExp (word (Syntax.v p) sHi) = some E) {ofs : Nat}
    {A : Word} {s0 u : PancakeState σ} (hA : Area ofs A s0) (hm : u.memaddrs = s0.memaddrs) {k : Nat}
    (hk : k < slots) (hp : u.locals p = some (at_ A (off k))) :
    eval u E = some (BitVec.ofNat 64 (u.memory (slotW A k 1)).toNat) := by
  cases he
  rw [ofNat_toNat]
  exact slotLoad_eval hA hm hk (by rw [setSize_eq]; omega) (hiAddr_eval rfl hp)

/-- Two words of slots apart, unless they are the same word of one slot. -/
theorem slotW_ne' {A : Word} {k k' i i' : Nat} (hk : k < slots) (hk' : k' < slots) (hi : i < setSize / 8)
    (hi' : i' < setSize / 8) (h : i ≠ i') : slotW A k i ≠ slotW A k' i' := fun e =>
  h (slotW_inj hk hk' hi hi' e).2

/-- Two words of one slot apart. -/
theorem slotW_ne {A : Word} {k i i' : Nat} (hk : k < slots) (hi : i < setSize / 8) (hi' : i' < setSize / 8)
    (h : i ≠ i') : slotW A k i ≠ slotW A k i' := slotW_ne' hk hk hi hi' h

/-- Bit word `w` of a slot is a word of it. -/
theorem bitIdx {w : Nat} (hw : w < setWords) : 2 + w < setSize / 8 := by
  rw [setWords_eq] at hw; rw [setSize_eq]; omega

/-- A bit word is not a window's end. -/
theorem slotW_bit_ne {A : Word} {k w : Nat} (hk : k < slots) (hw : w < setWords) :
    slotW A k (2 + w) ≠ slotW A k 0 ∧ slotW A k (2 + w) ≠ slotW A k 1 :=
  ⟨slotW_ne hk (bitIdx hw) (by decide) (by omega), slotW_ne hk (bitIdx hw) (by decide) (by omega)⟩

/-- **A window read** (`readWin p lo hi`): slot `k`'s window ends, its address in `p`, into `lo` and `hi`, each
checked. -/
theorem readWin_frag (o : Oracle σ) {ofs : Nat} {A : Word} {s1 : PancakeState σ} (hA : Area ofs A s1) {k : Nat}
    (hk : k < slots) {l : List (String × Value)} {m0 : Word → Word} {p lo hi : String} (hpl : p ≠ lo)
    (hlh : lo ≠ hi) (hp : l.lookup p = some (at_ A (off k))) (hlo : Fresh lo l = true) (hhi : Fresh hi l = true)
    {S : Nat → Bool} (hS : SetAt m0 A k S) :
    Frag o (readWin p lo hi) (RunF s1 l (· = m0)) (RunF s1 ((hi, BitVec.ofNat 64 (m0 (slotW A k 1)).toNat) ::
        (lo, BitVec.ofNat 64 (m0 (slotW A k 0)).toNat) :: l) (· = m0)) := by
  have l1 := hS.lo
  have h1 := hS.hi
  refine frag_append (xs := [_]) (runF_dec o rfl hlo (v := BitVec.ofNat 64 (m0 (slotW A k 0)).toNat)
        fun u h => h.2 ▸ lo_eval rfl hA h.1.memaddrs hk (vals_lookup h.1.vals hp)) ?_
  refine frag_append (xs := [_]) (kept_frag o (by decide) (runF_clock _ _ _) fun u h =>
    ⟨_, vals_lookup h.1.vals (lookup_head _ _ _), by rw [setWords_eq] at l1 ⊢; omega⟩) ?_
  refine frag_append (xs := [_]) (runF_dec o rfl
    (ScanRun.fresh_cons hlh hhi) (v := BitVec.ofNat 64 (m0 (slotW A k 1)).toNat) fun u h =>
      h.2 ▸ hi_eval rfl hA h.1.memaddrs hk (vals_lookup h.1.vals (by rw [ScanRun.lookup_cons_ne hpl]; exact hp))) ?_
  exact kept_frag o (by decide) (runF_clock _ _ _) fun u h =>
    ⟨_, vals_lookup h.1.vals (lookup_head _ _ _), by rw [setWords_eq] at h1 ⊢; omega⟩

/-- The words of slot `kd` from `lo` to below `e` what `g` makes of each and of slot `ks`'s in `m0`, every other word
as in `m0`. -/
def Worded (g : Word → Word → Word) (A : Word) (kd ks lo e : Nat) (m0 m : Word → Word) : Prop :=
  (∀ w, lo ≤ w → w < e → m (slotW A kd (2 + w)) = g (m0 (slotW A kd (2 + w))) (m0 (slotW A ks (2 + w)))) ∧
    ∀ a, (∀ w, lo ≤ w → w < e → a ≠ slotW A kd (2 + w)) → m a = m0 a

/-- **A word loop** (`.dec w (v lo)`, `wordLoop w hi f`): slot `kd`'s words from `lo` to `hi` what `f` makes of each and
of slot `ks`'s, as `g` says. -/
theorem wordLoop_frag (o : Oracle σ) {ofs : Nat} {A : Word} {s0 : PancakeState σ} (hA : Area ofs A s0) {kd ks : Nat}
    (hkd : kd < slots) (hks : ks < slots) {f : Syntax.PExpr → Syntax.PExpr → Syntax.PExpr} {g : Word → Word → Word}
    {w lo hi : String} {Ef : PancakeExp}
    (hlf : Lower.lowerExp (f (.loadw 1 (bitWord "q" (Syntax.v w))) (.loadw 1 (bitWord "p" (Syntax.v w)))) = some Ef)
    {l : List (String × Value)} {lov hiv : Nat} (hlo : l.lookup lo = some (BitVec.ofNat 64 lov))
    (hhi : l.lookup hi = some (BitVec.ofNat 64 hiv)) (hwh : w ≠ hi) (hwq : w ≠ "q") (hw : Fresh w l = true)
    (hq : l.lookup "q" = some (at_ A (off kd))) (hlb : lov < setWords) (hhb : hiv < setWords) {m0 : Word → Word}
    (hev : ∀ (u : PancakeState σ) (i : Nat), i < setWords → RunF s0 ((w, BitVec.ofNat 64 i) :: l) (fun _ => True) u →
      eval u Ef = some (g (u.memory (slotW A kd (2 + i))) (u.memory (slotW A ks (2 + i))))) :
    Frag o [.dec w (Syntax.v lo), wordLoop w hi f] (RunF s0 l (· = m0))
      (RunF s0 l (Worded g A kd ks lov (hiv + 1) m0)) := by
  rw [setWords_eq] at hlb hhb
  let Z (i : Nat) (m : Word → Word) : Prop := lov ≤ i ∧ i ≤ max lov (hiv + 1) ∧ Worded g A kd ks lov i m0 m
  let I (i : Nat) : Assn σ := RunF s0 ((w, BitVec.ofNat 64 i) :: l) (Z i)
  have hhi' : ∀ i, ((w, BitVec.ofNat 64 i) :: l).lookup hi = some (BitVec.ofNat 64 hiv) := fun i => by
    rw [ScanRun.lookup_cons_ne (Ne.symm hwh)]; exact hhi
  have hq' : ∀ i, ((w, BitVec.ofNat 64 i) :: l).lookup "q" = some (at_ A (off kd)) := fun i => by
    rw [ScanRun.lookup_cons_ne (Ne.symm hwq)]; exact hq
  refine frag_append (xs := [_]) (frag_conseq (runF_dec o (E := .var lo) rfl hw (v := BitVec.ofNat 64 lov)
    fun u h => vals_lookup h.1.vals hlo) (fun u h => h) (P' := I lov) fun u h => runF_mono h (fun q hq => hq)
      fun m e => ⟨Nat.le_refl _, Nat.le_max_left _ _, fun _ _ h2 => absurd h2 (by omega), fun a _ => by rw [e]⟩) ?_
  have hlow : LowKK [.store (bitWord "q" (Syntax.v w)) (f (.loadw 1 (bitWord "q" (Syntax.v w)))
      (.loadw 1 (bitWord "p" (Syntax.v w)))), inc w] :=
    lowKK_append (xs := [_]) (lowKK_one rfl (by simp only [Lower.lowerStmt1, hlf]; rfl)) (lowK_any _ (k := .skip) rfl)
  refine frag_conseq (frag_count o
    rfl hlow (fun _ => runF_clock _ _ _) (fun i => noDecl (P' := I i) _ rfl) (g := fun i => decide (i ≤ hiv))
    (fun i u h => FramerCode.eval_le (x := i) (y := hiv) (by have := h.2.2.1; omega) (by omega)
      (ev_var (vals_lookup h.1.vals (lookup_head _ _ _))) (ev_var (vals_lookup h.1.vals (hhi' i))))
    (fun i hg => ?_) lov) (fun u h => h) fun u ⟨i, h, hg⟩ => ?_
  · have hih : i ≤ hiv := of_decide_eq_true hg
    refine frag_append (xs := [_]) (runF_store o hA rfl hlf (y := off kd + 8 * (2 + i))
      (slotW_lt hkd (by rw [setSize_eq]; omega)) (slotW_mod kd _)
      (fun u h => bit_eval rfl (vals_lookup h.1.vals (hq' i)) (vals_lookup h.1.vals (lookup_head _ _ _)))
      (val := fun m => g (m (slotW A kd (2 + i))) (m (slotW A ks (2 + i))))
      (fun u h => hev u i (by rw [setWords_eq]; omega) (runF_mono h (fun _ q => q) fun _ _ => trivial))
      (G := Z (i + 1)) fun m ⟨z1, z2, o1, o2⟩ => ⟨by omega, by omega, fun w' h1 h2 => ?_, fun a ha => ?_⟩) ?_
    · show upd m (slotW A kd (2 + i)) _ (slotW A kd (2 + w')) = _
      by_cases ew : w' = i
      · subst ew
        rw [upd_eq]
        show g (m (slotW A kd (2 + w'))) (m (slotW A ks (2 + w'))) = _
        rw [o2 _ fun w'' _ h' => slotW_ne (i := 2 + w') (i' := 2 + w'') hkd (by rw [setSize_eq]; omega)
          (by rw [setSize_eq]; omega) (by omega), o2 _ fun w'' _ h' => slotW_ne' hks hkd (by rw [setSize_eq]; omega)
          (by rw [setSize_eq]; omega) (by omega)]
      · rw [upd_ne _ (slotW_ne hkd (by rw [setSize_eq]; omega) (by rw [setSize_eq]; omega) (by omega))]
        exact o1 w' h1 (by omega)
    · show upd m (slotW A kd (2 + i)) _ a = _
      rw [upd_ne _ (ha i z1 (by omega))]
      exact o2 a fun w' h1 h2 => ha w' h1 (by omega)
    refine frag_conseq (runF_set o rfl (lookup_head _ _ _) (v := BitVec.ofNat 64 (i + 1)) fun u h => by
        simp only [eval, vals_lookup h.1.vals (lookup_head _ _ _), BitVec.ofNat_add]) (fun u h => h)
      fun u h => runF_mono h (fun q hq => ?_) fun _ z => z
    simp only [List.mem_cons] at hq
    rcases hq with rfl | hq
    · exact List.mem_cons_self ..
    · exact List.mem_cons_of_mem _ (mem_without (List.mem_cons_of_mem _ hq) (ScanRun.fresh_ne hw q hq))
  · have hi' : hiv < i := by simpa using hg
    exact runF_mono h (fun q hq => List.mem_cons_of_mem _ hq) fun m ⟨_, _, o1, o2⟩ =>
      ⟨fun w' h1 h2 => o1 w' h1 (by omega), fun a ha => o2 a fun w' h1 h2 => ha w' h1 (by omega)⟩

/-- The window of slot `k` emptied, `[1, 0]`, over its cleared words. -/
def emptied (A : Word) (k : Nat) (m : Word → Word) : Word → Word := upd (upd m (slotW A k 0) 1) (slotW A k 1) 0

/-- **Cleared bits and an empty window**: slot `k` holds no position, every other word as in `m0`. -/
theorem cleared_empty {A : Word} {k : Nat} (hk : k < slots) {m0 m1 : Word → Word} {S : Nat → Bool}
    (hS : SetAt m0 A k S) {lo hi : Nat} (hL : (m0 (slotW A k 0)).toNat = lo) (hH : (m0 (slotW A k 1)).toNat = hi)
    (hc : Worded (fun _ _ => 0) A k k lo (hi + 1) m0 m1) :
    SetAt (emptied A k m1) A k (fun _ => false) ∧ Frame A k m0 (emptied A k m1) := by
  have h01 : slotW A k 0 ≠ slotW A k 1 := slotW_ne hk (by decide) (by decide) (by decide)
  have e0 : emptied A k m1 (slotW A k 0) = 1 := by rw [emptied, upd_ne _ h01, upd_eq]
  have e1 : emptied A k m1 (slotW A k 1) = 0 := by rw [emptied, upd_eq]
  have eb : ∀ w, w < setWords → emptied A k m1 (slotW A k (2 + w)) = m1 (slotW A k (2 + w)) := fun w hw => by
    rw [emptied, upd_ne _ (slotW_bit_ne hk hw).2, upd_ne _ (slotW_bit_ne hk hw).1]
  have hhi := hS.hi
  rw [hH, setWords_eq] at hhi
  refine ⟨⟨by rw [e0]; decide, by rw [e1]; decide, fun w hw j hj => ?_, fun _ h => by simp at h,
    fun _ h => by simp at h, fun h => by rw [e0, e1] at h; simp at h⟩, fun a ha => ?_⟩
  · rw [eb w hw]
    by_cases hw' : lo ≤ w ∧ w ≤ hi
    · rw [hc.1 w hw'.1 (by omega)]; simp
    · rw [hc.2 _ fun w' h1 h2 e => hw' ?_]
      · rw [hS.bits w hw j hj, setAt_out hS hj (by rw [hL, hH]; exact hw')]
      · rw [setWords_eq] at hw
        have := (slotW_inj hk hk (by rw [setSize_eq]; omega) (by rw [setSize_eq]; omega) e).2
        exact ⟨by omega, by omega⟩
  · have hne : ∀ i, i < setSize / 8 → a ≠ slotW A k i := fun i hi e => ha ⟨i, hi, e⟩
    rw [emptied, upd_ne _ (hne 1 (by decide)), upd_ne _ (hne 0 (by decide))]
    exact hc.2 a fun w _ h2 => hne (2 + w) (by rw [setSize_eq]; omega)

/-! ## Emptying a slot -/

/-- **The set at `q` emptied** (`clearQ`): slot `k` holds no position, every word outside it as it was. -/
theorem clearQ_frag (o : Oracle σ) {ofs : Nat} {A : Word} {s0 : PancakeState σ} (hA : Area ofs A s0) {k : Nat}
    (hk : k < slots) {l : List (String × Value)} (hq : l.lookup "q" = some (at_ A (off k)))
    (hcl : Fresh "cl" l = true) (hch : Fresh "ch" l = true) (hcw : Fresh "cw" l = true) {m0 : Word → Word}
    {S : Nat → Bool} (hS : SetAt m0 A k S) :
    Frag o clearQ (RunF s0 l (· = m0)) (RunF s0 l fun m => SetAt m A k (fun _ => false) ∧ Frame A k m0 m) := by
  have hlo := hS.lo
  have hhi := hS.hi
  rw [setWords_eq] at hlo hhi
  generalize hL : (m0 (slotW A k 0)).toNat = lo at hlo
  generalize hH : (m0 (slotW A k 1)).toNat = hi at hhi
  let l2 : List (String × Value) := ("ch", BitVec.ofNat 64 hi) :: ("cl", BitVec.ofNat 64 lo) :: l
  have hq2 : l2.lookup "q" = some (at_ A (off k)) := by
    rw [ScanRun.lookup_cons_ne (by decide), ScanRun.lookup_cons_ne (by decide)]; exact hq
  refine frag_append (frag_conseq (readWin_frag o hA hk (by decide) (by decide) hq hcl hch hS) (fun _ h => h)
    fun u h => by rw [hL, hH] at h; exact h) ?_
  refine frag_append (xs := [_, _]) (wordLoop_frag o hA hk hk (f := fun _ _ => Syntax.n 0) (g := fun _ _ => 0)
    rfl (l := l2) (lov := lo) (hiv := hi) rfl rfl (by decide) (by decide)
    (ScanRun.fresh_cons (by decide) (ScanRun.fresh_cons (by decide) hcw)) hq2 (by rw [setWords_eq]; omega)
    (by rw [setWords_eq]; omega) (m0 := m0) fun _ _ _ _ => rfl) ?_
  have hql : ∀ (u : PancakeState σ), Run s0 l2 u → u.locals "q" = some (at_ A (off k)) := fun u h =>
    vals_lookup h.vals hq2
  refine frag_append (xs := [_]) (runF_store o hA rfl rfl (y := off k + 8 * 0)
    (slotW_lt hk (by rw [setSize_eq]; omega)) (slotW_mod k 0)
    (fun u h => by rw [Nat.mul_zero, Nat.add_zero]; exact ev_var (hql u h.1)) (val := fun _ => 1)
    (fun _ _ => rfl) (G := fun m => ∃ m1, Worded (fun _ _ => 0) A k k lo (hi + 1) m0 m1 ∧ m = upd m1 (slotW A k 0) 1)
    fun m hc => ⟨m, hc, rfl⟩) ?_
  refine frag_conseq (runF_store o hA rfl
    rfl (y := off k + 8 * 1) (slotW_lt hk (by rw [setSize_eq]; omega)) (slotW_mod k 1)
    (fun u h => hiAddr_eval rfl (hql u h.1)) (val := fun _ => 0) (fun _ _ => rfl)
    (G := fun m => ∃ m1, Worded (fun _ _ => 0) A k k lo (hi + 1) m0 m1 ∧ m = emptied A k m1)
    fun m ⟨m1, hc, e⟩ => ⟨m1, hc, by rw [e]; rfl⟩) (fun u h => h)
    fun u h => runF_mono h (fun q hq => List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hq))
      fun m ⟨m1, hc, e⟩ => e ▸ cleared_empty hk hS hL hH hc

/-! ## The functions' starts -/

theorem atOff_lower (ofs : Nat) : ∃ E, Lower.lowerExp (Syntax.atOff .base ofs) = some E := by
  unfold Syntax.atOff; split <;> exact ⟨_, rfl⟩

theorem slots_small : slots - 1 < 2 ^ 63 := by have := slots_le; omega

theorem aSets_pos : 0 < aSets := by have := pow_lt; omega

theorem slot_lower (x : String) : Lower.lowerExp (slot x) = some (slotE x) := by
  have : (aSets == 0) = false := by simpa using Nat.pos_iff_ne_zero.1 aSets_pos
  simp only [slot, Syntax.atOff, this, Bool.false_eq_true, if_false]
  rfl

/-- **A function's start**, its slot `d` in `q`: the area in `a`, the slot checked. -/
theorem start_frag (o : Oracle σ) {ofs : Nat} {A : Word} {s1 : PancakeState σ} (hA : Area ofs A s1) {d q : String}
    (hda : d ≠ "a") (hqa : q ≠ "a") {k : Nat} (hk : k < slots) {l : List (String × Value)}
    (hl : l.lookup d = some (BitVec.ofNat 64 k)) (ha : Fresh "a" l = true) (hq : Fresh q l = true)
    {F : (Word → Word) → Prop} :
    Frag o (prologue .none ofs [(d, q)]) (RunF s1 l F) (RunF s1 ((q, at_ A (off k)) :: ("a", A) :: l) F) := by
  show Frag o [areaAt ofs, kept d (slots - 1), .dec q (slot d)] _ _
  obtain ⟨E, hE⟩ := atOff_lower ofs
  refine frag_append (xs := [_]) (runF_dec o hE ha (v := A) fun u h => areaAt_eval hA h.1.base hE) ?_
  refine frag_append (xs := [_]) (kept_frag o slots_small (runF_clock _ _ _) fun u h =>
    ⟨k, vals_lookup h.1.vals (by rw [ScanRun.lookup_cons_ne hda]; exact hl), by omega⟩) ?_
  exact runF_dec o (slot_lower d) (ScanRun.fresh_cons (Ne.symm hqa) hq) fun u h =>
      slot_eval (vals_lookup h.1.vals (lookup_head _ _ _))
        (vals_lookup h.1.vals (by rw [ScanRun.lookup_cons_ne hda]; exact hl))

/-! ## Emptying -/

/-- What `setClear` gives back: zero, slot `k` empty, every other word as in `m0`. -/
def ClearRet (A : Word) (k : Nat) (m0 : Word → Word) : Ret :=
  fun v m => v = 0 ∧ SetAt m A k (fun _ => false) ∧ Frame A k m0 m

/-- **`setClear` empties its slot.** -/
theorem setClear_ok (o : Oracle σ) {ofs : Nat} {A : Word} {s1 : PancakeState σ} (hA : Area ofs A s1) {k : Nat}
    (hk : k < slots) (hd : s1.locals "d" = some (BitVec.ofNat 64 k)) {S : Nat → Bool}
    (hS : SetAt s1.memory A k S) :
    ∃ body, Lower.lower (setClear .none ofs) = some body ∧
      SafeR o (fun s => s = s1) body (ClearRet A k s1.memory) fun _ => False := by
  refine body_of ?_
  dsimp only [setClear]
  refine fragR_conseq (P0 := RunF s1 [("d", BitVec.ofNat 64 k)] (· = s1.memory))
    (fragR_append (fragR_of (frag_append (start_frag o hA (by decide) (by decide) hk rfl rfl rfl)
      (clearQ_frag o hA hk rfl rfl rfl rfl hS))) (fragR_ret o rfl fun u h => ⟨_, rfl, rfl, h.2⟩))
    (entry_one hd) fun _ h => h

/-- **A slot `x` given in `p`**: checked, its address made. -/
theorem slotIn_frag (o : Oracle σ) {A : Word} {s1 : PancakeState σ} {x p : String} {k : Nat} (hk : k < slots) {l :
    List (String × Value)} (hl : l.lookup x = some (BitVec.ofNat 64 k))
    (ha : l.lookup "a" = some A) (hp : Fresh p l = true) {F : (Word → Word) → Prop} :
    Frag o [kept x (slots - 1), .dec p (slot x)] (RunF s1 l F) (RunF s1 ((p, at_ A (off k)) :: l) F) := by
  refine frag_append (xs := [_]) (kept_frag o slots_small (runF_clock _ _ _) fun u h =>
    ⟨k, vals_lookup h.1.vals hl, by omega⟩) ?_
  exact runF_dec o (slot_lower x) hp fun u h => slot_eval (vals_lookup h.1.vals ha) (vals_lookup h.1.vals hl)

/-! ## Tests of a set -/

/-- What `setEmpty` gives back: 1 if slot `k`'s set is empty, 0 if not, memory as in `m0`. -/
def EmptyRet (S : Nat → Bool) (m0 : Word → Word) : Ret :=
  fun v m => m = m0 ∧ ((v = 1 ∧ ∀ x, S x = false) ∨ (v = 0 ∧ ∃ x, S x = true))

/-- An empty window, a set empty; another, one with a position. -/
theorem setAt_empty {m : Word → Word} {A : Word} {k : Nat} {S : Nat → Bool} (h : SetAt m A k S) :
    ((m (slotW A k 1)).toNat < (m (slotW A k 0)).toNat → ∀ x, S x = false) ∧
      ((m (slotW A k 0)).toNat ≤ (m (slotW A k 1)).toNat → ∃ x, S x = true) :=
  ⟨fun hl x => by
    cases e : S x
    · rfl
    · have := h.win x e; omega, h.some⟩

/-- **`setEmpty` tells an empty set.** -/
theorem setEmpty_ok (o : Oracle σ) {ofs : Nat} {A : Word} {s1 : PancakeState σ} (hA : Area ofs A s1) {k : Nat}
    (hk : k < slots) (hs : s1.locals "s" = some (BitVec.ofNat 64 k)) {S : Nat → Bool}
    (hS : SetAt s1.memory A k S) :
    ∃ body, Lower.lower (setEmpty .none ofs) = some body ∧
      SafeR o (fun s => s = s1) body (EmptyRet S s1.memory) fun _ => False := by
  have hlo := hS.lo
  have hhi := hS.hi
  rw [setWords_eq] at hlo hhi
  refine body_of ?_
  dsimp only [setEmpty]
  let l0 : List (String × Value) := [("p", at_ A (off k)), ("a", A), ("s", BitVec.ofNat 64 k)]
  have hp : ∀ (u : PancakeState σ), RunF s1 l0 (· = s1.memory) u → u.locals "p" = some (at_ A (off k)) :=
    fun u h => vals_lookup h.1.vals rfl
  refine fragR_conseq (P0 := RunF s1 [("s", BitVec.ofNat 64 k)] (· = s1.memory))
    (fragR_append (fragR_of (start_frag o hA (by decide) (by decide) hk rfl rfl rfl)) ?_)
    (entry_one hs) fun _ h => h
  refine fragR_append (fragR_of (runF_dec o rfl rfl (v := s1.memory (slotW A k 0)) fun u h => ?_)) ?_
  · rw [← h.2]
    exact slotLoad_eval hA h.1.memaddrs hk (i := 0) (by rw [setSize_eq]; omega) (by rw [slotW_zero]; exact hp u h)
  refine fragR_append (fragR_of (runF_dec o rfl rfl (v := s1.memory (slotW A k 1)) fun u h => ?_)) ?_
  · rw [← h.2]
    exact slotLoad_eval hA h.1.memaddrs hk (i := 1) (by rw [setSize_eq]; omega)
        (hiAddr_eval rfl (vals_lookup h.1.vals rfl))
  have he := setAt_empty hS
  refine fragR_if o rfl (lowK_any _ (k := .skip) rfl)
    (lowK_any _ (k := .skip) rfl) (fun _ _ h => h) (noDecl _ rfl) (noDecl _ rfl)
    (b := decide ((s1.memory (slotW A k 1)).toNat < (s1.memory (slotW A k 0)).toNat)) (fun u h => ?_)
    (fun e => fragR_ret o rfl fun u h => ⟨_, rfl, h.2, Or.inl ⟨rfl, he.1 (of_decide_eq_true e)⟩⟩)
    fun e => fragR_ret o rfl fun u h => ⟨_, rfl, h.2, Or.inr ⟨rfl, he.2 (by simpa using e)⟩⟩
  have := FramerCode.eval_lt (t := u) (a := .var "hi") (b := .var "lo")
    (x := (s1.memory (slotW A k 1)).toNat) (y := (s1.memory (slotW A k 0)).toNat) (by omega) (by omega)
    (by rw [ofNat_toNat]; exact vals_lookup h.1.vals rfl) (by rw [ofNat_toNat]; exact vals_lookup h.1.vals rfl)
  exact this

/-- The powers of two below `2 ^ 64` in the area, as `tables` leaves them. -/
def Pows (m : Word → Word) (A : Word) : Prop := ∀ j, j < 64 → m (at_ A (aPow + 8 * j)) = BitVec.twoPow 64 j

/-- A word of the tables below the slots is in no slot. -/
theorem notInSlot {A : Word} {k x : Nat} (hk : k < slots) (hx : x < aSets) : ¬InSlot A k (at_ A x) := by
  rintro ⟨i, hi, e⟩
  have h1 := off_small hk (8 * i) (by rw [setSize_eq] at hi ⊢; omega)
  have := at_inj (by have := aSets_le; omega) (by omega) e
  simp only [off] at this; omega

/-- A slot's frame keeps the powers of two. -/
theorem frame_pows {m0 m : Word → Word} {A : Word} {k : Nat} (hk : k < slots) (hP : Pows m0 A) (hf : Frame A k m0 m) :
    Pows m A := fun j hj => by
  rw [hf _ (notInSlot hk (by have := pow_lt; omega))]; exact hP j hj

/-- Two slots' frame, as `setGrow` leaves it, keeps the powers of two. -/
theorem frame2_pows {m0 m : Word → Word} {A : Word} {k k' : Nat} (hk : k < slots) (hk' : k' < slots)
    (hP : Pows m0 A) (hf : ∀ a, ¬InSlot A k a → ¬InSlot A k' a → m a = m0 a) : Pows m A := fun j hj => by
  have := pow_lt
  rw [hf _ (notInSlot hk (by omega)) (notInSlot hk' (by omega))]; exact hP j hj

/-- The flag of a failed check set keeps every slot's set and the powers of two. -/
theorem refused_keeps {m : Word → Word} {A : Word} {k : Nat} {S : Nat → Bool} (hk : k < slots) (hS : SetAt m A k S)
    (hP : Pows m A) : SetAt (upd m (at_ A aBroken) 1) A k S ∧ Pows (upd m (at_ A aBroken) 1) A := by
  have hb : aBroken < aSets := by have := pow_lt; rw [aPow_eq] at this; simp only [aBroken]; omega
  refine ⟨setAt_frame hS fun i hi => upd_ne _ fun e => notInSlot hk hb ⟨i, hi, e.symm⟩, fun j hj => ?_⟩
  have := pow_lt
  rw [upd_ne _ fun e => ?_]; exact hP j hj
  have := at_inj (by rw [aPow_eq]; omega) (by simp only [aBroken]; omega) e
  rw [aPow_eq] at this; simp only [aBroken] at this; omega

/-- A position's word, `y` shifted right by six. -/
theorem shr6_lower {y : Syntax.PExpr} {Ey : PancakeExp} (hy0 : Lower.lowerExp y = some Ey) :
    Lower.lowerExp (.shr y (Syntax.n 6)) = some (.shiftR Ey (.const (BitVec.ofNat 64 6))) := by
  simp only [Lower.lowerExp, hy0]; rfl

theorem and63_lower {y : Syntax.PExpr} {Ey : PancakeExp} (hy0 : Lower.lowerExp y = some Ey) :
    Lower.lowerExp (Syntax.eAnd y (Syntax.n 63)) = some (.op .and_ Ey (.const (BitVec.ofNat 64 63))) := by
  simp only [Syntax.eAnd, Lower.lowerExp, hy0]; rfl

theorem shr6_eval {y : Syntax.PExpr} {Ey E : PancakeExp} (hy0 : Lower.lowerExp y = some Ey)
    (he : Lower.lowerExp (.shr y (Syntax.n 6)) = some E) {u : PancakeState σ} {Y : Nat} (hY : Y < 2 ^ 64)
    (hy : eval u Ey = some (BitVec.ofNat 64 Y)) : eval u E = some (BitVec.ofNat 64 (Y / 64)) := by
  rw [shr6_lower hy0] at he; cases he
  simp only [eval, hy]
  rw [if_neg (by decide)]
  congr 1
  apply BitVec.eq_of_toNat_eq
  have : Y / 64 < 2 ^ 64 := by omega
  have e6 : (2 : Nat) ^ (6 % 2 ^ 64) = 64 := by decide
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow,
    Nat.mod_eq_of_lt hY, e6, BitVec.toNat_ofNat, Nat.mod_eq_of_lt this]

/-- A position's bit in its word, `y` and 63. -/
theorem and63_eval {y : Syntax.PExpr} {Ey E : PancakeExp} (hy0 : Lower.lowerExp y = some Ey)
    (he : Lower.lowerExp (Syntax.eAnd y (Syntax.n 63)) = some E) {u : PancakeState σ} {Y : Nat} (hY : Y < 2 ^ 64)
    (hy : eval u Ey = some (BitVec.ofNat 64 Y)) : eval u E = some (BitVec.ofNat 64 (Y % 64)) := by
  rw [and63_lower hy0] at he; cases he
  simp only [eval, hy]
  congr 1
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hY,
    show (63 : Nat) % 2 ^ 64 = 2 ^ 6 - 1 by decide, Nat.and_two_pow_sub_one_eq_mod]
  have : Y % 2 ^ 6 < 2 ^ 64 := by omega
  rw [Nat.mod_eq_of_lt this]

/-- The power of two `j`, read from the table, `j` the value of `J`. -/
theorem powAt_eval {ofs : Nat} {A : Word} {s0 u : PancakeState σ} (hA : Area ofs A s0) (hm : u.memaddrs = s0.memaddrs)
    (hP : Pows u.memory A) (ha : u.locals "a" = some A) {J : PancakeExp} {j : Nat} (hj : j < 64)
    (hJ : eval u J = some (BitVec.ofNat 64 j)) :
    eval u (.loadWord (.op .add (.op .add (.var "a") (.const (BitVec.ofNat 64 aPow))) (.mul J
      (.const (BitVec.ofNat 64 8))))) = some (BitVec.twoPow 64 j) := by
  have hl := pow_lt
  have e : eval u (.op .add (.op .add (.var "a") (.const (BitVec.ofNat 64 aPow))) (.mul J
      (.const (BitVec.ofNat 64 8)))) = some (at_ A (aPow + 8 * j)) := by
    simp only [eval, ha, hJ]
    rw [← BitVec.ofNat_mul]
    show some (at_ A aPow + BitVec.ofNat 64 (j * 8)) = some (at_ A (aPow + 8 * j))
    rw [at_add]
    exact congrArg (fun y => some (at_ A y)) (by omega)
  rw [load_eval hA hm (y := aPow + 8 * j) (by omega) (by rw [aPow_eq]; omega) e, hP j hj]

/-- The power of two `j`, read from the table, `j` in `x`. -/
theorem pow_eval {E : PancakeExp} {x : String} (he : Lower.lowerExp (pow (Syntax.v x)) = some E) {ofs : Nat}
    {A : Word} {s0 u : PancakeState σ} (hA : Area ofs A s0) (hm : u.memaddrs = s0.memaddrs) (hP : Pows u.memory A)
    (ha : u.locals "a" = some A) {j : Nat} (hj : j < 64) (hx : u.locals x = some (BitVec.ofNat 64 j)) :
    eval u E = some (BitVec.twoPow 64 j) := by
  cases he
  exact powAt_eval hA hm hP ha hj (ev_var hx)

/-- Position `y`'s word into `yw` and its bit into `yj`, `y` any expression of value `Y` in a set's words. -/
theorem posParts_frag (o : Oracle σ) {s1 : PancakeState σ} {l : List (String × Value)} {m0 : Word → Word}
    {y : Syntax.PExpr} {Ey : PancakeExp} (hy0 : Lower.lowerExp y = some Ey) {Y : Nat} (hY : Y < 64 * setWords)
    (hy : ∀ u, RunF s1 l (· = m0) u → eval u Ey = some (BitVec.ofNat 64 Y)) (hw : Fresh "yw" l = true)
    (hj : Fresh "yj" l = true) :
    Frag o (posParts y) (RunF s1 l (· = m0))
      (RunF s1 (("yj", BitVec.ofNat 64 (Y % 64)) :: ("yw", BitVec.ofNat 64 (Y / 64)) :: l) (· = m0)) := by
  rw [setWords_eq] at hY
  refine frag_append (xs := [_]) (runF_dec o (shr6_lower hy0) hw
    (v := BitVec.ofNat 64 (Y / 64)) fun u h => shr6_eval hy0 (shr6_lower hy0) (by omega) (hy u h)) ?_
  refine frag_append (xs := [_]) (kept_frag o (by decide) (runF_clock _ _ _) fun u h =>
    ⟨Y / 64, vals_lookup h.1.vals (lookup_head _ _ _), by rw [setWords_eq]; omega⟩) ?_
  exact runF_dec o (and63_lower hy0) (ScanRun.fresh_cons (by decide) hj) (v := BitVec.ofNat 64 (Y % 64)) fun u h =>
    and63_eval hy0 (and63_lower hy0) (by omega)
        (hy u (runF_mono h (fun q hq => List.mem_cons_of_mem _ hq) fun _ e => e))

/-- **A position read** (`posOf`): `y` checked, its word into `yw` and its bit into `yj`. -/
theorem posOf_frag (o : Oracle σ) {s1 : PancakeState σ} {l : List (String × Value)} {m0 : Word → Word} {Y : Nat}
    (hY : Y ≤ inputMax) (hy : l.lookup "y" = some (BitVec.ofNat 64 Y)) (hw : Fresh "yw" l = true)
    (hj : Fresh "yj" l = true) :
    Frag o posOf (RunF s1 l (· = m0))
      (RunF s1 (("yj", BitVec.ofNat 64 (Y % 64)) :: ("yw", BitVec.ofNat 64 (Y / 64)) :: l) (· = m0)) := by
  have hI := inputMax_eq
  refine frag_append (xs := [_]) (kept_frag o (by decide) (runF_clock _ _ _) fun u h =>
    ⟨Y, vals_lookup h.1.vals hy, hY⟩) ?_
  exact posParts_frag o rfl (by rw [setWords_eq]; omega) (fun u h => ev_var (vals_lookup h.1.vals hy)) hw hj

/-- What `setHas` gives back: whether position `y` is in the set, memory as in `m0`. -/
def HasRet (S : Nat → Bool) (y : Nat) (m0 : Word → Word) : Ret := fun v m => m = m0 ∧ v = bw (S y)

/-- **`setHas` tells whether a position is in a set.** -/
theorem setHas_ok (o : Oracle σ) {ofs : Nat} {A : Word} {s1 : PancakeState σ} (hA : Area ofs A s1) {k : Nat}
    (hk : k < slots) {Y : Nat} (hY : Y ≤ inputMax) (hs : s1.locals "s" = some (BitVec.ofNat 64 k))
    (hy : s1.locals "y" = some (BitVec.ofNat 64 Y)) {S : Nat → Bool} (hS : SetAt s1.memory A k S)
    (hP : Pows s1.memory A) :
    ∃ body, Lower.lower (setHas .none ofs) = some body ∧
      SafeR o (fun s => s = s1) body (HasRet S Y s1.memory) fun _ => False := by
  have hI := inputMax_eq
  refine body_of ?_
  dsimp only [setHas]
  refine fragR_conseq (P0 := RunF s1 [("s", BitVec.ofNat 64 k), ("y", BitVec.ofNat 64 Y)] (· = s1.memory))
    (fragR_append (fragR_of (frag_append (start_frag o hA (by decide) (by decide) hk rfl rfl rfl)
      (posOf_frag o hY rfl rfl rfl))) ?_)
    (entry_two hs hy) fun _ h => h
  refine fragR_ret o rfl fun u h => ⟨_, ?_, h.2, rfl⟩
  have hw : Y / 64 < setWords := by rw [setWords_eq]; omega
  have hb := hS.bits (Y / 64) hw (Y % 64) (by omega)
  rw [show 64 * (Y / 64) + Y % 64 = Y by omega] at hb
  rw [eval_equal _ (eval_equal _ (ev_and (slotLoad_eval hA h.1.memaddrs hk (i := 2 + Y / 64)
      (by rw [setSize_eq]; rw [setWords_eq] at hw; omega)
      (bit_eval rfl (vals_lookup h.1.vals rfl) (vals_lookup h.1.vals rfl)))
    (pow_eval rfl hA h.1.memaddrs (h.2 ▸ hP) (vals_lookup h.1.vals rfl) (by omega)
        (vals_lookup h.1.vals rfl))) rfl) rfl,
    h.2, ← hb]
  exact congrArg some (bit_test _ (by omega))

/-- **A function's start with two slots**, `x` in `p` and `y` in `q`. -/
theorem start2_frag (o : Oracle σ) {ofs : Nat} {A : Word} {s1 : PancakeState σ} (hA : Area ofs A s1)
    {x p y q : String} (hxa : x ≠ "a") (hya : y ≠ "a") (hpa : p ≠ "a") (hyp : y ≠ p) {kx ky : Nat}
    (hkx : kx < slots) (hky : ky < slots) {l : List (String × Value)} (hx : l.lookup x = some (BitVec.ofNat 64 kx))
    (hy : l.lookup y = some (BitVec.ofNat 64 ky)) (ha : Fresh "a" l = true) (hp : Fresh p l = true)
    (hq : Fresh q ((p, at_ A (off kx)) :: ("a", A) :: l) = true) {F : (Word → Word) → Prop} :
    Frag o (prologue .none ofs [(x, p), (y, q)]) (RunF s1 l F)
      (RunF s1 ((q, at_ A (off ky)) :: (p, at_ A (off kx)) :: ("a", A) :: l) F) := by
  show Frag o ([areaAt ofs, kept x (slots - 1), .dec p (slot x)] ++ [kept y (slots - 1), .dec q (slot y)]) _ _
  refine frag_append (start_frag o hA hxa hpa hkx hx ha hp) ?_
  exact slotIn_frag o hky (by rw [ScanRun.lookup_cons_ne hyp, ScanRun.lookup_cons_ne hya]; exact hy)
    (by rw [ScanRun.lookup_cons_ne (Ne.symm hpa)]; exact lookup_head _ _ _) hq

/-! ## Emptying a slot when another is empty -/

/-- What `setVoid` gives back: 1, slot `kd` empty and every other word as in `m0`, when the set `S` is empty; 0 and
memory as in `m0` when not. -/
def VoidRet (A : Word) (kd : Nat) (S : Nat → Bool) (m0 : Word → Word) : Ret := fun v m =>
  ((∀ x, S x = false) ∧ v = 1 ∧ SetAt m A kd (fun _ => false) ∧ Frame A kd m0 m) ∨ ((∃ x, S x = true) ∧ v = 0 ∧ m = m0)

/-- **`setVoid` empties slot `d` when slot `s` is empty, and tells which.** -/
theorem setVoid_ok (o : Oracle σ) {ofs : Nat} {A : Word} {s1 : PancakeState σ} (hA : Area ofs A s1) {ks kd : Nat}
    (hks : ks < slots) (hkd : kd < slots) (hs : s1.locals "s" = some (BitVec.ofNat 64 ks))
    (hd : s1.locals "d" = some (BitVec.ofNat 64 kd)) {S Sd : Nat → Bool} (hS : SetAt s1.memory A ks S)
    (hSd : SetAt s1.memory A kd Sd) :
    ∃ body, Lower.lower (setVoid .none ofs) = some body ∧
      SafeR o (fun s => s = s1) body (VoidRet A kd S s1.memory) fun _ => False := by
  have hlo := hS.lo
  have hhi := hS.hi
  rw [setWords_eq] at hlo hhi
  refine body_of ?_
  dsimp only [setVoid]
  refine fragR_conseq (P0 := RunF s1 [("s", BitVec.ofNat 64 ks), ("d", BitVec.ofNat 64 kd)] (· = s1.memory))
    (fragR_append (fragR_of (start2_frag o hA (by decide) (by decide) (by decide) (by decide) hks hkd
      rfl rfl rfl rfl rfl)) ?_)
    (entry_two hs hd) fun _ h => h
  have he := setAt_empty hS
  let l0 : List (String × Value) := [("q", at_ A (off kd)), ("p", at_ A (off ks)), ("a", A),
    ("s", BitVec.ofNat 64 ks), ("d", BitVec.ofNat 64 kd)]
  refine fragR_if o rfl (lowK_any _ (k := .skip) rfl) (lowK_any _ (k := .skip) rfl)
    (Q := fun _ => False) (fun _ _ h => h) (fun _ _ _ h => h.elim) (fun _ _ _ h => h.elim)
    (b := decide ((s1.memory (slotW A ks 1)).toNat < (s1.memory (slotW A ks 0)).toNat)) (fun u h =>
      FramerCode.eval_lt (t := u) (by omega) (by omega)
        (h.2 ▸ hi_eval rfl hA h.1.memaddrs hks (vals_lookup h.1.vals (l := l0) rfl))
        (h.2 ▸ lo_eval rfl hA h.1.memaddrs hks (vals_lookup h.1.vals (l := l0) rfl)))
    (fun e => ?_)
    fun e => fragR_ret o rfl fun u h => ⟨_, rfl, Or.inr ⟨he.2 (by simpa using e), rfl, h.2⟩⟩
  exact fragR_append (fragR_of (clearQ_frag o hA hkd rfl rfl rfl rfl hSd))
    (fragR_ret o rfl fun u h => ⟨_, rfl, Or.inl ⟨he.1 (of_decide_eq_true e), rfl, h.2⟩⟩)

/-! ## A window widened -/

/-- Slot `k`'s window ends in `m` as `m1`'s but for the ends: `lo` and `hi`. -/
def WinIs (A : Word) (k : Nat) (m1 : Word → Word) (lo hi : Nat) (m : Word → Word) : Prop :=
  (∀ a, a ≠ slotW A k 0 → a ≠ slotW A k 1 → m a = m1 a) ∧ (m (slotW A k 0)).toNat = lo ∧ (m (slotW A k 1)).toNat = hi

/-- **A window widened to take `[lv, hv]`** (`setAdd`, `setUnion`): an empty one, `dh < dl`, becomes it; another
takes the lower of the starts, as the test `cL` says, and the higher of the ends. -/
theorem widen_frag (o : Oracle σ) {ofs : Nat} {A : Word} {s0 : PancakeState σ} (hA : Area ofs A s0) {k : Nat}
    (hk : k < slots) {l : List (String × Value)} (hq : l.lookup "q" = some (at_ A (off k))) {L H : String}
    {dl dh lv hv : Nat} (hdl : l.lookup "dl" = some (BitVec.ofNat 64 dl)) (hdh : l.lookup "dh" = some
        (BitVec.ofNat 64 dh))
    (hL : l.lookup L = some (BitVec.ofNat 64 lv)) (hH : l.lookup H = some (BitVec.ofNat 64 hv))
    (h1 : dl < 2 ^ 63) (h2 : dh < 2 ^ 63) (h3 : lv < 2 ^ 63) (h4 : hv < 2 ^ 63) {cL : Syntax.PExpr} {CL : PancakeExp}
    (hcL : Lower.lowerExp cL = some CL) {m1 : Word → Word} (hm0 : (m1 (slotW A k 0)).toNat = dl)
    (hm1 : (m1 (slotW A k 1)).toNat = dh)
    (hcv : ∀ u, RunF s0 l (· = m1) u → eval u CL = some (bw (decide (lv < dl)))) :
    Frag o [widen L H cL] (RunF s0 l (· = m1))
      (RunF s0 l (WinIs A k m1 (if dh < dl then lv else min dl lv) (if dh < dl then hv else max dh hv))) := by
  have h01 : slotW A k 0 ≠ slotW A k 1 := slotW_ne hk (by decide) (by decide) (by decide)
  have hq' : ∀ (u : PancakeState σ) (F : (Word → Word) → Prop), RunF s0 l F u → u.locals "q" = some (at_ A (off k)) :=
    fun u F h => vals_lookup h.1.vals hq
  have sLo_frag : ∀ (F G : (Word → Word) → Prop), (∀ m, F m → G (upd m (slotW A k 0) (BitVec.ofNat 64 lv))) →
      Frag o [.store (Syntax.atOff (Syntax.v "q") sLo) (Syntax.v L)] (RunF s0 l F) (RunF s0 l G) := fun F G hG =>
    runF_store o hA rfl rfl (y := off k + 8 * 0) (slotW_lt hk (by rw [setSize_eq]; omega))
      (slotW_mod k 0) (fun u h => by rw [Nat.mul_zero, Nat.add_zero]; exact hq' u F h) (val := fun _ =>
          BitVec.ofNat 64 lv)
      (fun u h => vals_lookup h.1.vals hL) hG
  have sHi_frag : ∀ (F G : (Word → Word) → Prop), (∀ m, F m → G (upd m (slotW A k 1) (BitVec.ofNat 64 hv))) →
      Frag o [.store (Syntax.atOff (Syntax.v "q") sHi) (Syntax.v H)] (RunF s0 l F) (RunF s0 l G) := fun F G hG =>
    runF_store o hA rfl rfl (y := off k + 8 * 1)
      (slotW_lt hk (by rw [setSize_eq]; omega)) (slotW_mod k 1) (fun u h => hiAddr_eval rfl (hq' u F h))
      (val := fun _ => BitVec.ofNat 64 hv) (fun u h => vals_lookup h.1.vals hH) hG
  have lt3 : ∀ x, x < 2 ^ 63 → (BitVec.ofNat 64 x).toNat = x := fun x hx => by
    rw [BitVec.toNat_ofNat]; omega
  unfold widen
  refine ScanRun.frag_if o rfl (lowK_any _ (k := .skip) rfl)
    (lowKK_append (xs := [_]) (lowKK_ite hcL (lowK_any _ (k := .skip) rfl) (fun k => ⟨k, rfl⟩))
      (lowK_any _ (k := .skip) rfl)) rfl rfl (runF_clock _ _ _) (b := decide (dh < dl))
    (fun u h => FramerCode.eval_lt h2 h1 (ev_var (vals_lookup h.1.vals hdh)) (ev_var (vals_lookup h.1.vals hdl)))
    (fun e => ?_) fun e => ?_
  · have he : dh < dl := of_decide_eq_true e
    refine frag_append (xs := [_]) (sLo_frag _ (fun m => m = upd m1 (slotW A k 0) (BitVec.ofNat 64 lv))
      fun m e => by rw [e]) (sHi_frag _ _ fun m e => ⟨fun a h0 h1' => ?_, ?_, ?_⟩)
    · rw [upd_ne _ h1', e, upd_ne _ h0]
    · rw [upd_ne _ h01, e, upd_eq, if_pos he, lt3 _ h3]
    · rw [upd_eq, if_pos he, lt3 _ h4]
  · have he : ¬dh < dl := by simpa using e
    let G2 : (Word → Word) → Prop := fun m =>
      (∀ a, a ≠ slotW A k 0 → m a = m1 a) ∧ (m (slotW A k 0)).toNat = min dl lv
    refine frag_append (xs := [_]) (ScanRun.frag_if o hcL (lowK_any _ (k := .skip) rfl)
      (fun k => ⟨k, rfl⟩) rfl rfl (runF_clock _ _ _) (Q := RunF s0 l G2) (b := decide (lv < dl)) hcv
      (fun e2 => sLo_frag _ _ fun m e => ⟨fun a ha => by rw [upd_ne _ ha, e], by
        rw [upd_eq, lt3 _ h3]; have := of_decide_eq_true e2; omega⟩)
      fun e2 => frag_nil o fun u h => runF_mono h (fun _ q => q) fun m e => ⟨fun a _ => by rw [e], by
        rw [e, hm0]; have : ¬lv < dl := by simpa using e2
        omega⟩) ?_
    refine ScanRun.frag_if o rfl (lowK_any _ (k := .skip) rfl)
      (fun k => ⟨k, rfl⟩) rfl rfl (runF_clock _ _ _) (b := decide (dh < hv))
      (fun u h => FramerCode.eval_lt h2 h4 (ev_var (vals_lookup h.1.vals hdh)) (ev_var (vals_lookup h.1.vals hH)))
      (fun e2 => sHi_frag _ _ fun m ⟨g1, g2⟩ => ⟨fun a h0 h1' => by rw [upd_ne _ h1', g1 a h0], by
        rw [upd_ne _ h01, g2, if_neg he], by
        rw [upd_eq, lt3 _ h4, if_neg he]; have := of_decide_eq_true e2; omega⟩)
      fun e2 => frag_nil o fun u h => runF_mono h (fun _ q => q) fun m ⟨g1, g2⟩ => ⟨fun a h0 _ => g1 a h0, by
        rw [g2, if_neg he], by
        rw [g1 _ (Ne.symm h01), hm1, if_neg he]; have : ¬dh < hv := by simpa using e2
        omega⟩

/-! ## A check that fails -/

/-- **A check that fails**: the local `x` past `hi`, the area's flag of a failed check set and 1 returned. -/
theorem kept_fail (o : Oracle σ) {R : Ret} {ofs : Nat} {A : Word} {s0 : PancakeState σ} (hA : Area ofs A s0)
    {x : String} {hi : Nat} (hhi : hi < 2 ^ 63) {l : List (String × Value)} {F : (Word → Word) → Prop}
    (ha : l.lookup "a" = some A) {w : Word} (hx : l.lookup x = some w) (hw : hi < w.toNat)
    (hR : ∀ m, F m → R 1 (upd m (at_ A aBroken) 1)) : FragR o R [kept x hi] (RunF s0 l F) fun _ => False := by
  have hsz : aBroken < aSets + slots * setSize := by
    have := pow_lt
    rw [aPow_eq] at this
    simp only [aBroken]; omega
  refine fragR_if o rfl (lowK_any _ (k := .skip) rfl)
    (fun k => ⟨k, rfl⟩) (fun _ _ h => h) (fun _ _ _ h => h.elim) (fun _ _ _ h => h.elim) (b := true)
    (fun u h => ?_) (fun _ => ?_) fun e => absurd e (by decide)
  · have e := FramerCode.eval_or2 (t := u) (p := signedLt w 0) (q := signedLt (BitVec.ofNat 64 hi) w)
      (a := .cmp .less (.var x) (.const 0)) (b := .cmp .less (.const (BitVec.ofNat 64 hi)) (.var x))
      (by simp only [eval, vals_lookup h.1.vals hx]; rfl) (by simp only [eval, vals_lookup h.1.vals hx]; rfl)
    rw [slt_out hhi hw] at e
    exact e
  · refine fragR_append (fragR_of (runF_store o hA
      rfl rfl (y := aBroken) hsz rfl (fun u h => by simp only [eval, vals_lookup h.1.vals ha]; rfl)
      (val := fun _ => 1) (fun _ _ => rfl) (G := fun m => ∃ m', F m' ∧ m = upd m' (at_ A aBroken) 1)
      fun m hF => ⟨m, hF, rfl⟩)) (fragR_ret o rfl fun u h => ⟨_, rfl, ?_⟩)
    obtain ⟨m', hF, e⟩ := h.2
    rw [e]; exact hR m' hF

/-! ## A position added -/

/-- **Position `y` added**: the bit set in its word and the window widened to the word, every other word as in
`m0`, give slot `k` the set with `y`. -/
theorem add_setAt {A : Word} {k : Nat} (hk : k < slots) {m0 m : Word → Word} {S : Nat → Bool}
    (hS : SetAt m0 A k S) {Y : Nat} (hY : Y ≤ inputMax)
    (hw : WinIs A k (upd m0 (slotW A k (2 + Y / 64)) (m0 (slotW A k (2 + Y / 64)) ||| BitVec.twoPow 64 (Y % 64)))
      (if (m0 (slotW A k 1)).toNat < (m0 (slotW A k 0)).toNat then Y / 64 else min (m0 (slotW A k 0)).toNat (Y / 64))
      (if (m0 (slotW A k 1)).toNat < (m0 (slotW A k 0)).toNat then Y / 64 else max (m0 (slotW A k 1)).toNat (Y / 64))
      m) :
    SetAt m A k (fun x => S x || x == Y) ∧ Frame A k m0 m := by
  have hI := inputMax_eq
  have hlo := hS.lo
  have hhi := hS.hi
  rw [setWords_eq] at hlo hhi
  generalize hL : (m0 (slotW A k 0)).toNat = lo at hlo hw
  generalize hH : (m0 (slotW A k 1)).toNat = hi at hhi hw
  obtain ⟨hm, h0, h1⟩ := hw
  have hW : ∀ w, w < setWords → slotW A k (2 + w) ≠ slotW A k 0 ∧ slotW A k (2 + w) ≠ slotW A k 1 :=
    fun _ hw' => slotW_bit_ne hk hw'
  have hbit : ∀ w, w < setWords → m (slotW A k (2 + w)) = if w = Y / 64 then
      m0 (slotW A k (2 + Y / 64)) ||| BitVec.twoPow 64 (Y % 64) else m0 (slotW A k (2 + w)) := fun w hw' => by
    rw [hm _ (hW w hw').1 (hW w hw').2]
    rw [setWords_eq] at hw'
    by_cases e : w = Y / 64
    · subst e; rw [if_pos rfl, upd_eq]
    · rw [if_neg e, upd_ne _ (slotW_ne hk (by rw [setSize_eq]; omega) (by rw [setSize_eq]; omega) (by omega))]
  refine ⟨⟨by rw [h0, setWords_eq]; split <;> omega, by rw [h1, setWords_eq]; split <;> omega,
    fun w hw' j hj => ?_, fun x hx => ?_, fun x hx => ?_, fun _ => ⟨Y, by simp⟩⟩, fun a ha => ?_⟩
  · rw [hbit w hw']
    by_cases e : w = Y / 64
    · subst e
      rw [if_pos rfl, getLsbD_or_twoPow _ (by omega), hS.bits _ hw' j hj]
      congr 1
      cases e2 : (j == Y % 64) <;> cases e3 : (64 * (Y / 64) + j == Y) <;> simp_all <;> omega
    · rw [if_neg e, hS.bits w hw' j hj]
      have : (64 * w + j == Y) = false := by simp; omega
      rw [this, Bool.or_false]
  · rw [setWords_eq]
    simp only [Bool.or_eq_true, beq_iff_eq] at hx
    rcases hx with hx | rfl
    · have := hS.small x hx; rwa [setWords_eq] at this
    · omega
  · rw [h0, h1]
    simp only [Bool.or_eq_true, beq_iff_eq] at hx
    rcases hx with hx | rfl
    · have := hS.win x hx
      rw [hL, hH] at this
      split <;> omega
    · split <;> omega
  · have hne : ∀ i, i < setSize / 8 → a ≠ slotW A k i := fun i hi e => ha ⟨i, hi, e⟩
    rw [hm a (hne 0 (by decide)) (hne 1 (by decide)), upd_ne _ (hne (2 + Y / 64) (by rw [setSize_eq]; omega))]

/-- **A bit set** (`setBit`): bit `Y % 64` of word `Y / 64` of the set at `q`, slot `k`. -/
theorem setBit_frag (o : Oracle σ) {ofs : Nat} {A : Word} {s1 : PancakeState σ} (hA : Area ofs A s1) {k : Nat}
    (hk : k < slots) {l : List (String × Value)} (ha : l.lookup "a" = some A) (hq : l.lookup "q" = some (at_ A (off k)))
    {Y : Nat} (hY : Y < 64 * setWords) (hw : l.lookup "yw" = some (BitVec.ofNat 64 (Y / 64)))
    (hj : l.lookup "yj" = some (BitVec.ofNat 64 (Y % 64))) {m0 : Word → Word} (hP : Pows m0 A) :
    Frag o [setBit] (RunF s1 l (· = m0)) (RunF s1 l (· = upd m0 (slotW A k (2 + Y / 64))
          (m0 (slotW A k (2 + Y / 64)) ||| BitVec.twoPow 64 (Y % 64)))) := by
  rw [setWords_eq] at hY
  exact runF_store o hA rfl rfl (y := off k + 8 * (2 + Y / 64)) (slotW_lt hk (by rw [setSize_eq]; omega))
    (slotW_mod k _) (fun u h => bit_eval rfl (vals_lookup h.1.vals hq) (vals_lookup h.1.vals hw))
    (val := fun m => m (slotW A k (2 + Y / 64)) ||| BitVec.twoPow 64 (Y % 64))
    (fun u h => FramerCode.eval_or (slotLoad_eval hA h.1.memaddrs hk (by rw [setSize_eq]; omega)
      (bit_eval rfl (vals_lookup h.1.vals hq) (vals_lookup h.1.vals hw)))
      (pow_eval rfl hA h.1.memaddrs (h.2 ▸ hP) (vals_lookup h.1.vals ha) (by omega) (vals_lookup h.1.vals hj)))
    fun m e => by subst e; rfl

/-- What `setAdd` gives back: 0, and position `y` added to slot `k`'s set, every other word as in `m0`, when `y` is
at most `inputMax`; 1, and the area's flag of a failed check set, when not. -/
def AddRet (A : Word) (k : Nat) (S : Nat → Bool) (Y : Word) (m0 : Word → Word) : Ret := fun v m =>
  (Y.toNat ≤ inputMax ∧ v = 0 ∧ SetAt m A k (fun x => S x || x == Y.toNat) ∧ Frame A k m0 m) ∨
    (inputMax < Y.toNat ∧ v = 1 ∧ m = upd m0 (at_ A aBroken) 1)

/-- **`setAdd` adds a position to a set**, or refuses one past the longest input. -/
theorem setAdd_ok (o : Oracle σ) {ofs : Nat} {A : Word} {s1 : PancakeState σ} (hA : Area ofs A s1) {k : Nat}
    (hk : k < slots) (hd : s1.locals "d" = some (BitVec.ofNat 64 k)) {Y : Word} (hy : s1.locals "y" = some Y)
    {S : Nat → Bool} (hS : SetAt s1.memory A k S) (hP : Pows s1.memory A) :
    ∃ body, Lower.lower (setAdd .none ofs) = some body ∧
      SafeR o (fun s => s = s1) body (AddRet A k S Y s1.memory) fun _ => False := by
  have hI := inputMax_eq
  refine body_of ?_
  dsimp only [setAdd]
  let l0 : List (String × Value) := [("q", at_ A (off k)), ("a", A), ("d", BitVec.ofNat 64 k), ("y", Y)]
  have hstart : FragR o (AddRet A k S Y s1.memory) (prologue .none ofs [("d", "q")])
      (fun s => s = s1) (RunF s1 l0 (· = s1.memory)) :=
    fragR_conseq (fragR_of (start_frag o hA (by decide) (by decide) hk (l := [("d", BitVec.ofNat 64 k), ("y", Y)])
      (F := (· = s1.memory)) rfl rfl rfl))
      (entry_two hd hy) fun _ h => h
  by_cases hYm : Y.toNat ≤ inputMax
  · generalize hYn : Y.toNat = Yn at hYm
    have hY' : Y = BitVec.ofNat 64 Yn := by rw [← hYn, ofNat_toNat]
    have hlo := hS.lo
    have hhi := hS.hi
    rw [setWords_eq] at hlo hhi
    have hW0 : slotW A k 0 ≠ slotW A k (2 + Yn / 64) := slotW_ne hk (by decide) (by rw [setSize_eq]; omega) (by omega)
    have hW1 : slotW A k 1 ≠ slotW A k (2 + Yn / 64) := slotW_ne hk (by decide) (by rw [setSize_eq]; omega) (by omega)
    let m1 := upd s1.memory (slotW A k (2 + Yn / 64))
      (s1.memory (slotW A k (2 + Yn / 64)) ||| BitVec.twoPow 64 (Yn % 64))
    let lo0 := (s1.memory (slotW A k 0)).toNat
    let hi0 := (s1.memory (slotW A k 1)).toNat
    let lfin : List (String × Value) := [("dh", BitVec.ofNat 64 hi0), ("dl", BitVec.ofNat 64 lo0),
      ("yj", BitVec.ofNat 64 (Yn % 64)), ("yw", BitVec.ofNat 64 (Yn / 64))] ++ l0
    have hl0 : l0.lookup "y" = some (BitVec.ofNat 64 Yn) := by
      show some Y = _; rw [hY']
    refine fragR_append (fragR_append (fragR_append hstart (fragR_of (posOf_frag o hYm hl0 rfl rfl))) (fragR_of ?_))
      (fragR_ret o rfl fun u (h : RunF s1 lfin (WinIs A k m1 (if hi0 < lo0 then Yn / 64 else min lo0 (Yn / 64))
        (if hi0 < lo0 then Yn / 64 else max hi0 (Yn / 64))) u) =>
          ⟨_, rfl, Or.inl ⟨by omega, rfl, hYn ▸ add_setAt hk hS hYm h.2⟩⟩)
    refine frag_append (xs := [_]) (frag_conseq (setBit_frag o hA hk rfl rfl (by rw [setWords_eq]; omega) rfl rfl hP)
      (fun _ h => h) (P' := RunF s1 _ (· = m1)) fun _ h => h) ?_
    have e0 : m1 (slotW A k 0) = s1.memory (slotW A k 0) := upd_ne _ hW0
    have e1 : m1 (slotW A k 1) = s1.memory (slotW A k 1) := upd_ne _ hW1
    refine frag_append (xs := [_]) (runF_dec o rfl rfl
      (v := BitVec.ofNat 64 (s1.memory (slotW A k 0)).toNat) fun u h => by
        have := lo_eval (p := "q") rfl hA h.1.memaddrs hk (vals_lookup h.1.vals rfl)
        rw [h.2, e0] at this; exact this) ?_
    refine frag_append (xs := [_]) (runF_dec o rfl
      rfl (v := BitVec.ofNat 64 (s1.memory (slotW A k 1)).toNat) fun u h => by
        have := hi_eval (p := "q") rfl hA h.1.memaddrs hk (vals_lookup h.1.vals rfl)
        rw [h.2, e1] at this; exact this) ?_
    exact widen_frag o hA hk rfl (dl := lo0) (dh := hi0) (lv := Yn / 64) (hv := Yn / 64) rfl rfl rfl rfl
      (by omega) (by omega) (by omega) (by omega)
      rfl
      (by rw [e0]) (by rw [e1]) fun u h => FramerCode.eval_lt (by omega) (by omega)
        (ev_var (vals_lookup h.1.vals rfl)) (ev_var (vals_lookup h.1.vals rfl))
  · refine fragR_append (fragR_append (fragR_append hstart (fragR_append (xs := [kept "y" inputMax])
      (kept_fail o hA (by decide) rfl rfl (by omega) fun m e => Or.inr ⟨by omega, rfl, by rw [e]⟩)
      (fragR_of (frag_unsat (lowK_any _ (k := .skip) rfl) fun _ h => h))))
      (fragR_of (frag_unsat (lowK_any _ (k := .skip) rfl) fun _ h => h)))
      (fragR_of (frag_unsat (lowK_any _ (k := .skip) rfl) fun _ h => h))

/-! ## Union -/

/-- **A union**: slot `ks`'s words or-ed into slot `kd`'s and the window widened to take `ks`'s give slot `kd` the
union, every other word as in `m0`. -/
theorem union_setAt {A : Word} {kd ks : Nat} (hkd : kd < slots) {m0 m2 m : Word → Word}
    {Sd Ss : Nat → Bool} (hSd : SetAt m0 A kd Sd) (hSs : SetAt m0 A ks Ss)
    (hne : (m0 (slotW A ks 0)).toNat ≤ (m0 (slotW A ks 1)).toNat)
    (ho : Worded (· ||| ·) A kd ks (m0 (slotW A ks 0)).toNat ((m0 (slotW A ks 1)).toNat + 1) m0 m2)
    (hw : WinIs A kd m2 (if (m0 (slotW A kd 1)).toNat < (m0 (slotW A kd 0)).toNat then (m0 (slotW A ks 0)).toNat
        else min (m0 (slotW A kd 0)).toNat (m0 (slotW A ks 0)).toNat)
      (if (m0 (slotW A kd 1)).toNat < (m0 (slotW A kd 0)).toNat then (m0 (slotW A ks 1)).toNat
        else max (m0 (slotW A kd 1)).toNat (m0 (slotW A ks 1)).toNat) m) :
    SetAt m A kd (fun x => Sd x || Ss x) ∧ Frame A kd m0 m := by
  have l1 := hSd.lo
  have h1 := hSd.hi
  have l2 := hSs.lo
  have h2 := hSs.hi
  have wd := hSd.win
  have ws := hSs.win
  have sm := hSs.some
  have hout := fun w j (hj : j < 64) => setAt_out hSs (w := w) (j := j) hj
  rw [setWords_eq] at l1 h1 l2 h2
  generalize (m0 (slotW A kd 0)).toNat = dl at l1 hw wd
  generalize (m0 (slotW A kd 1)).toNat = dh at h1 hw wd
  generalize (m0 (slotW A ks 0)).toNat = lo at l2 hne ho hw ws sm hout
  generalize (m0 (slotW A ks 1)).toNat = hi at h2 hne ho hw ws sm hout
  obtain ⟨hm, e0, e1⟩ := hw
  obtain ⟨o1, o2⟩ := ho
  have hW : ∀ w, w < setWords → slotW A kd (2 + w) ≠ slotW A kd 0 ∧ slotW A kd (2 + w) ≠ slotW A kd 1 :=
    fun _ hw' => slotW_bit_ne hkd hw'
  refine ⟨⟨by rw [e0, setWords_eq]; split <;> omega, by rw [e1, setWords_eq]; split <;> omega,
    fun w hw' j hj => ?_, fun x hx => ?_, fun x hx => ?_, fun _ => ?_⟩, fun a ha => ?_⟩
  · rw [hm _ (hW w hw').1 (hW w hw').2]
    by_cases hin : lo ≤ w ∧ w ≤ hi
    · rw [o1 w hin.1 (by omega), BitVec.getLsbD_or, hSd.bits w hw' j hj, hSs.bits w hw' j hj]
    · rw [setWords_eq] at hw'
      rw [o2 _ fun w' h1' h2' e => hin ?_, hSd.bits w (by rw [setWords_eq]; omega) j hj]
      · rw [hout w j hj hin, Bool.or_false]
      · have := (slotW_inj hkd hkd (by rw [setSize_eq]; omega) (by rw [setSize_eq]; omega) e).2
        exact ⟨by omega, by omega⟩
  · simp only [Bool.or_eq_true] at hx
    rcases hx with hx | hx
    · exact hSd.small x hx
    · exact hSs.small x hx
  · rw [e0, e1]
    simp only [Bool.or_eq_true] at hx
    rcases hx with hx | hx
    · have := wd x hx; split <;> omega
    · have := ws x hx; split <;> omega
  · obtain ⟨x, hx⟩ := sm hne
    exact ⟨x, by simp [hx]⟩
  · have hne' : ∀ i, i < setSize / 8 → a ≠ slotW A kd i := fun i hi e => ha ⟨i, hi, e⟩
    rw [hm a (hne' 0 (by decide)) (hne' 1 (by decide))]
    exact o2 a fun w _ h2' => hne' (2 + w) (by rw [setSize_eq]; omega)

/-- What `setUnion` gives back: zero, slot `kd` the union, every other word as in `m0`. -/
def UnionRet (A : Word) (kd : Nat) (Sd Ss : Nat → Bool) (m0 : Word → Word) : Ret :=
  fun v m => v = 0 ∧ SetAt m A kd (fun x => Sd x || Ss x) ∧ Frame A kd m0 m

/-- **`setUnion` gives slot `d` the union with slot `s`.** -/
theorem setUnion_ok (o : Oracle σ) {ofs : Nat} {A : Word} {s1 : PancakeState σ} (hA : Area ofs A s1) {kd ks : Nat}
    (hkd : kd < slots) (hks : ks < slots) (hd : s1.locals "d" = some (BitVec.ofNat 64 kd))
    (hs : s1.locals "s" = some (BitVec.ofNat 64 ks)) {Sd Ss : Nat → Bool} (hSd : SetAt s1.memory A kd Sd)
    (hSs : SetAt s1.memory A ks Ss) :
    ∃ body, Lower.lower (setUnion .none ofs) = some body ∧
      SafeR o (fun s => s = s1) body (UnionRet A kd Sd Ss s1.memory) fun _ => False := by
  let m0 := s1.memory
  have l1 := hSd.lo
  have h1 := hSd.hi
  have l2 := hSs.lo
  have h2 := hSs.hi
  rw [setWords_eq] at l1 h1 l2 h2
  let dl := (m0 (slotW A kd 0)).toNat
  let dh := (m0 (slotW A kd 1)).toNat
  let lo := (m0 (slotW A ks 0)).toNat
  let hi := (m0 (slotW A ks 1)).toNat
  have bdl : dl < 1026 := l1
  have bdh : dh < 1026 := h1
  have blo : lo < 1026 := l2
  have bhi : hi < 1026 := h2
  refine body_of ?_
  dsimp only [setUnion]
  let l1' : List (String × Value) := [("p", at_ A (off ks)), ("q", at_ A (off kd)), ("a", A),
    ("d", BitVec.ofNat 64 kd), ("s", BitVec.ofNat 64 ks)]
  let l2' : List (String × Value) := [("dh", BitVec.ofNat 64 dh), ("dl", BitVec.ofNat 64 dl),
    ("hi", BitVec.ofNat 64 hi), ("lo", BitVec.ofNat 64 lo)] ++ l1'
  let G : (Word → Word) → Prop := fun m => SetAt m A kd (fun x => Sd x || Ss x) ∧ Frame A kd m0 m
  refine fragR_conseq (P0 := RunF s1 [("d", BitVec.ofNat 64 kd), ("s", BitVec.ofNat 64 ks)] (· = m0))
    (fragR_append (fragR_append (fragR_of (frag_append (frag_append (start2_frag o hA (by decide) (by decide)
      (by decide) (by decide) hkd hks rfl rfl rfl rfl rfl) (readWin_frag o hA hks (l := l1') (by decide) (by decide) rfl
        rfl rfl hSs)) (readWin_frag o hA hkd (by decide) (by decide) rfl rfl rfl hSd))) ?_)
      (fragR_ret o rfl fun u (h : RunF s1 l2' G u) => ⟨_, rfl, rfl, h.2⟩))
    (entry_two hd hs) fun _ h => h
  refine fragR_if o rfl (lowK_any _ (k := .skip) rfl) (fun k => ⟨k, rfl⟩) (runF_clock _ _ _) (fun u y v h hy => by
      have : y = "w" := by simpa [declared, wordLoop, widen] using hy
      subst this; exact runF_restore h rfl v) (noDecl _ rfl) (b := decide (lo ≤ hi))
    (fun u h => FramerCode.eval_le (x := lo) (y := hi) (by omega) (by omega) (ev_var (vals_lookup h.1.vals rfl))
      (ev_var (vals_lookup h.1.vals rfl))) (fun e => ?_) fun e => fragR_of (frag_nil o fun u h => runF_mono h
        (fun _ q => q) fun m em => ?_)
  rotate_left
  · have hem := (setAt_empty hSs).1 (by simpa using e)
    rw [em]
    refine ⟨?_, fun _ _ => rfl⟩
    have : (fun x => Sd x || Ss x) = Sd := funext fun x => by rw [hem x, Bool.or_false]
    rw [this]; exact hSd
  have hle : lo ≤ hi := of_decide_eq_true e
  have hwin : Frag o [widen "lo" "hi" (Syntax.eAnd (Syntax.eLt (Syntax.v "lo") (Syntax.v "dl")) (Syntax.n 1))]
      (RunF s1 l2' (Worded (· ||| ·) A kd ks lo (hi + 1) m0)) (RunF s1 l2' G) := by
    refine frag_each o (lowK_any _ (k := .skip) rfl) fun s hs => ?_
    have hf0 : s.memory (slotW A kd 0) = m0 (slotW A kd 0) := hs.2.2 _ fun w _ _ =>
      slotW_ne hkd (by decide) (by rw [setSize_eq]; omega) (by omega)
    have hf1 : s.memory (slotW A kd 1) = m0 (slotW A kd 1) := hs.2.2 _ fun w _ _ =>
      slotW_ne hkd (by decide) (by rw [setSize_eq]; omega) (by omega)
    refine frag_conseq (widen_frag o hA hkd (l := l2') rfl (L := "lo") (H := "hi") (dl := dl) (dh := dh)
      (lv := lo) (hv := hi) rfl rfl rfl rfl (by omega) (by omega) (by omega) (by omega)
      rfl (m1 := s.memory)
      (by rw [hf0]) (by rw [hf1]) fun u h => ?_) (fun u hu => runF_like hs hu) fun u hu =>
      runF_mono hu (fun _ q => q) fun m hw => union_setAt hkd hSd hSs hle hs.2 hw
    have := FramerCode.eval_and (t := u) (p := decide (lo < dl)) (q := true)
      (a := .cmp .less (.var "lo") (.var "dl")) (b := .const (BitVec.ofNat 64 1))
      (FramerCode.eval_lt (x := lo) (y := dl) (by omega) (by omega) (ev_var (vals_lookup h.1.vals rfl))
        (ev_var (vals_lookup h.1.vals rfl))) rfl
    rwa [Bool.and_true] at this
  refine fragR_of (frag_append (xs := [_, _]) (wordLoop_frag o hA hkd hks (g := (· ||| ·)) (l := l2') rfl
    (lov := lo) (hiv := hi) rfl rfl (by decide) (by decide) rfl rfl (by rw [setWords_eq]; omega)
    (by rw [setWords_eq]; omega) fun u i hi' h => FramerCode.eval_or (slotLoad_eval hA h.1.memaddrs hkd
      (by rw [setSize_eq]; rw [setWords_eq] at hi'; omega) (bit_eval rfl (vals_lookup h.1.vals rfl)
        (vals_lookup h.1.vals (lookup_head _ _ _)))) (slotLoad_eval hA h.1.memaddrs hks
      (by rw [setSize_eq]; rw [setWords_eq] at hi'; omega) (bit_eval rfl (vals_lookup h.1.vals rfl)
        (vals_lookup h.1.vals (lookup_head _ _ _))))) hwin)

/-! ## Copy -/

/-- **A copy**: an emptied slot `kd` given slot `ks`'s words and window holds `ks`'s set. -/
theorem copy_setAt {A : Word} {kd ks : Nat} (hkd : kd < slots) (hks : ks < slots) (hne : kd ≠ ks)
    {m0 m1 m2 : Word → Word} {Ss : Nat → Bool} (hSs : SetAt m0 A ks Ss) (h1 : SetAt m1 A kd (fun _ => false))
    (hf1 : Frame A kd m0 m1)
    (hc : Worded (fun _ s => s) A kd ks (m0 (slotW A ks 0)).toNat ((m0 (slotW A ks 1)).toNat + 1) m1 m2) :
    SetAt (upd (upd m2 (slotW A kd 0) (m0 (slotW A ks 0))) (slotW A kd 1) (m0 (slotW A ks 1))) A kd Ss ∧
      Frame A kd m0 (upd (upd m2 (slotW A kd 0) (m0 (slotW A ks 0))) (slotW A kd 1) (m0 (slotW A ks 1))) := by
  have l2 := hSs.lo
  have h2 := hSs.hi
  rw [setWords_eq] at l2 h2
  have h01 : slotW A kd 0 ≠ slotW A kd 1 := slotW_ne hkd (by decide) (by decide) (by decide)
  have e0 : upd (upd m2 (slotW A kd 0) (m0 (slotW A ks 0))) (slotW A kd 1) (m0 (slotW A ks 1)) (slotW A kd 0) =
      m0 (slotW A ks 0) := by rw [upd_ne _ h01, upd_eq]
  have e1 : upd (upd m2 (slotW A kd 0) (m0 (slotW A ks 0))) (slotW A kd 1) (m0 (slotW A ks 1)) (slotW A kd 1) =
      m0 (slotW A ks 1) := upd_eq _ _ _
  have hks' : ∀ i, i < setSize / 8 → m1 (slotW A ks i) = m0 (slotW A ks i) := fun i hi =>
    hf1 _ fun ⟨i', hi', e⟩ => hne (slotW_inj hkd hks hi' hi e.symm).1
  refine ⟨⟨by rw [e0]; exact hSs.lo, by rw [e1]; exact hSs.hi, fun w hw j hj => ?_, hSs.small,
    fun x hx => by rw [e0, e1]; exact hSs.win x hx, fun h => hSs.some (by rwa [e0, e1] at h)⟩, fun a ha => ?_⟩
  · rw [setWords_eq] at hw
    rw [upd_ne _ (slotW_ne hkd (by rw [setSize_eq]; omega) (by decide) (by omega)),
      upd_ne _ (slotW_ne hkd (by rw [setSize_eq]; omega) (by decide) (by omega))]
    by_cases hin : (m0 (slotW A ks 0)).toNat ≤ w ∧ w < (m0 (slotW A ks 1)).toNat + 1
    · rw [hc.1 w hin.1 hin.2, hks' _ (by rw [setSize_eq]; omega)]
      exact hSs.bits w (by rw [setWords_eq]; omega) j hj
    · rw [hc.2 _ fun w' h1' h2' e => hin ?_, h1.bits w (by rw [setWords_eq]; omega) j hj]
      · rw [setAt_out hSs hj fun h => hin ⟨h.1, by omega⟩]
      · have := (slotW_inj hkd hkd (by rw [setSize_eq]; omega) (by rw [setSize_eq]; omega) e).2
        exact ⟨by omega, by omega⟩
  · have hne' : ∀ i, i < setSize / 8 → a ≠ slotW A kd i := fun i hi e => ha ⟨i, hi, e⟩
    rw [upd_ne _ (hne' 1 (by decide)), upd_ne _ (hne' 0 (by decide)),
      hc.2 a fun w _ _ => hne' (2 + w) (by rw [setSize_eq]; omega)]
    exact hf1 a ha

/-- What `setCopy` gives back: zero, slot `kd` holding `S`, every other word as in `m0`. -/
def CopyRet (A : Word) (kd : Nat) (S : Nat → Bool) (m0 : Word → Word) : Ret :=
  fun v m => v = 0 ∧ SetAt m A kd S ∧ Frame A kd m0 m

/-- **`setCopy` copies slot `s`'s set into slot `d`**, another slot. -/
theorem setCopy_ok (o : Oracle σ) {ofs : Nat} {A : Word} {s1 : PancakeState σ} (hA : Area ofs A s1) {kd ks : Nat}
    (hkd : kd < slots) (hks : ks < slots) (hne : kd ≠ ks) (hd : s1.locals "d" = some (BitVec.ofNat 64 kd))
    (hs : s1.locals "s" = some (BitVec.ofNat 64 ks)) {Sd Ss : Nat → Bool} (hSd : SetAt s1.memory A kd Sd)
    (hSs : SetAt s1.memory A ks Ss) :
    ∃ body, Lower.lower (setCopy .none ofs) = some body ∧
      SafeR o (fun s => s = s1) body (CopyRet A kd Ss s1.memory) fun _ => False := by
  let m0 := s1.memory
  have l2 := hSs.lo
  have h2 := hSs.hi
  rw [setWords_eq] at l2 h2
  let lo := (m0 (slotW A ks 0)).toNat
  let hi := (m0 (slotW A ks 1)).toNat
  have blo : lo < 1026 := l2
  have bhi : hi < 1026 := h2
  refine body_of ?_
  dsimp only [setCopy]
  let l1' : List (String × Value) := [("p", at_ A (off ks)), ("q", at_ A (off kd)), ("a", A),
    ("d", BitVec.ofNat 64 kd), ("s", BitVec.ofNat 64 ks)]
  let lR : List (String × Value) := ("hi", BitVec.ofNat 64 hi) :: ("lo", BitVec.ofNat 64 lo) :: l1'
  let F1 : (Word → Word) → Prop := fun m => SetAt m A kd (fun _ => false) ∧ Frame A kd m0 m
  let G : (Word → Word) → Prop := fun m => SetAt m A kd Ss ∧ Frame A kd m0 m
  -- slot `ks` as at the entry once slot `kd` is emptied
  have hks' : ∀ m, F1 m → ∀ i, i < setSize / 8 → m (slotW A ks i) = m0 (slotW A ks i) := fun m hm i hi' =>
    hm.2 _ fun ⟨i', hi'', e⟩ => hne (slotW_inj hkd hks hi'' hi' e.symm).1
  have hR : Frag o (readWin "p" "lo" "hi") (RunF s1 l1' F1) (RunF s1 lR F1) :=
    frag_each o (lowK_any _ (k := .skip) rfl) fun s hs => frag_conseq
      (readWin_frag o hA hks (l := l1') (m0 := s.memory) (by decide) (by decide) rfl rfl rfl
        (setAt_frame hSs fun i hi' => hks' _ hs.2 i hi'))
      (fun u hu => runF_like hs hu)
      fun u h => ⟨⟨fun q hq => by
        simp only [lR, List.mem_cons] at hq
        rcases hq with rfl | rfl | hq
        · rw [vals_lookup h.1.vals (lookup_head _ _ _), hks' _ hs.2 1 (by decide)]
        · rw [vals_lookup h.1.vals rfl, hks' _ hs.2 0 (by decide)]
        · exact h.1.vals q (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hq)),
        h.1.memaddrs, h.1.base, h.1.code, h.1.be⟩, by rw [h.2]; exact hs.2⟩
  refine fragR_conseq (P0 := RunF s1 [("d", BitVec.ofNat 64 kd), ("s", BitVec.ofNat 64 ks)] (· = m0))
    (fragR_append (fragR_of (frag_append (frag_append (frag_append (start2_frag o hA (by decide) (by decide)
      (by decide) (by decide) hkd hks rfl rfl rfl rfl rfl) (clearQ_frag o hA hkd (l := l1') rfl rfl rfl rfl hSd)) hR)
      ?_)) (fragR_ret o rfl fun u (h : RunF s1 lR G u) => ⟨_, rfl, rfl, h.2⟩))
    (entry_two hd hs) fun _ h => h
  refine frag_each o (lowK_any _ (k := .skip) rfl) fun s hs => ?_
  obtain ⟨hs1, hs2⟩ := hs.2
  refine frag_conseq (P0 := RunF s1 lR (· = s.memory)) ?_ (fun u hu => runF_like hs hu) fun _ h => h
  let m1 := s.memory
  refine frag_append (xs := [_, _]) (wordLoop_frag o hA hkd hks (g := fun _ s => s) (l := lR) rfl (lov := lo)
    (hiv := hi) rfl rfl (by decide) (by decide) rfl rfl (by rw [setWords_eq]; omega) (by rw [setWords_eq]; omega)
    (m0 := m1) fun u i hi' h => slotLoad_eval hA h.1.memaddrs hks (by rw [setSize_eq]; rw [setWords_eq] at hi'; omega)
      (bit_eval rfl (vals_lookup h.1.vals rfl) (vals_lookup h.1.vals (lookup_head _ _ _)))) ?_
  refine frag_append (xs := [_]) (runF_store o hA rfl rfl (y := off kd + 8 * 0)
    (slotW_lt hkd (by rw [setSize_eq]; omega)) (slotW_mod kd 0)
    (fun u h => by rw [Nat.mul_zero, Nat.add_zero]; exact vals_lookup h.1.vals rfl)
    (val := fun _ => m0 (slotW A ks 0)) (fun u h => by rw [← ofNat_toNat (m0 _)]; exact vals_lookup h.1.vals rfl)
    (G := fun m => ∃ m2, Worded (fun _ s => s) A kd ks lo (hi + 1) m1 m2 ∧
      m = upd m2 (slotW A kd 0) (m0 (slotW A ks 0)))
    fun m hc => ⟨m, hc, rfl⟩) ?_
  exact frag_conseq (runF_store o hA rfl
    rfl (y := off kd + 8 * 1) (slotW_lt hkd (by rw [setSize_eq]; omega)) (slotW_mod kd 1)
    (fun u h => hiAddr_eval rfl (vals_lookup h.1.vals rfl)) (val := fun _ => m0 (slotW A ks 1))
    (fun u h => by rw [← ofNat_toNat (m0 _)]; exact vals_lookup h.1.vals rfl)
    (G := fun m => ∃ m2, Worded (fun _ s => s) A kd ks lo (hi + 1) m1 m2 ∧
      m = upd (upd m2 (slotW A kd 0) (m0 (slotW A ks 0))) (slotW A kd 1) (m0 (slotW A ks 1)))
    fun m ⟨m2, hc, e⟩ => ⟨m2, hc, by rw [e]; rfl⟩) (fun _ h => h)
    fun u h => runF_mono h (fun _ q => q) fun m ⟨m2, hc, e⟩ => e ▸ copy_setAt hkd hks hne hSs hs1 hs2 hc

/-! ## Minus -/

/-- Slot `ks`'s bits from word `lo` to below `e` taken out of slot `kd`'s, every other word as in `m0`. -/
def andNot (d s : Word) : Word := d &&& (s ^^^ BitVec.ofNat 64 all1)

theorem getLsbD_andNot (a b : Word) {j : Nat} (hj : j < 64) :
    (andNot a b).getLsbD j = (a.getLsbD j && !b.getLsbD j) := by
  rw [andNot, BitVec.getLsbD_and, BitVec.getLsbD_xor]
  have : (BitVec.ofNat 64 all1).getLsbD j = true := by
    rw [BitVec.getLsbD_ofNat]; simp only [all1]
    rw [Nat.testBit_two_pow_sub_one]; simp [hj]
  rw [this]; cases b.getLsbD j <;> rfl

/-- **A difference with no word left**: slot `kd`'s words all cleared by slot `ks`'s, an emptied window gives slot
`kd` the difference, empty. -/
theorem minus_empty {A : Word} {kd ks : Nat} (hkd : kd < slots) {m0 M : Word → Word}
    {Sd Ss : Nat → Bool} (hSd : SetAt m0 A kd Sd) (hSs : SetAt m0 A ks Ss)
    (ha : Worded andNot A kd ks (m0 (slotW A kd 0)).toNat ((m0 (slotW A kd 1)).toNat + 1) m0 M)
    (hz : ∀ w, (m0 (slotW A kd 0)).toNat ≤ w → w ≤ (m0 (slotW A kd 1)).toNat → M (slotW A kd (2 + w)) = 0) :
    SetAt (emptied A kd M) A kd (fun x => Sd x && !Ss x) ∧ Frame A kd m0 (emptied A kd M) := by
  have l1 := hSd.lo
  have h1 := hSd.hi
  rw [setWords_eq] at l1 h1
  have hnone : ∀ x, (Sd x && !Ss x) = false := fun x => by
    cases e : Sd x
    · rfl
    · cases e2 : Ss x
      · have hw := hSd.win x e
        have hsm := hSd.small x e
        rw [setWords_eq] at hsm
        have := ha.1 (x / 64) hw.1 (by omega)
        rw [hz _ hw.1 hw.2] at this
        have hb := congrArg (fun W => W.getLsbD (x % 64)) this
        simp only at hb
        rw [getLsbD_andNot _ _ (by omega), hSd.bits _ (by rw [setWords_eq]; omega) _ (by omega),
          hSs.bits _ (by rw [setWords_eq]; omega) _ (by omega), show 64 * (x / 64) + x % 64 = x by omega, e, e2]
          at hb
        simp at hb
      · rfl
  have hfun : (fun x => Sd x && !Ss x) = fun _ => false := funext hnone
  rw [hfun]
  exact cleared_empty hkd hSd rfl rfl ⟨fun w h1' h2' => hz w h1' (by omega),
    fun a h => ha.2 a fun w h1' h2' => h w h1' h2'⟩

/-- **A difference with words left**: slot `ks`'s bits taken out of slot `kd`'s words, the window cut to `z1` and
`z2`, the first and last words still holding one, give slot `kd` the difference. -/
theorem minus_some {A : Word} {kd ks : Nat} (hkd : kd < slots) {m0 M : Word → Word}
    {Sd Ss : Nat → Bool} (hSd : SetAt m0 A kd Sd) (hSs : SetAt m0 A ks Ss)
    (ha : Worded andNot A kd ks (m0 (slotW A kd 0)).toNat ((m0 (slotW A kd 1)).toNat + 1) m0 M) {z1 z2 : Nat}
    (h1z : (m0 (slotW A kd 0)).toNat ≤ z1) (h12 : z1 ≤ z2) (h2z : z2 ≤ (m0 (slotW A kd 1)).toNat)
    (hn1 : M (slotW A kd (2 + z1)) ≠ 0)
    (hb1 : ∀ w, (m0 (slotW A kd 0)).toNat ≤ w → w < z1 → M (slotW A kd (2 + w)) = 0)
    (hb2 : ∀ w, z2 < w → w ≤ (m0 (slotW A kd 1)).toNat → M (slotW A kd (2 + w)) = 0) :
    SetAt (upd (upd M (slotW A kd 0) (BitVec.ofNat 64 z1)) (slotW A kd 1) (BitVec.ofNat 64 z2)) A kd
        (fun x => Sd x && !Ss x) ∧
      Frame A kd m0 (upd (upd M (slotW A kd 0) (BitVec.ofNat 64 z1)) (slotW A kd 1) (BitVec.ofNat 64 z2)) := by
  have l1 := hSd.lo
  have h1 := hSd.hi
  rw [setWords_eq] at l1 h1
  have wd := hSd.win
  have hout := fun w j (hj : j < 64) => setAt_out hSd (w := w) (j := j) hj
  generalize (m0 (slotW A kd 0)).toNat = dl at l1 ha h1z hb1 wd hout
  generalize (m0 (slotW A kd 1)).toNat = dh at h1 ha h2z hb2 wd hout
  have h01 : slotW A kd 0 ≠ slotW A kd 1 := slotW_ne hkd (by decide) (by decide) (by decide)
  let m := upd (upd M (slotW A kd 0) (BitVec.ofNat 64 z1)) (slotW A kd 1) (BitVec.ofNat 64 z2)
  have e0 : (m (slotW A kd 0)).toNat = z1 := by
    show (upd (upd M _ _) _ _ (slotW A kd 0)).toNat = z1
    rw [upd_ne _ h01, upd_eq, BitVec.toNat_ofNat]; omega
  have e1 : (m (slotW A kd 1)).toNat = z2 := by
    show (upd (upd M _ _) _ _ (slotW A kd 1)).toNat = z2
    rw [upd_eq, BitVec.toNat_ofNat]; omega
  have eb : ∀ w, w < setWords → m (slotW A kd (2 + w)) = M (slotW A kd (2 + w)) := fun w hw => by
    show upd (upd M _ _) _ _ _ = _
    rw [upd_ne _ (slotW_bit_ne hkd hw).2, upd_ne _ (slotW_bit_ne hkd hw).1]
  have hbit : ∀ w, w < setWords → ∀ j, j < 64 →
      (M (slotW A kd (2 + w))).getLsbD j = (Sd (64 * w + j) && !Ss (64 * w + j)) :=
    fun w hw j hj => by
      by_cases hin : dl ≤ w ∧ w < dh + 1
      · rw [ha.1 w hin.1 hin.2, getLsbD_andNot _ _ hj, hSd.bits w hw j hj, hSs.bits w hw j hj]
      · rw [setWords_eq] at hw
        rw [ha.2 _ fun w' h1' h2' e => hin ?_, hSd.bits w (by rw [setWords_eq]; omega) j hj]
        · rw [hout w j hj fun h => hin ⟨h.1, by omega⟩]; rfl
        · have := (slotW_inj hkd hkd (by rw [setSize_eq]; omega) (by rw [setSize_eq]; omega) e).2
          exact ⟨by omega, by omega⟩
  refine ⟨⟨by rw [e0, setWords_eq]; omega, by rw [e1, setWords_eq]; omega, fun w hw j hj => by
    show (m (slotW A kd (2 + w))).getLsbD j = _
    rw [eb w hw]; exact hbit w hw j hj, fun x hx => ?_, fun x hx => ?_, fun _ => ?_⟩, fun a ha' => ?_⟩
  · simp only [Bool.and_eq_true] at hx; exact hSd.small x hx.1
  · show (m (slotW A kd 0)).toNat ≤ x / 64 ∧ x / 64 ≤ (m (slotW A kd 1)).toNat
    rw [e0, e1]
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at hx
    have hw := wd x hx.1
    have hsm := hSd.small x hx.1
    rw [setWords_eq] at hsm
    have hb := hbit (x / 64) (by rw [setWords_eq]; omega) (x % 64) (by omega)
    rw [show 64 * (x / 64) + x % 64 = x by omega, hx.1, hx.2] at hb
    have hne := word_ne0 (W := M (slotW A kd (2 + x / 64))) (by simpa using hb)
    refine ⟨Classical.byContradiction fun h => hne (hb1 _ hw.1 (by omega)), Classical.byContradiction fun h =>
      hne (hb2 _ (by omega) hw.2)⟩
  · obtain ⟨j, hj, hb⟩ := exists_bit hn1
    refine ⟨64 * z1 + j, ?_⟩
    rw [← hbit z1 (by rw [setWords_eq]; omega) j hj]; exact hb
  · have hne' : ∀ i, i < setSize / 8 → a ≠ slotW A kd i := fun i hi e => ha' ⟨i, hi, e⟩
    show upd (upd M _ _) _ _ a = _
    rw [upd_ne _ (hne' 1 (by decide)), upd_ne _ (hne' 0 (by decide))]
    exact ha.2 a fun w _ _ => hne' (2 + w) (by rw [setSize_eq]; omega)

/-- What `setMinus` gives back: zero, slot `kd` the difference, every other word as in `m0`. -/
def MinusRet (A : Word) (kd : Nat) (Sd Ss : Nat → Bool) (m0 : Word → Word) : Ret :=
  fun v m => v = 0 ∧ SetAt m A kd (fun x => Sd x && !Ss x) ∧ Frame A kd m0 m

/-- **The bits taken out**: slot `ks`'s bits taken out of slot `kd`'s words in its window. -/
theorem minusBits_frag (o : Oracle σ) {ofs : Nat} {A : Word} {s1 : PancakeState σ} (hA : Area ofs A s1) {kd ks : Nat}
    (hkd : kd < slots) (hks : ks < slots) {l : List (String × Value)} {m0 : Word → Word}
    (hq : l.lookup "q" = some (at_ A (off kd))) (hp : l.lookup "p" = some (at_ A (off ks)))
    (hw : Fresh "w" l = true) {Sd : Nat → Bool} (hSd : SetAt m0 A kd Sd) :
    Frag o minusBits (RunF s1 (("hi", BitVec.ofNat 64 (m0 (slotW A kd 1)).toNat) ::
          ("lo", BitVec.ofNat 64 (m0 (slotW A kd 0)).toNat) :: l)
        (· = m0))
      (RunF s1 (("hi", BitVec.ofNat 64 (m0 (slotW A kd 1)).toNat) ::
          ("lo", BitVec.ofNat 64 (m0 (slotW A kd 0)).toNat) :: l)
        (Worded andNot A kd ks (m0 (slotW A kd 0)).toNat ((m0 (slotW A kd 1)).toNat + 1) m0)) := by
  have l1 := hSd.lo
  have h1 := hSd.hi
  have hq' : (("hi", BitVec.ofNat 64 (m0 (slotW A kd 1)).toNat) ::
      ("lo", BitVec.ofNat 64 (m0 (slotW A kd 0)).toNat) :: l).lookup "q" = some (at_ A (off kd)) := by
    rw [ScanRun.lookup_cons_ne (by decide), ScanRun.lookup_cons_ne (by decide)]; exact hq
  have hp' : ∀ i, (("w", BitVec.ofNat 64 i) :: ("hi", BitVec.ofNat 64 (m0 (slotW A kd 1)).toNat) ::
      ("lo", BitVec.ofNat 64 (m0 (slotW A kd 0)).toNat) :: l).lookup "p" = some (at_ A (off ks)) := fun i => by
    rw [ScanRun.lookup_cons_ne (by decide), ScanRun.lookup_cons_ne (by decide), ScanRun.lookup_cons_ne (by decide)]
    exact hp
  exact wordLoop_frag o hA hkd hks (g := fun d s => d &&& (s ^^^ BitVec.ofNat 64 all1)) rfl rfl rfl (by decide)
    (by decide) (ScanRun.fresh_cons (by decide) (ScanRun.fresh_cons (by decide) hw)) hq' l1 h1
    fun u i hi' h => ev_and (slotLoad_eval hA h.1.memaddrs hkd (by rw [setSize_eq]; rw [setWords_eq] at hi'; omega)
      (bit_eval rfl (vals_lookup h.1.vals (by rw [ScanRun.lookup_cons_ne (by decide)]; exact hq'))
        (vals_lookup h.1.vals (lookup_head _ _ _))))
      (ev_xor (slotLoad_eval hA h.1.memaddrs hks (by rw [setSize_eq]; rw [setWords_eq] at hi'; omega)
        (bit_eval rfl (vals_lookup h.1.vals (hp' i)) (vals_lookup h.1.vals (lookup_head _ _ _)))) rfl)

/-- A word of slot `k`'s bits compared with zero, its index in `x` and the slot's address in `q`. -/
theorem bitZero_eval {E : PancakeExp} {x : String}
    (he : Lower.lowerExp (Syntax.eEq (.loadw 1 (bitWord "q" (Syntax.v x))) (Syntax.n 0)) = some E) {ofs : Nat}
    {A : Word} {s0 u : PancakeState σ} (hA : Area ofs A s0) (hm : u.memaddrs = s0.memaddrs) {k : Nat}
    (hk : k < slots) {w : Nat} (hw : w < setWords) (hq : u.locals "q" = some (at_ A (off k)))
    (hx : u.locals x = some (BitVec.ofNat 64 w)) : eval u E = some
        (bw (decide (u.memory (slotW A k (2 + w)) = 0))) := by
  cases he
  rw [eval_equal _ (slotLoad_eval hA hm hk (by rw [setSize_eq]; rw [setWords_eq] at hw; omega)
      (bit_eval rfl hq hx)) rfl]
  by_cases e : u.memory (slotW A k (2 + w)) = 0 <;> simp [e, bw]

/-- **The window cut** to the words still holding one, stored, or emptied when none does: slot `kd` holds the
difference. -/
theorem trimWin_frag (o : Oracle σ) {ofs : Nat} {A : Word} {s1 : PancakeState σ} (hA : Area ofs A s1) {kd ks : Nat}
    (hkd : kd < slots) {l : List (String × Value)} (hq : l.lookup "q" = some (at_ A (off kd)))
    (hf : Fresh "lo" l = true ∧ Fresh "hi" l = true ∧ Fresh "go" l = true) {m0 M : Word → Word}
    {Sd Ss : Nat → Bool} (hSd : SetAt m0 A kd Sd) (hSs : SetAt m0 A ks Ss)
    (ha : Worded andNot A kd ks (m0 (slotW A kd 0)).toNat ((m0 (slotW A kd 1)).toNat + 1) m0 M) :
    Frag o trimWin (RunF s1 (("hi", BitVec.ofNat 64 (m0 (slotW A kd 1)).toNat) ::
        ("lo", BitVec.ofNat 64 (m0 (slotW A kd 0)).toNat) :: l) (· = M))
      (RunF s1 l fun m => SetAt m A kd (fun x => Sd x && !Ss x) ∧ Frame A kd m0 m) := by
  obtain ⟨f1, f2, f3⟩ := hf
  have l1 := hSd.lo
  have h1 := hSd.hi
  rw [setWords_eq] at l1 h1
  let dlo := (m0 (slotW A kd 0)).toNat
  let dhi := (m0 (slotW A kd 1)).toNat
  -- the first word from `dlo` that holds a position, or past `dhi`
  let p1 : Nat → Bool := fun w => decide (dhi < w) || !decide (M (slotW A kd (2 + w)) = 0)
  let z1 := seek p1 (dhi + 1 - dlo) dlo
  have hz1a : dlo ≤ z1 := seek_ge _ _ _
  have hz1b : z1 ≤ max dlo (dhi + 1) := by have := seek_le p1 (dhi + 1 - dlo) dlo; omega
  have hz1s : p1 z1 = true := seek_stop _ _ _ (by
    simp only [p1, Bool.or_eq_true, decide_eq_true_eq]; left; omega)
  have hz1p : ∀ w, dlo ≤ w → w < z1 → w ≤ dhi ∧ M (slotW A kd (2 + w)) = 0 := fun w h1' h2' => by
    have := seek_before p1 _ _ w h1' h2'
    simp only [p1, Bool.or_eq_false_iff, decide_eq_false_iff_not, Bool.not_eq_false', decide_eq_true_eq] at this
    exact ⟨by omega, this.2⟩
  have hz1n : z1 ≤ dhi → M (slotW A kd (2 + z1)) ≠ 0 := fun h e => by
    simp only [p1, Bool.or_eq_true, decide_eq_true_eq, Bool.not_eq_true', decide_eq_false_iff_not] at hz1s
    rcases hz1s with h' | h'
    · omega
    · exact h' e
  let t1 := z1 - dlo
  have ht1 : t1 = z1 - dlo := rfl
  let lB : List (String × Value) := [("hi", BitVec.ofNat 64 dhi)] ++ l
  have hqB : lB.lookup "q" = some (at_ A (off kd)) := by
    simp only [lB, List.cons_append, List.nil_append]; rw [ScanRun.lookup_cons_ne (by decide)]; exact hq
  have hloB : Fresh "lo" lB = true := ScanRun.fresh_cons (by decide) f1
  have hgoB : Fresh "go" lB = true := ScanRun.fresh_cons (by decide) f3
  let I1 (j : Nat) : Assn σ := fun u => RunF s1 lB (· = M) u ∧ u.locals "go" = some (bw (decide (j ≤ t1))) ∧
    u.locals "lo" = some (BitVec.ofNat 64 (if j ≤ t1 then dlo + j else z1)) ∧ j ≤ t1 + 1
  have hI1 : ∀ j, Safe.ClockFree (I1 j) := fun j s k h => ⟨runF_clock _ _ _ s k h.1, h.2⟩
  -- setting `go` or `lo` keeps the rest
  have setB : ∀ (u : PancakeState σ) (x : String) (v : Value), Fresh x lB = true → RunF s1 lB (· = M) u →
      RunF s1 lB (· = M) (setL u x v) := fun u x v hx h =>
    ⟨⟨ScanRun.vals_setL h.1.vals hx v, h.1.memaddrs, h.1.base, h.1.code, h.1.be⟩, h.2⟩
  refine frag_append (xs := [_]) (frag_conseq (runF_dec o rfl (l := [("hi", BitVec.ofNat 64 dhi),
    ("lo", BitVec.ofNat 64 dlo)] ++ l) (by simpa [Fresh] using f3) (v := 1) fun _ _ => rfl) (fun u h => h)
    (P' := I1 0) fun u h => ⟨runF_mono h (fun q hq => by
      simp only [lB, List.cons_append, List.nil_append, List.mem_cons] at hq ⊢
      rcases hq with hq | hq
      · exact Or.inr (Or.inl hq)
      · exact Or.inr (Or.inr (Or.inr hq))) fun _ e => e, by
        rw [vals_lookup h.1.vals (lookup_head _ _ _)]; simp [bw], by
        rw [vals_lookup h.1.vals rfl, if_pos (Nat.zero_le _), Nat.add_zero], by omega⟩) ?_
  have stop1 : ∀ j, j = t1 → Frag o [.assign "go" (Syntax.n 0)] (I1 j) (I1 (j + 1)) := fun j hj =>
    set_frag o rfl (hI1 _) fun u h => ⟨0, rfl, ⟨_, h.2.1⟩, setB u "go" 0 hgoB h.1, by
      show (if "go" = "go" then some (0 : Word) else u.locals "go") = some (bw (decide (j + 1 ≤ t1)))
      rw [if_pos rfl, decide_eq_false (by omega)]; rfl, by
      show (if "lo" = "go" then some (0 : Word) else u.locals "lo") = _
      rw [if_neg (by decide), h.2.2.1, if_pos (by omega), if_neg (by omega)]
      congr 2; omega, by omega⟩
  have step1 : ∀ j, j < t1 → Frag o [inc "lo"] (I1 j) (I1 (j + 1)) := fun j hj =>
    set_frag o rfl (hI1 _) fun u h =>
      ⟨BitVec.ofNat 64 (dlo + j + 1), by simp only [eval, h.2.2.1, if_pos (Nat.le_of_lt hj), BitVec.ofNat_add],
        ⟨_, h.2.2.1⟩, setB u "lo" _ hloB h.1, by
          show (if "go" = "lo" then some (BitVec.ofNat 64 (dlo + j + 1)) else u.locals "go") = _
          rw [if_neg (by decide), h.2.1, decide_eq_true (by omega), decide_eq_true (by omega)], by
          show (if "lo" = "lo" then some (BitVec.ofNat 64 (dlo + j + 1)) else u.locals "lo") = _
          rw [if_pos rfl, if_pos (by omega)]; congr 2, by omega⟩
  refine frag_append (xs := [_]) (frag_conseq (frag_count o (C := .var "go") rfl
    (lowK_any _ (k := .skip) rfl) hI1 (fun j => noDecl (P' := I1 j) _ rfl) (g := fun j => decide (j ≤ t1))
    (fun j u h => h.2.1) (fun j hg => ?_) 0) (fun u h => h)
    (P' := fun u => RunF s1 lB (· = M) u ∧ u.locals "lo" = some (BitVec.ofNat 64 z1) ∧ ∃ g, u.locals "go" = some g)
    fun u ⟨j, h, hg⟩ => ⟨h.1, by rw [h.2.2.1, if_neg (by simpa using hg)], ⟨_, h.2.1⟩⟩) ?_
  · have hj : j ≤ t1 := of_decide_eq_true hg
    refine ScanRun.frag_if o rfl (lowK_any _ (k := .skip) rfl)
      (lowK_any _ (k := .skip) rfl) rfl rfl (hI1 _) (b := decide (dlo + j ≤ dhi))
      (fun u h => FramerCode.eval_le (by omega) (by omega)
        (ev_var (by rw [h.2.2.1, if_pos hj])) (ev_var (vals_lookup h.1.1.vals (l := lB) rfl)))
      (fun e => ?_) fun e => stop1 j (by
        have := of_decide_eq_false e
        rcases Nat.lt_or_ge j t1 with hlt | hge
        · have := (hz1p (dlo + j) (by omega) (by omega)).1
          omega
        · omega)
    refine ScanRun.frag_if o rfl (lowK_any _ (k := .skip) rfl) (lowK_any _ (k := .skip) rfl) rfl rfl (hI1 _)
      (b := decide (M (slotW A kd (2 + (dlo + j))) = 0)) (fun u h => by
        rw [← h.1.2]
        exact bitZero_eval rfl hA h.1.1.memaddrs hkd (by rw [setWords_eq]; have := of_decide_eq_true e; omega)
          (vals_lookup h.1.1.vals hqB) (by rw [h.2.2.1, if_pos hj]))
      (fun e2 => step1 j ?_) fun e2 => stop1 j ?_
    · have hz := of_decide_eq_true e2
      rcases Nat.lt_or_ge j t1 with hlt | hge
      · exact hlt
      · exact absurd (by rw [show z1 = dlo + j by omega]; exact hz) (hz1n (by have := of_decide_eq_true e; omega))
    · have hz : ¬M (slotW A kd (2 + (dlo + j))) = 0 := by simpa using e2
      rcases Nat.lt_or_ge j t1 with hlt | hge
      · exact absurd (hz1p (dlo + j) (by omega) (by omega)).2 hz
      · omega
  -- the last word down to `z1` that holds a position, or `dhi` when none from `z1` does
  let p2 : Nat → Bool := fun w => !decide (M (slotW A kd (2 + w)) = 0)
  let hiEnd := if z1 ≤ dhi then seekDown p2 (dhi - z1) dhi else dhi
  have hE1 : z1 ≤ dhi → z1 ≤ hiEnd ∧ hiEnd ≤ dhi ∧ M (slotW A kd (2 + hiEnd)) ≠ 0 ∧
      ∀ w, hiEnd < w → w ≤ dhi → M (slotW A kd (2 + w)) = 0 := fun hz => by
    simp only [hiEnd, if_pos hz]
    refine ⟨by have := seekDown_ge p2 (dhi - z1) dhi (by omega); omega, seekDown_le _ _ _, ?_, fun w h1' h2' => ?_⟩
    · have := seekDown_stop p2 (dhi - z1) dhi (by omega) (by
        rw [show dhi - (dhi - z1) = z1 by omega]; simpa [p2] using hz1n hz)
      simpa [p2] using this
    · have := seekDown_after p2 _ _ w h1' h2'
      simpa [p2] using this
  have hE2 : dhi < z1 → hiEnd = dhi := fun h => if_neg (by omega)
  have hEle : hiEnd ≤ dhi := by
    by_cases hz : z1 ≤ dhi
    · exact (hE1 hz).2.1
    · rw [hE2 (by omega)]; exact Nat.le_refl _
  let t2 := dhi - hiEnd
  have ht2 : t2 = dhi - hiEnd := rfl
  let lC : List (String × Value) := [("lo", BitVec.ofNat 64 z1)] ++ l
  have hqC : lC.lookup "q" = some (at_ A (off kd)) := by
    simp only [lC, List.cons_append, List.nil_append]; rw [ScanRun.lookup_cons_ne (by decide)]; exact hq
  have hhiC : Fresh "hi" lC = true := ScanRun.fresh_cons (by decide) f2
  have hgoC : Fresh "go" lC = true := ScanRun.fresh_cons (by decide) f3
  let I2 (j : Nat) : Assn σ := fun u => RunF s1 lC (· = M) u ∧ u.locals "go" = some (bw (decide (j ≤ t2))) ∧
    u.locals "hi" = some (BitVec.ofNat 64 (if j ≤ t2 then dhi - j else hiEnd)) ∧ j ≤ t2 + 1
  have hI2 : ∀ j, Safe.ClockFree (I2 j) := fun j s k h => ⟨runF_clock _ _ _ s k h.1, h.2⟩
  have setC : ∀ (u : PancakeState σ) (x : String) (v : Value), Fresh x lC = true → RunF s1 lC (· = M) u →
      RunF s1 lC (· = M) (setL u x v) := fun u x v hx h =>
    ⟨⟨ScanRun.vals_setL h.1.vals hx v, h.1.memaddrs, h.1.base, h.1.code, h.1.be⟩, h.2⟩
  refine frag_append (xs := [_]) (set_frag o rfl (hI2 0) fun u h => ⟨1, rfl, h.2.2, ⟨⟨fun q hq => ?_,
    h.1.1.memaddrs, h.1.1.base, h.1.1.code, h.1.1.be⟩, h.1.2⟩, by
      show (if "go" = "go" then some (1 : Word) else u.locals "go") = _
      rw [if_pos rfl, decide_eq_true (Nat.zero_le _)]; rfl, by
      show (if "hi" = "go" then some (1 : Word) else u.locals "hi") = _
      rw [if_neg (by decide), vals_lookup h.1.1.vals (l := lB) rfl, if_pos (Nat.zero_le _), Nat.sub_zero], by omega⟩) ?_
  · simp only [lC, List.cons_append, List.nil_append, List.mem_cons] at hq
    rcases hq with rfl | hq
    · show (if "lo" = "go" then some (1 : Word) else u.locals "lo") = _
      rw [if_neg (by decide)]; exact h.2.1
    · show (if q.1 = "go" then some (1 : Word) else u.locals q.1) = _
      rw [if_neg (ScanRun.fresh_ne f3 q hq)]; exact h.1.1.vals q (List.mem_cons_of_mem _ hq)
  have stop2 : ∀ j, j = t2 → Frag o [.assign "go" (Syntax.n 0)] (I2 j) (I2 (j + 1)) := fun j hj =>
    set_frag o rfl (hI2 _) fun u h => ⟨0, rfl, ⟨_, h.2.1⟩, setC u "go" 0 hgoC h.1, by
      show (if "go" = "go" then some (0 : Word) else u.locals "go") = some (bw (decide (j + 1 ≤ t2)))
      rw [if_pos rfl, decide_eq_false (by omega)]; rfl, by
      show (if "hi" = "go" then some (0 : Word) else u.locals "hi") = _
      rw [if_neg (by decide), h.2.2.1, if_pos (by omega), if_neg (by omega)]
      congr 2; omega, by omega⟩
  have step2 : ∀ j, j < t2 → Frag o [.assign "hi" (Syntax.eSub (Syntax.v "hi") (Syntax.n 1))] (I2 j) (I2 (j + 1)) :=
    fun j hj => set_frag o rfl (hI2 _) fun u h =>
      ⟨BitVec.ofNat 64 (dhi - j - 1), by
        simp only [eval, h.2.2.1, if_pos (Nat.le_of_lt hj)]
        rw [ofNat_sub_one (by omega) (by omega)], ⟨_, h.2.2.1⟩, setC u "hi" _ hhiC h.1, by
          show (if "go" = "hi" then some (BitVec.ofNat 64 (dhi - j - 1)) else u.locals "go") = _
          rw [if_neg (by decide), h.2.1, decide_eq_true (by omega), decide_eq_true (by omega)], by
          show (if "hi" = "hi" then some (BitVec.ofNat 64 (dhi - j - 1)) else u.locals "hi") = _
          rw [if_pos rfl, if_pos (by omega)]; congr 2, by omega⟩
  refine frag_append (xs := [_]) (frag_conseq (frag_count o (C := .var "go") rfl
    (lowK_any _ (k := .skip) rfl) hI2 (fun j => noDecl (P' := I2 j) _ rfl) (g := fun j => decide (j ≤ t2))
    (fun j u h => h.2.1) (fun j hg => ?_) 0) (fun u h => h)
    (P' := RunF s1 (("hi", BitVec.ofNat 64 hiEnd) :: lC) (· = M))
    fun u ⟨j, h, hg⟩ => ⟨⟨fun q hq => by
      simp only [List.mem_cons] at hq
      rcases hq with rfl | hq
      · rw [h.2.2.1, if_neg (by simpa using hg)]
      · exact h.1.1.vals q hq, h.1.1.memaddrs, h.1.1.base, h.1.1.code, h.1.1.be⟩, h.1.2⟩) ?_
  · have hj : j ≤ t2 := of_decide_eq_true hg
    refine ScanRun.frag_if o rfl (lowK_any _ (k := .skip) rfl)
      (lowK_any _ (k := .skip) rfl) rfl rfl (hI2 _) (b := decide (z1 ≤ dhi - j))
      (fun u h => FramerCode.eval_le (by omega) (by omega) (ev_var (vals_lookup h.1.1.vals (l := lC) rfl))
        (ev_var (by rw [h.2.2.1, if_pos hj])))
      (fun e => ?_) fun e => stop2 j (by
        have := of_decide_eq_false e
        by_cases hz : z1 ≤ dhi
        · have := (hE1 hz).1; omega
        · rw [ht2, hE2 (by omega)]; omega)
    refine ScanRun.frag_if o rfl (lowK_any _ (k := .skip) rfl) (lowK_any _ (k := .skip) rfl) rfl rfl (hI2 _)
      (b := decide (M (slotW A kd (2 + (dhi - j))) = 0)) (fun u h => by
        rw [← h.1.2]
        exact bitZero_eval rfl hA h.1.1.memaddrs hkd (by rw [setWords_eq]; omega) (vals_lookup h.1.1.vals hqC)
          (by rw [h.2.2.1, if_pos hj]))
      (fun e2 => step2 j ?_) fun e2 => stop2 j ?_
    · have hz := of_decide_eq_true e2
      have hz1 := of_decide_eq_true e
      have hzd : z1 ≤ dhi := by omega
      rcases Nat.lt_or_ge j t2 with hlt | hge
      · exact hlt
      · exact absurd (by rw [show hiEnd = dhi - j by omega]; exact hz) (hE1 hzd).2.2.1
    · have hz : ¬M (slotW A kd (2 + (dhi - j))) = 0 := by simpa using e2
      have hz1 := of_decide_eq_true e
      have hzd : z1 ≤ dhi := by omega
      rcases Nat.lt_or_ge j t2 with hlt | hge
      · exact absurd ((hE1 hzd).2.2.2 (dhi - j) (by omega) (by omega)) hz
      · omega
  have hqW : ∀ (u : PancakeState σ) (G : (Word → Word) → Prop), RunF s1 (("hi", BitVec.ofNat 64 hiEnd) :: lC) G u →
      u.locals "q" = some (at_ A (off kd)) := fun u G h =>
    vals_lookup h.1.vals (by rw [ScanRun.lookup_cons_ne (by decide)]; exact hqC)
  have hsub : ∀ q ∈ l, q ∈ ("hi", BitVec.ofNat 64 hiEnd) :: lC := fun q hq =>
    List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hq)
  refine ScanRun.frag_if o rfl (lowK_any _ (k := .skip) rfl)
    (lowK_any _ (k := .skip) rfl) rfl rfl (runF_clock _ _ _) (b := decide (hiEnd < z1))
    (fun u h => FramerCode.eval_lt (by omega) (by omega) (ev_var (vals_lookup h.1.vals (lookup_head _ _ _)))
      (ev_var (vals_lookup h.1.vals rfl))) (fun e => ?_) fun e => ?_
  · have hd : dhi < z1 := by
      have := of_decide_eq_true e
      by_cases hz : z1 ≤ dhi
      · have := (hE1 hz).1; omega
      · omega
    refine frag_append (xs := [_]) (runF_store o hA rfl rfl (y := off kd + 8 * 0)
      (slotW_lt hkd (by rw [setSize_eq]; omega)) (slotW_mod kd 0)
      (fun u h => by rw [Nat.mul_zero, Nat.add_zero]; exact hqW u _ h) (val := fun _ => 1) (fun _ _ => rfl)
      (G := fun m => m = upd M (slotW A kd 0) 1) fun m e => by subst e; rfl) ?_
    exact frag_conseq (runF_store o hA rfl rfl
      (y := off kd + 8 * 1) (slotW_lt hkd (by rw [setSize_eq]; omega)) (slotW_mod kd 1)
      (fun u h => hiAddr_eval rfl (hqW u _ h)) (val := fun _ => 0) (fun _ _ => rfl)
      (G := fun m => m = emptied A kd M) fun m e => by rw [e]; rfl) (fun _ h => h)
      fun u h => runF_mono h hsub fun m e => e ▸ minus_empty hkd hSd hSs ha fun w h1' h2' => (hz1p w h1' (by omega)).2
  · have hz : z1 ≤ dhi := by
      have := of_decide_eq_false e
      by_cases hz : z1 ≤ dhi
      · exact hz
      · rw [hE2 (by omega)] at this; omega
    obtain ⟨e1, e2, e3, e4⟩ := hE1 hz
    refine frag_append (xs := [_]) (runF_store o hA rfl rfl (y := off kd + 8 * 0)
      (slotW_lt hkd (by rw [setSize_eq]; omega)) (slotW_mod kd 0)
      (fun u h => by rw [Nat.mul_zero, Nat.add_zero]; exact hqW u _ h) (val := fun _ => BitVec.ofNat 64 z1)
      (fun u h => vals_lookup h.1.vals rfl)
      (G := fun m => m = upd M (slotW A kd 0) (BitVec.ofNat 64 z1)) fun m e => by subst e; rfl) ?_
    exact frag_conseq (runF_store o hA rfl rfl
      (y := off kd + 8 * 1) (slotW_lt hkd (by rw [setSize_eq]; omega)) (slotW_mod kd 1)
      (fun u h => hiAddr_eval rfl (hqW u _ h)) (val := fun _ => BitVec.ofNat 64 hiEnd)
      (fun u h => vals_lookup h.1.vals (lookup_head _ _ _))
      (G := fun m => m = upd (upd M (slotW A kd 0) (BitVec.ofNat 64 z1)) (slotW A kd 1) (BitVec.ofNat 64 hiEnd))
      fun m e => by rw [e]; rfl) (fun _ h => h)
      fun u h => runF_mono h hsub fun m e => e ▸ minus_some hkd hSd hSs ha hz1a e1 e2 (hz1n hz)
        (fun w h1' h2' => (hz1p w h1' h2').2) e4

/-- **`setMinus` takes slot `s`'s set out of slot `d`'s.** -/
theorem setMinus_ok (o : Oracle σ) {ofs : Nat} {A : Word} {s1 : PancakeState σ} (hA : Area ofs A s1) {kd ks : Nat}
    (hkd : kd < slots) (hks : ks < slots) (hd : s1.locals "d" = some (BitVec.ofNat 64 kd))
    (hs : s1.locals "s" = some (BitVec.ofNat 64 ks)) {Sd Ss : Nat → Bool} (hSd : SetAt s1.memory A kd Sd)
    (hSs : SetAt s1.memory A ks Ss) :
    ∃ body, Lower.lower (setMinus .none ofs) = some body ∧
      SafeR o (fun s => s = s1) body (MinusRet A kd Sd Ss s1.memory) fun _ => False := by
  let m0 := s1.memory
  refine body_of ?_
  dsimp only [setMinus]
  let l1' : List (String × Value) := [("p", at_ A (off ks)), ("q", at_ A (off kd)), ("a", A),
    ("d", BitVec.ofNat 64 kd), ("s", BitVec.ofNat 64 ks)]
  let l2' : List (String × Value) := [("hi", BitVec.ofNat 64 (m0 (slotW A kd 1)).toNat),
    ("lo", BitVec.ofNat 64 (m0 (slotW A kd 0)).toNat)] ++ l1'
  let G : (Word → Word) → Prop := fun m => SetAt m A kd (fun x => Sd x && !Ss x) ∧ Frame A kd m0 m
  have hB : Frag o trimWin
      (RunF s1 l2' (Worded andNot A kd ks (m0 (slotW A kd 0)).toNat ((m0 (slotW A kd 1)).toNat + 1) m0))
          (RunF s1 l1' G) :=
    frag_each o (lowK_any _ (k := .skip) rfl) fun s hs =>
      frag_conseq (trimWin_frag o hA hkd (l := l1') rfl ⟨rfl, rfl, rfl⟩ hSd hSs hs.2)
        (fun u hu => runF_like hs hu) fun _ h => h
  refine fragR_conseq (P0 := RunF s1 [("d", BitVec.ofNat 64 kd), ("s", BitVec.ofNat 64 ks)] (· = m0))
    (fragR_append (fragR_of (frag_append (frag_append (frag_append (start2_frag o hA (by decide) (by decide)
      (by decide) (by decide) hkd hks rfl rfl rfl rfl rfl) (readWin_frag o hA hkd (l := l1') (by decide) (by decide) rfl
        rfl rfl hSd)) (minusBits_frag o hA hkd hks (l := l1') rfl rfl rfl hSd)) hB))
      (fragR_ret o rfl fun u (h : RunF s1 l1' G u) => ⟨_, rfl, rfl, h.2⟩))
    (entry_two hd hs) fun _ h => h

/-! ## Calls -/

/-- **A call of a set function**: its code held, its arguments the values `vs`, its body shown from any entry with
the area and those parameters; the call's result `v` in `rt`, memory as `G v` says of what `R` gives back. -/
theorem setCall_frag (o : Oracle σ) {ofs : Nat} {A : Word} {s0 : PancakeState σ} (hA : Area ofs A s0)
    {rt f : String} {ps : List String} (hnd : ps.Nodup) {as : List Syntax.PExpr} {args : List PancakeExp}
    (has : Lower.lowerArgs as = some args) {body : PancakeProg} (hcode : s0.code f = some (ps, body))
    {l : List (String × Value)} {F : (Word → Word) → Prop} {vs : List Value} (hlen : ps.length = vs.length)
    (hargs : ∀ u, RunF s0 l F u → evalArgs u args = some vs) {R : (Word → Word) → Ret}
    (hbody : ∀ s1 : PancakeState σ, Area ofs A s1 → s1.code = s0.code → s1.memaddrs = s0.memaddrs → s1.be = s0.be →
      (∀ k, s1.locals k = (ps.zip vs).lookup k) → F s1.memory →
      SafeR o (fun s => s = s1) body (R s1.memory) fun _ => False)
    (hrt : Fresh rt l = true) {G : Value → (Word → Word) → Prop} (hG : ∀ m m' v, F m → R m v m' → G v m') :
    Frag o [.call rt f as] (RunF s0 l F) (fun u => ∃ v, RunF s0 ((rt, v) :: l) (G v) u) := by
  refine frag_call o has (body := body)
    (Pc := fun s s1 => s1 = { decClock s with locals := fun k => (ps.zip vs).lookup k })
    (Rc := fun s => R s.memory) (fun s h => ?_) (fun s h => ⟨vs, _, hargs s h,
      Block.lookupCode_of (by rw [h.1.code]; exact hcode) hnd hlen, rfl⟩) fun s t v h hr hsame => ?_
  · refine hbody _ ⟨by rw [← hA.base]; show s.baseAddr + _ = _; rw [h.1.base], hA.hA, fun x hx h8 => by
      show s.memaddrs _ = true; rw [h.1.memaddrs]; exact hA.dom x hx h8⟩ h.1.code h.1.memaddrs h.1.be (fun _ => rfl)
      h.2
  · exact ⟨v, ⟨⟨vals_cons h.1.vals hrt v, hsame.1.trans h.1.memaddrs, hsame.2.1.trans h.1.base,
      hsame.2.2.2.trans h.1.code, hsame.2.2.1.trans h.1.be⟩, hG _ _ v h.2 hr⟩⟩

/-! ### Each operation called -/

/-- **A call of `setClear`.** -/
theorem setClear_call (o : Oracle σ) {ofs : Nat} {A : Word} {s0 : PancakeState σ} (hA : Area ofs A s0) {rt : String}
    {l : List (String × Value)} {F : (Word → Word) → Prop} (hrt : Fresh rt l = true) {body : PancakeProg}
    (hb : Lower.lower (setClear .none ofs) = some body) (hcode : s0.code "setClear" = some (["d"], body))
    {e1 : Syntax.PExpr} {E1 : PancakeExp} (he1 : Lower.lowerExp e1 = some E1) {k : Nat} (hk : k < slots)
    (hv1 : ∀ u, RunF s0 l F u → eval u E1 = some (BitVec.ofNat 64 k)) {S : Nat → Bool}
    (hS : ∀ m, F m → SetAt m A k S) :
    Frag o [.call rt "setClear" [e1]] (RunF s0 l F)
      (fun u => ∃ v, RunF s0 ((rt, v) :: l) (fun m' => ∃ m, F m ∧ ClearRet A k m v m') u) :=
  setCall_frag o hA (ps := ["d"]) (args := [E1]) (vs := [BitVec.ofNat 64 k])
      (by decide) (by simp [Lower.lowerArgs, he1]) hcode rfl
    (fun u h => by simp only [evalArgs, hv1 u h]) (R := ClearRet A k)
    (fun s1 hA1 _ _ _ hloc hF => body_eq hb
        (setClear_ok o hA1 hk ((hloc "d").trans rfl) (hS _ hF))) hrt fun m m' v hF hr => ⟨m, hF, hr⟩

/-- **A call of `setEmpty`.** -/
theorem setEmpty_call (o : Oracle σ) {ofs : Nat} {A : Word} {s0 : PancakeState σ} (hA : Area ofs A s0) {rt : String}
    {l : List (String × Value)} {F : (Word → Word) → Prop} (hrt : Fresh rt l = true) {body : PancakeProg}
    (hb : Lower.lower (setEmpty .none ofs) = some body) (hcode : s0.code "setEmpty" = some (["s"], body))
    {e1 : Syntax.PExpr} {E1 : PancakeExp} (he1 : Lower.lowerExp e1 = some E1) {k : Nat} (hk : k < slots)
    (hv1 : ∀ u, RunF s0 l F u → eval u E1 = some (BitVec.ofNat 64 k)) {S : Nat → Bool}
    (hS : ∀ m, F m → SetAt m A k S) :
    Frag o [.call rt "setEmpty" [e1]] (RunF s0 l F)
      (fun u => ∃ v, RunF s0 ((rt, v) :: l) (fun m' => ∃ m, F m ∧ EmptyRet S m v m') u) :=
  setCall_frag o hA (ps := ["s"]) (args := [E1]) (vs := [BitVec.ofNat 64 k])
      (by decide) (by simp [Lower.lowerArgs, he1]) hcode rfl
    (fun u h => by simp only [evalArgs, hv1 u h]) (R := EmptyRet S)
    (fun s1 hA1 _ _ _ hloc hF => body_eq hb
        (setEmpty_ok o hA1 hk ((hloc "s").trans rfl) (hS _ hF))) hrt fun m m' v hF hr => ⟨m, hF, hr⟩

/-- **A call of `setHas`.** -/
theorem setHas_call (o : Oracle σ) {ofs : Nat} {A : Word} {s0 : PancakeState σ} (hA : Area ofs A s0) {rt : String}
    {l : List (String × Value)} {F : (Word → Word) → Prop} (hrt : Fresh rt l = true) {body : PancakeProg}
    (hb : Lower.lower (setHas .none ofs) = some body) (hcode : s0.code "setHas" = some (["s", "y"], body))
    {e1 e2 : Syntax.PExpr} {E1 E2 : PancakeExp} (he1 : Lower.lowerExp e1 = some E1)
    (he2 : Lower.lowerExp e2 = some E2) {k Y : Nat} (hk : k < slots) (hY : Y ≤ inputMax)
    (hv1 : ∀ u, RunF s0 l F u → eval u E1 = some (BitVec.ofNat 64 k))
    (hv2 : ∀ u, RunF s0 l F u → eval u E2 = some (BitVec.ofNat 64 Y)) {S : Nat → Bool}
    (hS : ∀ m, F m → SetAt m A k S ∧ Pows m A) :
    Frag o [.call rt "setHas" [e1, e2]] (RunF s0 l F)
      (fun u => ∃ v, RunF s0 ((rt, v) :: l) (fun m' => ∃ m, F m ∧ HasRet S Y m v m') u) :=
  setCall_frag o hA (ps := ["s", "y"]) (args := [E1, E2])
    (vs := [BitVec.ofNat 64 k, BitVec.ofNat 64 Y]) (by decide) (by simp [Lower.lowerArgs, he1, he2]) hcode rfl
    (fun u h => by simp only [evalArgs, hv1 u h, hv2 u h]) (R := HasRet S Y)
    (fun s1 hA1 _ _ _ hloc hF => body_eq hb
      (setHas_ok o hA1 hk hY ((hloc "s").trans rfl) ((hloc "y").trans rfl) (hS _ hF).1 (hS _ hF).2)) hrt
    fun m m' v hF hr => ⟨m, hF, hr⟩

/-- **A call of `setAdd`.** -/
theorem setAdd_call (o : Oracle σ) {ofs : Nat} {A : Word} {s0 : PancakeState σ} (hA : Area ofs A s0) {rt : String}
    {l : List (String × Value)} {F : (Word → Word) → Prop} (hrt : Fresh rt l = true) {body : PancakeProg}
    (hb : Lower.lower (setAdd .none ofs) = some body) (hcode : s0.code "setAdd" = some (["d", "y"], body))
    {e1 e2 : Syntax.PExpr} {E1 E2 : PancakeExp} (he1 : Lower.lowerExp e1 = some E1)
    (he2 : Lower.lowerExp e2 = some E2) {k : Nat} {Y : Word} (hk : k < slots)
    (hv1 : ∀ u, RunF s0 l F u → eval u E1 = some (BitVec.ofNat 64 k))
    (hv2 : ∀ u, RunF s0 l F u → eval u E2 = some Y) {S : Nat → Bool}
    (hS : ∀ m, F m → SetAt m A k S ∧ Pows m A) :
    Frag o [.call rt "setAdd" [e1, e2]] (RunF s0 l F)
      (fun u => ∃ v, RunF s0 ((rt, v) :: l) (fun m' => ∃ m, F m ∧ AddRet A k S Y m v m') u) :=
  setCall_frag o hA (ps := ["d", "y"]) (args := [E1, E2])
    (vs := [BitVec.ofNat 64 k, Y]) (by decide) (by simp [Lower.lowerArgs, he1, he2]) hcode rfl
    (fun u h => by simp only [evalArgs, hv1 u h, hv2 u h]) (R := AddRet A k S Y)
    (fun s1 hA1 _ _ _ hloc hF => body_eq hb
      (setAdd_ok o hA1 hk ((hloc "d").trans rfl) ((hloc "y").trans rfl) (hS _ hF).1 (hS _ hF).2)) hrt
    fun m m' v hF hr => ⟨m, hF, hr⟩

/-- **A call of `setUnion`.** -/
theorem setUnion_call (o : Oracle σ) {ofs : Nat} {A : Word} {s0 : PancakeState σ} (hA : Area ofs A s0) {rt : String}
    {l : List (String × Value)} {F : (Word → Word) → Prop} (hrt : Fresh rt l = true) {body : PancakeProg}
    (hb : Lower.lower (setUnion .none ofs) = some body) (hcode : s0.code "setUnion" = some (["d", "s"], body))
    {e1 e2 : Syntax.PExpr} {E1 E2 : PancakeExp} (he1 : Lower.lowerExp e1 = some E1)
    (he2 : Lower.lowerExp e2 = some E2) {kd ks : Nat} (h1 : kd < slots) (h2 : ks < slots)
    (hv1 : ∀ u, RunF s0 l F u → eval u E1 = some (BitVec.ofNat 64 kd))
    (hv2 : ∀ u, RunF s0 l F u → eval u E2 = some (BitVec.ofNat 64 ks)) {Sd Ss : Nat → Bool}
    (hS : ∀ m, F m → SetAt m A kd Sd ∧ SetAt m A ks Ss) :
    Frag o [.call rt "setUnion" [e1, e2]] (RunF s0 l F)
      (fun u => ∃ v, RunF s0 ((rt, v) :: l) (fun m' => ∃ m, F m ∧ UnionRet A kd Sd Ss m v m') u) :=
  setCall_frag o hA (ps := ["d", "s"]) (args := [E1, E2])
    (vs := [BitVec.ofNat 64 kd, BitVec.ofNat 64 ks]) (by decide) (by simp [Lower.lowerArgs, he1, he2]) hcode rfl
    (fun u h => by simp only [evalArgs, hv1 u h, hv2 u h]) (R := UnionRet A kd Sd Ss)
    (fun s1 hA1 _ _ _ hloc hF => body_eq hb
        (setUnion_ok o hA1 h1 h2 ((hloc "d").trans rfl) ((hloc "s").trans rfl) (hS _ hF).1
        (hS _ hF).2)) hrt fun m m' v hF hr => ⟨m, hF, hr⟩

/-- **A call of `setMinus`.** -/
theorem setMinus_call (o : Oracle σ) {ofs : Nat} {A : Word} {s0 : PancakeState σ} (hA : Area ofs A s0) {rt : String}
    {l : List (String × Value)} {F : (Word → Word) → Prop} (hrt : Fresh rt l = true) {body : PancakeProg}
    (hb : Lower.lower (setMinus .none ofs) = some body) (hcode : s0.code "setMinus" = some (["d", "s"], body))
    {e1 e2 : Syntax.PExpr} {E1 E2 : PancakeExp} (he1 : Lower.lowerExp e1 = some E1)
    (he2 : Lower.lowerExp e2 = some E2) {kd ks : Nat} (h1 : kd < slots) (h2 : ks < slots)
    (hv1 : ∀ u, RunF s0 l F u → eval u E1 = some (BitVec.ofNat 64 kd))
    (hv2 : ∀ u, RunF s0 l F u → eval u E2 = some (BitVec.ofNat 64 ks)) {Sd Ss : Nat → Bool}
    (hS : ∀ m, F m → SetAt m A kd Sd ∧ SetAt m A ks Ss) :
    Frag o [.call rt "setMinus" [e1, e2]] (RunF s0 l F)
      (fun u => ∃ v, RunF s0 ((rt, v) :: l) (fun m' => ∃ m, F m ∧ MinusRet A kd Sd Ss m v m') u) :=
  setCall_frag o hA (ps := ["d", "s"]) (args := [E1, E2])
    (vs := [BitVec.ofNat 64 kd, BitVec.ofNat 64 ks]) (by decide) (by simp [Lower.lowerArgs, he1, he2]) hcode rfl
    (fun u h => by simp only [evalArgs, hv1 u h, hv2 u h]) (R := MinusRet A kd Sd Ss)
    (fun s1 hA1 _ _ _ hloc hF => body_eq hb
        (setMinus_ok o hA1 h1 h2 ((hloc "d").trans rfl) ((hloc "s").trans rfl) (hS _ hF).1
        (hS _ hF).2)) hrt fun m m' v hF hr => ⟨m, hF, hr⟩

/-- **A call of `setCopy`.** -/
theorem setCopy_call (o : Oracle σ) {ofs : Nat} {A : Word} {s0 : PancakeState σ} (hA : Area ofs A s0) {rt : String}
    {l : List (String × Value)} {F : (Word → Word) → Prop} (hrt : Fresh rt l = true) {body : PancakeProg}
    (hb : Lower.lower (setCopy .none ofs) = some body) (hcode : s0.code "setCopy" = some (["d", "s"], body))
    {e1 e2 : Syntax.PExpr} {E1 E2 : PancakeExp} (he1 : Lower.lowerExp e1 = some E1)
    (he2 : Lower.lowerExp e2 = some E2) {kd ks : Nat} (h1 : kd < slots) (h2 : ks < slots) (hne : kd ≠ ks)
    (hv1 : ∀ u, RunF s0 l F u → eval u E1 = some (BitVec.ofNat 64 kd))
    (hv2 : ∀ u, RunF s0 l F u → eval u E2 = some (BitVec.ofNat 64 ks)) {Sd Ss : Nat → Bool}
    (hS : ∀ m, F m → SetAt m A kd Sd ∧ SetAt m A ks Ss) :
    Frag o [.call rt "setCopy" [e1, e2]] (RunF s0 l F)
      (fun u => ∃ v, RunF s0 ((rt, v) :: l) (fun m' => ∃ m, F m ∧ CopyRet A kd Ss m v m') u) :=
  setCall_frag o hA (ps := ["d", "s"]) (args := [E1, E2])
    (vs := [BitVec.ofNat 64 kd, BitVec.ofNat 64 ks]) (by decide) (by simp [Lower.lowerArgs, he1, he2]) hcode rfl
    (fun u h => by simp only [evalArgs, hv1 u h, hv2 u h]) (R := CopyRet A kd Ss)
    (fun s1 hA1 _ _ _ hloc hF => body_eq hb
        (setCopy_ok o hA1 h1 h2 hne ((hloc "d").trans rfl) ((hloc "s").trans rfl) (hS _ hF).1
        (hS _ hF).2)) hrt fun m m' v hF hr => ⟨m, hF, hr⟩

/-- **A call of `setVoid`.** -/
theorem setVoid_call (o : Oracle σ) {ofs : Nat} {A : Word} {s0 : PancakeState σ} (hA : Area ofs A s0) {rt : String}
    {l : List (String × Value)} {F : (Word → Word) → Prop} (hrt : Fresh rt l = true) {body : PancakeProg}
    (hb : Lower.lower (setVoid .none ofs) = some body) (hcode : s0.code "setVoid" = some (["s", "d"], body))
    {e1 e2 : Syntax.PExpr} {E1 E2 : PancakeExp} (he1 : Lower.lowerExp e1 = some E1)
    (he2 : Lower.lowerExp e2 = some E2) {ks kd : Nat} (h1 : ks < slots) (h2 : kd < slots)
    (hv1 : ∀ u, RunF s0 l F u → eval u E1 = some (BitVec.ofNat 64 ks))
    (hv2 : ∀ u, RunF s0 l F u → eval u E2 = some (BitVec.ofNat 64 kd)) {Ss Sd : Nat → Bool}
    (hS : ∀ m, F m → SetAt m A ks Ss ∧ SetAt m A kd Sd) :
    Frag o [.call rt "setVoid" [e1, e2]] (RunF s0 l F)
      (fun u => ∃ v, RunF s0 ((rt, v) :: l) (fun m' => ∃ m, F m ∧ VoidRet A kd Ss m v m') u) :=
  setCall_frag o hA (ps := ["s", "d"]) (args := [E1, E2])
    (vs := [BitVec.ofNat 64 ks, BitVec.ofNat 64 kd]) (by decide) (by simp [Lower.lowerArgs, he1, he2]) hcode rfl
    (fun u h => by simp only [evalArgs, hv1 u h, hv2 u h]) (R := VoidRet A kd Ss)
    (fun s1 hA1 _ _ _ hloc hF => body_eq hb
        (setVoid_ok o hA1 h1 h2 ((hloc "s").trans rfl) ((hloc "d").trans rfl) (hS _ hF).1
        (hS _ hF).2)) hrt fun m m' v hF hr => ⟨m, hF, hr⟩

/-! ## A round's new positions -/

/-- What `setGrow` gives back: zero, slot `kx` without the positions of slot `kd`, slot `kd` given them, every
other word as in `m0`. -/
def GrowRet (A : Word) (kx kd : Nat) (Sx Sd : Nat → Bool) (m0 : Word → Word) : Ret := fun v m =>
  v = 0 ∧ SetAt m A kx (fun z => Sx z && !Sd z) ∧ SetAt m A kd (fun z => Sd z || (Sx z && !Sd z)) ∧
    ∀ a, ¬InSlot A kx a → ¬InSlot A kd a → m a = m0 a

/-- **`setGrow` keeps a round's new positions and adds them to those counted.** -/
theorem setGrow_ok (o : Oracle σ) {ofs : Nat} {A : Word} {s1 : PancakeState σ} (hA : Area ofs A s1) {kx kd : Nat}
    (hkx : kx < slots) (hkd : kd < slots) (hne : kx ≠ kd) (hx : s1.locals "x" = some (BitVec.ofNat 64 kx))
    (hd : s1.locals "d" = some (BitVec.ofNat 64 kd)) {Sx Sd : Nat → Bool} (hSx : SetAt s1.memory A kx Sx)
    (hSd : SetAt s1.memory A kd Sd) {bm bu : PancakeProg} (hbm : Lower.lower (setMinus .none ofs) = some bm)
    (hcm : s1.code "setMinus" = some (["d", "s"], bm)) (hbu : Lower.lower (setUnion .none ofs) = some bu)
    (hcu : s1.code "setUnion" = some (["d", "s"], bu)) :
    ∃ body, Lower.lower setGrow = some body ∧
      SafeR o (fun s => s = s1) body (GrowRet A kx kd Sx Sd s1.memory) fun _ => False := by
  let m0 := s1.memory
  let l : List (String × Value) := [("x", BitVec.ofNat 64 kx), ("d", BitVec.ofNat 64 kd)]
  refine body_of ?_
  show FragR o _ ([_] ++ [_] ++ [_]) _ _
  have hm := setMinus_call o hA (rt := "c") (l := l) (F := (· = m0)) rfl hbm hcm (e1 := Syntax.v "x")
    (e2 := Syntax.v "d") rfl rfl hkx hkd (fun u h => vals_lookup h.1.vals rfl) (fun u h => vals_lookup h.1.vals rfl)
    (Sd := Sx) (Ss := Sd) fun m e => by subst e; exact ⟨hSx, hSd⟩
  let Gu (v v' : Value) : (Word → Word) → Prop := fun m'' =>
    ∃ m', (∃ m, m = m0 ∧ MinusRet A kx Sx Sd m v m') ∧ UnionRet A kd Sd (fun z => Sx z && !Sd z) m' v' m''
  let Q : Assn σ := fun u => ∃ v v', RunF s1 (("u", v') :: ("c", v) :: l) (Gu v v') u
  have hu : Frag o [.call "u" "setUnion" [Syntax.v "d", Syntax.v "x"]]
      (fun u => ∃ v, RunF s1 (("c", v) :: l) (fun m' => ∃ m, m = m0 ∧ MinusRet A kx Sx Sd m v m') u) Q :=
    frag_exists (lowKK_call rfl) fun v => frag_conseq (setUnion_call o hA (rt := "u") (l := ("c", v) :: l)
      (F := fun m' => ∃ m, m = m0 ∧ MinusRet A kx Sx Sd m v m') rfl hbu hcu
      (e1 := Syntax.v "d") (e2 := Syntax.v "x") rfl rfl hkd hkx (fun u h => vals_lookup h.1.vals rfl)
      (fun u h => vals_lookup h.1.vals rfl) (Sd := Sd) (Ss := fun z => Sx z && !Sd z)
      fun m' ⟨m, e, hr⟩ => ⟨setAt_other (e ▸ hSd) hkx hkd hne hr.2.2, hr.2.1⟩) (fun u h => h)
      fun u ⟨v', h⟩ => ⟨v, v', h⟩
  refine fragR_conseq (P0 := RunF s1 l (· = m0)) (fragR_append (fragR_append (fragR_of hm) (fragR_of hu))
    (fragR_ret o rfl fun u (h : Q u) => ?_))
    (entry_two hx hd) fun _ h => h
  obtain ⟨v, v', h⟩ := h
  obtain ⟨m', ⟨m, e, hr1⟩, hr2⟩ := h.2
  subst e
  refine ⟨_, rfl, rfl, setAt_other hr1.2.1 hkd hkx (Ne.symm hne) hr2.2.2, hr2.2.1, fun a h1 h2 => ?_⟩
  rw [hr2.2.2 a h2, hr1.2.2 a h1]

/-- **A call of `setGrow`.** -/
theorem setGrow_call (o : Oracle σ) {ofs : Nat} {A : Word} {s0 : PancakeState σ} (hA : Area ofs A s0) {rt : String}
    {l : List (String × Value)} {F : (Word → Word) → Prop} (hrt : Fresh rt l = true) {body bm bu : PancakeProg}
    (hb : Lower.lower setGrow = some body) (hcode : s0.code "setGrow" = some (["x", "d"], body))
    (hbm : Lower.lower (setMinus .none ofs) = some bm) (hcm : s0.code "setMinus" = some (["d", "s"], bm))
    (hbu : Lower.lower (setUnion .none ofs) = some bu) (hcu : s0.code "setUnion" = some (["d", "s"], bu))
    {e1 e2 : Syntax.PExpr} {E1 E2 : PancakeExp} (he1 : Lower.lowerExp e1 = some E1)
    (he2 : Lower.lowerExp e2 = some E2) {kx kd : Nat} (hkx : kx < slots) (hkd : kd < slots) (hne : kx ≠ kd)
    (hv1 : ∀ u, RunF s0 l F u → eval u E1 = some (BitVec.ofNat 64 kx))
    (hv2 : ∀ u, RunF s0 l F u → eval u E2 = some (BitVec.ofNat 64 kd)) {Sx Sd : Nat → Bool}
    (hS : ∀ m, F m → SetAt m A kx Sx ∧ SetAt m A kd Sd) :
    Frag o [.call rt "setGrow" [e1, e2]] (RunF s0 l F)
      (fun u => ∃ v, RunF s0 ((rt, v) :: l) (fun m' => ∃ m, F m ∧ GrowRet A kx kd Sx Sd m v m') u) :=
  setCall_frag o hA (ps := ["x", "d"]) (args := [E1, E2]) (vs := [BitVec.ofNat 64 kx, BitVec.ofNat 64 kd])
    (by decide) (by simp [Lower.lowerArgs, he1, he2]) hcode rfl
    (fun u h => by simp only [evalArgs, hv1 u h, hv2 u h]) (R := GrowRet A kx kd Sx Sd)
    (fun s1 hA1 hc _ _ hloc hF => body_eq hb
        (setGrow_ok o hA1 hkx hkd hne ((hloc "x").trans rfl) ((hloc "d").trans rfl) (hS _ hF).1 (hS _ hF).2 hbm
        (by rw [hc]; exact hcm) hbu (by rw [hc]; exact hcu))) hrt fun m m' v hF hr => ⟨m, hF, hr⟩

/-! ## The premises can hold -/

theorem area_witness : Area (σ := Unit) 0 0 (bareState ()) := ⟨rfl, rfl, fun _ _ _ => rfl⟩

/-- An empty set in slot 0: its window `[1, 0]`, its bits clear. -/
def emptyMem : Word → Word := fun a => if a = slotW 0 0 0 then 1 else 0

theorem setAt_witness : SetAt emptyMem 0 0 (fun _ => false) := by
  have h2 := slots_two
  have h0 : emptyMem (slotW 0 0 0) = 1 := if_pos rfl
  have h1 : emptyMem (slotW 0 0 1) = 0 := if_neg (slotW_ne (by omega) (by decide) (by decide) (by decide))
  refine ⟨by rw [h0]; decide, by rw [h1]; decide, fun w hw j _ => ?_, fun _ h => by simp at h,
    fun _ h => by simp at h, fun h => by rw [h0, h1] at h; simp at h⟩
  rw [setWords_eq] at hw
  rw [show emptyMem (slotW 0 0 (2 + w)) = 0 from
    if_neg (slotW_ne (by omega) (by rw [setSize_eq]; omega) (by decide) (by omega))]
  simp

theorem run_witness : Run (σ := Unit) (bareState ()) [] (bareState ()) :=
  ⟨(fun _ h => nomatch h), rfl, rfl, rfl, rfl⟩

theorem runF_witness : RunF (σ := Unit) (bareState ()) [] (fun _ => True) (bareState ()) := ⟨run_witness, trivial⟩

theorem frame_witness : Frame 0 0 emptyMem emptyMem := fun _ _ => rfl

/-- One position, 0, in slot 0: its window `[0, 0]`. -/
def oneMem : Word → Word := fun a =>
  if a = slotW 0 0 0 then 0 else if a = slotW 0 0 1 then 0 else if a = slotW 0 0 2 then 1 else 0

theorem setAt_one_witness : SetAt oneMem 0 0 (fun x => x == 0) := by
  have h2 := slots_two
  have ne : ∀ {i i' : Nat}, i < 1028 → i' < 1028 → i ≠ i' → slotW 0 0 i ≠ slotW 0 0 i' := fun hi hi' h =>
    slotW_ne (by omega) (by rw [setSize_eq]; omega) (by rw [setSize_eq]; omega) h
  have e0 : oneMem (slotW 0 0 0) = 0 := if_pos rfl
  have e1 : oneMem (slotW 0 0 1) = 0 := by
    unfold oneMem; rw [if_neg (ne (by decide) (by decide) (by decide)), if_pos rfl]
  refine ⟨by rw [e0]; decide, by rw [e1]; decide, fun w hw j hj => ?_, fun x hx => ?_, fun x hx => ?_,
    fun _ => ⟨0, rfl⟩⟩
  · rw [setWords_eq] at hw
    by_cases hw0 : w = 0
    · subst hw0
      have : oneMem (slotW 0 0 (2 + 0)) = 1 := by
        unfold oneMem
        rw [if_neg (ne (by decide) (by decide) (by decide)), if_neg (ne (by decide) (by decide) (by decide)),
          if_pos rfl]
      rw [this]
      by_cases hj0 : j = 0
      · subst hj0; rfl
      · have : (1 : Word).getLsbD j = false := by simp [BitVec.getLsbD_one, hj0]
        rw [this]; simp; omega
    · have : oneMem (slotW 0 0 (2 + w)) = 0 := by
        unfold oneMem
        rw [if_neg (ne (by omega) (by decide) (by omega)), if_neg (ne (by omega) (by decide) (by omega)),
          if_neg (ne (by omega) (by decide) (by omega))]
      rw [this]; simp; omega
  · simp at hx; subst hx; rw [setWords_eq]; omega
  · simp at hx; subst hx; rw [e0, e1]; decide

/-- `setClear_ok`'s premises at once, on a state with an empty slot 0. -/
def clearState : PancakeState Unit :=
  { bareState () with memory := emptyMem, locals := fun x => if x = "d" then some (BitVec.ofNat 64 0) else none }

theorem setClear_witness : ∃ body, Lower.lower (setClear .none 0) = some body ∧
    SafeR Oracle.idle (fun s => s = clearState) body (ClearRet 0 0 clearState.memory) fun _ => False :=
  setClear_ok Oracle.idle (ofs := 0) (A := 0) ⟨rfl, rfl, fun _ _ _ => rfl⟩ (by have := slots_two; omega) rfl
    setAt_witness

theorem pows_witness : Pows (fun a => BitVec.twoPow 64 ((a.toNat - aPow) / 8)) 0 := fun j hj => by
  have : (at_ 0 (aPow + 8 * j)).toNat = aPow + 8 * j := by
    have := aPow_eq
    rw [at_, BitVec.toNat_add, BitVec.toNat_ofNat]
    show (0 + (aPow + 8 * j) % 2 ^ 64) % 2 ^ 64 = aPow + 8 * j
    omega
  simp only [this]
  congr 1; omega

theorem at0_toNat {x : Nat} (hx : x < 2 ^ 64) : (at_ 0 x).toNat = x := by
  rw [at_, BitVec.toNat_add, BitVec.toNat_ofNat]
  show (0 + x % 2 ^ 64) % 2 ^ 64 = x
  omega

/-- The powers of two from `aPow`, past them nothing (a power past 63 is 0), slot 0 empty. -/
def powMem : Word → Word := fun a => if a = slotW 0 0 0 then 1 else BitVec.twoPow 64 ((a.toNat - aPow) / 8)

theorem twoPow_big {j : Nat} (h : 64 ≤ j) : BitVec.twoPow 64 j = 0 := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_twoPow, Nat.mod_eq_zero_of_dvd (Nat.pow_dvd_pow 2 h)]; rfl

/-- A memory where a slot holds a set and the powers of two are there, as `setHas_ok` and `setAdd_ok` assume. -/
theorem setAt_pows_witness : SetAt powMem 0 0 (fun _ => false) ∧ Pows powMem 0 := by
  have h2 := slots_two
  have hp := pow_lt
  refine ⟨setAt_frame setAt_witness fun i hi => ?_, fun j hj => ?_⟩
  · unfold powMem emptyMem
    by_cases h0 : i = 0
    · subst h0; rw [if_pos rfl, if_pos rfl]
    · have hne := slotW_ne (A := 0) (k := 0) (by omega) hi (by decide) h0
      have := off_small (k := 0) (by omega) (8 * i) (by rw [setSize_eq] at hi ⊢; omega)
      have ht : (slotW 0 0 i).toNat = off 0 + 8 * i := by rw [slotW, at0_toNat (by omega)]
      rw [if_neg hne, if_neg hne, ht, twoPow_big (by have := aSets_le_off 0; omega)]
  · have hne : at_ 0 (aPow + 8 * j) ≠ slotW 0 0 0 := fun e => by
      rw [slotW] at e
      have := at_inj (by have := aSets_le; omega)
        (by have := off_small (k := 0) (by omega) 0 (by decide); omega) e
      have := aSets_le_off 0; omega
    unfold powMem
    rw [if_neg hne, at0_toNat (by have := aSets_le; omega), show (aPow + 8 * j - aPow) / 8 = j by omega]

theorem winIs_witness : WinIs 0 0 (fun _ => 0) 0 0 (fun _ => 0) := ⟨fun _ _ _ => rfl, rfl, rfl⟩

theorem worded_witness : Worded (fun _ _ => 0) 0 0 0 0 0 emptyMem emptyMem :=
  ⟨fun _ _ h => absurd h (by omega), fun _ _ => rfl⟩


end DN.News.AbnfSets
