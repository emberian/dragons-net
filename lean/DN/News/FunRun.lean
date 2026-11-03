-- SPDX-License-Identifier: AGPL-3.0-or-later
import DN.News.ScanArea
import DN.News.FramerCode
import DN.Compiler.FragRet

/-!
# DN.News.FunRun

What proofs of a program's functions keep of a run: the locals so far and what the memory is (`Run`, `RunF`), a
function's entry with its parameters (`entry_one`, `entry_two`) and its body closed (`body_of`), a word stored
(`upd`), where a scan stops (`seek`, `seekDown`), and a word's bits.
-/

namespace DN.News.FunRun

open DN.Compiler DN.Compiler.Wp DN.Compiler.WpRet DN.Compiler.Frag
open DN.News.ScanRun (at_ at_add at_ne at_inj Vals vals_lookup vals_cons vals_set Fresh without lookup_head)
open DN.News.FramerCode (bw ev_var)

variable {σ : Type}

/-- A state of a set function's body: the locals `l`, the addresses and the base as at the entry `s0`. -/
structure Run (s0 : PancakeState σ) (l : List (String × Value)) (u : PancakeState σ) : Prop where
  vals : Vals u l
  memaddrs : u.memaddrs = s0.memaddrs
  base : u.baseAddr = s0.baseAddr
  code : u.code = s0.code
  be : u.be = s0.be

/-- …and memory as `F` says. -/
def RunF (s0 : PancakeState σ) (l : List (String × Value)) (F : (Word → Word) → Prop) (u : PancakeState σ) :
    Prop :=
  Run s0 l u ∧ F u.memory

theorem runF_clock (s0 : PancakeState σ) (l : List (String × Value)) (F : (Word → Word) → Prop) :
    Safe.ClockFree (RunF s0 l F) := fun _ _ h => ⟨⟨h.1.vals, h.1.memaddrs, h.1.base, h.1.code, h.1.be⟩, h.2⟩

theorem runF_mono {s0 u : PancakeState σ} {l l' : List (String × Value)} {F F' : (Word → Word) → Prop}
    (h : RunF s0 l F u) (hl : ∀ q ∈ l', q ∈ l) (hF : ∀ m, F m → F' m) : RunF s0 l' F' u :=
  ⟨⟨fun q hq => h.1.vals q (hl q hq), h.1.memaddrs, h.1.base, h.1.code, h.1.be⟩, hF _ h.2⟩

/-- A state alike but for the clock to one of `RunF` is one, with that state's memory. -/
theorem runF_like {s0 s u : PancakeState σ} {l : List (String × Value)} {F : (Word → Word) → Prop}
    (hs : RunF s0 l F s) (hu : Like s u) : RunF s0 l (· = s.memory) u :=
  ⟨⟨fun q hq => by rw [hu.locals]; exact hs.1.vals q hq, by rw [hu.memaddrs]; exact hs.1.memaddrs,
    by rw [hu.base]; exact hs.1.base, by rw [hu.code]; exact hs.1.code, by rw [hu.be]; exact hs.1.be⟩, hu.memory⟩

/-- A word stored. -/
def upd (m : Word → Word) (a v : Word) : Word → Word := fun k => if k = a then v else m k

/-- **A declaration**, its value the same from every state. -/
theorem runF_dec (o : Oracle σ) {s0 : PancakeState σ} {l : List (String × Value)} {F : (Word → Word) → Prop}
    {x : String} {e : Syntax.PExpr} {E : PancakeExp} (he : Lower.lowerExp e = some E) (hx : Fresh x l = true)
    {v : Value} (hv : ∀ u, RunF s0 l F u → eval u E = some v) :
    Frag o [.dec x e] (RunF s0 l F) (RunF s0 ((x, v) :: l) F) :=
  frag_dec o he fun u h => ⟨v, hv u h, ⟨vals_cons h.1.vals hx v, h.1.memaddrs, h.1.base, h.1.code, h.1.be⟩, h.2⟩

/-- **An assignment**, its value the same from every state. -/
theorem runF_set (o : Oracle σ) {s0 : PancakeState σ} {l : List (String × Value)} {F : (Word → Word) → Prop}
    {x : String} {e : Syntax.PExpr} {E : PancakeExp} (he : Lower.lowerExp e = some E) {w : Value}
    (hl : l.lookup x = some w) {v : Value} (hv : ∀ u, RunF s0 l F u → eval u E = some v) :
    Frag o [.assign x e] (RunF s0 l F) (RunF s0 ((x, v) :: without x l) F) :=
  set_frag o he (runF_clock _ _ _) fun u h =>
    ⟨v, hv u h, ⟨w, vals_lookup h.1.vals hl⟩, ⟨vals_set h.1.vals x v, h.1.memaddrs, h.1.base, h.1.code, h.1.be⟩, h.2⟩

theorem ofNat_toNat (w : Word) : BitVec.ofNat 64 w.toNat = w := by simp

theorem upd_eq (m : Word → Word) (a v : Word) : upd m a v a = v := if_pos rfl

theorem upd_ne {m : Word → Word} {a b : Word} (v : Word) (h : b ≠ a) : upd m a v b = m b := if_neg h

theorem mem_without {x : String} {l : List (String × Value)} {q : String × Value} (hq : q ∈ l) (hne : q.1 ≠ x) :
    q ∈ without x l := List.mem_filter.2 ⟨hq, by simpa using hne⟩

/-- A function's entry as a call makes it: the locals its parameters. -/
theorem entry_run {s1 : PancakeState σ} {l : List (String × Value)} (hl : Vals s1 l) {F : (Word → Word) → Prop}
    (hF : F s1.memory) : ∀ s, s = s1 → RunF s1 l F s := fun s e => by subst e; exact ⟨⟨hl, rfl, rfl, rfl, rfl⟩, hF⟩

/-- An entry with one parameter. -/
theorem entry_one {s1 : PancakeState σ} {x : String} {vx : Value} (hx : s1.locals x = some vx) :
    ∀ s, s = s1 → RunF s1 [(x, vx)] (· = s1.memory) s :=
  entry_run (fun q hq => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hq; subst hq; exact hx) rfl

/-- An entry with two parameters. -/
theorem entry_two {s1 : PancakeState σ} {x y : String} {vx vy : Value} (hx : s1.locals x = some vx)
    (hy : s1.locals y = some vy) : ∀ s, s = s1 → RunF s1 [(x, vx), (y, vy)] (· = s1.memory) s :=
  entry_run (fun q hq => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact hx
    · exact hy) rfl

/-- A body closed: the function lowers to it, and runs as it does. -/
theorem body_of {o : Oracle σ} {R : Ret} {f : Syntax.PFun} {P : Assn σ} (h : FragR o R f.body P fun _ => False) :
    ∃ body, Lower.lower f = some body ∧ SafeR o P body R fun _ => False :=
  fragR_close h fun _ _ _ h _ => h

theorem ev_and {u : PancakeState σ} {a b : PancakeExp} {x y : Word} (ha : eval u a = some x)
    (hb : eval u b = some y) : eval u (.op .and_ a b) = some (x &&& y) := by simp only [eval, ha, hb]

theorem ev_xor {u : PancakeState σ} {a b : PancakeExp} {x y : Word} (ha : eval u a = some x)
    (hb : eval u b = some y) : eval u (.op .xor a b) = some (x ^^^ y) := by simp only [eval, ha, hb]

/-- A word's bit `j` tested as `setHas` does: the word and the power of two, twice compared with zero. -/
theorem bit_test (W : Word) {j : Nat} (hj : j < 64) :
    (if (if W &&& BitVec.twoPow 64 j = 0 then (1 : Word) else 0) = 0 then (1 : Word) else 0) = bw (W.getLsbD j) := by
  rw [BitVec.and_twoPow]
  cases W.getLsbD j
  · simp [bw]
  · have : BitVec.twoPow 64 j ≠ 0 := by
      intro e
      have := congrArg (fun x => x.getLsbD j) e
      simp [hj] at this
    rw [if_pos rfl, if_neg this, if_pos rfl]; rfl

/-- A word past `hi` as an unsigned number is below zero or past `hi` as a signed one. -/
theorem slt_out {w : Word} {hi : Nat} (hhi : hi < 2 ^ 63) (hw : hi < w.toNat) :
    (signedLt w 0 || signedLt (BitVec.ofNat 64 hi) w) = true := by
  simp only [signedLt, BitVec.slt, BitVec.toInt_eq_toNat_cond, BitVec.toNat_ofNat, Bool.or_eq_true, decide_eq_true_eq]
  have e1 : hi % 2 ^ 64 = hi := Nat.mod_eq_of_lt (by omega)
  have e0 : (0 : BitVec 64).toNat = 0 := rfl
  rw [e1, e0]
  split <;> split <;> split <;> omega

/-- Bit `j` of a word with the power of two `i` set. -/
theorem getLsbD_or_twoPow (W : Word) {i j : Nat} (hi : i < 64) :
    (W ||| BitVec.twoPow 64 i).getLsbD j = (W.getLsbD j || j == i) := by
  rw [BitVec.getLsbD_or, BitVec.getLsbD_twoPow]
  by_cases h : j = i
  · subst h; simp [hi]
  · simp [h, Ne.symm h]

theorem runF_restore {s0 u : PancakeState σ} {l : List (String × Value)} {F : (Word → Word) → Prop}
    (h : RunF s0 l F u) {y : String} (hy : Fresh y l = true) (v : Option Value) : RunF s0 l F (restore u y v) :=
  ⟨⟨fun q hq => by
    show (if q.1 = y then v else u.locals q.1) = some q.2
    rw [if_neg (ScanRun.fresh_ne hy q hq)]; exact h.1.vals q hq, h.1.memaddrs, h.1.base, h.1.code, h.1.be⟩, h.2⟩

/-- The first place from `k` on where `p` holds, at most `n` places on. -/
def seek (p : Nat → Bool) : Nat → Nat → Nat
  | 0, k => k
  | n + 1, k => if p k then k else seek p n (k + 1)

theorem seek_ge (p : Nat → Bool) : ∀ n k, k ≤ seek p n k
  | 0, _ => Nat.le_refl _
  | n + 1, k => by
    simp only [seek]; split
    · exact Nat.le_refl _
    · exact Nat.le_trans (Nat.le_succ k) (seek_ge p n (k + 1))

theorem seek_le (p : Nat → Bool) : ∀ n k, seek p n k ≤ k + n
  | 0, _ => Nat.le_refl _
  | n + 1, k => by
    simp only [seek]; split
    · omega
    · have := seek_le p n (k + 1); omega

theorem seek_before (p : Nat → Bool) : ∀ n k w, k ≤ w → w < seek p n k → p w = false
  | 0, _, _, h1, h2 => absurd h2 (by simp only [seek]; omega)
  | n + 1, k, w, h1, h2 => by
    simp only [seek] at h2; split at h2
    · omega
    · rename_i hk
      by_cases e : w = k
      · subst e; simpa using hk
      · exact seek_before p n (k + 1) w (by omega) h2

theorem seek_stop (p : Nat → Bool) : ∀ n k, p (k + n) = true → p (seek p n k) = true
  | 0, _, h => h
  | n + 1, k, h => by
    simp only [seek]; split
    · assumption
    · exact seek_stop p n (k + 1) (by rw [show k + 1 + n = k + (n + 1) by omega]; exact h)

/-- The last place from `k` down where `p` holds, at most `n` places down. -/
def seekDown (p : Nat → Bool) : Nat → Nat → Nat
  | 0, k => k
  | n + 1, k => if p k then k else seekDown p n (k - 1)

theorem seekDown_le (p : Nat → Bool) : ∀ n k, seekDown p n k ≤ k
  | 0, _ => Nat.le_refl _
  | n + 1, k => by
    simp only [seekDown]; split
    · exact Nat.le_refl _
    · have := seekDown_le p n (k - 1); omega

theorem seekDown_ge (p : Nat → Bool) : ∀ n k, n ≤ k → k - n ≤ seekDown p n k
  | 0, _, _ => by simp [seekDown]
  | n + 1, k, h => by
    simp only [seekDown]; split
    · omega
    · have := seekDown_ge p n (k - 1) (by omega); omega

theorem seekDown_after (p : Nat → Bool) : ∀ n k w, seekDown p n k < w → w ≤ k → p w = false
  | 0, _, _, h1, h2 => absurd h1 (by simp only [seekDown]; omega)
  | n + 1, k, w, h1, h2 => by
    simp only [seekDown] at h1; split at h1
    · omega
    · rename_i hk
      by_cases e : w = k
      · subst e; simpa using hk
      · exact seekDown_after p n (k - 1) w h1 (by omega)

theorem seekDown_stop (p : Nat → Bool) : ∀ n k, n ≤ k → p (k - n) = true → p (seekDown p n k) = true
  | 0, k, _, h => by simpa [seekDown] using h
  | n + 1, k, hn, h => by
    simp only [seekDown]; split
    · assumption
    · exact seekDown_stop p n (k - 1) (by omega) (by rw [show k - 1 - n = k - (n + 1) by omega]; exact h)

theorem word_ne0 {W : Word} {j : Nat} (h : W.getLsbD j = true) : W ≠ 0 := fun e => by
  rw [e] at h; simp at h

theorem exists_bit {W : Word} (h : W ≠ 0) : ∃ j, j < 64 ∧ W.getLsbD j = true := by
  apply Classical.byContradiction
  intro hn
  apply h
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  have : ¬(W.getLsbD j = true) := fun e => hn ⟨j, hj, e⟩
  simpa using this

theorem ofNat_sub_one {y : Nat} (h1 : 1 ≤ y) (h2 : y < 2 ^ 64) :
    BitVec.ofNat 64 y - BitVec.ofNat 64 1 = BitVec.ofNat 64 (y - 1) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  omega

/-- The body a function lowers to, as an `_ok` theorem gives it. -/
theorem body_eq {f : Syntax.PFun} {body : PancakeProg} (hb : Lower.lower f = some body) {S : PancakeProg → Prop}
    (h : ∃ b, Lower.lower f = some b ∧ S b) : S body := by
  obtain ⟨b, hb', hs⟩ := h
  rw [hb] at hb'; cases hb'; exact hs

end DN.News.FunRun
