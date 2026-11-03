-- SPDX-License-Identifier: AGPL-3.0-or-later
import DN.Server.SessionFrame
import DN.Compiler.Preservation
import DN.News.CharsRun

/-!
# DN.Server.SessionCheck

The session's checks of a command's words, proven against `DN.News.CommandSpec`: numbers, message-ids, ranges, dates,
wildmats and group names. Each leaves its verdict in `ok`, changing no other local nor memory; `groupName` returns it in
the return word. Premises: the words in the line's octets, their places read from no written local.
-/

namespace DN.Server.SessionCheck

open DN.Compiler DN.Compiler.Wp DN.Compiler.WpRet DN.Compiler.Preservation DN.Server DN.Server.SessionLayout
  DN.News DN.News.FrameSpec DN.News.CharsRun
open DN.News.FramerCode (bw leE or2E bw_and le_eval eq_word eval_lt eval_le eval_eq eval_and eval_or2)

variable {σ : Type}

/-! ## What a check leaves alone -/

/-- `t` is `s0` but for the locals `xs`, as far as an expression can tell, the clock aside. -/
structure ButFor (xs : List String) (s0 t : PancakeState σ) : Prop where
  locals : ∀ x, x ∉ xs → t.locals x = s0.locals x
  memory : t.memory = s0.memory
  memaddrs : t.memaddrs = s0.memaddrs
  be : t.be = s0.be
  base : t.baseAddr = s0.baseAddr
  ffi : t.ffi = s0.ffi
  code : t.code = s0.code

/-- …so its octets read as they did. -/
theorem ButFor.load {xs : List String} {s0 t : PancakeState σ} (h : ButFor xs s0 t) (a : Word) :
    memLoadByte t.memory t.memaddrs t.be a = memLoadByte s0.memory s0.memaddrs s0.be a := by
  rw [h.memory, h.memaddrs, h.be]

theorem but_refl (xs : List String) (s : PancakeState σ) : ButFor xs s s :=
  ⟨fun _ _ => rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem but_set {xs : List String} {s0 t : PancakeState σ} (h : ButFor xs s0 t) {x : String}
    (hx : x ∈ xs) (w : Value) : ButFor xs s0 { t with locals := setLocal t.locals x w } :=
  ⟨fun y hy => by simp [setLocal, show y ≠ x from fun e => hy (e ▸ hx), h.locals y hy], h.memory,
    h.memaddrs, h.be, h.base, h.ffi, h.code⟩

theorem but_clock {xs : List String} {s0 t : PancakeState σ} (h : ButFor xs s0 t) (k : Nat) :
    ButFor xs s0 { t with clock := k } := ⟨h.locals, h.memory, h.memaddrs, h.be, h.base, h.ffi, h.code⟩

/-- A check's post, its frame and what it says of the locals, does not see the clock. -/
theorem but_clockFree {xs : List String} {s0 : PancakeState σ} {F : PancakeState σ → Prop}
    (hF : ∀ t k, F { t with clock := k } = F t := by intros; rfl) :
    Safe.ClockFree (fun t => ButFor xs s0 t ∧ F t) :=
  fun t k ⟨hf, h⟩ => ⟨but_clock hf k, by rw [hF]; exact h⟩

theorem but_restore {xs : List String} {s0 t : PancakeState σ} (h : ButFor xs s0 t) {x : String}
    (hx : x ∈ xs) (old : Option Value) : ButFor xs s0 (restore t x old) :=
  ⟨fun y hy => by
    have hyx : y ≠ x := fun e => hy (e ▸ hx)
    simp only [restore, resVar, if_neg hyx]
    exact h.locals y hy, h.memory, h.memaddrs, h.be, h.base, h.ffi, h.code⟩

theorem but_trans {xs : List String} {s0 t u : PancakeState σ} (h1 : ButFor xs s0 t) (h2 : ButFor xs t u) :
    ButFor xs s0 u :=
  ⟨fun y hy => (h2.locals y hy).trans (h1.locals y hy), h2.memory.trans h1.memory,
    h2.memaddrs.trans h1.memaddrs, h2.be.trans h1.be, h2.base.trans h1.base, h2.ffi.trans h1.ffi,
    h2.code.trans h1.code⟩

theorem but_mono {xs ys : List String} {s0 t : PancakeState σ} (h : ButFor xs s0 t)
    (hxy : ∀ y, y ∈ xs → y ∈ ys) : ButFor ys s0 t :=
  ⟨fun y hy => h.locals y fun hx => hy (hxy y hx), h.memory, h.memaddrs, h.be, h.base, h.ffi, h.code⟩

/-- An expression reading none of `xs` evaluates alike in the frame. -/
theorem eval_but {xs : List String} {s0 t : PancakeState σ} (h : ButFor xs s0 t) {e : PancakeExp}
    (he : ExpAvoids (· ∈ xs) e) {v : Value} (hv : eval s0 e = some v) : eval t e = some v := by
  have ha : Agree (· ∈ xs) s0 { t with clock := s0.clock } :=
    ⟨fun x hx => h.locals x hx, fun a ha => by simp [h.memaddrs, ha], fun a _ => by simp [h.memory],
      h.be, rfl, h.ffi, h.base, h.code⟩
  have := eval_agree' ha he hv
  rwa [Safe.eval_clock] at this

/-! ## Rules -/

/-- **A check, then what follows**: a check shown from each state it starts in. What follows is shown from the states it
leaves. -/
theorem then_ {o : Oracle σ} {P P' Q : PancakeState σ → Prop} {c k : PancakeProg}
    {M : PancakeState σ → PancakeState σ → Prop}
    (hc : ∀ s0, Safe.Safe o (fun s => s = s0 ∧ P s) c (M s0)) (hM : ∀ s0, Safe.ClockFree (M s0))
    (hnext : ∀ s0 t, P s0 → M s0 t → P' t) (hk : Safe.Safe o P' k Q) :
    Safe.Safe o P (.seq c k) Q := fun s0 hs0 =>
  Safe.seq (hc s0) (Safe.conseq hk (fun t ht => hnext s0 t hs0 ht) (fun _ h => h)) (hM s0) s0 ⟨rfl, hs0⟩

/-- Programs that run alike are safe alike. -/
theorem safe_congr {o : Oracle σ} {P Q : PancakeState σ → Prop} {c c' : PancakeProg}
    (h : ∀ s, PancakeSem o c s = PancakeSem o c' s) (hc : Safe.Safe o P c' Q) : Safe.Safe o P c Q :=
  fun s hs => (h s) ▸ hc s hs

theorem avoids_mono {p q : String → Prop} (hpq : ∀ x, q x → p x) : ∀ e, ExpAvoids p e → ExpAvoids q e
  | .var _, h => fun hq => h (hpq _ hq)
  | .op _ l r, h | .mul l r, h | .cmp _ l r, h | .shiftR l r, h | .shiftL l r, h =>
    ⟨avoids_mono hpq l h.1, avoids_mono hpq r h.2⟩
  | .loadByte a, h | .loadWord a, h => avoids_mono hpq a h
  | .const _, _ | .base, _ => trivial

/-- An assignment, then what follows. -/
theorem assign_then {o : Oracle σ} {P P' Q : PancakeState σ → Prop} {x : String} {e : PancakeExp}
    {k : PancakeProg}
    (h : ∀ v, P v → ∃ val old, eval v e = some val ∧ v.locals x = some old ∧
      P' { v with locals := setLocal v.locals x val })
    (hk : Safe.Safe o P' k Q) : Safe.Safe o P (.seq (.assign x e) k) Q := fun v hv => by
  obtain ⟨val, old, he, hx, hp⟩ := h v hv
  rw [SessionFrame.assign_seq o he hx]
  exact hk _ hp

theorem wp_cond_ne {e : PancakeExp} {c1 c2 : AProg σ} {Q : Assn σ} {t : PancakeState σ} {v : Word}
    (he : eval t e = some v) (hv : v ≠ 0) (h : wp c1 Q t) : wp (.cond e c1 c2) Q t := by
  simp only [wp, he, if_neg hv]
  exact h

theorem wp_cond_eq {e : PancakeExp} {c1 c2 : AProg σ} {Q : Assn σ} {t : PancakeState σ}
    (he : eval t e = some 0) (h : wp c2 Q t) : wp (.cond e c1 c2) Q t := by
  simp only [wp, he, if_true]
  exact h

section

variable {R : Ret} {Q : Assn σ} {t : PancakeState σ}

theorem wpR_cond_ne {e : PancakeExp} {c1 c2 : AProg σ} {v : Word} (he : eval t e = some v) (hv : v ≠ 0)
    (h : wpR c1 R Q t) : wpR (.cond e c1 c2) R Q t := by
  simp only [wpR, he, if_neg hv]
  exact h

theorem wpR_cond_eq {e : PancakeExp} {c1 c2 : AProg σ} (he : eval t e = some 0) (h : wpR c2 R Q t) :
    wpR (.cond e c1 c2) R Q t := by
  simp only [wpR, he, if_true]
  exact h

theorem wpR_seq {c1 c2 : AProg σ} {M : Assn σ} (h1 : wpR c1 R M t) (h2 : ∀ u, M u → wpR c2 R Q u) :
    wpR (.seq c1 c2) R Q t :=
  wpR_mono c1 R h2 t h1

theorem wpR_assign {x : String} {e : PancakeExp} {val old : Value} (he : eval t e = some val)
    (hx : t.locals x = some old) (hq : Q { t with locals := setLocal t.locals x val }) :
    wpR (.assign x e) R Q t :=
  wp_assign he hx hq

end

theorem wpR_seq_iff (c1 c2 : AProg σ) (R : Ret) (Q : Assn σ) {s : PancakeState σ} :
    wpR (.seq c1 c2) R Q s ↔ wpR c1 R (wpR c2 R Q) s := Iff.rfl

/-- A loop's `wpR` is its invariant, whatever follows it. -/
theorem wpR_while_seq (inv : Assn σ) (e : PancakeExp) (body c : AProg σ) (R : Ret) (Q : Assn σ)
    {s : PancakeState σ} : wpR (.seq (.while_ inv e body) c) R Q s ↔ inv s := Iff.rfl

theorem wpR_dec {R : Ret} {Q : Assn σ} {t : PancakeState σ} {v : String} {e : PancakeExp} {c : AProg σ}
    {val : Value} (he : eval t e = some val)
    (h : wpR c R (fun u => Q (restore u v (t.locals v))) { t with locals := setLocal t.locals v val }) :
    wpR (.dec v e c) R Q t := by
  simp only [wpR, he]
  exact h

/-! ## Arithmetic of digits -/

theorem value_append (ws : List Byte) (b : Byte) :
    CommandSpec.value (ws ++ [b]) = 10 * CommandSpec.value ws + (b.toNat - 48) := by
  simp [CommandSpec.value, List.foldl_append]

theorem foldl_value_lt : ∀ (ws : List Byte) (acc : Nat), ws.all CommandSpec.isDigit = true →
    ws.foldl (fun n b => 10 * n + (b.toNat - 48)) acc < (acc + 1) * 10 ^ ws.length
  | [], acc, _ => by simp
  | b :: ws, acc, h => by
    simp only [List.all_cons, Bool.and_eq_true] at h
    have hb := h.1
    simp only [CommandSpec.isDigit, Bool.and_eq_true, decide_eq_true_eq] at hb
    have ih := foldl_value_lt ws (10 * acc + (b.toNat - 48)) h.2
    simp only [List.foldl_cons, List.length_cons, Nat.pow_succ]
    have : (10 * acc + (b.toNat - 48) + 1) * 10 ^ ws.length ≤ (acc + 1) * (10 ^ ws.length * 10) := by
      rw [Nat.mul_comm (10 ^ ws.length) 10, ← Nat.mul_assoc]
      exact Nat.mul_le_mul_right _ (by omega)
    exact Nat.lt_of_lt_of_le ih this

theorem value_lt (ws : List Byte) (h : ws.all CommandSpec.isDigit = true) :
    CommandSpec.value ws < 10 ^ ws.length := by
  have := foldl_value_lt ws 0 h
  simpa [CommandSpec.value] using this

theorem take_succ_all {w : List Byte} {k : Nat} (hk : k < w.length) :
    (w.take (k + 1)).all CommandSpec.isDigit = ((w.take k).all CommandSpec.isDigit && CommandSpec.isDigit w[k]) := by
  rw [List.take_add_one, List.getElem?_eq_getElem hk, Option.toList_some, List.all_append]
  simp

theorem take_succ_value {w : List Byte} {k : Nat} (hk : k < w.length) :
    CommandSpec.value (w.take (k + 1)) = 10 * CommandSpec.value (w.take k) + (w[k].toNat - 48) := by
  rw [List.take_add_one, List.getElem?_eq_getElem hk, Option.toList_some]
  exact value_append _ _

/-! ## Tests of small numbers, as the session evaluates them -/


/-- `lo ≤ e ≤ hi`. -/
def betweenE (lo hi : Word) (e : PancakeExp) : PancakeExp := .op .and_ (leE (.const lo) e) (leE e (.const hi))

theorem sub_small (a b : Nat) (h : b ≤ a) (ha : a < 2 ^ 64) :
    BitVec.ofNat 64 a - BitVec.ofNat 64 b = BitVec.ofNat 64 (a - b) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt (by omega : b < 2 ^ 64), Nat.mod_eq_of_lt (by omega : a - b < 2 ^ 64)]
  omega

/-- An octet compared with a constant, as a word. -/
theorem byte_eq (y : Byte) (k : Nat) (hk : k < 256) :
    (if y.setWidth 64 = BitVec.ofNat 64 k then (1 : Word) else 0) = bw (decide (y = BitVec.ofNat 8 k)) := by
  by_cases h : y = BitVec.ofNat 8 k
  · rw [if_pos ((FramerCode.widen_eq y k hk).mpr h)]
    simp [bw, h]
  · simp only [bw, h, decide_false]
    rw [if_neg (fun e => h ((FramerCode.widen_eq y k hk).mp e))]
    rfl

section

variable {t : PancakeState σ}

theorem eval_const {c : Word} {n : Nat} (h : c = BitVec.ofNat 64 n) :
    eval t (.const c) = some (BitVec.ofNat 64 n) := by simp [eval, h]

theorem eval_between {e : PancakeExp} {L H : Word} {x lo hi : Nat} (hx : x < 2 ^ 63) (hlo : lo < 2 ^ 63)
    (hhi : hi < 2 ^ 63) (he : eval t e = some (BitVec.ofNat 64 x)) (hL : L = BitVec.ofNat 64 lo)
    (hH : H = BitVec.ofNat 64 hi) : eval t (betweenE L H e) = some (bw (decide (lo ≤ x ∧ x ≤ hi))) := by
  rw [betweenE, eval_and (eval_le hlo hx (eval_const hL) he) (eval_le hx hhi he (eval_const hH))]
  simp [bw]

end

/-- The line's octet at `se + k`. -/
def kb (se k : PancakeExp) : PancakeExp :=
  .loadByte (.op .add (.op .add (.var "blk") (.const 40)) (.op .add se k))

theorem kb_eval {t : PancakeState σ} {se k : PancakeExp} {B S : Word} {y : Byte} {j : Nat}
    (hB : t.locals "blk" = some B) (hA : eval t (.op .add se k) = some (S + BitVec.ofNat 64 j))
    (hbyte : memLoadByte t.memory t.memaddrs t.be (B + BitVec.ofNat 64 40 + (S + BitVec.ofNat 64 j)) = some y) :
    eval t (kb se k) = some (y.setWidth 64) := by
  simp only [kb]
  simp only [eval] at hA ⊢
  rw [hA]
  simp only [hB]
  rw [show (40 : Word) = BitVec.ofNat 64 40 from rfl, hbyte]

/-! ## What the checks ask -/

/-- Where connection `ci`'s framer's block lies, as `groupName` computes it. -/
def gnBlock (b : Word) (ci : Nat) : Word :=
  b + BitVec.ofNat 64 tableOff + BitVec.ofNat 64 ci * BitVec.ofNat 64 connSlot + BitVec.ofNat 64 cFramer

/-- …which is where `SessionFrame` has it. -/
theorem gnBlock_eq (b : Word) (ci : Nat) : gnBlock b ci = SessionFrame.blockAt b ci := by
  simp only [gnBlock, SessionFrame.blockAt, SessionFrame.recordAt, BitVec.ofNat_add, BitVec.ofNat_mul,
    BitVec.add_assoc]

/-- The session's return word. -/
def retW (b : Word) : Word := b + BitVec.ofNat 64 (ownOff + ownRet)

/-- What the check asks: the word from `se` of length `le`, the line's octets from `blk + 40`, those of `w`. The locals
it writes are bound. -/
structure NumPre (se le : PancakeExp) (B S : Word) (w : List Byte) (s : PancakeState σ) : Prop where
  se : eval s se = some S
  le : eval s le = some (BitVec.ofNat 64 w.length)
  blk : s.locals "blk" = some B
  bytes : ∀ j (h : j < w.length),
    memLoadByte s.memory s.memaddrs s.be (B + BitVec.ofNat 64 40 + (S + BitVec.ofNat 64 j)) = some w[j]
  short : w.length < 2 ^ 62
  ok : ∃ v, s.locals "ok" = some v
  val : ∃ v, s.locals "val" = some v
  jq : ∃ v, s.locals "jq" = some v

/-- What the check asks: the word from `se` of length `le`, `w` in the line's octets; `ok` and
`jq` bound. -/
structure MidPre (se le : PancakeExp) (B S : Word) (w : List Byte) (s : PancakeState σ) : Prop where
  se : eval s se = some S
  le : eval s le = some (BitVec.ofNat 64 w.length)
  blk : s.locals "blk" = some B
  bytes : ∀ j (h : j < w.length),
    memLoadByte s.memory s.memaddrs s.be (B + BitVec.ofNat 64 40 + (S + BitVec.ofNat 64 j)) = some w[j]
  short : w.length < 2 ^ 62
  ok : ∃ v, s.locals "ok" = some v
  jq : ∃ v, s.locals "jq" = some v

/-- What the check asks: the word from `se` of length `le`, `w` in the line's octets. The locals it writes are bound. -/
structure RngPre (se le : PancakeExp) (B S : Word) (w : List Byte) (s : PancakeState σ) : Prop where
  se : eval s se = some S
  le : eval s le = some (BitVec.ofNat 64 w.length)
  blk : s.locals "blk" = some B
  bytes : ∀ j (h : j < w.length),
    memLoadByte s.memory s.memaddrs s.be (B + BitVec.ofNat 64 40 + (S + BitVec.ofNat 64 j)) = some w[j]
  short : w.length < 2 ^ 62
  ok : ∃ v, s.locals "ok" = some v
  val : ∃ v, s.locals "val" = some v
  jq : ∃ v, s.locals "jq" = some v
  lo : ∃ v, s.locals "lo" = some v
  hi : ∃ v, s.locals "hi" = some v

/-- What the check asks: date `w1` from `s1` of length `l1`, time `w2` from `s2` of length `l2`. Both lie in the line's
octets; `ok` and `jq` are bound. -/
structure DTPre (B S1 S2 : Word) (w1 w2 : List Byte) (s : PancakeState σ) : Prop where
  s1 : s.locals "s1" = some S1
  l1 : s.locals "l1" = some (BitVec.ofNat 64 w1.length)
  s2 : s.locals "s2" = some S2
  l2 : s.locals "l2" = some (BitVec.ofNat 64 w2.length)
  blk : s.locals "blk" = some B
  bytes1 : ∀ j (h : j < w1.length),
    memLoadByte s.memory s.memaddrs s.be (B + BitVec.ofNat 64 40 + (S1 + BitVec.ofNat 64 j)) = some w1[j]
  bytes2 : ∀ j (h : j < w2.length),
    memLoadByte s.memory s.memaddrs s.be (B + BitVec.ofNat 64 40 + (S2 + BitVec.ofNat 64 j)) = some w2[j]
  short1 : w1.length < 2 ^ 62
  short2 : w2.length < 2 ^ 62
  ok : ∃ v, s.locals "ok" = some v
  jq : ∃ v, s.locals "jq" = some v

/-- What `groupName` asks: connection `ci`'s record holding the name `w` from `S` of its line's octets. The return word
is addressable. -/
structure GnPre (b : Word) (ci S : Nat) (w : List Byte) (s : PancakeState σ) : Prop where
  base : s.baseAddr = b
  c : s.locals "c" = some (BitVec.ofNat 64 ci)
  hci : ci ≤ conns - 1
  s1 : s.locals "s1" = some (BitVec.ofNat 64 S)
  hS : S ≤ News.SessionSpec.lineLimit
  l1 : s.locals "l1" = some (BitVec.ofNat 64 w.length)
  len : w.length ≤ News.SessionSpec.lineLimit
  bytes : ∀ j (h : j < w.length), memLoadByte s.memory s.memaddrs s.be
    (gnBlock b ci + BitVec.ofNat 64 40 + (BitVec.ofNat 64 S + BitVec.ofNat 64 j)) = some w[j]
  ret : s.memaddrs (retW b) = true

/-- What the wildmat check asks: the wildmat `w` from `S` of length `l2` in the line's octets. `ok` is the flag `p`,
`jq` bound. -/
structure WmPre (B S : Word) (w : List Byte) (p : Bool) (s : PancakeState σ) : Prop where
  s2 : s.locals "s2" = some S
  l2 : s.locals "l2" = some (BitVec.ofNat 64 w.length)
  blk : s.locals "blk" = some B
  bytes : ∀ j (h : j < w.length),
    memLoadByte s.memory s.memaddrs s.be (B + BitVec.ofNat 64 40 + (S + BitVec.ofNat 64 j)) = some w[j]
  short : w.length < 2 ^ 62
  ok : s.locals "ok" = some (bw p)
  jq : ∃ v, s.locals "jq" = some v

/-! ## An article number -/

/-- The names the number check writes. -/
def numNames : List String := ["ok", "val", "jq", "cz"]

/-- The loop's state after `k` octets of `w`: `jq` is `k`. `ok` is one and `val` the digits' value while all are digits
and one to sixteen long. Else `ok` is zero and `w` no article number. -/
def NumInv (w : List Byte) (s0 : PancakeState σ) (t : PancakeState σ) : Prop :=
  ButFor numNames s0 t ∧ ∃ k, k ≤ w.length ∧ t.locals "jq" = some (BitVec.ofNat 64 k) ∧
    ∃ okv valv, t.locals "ok" = some okv ∧ t.locals "val" = some valv ∧
      ((okv = 1 ∧ 1 ≤ w.length ∧ w.length ≤ 16 ∧ (w.take k).all CommandSpec.isDigit = true ∧
          valv = BitVec.ofNat 64 (CommandSpec.value (w.take k))) ∨
        (okv = 0 ∧ CommandSpec.isArticleNumber w = false))

/-- An octet: read, a digit or not, its value taken in, the place moved on. -/
def numBody (se : PancakeExp) : AProg σ :=
  .dec "cz" (kb se (.var "jq"))
    (.seq (.assign "ok" (.op .and_ (.cmp .less (.const 47) (.var "cz"))
        (.cmp .less (.var "cz") (.const 58))))
    (.seq (.assign "val" (.op .add (.mul (.var "val") (.const 10)) (.op .sub (.var "cz") (.const 48))))
      (.assign "jq" (.op .add (.var "jq") (.const 1)))))

/-- The last test: a value no more than the largest article number. -/
def numLast : AProg σ :=
  .cond (.var "ok") (.assign "ok" (.cmp .notLess (.const 2147483647) (.var "val"))) .skip

/-- The check, as it lowers, at the word from `se` of length `le`, its loop carrying `NumInv`. -/
def numA (se le : PancakeExp) (w : List Byte) (s0 : PancakeState σ) : AProg σ :=
  .seq (.assign "ok" (.op .and_ (.cmp .notLess le (.const 1)) (.cmp .notLess (.const 16) le)))
  (.seq (.assign "val" (.const 0))
  (.seq (.assign "jq" (.const 0))
  (.seq (.while_ (NumInv w s0) (.op .and_ (.var "ok") (.cmp .less (.var "jq") le)) (numBody se))
    numLast)))

theorem numberCheck_lower {s l : Syntax.PExpr} {se le : PancakeExp} (hs : Lower.lowerExp s = some se)
    (hl : Lower.lowerExp l = some le) (w : List Byte) (s0 : PancakeState σ) :
    Lower.lowerStmtsFold (Session.numberCheckAt s l) = some (numA se le w s0).erase := by
  simp [Session.numberCheckAt, Lower.lowerStmtsFold, Lower.lowerStmt1, Lower.lowerExp, hs, hl,
    Session.kept, Session.isDigitE, Syntax.eAdd, Syntax.eAnd, Syntax.eLe, Syntax.eLt, Syntax.eMul,
    Syntax.eSub, Syntax.n, Syntax.v, SessionStore.inc, numA, numBody, numLast, kb, AProg.erase, framerHead]

/-! ### The words a check reads -/

/-- `isDigitE`, of an octet: one for a digit. -/
theorem digit_eval (b : Byte) :
    ((if signedLt (47 : Word) (b.setWidth 64) = true then (1 : Word) else 0) &&&
      (if signedLt (b.setWidth 64) (58 : Word) = true then (1 : Word) else 0)) = bw (CommandSpec.isDigit b) := by
  have hb := b.isLt
  rw [Bytes.setWidth8_64, show (47 : Word) = BitVec.ofNat 64 47 from rfl,
    show (58 : Word) = BitVec.ofNat 64 58 from rfl, WpBytes.signedLt_small (a := _) (b := _) (by omega) (by omega),
    WpBytes.signedLt_small (a := _) (b := _) (by omega) (by omega)]
  simp only [bw, CommandSpec.isDigit]
  by_cases h1 : 47 < b.toNat <;> by_cases h2 : b.toNat < 58 <;> simp [h1, h2] <;> omega

theorem val_step (v c : Nat) (hc : 48 ≤ c) (hv : 10 * v + (c - 48) < 2 ^ 63) :
    BitVec.ofNat 64 v * 10 + (BitVec.ofNat 64 c - 48) = BitVec.ofNat 64 (10 * v + (c - 48)) := by
  apply BitVec.eq_of_toNat_eq
  have hc' : c < 2 ^ 64 := by omega
  simp only [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_sub, BitVec.toNat_ofNat]
  rw [show (10 : Word) = BitVec.ofNat 64 10 from rfl, show (48 : Word) = BitVec.ofNat 64 48 from rfl,
    BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  have hv' : v < 2 ^ 63 := by omega
  rw [Nat.mod_eq_of_lt (by omega : v < 2 ^ 64), Nat.mod_eq_of_lt (by omega : c < 2 ^ 64)]
  omega

/-- What the check leaves: the frame, `ok` its verdict and, for an article number, `val` its value. -/
def NumPost (w : List Byte) (s0 : PancakeState σ) (t : PancakeState σ) : Prop :=
  ButFor numNames s0 t ∧ t.locals "ok" = some (bw (CommandSpec.isArticleNumber w)) ∧
    (∃ v, t.locals "val" = some v) ∧ (∃ v, t.locals "jq" = some v) ∧ (CommandSpec.isArticleNumber w = true →
      t.locals "val" = some (BitVec.ofNat 64 (CommandSpec.value w)))

theorem but_blk {s0 t : PancakeState σ} (h : ButFor numNames s0 t) : t.locals "blk" = s0.locals "blk" :=
  h.locals "blk" (by decide)

/-- **An octet of the word, a digit after digits**: the loop goes on, one octet further. -/
theorem num_step (se : PancakeExp) (hse : ExpAvoids (· ∈ numNames) se) {le : PancakeExp} {B S : Word}
    {w : List Byte} {s0 : PancakeState σ} (hpre : NumPre se le B S w s0) (t : PancakeState σ)
    (hf : ButFor numNames s0 t) (k : Nat) (hk : k < w.length)
    (hjq : t.locals "jq" = some (BitVec.ofNat 64 k)) (hok : t.locals "ok" = some 1)
    (hval : t.locals "val" = some (BitVec.ofNat 64 (CommandSpec.value (w.take k))))
    (hlen : 1 ≤ w.length ∧ w.length ≤ 16) (hall : (w.take k).all CommandSpec.isDigit = true) :
    wp (numBody se) (NumInv w s0) t := by
  have hS := eval_but hf hse hpre.se
  have hB : t.locals "blk" = some B := (but_blk hf).trans hpre.blk
  have hbyte : memLoadByte t.memory t.memaddrs t.be (B + BitVec.ofNat 64 40 + (S + BitVec.ofNat 64 k)) =
      some w[k] := by rw [hf.load]; exact hpre.bytes k hk
  have hE := kb_eval (se := se) (k := .var "jq") hB (by simp only [eval, hS, hjq]) hbyte
  have hv : CommandSpec.value (w.take k) < 10 ^ k := by
    have := value_lt (w.take k) hall
    rwa [List.length_take, Nat.min_eq_left (by omega)] at this
  simp only [numBody, wp, hE]
  simp only [eval, setLocal, hok, hval, hjq, if_true, if_false, String.reduceEq]
  rw [digit_eval]
  have hb := w[k].isLt
  refine ⟨but_restore (but_set (but_set (but_set (but_set hf (by decide) _) (by decide) _)
    (by decide) _) (by decide) _) (by decide) _, k + 1, by omega,
    by simp [restore, resVar, setLocal, BitVec.ofNat_add], ?_⟩
  by_cases hd : CommandSpec.isDigit w[k] = true
  · refine ⟨1, BitVec.ofNat 64 (CommandSpec.value (List.take k w)) * 10 + (BitVec.setWidth 64 w[k] - 48),
      by simp [restore, resVar, setLocal, bw, hd], by simp [restore, resVar, setLocal], Or.inl
      ⟨rfl, hlen.1, hlen.2, by rw [take_succ_all hk, hall, hd]; rfl, ?_⟩⟩
    simp only [CommandSpec.isDigit, Bool.and_eq_true, decide_eq_true_eq] at hd
    have hv16 : CommandSpec.value (w.take k) < 10 ^ 16 :=
      Nat.lt_of_lt_of_le hv (Nat.pow_le_pow_right (by decide) (by omega))
    rw [take_succ_value hk, Bytes.setWidth8_64,
      val_step _ _ hd.1 (by have h1 : (10 : Nat) ^ 16 < 2 ^ 59 := (by decide); omega)]
  · refine ⟨0, BitVec.ofNat 64 (CommandSpec.value (List.take k w)) * 10 + (BitVec.setWidth 64 w[k] - 48),
      by simp [restore, resVar, setLocal, bw, hd], by simp [restore, resVar, setLocal], Or.inr
      ⟨rfl, ?_⟩⟩
    simp only [CommandSpec.isArticleNumber, Bool.and_eq_false_iff]
    left; right
    rw [List.all_eq_false]
    exact ⟨w[k], List.getElem_mem hk, by simpa using hd⟩

/-- **After the octets**: the last test gives the verdict. -/
theorem num_exit {w : List Byte} {s0 t : PancakeState σ} (hf : ButFor numNames s0 t) {okv valv : Word}
    (hok : t.locals "ok" = some okv) (hval : t.locals "val" = some valv) (hjq : ∃ x, t.locals "jq" = some x)
    (h : (okv = 1 ∧ 1 ≤ w.length ∧ w.length ≤ 16 ∧ w.all CommandSpec.isDigit = true ∧
          valv = BitVec.ofNat 64 (CommandSpec.value w)) ∨
        (okv = 0 ∧ CommandSpec.isArticleNumber w = false)) :
    wp numLast (NumPost w s0) t := by
  rcases h with ⟨rfl, h1, h16, hall, rfl⟩ | ⟨rfl, hno⟩
  · have hv : CommandSpec.value w < 10 ^ 16 :=
      Nat.lt_of_lt_of_le (value_lt w hall) (Nat.pow_le_pow_right (by decide) h16)
    have hlt := WpBytes.signedLt_small (a := 2147483647) (b := (CommandSpec.value w)) (by decide)
      (by have h1 : (10 : Nat) ^ 16 < 2 ^ 63 := (by decide); omega)
    simp only [numLast, wp, eval, hok, hval, show ((1 : Word) = 0) = False by decide, if_false]
    obtain ⟨x, hx⟩ := hjq
    refine ⟨but_set hf (by decide) _, ?_, ⟨BitVec.ofNat 64 (CommandSpec.value w), by simp [setLocal, hval]⟩,
      ⟨x, by simp [setLocal, hx]⟩, ?_⟩
    · simp only [setLocal, if_true, show (2147483647 : Word) = BitVec.ofNat 64 2147483647 from rfl, hlt]
      simp [bw, CommandSpec.isArticleNumber, h1, h16, hall]
      by_cases h : 2147483647 < CommandSpec.value w <;> simp [h] <;> omega
    · intro _
      simp [setLocal, hval]
  · simp only [numLast, wp, eval, hok, if_true]
    exact ⟨hf, by simp [hok, bw, hno], ⟨_, hval⟩, hjq, by simp [hno]⟩

/-- What the loops ask holds. -/
theorem num_vc (se le : PancakeExp) (hse : ExpAvoids (· ∈ numNames) se)
    (hle : ExpAvoids (· ∈ numNames) le) {B S : Word} {w : List Byte} {s0 : PancakeState σ}
    (hpre : NumPre se le B S w s0) : vc (numA se le w s0) (NumPost w s0) := by
  refine ⟨trivial, trivial, trivial, ⟨but_clockFree,
    fun _ => ⟨trivial, trivial, trivial⟩, fun t ⟨hf, k, hk, hjq, okv, valv, hok, hval, h⟩ => ?_⟩,
    trivial, trivial⟩
  have hL := eval_but hf hle hpre.le
  have hlt := WpBytes.signedLt_small (a := k) (b := w.length) (by have := hpre.short; omega)
    (by have := hpre.short; omega)
  simp only [eval, hok, hjq, hL, hlt]
  rcases h with ⟨rfl, h1, h16, hall, rfl⟩ | ⟨rfl, hno⟩
  · by_cases hkl : k < w.length
    · simp only [hkl, decide_true, if_true, show ((1 : Word) &&& 1) = 1 from rfl,
        show ((1 : Word) = 0) = False by decide, if_false]
      exact num_step se hse hpre t hf k hkl hjq hok hval ⟨h1, h16⟩ hall
    · have hkw : k = w.length := by omega
      subst hkw
      simp only [hkl, decide_false, Bool.false_eq_true, if_false, show ((1 : Word) &&& 0) = 0 from rfl,
        if_true]
      rw [List.take_length] at hall
      exact num_exit hf hok hval ⟨_, hjq⟩ (Or.inl ⟨rfl, h1, h16, hall, by rw [List.take_length]⟩)
  · simp only [show ∀ x : Word, ((0 : Word) &&& x) = 0 from fun x => by simp, if_true]
    exact num_exit hf hok hval ⟨_, hjq⟩ (Or.inr ⟨rfl, hno⟩)

/-- The check starts with the verdict on the length, the value and the place at zero. -/
theorem num_wp (se le : PancakeExp) {B S : Word} {w : List Byte} {s0 : PancakeState σ}
    (hpre : NumPre se le B S w s0) : wp (numA se le w s0) (NumPost w s0) s0 := by
  obtain ⟨okv, hok⟩ := hpre.ok
  obtain ⟨valv, hval⟩ := hpre.val
  obtain ⟨jqv, hjq⟩ := hpre.jq
  have hs := hpre.short
  have h1 := WpBytes.signedLt_small (a := w.length) (b := 1) (by omega) (by omega)
  have h2 := WpBytes.signedLt_small (a := 16) (b := w.length) (by omega) (by omega)
  simp only [numA, wp, eval, hpre.le, hok, show (1 : Word) = BitVec.ofNat 64 1 from rfl,
    show (16 : Word) = BitVec.ofNat 64 16 from rfl, h1, h2, setLocal, String.reduceEq, if_false, hval, hjq]
  refine ⟨but_set (but_set (but_set (but_refl _ _) (by decide) _) (by decide) _) (by decide) _,
    0, Nat.zero_le _, by simp [setLocal], ?_⟩
  by_cases hr : 1 ≤ w.length ∧ w.length ≤ 16
  · have ha : ¬ w.length < 1 := by omega
    have hb : ¬ 16 < w.length := by omega
    exact ⟨1, 0, by simp [setLocal, ha, hb], by simp [setLocal],
      Or.inl ⟨rfl, hr.1, hr.2, by simp, by simp [CommandSpec.value]⟩⟩
  · have hno : CommandSpec.isArticleNumber w = false := by
      simp only [CommandSpec.isArticleNumber, Bool.and_eq_false_iff, decide_eq_false_iff_not]
      left; left
      omega
    rcases Nat.lt_or_ge w.length 1 with ha | ha
    · exact ⟨0, 0, by simp [setLocal, ha], by simp [setLocal], Or.inr ⟨rfl, hno⟩⟩
    · have hb : 16 < w.length := by omega
      exact ⟨0, 0, by simp [setLocal, hb], by simp [setLocal], Or.inr ⟨rfl, hno⟩⟩

/-- **The number check is `CommandSpec.isArticleNumber`**: the word from `se` of length `le` is `w` in the line's
octets. A normally finishing run leaves `ok` the verdict and, for an article number, `val` its value. It changes no
local but its own nor the memory. -/
theorem number_safe (o : Oracle σ) (se le : PancakeExp) (hse : ExpAvoids (· ∈ numNames) se)
    (hle : ExpAvoids (· ∈ numNames) le) (B S : Word) (w : List Byte) (s0 : PancakeState σ) :
    Safe.Safe o (fun s => s = s0 ∧ NumPre se le B S w s) (numA se le w s0).erase (NumPost w s0) := by
  intro s ⟨hs, hpre⟩
  subst hs
  exact wp_sound o _ _ but_clockFree
    (num_vc se le hse hle hpre) s (num_wp se le hpre)

/-- The number check, as it lowers. -/
def numP (se le : PancakeExp) : PancakeProg := (numA (σ := Unit) se le [] (bareState ())).erase

theorem numA_erase (se le : PancakeExp) (w : List Byte) (s0 : PancakeState σ) :
    (numA se le w s0).erase = numP se le := rfl

/-- What the check leaves, from any state it starts in. -/
theorem numP_safe (o : Oracle σ) (se le : PancakeExp) (hse : ExpAvoids (· ∈ numNames) se)
    (hle : ExpAvoids (· ∈ numNames) le) (B S : Word) (w : List Byte) (s0 : PancakeState σ) :
    Safe.Safe o (fun s => s = s0 ∧ NumPre se le B S w s) (numP se le) (NumPost w s0) :=
  numA_erase se le w s0 ▸ number_safe o se le hse hle B S w s0

theorem numPost_clock (w : List Byte) (s0 : PancakeState σ) : Safe.ClockFree (NumPost w s0) :=
  but_clockFree

/-! ## A message-id -/

/-- The names the message-id check writes. -/
def midNames : List String := ["ok", "jq", "cz"]

/-- The octets between the first and the last. -/
def middle (w : List Byte) : List Byte := (w.drop 1).dropLast

theorem middle_length (w : List Byte) : (middle w).length = w.length - 2 := by
  simp [middle]
  omega

theorem middle_get (w : List Byte) (i : Nat) (h : i < (middle w).length) :
    (middle w)[i] = w[i + 1]'(by rw [middle_length] at h; omega) := by
  simp [middle, List.getElem_dropLast]

theorem middle_take_succ_all {w : List Byte} {i : Nat} (hi : i < (middle w).length) :
    ((middle w).take (i + 1)).all CommandSpec.isNotGt =
      (((middle w).take i).all CommandSpec.isNotGt && CommandSpec.isNotGt (middle w)[i]) := by
  rw [List.take_add_one, List.getElem?_eq_getElem hi, Option.toList_some, List.all_append]
  simp

theorem or_word (p q : Bool) : bw (signedLt (0 : Word) (bw p + bw q)) = bw (p || q) := by
  cases p <;> cases q <;> decide

/-- `A-NOTGT`, of an octet: one for a printable US-ASCII octet other than `>`. -/
theorem notGt_eval (b : Byte) :
    (if signedLt (0 : Word)
        (((if signedLt (32 : Word) (b.setWidth 64) = true then (1 : Word) else 0) &&&
            (if signedLt (b.setWidth 64) (62 : Word) = true then (1 : Word) else 0)) +
          ((if signedLt (62 : Word) (b.setWidth 64) = true then (1 : Word) else 0) &&&
            (if signedLt (b.setWidth 64) (127 : Word) = true then (1 : Word) else 0))) = true
      then (1 : Word) else 0) = bw (CommandSpec.isNotGt b) := by
  have hb := b.isLt
  rw [Bytes.setWidth8_64, show (32 : Word) = BitVec.ofNat 64 32 from rfl,
    show (62 : Word) = BitVec.ofNat 64 62 from rfl,
    show (127 : Word) = BitVec.ofNat 64 127 from rfl,
    WpBytes.signedLt_small (a := 32) (b := _) (by omega) (by omega),
    WpBytes.signedLt_small (a := _) (b := 62) (by omega) (by omega),
    WpBytes.signedLt_small (a := 62) (b := _) (by omega) (by omega),
    WpBytes.signedLt_small (a := _) (b := 127) (by omega) (by omega)]
  simp only [show ∀ c : Bool, (if c = true then (1 : Word) else 0) = bw c from fun _ => rfl, bw_and]
  rw [or_word]
  congr 1
  rw [Bool.eq_iff_iff]
  simp only [CommandSpec.isNotGt, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
  omega

theorem lt_angle : (CommandSpec.ascii "<").head! = 60#8 := by decide

theorem gt_angle : (CommandSpec.ascii ">").head! = 62#8 := by decide

/-- The loop's state at octet `k` of `w`, from the second octet on. `ok` is one while the prefix can be a message-id;
else zero, and `w` is none. -/
def MidInv (w : List Byte) (s0 : PancakeState σ) (t : PancakeState σ) : Prop :=
  ButFor midNames s0 t ∧ ∃ k, 1 ≤ k ∧ t.locals "jq" = some (BitVec.ofNat 64 k) ∧
    ∃ okv, t.locals "ok" = some okv ∧
      ((okv = 1 ∧ 3 ≤ w.length ∧ w.length ≤ 250 ∧ w.head? = some 60#8 ∧ w.getLast? = some 62#8 ∧
          k ≤ w.length - 1 ∧ ((middle w).take (k - 1)).all CommandSpec.isNotGt = true) ∨
        (okv = 0 ∧ CommandSpec.isMessageId w = false))

/-- An octet of the middle: read, `A-NOTGT` or not, the place moved on. -/
def midBody (se : PancakeExp) : AProg σ :=
  .dec "cz" (kb se (.var "jq"))
    (.seq (.assign "ok" (.cmp .less (.const 0)
        (.op .add (.op .and_ (.cmp .less (.const 32) (.var "cz")) (.cmp .less (.var "cz") (.const 62)))
          (.op .and_ (.cmp .less (.const 62) (.var "cz")) (.cmp .less (.var "cz") (.const 127))))))
      (.assign "jq" (.op .add (.var "jq") (.const 1))))

/-- The check, as it lowers, its loop carrying `MidInv`. -/
def midA (se le : PancakeExp) (w : List Byte) (s0 : PancakeState σ) : AProg σ :=
  .seq (.assign "ok" (.op .and_ (.cmp .notLess le (.const 3)) (.cmp .notLess (.const 250) le)))
  (.seq (.cond (.var "ok")
      (.assign "ok" (.op .and_
        (.cmp .equal (.loadByte (.op .add (.op .add (.var "blk") (.const 40)) se)) (.const 60))
        (.cmp .equal (.loadByte (.op .add (.op .add (.var "blk") (.const 40))
          (.op .sub (.op .add se le) (.const 1)))) (.const 62))))
      .skip)
  (.seq (.assign "jq" (.const 1))
    (.while_ (MidInv w s0) (.op .and_ (.var "ok") (.cmp .less (.var "jq") (.op .sub le (.const 1))))
      (midBody se))))

theorem messageIdCheck_lower {s l : Syntax.PExpr} {se le : PancakeExp} (hs : Lower.lowerExp s = some se)
    (hl : Lower.lowerExp l = some le) (w : List Byte) (s0 : PancakeState σ) :
    Lower.lowerStmtsFold (Session.messageIdCheckAt s l) = some (midA se le w s0).erase := by
  simp [Session.messageIdCheckAt, Lower.lowerStmtsFold, Lower.lowerStmt1, Lower.lowerExp, hs, hl,
    Session.kept, SessionStore.or2, Syntax.eAdd, Syntax.eAnd, Syntax.eLe, Syntax.eLt, Syntax.eEq,
    Syntax.eSub, Syntax.n, Syntax.v, SessionStore.inc, midA, midBody, kb, AProg.erase, framerHead]

/-- What the check leaves: the frame and `ok` its verdict. -/
def MidPost (w : List Byte) (s0 : PancakeState σ) (t : PancakeState σ) : Prop :=
  ButFor midNames s0 t ∧ t.locals "ok" = some (bw (CommandSpec.isMessageId w))

theorem isMessageId_iff (w : List Byte) :
    CommandSpec.isMessageId w = true ↔ 3 ≤ w.length ∧ w.length ≤ 250 ∧ w.head? = some 60#8 ∧
      w.getLast? = some 62#8 ∧ (middle w).all CommandSpec.isNotGt = true := by
  simp only [CommandSpec.isMessageId, lt_angle, gt_angle, middle, Bool.and_eq_true, decide_eq_true_eq,
    beq_iff_eq, and_assoc]

/-- **An octet of the middle, after octets that can be a message-id**: the loop goes on. -/
theorem mid_step (se : PancakeExp) (hse : ExpAvoids (· ∈ midNames) se) {le : PancakeExp} {B S : Word}
    {w : List Byte} {s0 : PancakeState σ} (hpre : MidPre se le B S w s0) (t : PancakeState σ)
    (hf : ButFor midNames s0 t) (k : Nat) (hk1 : 1 ≤ k) (hk : k < w.length - 1)
    (hjq : t.locals "jq" = some (BitVec.ofNat 64 k)) (hok : t.locals "ok" = some 1)
    (h3 : 3 ≤ w.length) (h250 : w.length ≤ 250) (hhd : w.head? = some 60#8)
    (hlt : w.getLast? = some 62#8)
    (hall : ((middle w).take (k - 1)).all CommandSpec.isNotGt = true) :
    wp (midBody se) (MidInv w s0) t := by
  have hS := eval_but hf hse hpre.se
  have hB : t.locals "blk" = some B := (hf.locals "blk" (by decide)).trans hpre.blk
  have hkw : k < w.length := by omega
  have hbyte : memLoadByte t.memory t.memaddrs t.be (B + BitVec.ofNat 64 40 + (S + BitVec.ofNat 64 k)) =
      some w[k] := by rw [hf.load]; exact hpre.bytes k hkw
  have hE := kb_eval (se := se) (k := .var "jq") hB (by simp only [eval, hS, hjq]) hbyte
  have hi : k - 1 < (middle w).length := by rw [middle_length]; omega
  have hmid : (middle w)[k - 1] = w[k] := by
    rw [middle_get w (k - 1) hi]
    congr 1
    omega
  simp only [midBody, wp, hE]
  simp only [eval, setLocal, hjq, if_true, if_false, String.reduceEq]
  rw [notGt_eval]
  simp only [hok]
  refine ⟨but_restore (but_set (but_set (but_set hf (by decide) _) (by decide) _) (by decide) _)
    (by decide) _, k + 1, by omega,
    by simp [restore, resVar, setLocal, BitVec.ofNat_add], ?_⟩
  by_cases hd : CommandSpec.isNotGt w[k] = true
  · refine ⟨1, by simp [restore, resVar, setLocal, bw, hd], Or.inl ⟨rfl, h3, h250, hhd, hlt, by omega, ?_⟩⟩
    rw [show k + 1 - 1 = (k - 1) + 1 by omega, middle_take_succ_all hi, hall, hmid, hd]
    rfl
  · refine ⟨0, by simp [restore, resVar, setLocal, bw, hd], Or.inr ⟨rfl, ?_⟩⟩
    rw [Bool.eq_false_iff]
    intro h
    have hm := ((isMessageId_iff w).mp h).2.2.2.2
    rw [List.all_eq_true] at hm
    have := hm _ (List.getElem_mem hi)
    rw [hmid] at this
    exact hd this

/-- The loop's test: `ok`, while the place is before the last octet. -/
theorem mid_cond {le : PancakeExp} {t : PancakeState σ} {okv : Word} {k n : Nat}
    (hok : t.locals "ok" = some okv) (hjq : t.locals "jq" = some (BitVec.ofNat 64 k))
    (hL : eval t le = some (BitVec.ofNat 64 n)) :
    eval t (.op .and_ (.var "ok") (.cmp .less (.var "jq") (.op .sub le (.const 1)))) =
      some (okv &&& if signedLt (BitVec.ofNat 64 k) (BitVec.ofNat 64 n - 1) then 1 else 0) := by
  simp only [eval, hok, hjq, hL]

/-- What the loop asks holds, and its end gives the verdict. -/
theorem mid_vc (se le : PancakeExp) (hse : ExpAvoids (· ∈ midNames) se)
    (hle : ExpAvoids (· ∈ midNames) le) {B S : Word} {w : List Byte} {s0 : PancakeState σ}
    (hpre : MidPre se le B S w s0) : vc (midA se le w s0) (MidPost w s0) := by
  refine ⟨trivial, ⟨trivial, trivial⟩, trivial, but_clockFree,
    fun _ => ⟨trivial, trivial⟩, fun t ⟨hf, k, hk1, hjq, okv, hok, h⟩ => ?_⟩
  have hL := eval_but hf hle hpre.le
  rw [mid_cond hok hjq hL]
  simp only
  rcases h with ⟨rfl, h3, h250, hhd, hlt, hkl, hall⟩ | ⟨rfl, hno⟩
  · have hs := hpre.short
    rw [show BitVec.ofNat 64 w.length - 1 = BitVec.ofNat 64 (w.length - 1) from
      sub_small _ 1 (by omega) (by omega), WpBytes.signedLt_small (a := k) (b := (w.length - 1)) (by omega) (by omega)]
    by_cases hk : k < w.length - 1
    · simp only [hk, decide_true, if_true, show ((1 : Word) &&& 1) = 1 from rfl,
        show ((1 : Word) = 0) = False by decide, if_false]
      exact mid_step se hse hpre t hf k hk1 hk hjq hok h3 h250 hhd hlt hall
    · simp only [hk, decide_false, Bool.false_eq_true, if_false,
        show ((1 : Word) &&& 0) = 0 from rfl, if_true]
      refine ⟨hf, ?_⟩
      have hm : (middle w).take (k - 1) = middle w := by
        rw [List.take_of_length_le]; rw [middle_length]; omega
      rw [hm] at hall
      rw [hok, (isMessageId_iff w).mpr ⟨h3, h250, hhd, hlt, hall⟩]
      rfl
  · rw [show ∀ x : Word, ((0 : Word) &&& x) = 0 from fun x => by simp]
    simp only [if_true]
    exact ⟨hf, by rw [hok, hno]; rfl⟩

theorem add_sub_one (S : Word) (n : Nat) (hn : 1 ≤ n) (hn' : n < 2 ^ 64) :
    S + BitVec.ofNat 64 n - 1 = S + BitVec.ofNat 64 (n - 1) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat]
  have hS := S.isLt
  rw [show (1 : Word).toNat = 1 from rfl, Nat.mod_eq_of_lt hn', Nat.mod_eq_of_lt (by omega : n - 1 < 2 ^ 64)]
  omega

/-- The verdict on the length: one when it lies in `[3, 250]`. -/
theorem len_eval (n : Nat) (hn : n < 2 ^ 62) :
    ((if signedLt (BitVec.ofNat 64 n) (3 : Word) = true then (0 : Word) else 1) &&&
      (if signedLt (250 : Word) (BitVec.ofNat 64 n) = true then (0 : Word) else 1)) =
      bw (decide (3 ≤ n ∧ n ≤ 250)) := by
  rw [show (3 : Word) = BitVec.ofNat 64 3 from rfl, show (250 : Word) = BitVec.ofNat 64 250 from rfl,
    WpBytes.signedLt_small (a := n) (b := 3) (by omega) (by omega),
    WpBytes.signedLt_small (a := 250) (b := n) (by omega) (by omega)]
  by_cases h1 : n < 3 <;> by_cases h2 : 250 < n <;> simp [h1, h2, bw] <;> omega

/-- The check starts with the verdict on the length and the angle brackets, the place at one. -/
theorem mid_wp (se le : PancakeExp) (hse : ExpAvoids (· ∈ midNames) se)
    (hle : ExpAvoids (· ∈ midNames) le) {B S : Word} {w : List Byte} {s0 : PancakeState σ}
    (hpre : MidPre se le B S w s0) : wp (midA se le w s0) (MidPost w s0) s0 := by
  obtain ⟨okv, hok⟩ := hpre.ok
  obtain ⟨jqv, hjq⟩ := hpre.jq
  have hs := hpre.short
  simp only [midA, wp, eval, hpre.le, hok]
  rw [len_eval _ (by omega)]
  have hf1 := but_set (but_refl midNames s0) (x := "ok") (by decide) (bw (decide (3 ≤ w.length ∧ w.length ≤ 250)))
  by_cases hr : 3 ≤ w.length ∧ w.length ≤ 250
  · have h0 : 0 < w.length := by omega
    have hl : w.length - 1 < w.length := by omega
    have hone : bw (decide (3 ≤ w.length ∧ w.length ≤ 250)) = 1 := by simp [bw, hr]
    rw [hone] at hf1 ⊢
    have hS := eval_but hf1 hse hpre.se
    have hL := eval_but hf1 hle hpre.le
    have hb0 := hpre.bytes 0 h0
    have hbl := hpre.bytes (w.length - 1) hl
    rw [show S + BitVec.ofNat 64 0 = S from BitVec.add_zero S] at hb0
    rw [← add_sub_one S w.length (by omega) (by omega)] at hbl
    simp only [setLocal, hS, hL, String.reduceEq, hpre.blk, hjq, ↓reduceIte]
    rw [show (40 : Word) = BitVec.ofNat 64 40 from rfl, hb0, hbl]
    simp only [show (60 : Word) = BitVec.ofNat 64 60 from rfl, show (62 : Word) = BitVec.ofNat 64 62 from rfl,
      byte_eq _ 60 (by decide), byte_eq _ 62 (by decide), bw_and]
    refine ⟨but_set (but_set hf1 (by decide) _) (by decide) _, 1, Nat.le_refl _, by simp [setLocal],
      bw (decide (w[0] = BitVec.ofNat 8 60) && decide (w[w.length - 1] = BitVec.ofNat 8 62)),
      by simp [setLocal], ?_⟩
    by_cases hb : (decide (w[0] = BitVec.ofNat 8 60) && decide (w[w.length - 1] = BitVec.ofNat 8 62)) = true
    · simp only [Bool.and_eq_true, decide_eq_true_eq] at hb
      left
      refine ⟨by simp [bw, hb], hr.1, hr.2, ?_, ?_, by omega, by simp⟩
      · rw [List.head?_eq_getElem?, List.getElem?_eq_getElem h0, hb.1]
      · rw [List.getLast?_eq_getElem?, List.getElem?_eq_getElem hl, hb.2]
    · right
      refine ⟨by simp only [bw, Bool.eq_false_iff.mpr hb]; rfl, ?_⟩
      rw [Bool.eq_false_iff]
      intro h
      obtain ⟨_, _, hhd, hlt, _⟩ := (isMessageId_iff w).mp h
      rw [List.head?_eq_getElem?, List.getElem?_eq_getElem h0, Option.some.injEq] at hhd
      rw [List.getLast?_eq_getElem?, List.getElem?_eq_getElem hl, Option.some.injEq] at hlt
      exact hb (by simp [hhd, hlt])
  · have hzero : bw (decide (3 ≤ w.length ∧ w.length ≤ 250)) = 0 := by simp [bw, hr]
    rw [hzero] at hf1 ⊢
    simp only [setLocal, String.reduceEq, hjq, ↓reduceIte]
    refine ⟨but_set hf1 (by decide) _, 1, Nat.le_refl _, by simp [setLocal], 0, by simp [setLocal],
      Or.inr ⟨rfl, ?_⟩⟩
    rw [Bool.eq_false_iff]
    intro h
    obtain ⟨h3, h250, _⟩ := (isMessageId_iff w).mp h
    exact hr ⟨h3, h250⟩

/-- **The message-id check is `CommandSpec.isMessageId`**: the word from `se` of length `le` is `w` in the line's
octets. A normally finishing run leaves `ok` the verdict. It changes no local but its own nor the memory. -/
theorem messageId_safe (o : Oracle σ) (se le : PancakeExp) (hse : ExpAvoids (· ∈ midNames) se)
    (hle : ExpAvoids (· ∈ midNames) le) (B S : Word) (w : List Byte) (s0 : PancakeState σ) :
    Safe.Safe o (fun s => s = s0 ∧ MidPre se le B S w s) (midA se le w s0).erase (MidPost w s0) := by
  intro s ⟨hs, hpre⟩
  subst hs
  exact wp_sound o _ _ but_clockFree
    (mid_vc se le hse hle hpre) s (mid_wp se le hse hle hpre)

/-! ## A range -/

/-- `-`. -/
def dash : Byte := 45#8

theorem count_take_succ (w : List Byte) {k : Nat} (hk : k < w.length) :
    (w.take (k + 1)).count dash = (w.take k).count dash + (if w[k] = dash then 1 else 0) := by
  rw [List.take_add_one, List.getElem?_eq_getElem hk, Option.toList_some, List.count_append,
    List.count_singleton]
  by_cases h : w[k] = dash <;> simp [h]

theorem count_split {w : List Byte} {d : Nat} (hd : w[d]? = some dash) :
    w.count dash = (w.take d).count dash + 1 + (w.drop (d + 1)).count dash := by
  obtain ⟨hlt, e⟩ := List.getElem?_eq_some_iff.mp hd
  conv => lhs; rw [← List.take_append_drop d w, List.drop_eq_getElem_cons hlt, e]
  rw [List.count_append, List.count_cons_self]
  omega

/-- A word split at its first dash. -/
theorem split_first {w : List Byte} {d : Nat} (hd : w[d]? = some dash) (h0 : (w.take d).count dash = 0) :
    w.splitOn dash = w.take d :: (w.drop (d + 1)).splitOn dash := by
  obtain ⟨hlt, e⟩ := List.getElem?_eq_some_iff.mp hd
  have hw : w = w.take d ++ dash :: w.drop (d + 1) := by
    conv => lhs; rw [← List.take_append_drop d w, List.drop_eq_getElem_cons hlt, e]
  exact (congrArg (List.splitOn dash) hw).trans
    (List.splitOn_append_cons_self_of_not_mem (List.count_eq_zero.mp h0) _)

/-- With no dash a range is a number… -/
theorem range_none {w : List Byte} (h : w.count dash = 0) :
    CommandSpec.range? w =
      if CommandSpec.isArticleNumber w then some (CommandSpec.value w, CommandSpec.value w) else none := by
  unfold CommandSpec.range?
  rw [show (45#8 : Byte) = dash from rfl, List.splitOn_eq_singleton (List.count_eq_zero.mp h)]

/-- …with one, a number and all after it, or two numbers… -/
theorem range_one {w : List Byte} {d : Nat} (hd : w[d]? = some dash) (h0 : (w.take d).count dash = 0)
    (h1 : (w.drop (d + 1)).count dash = 0) :
    CommandSpec.range? w =
      if w.drop (d + 1) = [] then
        (if CommandSpec.isArticleNumber (w.take d) then
          some (CommandSpec.value (w.take d), CommandSpec.numberMax) else none)
      else if CommandSpec.isArticleNumber (w.take d) && CommandSpec.isArticleNumber (w.drop (d + 1)) then
        some (CommandSpec.value (w.take d), CommandSpec.value (w.drop (d + 1))) else none := by
  unfold CommandSpec.range?
  rw [show (45#8 : Byte) = dash from rfl, split_first hd h0,
    List.splitOn_eq_singleton (List.count_eq_zero.mp h1)]
  generalize w.drop (d + 1) = b
  cases b <;> simp

/-- …and with more, none. -/
theorem range_many {w : List Byte} {d : Nat} (hd : w[d]? = some dash) (h0 : (w.take d).count dash = 0)
    (h2 : 0 < (w.drop (d + 1)).count dash) : CommandSpec.range? w = none := by
  obtain ⟨u, v, huv⟩ := List.append_of_mem (List.count_pos_iff.mp h2)
  have hs : (w.drop (d + 1)).splitOn dash = u.splitOn dash ++ v.splitOn dash := by
    rw [huv, List.splitOn_append_cons_self]
  obtain ⟨x, xs, hx⟩ := List.exists_cons_of_ne_nil (List.splitOn_ne_nil dash u)
  obtain ⟨y, ys, hy⟩ := List.exists_cons_of_ne_nil (List.splitOn_ne_nil dash v)
  unfold CommandSpec.range?
  rw [show (45#8 : Byte) = dash from rfl, split_first hd h0, hs, hx, hy]
  cases xs <;> simp

/-- The names the count of dashes writes… -/
def dashNames : List String := ["jq", "dn", "dp"]

/-- …and the range check. -/
def rngNames : List String := ["ok", "val", "jq", "cz", "lo", "hi", "dn", "dp"]

/-- An octet of the word: a dash counted, where the first is kept, the place moved on. -/
def dashBody (se : PancakeExp) : AProg σ :=
  .seq (.cond (.cmp .equal (kb se (.var "jq")) (.const 45))
      (.seq (.cond (.cmp .equal (.var "dn") (.const 0)) (.assign "dp" (.var "jq")) .skip)
        (.assign "dn" (.op .add (.var "dn") (.const 1))))
      .skip)
    (.assign "jq" (.op .add (.var "jq") (.const 1)))

/-- The dashes among the first `k` octets, and where the first is when there is one. -/
def Dashes (w : List Byte) (k : Nat) (t : PancakeState σ) : Prop :=
  t.locals "dn" = some (BitVec.ofNat 64 ((w.take k).count dash)) ∧ ∃ dpv, t.locals "dp" = some dpv ∧
    ((w.take k).count dash = 0 ∨
      ∃ d, w[d]? = some dash ∧ (w.take d).count dash = 0 ∧ dpv = BitVec.ofNat 64 d)

/-- The loop's state after `k` octets. -/
def DashInv (w : List Byte) (s0 : PancakeState σ) (t : PancakeState σ) : Prop :=
  ButFor dashNames s0 t ∧ ∃ k, k ≤ w.length ∧ t.locals "jq" = some (BitVec.ofNat 64 k) ∧ Dashes w k t

/-- …and after all of them. -/
def DashPost (w : List Byte) (s0 : PancakeState σ) (t : PancakeState σ) : Prop :=
  ButFor dashNames s0 t ∧ t.locals "jq" = some (BitVec.ofNat 64 w.length) ∧ Dashes w w.length t

def dashA (se le : PancakeExp) (w : List Byte) (s0 : PancakeState σ) : AProg σ :=
  .while_ (DashInv w s0) (.cmp .less (.var "jq") le) (dashBody se)

/-- **An octet of the word**: counted, the loop goes on. -/
theorem dash_step (se : PancakeExp) (hse : ExpAvoids (· ∈ dashNames) se) {le : PancakeExp} {B S : Word}
    {w : List Byte} {s0 : PancakeState σ} (hpre : RngPre se le B S w s0) (t : PancakeState σ)
    (hf : ButFor dashNames s0 t) (k : Nat) (hk : k < w.length)
    (hjq : t.locals "jq" = some (BitVec.ofNat 64 k)) (hd : Dashes w k t) :
    wp (dashBody se) (DashInv w s0) t := by
  obtain ⟨hdn, dpv, hdp, hfirst⟩ := hd
  have hS := eval_but hf hse hpre.se
  have hB : t.locals "blk" = some B := (hf.locals "blk" (by decide)).trans hpre.blk
  have hbyte : memLoadByte t.memory t.memaddrs t.be (B + BitVec.ofNat 64 40 + (S + BitVec.ofNat 64 k)) =
      some w[k] := by rw [hf.load]; exact hpre.bytes k hk
  have hE : eval t (.cmp .equal (kb se (.var "jq")) (.const 45)) = some (bw (decide (w[k] = dash))) := by
    simp only [eval, kb_eval (se := se) (k := .var "jq") hB (by simp only [eval, hS, hjq]) hbyte]
    exact congrArg some (byte_eq w[k] 45 (by decide))
  have hs := hpre.short
  have hc : (w.take k).count dash ≤ k := by
    have := List.count_le_length (a := dash) (l := w.take k)
    simp only [List.length_take] at this
    omega
  have htake := count_take_succ w hk
  apply wp_seq (M := fun u => ButFor dashNames s0 u ∧ u.locals "jq" = some (BitVec.ofNat 64 k) ∧
    Dashes w (k + 1) u)
  · by_cases hx : w[k] = dash
    · refine wp_cond_ne hE (by simp [bw, hx]) ?_
      have hcount : (w.take (k + 1)).count dash = (w.take k).count dash + 1 := by rw [htake, if_pos hx]
      unfold Dashes
      rw [hcount]
      by_cases h0 : (w.take k).count dash = 0
      · rw [h0] at hdn ⊢
        refine wp_seq (M := fun u => u = { t with locals := setLocal t.locals "dp" (BitVec.ofNat 64 k) })
          (wp_cond_ne (v := 1) (by simp only [eval, hdn]; decide) (by decide)
            (wp_assign (by simp [eval, hjq]) hdp rfl)) ?_
        rintro u rfl
        refine wp_assign (val := BitVec.ofNat 64 (0 + 1)) (old := 0#64) (by simp [eval, setLocal, hdn])
          (by simp [setLocal, hdn]) ?_
        exact ⟨but_set (but_set hf (by decide) _) (by decide) _, by simp [setLocal, hjq], by simp [setLocal],
          BitVec.ofNat 64 k, by simp [setLocal], Or.inr ⟨k, by simp [hk, hx], h0, rfl⟩⟩
      · have hne : BitVec.ofNat 64 ((w.take k).count dash) ≠ (0 : Word) := NatToDec.ofNat64_ne_zero h0 (by omega)
        refine wp_seq (M := fun u => u = t) (wp_cond_eq (by simp only [eval, hdn, if_neg hne]) rfl) ?_
        rintro u rfl
        refine wp_assign (val := BitVec.ofNat 64 ((w.take k).count dash + 1))
          (by simp [eval, hdn, BitVec.ofNat_add]) hdn ?_
        exact ⟨but_set hf (by decide) _, by simp [setLocal, hjq], by simp [setLocal], dpv,
          by simp [setLocal, hdp], Or.inr (hfirst.resolve_left h0)⟩
    · refine wp_cond_eq (by rw [hE]; simp [bw, hx]) ?_
      have hcount : (w.take (k + 1)).count dash = (w.take k).count dash := by
        rw [htake, if_neg hx, Nat.add_zero]
      unfold Dashes
      rw [hcount]
      exact ⟨hf, hjq, hdn, dpv, hdp, hfirst⟩
  · intro u ⟨hfu, hju, hdu⟩
    refine wp_assign (val := BitVec.ofNat 64 (k + 1)) (by simp [eval, hju, BitVec.ofNat_add]) hju ?_
    obtain ⟨hdn', dpv', hdp', hf'⟩ := hdu
    exact ⟨but_set hfu (by decide) _, k + 1, by omega, by simp [setLocal],
      by simp [setLocal, hdn'], dpv', by simp [setLocal, hdp'], hf'⟩

theorem dash_vc (se le : PancakeExp) (hse : ExpAvoids (· ∈ dashNames) se)
    (hle : ExpAvoids (· ∈ dashNames) le) {B S : Word} {w : List Byte} {s0 : PancakeState σ}
    (hpre : RngPre se le B S w s0) : vc (dashA se le w s0) (DashPost w s0) := by
  refine ⟨but_clockFree, by simp [vc, dashBody],
    fun t ⟨hf, k, hk, hjq, hd⟩ => ?_⟩
  have hL := eval_but hf hle hpre.le
  have hs := hpre.short
  have hlt := WpBytes.signedLt_small (a := k) (b := w.length) (by omega) (by omega)
  simp only [eval, hjq, hL, hlt]
  by_cases hkl : k < w.length
  · simp only [hkl, decide_true, if_true, show ((1 : Word) = 0) = False by decide, if_false]
    exact dash_step se hse hpre t hf k hkl hjq hd
  · have hkw : k = w.length := by omega
    subst hkw
    simp only [hkl, decide_false, Bool.false_eq_true, if_false, if_true]
    exact ⟨hf, hjq, hd⟩

theorem numberCheck_lowerP {s l : Syntax.PExpr} {se le : PancakeExp} (hs : Lower.lowerExp s = some se)
    (hl : Lower.lowerExp l = some le) : Lower.lowerStmtsFold (Session.numberCheckAt s l) = some (numP se le) :=
  numberCheck_lower (σ := Unit) hs hl [] (bareState ())

def dashP (se le : PancakeExp) : PancakeProg := (dashA (σ := Unit) se le [] (bareState ())).erase

/-- The range check as it lowers, given what follows its count of dashes. -/
def rangeP (W t0 t1 : PancakeProg) : PancakeProg :=
  .dec "dn" (.const 0) (.dec "dp" (.const 0) (.seq (.assign "jq" (.const 0))
    (.seq W (.cond (.cmp .equal (.var "dn") (.const 0)) t0
      (.cond (.cmp .equal (.var "dn") (.const 1)) t1 (.assign "ok" (.const 0)))))))

/-- The second number's place and length, as they lower. -/
def afterDash (se : PancakeExp) : PancakeExp := .op .add (.op .add se (.var "dp")) (.const 1)

def restLen (le : PancakeExp) : PancakeExp := .op .sub (.op .sub le (.var "dp")) (.const 1)

theorem rangeCheck_lower (o : Oracle σ) {s l : Syntax.PExpr} {se le : PancakeExp}
    (hs : Lower.lowerExp s = some se) (hl : Lower.lowerExp l = some le) :
    ∃ t0 t1 t2, Lower.lowerStmtsFold (Session.rangeCheckAt s l) = some (rangeP (dashP se le) t0 t1) ∧
      (∀ u, PancakeSem o t0 u = PancakeSem o (.seq (numP se le)
        (.seq (.assign "lo" (.var "val")) (.assign "hi" (.var "val")))) u) ∧
      (∀ u, PancakeSem o t1 u = PancakeSem o (.seq (numP se (.var "dp")) (.seq (.assign "lo" (.var "val"))
        (.cond (.var "ok") (.cond (.cmp .equal (.op .add (.var "dp") (.const 1)) le)
          (.assign "hi" (.const 2147483647)) t2) .skip))) u) ∧
      (∀ u, PancakeSem o t2 u = PancakeSem o (.seq (numP (afterDash se) (restLen le))
        (.assign "hi" (.var "val"))) u) := by
  have hs' : Lower.lowerExp (Syntax.eAdd (Syntax.eAdd s (Syntax.v "dp")) (Syntax.n 1)) = some (afterDash se) := by
    simp [Lower.lowerExp, Syntax.eAdd, Syntax.v, Syntax.n, hs, afterDash]
  have hl' : Lower.lowerExp (Syntax.eSub (Syntax.eSub l (Syntax.v "dp")) (Syntax.n 1)) = some (restLen le) := by
    simp [Lower.lowerExp, Syntax.eSub, Syntax.v, Syntax.n, hl, restLen]
  have hnd : ∀ (a b : Syntax.PExpr), ∀ x ∈ Session.numberCheckAt a b, x.isDec = false := by
    intro a b x hx
    simp only [Session.numberCheckAt, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl <;> rfl
  have hne : ∀ (a b : Syntax.PExpr), Session.numberCheckAt a b ≠ [] := by
    intro a b; simp [Session.numberCheckAt]
  obtain ⟨t2, ht2, ht2s⟩ := DN.Compiler.Block.fold_append o _ [.assign "hi" (Syntax.v "val")] (hne _ _) (by simp)
    (hnd _ _) (numberCheck_lowerP hs' hl') (b := .assign "hi" (.var "val")) rfl
  obtain ⟨t1, ht1, ht1s⟩ := DN.Compiler.Block.fold_append o (Session.numberCheckAt s (Syntax.v "dp"))
    [.assign "lo" (Syntax.v "val"), SessionStore.ifs (Syntax.v "ok")
      [.ite (Syntax.eEq (Syntax.eAdd (Syntax.v "dp") (Syntax.n 1)) l)
        [.assign "hi" (Syntax.n CommandSpec.numberMax)]
        (Session.numberCheckAt (Syntax.eAdd (Syntax.eAdd s (Syntax.v "dp")) (Syntax.n 1))
          (Syntax.eSub (Syntax.eSub l (Syntax.v "dp")) (Syntax.n 1)) ++ [.assign "hi" (Syntax.v "val")])]]
    (hne _ _) (by simp) (hnd _ _) (numberCheck_lowerP hs rfl)
    (b := .seq (.assign "lo" (.var "val")) (.cond (.var "ok") (.cond (.cmp .equal (.op .add (.var "dp") (.const 1)) le)
          (.assign "hi" (.const 2147483647)) t2) .skip))
    (by
      have h := ht2
      simp only [Syntax.eAdd, Syntax.eSub, Syntax.v, Syntax.n] at h
      simp [Lower.lowerStmtsFold, Lower.lowerStmt1, Lower.lowerExp, SessionStore.ifs, Syntax.eEq, Syntax.eAdd,
        Syntax.eSub, Syntax.v, Syntax.n, hl, h, CommandSpec.numberMax])
  obtain ⟨t0, ht0, ht0s⟩ := DN.Compiler.Block.fold_append o (Session.numberCheckAt s l)
    [.assign "lo" (Syntax.v "val"), .assign "hi" (Syntax.v "val")] (hne _ _) (by simp) (hnd _ _)
    (numberCheck_lowerP hs hl) (b := .seq (.assign "lo" (.var "val")) (.assign "hi" (.var "val"))) rfl
  refine ⟨t0, t1, t2, ?_, ht0s, ht1s, ht2s⟩
  simp only [Syntax.eEq, Syntax.eAdd, Syntax.eSub, Syntax.v, Syntax.n, SessionStore.ifs,
    CommandSpec.numberMax] at ht0 ht1
  simp [Session.rangeCheckAt, Lower.lowerStmtsFold, Lower.lowerStmt1, Lower.lowerExp, hs, hl, ht0, ht1,
    rangeP, dashP, dashA, dashBody, kb, AProg.erase, Syntax.eEq, Syntax.eAdd, Syntax.eSub, Syntax.eLt, Syntax.v,
    Syntax.n, SessionStore.ifs, SessionStore.inc, Session.kept, framerHead, CommandSpec.numberMax]

/-- What the check leaves: `ok` whether the word is a range and, for one, `lo` and `hi` its ends. -/
def RngPost (w : List Byte) (s0 : PancakeState σ) (t : PancakeState σ) : Prop :=
  ButFor rngNames s0 t ∧ t.locals "ok" = some (bw (CommandSpec.range? w).isSome) ∧
    ∀ lo hi, CommandSpec.range? w = some (lo, hi) →
      t.locals "lo" = some (BitVec.ofNat 64 lo) ∧ t.locals "hi" = some (BitVec.ofNat 64 hi)

theorem dashPost_clock (w : List Byte) (s0 : PancakeState σ) : Safe.ClockFree (DashPost w s0) :=
  but_clockFree

/-- The end of `dn`'s and `dp`'s scope. -/
theorem rngPost_restore {w : List Byte} {s0 t : PancakeState σ} (h : RngPost w s0 t) {x : String}
    (hx : x ∈ ["dn", "dp"]) (old : Option Value) :
    RngPost w s0 { t with locals := resVar t.locals x old } := by
  obtain ⟨hf, hok, hlh⟩ := h
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  have hr : x ∈ rngNames := by rcases hx with rfl | rfl <;> decide
  have hne : ∀ y, y ∈ ["ok", "lo", "hi"] → y ≠ x := by
    intro y hy
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl | rfl <;> decide
  refine ⟨but_restore hf hr old, by simp [resVar, hne "ok" (by simp), hok], fun lo hi h => ?_⟩
  obtain ⟨h1, h2⟩ := hlh lo hi h
  exact ⟨by simp [resVar, hne "lo" (by simp), h1], by simp [resVar, hne "hi" (by simp), h2]⟩

theorem dash_rng : ∀ x, x ∈ dashNames → x ∈ rngNames := by
  intro x hx
  simp only [dashNames, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl <;> decide

theorem num_rng : ∀ x, x ∈ numNames → x ∈ rngNames := by
  intro x hx
  simp only [numNames, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl <;> decide

/-- A number check's word inside the range's, from `S + a`, `n` octets, the range's from `a` on. -/
theorem numPre_at {se le se' le' : PancakeExp} {B S S' : Word} {w : List Byte} {s0 v : PancakeState σ}
    (hpre : RngPre se le B S w s0) (hf : ButFor rngNames s0 v) (a n : Nat) (han : a + n ≤ w.length)
    (hS' : eval v se' = some S') (hSa : S' = S + BitVec.ofNat 64 a)
    (hL : eval v le' = some (BitVec.ofNat 64 n)) (hval : ∃ x, v.locals "val" = some x)
    (hjq : ∃ x, v.locals "jq" = some x) (hok : ∃ x, v.locals "ok" = some x) :
    NumPre se' le' B S' ((w.drop a).take n) v := by
  have hlen : ((w.drop a).take n).length = n := by simp; omega
  refine ⟨hS', by rw [hlen]; exact hL, (hf.locals "blk" (by decide)).trans hpre.blk, fun j hj => ?_,
    by rw [hlen]; have := hpre.short; omega, hok, hval, hjq⟩
  rw [hlen] at hj
  rw [hf.memory, hf.memaddrs, hf.be, hSa, BitVec.add_assoc S, ← BitVec.ofNat_add]
  have := hpre.bytes (a + j) (by omega)
  simp only [List.getElem_take, List.getElem_drop]
  exact this

/-- A local of the range check's start, where neither the count nor a number check writes it. -/
theorem keeps_local {s0 v t : PancakeState σ} (hd : ButFor dashNames s0 v) (hn : ButFor numNames v t)
    (x : String) (hxd : x ∉ dashNames) (hxn : x ∉ numNames) : t.locals x = s0.locals x :=
  (hn.locals x hxn).trans (hd.locals x hxd)

/-- **No dash**: a number or not a range. -/
theorem range_noDash (o : Oracle σ) {se le : PancakeExp} (hse : ExpAvoids (· ∈ rngNames) se)
    (hle : ExpAvoids (· ∈ rngNames) le) {B S : Word} {w : List Byte} {u : PancakeState σ}
    (hpre : RngPre se le B S w u) (h0 : w.count dash = 0) :
    Safe.Safe o (DashPost w u)
      (.seq (numP se le) (.seq (.assign "lo" (.var "val")) (.assign "hi" (.var "val")))) (RngPost w u) := by
  have hse_d := avoids_mono (fun x hx => dash_rng x hx) se hse
  have hle_d := avoids_mono (fun x hx => dash_rng x hx) le hle
  have hse_n := avoids_mono (fun x hx => num_rng x hx) se hse
  have hle_n := avoids_mono (fun x hx => num_rng x hx) le hle
  refine then_ (M := NumPost w) (P' := fun t => ButFor rngNames u t ∧
      t.locals "ok" = some (bw (CommandSpec.isArticleNumber w)) ∧ (∃ x, t.locals "val" = some x) ∧
      (CommandSpec.isArticleNumber w = true → t.locals "val" = some (BitVec.ofNat 64 (CommandSpec.value w))) ∧
      (∃ x, t.locals "lo" = some x) ∧ (∃ x, t.locals "hi" = some x))
    (fun v0 => Safe.conseq (numP_safe o se le hse_n hle_n B S w v0) (fun v ⟨hv, hd⟩ => ⟨hv, ?_⟩)
      (fun _ h => h))
    (numPost_clock w) (fun v0 t hd hn => ?_) ?_
  · obtain ⟨x, hx⟩ := hpre.val
    obtain ⟨y, hy⟩ := hpre.ok
    have h := numPre_at hpre (but_mono hd.1 dash_rng) 0 w.length (by omega) (eval_but hd.1 hse_d hpre.se)
      (BitVec.add_zero S).symm (eval_but hd.1 hle_d hpre.le)
      ⟨x, (hd.1.locals "val" (by decide)).trans hx⟩ ⟨_, hd.2.1⟩ ⟨y, (hd.1.locals "ok" (by decide)).trans hy⟩
    rwa [List.drop_zero, List.take_length] at h
  · obtain ⟨hn, hok, hv, _, hval⟩ := hn
    exact ⟨but_trans (but_mono hd.1 dash_rng) (but_mono hn num_rng), hok, hv, hval,
      by rw [keeps_local hd.1 hn "lo" (by decide) (by decide)]; exact hpre.lo,
      by rw [keeps_local hd.1 hn "hi" (by decide) (by decide)]; exact hpre.hi⟩
  · refine assign_then (P' := fun t => ButFor rngNames u t ∧
        t.locals "ok" = some (bw (CommandSpec.isArticleNumber w)) ∧ (∃ x, t.locals "hi" = some x) ∧
        ∃ x, t.locals "val" = some x ∧ t.locals "lo" = some x ∧
          (CommandSpec.isArticleNumber w = true → x = BitVec.ofNat 64 (CommandSpec.value w)))
      (fun v ⟨hf, hok, ⟨x, hx⟩, hval, ⟨y, hy⟩, ⟨z, hz⟩⟩ => ⟨x, y, by simp [eval, hx], hy,
        but_set hf (by decide) _, by simp [setLocal, hok], ⟨z, by simp [setLocal, hz]⟩, x,
        by simp [setLocal, hx], by simp [setLocal],
        fun h => by rw [hval h] at hx; exact (Option.some.inj hx).symm⟩) ?_
    refine Safe.assign fun v ⟨hf, hok, ⟨z, hz⟩, x, hx, hlo, hxv⟩ => ⟨x, z, by simp [eval, hx], hz, ?_⟩
    refine ⟨but_set hf (by decide) _, ?_, fun lo hi h => ?_⟩
    · rw [range_none h0]
      cases hn : CommandSpec.isArticleNumber w <;> simp [setLocal, hok, hn, bw]
    · rw [range_none h0] at h
      split at h
      · rename_i hn
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨by simp [setLocal, hlo, hxv hn], by simp [setLocal, hxv hn]⟩
      · cases h

/-- **One dash**: a number and all after it, or two numbers. -/
theorem range_oneDash (o : Oracle σ) {se le : PancakeExp} (hse : ExpAvoids (· ∈ rngNames) se)
    (hle : ExpAvoids (· ∈ rngNames) le) {B S : Word} {w : List Byte} {u : PancakeState σ}
    (hpre : RngPre se le B S w u) {d : Nat} (hd : w[d]? = some dash) (h0 : (w.take d).count dash = 0)
    (h1 : (w.drop (d + 1)).count dash = 0) {t2 : PancakeProg}
    (h2s : ∀ v, PancakeSem o t2 v =
      PancakeSem o (.seq (numP (afterDash se) (restLen le)) (.assign "hi" (.var "val"))) v) :
    Safe.Safe o (fun v => DashPost w u v ∧ v.locals "dp" = some (BitVec.ofNat 64 d))
      (.seq (numP se (.var "dp")) (.seq (.assign "lo" (.var "val"))
        (.cond (.var "ok") (.cond (.cmp .equal (.op .add (.var "dp") (.const 1)) le)
          (.assign "hi" (.const 2147483647)) t2) .skip))) (RngPost w u) := by
  have hse_d := avoids_mono (fun x hx => dash_rng x hx) se hse
  have hle_d := avoids_mono (fun x hx => dash_rng x hx) le hle
  have hse_n := avoids_mono (fun x hx => num_rng x hx) se hse
  have hle_n := avoids_mono (fun x hx => num_rng x hx) le hle
  have hs := hpre.short
  obtain ⟨hlt, _⟩ := List.getElem?_eq_some_iff.mp hd
  have hrange := range_one hd h0 h1
  have hdpN : ExpAvoids (· ∈ numNames) (.var "dp") := by simp [ExpAvoids, numNames]
  refine then_ (M := NumPost (w.take d)) (P' := fun t => ButFor rngNames u t ∧
      t.locals "ok" = some (bw (CommandSpec.isArticleNumber (w.take d))) ∧ (∃ x, t.locals "val" = some x) ∧
      (∃ x, t.locals "jq" = some x) ∧
      (CommandSpec.isArticleNumber (w.take d) = true →
        t.locals "val" = some (BitVec.ofNat 64 (CommandSpec.value (w.take d)))) ∧
      (∃ x, t.locals "lo" = some x) ∧ (∃ x, t.locals "hi" = some x) ∧
      t.locals "dp" = some (BitVec.ofNat 64 d))
    (fun v0 => Safe.conseq (numP_safe o se (.var "dp") hse_n hdpN B S (w.take d) v0)
      (fun v ⟨hv, hd', hdp⟩ => ⟨hv, ?_⟩) (fun _ h => h))
    (numPost_clock _) (fun v0 t ⟨hd', hdp⟩ hn => ?_) ?_
  · obtain ⟨x, hx⟩ := hpre.val
    obtain ⟨y, hy⟩ := hpre.ok
    have h := numPre_at hpre (but_mono hd'.1 dash_rng) 0 d (by omega) (eval_but hd'.1 hse_d hpre.se)
      (BitVec.add_zero S).symm (show eval v (.var "dp") = _ from hdp)
      ⟨x, (hd'.1.locals "val" (by decide)).trans hx⟩ ⟨_, hd'.2.1⟩ ⟨y, (hd'.1.locals "ok" (by decide)).trans hy⟩
    rwa [List.drop_zero] at h
  · obtain ⟨hn, hok, hv, hj, hval⟩ := hn
    exact ⟨but_trans (but_mono hd'.1 dash_rng) (but_mono hn num_rng), hok, hv, hj, hval,
      by rw [keeps_local hd'.1 hn "lo" (by decide) (by decide)]; exact hpre.lo,
      by rw [keeps_local hd'.1 hn "hi" (by decide) (by decide)]; exact hpre.hi,
      by rw [hn.locals "dp" (by decide)]; exact hdp⟩
  refine assign_then (P' := fun t => ButFor rngNames u t ∧
      t.locals "ok" = some (bw (CommandSpec.isArticleNumber (w.take d))) ∧ (∃ x, t.locals "val" = some x) ∧
      (∃ x, t.locals "jq" = some x) ∧
      (CommandSpec.isArticleNumber (w.take d) = true →
        t.locals "lo" = some (BitVec.ofNat 64 (CommandSpec.value (w.take d)))) ∧
      (∃ x, t.locals "hi" = some x) ∧ t.locals "dp" = some (BitVec.ofNat 64 d))
    (fun v ⟨hf, hok, ⟨x, hx⟩, ⟨j, hj⟩, hval, ⟨y, hy⟩, ⟨z, hz⟩, hdp⟩ => ⟨x, y, by simp [eval, hx], hy,
      but_set hf (by decide) _, by simp [setLocal, hok], ⟨x, by simp [setLocal, hx]⟩,
      ⟨j, by simp [setLocal, hj]⟩, fun h => by rw [hval h] at hx; simp [setLocal, hx],
      ⟨z, by simp [setLocal, hz]⟩, by simp [setLocal, hdp]⟩) ?_
  refine Safe.cond (fun v ⟨_, hok, _⟩ => ⟨_, hok⟩) ?_ ?_
  · -- a number before the dash
    rintro v ⟨⟨hf, hok, ⟨x, hx⟩, ⟨j, hj⟩, hlo, ⟨z, hz⟩, hdp⟩, hne⟩
    have ha : CommandSpec.isArticleNumber (w.take d) = true := by
      cases h : CommandSpec.isArticleNumber (w.take d)
      · exact absurd (show eval v (.var "ok") = some 0 by simp [eval, hok, h, bw]) hne
      · rfl
    have hL := eval_but hf hle hpre.le
    have hE : eval v (.cmp .equal (.op .add (.var "dp") (.const 1)) le) =
        some (bw (decide (d + 1 = w.length))) := by
      simp only [eval, hdp, hL]
      rw [show (1 : Word) = BitVec.ofNat 64 1 from rfl, ← BitVec.ofNat_add]
      by_cases h : d + 1 = w.length
      · simp [h, bw]
      · rw [if_neg (fun e => h (NatToDec.ofNat64_inj (by omega) (by omega) e))]
        simp [h, bw]
    refine Safe.cond (P := fun v' => v' = v) (fun _ h => ⟨_, h ▸ hE⟩) ?_ ?_ v rfl
    · -- the dash last: all after the number
      intro v' ⟨hvv, hne'⟩
      rw [hvv] at hne' ⊢
      have hend : d + 1 = w.length := by
        refine Classical.byContradiction fun h => hne' ?_
        rw [hE]; simp [h, bw]
      have hb : w.drop (d + 1) = [] := by simp; omega
      refine Safe.assign (P := fun v' => v' = v) (fun _ h => ?_) v rfl
      subst h
      refine ⟨_, z, rfl, hz, but_set hf (by decide) _, ?_, fun lo hi h => ?_⟩
      · rw [hrange]; simp [setLocal, hok, hb, ha, bw]
      · rw [hrange] at h
        simp only [hb, if_true, ha, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨by simp [setLocal, hlo ha], by simp [setLocal, CommandSpec.numberMax]⟩
    · -- a second number
      intro v' ⟨hvv, he⟩
      rw [hvv] at he ⊢
      have hend : d + 1 ≠ w.length := by
        intro h
        rw [hE] at he
        simp [h, bw] at he
      have hb : w.drop (d + 1) ≠ [] := by simp; omega
      have hse' : ExpAvoids (· ∈ numNames) (afterDash se) := ⟨⟨hse_n, by simp [ExpAvoids, numNames]⟩, trivial⟩
      have hle' : ExpAvoids (· ∈ numNames) (restLen le) := ⟨⟨hle_n, by simp [ExpAvoids, numNames]⟩, trivial⟩
      refine safe_congr h2s (then_ (P := fun v' => v' = v) (M := NumPost (w.drop (d + 1)))
        (P' := fun t => ButFor rngNames u t ∧
          t.locals "ok" = some (bw (CommandSpec.isArticleNumber (w.drop (d + 1)))) ∧
          (∃ x, t.locals "val" = some x) ∧
          (CommandSpec.isArticleNumber (w.drop (d + 1)) = true →
            t.locals "val" = some (BitVec.ofNat 64 (CommandSpec.value (w.drop (d + 1))))) ∧
          t.locals "lo" = some (BitVec.ofNat 64 (CommandSpec.value (w.take d))) ∧ (∃ x, t.locals "hi" = some x))
        (fun v0 => Safe.conseq (numP_safe o _ _ hse' hle' B (S + BitVec.ofNat 64 (d + 1)) _ v0)
          (fun v'' ⟨hv, hv'⟩ => ⟨hv, ?_⟩) (fun _ h => h))
        (numPost_clock _) (fun v0 t hv0 hn => ?_) ?_) v rfl
      · subst hv'
        have hS := eval_but hf hse hpre.se
        have h := numPre_at hpre hf (d + 1) (w.length - (d + 1)) (by omega)
          (se' := afterDash se) (le' := restLen le) (S' := S + BitVec.ofNat 64 (d + 1))
          (by simp only [afterDash, eval, hS, hdp]
              rw [show (1 : Word) = BitVec.ofNat 64 1 from rfl, BitVec.add_assoc, ← BitVec.ofNat_add])
          rfl
          (by simp only [restLen, eval, hL, hdp]
              rw [sub_small _ _ (by omega) (by omega), show (1 : Word) = BitVec.ofNat 64 1 from rfl,
                sub_small _ _ (by omega) (by omega)]
              congr 2)
          ⟨x, hx⟩ ⟨j, hj⟩ ⟨_, hok⟩
        rwa [List.take_of_length_le (by simp)] at h
      · subst hv0
        obtain ⟨hn, hok', hv, _, hval⟩ := hn
        exact ⟨but_trans hf (but_mono hn num_rng), hok', hv, hval,
          by rw [hn.locals "lo" (by decide)]; exact hlo ha,
          by rw [hn.locals "hi" (by decide)]; exact ⟨z, hz⟩⟩
      · refine Safe.assign fun t ⟨hf', hok', ⟨x', hx'⟩, hval', hlo', ⟨z', hz'⟩⟩ =>
          ⟨x', z', by simp [eval, hx'], hz', ?_⟩
        refine ⟨but_set hf' (by decide) _, ?_, fun lo hi h => ?_⟩
        · rw [hrange]; simp [setLocal, hok', hb, ha, bw]
        · rw [hrange] at h
          simp only [hb, if_false, ha, Bool.true_and] at h
          split at h
          · rename_i hn
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            rw [hval' hn] at hx'
            exact ⟨by simp [setLocal, hlo'], by simp [setLocal, Option.some.inj hx']⟩
          · cases h
  · -- no number before the dash: none
    refine Safe.conseq (Safe.skip o _) (fun _ h => h) ?_
    rintro t ⟨⟨hf, hok, _, _, _, _, _⟩, he⟩
    have ha : CommandSpec.isArticleNumber (w.take d) = false := by
      cases h : CommandSpec.isArticleNumber (w.take d)
      · rfl
      · rw [show eval t (.var "ok") = some 1 by simp [eval, hok, h, bw]] at he
        exact absurd (Option.some.inj he) (by decide)
    have hnone : CommandSpec.range? w = none := by rw [hrange]; split <;> simp [ha]
    refine ⟨hf, ?_, fun lo hi h => ?_⟩
    · rw [hnone]; simp [hok, ha, bw]
    · rw [hnone] at h; cases h

/-- **The session's range check is `CommandSpec.range?`**: the word from `se` of length `le` is `w` in the line's
octets. A normally finishing run leaves `ok` whether `w` is a range, its bounds in `lo` and `hi`. It changes no local
but its own nor the memory. -/
theorem rangeCheck_safe (o : Oracle σ) {s l : Syntax.PExpr} {se le : PancakeExp}
    (hs : Lower.lowerExp s = some se) (hl : Lower.lowerExp l = some le)
    (hse : ExpAvoids (· ∈ rngNames) se) (hle : ExpAvoids (· ∈ rngNames) le)
    (B S : Word) (w : List Byte) (s0 : PancakeState σ) :
    ∃ c, Lower.lowerStmtsFold (Session.rangeCheckAt s l) = some c ∧
      Safe.Safe o (fun u => u = s0 ∧ RngPre se le B S w u) c (RngPost w s0) := by
  obtain ⟨t0, t1, t2, hc, h0s, h1s, h2s⟩ := rangeCheck_lower o hs hl
  refine ⟨_, hc, ?_⟩
  rintro u ⟨rfl, hpre⟩
  have hse_d := avoids_mono (fun x hx => dash_rng x hx) se hse
  have hle_d := avoids_mono (fun x hx => dash_rng x hx) le hle
  have hshort := hpre.short
  have hC : w.count dash ≤ w.length := List.count_le_length
  have hD : Safe.Safe o (DashPost w u) (.cond (.cmp .equal (.var "dn") (.const 0)) t0
      (.cond (.cmp .equal (.var "dn") (.const 1)) t1 (.assign "ok" (.const 0)))) (RngPost w u) := by
    intro v hv
    have hv0 := hv
    obtain ⟨hf, _, hdn, dpv, hdp, hfirst⟩ := hv0
    rw [List.take_length] at hdn hfirst
    have hCs : w.count dash < 2 ^ 64 := by omega
    by_cases hz : w.count dash = 0
    · have hE : eval v (.cmp .equal (.var "dn") (.const 0)) = some 1 := by simp [eval, hdn, hz]
      refine Safe.cond (P := fun v' => v' = v) (fun _ h => ⟨1, h ▸ hE⟩) ?_ ?_ v rfl
      · intro v' ⟨hvv, _⟩
        rw [hvv]
        exact safe_congr h0s (range_noDash o hse hle hpre hz) v hv
      · intro v' ⟨hvv, he⟩
        rw [hvv, hE] at he
        exact absurd (Option.some.inj he) (by decide)
    obtain ⟨d, hd, h0, rfl⟩ := hfirst.resolve_left hz
    have hsplit := count_split hd
    have hE0 : eval v (.cmp .equal (.var "dn") (.const 0)) = some 0 := by
      simp only [eval, hdn]
      rw [if_neg (NatToDec.ofNat64_ne_zero hz hCs)]
    refine Safe.cond (P := fun v' => v' = v) (fun _ h => ⟨0, h ▸ hE0⟩) ?_ ?_ v rfl
    · intro v' ⟨hvv, he⟩
      rw [hvv, hE0] at he
      exact absurd rfl he
    intro v' ⟨hvv, _⟩
    rw [hvv]
    by_cases h1 : (w.drop (d + 1)).count dash = 0
    · have hC1 : w.count dash = 1 := by omega
      have hE1 : eval v (.cmp .equal (.var "dn") (.const 1)) = some 1 := by simp [eval, hdn, hC1]
      refine Safe.cond (P := fun v' => v' = v) (fun _ h => ⟨1, h ▸ hE1⟩) ?_ ?_ v rfl
      · intro v' ⟨hvv, _⟩
        rw [hvv]
        exact safe_congr h1s (range_oneDash o hse hle hpre hd h0 h1 h2s) v ⟨hv, hdp⟩
      · intro v' ⟨hvv, he⟩
        rw [hvv, hE1] at he
        exact absurd (Option.some.inj he) (by decide)
    have hE1 : eval v (.cmp .equal (.var "dn") (.const 1)) = some 0 := by
      simp only [eval, hdn]
      rw [if_neg (fun e => ?_)]
      have := NatToDec.ofNat64_inj hCs (by decide : 1 < 2 ^ 64) e
      omega
    have hnone := range_many hd h0 (by omega)
    obtain ⟨x, hx⟩ := hpre.ok
    refine Safe.cond (P := fun v' => v' = v) (fun _ h => ⟨0, h ▸ hE1⟩) ?_ ?_ v rfl
    · intro v' ⟨hvv, he⟩
      rw [hvv, hE1] at he
      exact absurd rfl he
    · refine Safe.assign fun v' ⟨hvv, _⟩ => ?_
      rw [hvv]
      exact ⟨0, x, rfl, (hf.locals "ok" (by decide)).trans hx, but_set (but_mono hf dash_rng) (by decide) _,
        by simp [setLocal, hnone, bw], fun lo hi h => by rw [hnone] at h; cases h⟩
  refine (?_ : Safe.Safe o (fun v => v = u) _ (RngPost w u)) u rfl
  refine Safe.dec (P' := fun v => ButFor dashNames u v ∧ v.locals "dn" = some 0 ∧
      ∃ x, v.locals "jq" = some x) (Q' := RngPost w u) ?_ ?_ (fun _ t _ hq => rngPost_restore hq (by simp) _)
  · rintro v rfl
    obtain ⟨x, hx⟩ := hpre.jq
    exact ⟨0, rfl, but_set (but_refl _ _) (by decide) _, by simp [setLocal], x, by simp [setLocal, hx]⟩
  refine Safe.dec (P' := fun v => ButFor dashNames u v ∧ v.locals "dn" = some 0 ∧ v.locals "dp" = some 0 ∧
      ∃ x, v.locals "jq" = some x) (Q' := RngPost w u) ?_ ?_ (fun _ t _ hq => rngPost_restore hq (by simp) _)
  · rintro v ⟨hf, hdn, x, hjq⟩
    exact ⟨0, rfl, but_set hf (by decide) _, by simp [setLocal, hdn], by simp [setLocal], x,
      by simp [setLocal, hjq]⟩
  refine assign_then (P' := DashInv w u) (fun v ⟨hf, hdn, hdp, x, hjq⟩ => ⟨0, x, rfl, hjq,
    but_set hf (by decide) _, 0, Nat.zero_le _, by simp [setLocal], by simp [setLocal, hdn], 0,
    by simp [setLocal, hdp], Or.inl (by simp)⟩) ?_
  exact Safe.seq (M := DashPost w u)
    (wp_sound o (dashA se le w u) (DashPost w u) (dashPost_clock w u) (dash_vc se le hse_d hle_d hpre))
    hD (dashPost_clock w u)

/-! ## A date and a time -/

/-- The names the date and time check writes. -/
def dtNames : List String := ["ok", "jq"]

/-- The number the two digits at `se + k` write. -/
def twoE (se k : PancakeExp) : PancakeExp :=
  .op .add (.mul (.op .sub (kb se k) (.const 48)) (.const 10)) (.op .sub (kb (.op .add se k) (.const 1)) (.const 48))

/-- An octet of the word: a digit or not, the place moved on. -/
def digBody (se : PancakeExp) : AProg σ :=
  .seq (.assign "ok" (.op .and_ (.cmp .less (.const 47) (kb se (.var "jq")))
      (.cmp .less (kb se (.var "jq")) (.const 58))))
    (.assign "jq" (.op .add (.var "jq") (.const 1)))

/-- The loop's state after `k` octets of `w`, `F` known. `ok` is one while the length is right (`A`) and the octets are
digits. Else zero, and the word is not all digits of a right length. -/
def DigInv (A F : Prop) (w : List Byte) (s0 : PancakeState σ) (t : PancakeState σ) : Prop :=
  ButFor dtNames s0 t ∧ F ∧ ∃ k, k ≤ w.length ∧ t.locals "jq" = some (BitVec.ofNat 64 k) ∧
    ∃ okv, t.locals "ok" = some okv ∧
      ((okv = 1 ∧ A ∧ (w.take k).all CommandSpec.isDigit = true) ∨
        (okv = 0 ∧ ¬ (A ∧ w.all CommandSpec.isDigit = true)))

/-- The time's last test. -/
def timeTest : AProg σ :=
  .cond (.var "ok")
    (.assign "ok" (.op .and_ (.op .and_ (leE (twoE (.var "s2") (.const 0)) (.const 23))
      (leE (twoE (.var "s2") (.const 2)) (.const 59))) (leE (twoE (.var "s2") (.const 4)) (.const 60))))
    .skip

/-- The time, once the date is one. -/
def timeA (w1 w2 : List Byte) (s0 : PancakeState σ) : AProg σ :=
  .seq (.assign "ok" (.cmp .equal (.var "l2") (.const 6)))
  (.seq (.assign "jq" (.const 0))
  (.seq (.while_ (DigInv (w2.length = 6) (CommandSpec.isDate w1 = true) w2 s0)
      (.op .and_ (.var "ok") (.cmp .less (.var "jq") (.var "l2"))) (digBody (.var "s2")))
    timeTest))

/-- The date's century, month and day, then the time. -/
def dateRest (w1 w2 : List Byte) (s0 : PancakeState σ) : AProg σ :=
  .seq (.cond (.cmp .equal (.var "l1") (.const 8))
      (.assign "ok" (.op .and_ (.var "ok") (leE (.const 19) (twoE (.var "s1") (.const 0))))) .skip)
  (.seq (.cond (.var "ok")
      (.assign "ok" (.op .and_ (betweenE 1 12 (twoE (.var "s1") (.op .sub (.var "l1") (.const 4))))
        (betweenE 1 31 (twoE (.var "s1") (.op .sub (.var "l1") (.const 2)))))) .skip)
    (.cond (.var "ok") (timeA w1 w2 s0) .skip))

/-- The check, as it lowers, its loops carrying `DigInv`. -/
def dtA (w1 w2 : List Byte) (s0 : PancakeState σ) : AProg σ :=
  .seq (.assign "ok" (.cmp .less (.const 0)
      (.op .add (.cmp .equal (.var "l1") (.const 6)) (.cmp .equal (.var "l1") (.const 8)))))
  (.seq (.assign "jq" (.const 0))
  (.seq (.while_ (DigInv (w1.length = 6 ∨ w1.length = 8) True w1 s0)
      (.op .and_ (.var "ok") (.cmp .less (.var "jq") (.var "l1"))) (digBody (.var "s1")))
    (dateRest w1 w2 s0)))

theorem dateTimeCheck_lower (w1 w2 : List Byte) (s0 : PancakeState σ) :
    Lower.lowerStmtsFold Session.dateTimeCheck = some (dtA w1 w2 s0).erase := by
  simp [Session.dateTimeCheck, Session.allDigits, Session.twoAt, Session.between, Session.isDigitE,
    Lower.lowerStmtsFold, Lower.lowerStmt1, Lower.lowerExp, Session.kept, SessionStore.or2, SessionStore.ifs,
    SessionStore.inc, Syntax.eAdd, Syntax.eAnd, Syntax.eLe, Syntax.eLt, Syntax.eEq, Syntax.eSub, Syntax.eMul,
    Syntax.n, Syntax.v, dtA, dateRest, timeA, timeTest, digBody, kb, twoE, leE, betweenE, AProg.erase,
    framerHead]

/-- What the check leaves: `ok` whether the words are a date and a time. -/
def DTPost (w1 w2 : List Byte) (s0 : PancakeState σ) (t : PancakeState σ) : Prop :=
  ButFor dtNames s0 t ∧ t.locals "ok" = some (bw (CommandSpec.isDate w1 && CommandSpec.isTime w2))

theorem twoAt_eq (w : List Byte) (j : Nat) (hj : j + 1 < w.length) :
    CommandSpec.twoAt w j = 10 * (w[j].toNat - 48) + (w[j + 1].toNat - 48) := by
  unfold CommandSpec.twoAt
  rw [List.drop_eq_getElem_cons (by omega), List.drop_eq_getElem_cons hj]
  simp only [CommandSpec.value, List.take_succ_cons, List.take_zero, List.foldl_cons, List.foldl_nil]
  omega

theorem two_word (a b : Byte) (ha : CommandSpec.isDigit a = true) (hb : CommandSpec.isDigit b = true) :
    (a.setWidth 64 - 48) * 10 + (b.setWidth 64 - 48) =
      BitVec.ofNat 64 (10 * (a.toNat - 48) + (b.toNat - 48)) := by
  simp only [CommandSpec.isDigit, Bool.and_eq_true, decide_eq_true_eq] at ha hb
  apply BitVec.eq_of_toNat_eq
  rw [Bytes.setWidth8_64, Bytes.setWidth8_64]
  simp only [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_sub, BitVec.toNat_ofNat]
  rw [show (10 : Word) = BitVec.ofNat 64 10 from rfl, show (48 : Word) = BitVec.ofNat 64 48 from rfl,
    BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  have := a.isLt
  have := b.isLt
  rw [Nat.mod_eq_of_lt (by omega : a.toNat < 2 ^ 64), Nat.mod_eq_of_lt (by omega : b.toNat < 2 ^ 64)]
  omega

/-- Two octets of a word read as a number: defined, and for digits their number. -/
theorem two_eval {t : PancakeState σ} {se k : PancakeExp} {B S : Word} {w : List Byte} {j : Nat}
    (hj : j + 1 < w.length) (hB : t.locals "blk" = some B)
    (hA : eval t (.op .add se k) = some (S + BitVec.ofNat 64 j))
    (hbytes : ∀ i (h : i < w.length),
      memLoadByte t.memory t.memaddrs t.be (B + BitVec.ofNat 64 40 + (S + BitVec.ofNat 64 i)) = some w[i]) :
    (∃ x, eval t (twoE se k) = some x) ∧
      (CommandSpec.isDigit w[j] = true → CommandSpec.isDigit w[j + 1] = true →
        eval t (twoE se k) = some (BitVec.ofNat 64 (CommandSpec.twoAt w j))) := by
  have h1 := kb_eval hB hA (hbytes j (by omega))
  have hA2 : eval t (.op .add (.op .add se k) (.const 1)) = some (S + BitVec.ofNat 64 (j + 1)) := by
    simp only [eval] at hA ⊢
    rw [hA]
    simp only
    rw [BitVec.add_assoc, show (1 : Word) = BitVec.ofNat 64 1 from rfl, ← BitVec.ofNat_add]
  have h2 := kb_eval hB hA2 (hbytes (j + 1) hj)
  refine ⟨⟨(w[j].setWidth 64 - 48) * 10 + (w[j + 1].setWidth 64 - 48), by simp only [twoE, eval, h1, h2]⟩,
    fun ha hb => ?_⟩
  simp only [twoE, eval, h1, h2]
  rw [two_word _ _ ha hb, twoAt_eq w j hj]

/-- **An octet of the word, a digit after digits**: the loop goes on. -/
theorem dig_step {A F : Prop} {w : List Byte} {s0 t : PancakeState σ} {x : String} {B S : Word}
    (hf : ButFor dtNames s0 t) (hF : F) (hA : A) (hB : t.locals "blk" = some B)
    (hS : t.locals x = some S)
    (hbytes : ∀ j (h : j < w.length),
      memLoadByte t.memory t.memaddrs t.be (B + BitVec.ofNat 64 40 + (S + BitVec.ofNat 64 j)) = some w[j])
    (k : Nat) (hk : k < w.length) (hjq : t.locals "jq" = some (BitVec.ofNat 64 k))
    (hok : t.locals "ok" = some 1) (hall : (w.take k).all CommandSpec.isDigit = true) :
    wp (digBody (.var x)) (DigInv A F w s0) t := by
  have hE := kb_eval (se := .var x) (k := .var "jq") (j := k) hB (by simp [eval, hS, hjq]) (hbytes k hk)
  have hD : eval t (.op .and_ (.cmp .less (.const 47) (kb (.var x) (.var "jq")))
      (.cmp .less (kb (.var x) (.var "jq")) (.const 58))) = some (bw (CommandSpec.isDigit w[k])) := by
    simp only [eval, hE]
    exact congrArg some (digit_eval _)
  refine wp_seq (M := fun u => u = { t with locals := setLocal t.locals "ok" (bw (CommandSpec.isDigit w[k])) })
    (wp_assign hD hok rfl) ?_
  rintro u rfl
  refine wp_assign (val := BitVec.ofNat 64 (k + 1)) (old := BitVec.ofNat 64 k)
    (by simp [eval, setLocal, hjq, BitVec.ofNat_add]) (by simp [setLocal, hjq]) ?_
  refine ⟨but_set (but_set hf (by decide) _) (by decide) _, hF, k + 1, by omega, by simp [setLocal],
    bw (CommandSpec.isDigit w[k]), by simp [setLocal], ?_⟩
  by_cases hd : CommandSpec.isDigit w[k] = true
  · exact Or.inl ⟨by simp [bw, hd], hA, by rw [List.take_add_one, List.getElem?_eq_getElem hk,
      Option.toList_some, List.all_append, hall, List.all_cons, hd]; rfl⟩
  · refine Or.inr ⟨by simp [bw, hd], fun ⟨_, h⟩ => hd ?_⟩
    rw [List.all_eq_true] at h
    exact h _ (List.getElem_mem hk)

/-- The loop's test: `ok`, while the place is before the end. -/
theorem dig_guard {t : PancakeState σ} {l : String} {okv : Word} {k n : Nat} (hn : n < 2 ^ 62) (hk : k ≤ n)
    (hok : t.locals "ok" = some okv) (hjq : t.locals "jq" = some (BitVec.ofNat 64 k))
    (hl : t.locals l = some (BitVec.ofNat 64 n)) :
    eval t (.op .and_ (.var "ok") (.cmp .less (.var "jq") (.var l))) = some (okv &&& bw (decide (k < n))) := by
  simp only [eval, hok, hjq, hl, WpBytes.signedLt_small (a := k) (b := n) (by omega) (by omega)]
  rfl

/-- What the loop leaves: `ok` whether the length is right and all octets are digits. -/
theorem dig_exit {A : Prop} [Decidable A] {w : List Byte} {t : PancakeState σ} {k : Nat} (hk : k ≤ w.length)
    {okv : Word} (hok : t.locals "ok" = some okv)
    (h : (okv = 1 ∧ A ∧ (w.take k).all CommandSpec.isDigit = true) ∨
      (okv = 0 ∧ ¬ (A ∧ w.all CommandSpec.isDigit = true)))
    (hend : (okv &&& bw (decide (k < w.length))) = 0) :
    t.locals "ok" = some (bw (decide (A ∧ w.all CommandSpec.isDigit = true))) := by
  rcases h with ⟨rfl, hA, hall⟩ | ⟨rfl, hn⟩
  · have hkw : k = w.length := by
      by_cases hlt : k < w.length
      · simp [bw, hlt] at hend
      · omega
    subst hkw
    rw [List.take_length] at hall
    simp [hok, bw, hA, hall]
  · rw [hok, decide_eq_false hn]
    rfl

theorem isDate_iff (w : List Byte) : CommandSpec.isDate w = true ↔
    (w.all CommandSpec.isDigit = true ∧ (w.length = 6 ∨ (w.length = 8 ∧ 19 ≤ CommandSpec.twoAt w 0))) ∧
      (1 ≤ CommandSpec.twoAt w (w.length - 4) ∧ CommandSpec.twoAt w (w.length - 4) ≤ 12 ∧
        1 ≤ CommandSpec.twoAt w (w.length - 2) ∧ CommandSpec.twoAt w (w.length - 2) ≤ 31) := by
  simp only [CommandSpec.isDate, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq, and_assoc]

theorem isTime_iff (w : List Byte) : CommandSpec.isTime w = true ↔
    (w.length = 6 ∧ w.all CommandSpec.isDigit = true) ∧ (CommandSpec.twoAt w 0 ≤ 23 ∧
      CommandSpec.twoAt w 2 ≤ 59 ∧ CommandSpec.twoAt w 4 ≤ 60) := by
  simp only [CommandSpec.isTime, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, and_assoc]

theorem digit_at {w : List Byte} (h : w.all CommandSpec.isDigit = true) (i : Nat) (hi : i < w.length) :
    CommandSpec.isDigit w[i] = true :=
  List.all_eq_true.mp h _ (List.getElem_mem hi)

theorem twoAt_lt {w : List Byte} (h : w.all CommandSpec.isDigit = true) (j : Nat) (hj : j + 1 < w.length) :
    CommandSpec.twoAt w j < 100 := by
  have h1 := digit_at h j (by omega)
  have h2 := digit_at h (j + 1) hj
  simp only [CommandSpec.isDigit, Bool.and_eq_true, decide_eq_true_eq] at h1 h2
  rw [twoAt_eq w j hj]
  omega

/-- **The time's last test**: `ok` whether the words are a date and a time. -/
theorem time_rest {B S1 S2 : Word} {w1 w2 : List Byte} {s0 t : PancakeState σ}
    (hpre : DTPre B S1 S2 w1 w2 s0) (hf : ButFor dtNames s0 t) (hdate : CommandSpec.isDate w1 = true)
    (hok : t.locals "ok" = some (bw (decide (w2.length = 6 ∧ w2.all CommandSpec.isDigit = true)))) :
    wp timeTest (DTPost w1 w2 s0) t := by
  have hB : t.locals "blk" = some B := (hf.locals "blk" (by decide)).trans hpre.blk
  have hS : t.locals "s2" = some S2 := (hf.locals "s2" (by decide)).trans hpre.s2
  have hbytes : ∀ i (h : i < w2.length), memLoadByte t.memory t.memaddrs t.be
      (B + BitVec.ofNat 64 40 + (S2 + BitVec.ofNat 64 i)) = some w2[i] := fun i h => by
    rw [hf.load]; exact hpre.bytes2 i h
  by_cases hd : w2.length = 6 ∧ w2.all CommandSpec.isDigit = true
  · obtain ⟨h6, hall⟩ := hd
    have two : ∀ j, j + 1 < 6 → eval t (twoE (.var "s2") (.const (BitVec.ofNat 64 j))) =
        some (BitVec.ofNat 64 (CommandSpec.twoAt w2 j)) := fun j hj =>
      (two_eval (by omega) hB (by simp [eval, hS]) hbytes).2 (digit_at hall j (by omega))
        (digit_at hall (j + 1) (by omega))
    have t0 := two 0 (by decide)
    have t2 := two 2 (by decide)
    have t4 := two 4 (by decide)
    have l0 := twoAt_lt hall 0 (by omega)
    have l2 := twoAt_lt hall 2 (by omega)
    have l4 := twoAt_lt hall 4 (by omega)
    have ht : CommandSpec.isTime w2 = ((decide (CommandSpec.twoAt w2 0 ≤ 23) && decide (CommandSpec.twoAt w2 2 ≤ 59)) &&
        decide (CommandSpec.twoAt w2 4 ≤ 60)) := by
      simp [CommandSpec.isTime, h6, hall, Bool.and_assoc]
    have hone : bw (decide (w2.length = 6 ∧ w2.all CommandSpec.isDigit = true)) = 1 := by simp [bw, h6, hall]
    refine wp_cond_ne (v := 1) (by simp only [eval, hok, hone]) (by decide) ?_
    refine wp_assign (old := 1) (val := bw ((decide (CommandSpec.twoAt w2 0 ≤ 23) &&
        decide (CommandSpec.twoAt w2 2 ≤ 59)) && decide (CommandSpec.twoAt w2 4 ≤ 60))) ?_
      (by rw [hok, hone]) ?_
    · show eval t (.op .and_ (.op .and_ (leE (twoE (.var "s2") (.const (BitVec.ofNat 64 0)))
          (.const (BitVec.ofNat 64 23))) (leE (twoE (.var "s2") (.const (BitVec.ofNat 64 2)))
          (.const (BitVec.ofNat 64 59)))) (leE (twoE (.var "s2") (.const (BitVec.ofNat 64 4)))
          (.const (BitVec.ofNat 64 60)))) = _
      simp only [leE, eval, t0, t2, t4]
      rw [le_eval _ 23 (by omega) (by decide), le_eval _ 59 (by omega) (by decide),
        le_eval _ 60 (by omega) (by decide), bw_and, bw_and]
    refine ⟨but_set hf (by decide) _, ?_⟩
    simp [setLocal, hdate, ht]
  · have hz : bw (decide (w2.length = 6 ∧ w2.all CommandSpec.isDigit = true)) = 0 := by
      rw [decide_eq_false hd]; rfl
    refine wp_cond_eq (by simp only [eval, hok, hz]) ?_
    refine ⟨hf, ?_⟩
    rw [hok, hz]
    have : CommandSpec.isTime w2 = false := by
      cases h : CommandSpec.isTime w2
      · rfl
      · exact absurd ((isTime_iff w2).mp h).1 hd
    simp [this, bw]

/-- **The time, once the date is one**: its loop starts. -/
theorem time_start {B S1 S2 : Word} {w1 w2 : List Byte} {s0 t : PancakeState σ}
    (hpre : DTPre B S1 S2 w1 w2 s0) (hf : ButFor dtNames s0 t) (hdate : CommandSpec.isDate w1 = true)
    (hok : ∃ x, t.locals "ok" = some x) (hjq : ∃ x, t.locals "jq" = some x) :
    wp (timeA w1 w2 s0) (DTPost w1 w2 s0) t := by
  have hl2 : t.locals "l2" = some (BitVec.ofNat 64 w2.length) := (hf.locals "l2" (by decide)).trans hpre.l2
  have hs := hpre.short2
  have hE : eval t (.cmp .equal (.var "l2") (.const 6)) = some (bw (decide (w2.length = 6))) := by
    simp only [eval, hl2]
    rw [eq_word rfl (show (6 : Word) = BitVec.ofNat 64 6 from rfl) (by omega) (by decide)]
  obtain ⟨x, hx⟩ := hok
  obtain ⟨y, hy⟩ := hjq
  refine wp_seq (M := fun u => u = { t with locals := setLocal t.locals "ok" (bw (decide (w2.length = 6))) })
    (wp_assign hE hx rfl) ?_
  rintro u rfl
  refine wp_seq (M := DigInv (w2.length = 6) (CommandSpec.isDate w1 = true) w2 s0)
    (wp_assign (val := 0) (old := y) rfl (by simp [setLocal, hy]) ?_) (fun u h => h)
  refine ⟨but_set (but_set hf (by decide) _) (by decide) _, hdate, 0, Nat.zero_le _, by simp [setLocal],
    bw (decide (w2.length = 6)), by simp [setLocal], ?_⟩
  by_cases h6 : w2.length = 6
  · exact Or.inl ⟨by simp [bw, h6], h6, by simp⟩
  · exact Or.inr ⟨by simp [bw, h6], fun ⟨h, _⟩ => h6 h⟩

/-- **After the date's octets**: its century, month and day, then the time. -/
theorem date_rest {B S1 S2 : Word} {w1 w2 : List Byte} {s0 t : PancakeState σ}
    (hpre : DTPre B S1 S2 w1 w2 s0) (hf : ButFor dtNames s0 t)
    (hok : t.locals "ok" =
      some (bw (decide ((w1.length = 6 ∨ w1.length = 8) ∧ w1.all CommandSpec.isDigit = true))))
    (hjq : ∃ x, t.locals "jq" = some x) :
    wp (dateRest w1 w2 s0) (DTPost w1 w2 s0) t := by
  have hB : t.locals "blk" = some B := (hf.locals "blk" (by decide)).trans hpre.blk
  have hS : t.locals "s1" = some S1 := (hf.locals "s1" (by decide)).trans hpre.s1
  have hl1 : t.locals "l1" = some (BitVec.ofNat 64 w1.length) := (hf.locals "l1" (by decide)).trans hpre.l1
  have hs := hpre.short1
  have hbytes : ∀ i (h : i < w1.length), memLoadByte t.memory t.memaddrs t.be
      (B + BitVec.ofNat 64 40 + (S1 + BitVec.ofNat 64 i)) = some w1[i] := fun i h => by
    rw [hf.load]; exact hpre.bytes1 i h
  -- the century
  refine wp_seq (M := fun u => ButFor dtNames s0 u ∧ (∃ x, u.locals "jq" = some x) ∧
      u.locals "ok" = some (bw (decide (w1.all CommandSpec.isDigit = true ∧
        (w1.length = 6 ∨ (w1.length = 8 ∧ 19 ≤ CommandSpec.twoAt w1 0)))))) ?_ ?_
  · by_cases h8 : w1.length = 8
    · have hE : eval t (.cmp .equal (.var "l1") (.const 8)) = some 1 := by
        simp only [eval, hl1]
        rw [eq_word rfl (show (8 : Word) = BitVec.ofNat 64 8 from rfl) (by omega) (by decide)]
        simp [h8, bw]
      refine wp_cond_ne hE (by decide) ?_
      obtain ⟨⟨x, hx⟩, hval⟩ := two_eval (se := .var "s1") (j := 0) (k := .const (BitVec.ofNat 64 0))
        (by omega) hB (by simp only [eval, hS]) hbytes
      by_cases hd : w1.all CommandSpec.isDigit = true
      · have hv := hval (digit_at hd 0 (by omega)) (digit_at hd 1 (by omega))
        have hlt := twoAt_lt hd 0 (by omega)
        refine wp_assign (val := bw (decide (19 ≤ CommandSpec.twoAt w1 0))) ?_ hok ?_
        · show eval t (.op .and_ (.var "ok") (leE (.const (BitVec.ofNat 64 19))
            (twoE (.var "s1") (.const (BitVec.ofNat 64 0))))) = _
          simp only [leE, eval, hok, hv]
          rw [le_eval 19 _ (by decide) (by omega)]
          have hone : bw (decide ((w1.length = 6 ∨ w1.length = 8) ∧ w1.all CommandSpec.isDigit = true)) = 1 := by
            simp [h8, hd, bw]
          rw [hone]
          cases decide (19 ≤ CommandSpec.twoAt w1 0) <;> rfl
        · exact ⟨but_set hf (by decide) _, by obtain ⟨y, hy⟩ := hjq; exact ⟨y, by simp [setLocal, hy]⟩,
            by simp [setLocal, h8, hd]⟩
      · refine wp_assign (val := 0) ?_ hok ?_
        · show eval t (.op .and_ (.var "ok") (leE (.const (BitVec.ofNat 64 19))
            (twoE (.var "s1") (.const (BitVec.ofNat 64 0))))) = _
          simp only [leE, eval, hok, hx]
          simp [hd, bw]
        · exact ⟨but_set hf (by decide) _, by obtain ⟨y, hy⟩ := hjq; exact ⟨y, by simp [setLocal, hy]⟩,
            by simp [setLocal, hd, bw]⟩
    · have hE : eval t (.cmp .equal (.var "l1") (.const 8)) = some 0 := by
        simp only [eval, hl1]
        rw [eq_word rfl (show (8 : Word) = BitVec.ofNat 64 8 from rfl) (by omega) (by decide)]
        simp [h8, bw]
      refine wp_cond_eq hE ?_
      refine ⟨hf, hjq, ?_⟩
      rw [hok]
      congr 2
      simp only [h8, false_and, or_false]
      exact decide_eq_decide.mpr ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩
  rintro u ⟨hfu, hjqu, hoku⟩
  have hBu : u.locals "blk" = some B := (hfu.locals "blk" (by decide)).trans hpre.blk
  have hSu : u.locals "s1" = some S1 := (hfu.locals "s1" (by decide)).trans hpre.s1
  have hl1u : u.locals "l1" = some (BitVec.ofNat 64 w1.length) := (hfu.locals "l1" (by decide)).trans hpre.l1
  have hbytesu : ∀ i (h : i < w1.length), memLoadByte u.memory u.memaddrs u.be
      (B + BitVec.ofNat 64 40 + (S1 + BitVec.ofNat 64 i)) = some w1[i] := fun i h => by
    rw [hfu.memory, hfu.memaddrs, hfu.be]; exact hpre.bytes1 i h
  -- the month and the day
  refine wp_seq (M := fun u => ButFor dtNames s0 u ∧ (∃ x, u.locals "jq" = some x) ∧
      u.locals "ok" = some (bw (CommandSpec.isDate w1))) ?_ ?_
  · by_cases hD : w1.all CommandSpec.isDigit = true ∧
        (w1.length = 6 ∨ (w1.length = 8 ∧ 19 ≤ CommandSpec.twoAt w1 0))
    · refine wp_cond_ne (v := 1) (by simp only [eval, hoku]; simp [hD, bw]) (by decide) ?_
      have h6 : 6 ≤ w1.length := by omega
      have hA : ∀ c : Nat, c ≤ 4 → eval u (.op .add (.var "s1") (.op .sub (.var "l1") (.const (BitVec.ofNat 64 c)))) =
          some (S1 + BitVec.ofNat 64 (w1.length - c)) := fun c hc => by
        simp only [eval, hSu, hl1u]
        rw [sub_small _ _ (by omega) (by omega)]
      have hm := (two_eval (j := w1.length - 4) (by omega) hBu (hA 4 (by decide)) hbytesu).2
        (digit_at hD.1 _ (by omega)) (digit_at hD.1 _ (by omega))
      have hd := (two_eval (j := w1.length - 2) (by omega) hBu (hA 2 (by decide)) hbytesu).2
        (digit_at hD.1 _ (by omega)) (digit_at hD.1 _ (by omega))
      have lm := twoAt_lt hD.1 (w1.length - 4) (by omega)
      have ld := twoAt_lt hD.1 (w1.length - 2) (by omega)
      refine wp_assign (val := bw (CommandSpec.isDate w1)) ?_ hoku ?_
      · show eval u (.op .and_ (betweenE (BitVec.ofNat 64 1) (BitVec.ofNat 64 12)
          (twoE (.var "s1") (.op .sub (.var "l1") (.const (BitVec.ofNat 64 4)))))
          (betweenE (BitVec.ofNat 64 1) (BitVec.ofNat 64 31)
          (twoE (.var "s1") (.op .sub (.var "l1") (.const (BitVec.ofNat 64 2)))))) = _
        simp only [betweenE, leE, eval, hm, hd]
        rw [le_eval 1 (CommandSpec.twoAt w1 (w1.length - 4)) (by decide) (by omega),
          le_eval (CommandSpec.twoAt w1 (w1.length - 4)) 12 (by omega) (by decide),
          le_eval 1 (CommandSpec.twoAt w1 (w1.length - 2)) (by decide) (by omega),
          le_eval (CommandSpec.twoAt w1 (w1.length - 2)) 31 (by omega) (by decide),
          bw_and, bw_and, bw_and]
        congr 2
        have hlen : (w1.length == 6 || (w1.length == 8 && decide (19 ≤ CommandSpec.twoAt w1 0))) = true := by
          rcases hD.2 with h | h
          · simp [h]
          · simp [h.1, h.2]
        simp only [CommandSpec.isDate, hD.1, hlen, Bool.true_and, Bool.and_assoc]
      · exact ⟨but_set hfu (by decide) _, by obtain ⟨y, hy⟩ := hjqu; exact ⟨y, by simp [setLocal, hy]⟩,
          by simp [setLocal]⟩
    · have hz : bw (decide (w1.all CommandSpec.isDigit = true ∧
          (w1.length = 6 ∨ (w1.length = 8 ∧ 19 ≤ CommandSpec.twoAt w1 0)))) = 0 := by
        rw [decide_eq_false hD]; rfl
      refine wp_cond_eq (by simp only [eval, hoku, hz]) ?_
      refine ⟨hfu, hjqu, ?_⟩
      rw [hoku, hz]
      have : CommandSpec.isDate w1 = false := by
        cases h : CommandSpec.isDate w1
        · rfl
        · exact absurd ((isDate_iff w1).mp h).1 hD
      simp [this, bw]
  -- the time
  rintro v ⟨hfv, hjqv, hokv⟩
  by_cases hdate : CommandSpec.isDate w1 = true
  · refine wp_cond_ne (v := 1) (by simp only [eval, hokv, hdate]; rfl) (by decide) ?_
    exact time_start hpre hfv hdate ⟨_, hokv⟩ hjqv
  · have hf' : CommandSpec.isDate w1 = false := by simpa using hdate
    refine wp_cond_eq (by simp only [eval, hokv, hf']; rfl) ?_
    exact ⟨hfv, by rw [hokv]; simp [hf', bw]⟩

theorem digInv_clock (A F : Prop) (w : List Byte) (s0 : PancakeState σ) : Safe.ClockFree (DigInv A F w s0) :=
  but_clockFree

theorem dtPost_clock (w1 w2 : List Byte) (s0 : PancakeState σ) : Safe.ClockFree (DTPost w1 w2 s0) :=
  but_clockFree

/-- What the loops ask holds. -/
theorem dt_vc {B S1 S2 : Word} {w1 w2 : List Byte} {s0 : PancakeState σ} (hpre : DTPre B S1 S2 w1 w2 s0) :
    vc (dtA w1 w2 s0) (DTPost w1 w2 s0) := by
  have hs1 := hpre.short1
  have hs2 := hpre.short2
  refine ⟨trivial, trivial, ⟨digInv_clock _ _ _ _, ⟨trivial, trivial⟩, fun t ⟨hf, _, k, hk, hjq, okv, hok, h⟩ => ?_⟩,
    ⟨trivial, trivial⟩, ⟨trivial, trivial⟩, ⟨trivial, trivial, ⟨digInv_clock _ _ _ _, ⟨trivial, trivial⟩,
      fun t ⟨hf, hdate, k, hk, hjq, okv, hok, h⟩ => ?_⟩, trivial, trivial⟩, trivial⟩
  · have hl : t.locals "l1" = some (BitVec.ofNat 64 w1.length) := (hf.locals "l1" (by decide)).trans hpre.l1
    rw [dig_guard hs1 hk hok hjq hl]
    show (if (okv &&& bw (decide (k < w1.length))) = 0 then _ else _)
    by_cases hz : (okv &&& bw (decide (k < w1.length))) = 0
    · rw [if_pos hz]
      exact date_rest hpre hf (dig_exit hk hok h hz) ⟨_, hjq⟩
    · rw [if_neg hz]
      rcases h with ⟨rfl, hA, hall⟩ | ⟨rfl, _⟩
      · have hkl : k < w1.length := by
          refine Classical.byContradiction fun hn => hz ?_
          simp [hn, bw]
        exact dig_step (x := "s1") hf trivial hA
          ((hf.locals "blk" (by decide)).trans hpre.blk) ((hf.locals "s1" (by decide)).trans hpre.s1)
          (fun j hj => by rw [hf.load]; exact hpre.bytes1 j hj) k hkl hjq hok hall
      · exact absurd (by simp) hz
  · have hl : t.locals "l2" = some (BitVec.ofNat 64 w2.length) := (hf.locals "l2" (by decide)).trans hpre.l2
    rw [dig_guard hs2 hk hok hjq hl]
    show (if (okv &&& bw (decide (k < w2.length))) = 0 then _ else _)
    by_cases hz : (okv &&& bw (decide (k < w2.length))) = 0
    · rw [if_pos hz]
      exact time_rest hpre hf hdate (dig_exit hk hok h hz)
    · rw [if_neg hz]
      rcases h with ⟨rfl, hA, hall⟩ | ⟨rfl, _⟩
      · have hkl : k < w2.length := by
          refine Classical.byContradiction fun hn => hz ?_
          simp [hn, bw]
        exact dig_step (x := "s2") hf hdate hA
          ((hf.locals "blk" (by decide)).trans hpre.blk) ((hf.locals "s2" (by decide)).trans hpre.s2)
          (fun j hj => by rw [hf.load]; exact hpre.bytes2 j hj) k hkl hjq hok hall
      · exact absurd (by simp) hz

/-- The check starts with the verdict on the date's length, the place at zero. -/
theorem dt_wp {B S1 S2 : Word} {w1 w2 : List Byte} {s0 : PancakeState σ} (hpre : DTPre B S1 S2 w1 w2 s0) :
    wp (dtA w1 w2 s0) (DTPost w1 w2 s0) s0 := by
  have hs := hpre.short1
  obtain ⟨x, hx⟩ := hpre.ok
  obtain ⟨y, hy⟩ := hpre.jq
  have hE : eval s0 (.cmp .less (.const 0)
      (.op .add (.cmp .equal (.var "l1") (.const 6)) (.cmp .equal (.var "l1") (.const 8)))) =
      some (bw (decide (w1.length = 6 ∨ w1.length = 8))) := by
    simp only [eval, hpre.l1]
    rw [eq_word rfl (show (6 : Word) = BitVec.ofNat 64 6 from rfl) (by omega) (by decide),
      eq_word rfl (show (8 : Word) = BitVec.ofNat 64 8 from rfl) (by omega) (by decide)]
    by_cases h6 : w1.length = 6
    · simp [h6, bw]; decide
    · by_cases h8 : w1.length = 8
      · simp [h8, bw]; decide
      · simp [h6, h8, bw]; decide
  refine wp_seq (M := fun u => u = { s0 with locals :=
    (setLocal s0.locals "ok" (bw (decide (w1.length = 6 ∨ w1.length = 8)))) }) (wp_assign hE hx rfl) ?_
  rintro u rfl
  refine wp_seq (M := DigInv (w1.length = 6 ∨ w1.length = 8) True w1 s0)
    (wp_assign (val := 0) (old := y) rfl (by simp [setLocal, hy]) ?_) (fun u h => h)
  refine ⟨but_set (but_set (but_refl _ _) (by decide) _) (by decide) _, trivial, 0, Nat.zero_le _,
    by simp [setLocal], bw (decide (w1.length = 6 ∨ w1.length = 8)), by simp [setLocal], ?_⟩
  by_cases hl : w1.length = 6 ∨ w1.length = 8
  · exact Or.inl ⟨by simp [bw, hl], hl, by simp⟩
  · exact Or.inr ⟨by simp [bw, hl], fun ⟨h, _⟩ => hl h⟩

/-- **The date and time check is `CommandSpec.isDate` and `CommandSpec.isTime`**: words two and three are `w1` and `w2`.
A normally finishing run leaves `ok` whether they are a date and a time. It changes no local but its own nor the memory.
-/
theorem dateTime_safe (o : Oracle σ) (B S1 S2 : Word) (w1 w2 : List Byte) (s0 : PancakeState σ) :
    Safe.Safe o (fun s => s = s0 ∧ DTPre B S1 S2 w1 w2 s) (dtA w1 w2 s0).erase (DTPost w1 w2 s0) := by
  rintro s ⟨rfl, hpre⟩
  exact wp_sound o _ _ (dtPost_clock w1 w2 s) (dt_vc hpre) s (dt_wp hpre)

/-! ## A newsgroup's name -/

/-- The names `groupName` declares. -/
def gnNames : List String := ["blk", "ok", "nd", "clo", "chi", "jq", "cz"]

/-- The octet the name's loop tests. -/
def czE : PancakeExp := .var "cz"

/-- `wildmat-exact` of US-ASCII, as the session tests an octet. -/
def exactE : PancakeExp :=
  or2E (or2E (or2E (betweenE 34 41 czE) (.cmp .equal czE (.const 43)))
    (or2E (betweenE 45 62 czE) (betweenE 64 90 czE))) (betweenE 94 126 czE)

/-- A continuation octet: in its range or not, one fewer to come, the range reset. -/
def tailA : AProg σ :=
  .seq (.cond (or2E (.cmp .less czE (.var "clo")) (.cmp .less (.var "chi") czE)) (.assign "ok" (.const 0)) .skip)
  (.seq (.assign "nd" (.op .sub (.var "nd") (.const 1)))
  (.seq (.assign "clo" (.const 128)) (.assign "chi" (.const 191))))

/-- A lead octet past US-ASCII: the continuation octets it needs, or `ok` zero. -/
def leadA : AProg σ :=
  .cond (betweenE 194 223 czE) (.assign "nd" (.const 1))
  (.cond (.cmp .equal czE (.const 224)) (.seq (.assign "nd" (.const 2)) (.assign "clo" (.const 160)))
  (.cond (or2E (betweenE 225 236 czE) (betweenE 238 239 czE)) (.assign "nd" (.const 2))
  (.cond (.cmp .equal czE (.const 237)) (.seq (.assign "nd" (.const 2)) (.assign "chi" (.const 159)))
  (.cond (.cmp .equal czE (.const 240)) (.seq (.assign "nd" (.const 3)) (.assign "clo" (.const 144)))
  (.cond (betweenE 241 243 czE) (.assign "nd" (.const 3))
  (.cond (.cmp .equal czE (.const 244)) (.seq (.assign "nd" (.const 3)) (.assign "chi" (.const 143)))
    (.assign "ok" (.const 0))))))))

/-- An octet of the name. -/
def gnBody : AProg σ :=
  .dec "cz" (kb (.var "s1") (.var "jq"))
    (.seq (.cond (.cmp .less (.const 0) (.var "nd")) tailA
        (.cond (.cmp .less czE (.const 128)) (.assign "ok" exactE) leadA))
      (.assign "jq" (.op .add (.var "jq") (.const 1))))

/-- The loop's state after `k` octets of name `w`: `nd` continuation octets to come, the next from `lo` to `hi`. `ok` is
one while the octets left decide as the whole name does, else zero and `w` no name. -/
def GnInv (B : Word) (w : List Byte) (s0 : PancakeState σ) (t : PancakeState σ) : Prop :=
  ButFor gnNames s0 t ∧ t.locals "blk" = some B ∧ ∃ k nd lo hi okv, k ≤ w.length ∧
    t.locals "jq" = some (BitVec.ofNat 64 k) ∧ t.locals "nd" = some (BitVec.ofNat 64 nd) ∧
    t.locals "clo" = some (BitVec.ofNat 64 lo) ∧ t.locals "chi" = some (BitVec.ofNat 64 hi) ∧
    t.locals "ok" = some okv ∧ nd ≤ 3 ∧ lo < 256 ∧ hi < 256 ∧ (nd = 0 → lo = 128 ∧ hi = 191) ∧
    ((okv = 1 ∧ (bRun gAsc gMulti () nd lo hi (w.drop k)).isSome = CommandSpec.isGroupName w) ∨
      (okv = 0 ∧ CommandSpec.isGroupName w = false))

/-- Where `groupName` finds the framer's block, and the return word, as it computes them. -/
def blkSrc : Syntax.PExpr := Syntax.atOff (Session.record (Syntax.v "c")) cFramer

def retSrc : Syntax.PExpr := SessionStore.at_ (ownOff + ownRet)

-- Kept folded: unfolding the layout's offsets overflows the recursion depth.
@[irreducible] def blkE : PancakeExp := (Lower.lowerExp blkSrc).getD (.const 0)

def retE : PancakeExp := (Lower.lowerExp retSrc).getD (.const 0)

theorem blk_lower : Lower.lowerExp blkSrc = some blkE := by
  unfold blkE blkSrc Syntax.atOff Session.record SessionStore.at_ Syntax.atOff
  split <;> split <;> rfl

theorem ret_lower : Lower.lowerExp retSrc = some retE := by
  unfold retE retSrc SessionStore.at_ Syntax.atOff
  split <;> rfl

/-- `groupName`'s locals after the block and its loop, as they lower, the loop carrying `GnInv`. -/
def gnInner (B : Word) (w : List Byte) (s0 : PancakeState σ) : AProg σ :=
  .dec "ok" (leE (.const 1) (.var "l1"))
  (.dec "nd" (.const 0) (.dec "clo" (.const 128) (.dec "chi" (.const 191) (.dec "jq" (.const 0)
    (.seq (.while_ (GnInv B w s0) (.op .and_ (.var "ok") (.cmp .less (.var "jq") (.var "l1"))) gnBody)
    (.seq (.cond (.cmp .less (.const 0) (.var "nd")) (.assign "ok" (.const 0)) .skip)
    (.seq (.store retE (.var "ok")) (.ret (.const 0)))))))))

/-- …and the block first. -/
def gnDecs (B : Word) (w : List Byte) (s0 : PancakeState σ) : AProg σ := .dec "blk" blkE (gnInner B w s0)

/-- `groupName`, as it lowers: its words checked, then the rest. -/
def gnA (B : Word) (w : List Byte) (s0 : PancakeState σ) : AProg σ :=
  .seq (SessionRun.keptA (.var "c") (conns - 1))
  (.seq (SessionRun.keptA (.var "s1") News.SessionSpec.lineLimit)
  (.seq (SessionRun.keptA (.var "l1") News.SessionSpec.lineLimit) (gnDecs B w s0)))

theorem groupName_lower (B : Word) (w : List Byte) (s0 : PancakeState σ) :
    Lower.lower Session.groupName = some (gnA B w s0).erase := by
  have hk1 := SessionRun.keptIn_lower (e := Syntax.v "c") rfl (conns - 1)
  have hk2 := SessionRun.keptIn_lower (e := Syntax.v "s1") rfl News.SessionSpec.lineLimit
  have hk3 := SessionRun.keptIn_lower (e := Syntax.v "l1") rfl News.SessionSpec.lineLimit
  have hb : Lower.lowerExp (Syntax.atOff (Session.record (Syntax.PExpr.var "c")) cFramer) = some blkE := blk_lower
  have hr : Lower.lowerExp (SessionStore.at_ (ownOff + ownRet)) = some retE := ret_lower
  have hin : Lower.lowerStmtsFold (Session.groupName.body.drop 4) = some (gnInner (σ := σ) B w s0).erase := by
    simp [Session.groupName, SessionStore.give, Lower.lowerStmtsFold, Lower.lowerStmt1, Lower.lowerExp, hr,
      Session.utf8Tail, Session.utf8Lead, Session.isExactE, Session.between, Session.kept,
      SessionStore.or2, SessionStore.ifs, SessionStore.inc, Syntax.eAdd, Syntax.eAnd, Syntax.eLe, Syntax.eLt,
      Syntax.eEq, Syntax.eSub, Syntax.n, Syntax.v, gnInner, gnBody, tailA, leadA, exactE, or2E, czE,
      kb, leE, betweenE, AProg.erase, framerHead]
  have e4 : Session.groupName.body.drop 3 =
      .dec "blk" (Syntax.atOff (Session.record (Syntax.PExpr.var "c")) cFramer) ::
        Session.groupName.body.drop 4 := rfl
  have hrest : Lower.lowerStmtsFold (Session.groupName.body.drop 3) = some (gnDecs (σ := σ) B w s0).erase := by
    rw [e4]
    exact Block.fold_dec hb (by simp [Session.groupName]) hin
  have e : Session.groupName.body = SessionStore.keptIn (Syntax.v "c") (conns - 1) ::
      SessionStore.keptIn (Syntax.v "s1") News.SessionSpec.lineLimit ::
      SessionStore.keptIn (Syntax.v "l1") News.SessionSpec.lineLimit :: Session.groupName.body.drop 3 := rfl
  have hl := Block.fold_cons hk1 rfl (by simp) (Block.fold_cons hk2 rfl (by simp)
    (Block.fold_cons hk3 rfl (by simp [Session.groupName]) hrest))
  rw [Lower.lower, e, hl]
  rfl

/-- `wildmat-exact` of US-ASCII, as a number's test. -/
theorem exact_eval {t : PancakeState σ} {x : Nat} (hx : x < 256)
    (hcz : t.locals "cz" = some (BitVec.ofNat 64 x)) :
    eval t exactE = some (bw (CommandSpec.isExactAscii (BitVec.ofNat 8 x))) := by
  have he : eval t czE = some (BitVec.ofNat 64 x) := hcz
  have hx' : x < 2 ^ 63 := by omega
  rw [exactE, eval_or2 (eval_or2 (eval_or2
      (eval_between (L := 34) (H := 41) (lo := 34) (hi := 41) hx' (by decide) (by decide) he rfl rfl)
      (eval_eq (y := 43) (by omega) (by decide) he (eval_const (c := 43) rfl)))
    (eval_or2 (eval_between (L := 45) (H := 62) (lo := 45) (hi := 62) hx' (by decide) (by decide) he rfl rfl)
      (eval_between (L := 64) (H := 90) (lo := 64) (hi := 90) hx' (by decide) (by decide) he rfl rfl)))
    (eval_between (L := 94) (H := 126) (lo := 94) (hi := 126) hx' (by decide) (by decide) he rfl rfl)]
  congr 2
  simp only [CommandSpec.isExactAscii, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hx]
  rw [Bool.eq_iff_iff]
  simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
  omega

/-- **A continuation octet**: `ok` zero when it is out of its range, one fewer to come, the range
reset. -/
theorem tail_wp {t : PancakeState σ} {R : Ret} {Q : Assn σ} {x n lo hi : Nat} {okv : Word}
    (hx : x < 256) (hlo : lo < 256) (hhi : hi < 256) (hn : 1 ≤ n) (hn4 : n ≤ 3)
    (hcz : t.locals "cz" = some (BitVec.ofNat 64 x)) (hnd : t.locals "nd" = some (BitVec.ofNat 64 n))
    (hclo : t.locals "clo" = some (BitVec.ofNat 64 lo)) (hchi : t.locals "chi" = some (BitVec.ofNat 64 hi))
    (hok : t.locals "ok" = some okv)
    (hQ : ∀ u : PancakeState σ, ButFor ["ok", "nd", "clo", "chi"] t u →
      u.locals "nd" = some (BitVec.ofNat 64 (n - 1)) → u.locals "clo" = some (BitVec.ofNat 64 128) →
      u.locals "chi" = some (BitVec.ofNat 64 191) →
      u.locals "ok" = some (if x < lo ∨ hi < x then 0 else okv) → Q u) :
    wpR tailA R Q t := by
  have htest := eval_or2 (eval_lt (a := czE) (b := .var "clo") (by omega) (by omega) hcz hclo)
    (eval_lt (a := .var "chi") (b := czE) (by omega) (by omega) hchi hcz)
  refine wpR_seq (M := fun u => ButFor ["ok", "nd", "clo", "chi"] t u ∧
    u.locals "ok" = some (if x < lo ∨ hi < x then 0 else okv) ∧ u.locals "nd" = t.locals "nd" ∧
    u.locals "clo" = t.locals "clo" ∧ u.locals "chi" = t.locals "chi") ?_ ?_
  · by_cases hout : x < lo ∨ hi < x
    · refine wpR_cond_ne htest (by simp [bw, hout]) (wpR_assign (val := 0) rfl hok ?_)
      exact ⟨but_set (but_refl _ _) (by simp) _, by simp [setLocal, hout], by simp [setLocal],
        by simp [setLocal], by simp [setLocal]⟩
    · refine wpR_cond_eq (by rw [htest]; simp [bw, hout]) ?_
      exact ⟨but_refl _ _, by simp [hout, hok], rfl, rfl, rfl⟩
  rintro u ⟨hfu, hoku, hndu, hclou, hchiu⟩
  rw [hnd] at hndu
  refine wpR_seq (M := fun v => v = { u with locals := setLocal u.locals "nd" (BitVec.ofNat 64 (n - 1)) })
    (wpR_assign (by simp only [eval, hndu]; exact congrArg some (sub_small n 1 hn (by omega))) hndu rfl) ?_
  rintro v rfl
  refine wpR_seq (M := fun v' => v' = { u with locals := (setLocal (setLocal u.locals "nd"
    (BitVec.ofNat 64 (n - 1))) "clo" 128) })
    (wpR_assign (old := BitVec.ofNat 64 lo) rfl (by simp [setLocal, hclou, hclo]) rfl) ?_
  rintro v rfl
  refine wpR_assign (val := 191) (old := BitVec.ofNat 64 hi) rfl (by simp [setLocal, hchiu, hchi])
    (hQ _ ?_ ?_ ?_ ?_ ?_)
  · exact but_set (but_set (but_set hfu (by simp) _) (by simp) _) (by simp) _
  · simp [setLocal]
  · simp [setLocal]
  · simp [setLocal]
  · simp [setLocal, hoku]

/-- What a lead octet leaves: its continuation octets and their first's range, or `ok` zero. -/
def LeadOut (x : Nat) (okv : Word) (u : PancakeState σ) : Prop :=
  match lead (BitVec.ofNat 8 x) with
  | some (n, lo, hi) => u.locals "ok" = some okv ∧ u.locals "nd" = some (BitVec.ofNat 64 n) ∧
      u.locals "clo" = some (BitVec.ofNat 64 lo) ∧ u.locals "chi" = some (BitVec.ofNat 64 hi)
  | none => u.locals "ok" = some 0 ∧ u.locals "nd" = some (BitVec.ofNat 64 0) ∧
      u.locals "clo" = some (BitVec.ofNat 64 128) ∧ u.locals "chi" = some (BitVec.ofNat 64 191)

/-- **A lead octet past US-ASCII**: as `lead` reads it. -/
theorem lead_wp {t : PancakeState σ} {R : Ret} {Q : Assn σ} {x : Nat} {okv : Word}
    (hx1 : 128 ≤ x) (hx : x < 256) (hcz : t.locals "cz" = some (BitVec.ofNat 64 x))
    (hnd : t.locals "nd" = some (BitVec.ofNat 64 0)) (hclo : t.locals "clo" = some (BitVec.ofNat 64 128))
    (hchi : t.locals "chi" = some (BitVec.ofNat 64 191)) (hok : t.locals "ok" = some okv)
    (hQ : ∀ u : PancakeState σ, ButFor ["ok", "nd", "clo", "chi"] t u → LeadOut x okv u → Q u) :
    wpR leadA R Q t := by
  have he : eval t czE = some (BitVec.ofNat 64 x) := hcz
  have hx' : x < 2 ^ 63 := by omega
  have hb : (BitVec.ofNat 8 x).toNat = x := by simp [Nat.mod_eq_of_lt hx]
  have fr : ∀ (y : String), y ∈ ["ok", "nd", "clo", "chi"] → ∀ w,
      ButFor ["ok", "nd", "clo", "chi"] t { t with locals := setLocal t.locals y w } :=
    fun y hy w => but_set (but_refl _ _) hy w
  have two : ∀ (z : String) (a b : Word) (old : Value), t.locals z = some old → z ≠ "nd" →
      z ∈ ["ok", "nd", "clo", "chi"] →
      LeadOut x okv { t with locals := setLocal (setLocal t.locals "nd" a) z b } →
      wpR (.seq (.assign "nd" (.const a)) (.assign z (.const b))) R Q t := by
    intro z a b old hz hzn hzm hq
    refine wpR_seq (M := fun u => u = { t with locals := setLocal t.locals "nd" a }) (wpR_assign rfl hnd rfl) ?_
    rintro u rfl
    exact wpR_assign (old := old) rfl (by simp [setLocal, hzn, hz]) (hQ _ (but_set (fr "nd" (by simp) a) hzm b) hq)
  have btw : ∀ lo hi : Nat, lo < 256 → hi < 256 → eval t (betweenE (BitVec.ofNat 64 lo) (BitVec.ofNat 64 hi) czE) =
      some (bw (decide (lo ≤ x ∧ x ≤ hi))) := fun lo hi hlo hhi =>
    eval_between hx' (by omega) (by omega) he rfl rfl
  have eqc : ∀ c : Nat, c < 256 → eval t (.cmp .equal czE (.const (BitVec.ofNat 64 c))) =
      some (bw (decide (x = c))) := fun c hc => eval_eq (by omega) (by omega) he (eval_const rfl)
  have ne0 : ∀ {p : Prop} [Decidable p], p → bw (decide p) ≠ 0 := fun h => by simp [bw, h]
  have eq0 : ∀ {p : Prop} [Decidable p], ¬ p → bw (decide p) = 0 := fun h => by simp [bw, h]
  -- 194 to 223: one to come
  by_cases c1 : 194 ≤ x ∧ x ≤ 223
  · refine wpR_cond_ne (btw 194 223 (by decide) (by decide)) (ne0 c1)
      (wpR_assign (val := 1) rfl hnd (hQ _ (fr "nd" (by simp) _) ?_))
    have : lead (BitVec.ofNat 8 x) = some (1, 128, 191) := by rw [lead, hb, if_pos c1]
    simp only [LeadOut, this]
    exact ⟨by simp [setLocal, hok], by simp [setLocal], by simp [setLocal, hclo], by simp [setLocal, hchi]⟩
  refine wpR_cond_eq ((btw 194 223 (by decide) (by decide)).trans (congrArg some (eq0 c1))) ?_
  -- 224: two to come, the first from 160
  by_cases c2 : x = 224
  · refine wpR_cond_ne (eqc 224 (by decide)) (ne0 c2) (two "clo" 2 160 _ hclo (by decide) (by simp) ?_)
    have : lead (BitVec.ofNat 8 x) = some (2, 160, 191) := by rw [lead, hb, if_neg c1, if_pos c2]
    simp only [LeadOut, this]
    exact ⟨by simp [setLocal, hok], by simp [setLocal], by simp [setLocal], by simp [setLocal, hchi]⟩
  refine wpR_cond_eq ((eqc 224 (by decide)).trans (congrArg some (eq0 c2))) ?_
  -- 225 to 236 and 238 to 239: two to come
  have t3 := eval_or2 (btw 225 236 (by decide) (by decide)) (btw 238 239 (by decide) (by decide))
  by_cases c3 : (225 ≤ x ∧ x ≤ 236) ∨ (238 ≤ x ∧ x ≤ 239)
  · refine wpR_cond_ne t3 (by rcases c3 with h | h <;> simp [bw, h])
      (wpR_assign (val := 2) rfl hnd (hQ _ (fr "nd" (by simp) _) ?_))
    have : lead (BitVec.ofNat 8 x) = some (2, 128, 191) := by rw [lead, hb, if_neg c1, if_neg c2, if_pos c3]
    simp only [LeadOut, this]
    exact ⟨by simp [setLocal, hok], by simp [setLocal], by simp [setLocal, hclo], by simp [setLocal, hchi]⟩
  have c3' := not_or.mp c3
  refine wpR_cond_eq (t3.trans (congrArg some (by simp [bw, c3'.1, c3'.2]))) ?_
  -- 237: two to come, the first to 159
  by_cases c4 : x = 237
  · refine wpR_cond_ne (eqc 237 (by decide)) (ne0 c4) (two "chi" 2 159 _ hchi (by decide) (by simp) ?_)
    have : lead (BitVec.ofNat 8 x) = some (2, 128, 159) := by rw [lead, hb, if_neg c1, if_neg c2, if_neg c3, if_pos c4]
    simp only [LeadOut, this]
    exact ⟨by simp [setLocal, hok], by simp [setLocal], by simp [setLocal, hclo], by simp [setLocal]⟩
  refine wpR_cond_eq ((eqc 237 (by decide)).trans (congrArg some (eq0 c4))) ?_
  -- 240: three to come, the first from 144
  by_cases c5 : x = 240
  · refine wpR_cond_ne (eqc 240 (by decide)) (ne0 c5) (two "clo" 3 144 _ hclo (by decide) (by simp) ?_)
    have : lead (BitVec.ofNat 8 x) = some (3, 144, 191) := by
      rw [lead, hb, if_neg c1, if_neg c2, if_neg c3, if_neg c4, if_pos c5]
    simp only [LeadOut, this]
    exact ⟨by simp [setLocal, hok], by simp [setLocal], by simp [setLocal], by simp [setLocal, hchi]⟩
  refine wpR_cond_eq ((eqc 240 (by decide)).trans (congrArg some (eq0 c5))) ?_
  -- 241 to 243: three to come
  by_cases c6 : 241 ≤ x ∧ x ≤ 243
  · refine wpR_cond_ne (btw 241 243 (by decide) (by decide)) (ne0 c6)
      (wpR_assign (val := 3) rfl hnd (hQ _ (fr "nd" (by simp) _) ?_))
    have : lead (BitVec.ofNat 8 x) = some (3, 128, 191) := by
      rw [lead, hb, if_neg c1, if_neg c2, if_neg c3, if_neg c4, if_neg c5, if_pos c6]
    simp only [LeadOut, this]
    exact ⟨by simp [setLocal, hok], by simp [setLocal], by simp [setLocal, hclo], by simp [setLocal, hchi]⟩
  refine wpR_cond_eq ((btw 241 243 (by decide) (by decide)).trans (congrArg some (eq0 c6))) ?_
  -- 244: three to come, the first to 143
  by_cases c7 : x = 244
  · refine wpR_cond_ne (eqc 244 (by decide)) (ne0 c7) (two "chi" 3 143 _ hchi (by decide) (by simp) ?_)
    have : lead (BitVec.ofNat 8 x) = some (3, 128, 143) := by
      rw [lead, hb, if_neg c1, if_neg c2, if_neg c3, if_neg c4, if_neg c5, if_neg c6, if_pos c7]
    simp only [LeadOut, this]
    exact ⟨by simp [setLocal, hok], by simp [setLocal], by simp [setLocal, hclo], by simp [setLocal]⟩
  refine wpR_cond_eq ((eqc 244 (by decide)).trans (congrArg some (eq0 c7))) ?_
  -- any other: not UTF-8
  refine wpR_assign (val := 0) rfl hok (hQ _ (fr "ok" (by simp) _) ?_)
  have : lead (BitVec.ofNat 8 x) = none := by
    rw [lead, hb, if_neg c1, if_neg c2, if_neg c3, if_neg c4, if_neg c5, if_neg c6, if_neg c7]
  simp only [LeadOut, this]
  exact ⟨by simp [setLocal], by simp [setLocal, hnd], by simp [setLocal, hclo], by simp [setLocal, hchi]⟩

theorem blk_eval {s : PancakeState σ} {b : Word} {ci : Nat} (hb : s.baseAddr = b)
    (hc : s.locals "c" = some (BitVec.ofNat 64 ci)) : eval s blkE = some (gnBlock b ci) := by
  unfold blkE blkSrc gnBlock Syntax.atOff Session.record SessionStore.at_ Syntax.atOff
  by_cases h1 : (cFramer == 0) = true <;> by_cases h2 : (tableOff == 0) = true <;>
    simp only [h1, h2, Bool.false_eq_true, ↓reduceIte, Lower.lowerExp, Syntax.eAdd, Syntax.eMul, Syntax.n,
      Syntax.v, Option.getD_some, eval, hb, hc]
  · rw [beq_iff_eq.mp h1, beq_iff_eq.mp h2, BitVec.add_zero, BitVec.add_zero]
  · rw [beq_iff_eq.mp h1, BitVec.add_zero]
  · rw [beq_iff_eq.mp h2, BitVec.add_zero]

theorem ret_eval {s : PancakeState σ} {b : Word} (hb : s.baseAddr = b) : eval s retE = some (retW b) := by
  unfold retE retSrc retW SessionStore.at_ Syntax.atOff
  by_cases h1 : (ownOff + ownRet == 0) = true <;>
    simp only [h1, Bool.false_eq_true, ↓reduceIte, Lower.lowerExp, Syntax.eAdd, Syntax.n, Option.getD_some, eval,
      hb]
  rw [beq_iff_eq.mp h1, BitVec.add_zero]

/-- `groupName`'s ending: `ok` in the return word, zero returned. -/
def gnRet (b : Word) (w : List Byte) (m0 : Word → Word) : Ret :=
  fun v m => v = 0 ∧ m (retW b) = bw (CommandSpec.isGroupName w) ∧ ∀ a, a ≠ retW b → m a = m0 a

/-- After an octet's test: the name's locals, the place not yet moved on. -/
def GnMid (B : Word) (w : List Byte) (s0 : PancakeState σ) (k : Nat) (u : PancakeState σ) : Prop :=
  ButFor gnNames s0 u ∧ u.locals "blk" = some B ∧ u.locals "jq" = some (BitVec.ofNat 64 k) ∧
    ∃ nd lo hi okv, u.locals "nd" = some (BitVec.ofNat 64 nd) ∧
    u.locals "clo" = some (BitVec.ofNat 64 lo) ∧ u.locals "chi" = some (BitVec.ofNat 64 hi) ∧
    u.locals "ok" = some okv ∧ nd ≤ 3 ∧ lo < 256 ∧ hi < 256 ∧ (nd = 0 → lo = 128 ∧ hi = 191) ∧
    ((okv = 1 ∧ (bRun gAsc gMulti () nd lo hi (w.drop (k + 1))).isSome = CommandSpec.isGroupName w) ∨
      (okv = 0 ∧ CommandSpec.isGroupName w = false))

/-- **An octet of the name, the octets so far deciding as the whole name**: the loop goes on. -/
theorem gn_step {b : Word} {ci S : Nat} {w : List Byte} {s0 t : PancakeState σ} {R : Ret}
    (hpre : GnPre b ci S w s0) (hf : ButFor gnNames s0 t) (hblk : t.locals "blk" = some (gnBlock b ci))
    {k nd lo hi : Nat} (hk : k < w.length) (hjq : t.locals "jq" = some (BitVec.ofNat 64 k))
    (hnd : t.locals "nd" = some (BitVec.ofNat 64 nd)) (hclo : t.locals "clo" = some (BitVec.ofNat 64 lo))
    (hchi : t.locals "chi" = some (BitVec.ofNat 64 hi)) (hok : t.locals "ok" = some 1)
    (hnd3 : nd ≤ 3) (hlo : lo < 256) (hhi : hi < 256) (hz : nd = 0 → lo = 128 ∧ hi = 191)
    (hv : (bRun gAsc gMulti () nd lo hi (w.drop k)).isSome = CommandSpec.isGroupName w) :
    wpR gnBody R (GnInv (gnBlock b ci) w s0) t := by
  have hx : w[k].toNat < 256 := w[k].isLt
  have hS : t.locals "s1" = some (BitVec.ofNat 64 S) := (hf.locals "s1" (by decide)).trans hpre.s1
  have hbyte : eval t (kb (.var "s1") (.var "jq")) = some (BitVec.ofNat 64 w[k].toNat) := by
    rw [kb_eval (S := BitVec.ofNat 64 S) (j := k) hblk (by simp [eval, hS, hjq])
      (by rw [hf.load]; exact hpre.bytes k hk), Bytes.setWidth8_64]
  have hw8 : BitVec.ofNat 8 w[k].toNat = w[k] := by simp
  rw [List.drop_eq_getElem_cons hk] at hv
  refine wpR_dec hbyte ?_
  -- the state with the octet
  let t1 : PancakeState σ := { t with locals := setLocal t.locals "cz" (BitVec.ofNat 64 w[k].toNat) }
  have l1 : ∀ y, y ≠ "cz" → t1.locals y = t.locals y := fun y hy => by simp [t1, setLocal, hy]
  have hf1 : ButFor gnNames s0 t1 := but_set hf (by decide) _
  have hcz1 : t1.locals "cz" = some (BitVec.ofNat 64 w[k].toNat) := by simp [t1, setLocal]
  have hnd1 := (l1 "nd" (by decide)).trans hnd
  have hclo1 := (l1 "clo" (by decide)).trans hclo
  have hchi1 := (l1 "chi" (by decide)).trans hchi
  have hok1 := (l1 "ok" (by decide)).trans hok
  have hjq1 := (l1 "jq" (by decide)).trans hjq
  have hblk1 := (l1 "blk" (by decide)).trans hblk
  -- after the octet's test, the place moved on and the octet's local ended
  refine wpR_seq (M := GnMid (gnBlock b ci) w s0 k) ?_ ?_
  rotate_left
  · rintro u ⟨hfu, hblku, hjqu, nd', lo', hi', okv, hndu, hclou, hchiu, hoku, h3, hl, hh, hz', hv'⟩
    refine wpR_assign (val := BitVec.ofNat 64 (k + 1)) (by simp [eval, hjqu, BitVec.ofNat_add]) hjqu ?_
    refine ⟨but_restore (but_set hfu (by decide) _) (by decide) _, by simp [restore, resVar, setLocal, hblku],
      k + 1, nd', lo', hi', okv, by omega, by simp [restore, resVar, setLocal],
      by simp [restore, resVar, setLocal, hndu], by simp [restore, resVar, setLocal, hclou],
      by simp [restore, resVar, setLocal, hchiu], by simp [restore, resVar, setLocal, hoku], h3, hl, hh, hz', hv'⟩
  -- what the octet does
  have ho : ∀ u : PancakeState σ, ButFor ["ok", "nd", "clo", "chi"] t1 u → ButFor gnNames s0 u ∧
      u.locals "blk" = some (gnBlock b ci) ∧ u.locals "jq" = some (BitVec.ofNat 64 k) := fun u hu =>
    ⟨but_trans hf1 (but_mono hu (by decide)), (hu.locals "blk" (by decide)).trans hblk1,
      (hu.locals "jq" (by decide)).trans hjq1⟩
  have htest := eval_lt (a := .const 0) (b := .var "nd") (x := 0) (y := nd) (by decide) (by omega) rfl hnd1
  by_cases hpos : 0 < nd
  · -- a continuation octet
    refine wpR_cond_ne htest (by simp [bw, hpos]) (tail_wp hx hlo hhi hpos hnd3 hcz1 hnd1 hclo1 hchi1 hok1 ?_)
    intro u hu hndu hclou hchiu hoku
    obtain ⟨hfu, hblku, hjqu⟩ := ho u hu
    simp only [bRun, hpos, if_true] at hv
    refine ⟨hfu, hblku, hjqu, nd - 1, 128, 191, _, hndu, hclou, hchiu, hoku, by omega, by decide, by decide,
      fun _ => ⟨rfl, rfl⟩, ?_⟩
    by_cases hout : w[k].toNat < lo ∨ hi < w[k].toNat
    · rw [if_pos hout] at hv ⊢
      exact Or.inr ⟨rfl, hv.symm⟩
    · rw [if_neg hout] at hv ⊢
      exact Or.inl ⟨rfl, hv⟩
  obtain ⟨rfl, rfl⟩ := hz (by omega)
  have hn0 : nd = 0 := by omega
  subst hn0
  refine wpR_cond_eq (htest.trans (by simp [bw])) ?_
  have hlt := eval_lt (a := czE) (b := .const 128) (x := w[k].toNat) (y := 128) (by omega) (by decide) hcz1
    (eval_const rfl)
  by_cases hascii : w[k].toNat < 128
  · -- US-ASCII
    refine wpR_cond_ne hlt (by simp [bw, hascii]) (wpR_assign (exact_eval hx hcz1) hok1 ?_)
    obtain ⟨hfu, hblku, hjqu⟩ := ho _ (but_set (x := "ok") (but_refl _ _) (by simp) _)
    simp only [bRun, Nat.lt_irrefl, if_false, hascii, if_true, gAsc] at hv
    rw [hw8]
    refine ⟨hfu, hblku, hjqu, 0, 128, 191, bw (CommandSpec.isExactAscii w[k]), by simp [setLocal, hnd],
      by simp [setLocal, hclo],
      by simp [setLocal, hchi], by simp [setLocal], by decide, by decide, by decide, fun _ => ⟨rfl, rfl⟩, ?_⟩
    cases he : CommandSpec.isExactAscii w[k]
    · rw [he] at hv
      exact Or.inr ⟨rfl, hv.symm⟩
    · rw [he] at hv
      exact Or.inl ⟨rfl, hv⟩
  · -- a lead octet
    refine wpR_cond_eq (hlt.trans (by simp [bw, hascii])) ?_
    refine lead_wp (by omega) hx hcz1 hnd1 hclo1 hchi1 hok1 fun u hu hout => ?_
    obtain ⟨hfu, hblku, hjqu⟩ := ho u hu
    simp only [bRun, Nat.lt_irrefl, if_false, hascii] at hv
    simp only [LeadOut] at hout
    rw [hw8] at hout
    cases hl : lead w[k] with
    | none =>
      rw [hl] at hout
      simp only [hl] at hv
      obtain ⟨h0, h1, h2, h3⟩ := hout
      exact ⟨hfu, hblku, hjqu, 0, 128, 191, 0, h1, h2, h3, h0, by decide, by decide, by decide,
        fun _ => ⟨rfl, rfl⟩, Or.inr ⟨rfl, hv.symm⟩⟩
    | some y =>
      obtain ⟨n, lo', hi'⟩ := y
      rw [hl] at hout
      simp only [hl, gMulti, Option.bind_some] at hv
      obtain ⟨h0, h1, h2, h3⟩ := hout
      obtain ⟨b1, b2, b3, b4⟩ := lead_bounds hl
      exact ⟨hfu, hblku, hjqu, n, lo', hi', 1, h1, h2, h3, h0, b2, b3, b4, fun h => by omega,
        Or.inl ⟨rfl, hv⟩⟩

/-- The name's ending after its octets: no character left open, `ok` into the return word. -/
def gnRest : AProg σ :=
  .seq (.cond (.cmp .less (.const 0) (.var "nd")) (.assign "ok" (.const 0)) .skip)
    (.seq (.store retE (.var "ok")) (.ret (.const 0)))

/-- **After the name's octets**: `ok` the verdict into the return word, zero returned. -/
theorem gn_exit {b : Word} {ci S : Nat} {w : List Byte} {s0 t : PancakeState σ} {Q : Assn σ}
    (hpre : GnPre b ci S w s0) (hf : ButFor gnNames s0 t) {nd : Nat} (hnd3 : nd ≤ 3)
    (hnd : t.locals "nd" = some (BitVec.ofNat 64 nd)) {okv : Word} (hok : t.locals "ok" = some okv)
    (hv : (okv = 1 ∧ (nd = 0) = (CommandSpec.isGroupName w = true)) ∨ (okv = 0 ∧ CommandSpec.isGroupName w = false)) :
    wpR gnRest (gnRet b w s0.memory) Q t := by
  have htest := eval_lt (a := .const 0) (b := .var "nd") (x := 0) (y := nd) (by decide) (by omega) rfl hnd
  have hstore : ∀ (u : PancakeState σ) (v : Word), ButFor gnNames s0 u → u.locals "ok" = some v →
      v = bw (CommandSpec.isGroupName w) →
      wpR (.seq (.store retE (.var "ok")) (.ret (.const 0))) (gnRet b w s0.memory) Q u := by
    intro u v hu huok hvv
    refine wpR_seq (M := fun u' => u'.memory = fun k => if k = retW b then v else s0.memory k) ?_ ?_
    · refine wp_store (a := retW b) (val := v) (ret_eval (hu.base.trans hpre.base)) huok
        (by simp [memStoreWord, hu.memaddrs, hpre.ret]; rfl) ?_
      simp [hu.memory]
    · intro u' hm
      exact ⟨0, rfl, rfl, by rw [hm]; simp [hvv], fun a ha => by rw [hm]; simp [ha]⟩
  by_cases hpos : 0 < nd
  · refine wpR_seq (M := fun u => ButFor gnNames s0 u ∧ u.locals "ok" = some 0)
      (wpR_cond_ne htest (by simp [bw, hpos]) (wpR_assign rfl hok ⟨but_set hf (by decide) _, by simp [setLocal]⟩))
      (fun u ⟨hu, huok⟩ => hstore u 0 hu huok ?_)
    rcases hv with ⟨rfl, he⟩ | ⟨rfl, he⟩
    · have : CommandSpec.isGroupName w = false := by
        cases h : CommandSpec.isGroupName w
        · rfl
        · rw [h] at he; simp at he; omega
      simp [this, bw]
    · simp [he, bw]
  · refine wpR_seq (M := fun u => u = t) (wpR_cond_eq (htest.trans (by simp [bw, hpos])) rfl) ?_
    rintro u rfl
    refine hstore u okv hf hok ?_
    rcases hv with ⟨rfl, he⟩ | ⟨rfl, he⟩
    · have : CommandSpec.isGroupName w = true := by rw [← eq_iff_iff.mp he]; omega
      simp [this, bw]
    · simp [he, bw]

theorem gnInv_clock (B : Word) (w : List Byte) (s0 : PancakeState σ) : Safe.ClockFree (GnInv B w s0) :=
  but_clockFree

/-- What the loop asks holds. -/
theorem gn_vc {b : Word} {ci S : Nat} {w : List Byte} {s0 : PancakeState σ} (hpre : GnPre b ci S w s0) :
    vcR (gnA (gnBlock b ci) w s0) (gnRet b w s0.memory) (fun _ => False) := by
  have hs : w.length < 2 ^ 62 := by have := hpre.len; unfold News.SessionSpec.lineLimit at this; omega
  refine ⟨SessionRun.keptA_vc _ _ _ _, SessionRun.keptA_vc _ _ _ _, SessionRun.keptA_vc _ _ _ _,
    fun _ _ _ _ _ _ => ⟨⟨gnInv_clock _ _ _, fun _ => by simp [vcR, tailA, leadA], fun t ht => ?_⟩, by simp [vcR]⟩⟩
  obtain ⟨hf, hblk, k, nd, lo, hi, okv, hk, hjq, hnd, hclo, hchi, hok, h3, hl, hh, hz, hv⟩ := ht
  have hl1 : t.locals "l1" = some (BitVec.ofNat 64 w.length) := (hf.locals "l1" (by decide)).trans hpre.l1
  rw [dig_guard hs hk hok hjq hl1]
  show (if (okv &&& bw (decide (k < w.length))) = 0 then _ else _)
  by_cases hend : (okv &&& bw (decide (k < w.length))) = 0
  · rw [if_pos hend]
    refine gn_exit hpre hf h3 hnd hok ?_
    rcases hv with ⟨rfl, hv⟩ | ⟨rfl, hv⟩
    · have hkw : k = w.length := by
        refine Classical.byContradiction fun hne => ?_
        simp [bw, show k < w.length by omega] at hend
      subst hkw
      rw [List.drop_length] at hv
      refine Or.inl ⟨rfl, ?_⟩
      rw [← hv]
      simp [bRun]
    · exact Or.inr ⟨rfl, hv⟩
  · rw [if_neg hend]
    rcases hv with ⟨rfl, hv⟩ | ⟨rfl, _⟩
    · have hkl : k < w.length := by
        refine Classical.byContradiction fun hne => hend ?_
        simp [bw, hne]
      exact gn_step hpre hf hblk hkl hjq hnd hclo hchi hok h3 hl hh hz hv
    · exact absurd (by simp) hend

/-- The name check starts: its words in range, the locals declared, the verdict on the length. -/
theorem gn_wp {b : Word} {ci S : Nat} {w : List Byte} {s0 : PancakeState σ} (hpre : GnPre b ci S w s0) :
    wpR (gnA (gnBlock b ci) w s0) (gnRet b w s0.memory) (fun _ => False) s0 := by
  have hs : w.length < 2 ^ 62 := by have := hpre.len; unfold News.SessionSpec.lineLimit at this; omega
  refine (wpR_seq_iff _ _ _ _).mpr (SessionRun.keptA_wp (E := .var "c") (k := ci) (by decide) hpre.hci hpre.c ?_)
  refine (wpR_seq_iff _ _ _ _).mpr (SessionRun.keptA_wp (E := .var "s1") (k := S) (by decide) hpre.hS hpre.s1 ?_)
  refine (wpR_seq_iff _ _ _ _).mpr
    (SessionRun.keptA_wp (E := .var "l1") (k := w.length) (by decide) hpre.len hpre.l1 ?_)
  refine wpR_dec (val := gnBlock b ci) (blk_eval hpre.base hpre.c) ?_
  refine wpR_dec (val := bw (decide (1 ≤ w.length)))
    (eval_le (x := 1) (y := w.length) (by decide) (by omega) (eval_const rfl) (by simp [eval, setLocal, hpre.l1])) ?_
  apply wpR_dec (val := 0) rfl
  apply wpR_dec (val := 128) rfl
  apply wpR_dec (val := 191) rfl
  refine wpR_dec (val := 0) rfl ((wpR_while_seq _ _ _ _ _ _).mpr ?_)
  refine ⟨?_, by simp [setLocal], 0, 0, 128, 191, bw (decide (1 ≤ w.length)), Nat.zero_le _,
    by simp [setLocal], by simp [setLocal], by simp [setLocal], by simp [setLocal], by simp [setLocal],
    by decide, by decide, by decide, fun _ => ⟨rfl, rfl⟩, ?_⟩
  · exact but_set (but_set (but_set (but_set (but_set (but_set (but_refl _ _) (by decide) _) (by decide) _)
      (by decide) _) (by decide) _) (by decide) _) (by decide) _
  · by_cases hw : 1 ≤ w.length
    · refine Or.inl ⟨by simp [bw, hw], ?_⟩
      rw [List.drop_zero, ← exactChars_run]
      have : w.isEmpty = false := by cases w <;> simp_all
      simp [CommandSpec.isGroupName, this]
    · refine Or.inr ⟨by simp [bw, hw], ?_⟩
      have : w = [] := List.eq_nil_of_length_eq_zero (by omega)
      simp [CommandSpec.isGroupName, this]

/-- **The session's `groupName` is `CommandSpec.isGroupName`**: from connection `ci`'s record holding the name `w` in
its line's octets. It puts in the return word whether `w` is a group name, changes no other word, and returns zero. -/
theorem groupName_run (o : Oracle σ) (b : Word) (ci S : Nat) (w : List Byte) (s0 : PancakeState σ)
    {body : PancakeProg} (hb : Lower.lower Session.groupName = some body) :
    SafeR o (fun s => s = s0 ∧ GnPre b ci S w s) body (gnRet b w s0.memory) (fun _ => False) := by
  rw [groupName_lower (gnBlock b ci) w s0] at hb
  cases hb
  rintro s ⟨rfl, hpre⟩
  exact wpR_sound o _ _ (fun _ => False) (fun _ _ h => h) (gn_vc hpre) s (gn_wp hpre)

/-! ## A wildmat -/

/-- The names the wildmat check writes. -/
def wmNames : List String := ["ok", "jq", "cz", "nd", "clo", "chi", "items", "bang"]

/-- An item's octet of US-ASCII: `wildmat-exact`, `*` or `?`. -/
def wmExactE : PancakeExp := or2E exactE (or2E (.cmp .equal czE (.const 42)) (.cmp .equal czE (.const 63)))

/-- An octet of the wildmat. -/
def wmBody : AProg σ :=
  .dec "cz" (kb (.var "s2") (.var "jq"))
    (.seq (.cond (.cmp .less (.const 0) (.var "nd")) tailA
      (.cond (.cmp .equal czE (.const 44))
        (.seq (.cond (.cmp .equal (.var "items") (.const 0)) (.assign "ok" (.const 0)) .skip)
          (.seq (.assign "items" (.const 0)) (.assign "bang" (.const 1))))
        (.cond (.cmp .equal czE (.const 33))
          (.cond (.var "bang") (.assign "bang" (.const 0)) (.assign "ok" (.const 0)))
          (.seq (.assign "bang" (.const 0)) (.seq (.assign "items" (.op .add (.var "items") (.const 1)))
            (.cond (.cmp .less czE (.const 128)) (.assign "ok" wmExactE) leadA))))))
      (.assign "jq" (.op .add (.var "jq") (.const 1))))

/-- The loop's state after `k` octets of the wildmat `w`, the check asked of `p`. `ok` is one while the octets left
decide as the whole wildmat does, else zero and `p` or `w` no. -/
def WmInv (w : List Byte) (s0 : PancakeState σ) (p : Bool) (t : PancakeState σ) : Prop :=
  ButFor wmNames s0 t ∧ ∃ k nd lo hi items bang okv, k ≤ w.length ∧
    t.locals "jq" = some (BitVec.ofNat 64 k) ∧ t.locals "nd" = some (BitVec.ofNat 64 nd) ∧
    t.locals "clo" = some (BitVec.ofNat 64 lo) ∧ t.locals "chi" = some (BitVec.ofNat 64 hi) ∧
    t.locals "items" = some (BitVec.ofNat 64 items) ∧ t.locals "bang" = some (bw bang) ∧
    t.locals "ok" = some okv ∧ nd ≤ 3 ∧ lo < 256 ∧ hi < 256 ∧ (nd = 0 → lo = 128 ∧ hi = 191) ∧ items ≤ k ∧
    ((okv = 1 ∧ p = true ∧
        okItems (bRun wAsc wMulti (items, bang) nd lo hi (w.drop k)) = (CommandSpec.wildmat? w).isSome) ∨
      (okv = 0 ∧ (p && (CommandSpec.wildmat? w).isSome) = false))

/-- The wildmat check, as it lowers, its loop carrying `WmInv`. -/
def wmA (w : List Byte) (s0 : PancakeState σ) (p : Bool) : AProg σ :=
  .dec "nd" (.const 0) (.dec "clo" (.const 128) (.dec "chi" (.const 191) (.dec "items" (.const 0)
  (.dec "bang" (.const 0)
    (.seq (.assign "jq" (.const 0))
    (.seq (.while_ (WmInv w s0 p) (.op .and_ (.var "ok") (.cmp .less (.var "jq") (.var "l2"))) wmBody)
      (.cond (or2E (.cmp .less (.const 0) (.var "nd")) (.cmp .equal (.var "items") (.const 0)))
        (.assign "ok" (.const 0)) .skip)))))))

theorem wildmatCheck_lower (w : List Byte) (s0 : PancakeState σ) (p : Bool) :
    Lower.lowerStmtsFold Session.wildmatCheck = some (wmA w s0 p).erase := by
  simp [Session.wildmatCheck, Session.utf8Tail, Session.utf8Lead, Session.isExactE, Session.between,
    Session.kept, Lower.lowerStmtsFold, Lower.lowerStmt1, Lower.lowerExp, SessionStore.or2, SessionStore.ifs,
    SessionStore.inc, Syntax.eAdd, Syntax.eAnd, Syntax.eLe, Syntax.eLt, Syntax.eEq, Syntax.eSub, Syntax.n,
    Syntax.v, wmA, wmBody, wmExactE, tailA, leadA, exactE, or2E, czE, kb, leE, betweenE, AProg.erase,
    framerHead]

/-- What it leaves: `ok` one when `p` was and `w` is a wildmat. -/
def WmPost (w : List Byte) (s0 : PancakeState σ) (p : Bool) (t : PancakeState σ) : Prop :=
  ButFor wmNames s0 t ∧ t.locals "ok" = some (bw (p && (CommandSpec.wildmat? w).isSome))

/-- After an octet's test, the place not yet moved on. -/
def WmMid (w : List Byte) (s0 : PancakeState σ) (p : Bool) (k : Nat) (u : PancakeState σ) : Prop :=
  ButFor wmNames s0 u ∧ u.locals "jq" = some (BitVec.ofNat 64 k) ∧ ∃ nd lo hi items bang okv,
    u.locals "nd" = some (BitVec.ofNat 64 nd) ∧ u.locals "clo" = some (BitVec.ofNat 64 lo) ∧
    u.locals "chi" = some (BitVec.ofNat 64 hi) ∧ u.locals "items" = some (BitVec.ofNat 64 items) ∧
    u.locals "bang" = some (bw bang) ∧ u.locals "ok" = some okv ∧ nd ≤ 3 ∧ lo < 256 ∧ hi < 256 ∧
    (nd = 0 → lo = 128 ∧ hi = 191) ∧ items ≤ k + 1 ∧
    ((okv = 1 ∧ p = true ∧
        okItems (bRun wAsc wMulti (items, bang) nd lo hi (w.drop (k + 1))) = (CommandSpec.wildmat? w).isSome) ∨
      (okv = 0 ∧ (p && (CommandSpec.wildmat? w).isSome) = false))

theorem okItems_none_false {p : Bool} {V : Bool} (hp : p = true) (h : okItems none = V) : (p && V) = false := by
  subst hp; rw [← h]; rfl

/-- **An octet of the wildmat, the octets so far deciding as the whole**: the loop goes on. -/
theorem wm_step {B S : Word} {w : List Byte} {p : Bool} {s0 t : PancakeState σ} {R : Ret}
    (hpre : WmPre B S w p s0) (hf : ButFor wmNames s0 t)
    {k nd lo hi items : Nat} {bang : Bool} (hk : k < w.length) (hjq : t.locals "jq" = some (BitVec.ofNat 64 k))
    (hnd : t.locals "nd" = some (BitVec.ofNat 64 nd)) (hclo : t.locals "clo" = some (BitVec.ofNat 64 lo))
    (hchi : t.locals "chi" = some (BitVec.ofNat 64 hi)) (hit : t.locals "items" = some (BitVec.ofNat 64 items))
    (hbang : t.locals "bang" = some (bw bang)) (hok : t.locals "ok" = some 1) (hp : p = true)
    (hnd3 : nd ≤ 3) (hlo : lo < 256) (hhi : hi < 256) (hz : nd = 0 → lo = 128 ∧ hi = 191) (hik : items ≤ k)
    (hv : okItems (bRun wAsc wMulti (items, bang) nd lo hi (w.drop k)) = (CommandSpec.wildmat? w).isSome) :
    wpR wmBody R (WmInv w s0 p) t := by
  have hx : w[k].toNat < 256 := w[k].isLt
  have hs := hpre.short
  have hB : t.locals "blk" = some B := (hf.locals "blk" (by decide)).trans hpre.blk
  have hS : t.locals "s2" = some S := (hf.locals "s2" (by decide)).trans hpre.s2
  have hbyte : eval t (kb (.var "s2") (.var "jq")) = some (BitVec.ofNat 64 w[k].toNat) := by
    rw [kb_eval (S := S) (j := k) hB (by simp [eval, hS, hjq])
      (by rw [hf.load]; exact hpre.bytes k hk), Bytes.setWidth8_64]
  have hw8 : BitVec.ofNat 8 w[k].toNat = w[k] := by simp
  rw [List.drop_eq_getElem_cons hk] at hv
  refine wpR_dec hbyte ?_
  obtain ⟨t1, ht1⟩ : ∃ t1 : PancakeState σ,
      t1 = { t with locals := setLocal t.locals "cz" (BitVec.ofNat 64 w[k].toNat) } := ⟨_, rfl⟩
  rw [← ht1]
  have l1 : ∀ y, y ≠ "cz" → t1.locals y = t.locals y := fun y hy => by simp [ht1, setLocal, hy]
  have hf1 : ButFor wmNames s0 t1 := ht1 ▸ but_set hf (by decide) _
  have hcz1 : t1.locals "cz" = some (BitVec.ofNat 64 w[k].toNat) := by simp [ht1, setLocal]
  have hnd1 := (l1 "nd" (by decide)).trans hnd
  have hclo1 := (l1 "clo" (by decide)).trans hclo
  have hchi1 := (l1 "chi" (by decide)).trans hchi
  have hok1 := (l1 "ok" (by decide)).trans hok
  have hjq1 := (l1 "jq" (by decide)).trans hjq
  have hit1 := (l1 "items" (by decide)).trans hit
  have hbang1 := (l1 "bang" (by decide)).trans hbang
  refine wpR_seq (M := WmMid w s0 p k) ?_ ?_
  rotate_left
  · rintro u ⟨hfu, hjqu, nd', lo', hi', it', bg', okv, hndu, hclou, hchiu, hitu, hbgu, hoku, h3, hl, hh, hz', hik',
      hv'⟩
    refine wpR_assign (val := BitVec.ofNat 64 (k + 1)) (by simp [eval, hjqu, BitVec.ofNat_add]) hjqu ?_
    refine ⟨but_restore (but_set hfu (by decide) _) (by decide) _, k + 1, nd', lo', hi', it', bg', okv, by omega,
      by simp [restore, resVar, setLocal], by simp [restore, resVar, setLocal, hndu],
      by simp [restore, resVar, setLocal, hclou], by simp [restore, resVar, setLocal, hchiu],
      by simp [restore, resVar, setLocal, hitu], by simp [restore, resVar, setLocal, hbgu],
      by simp [restore, resVar, setLocal, hoku], h3, hl, hh, hz', hik', hv'⟩
  have fr : ∀ u : PancakeState σ, ButFor ["ok", "nd", "clo", "chi", "items", "bang"] t1 u →
      ButFor wmNames s0 u ∧ u.locals "jq" = some (BitVec.ofNat 64 k) :=
    fun u hu => ⟨but_trans hf1 (but_mono hu (by decide)), (hu.locals "jq" (by decide)).trans hjq1⟩
  have htest := eval_lt (a := .const 0) (b := .var "nd") (x := 0) (y := nd) (by decide) (by omega) rfl hnd1
  by_cases hpos : 0 < nd
  · -- a continuation octet
    refine wpR_cond_ne htest (by simp [bw, hpos]) (tail_wp hx hlo hhi hpos hnd3 hcz1 hnd1 hclo1 hchi1 hok1 ?_)
    intro u hu hndu hclou hchiu hoku
    obtain ⟨hfu, hjqu⟩ := fr u (but_mono hu (by decide))
    simp only [bRun, hpos, if_true] at hv
    refine ⟨hfu, hjqu, nd - 1, 128, 191, items, bang, if w[k].toNat < lo ∨ hi < w[k].toNat then 0 else 1,
      hndu, hclou, hchiu,
      (hu.locals "items" (by decide)).trans hit1, (hu.locals "bang" (by decide)).trans hbang1, hoku,
      by omega, by decide, by decide, fun _ => ⟨rfl, rfl⟩, by omega, ?_⟩
    by_cases hout : w[k].toNat < lo ∨ hi < w[k].toNat
    · rw [if_pos hout] at hv ⊢
      exact Or.inr ⟨rfl, okItems_none_false hp hv⟩
    · rw [if_neg hout] at hv ⊢
      exact Or.inl ⟨rfl, hp, hv⟩
  obtain ⟨rfl, rfl⟩ := hz (by omega)
  have hn0 : nd = 0 := by omega
  subst hn0
  refine wpR_cond_eq (htest.trans (by simp [bw])) ?_
  simp only [bRun, Nat.lt_irrefl, if_false] at hv
  have hx44 := eval_eq (a := czE) (b := .const 44) (x := w[k].toNat) (y := 44) (by omega) (by decide) hcz1
    (eval_const rfl)
  by_cases c44 : w[k].toNat = 44
  · -- a comma: the pattern before it had an item, a `!` may stand after it
    refine wpR_cond_ne hx44 (by simp [bw, c44]) ?_
    simp only [if_true, wAsc, c44] at hv
    have hie := eval_eq (a := .var "items") (b := .const 0) (x := items) (y := 0) (by omega) (by decide) hit1
      (eval_const rfl)
    refine wpR_seq (M := fun u => ButFor ["ok"] t1 u ∧ u.locals "ok" = some (if items = 0 then 0 else 1)) ?_ ?_
    · by_cases hi0 : items = 0
      · exact wpR_cond_ne hie (by simp [bw, hi0])
          (wpR_assign rfl hok1 ⟨but_set (but_refl _ _) (by simp) _, by simp [setLocal, hi0]⟩)
      · exact wpR_cond_eq (hie.trans (by simp [bw, hi0])) ⟨but_refl _ _, by simp [hi0, hok1]⟩
    rintro u ⟨hu, hoku⟩
    have hitu := (hu.locals "items" (by decide)).trans hit1
    have hbgu := (hu.locals "bang" (by decide)).trans hbang1
    refine wpR_seq (M := fun v => v = { u with locals := setLocal u.locals "items" 0 }) (wpR_assign rfl hitu rfl) ?_
    rintro v rfl
    refine wpR_assign (val := 1) (old := bw bang) rfl (by simp [setLocal, hbgu]) ?_
    obtain ⟨hfv, hjqv⟩ := fr _ (but_set (x := "bang") (but_set (x := "items") (but_mono hu (by decide))
      (by decide) _) (by decide) _)
    refine ⟨hfv, hjqv, 0, 128, 191, 0, true, if items = 0 then 0 else 1,
      by simp [setLocal, (hu.locals "nd" (by decide)).trans hnd1],
      by simp [setLocal, (hu.locals "clo" (by decide)).trans hclo1],
      by simp [setLocal, (hu.locals "chi" (by decide)).trans hchi1], by simp [setLocal], by simp [setLocal, bw],
      by simp [setLocal, hoku], by decide, by decide, by decide, fun _ => ⟨rfl, rfl⟩, by omega, ?_⟩
    by_cases hi0 : items = 0
    · simp only [hi0, if_true] at hv
      exact Or.inr ⟨by simp [hi0], okItems_none_false hp hv⟩
    · simp only [hi0, if_false, Option.bind_some] at hv
      exact Or.inl ⟨by simp [hi0], hp, hv⟩
  refine wpR_cond_eq (hx44.trans (by simp [bw, c44])) ?_
  have hx33 := eval_eq (a := czE) (b := .const 33) (x := w[k].toNat) (y := 33) (by omega) (by decide) hcz1
    (eval_const rfl)
  by_cases c33 : w[k].toNat = 33
  · -- a `!`, where one may stand
    refine wpR_cond_ne hx33 (by simp [bw, c33]) ?_
    simp only [if_true, wAsc, c33, show (33 : Nat) ≠ 44 by decide, if_false] at hv
    cases bang with
    | true =>
      refine wpR_cond_ne (v := 1) (by simp [eval, hbang1, bw]) (by decide) (wpR_assign rfl hbang1 ?_)
      obtain ⟨hfv, hjqv⟩ := fr _ (but_set (x := "bang") (but_refl _ _) (by decide) _)
      refine ⟨hfv, hjqv, 0, 128, 191, items, false, 1, by simp [setLocal, hnd1], by simp [setLocal, hclo1],
        by simp [setLocal, hchi1], by simp [setLocal, hit1], by simp [setLocal, bw], by simp [setLocal, hok1],
        by decide, by decide, by decide, fun _ => ⟨rfl, rfl⟩, by omega, Or.inl ⟨rfl, hp, ?_⟩⟩
      simpa using hv
    | false =>
      refine wpR_cond_eq (by simp [eval, hbang1, bw]) (wpR_assign (val := 0) rfl hok1 ?_)
      obtain ⟨hfv, hjqv⟩ := fr _ (but_set (x := "ok") (but_refl _ _) (by decide) _)
      refine ⟨hfv, hjqv, 0, 128, 191, items, false, 0, by simp [setLocal, hnd1], by simp [setLocal, hclo1],
        by simp [setLocal, hchi1], by simp [setLocal, hit1], by simp [setLocal, hbang1], by simp [setLocal],
        by decide, by decide, by decide, fun _ => ⟨rfl, rfl⟩, by omega, Or.inr ⟨rfl, ?_⟩⟩
      exact okItems_none_false hp (by simpa using hv)
  refine wpR_cond_eq (hx33.trans (by simp [bw, c33])) ?_
  -- an item: no `!` after it, one item more
  refine wpR_seq (M := fun v => v = { t1 with locals := setLocal t1.locals "bang" 0 }) (wpR_assign rfl hbang1 rfl) ?_
  rintro v rfl
  refine wpR_seq (M := fun v => v = { t1 with locals := (setLocal (setLocal t1.locals "bang" 0) "items"
    (BitVec.ofNat 64 (items + 1))) })
    (wpR_assign (old := BitVec.ofNat 64 items) (by simp [eval, setLocal, hit1, BitVec.ofNat_add])
      (by simp [setLocal, hit1]) rfl) ?_
  rintro v rfl
  obtain ⟨t2, ht2⟩ : ∃ t2 : PancakeState σ, t2 = { t1 with locals := (setLocal (setLocal t1.locals "bang" 0)
      "items" (BitVec.ofNat 64 (items + 1))) } := ⟨_, rfl⟩
  rw [← ht2]
  have l2 : ∀ y, y ≠ "bang" → y ≠ "items" → t2.locals y = t1.locals y := fun y h1 h2 => by
    simp [ht2, setLocal, h1, h2]
  have hf2 : ButFor wmNames s0 t2 := ht2 ▸ but_set (but_set hf1 (by decide) _) (by decide) _
  have hcz2 := (l2 "cz" (by decide) (by decide)).trans hcz1
  have hnd2 := (l2 "nd" (by decide) (by decide)).trans hnd1
  have hclo2 := (l2 "clo" (by decide) (by decide)).trans hclo1
  have hchi2 := (l2 "chi" (by decide) (by decide)).trans hchi1
  have hok2 := (l2 "ok" (by decide) (by decide)).trans hok1
  have hjq2 := (l2 "jq" (by decide) (by decide)).trans hjq1
  have hit2 : t2.locals "items" = some (BitVec.ofNat 64 (items + 1)) := by simp [ht2, setLocal]
  have hbg2 : t2.locals "bang" = some (bw false) := by simp [ht2, setLocal, bw]
  have hlt := eval_lt (a := czE) (b := .const 128) (x := w[k].toNat) (y := 128) (by omega) (by decide) hcz2
    (eval_const rfl)
  by_cases hascii : w[k].toNat < 128
  · -- US-ASCII: `wildmat-exact`, `*` or `?`
    have hE : eval t2 wmExactE = some (bw (CommandSpec.isExactAscii w[k] ||
        (decide (w[k].toNat = 42) || decide (w[k].toNat = 63)))) := by
      rw [wmExactE, eval_or2 (exact_eval hx hcz2) (eval_or2
        (eval_eq (a := czE) (x := w[k].toNat) (y := 42) (by omega) (by decide) hcz2 (eval_const (c := 42) rfl))
        (eval_eq (a := czE) (x := w[k].toNat) (y := 63) (by omega) (by decide) hcz2 (eval_const (c := 63) rfl))),
        hw8]
    refine wpR_cond_ne hlt (by simp [bw, hascii]) (wpR_assign hE hok2 ?_)
    simp only [hascii, if_true, wAsc, c44, c33, if_false] at hv
    refine ⟨but_set hf2 (by decide) _, by simp [setLocal, hjq2], 0, 128, 191, items + 1, false,
      bw (CommandSpec.isExactAscii w[k] || (decide (w[k].toNat = 42) || decide (w[k].toNat = 63))),
      by simp [setLocal, hnd2], by simp [setLocal, hclo2], by simp [setLocal, hchi2], by simp [setLocal, hit2],
      by simp [setLocal, hbg2], by simp [setLocal], by decide, by decide, by decide, fun _ => ⟨rfl, rfl⟩,
      by omega, ?_⟩
    rw [← Bool.or_assoc]
    cases he : (CommandSpec.isExactAscii w[k] || decide (w[k].toNat = 42) || decide (w[k].toNat = 63))
    · rw [he] at hv
      exact Or.inr ⟨rfl, okItems_none_false hp (by simpa using hv)⟩
    · rw [he] at hv
      exact Or.inl ⟨rfl, hp, by simpa using hv⟩
  · -- a lead octet
    refine wpR_cond_eq (hlt.trans (by simp [bw, hascii])) ?_
    refine lead_wp (by omega) hx hcz2 hnd2 hclo2 hchi2 hok2 fun u hu hout => ?_
    have hfu := but_trans hf2 (but_mono hu (by decide))
    have hjqu := (hu.locals "jq" (by decide)).trans hjq2
    have hitu := (hu.locals "items" (by decide)).trans hit2
    have hbgu := (hu.locals "bang" (by decide)).trans hbg2
    simp only [hascii, if_false] at hv
    simp only [LeadOut] at hout
    rw [hw8] at hout
    cases hl : lead w[k] with
    | none =>
      rw [hl] at hout
      simp only [hl] at hv
      obtain ⟨h0, h1, h2, h3⟩ := hout
      exact ⟨hfu, hjqu, 0, 128, 191, items + 1, false, 0, h1, h2, h3, hitu, hbgu, h0, by decide, by decide,
        by decide, fun _ => ⟨rfl, rfl⟩, by omega, Or.inr ⟨rfl, okItems_none_false hp hv⟩⟩
    | some y =>
      obtain ⟨n, lo', hi'⟩ := y
      rw [hl] at hout
      simp only [hl, wMulti, Option.bind_some] at hv
      obtain ⟨h0, h1, h2, h3⟩ := hout
      obtain ⟨b1, b2, b3, b4⟩ := lead_bounds hl
      exact ⟨hfu, hjqu, n, lo', hi', items + 1, false, 1, h1, h2, h3, hitu, hbgu, h0, b2, b3, b4,
        fun h => by omega, by omega, Or.inl ⟨rfl, hp, hv⟩⟩

/-- The check's last test: no character left open, a last pattern of at least one item. -/
def wmLast : AProg σ :=
  .cond (or2E (.cmp .less (.const 0) (.var "nd")) (.cmp .equal (.var "items") (.const 0)))
    (.assign "ok" (.const 0)) .skip

/-- **After the wildmat's octets**: `ok` the verdict. -/
theorem wm_exit {w : List Byte} {s0 t : PancakeState σ} {p : Bool} {R : Ret} (hf : ButFor wmNames s0 t)
    {nd items : Nat} (hnd3 : nd ≤ 3) (hit : items < 2 ^ 62)
    (hnd : t.locals "nd" = some (BitVec.ofNat 64 nd)) (hitl : t.locals "items" = some (BitVec.ofNat 64 items))
    {okv : Word} (hok : t.locals "ok" = some okv)
    (hv : (okv = 1 ∧ p = true ∧ (nd = 0 ∧ items ≠ 0 ↔ (CommandSpec.wildmat? w).isSome = true)) ∨
      (okv = 0 ∧ (p && (CommandSpec.wildmat? w).isSome) = false)) :
    wpR wmLast R (WmPost w s0 p) t := by
  have htest := eval_or2 (eval_lt (a := .const 0) (b := .var "nd") (x := 0) (y := nd) (by decide) (by omega) rfl hnd)
    (eval_eq (a := .var "items") (b := .const 0) (x := items) (y := 0) (by omega) (by decide) hitl (eval_const rfl))
  by_cases hbad : 0 < nd ∨ items = 0
  · refine wpR_cond_ne htest (by rcases hbad with h | h <;> simp [bw, h]) (wpR_assign rfl hok ?_)
    refine ⟨but_set hf (by decide) _, ?_⟩
    have : (p && (CommandSpec.wildmat? w).isSome) = false := by
      rcases hv with ⟨_, rfl, he⟩ | ⟨_, he⟩
      · have : (CommandSpec.wildmat? w).isSome = false := by
          cases h : (CommandSpec.wildmat? w).isSome
          · rfl
          · have := he.mpr h; omega
        simp [this]
      · exact he
    simp [setLocal, this, bw]
  · refine wpR_cond_eq (htest.trans (by simp [bw]; omega)) ⟨hf, ?_⟩
    rcases hv with ⟨rfl, rfl, he⟩ | ⟨rfl, he⟩
    · have : (CommandSpec.wildmat? w).isSome = true := he.mp ⟨by omega, by omega⟩
      simp [hok, this, bw]
    · simp [hok, he, bw]

theorem wmInv_clock (w : List Byte) (s0 : PancakeState σ) (p : Bool) : Safe.ClockFree (WmInv w s0 p) :=
  but_clockFree

theorem wmPost_restore {w : List Byte} {s0 t : PancakeState σ} {p : Bool} (h : WmPost w s0 p t) {x : String}
    (hx : x ∈ ["nd", "clo", "chi", "items", "bang"]) (old : Option Value) : WmPost w s0 p (restore t x old) := by
  have hr : x ∈ wmNames := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl <;> decide
  have hne : "ok" ≠ x := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl <;> decide
  exact ⟨but_restore h.1 hr old, by simp [restore, resVar, hne, h.2]⟩

theorem wmPost_clock (w : List Byte) (s0 : PancakeState σ) (p : Bool) : Safe.ClockFree (WmPost w s0 p) :=
  but_clockFree

/-- The declarations' ends keep what the check leaves. -/
theorem wmPost_restores {w : List Byte} {s0 t : PancakeState σ} {p : Bool} (h : WmPost w s0 p t)
    (o1 o2 o3 o4 o5 : Option Value) :
    WmPost w s0 p (restore (restore (restore (restore (restore t "bang" o5) "items" o4) "chi" o3) "clo" o2)
      "nd" o1) :=
  wmPost_restore (wmPost_restore (wmPost_restore (wmPost_restore (wmPost_restore h (by simp) o5) (by simp) o4)
    (by simp) o3) (by simp) o2) (by simp) o1

/-- What the loop asks holds. -/
theorem wm_vc {B S : Word} {w : List Byte} {p : Bool} {s0 : PancakeState σ} {R : Ret}
    (hpre : WmPre B S w p s0) : vcR (wmA w s0 p) R (WmPost w s0 p) := by
  have hs := hpre.short
  intro o1 o2 o3 o4 o5
  refine ⟨trivial, ⟨wmInv_clock _ _ _, fun _ => by simp [vcR, tailA, leadA], fun t ht => ?_⟩, trivial, trivial⟩
  obtain ⟨hf, k, nd, lo, hi, items, bang, okv, hk, hjq, hnd, hclo, hchi, hit, hbg, hok, h3, hl, hh, hz, hik, hv⟩ := ht
  have hl2 : t.locals "l2" = some (BitVec.ofNat 64 w.length) := (hf.locals "l2" (by decide)).trans hpre.l2
  rw [dig_guard hs hk hok hjq hl2]
  show (if (okv &&& bw (decide (k < w.length))) = 0 then _ else _)
  by_cases hend : (okv &&& bw (decide (k < w.length))) = 0
  · rw [if_pos hend]
    refine wpR_mono wmLast R (fun u hu => wmPost_restores hu o1 o2 o3 o4 o5) t
      (wm_exit hf h3 (by omega) hnd hit hok ?_)
    rcases hv with ⟨rfl, hp, hv⟩ | ⟨rfl, hv⟩
    · have hkw : k = w.length := by
        refine Classical.byContradiction fun hne => ?_
        simp [bw, show k < w.length by omega] at hend
      subst hkw
      rw [List.drop_length] at hv
      refine Or.inl ⟨rfl, hp, ?_⟩
      rw [← hv]
      by_cases h0 : nd = 0
      · subst h0
        simp [bRun, okItems]
      · simp [bRun, okItems, h0]
    · exact Or.inr ⟨rfl, hv⟩
  · rw [if_neg hend]
    rcases hv with ⟨rfl, hp, hv⟩ | ⟨rfl, _⟩
    · have hkl : k < w.length := by
        refine Classical.byContradiction fun hne => hend ?_
        simp [bw, hne]
      exact wm_step hpre hf hkl hjq hnd hclo hchi hit hbg hok hp h3 hl hh hz hik hv
    · exact absurd (by simp) hend

/-- The wildmat check starts: its locals declared, the place at zero. -/
theorem wm_wp {B S : Word} {w : List Byte} {p : Bool} {s0 : PancakeState σ} {R : Ret}
    (hpre : WmPre B S w p s0) : wpR (wmA w s0 p) R (WmPost w s0 p) s0 := by
  obtain ⟨x, hx⟩ := hpre.jq
  refine wpR_dec (val := 0) rfl (wpR_dec (val := 128) rfl (wpR_dec (val := 191) rfl (wpR_dec (val := 0) rfl
    (wpR_dec (val := 0) rfl ?_))))
  refine wpR_seq (M := WmInv w s0 p) (wpR_assign (val := 0) (old := x) rfl (by simp [setLocal, hx]) ?_)
    (fun u hu => wpR_mono _ R (fun t ht => wmPost_restores ht _ _ _ _ _) u hu)
  refine ⟨?_, 0, 0, 128, 191, 0, false, bw p, Nat.zero_le _, by simp [setLocal], by simp [setLocal],
    by simp [setLocal], by simp [setLocal], by simp [setLocal], by simp [setLocal, bw],
    by simp [setLocal, hpre.ok], by decide, by decide, by decide, fun _ => ⟨rfl, rfl⟩, Nat.le_refl _, ?_⟩
  · exact but_set (but_set (but_set (but_set (but_set (but_set (but_refl _ _) (by decide) _) (by decide) _)
      (by decide) _) (by decide) _) (by decide) _) (by decide) _
  · cases p
    · exact Or.inr ⟨rfl, rfl⟩
    · exact Or.inl ⟨rfl, rfl, by rw [List.drop_zero]; exact wildmat_run w⟩

/-- **The wildmat check is `CommandSpec.wildmat?`**: the third word is `w` in the line's octets, `ok` the flag `p`. A
normally finishing run leaves `ok` one when `p` was and `w` is a wildmat. It changes no local but its own nor the
memory. -/
theorem wildmat_safe (o : Oracle σ) (B S : Word) (w : List Byte) (p : Bool) (s0 : PancakeState σ) (R : Ret) :
    SafeR o (fun s => s = s0 ∧ WmPre B S w p s) (wmA w s0 p).erase R (WmPost w s0 p) := by
  rintro s ⟨rfl, hpre⟩
  exact wpR_sound o _ R _ (wmPost_clock w s p) (wm_vc hpre) s (wm_wp hpre)

/-! ## The checks as the session has them -/

/-- **The session's number check is `CommandSpec.isArticleNumber`**, of the statements it lowers to. -/
theorem numberCheck_safe (o : Oracle σ) {s l : Syntax.PExpr} {se le : PancakeExp}
    (hs : Lower.lowerExp s = some se) (hl : Lower.lowerExp l = some le) (hse : ExpAvoids (· ∈ numNames) se)
    (hle : ExpAvoids (· ∈ numNames) le) (B S : Word) (w : List Byte) (s0 : PancakeState σ) :
    ∃ c, Lower.lowerStmtsFold (Session.numberCheckAt s l) = some c ∧
      Safe.Safe o (fun u => u = s0 ∧ NumPre se le B S w u) c (NumPost w s0) :=
  ⟨_, numberCheck_lowerP hs hl, numP_safe o se le hse hle B S w s0⟩

/-- **The session's message-id check is `CommandSpec.isMessageId`**, of the statements it lowers to. -/
theorem messageIdCheck_safe (o : Oracle σ) {s l : Syntax.PExpr} {se le : PancakeExp}
    (hs : Lower.lowerExp s = some se) (hl : Lower.lowerExp l = some le) (hse : ExpAvoids (· ∈ midNames) se)
    (hle : ExpAvoids (· ∈ midNames) le) (B S : Word) (w : List Byte) (s0 : PancakeState σ) :
    ∃ c, Lower.lowerStmtsFold (Session.messageIdCheckAt s l) = some c ∧
      Safe.Safe o (fun u => u = s0 ∧ MidPre se le B S w u) c (MidPost w s0) :=
  ⟨_, messageIdCheck_lower hs hl w s0, messageId_safe o se le hse hle B S w s0⟩

/-- **The session's date and time check is `CommandSpec.isDate` and `CommandSpec.isTime`**, of the
statements it lowers to. -/
theorem dateTimeCheck_safe (o : Oracle σ) (B S1 S2 : Word) (w1 w2 : List Byte) (s0 : PancakeState σ) :
    ∃ c, Lower.lowerStmtsFold Session.dateTimeCheck = some c ∧
      Safe.Safe o (fun s => s = s0 ∧ DTPre B S1 S2 w1 w2 s) c (DTPost w1 w2 s0) :=
  ⟨_, dateTimeCheck_lower w1 w2 s0, dateTime_safe o B S1 S2 w1 w2 s0⟩

/-- **The session's wildmat check is `CommandSpec.wildmat?`**, of the statements it lowers to. -/
theorem wildmatCheck_safe (o : Oracle σ) (B S : Word) (w : List Byte) (p : Bool) (s0 : PancakeState σ)
    (R : Ret) :
    ∃ c, Lower.lowerStmtsFold Session.wildmatCheck = some c ∧
      SafeR o (fun s => s = s0 ∧ WmPre B S w p s) c R (WmPost w s0 p) :=
  ⟨_, wildmatCheck_lower w s0 p, wildmat_safe o B S w p s0 R⟩

/-! ## The premises can hold -/

/-- A line of one octet, `1`, in a heap of zeros, every word addressable. The words' places and lengths are in the
locals, the checks' locals bound, `ok` one. -/
def chkState : PancakeState Unit :=
  { bareState () with
    memory := fun a => if a = 40 then 49 else 0
    locals := fun x =>
      if x = "l1" ∨ x = "l2" ∨ x = "ok" then some 1
      else if x ∈ ["val", "jq", "lo", "hi", "blk", "s1", "s2", "c", "dn", "dp"] then some 0 else none }

theorem chk_byte (a : Word) (h : a = 0 + BitVec.ofNat 64 40 + (0 + BitVec.ofNat 64 0)) :
    memLoadByte chkState.memory chkState.memaddrs chkState.be a = some 49#8 := by
  subst h; decide

theorem chk_bytes : ∀ j (h : j < [49#8].length), memLoadByte chkState.memory chkState.memaddrs chkState.be
    (0 + BitVec.ofNat 64 40 + (0 + BitVec.ofNat 64 j)) = some [49#8][j] := fun j h => by
  obtain rfl : j = 0 := by simp at h; omega
  exact chk_byte _ rfl

theorem butFor_witness : ButFor ["ok"] chkState chkState := but_refl _ _

/-- The article number `1` meets the number check's premises… -/
theorem numPre_witness : NumPre (.var "s1") (.var "l1") 0 0 [49#8] chkState where
  se := rfl
  le := rfl
  blk := rfl
  bytes := chk_bytes
  short := by decide
  ok := ⟨_, rfl⟩
  val := ⟨_, rfl⟩
  jq := ⟨_, rfl⟩

theorem midPre_witness : MidPre (.var "s1") (.var "l1") 0 0 [49#8] chkState where
  se := rfl
  le := rfl
  blk := rfl
  bytes := chk_bytes
  short := by decide
  ok := ⟨_, rfl⟩
  jq := ⟨_, rfl⟩

theorem rngPre_witness : RngPre (.var "s1") (.var "l1") 0 0 [49#8] chkState where
  se := rfl
  le := rfl
  blk := rfl
  bytes := chk_bytes
  short := by decide
  ok := ⟨_, rfl⟩
  val := ⟨_, rfl⟩
  jq := ⟨_, rfl⟩
  lo := ⟨_, rfl⟩
  hi := ⟨_, rfl⟩

theorem dashes_witness : Dashes [49#8] 0 chkState := ⟨rfl, 0, rfl, Or.inl rfl⟩

/-- …and is a range from one to one. -/
theorem rngPost_witness :
    RngPost [49#8] chkState { chkState with locals := fun x =>
      if x = "lo" ∨ x = "hi" ∨ x = "ok" then some 1 else chkState.locals x } := by
  have h0 : CommandSpec.range? [49#8] = some (1, 1) := by decide
  refine ⟨⟨fun x hx => ?_, rfl, rfl, rfl, rfl, rfl, rfl⟩, by rw [h0]; rfl, fun lo hi h => ?_⟩
  · simp only [rngNames, List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
    simp [hx.1, hx.2.2.2.2.1, hx.2.2.2.2.2.1]
  · rw [h0] at h
    cases h
    exact ⟨rfl, rfl⟩

theorem dtPre_witness : DTPre 0 0 0 [49#8] [49#8] chkState where
  s1 := rfl
  l1 := rfl
  s2 := rfl
  l2 := rfl
  blk := rfl
  bytes1 := chk_bytes
  bytes2 := chk_bytes
  short1 := by decide
  short2 := by decide
  ok := ⟨_, rfl⟩
  jq := ⟨_, rfl⟩

/-- The wildmat `1` with `ok` one, as the session checks it. -/
theorem wmPre_witness : WmPre 0 0 [49#8] true chkState where
  s2 := rfl
  l2 := rfl
  blk := rfl
  bytes := chk_bytes
  short := by decide
  ok := rfl
  jq := ⟨_, rfl⟩

theorem wmPost_witness : WmPost [49#8] chkState true chkState := by
  have h0 : (CommandSpec.wildmat? [49#8]).isSome = true := by decide
  exact ⟨but_refl _ _, by rw [h0]; rfl⟩

/-- The name `1` in connection zero's record. -/
theorem gnPre_witness :
    GnPre SessionFrame.base0 0 0 [49#8] { chkState with baseAddr := SessionFrame.base0 } where
  base := rfl
  c := rfl
  hci := Nat.zero_le _
  s1 := rfl
  hS := Nat.zero_le _
  l1 := rfl
  len := by decide
  bytes := fun j h => by
    obtain rfl : j = 0 := by simp at h; omega
    rw [gnBlock_eq, SessionFrame.blockAt_base0]
    exact chk_byte _ rfl
  ret := rfl

/-- A state of no memory, every local zero. -/
def zeroState : PancakeState Unit := { bareState () with locals := fun _ => some 0 }

theorem midPost_witness : MidPost [] zeroState zeroState := ⟨but_refl _ _, rfl⟩

theorem numPost_witness : NumPost [] zeroState zeroState :=
  ⟨but_refl _ _, rfl, ⟨0, rfl⟩, ⟨0, rfl⟩, fun h => absurd h (by decide)⟩

end DN.Server.SessionCheck
