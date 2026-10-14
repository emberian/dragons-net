-- SPDX-License-Identifier: AGPL-3.0-or-later
import DN.Compiler.WpBytes
import DN.News.SipHash
import DN.News.SipProg

/-!
# DN.News.SipHashCode

SipHash-2-4 as Pancake statements, shown by `DN.Compiler.Wp` to compute `DN.News.SipHash`.
-/

namespace DN.News.SipHashCode

open DN.Compiler DN.Compiler.Wp DN.Compiler.WpBytes DN.News.SipHash
open DN.News.FrameSpec (Byte)

variable {σ : Type}

private def c (k : Nat) : PancakeExp := .c k
private def v (x : String) : PancakeExp := .var x

/-- `x` rotated left by `b` bits: two shifts and an or. -/
def rotlE (x : String) (b : Nat) : PancakeExp :=
  .op .or_ (.shiftL (v x) (c b)) (.shiftR (v x) (c (64 - b)))

/-- One SipRound over the locals `v0` to `v3`, then `rest`. -/
def roundK (rest : AProg σ) : AProg σ :=
  .seq (.assign "v0" (.op .add (v "v0") (v "v1"))) <|
  .seq (.assign "v1" (.op .xor (rotlE "v1" 13) (v "v0"))) <|
  .seq (.assign "v0" (rotlE "v0" 32)) <|
  .seq (.assign "v2" (.op .add (v "v2") (v "v3"))) <|
  .seq (.assign "v3" (.op .xor (rotlE "v3" 16) (v "v2"))) <|
  .seq (.assign "v0" (.op .add (v "v0") (v "v3"))) <|
  .seq (.assign "v3" (.op .xor (rotlE "v3" 21) (v "v0"))) <|
  .seq (.assign "v2" (.op .add (v "v2") (v "v1"))) <|
  .seq (.assign "v1" (.op .xor (rotlE "v1" 17) (v "v2"))) <|
  .seq (.assign "v2" (rotlE "v2" 32)) rest

/-- The locals a round changes. -/
def vs : List String := ["v0", "v1", "v2", "v3"]

/-- The locals `v0` to `v3` hold the state `st`. -/
def Holds (st : State) (s : PancakeState σ) : Prop :=
  s.locals "v0" = some st.v0.toBitVec ∧ s.locals "v1" = some st.v1.toBitVec ∧
    s.locals "v2" = some st.v2.toBitVec ∧ s.locals "v3" = some st.v3.toBitVec

theorem eval_rotl {s : PancakeState σ} {x : String} {w : UInt64} {b : Nat} (hb0 : 0 < b)
    (hb : b < 64) (hx : s.locals x = some w.toBitVec) :
    eval s (rotlE x b) = some (rotl w (UInt64.ofNat b)).toBitVec := by
  have h1 : (BitVec.ofNat 64 b).toNat = b := by simp [BitVec.toNat_ofNat]; omega
  have h2 : (BitVec.ofNat 64 (64 - b)).toNat = 64 - b := by simp [BitVec.toNat_ofNat]; omega
  have e1 : ((UInt64.ofNat b).toBitVec % (64 : BitVec 64)).toNat = b := by
    simp [BitVec.toNat_umod, BitVec.toNat_ofNat]; omega
  have e2 : ((64 - UInt64.ofNat b).toBitVec % (64 : BitVec 64)).toNat = 64 - b := by
    simp [BitVec.toNat_umod, BitVec.toNat_sub, UInt64.toBitVec_ofNat, BitVec.toNat_ofNat]; omega
  have n1 : (decide (b ≠ 0) && decide (b ≥ 64)) = false := by simp; omega
  have n2 : (decide (64 - b ≠ 0) && decide (64 - b ≥ 64)) = false := by simp; omega
  simp only [rotlE, v, c, PancakeExp.c, eval, hx, h1, h2, n1, n2, Bool.false_eq_true, if_false,
    rotl,
    UInt64.toBitVec_or, UInt64.toBitVec_shiftLeft, UInt64.toBitVec_shiftRight,
    BitVec.shiftLeft_eq', BitVec.ushiftRight_eq']
  rw [e1, e2]

theorem holds_v0 {st : State} {s : PancakeState σ} (h : Holds st s) (w : UInt64) :
    Holds { st with v0 := w } { s with locals := setLocal s.locals "v0" w.toBitVec } := by
  obtain ⟨_, h1, h2, h3⟩ := h
  simp [Holds, setLocal, h1, h2, h3]

theorem holds_v1 {st : State} {s : PancakeState σ} (h : Holds st s) (w : UInt64) :
    Holds { st with v1 := w } { s with locals := setLocal s.locals "v1" w.toBitVec } := by
  obtain ⟨h0, _, h2, h3⟩ := h
  simp [Holds, setLocal, h0, h2, h3]

theorem holds_v2 {st : State} {s : PancakeState σ} (h : Holds st s) (w : UInt64) :
    Holds { st with v2 := w } { s with locals := setLocal s.locals "v2" w.toBitVec } := by
  obtain ⟨h0, h1, _, h3⟩ := h
  simp [Holds, setLocal, h0, h1, h3]

theorem holds_v3 {st : State} {s : PancakeState σ} (h : Holds st s) (w : UInt64) :
    Holds { st with v3 := w } { s with locals := setLocal s.locals "v3" w.toBitVec } := by
  obtain ⟨h0, h1, h2, _⟩ := h
  simp [Holds, setLocal, h0, h1, h2]

theorem round_wp (st : State) (s : PancakeState σ) (h : Holds st s) {rest : AProg σ} {Q : Assn σ}
    (k : ∀ t, Holds (sipRound st) t → Frame vs s t → wp rest Q t) : wp (roundK rest) Q s := by
  obtain ⟨a, b, c', d⟩ := st
  replace h : Holds ⟨a, b, c', d⟩ s ∧ Frame vs s s := ⟨h, frame_refl _ _⟩
  refine wp_seq (wp_assign (Q := fun t => Holds _ t ∧ Frame vs s t)
    (val := (a + b).toBitVec)
    (by simp [eval, v, h.1.1, h.1.2.1])
    h.1.1 ⟨holds_v0 h.1 _, frame_trans h.2 (frame_set (by decide) _ _)⟩) fun s' h => ?_
  refine wp_seq (wp_assign (Q := fun t => Holds _ t ∧ Frame vs s t)
    (val := (rotl b 13 ^^^ (a + b)).toBitVec)
    (by simp [eval, v, eval_rotl (b := 13) (by decide) (by decide) h.1.2.1, h.1.1])
    h.1.2.1 ⟨holds_v1 h.1 _, frame_trans h.2 (frame_set (by decide) _ _)⟩) fun s' h => ?_
  refine wp_seq (wp_assign (Q := fun t => Holds _ t ∧ Frame vs s t)
    (val := (rotl (a + b) 32).toBitVec)
    (by simp [eval_rotl (b := 32) (by decide) (by decide) h.1.1])
    h.1.1 ⟨holds_v0 h.1 _, frame_trans h.2 (frame_set (by decide) _ _)⟩) fun s' h => ?_
  refine wp_seq (wp_assign (Q := fun t => Holds _ t ∧ Frame vs s t)
    (val := (c' + d).toBitVec)
    (by simp [eval, v, h.1.2.2.1, h.1.2.2.2])
    h.1.2.2.1 ⟨holds_v2 h.1 _, frame_trans h.2 (frame_set (by decide) _ _)⟩) fun s' h => ?_
  refine wp_seq (wp_assign (Q := fun t => Holds _ t ∧ Frame vs s t)
    (val := (rotl d 16 ^^^ (c' + d)).toBitVec)
    (by simp [eval, v, eval_rotl (b := 16) (by decide) (by decide) h.1.2.2.2, h.1.2.2.1])
    h.1.2.2.2 ⟨holds_v3 h.1 _, frame_trans h.2 (frame_set (by decide) _ _)⟩) fun s' h => ?_
  refine wp_seq (wp_assign (Q := fun t => Holds _ t ∧ Frame vs s t)
    (val := ((rotl (a + b) 32) + (rotl d 16 ^^^ (c' + d))).toBitVec)
    (by simp [eval, v, h.1.1, h.1.2.2.2])
    h.1.1 ⟨holds_v0 h.1 _, frame_trans h.2 (frame_set (by decide) _ _)⟩) fun s' h => ?_
  refine wp_seq (wp_assign (Q := fun t => Holds _ t ∧ Frame vs s t)
    (val := (rotl (rotl d 16 ^^^ (c' + d)) 21 ^^^
      ((rotl (a + b) 32) + (rotl d 16 ^^^ (c' + d)))).toBitVec)
    (by simp [eval, v, eval_rotl (b := 21) (by decide) (by decide) h.1.2.2.2, h.1.1])
    h.1.2.2.2 ⟨holds_v3 h.1 _, frame_trans h.2 (frame_set (by decide) _ _)⟩) fun s' h => ?_
  refine wp_seq (wp_assign (Q := fun t => Holds _ t ∧ Frame vs s t)
    (val := ((c' + d) + (rotl b 13 ^^^ (a + b))).toBitVec)
    (by simp [eval, v, h.1.2.2.1, h.1.2.1])
    h.1.2.2.1 ⟨holds_v2 h.1 _, frame_trans h.2 (frame_set (by decide) _ _)⟩) fun s' h => ?_
  refine wp_seq (wp_assign (Q := fun t => Holds _ t ∧ Frame vs s t)
    (val := (rotl (rotl b 13 ^^^ (a + b)) 17 ^^^ ((c' + d) + (rotl b 13 ^^^ (a + b)))).toBitVec)
    (by simp [eval, v, eval_rotl (b := 17) (by decide) (by decide) h.1.2.1, h.1.2.2.1])
    h.1.2.1 ⟨holds_v1 h.1 _, frame_trans h.2 (frame_set (by decide) _ _)⟩) fun s' h => ?_
  refine wp_seq (wp_assign (Q := fun t => Holds _ t ∧ Frame vs s t)
    (val := (rotl ((c' + d) + (rotl b 13 ^^^ (a + b))) 32).toBitVec)
    (by simp [eval_rotl (b := 32) (by decide) (by decide) h.1.2.2.1])
    h.1.2.2.1 ⟨holds_v2 h.1 _, frame_trans h.2 (frame_set (by decide) _ _)⟩) fun s' h => ?_
  exact k s' h.1 h.2

/-! ## Words from octets -/

theorem word_cons (b : Byte) (bs : Bytes) :
    (word (b :: bs)).toBitVec = ((word bs).toBitVec <<< 8) ||| b.setWidth 64 := by
  have hb : (b.toNat.toUInt64).toBitVec = b.setWidth 64 := by
    apply BitVec.eq_of_toNat_eq
    have := b.isLt
    simp
  simp only [word, List.foldr_cons, UInt64.toBitVec_or, UInt64.toBitVec_shiftLeft, hb]
  rfl

/-- The octet at `q + i` below the ones `m` holds. -/
def byteE (q i : PancakeExp) : PancakeExp :=
  .op .or_ (.shiftL (v "m") (c 8)) (.loadByte (.op .add q i))

/-- The octets at `q + i - 1` down to `q`, each below the last, into `m`, then `rest`. -/
def bytesDown (q : PancakeExp) : Nat → AProg σ → AProg σ
  | 0, rest => rest
  | i + 1, rest => .seq (.assign "m" (byteE q (c i))) (bytesDown q i rest)

theorem bytesDown_wp {q : PancakeExp} {qv : Word} {bs : Bytes} {rest : AProg σ} {Q : Assn σ}
    (s0 : PancakeState σ) (hq : ∀ t, Frame ["m"] s0 t → eval t q = some qv)
    (hbytes : ∀ i (hi : i < bs.length),
      memLoadByte s0.memory s0.memaddrs s0.be (qv + BitVec.ofNat 64 i) = some bs[i])
    (k : ∀ t, Frame ["m"] s0 t → t.locals "m" = some (word bs).toBitVec → wp rest Q t) :
    ∀ i (s : PancakeState σ), i ≤ bs.length → Frame ["m"] s0 s →
      s.locals "m" = some (word (bs.drop i)).toBitVec → wp (bytesDown q i rest) Q s
  | 0, s, _, hf, hm => k s hf (by simpa using hm)
  | i + 1, s, hi, hf, hm => by
    have hlt : i < bs.length := by omega
    have hd : bs.drop i = bs[i] :: bs.drop (i + 1) := List.drop_eq_getElem_cons hlt
    have hb : memLoadByte s.memory s.memaddrs s.be (qv + BitVec.ofNat 64 i) = some bs[i] := by
      rw [hf.2.1, hf.2.2.1, hf.2.2.2]; exact hbytes i hlt
    have h8 : (decide ((8#64).toNat ≠ 0) && decide ((8#64).toNat ≥ 64)) = false := by decide
    refine wp_seq (wp_assign (val := (word (bs.drop i)).toBitVec) ?_ hm
      (Q := fun t => Frame ["m"] s0 t ∧ t.locals "m" = some (word (bs.drop i)).toBitVec)
      ⟨frame_trans hf (frame_set (by decide) _ _), by simp [setLocal]⟩) fun t ⟨hft, hmt⟩ =>
      bytesDown_wp s0 hq hbytes k i t (by omega) hft hmt
    simp only [byteE, eval, c, v, PancakeExp.c, hm, hq s hf, hb, h8, Bool.false_eq_true, if_false]
    rw [hd, word_cons]
    rfl

/-! ## The whole hash -/

/-- The key's sixteen octets at `k`, the message's `n` at `p`, and `r` bound. -/
def SipGiven (kv pv : Word) (key msg : Bytes) (s : PancakeState σ) : Prop :=
  s.locals "k" = some kv ∧ s.locals "p" = some pv ∧
    s.locals "n" = some (BitVec.ofNat 64 msg.length) ∧ (∃ r, s.locals "r" = some r) ∧
    readByteArray s.memory s.memaddrs s.be kv 16 = some key ∧
    readByteArray s.memory s.memaddrs s.be pv msg.length = some msg

theorem sipGiven_frame {kv pv : Word} {key msg : Bytes} {xs : List String} {s t : PancakeState σ}
    (h : SipGiven kv pv key msg s) (hf : Frame xs s t) (hk : "k" ∉ xs) (hp : "p" ∉ xs)
    (hn : "n" ∉ xs) (hr : "r" ∉ xs) : SipGiven kv pv key msg t := by
  obtain ⟨h1, h2, h3, ⟨r, h4⟩, h5, h6⟩ := h
  refine ⟨?_, ?_, ?_, ⟨r, ?_⟩, ?_, ?_⟩
  · rw [hf.1 _ hk, h1]
  · rw [hf.1 _ hp, h2]
  · rw [hf.1 _ hn, h3]
  · rw [hf.1 _ hr, h4]
  · rw [frame_read hf, h5]
  · rw [frame_read hf, h6]

theorem absorb_block (st : State) (bs : Bytes) (h : 8 ≤ bs.length) :
    absorb st bs = absorb (compress st (word (bs.take 8))) (bs.drop 8) := by
  match bs, h with
  | b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: rest, _ => simp [absorb]

theorem absorb_short (st : State) (bs : Bytes) (h : bs.length < 8) : absorb st bs = (st, bs) := by
  match bs, h with
  | [], _ | [_], _ | [_, _], _ | [_, _, _], _ | [_, _, _, _], _ | [_, _, _, _, _], _
  | [_, _, _, _, _, _], _ | [_, _, _, _, _, _, _], _ => simp [absorb]

/-- The state a key starts the hash in. -/
def initOf (key : Bytes) : State :=
  let k0 := word (key.take 8)
  let k1 := word ((key.drop 8).take 8)
  ⟨k0 ^^^ 0x736f6d6570736575, k1 ^^^ 0x646f72616e646f6d, k0 ^^^ 0x6c7967656e657261,
    k1 ^^^ 0x7465646279746573⟩

def xorE (x : String) (e : PancakeExp) : PancakeExp := .op .xor (v x) e

/-- After `o` octets of whole blocks: the state, and the rest still to absorb. -/
def Blocks (kv pv : Word) (key msg : Bytes) (s : PancakeState σ) : Prop :=
  ∃ o st, o ≤ msg.length ∧ SipGiven kv pv key msg s ∧ s.locals "off" = some (BitVec.ofNat 64 o) ∧
    Holds st s ∧ absorb (initOf key) msg = absorb st (msg.drop o) ∧
    (∃ x, s.locals "m" = some x) ∧ ∃ x, s.locals "j" = some x

/-- The octets left, fewer than eight, from the last down to index `i`, into `m`. -/
def TailInv (kv pv : Word) (key msg : Bytes) (s : PancakeState σ) : Prop :=
  ∃ o st i, o ≤ msg.length ∧ msg.length < o + 8 ∧ i ≤ msg.length - o ∧ SipGiven kv pv key msg s ∧
    s.locals "off" = some (BitVec.ofNat 64 o) ∧ Holds st s ∧
    absorb (initOf key) msg = (st, msg.drop o) ∧ s.locals "j" = some (BitVec.ofNat 64 i) ∧
    s.locals "m" = some (word ((msg.drop o).drop i)).toBitVec

/-- `r` gets SipHash-2-4 of the `n` octets from `p` under the key at `k`. -/
def sipA (kv pv : Word) (key msg : Bytes) : AProg σ :=
  .seq (.assign "m" (c 0)) <| bytesDown (v "k") 8 <|
  .seq (.assign "v0" (xorE "m" (c 0x736f6d6570736575))) <|
  .seq (.assign "v2" (xorE "m" (c 0x6c7967656e657261))) <|
  .seq (.assign "m" (c 0)) <| bytesDown (.op .add (v "k") (c 8)) 8 <|
  .seq (.assign "v1" (xorE "m" (c 0x646f72616e646f6d))) <|
  .seq (.assign "v3" (xorE "m" (c 0x7465646279746573))) <|
  .seq (.assign "off" (c 0)) <|
  .seq (.while_ (Blocks kv pv key msg) (.cmp .notLess (v "n") (.op .add (v "off") (c 8)))
    (.seq (.assign "m" (c 0)) <| bytesDown (.op .add (v "p") (v "off")) 8 <|
      .seq (.assign "v3" (xorE "v3" (v "m"))) <| roundK <| roundK <|
      .seq (.assign "v0" (xorE "v0" (v "m"))) <| .assign "off" (.op .add (v "off") (c 8)))) <|
  .seq (.assign "j" (.op .sub (v "n") (v "off"))) <| .seq (.assign "m" (c 0)) <|
  .seq (.while_ (TailInv kv pv key msg) (.cmp .less (c 0) (v "j"))
    (.seq (.assign "j" (.op .sub (v "j") (c 1)))
      (.assign "m" (byteE (.op .add (v "p") (v "off")) (v "j"))))) <|
  .seq (.assign "m" (.op .or_ (.shiftL (v "n") (c 56)) (v "m"))) <|
  .seq (.assign "v3" (xorE "v3" (v "m"))) <| roundK <| roundK <|
  .seq (.assign "v0" (xorE "v0" (v "m"))) <|
  .seq (.assign "v2" (xorE "v2" (c 255))) <| roundK <| roundK <| roundK <| roundK <|
  .assign "r" (.op .xor (.op .xor (.op .xor (v "v0") (v "v1")) (v "v2")) (v "v3"))

theorem holds_frame {st : State} {xs : List String} {s t : PancakeState σ} (h : Holds st s)
    (hf : Frame xs s t) (hxs : ∀ y, y ∈ vs → y ∉ xs) : Holds st t := by
  obtain ⟨h0, h1, h2, h3⟩ := h
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hf.1 _ (hxs _ (by decide)), h0]
  · rw [hf.1 _ (hxs _ (by decide)), h1]
  · rw [hf.1 _ (hxs _ (by decide)), h2]
  · rw [hf.1 _ (hxs _ (by decide)), h3]

/-- The octets of the block at `o` are those of the message there. -/
theorem block_bytes {s : PancakeState σ} {pv : Word} {msg : Bytes} {o : Nat}
    (hbuf : readByteArray s.memory s.memaddrs s.be pv msg.length = some msg)
    (ho : o + 8 ≤ msg.length) :
    ∀ i (hi : i < ((msg.drop o).take 8).length),
      memLoadByte s.memory s.memaddrs s.be (pv + BitVec.ofNat 64 o + BitVec.ofNat 64 i) =
        some ((msg.drop o).take 8)[i] := by
  intro i hi
  have hi' : i < 8 := by simp at hi; omega
  rw [BitVec.add_assoc, ← BitVec.ofNat_add, readByteArray_get hbuf (o + i) (by omega),
    List.getElem?_eq_getElem (by omega)]
  simp [List.getElem_take, List.getElem_drop]

/-- `v3 := v3 ^ m`, two rounds, `v0 := v0 ^ m`: the block `m` into the state. -/
theorem compress_wp (st : State) (mv : UInt64) (s : PancakeState σ) (h : Holds st s)
    (hm : s.locals "m" = some mv.toBitVec) {rest : AProg σ} {Q : Assn σ}
    (k : ∀ t, Holds (compress st mv) t → Frame vs s t → wp rest Q t) :
    wp (.seq (.assign "v3" (xorE "v3" (v "m"))) <| roundK <| roundK <|
      .seq (.assign "v0" (xorE "v0" (v "m"))) rest) Q s := by
  refine wp_seq (wp_assign (val := (st.v3 ^^^ mv).toBitVec) (by simp [eval, xorE, v, h.2.2.2, hm])
    h.2.2.2 (Q := fun t => Holds { st with v3 := st.v3 ^^^ mv } t ∧ Frame vs s t)
    ⟨holds_v3 h _, frame_set (by decide) _ _⟩) fun s1 ⟨h1, f1⟩ => ?_
  refine round_wp _ s1 h1 fun s2 h2 f2 => round_wp _ s2 h2 fun s3 h3 f3 => ?_
  refine wp_assign
    (val := ((sipRound (sipRound { st with v3 := st.v3 ^^^ mv })).v0 ^^^ mv).toBitVec)
    ?_ h3.1 (k _ (holds_v0 h3 _) ?_)
  · have hm3 : s3.locals "m" = some mv.toBitVec := by
      rw [f3.1 _ (by decide), f2.1 _ (by decide), f1.1 _ (by decide), hm]
    simp [eval, xorE, v, h3.1, hm3]
  · exact frame_trans (frame_trans (frame_trans f1 f2) f3) (frame_set (by decide) _ _)

/-- The locals the hash sets on the way. -/
def work : List String := ["m", "v0", "v1", "v2", "v3", "off", "j"]

/-- The locals a block or the key's words change. -/
def mvs : List String := ["m", "v0", "v1", "v2", "v3"]

/-- One whole block from `o`: the invariant again, `o + 8` octets absorbed. -/
theorem block_step (kv pv : Word) (key msg : Bytes) (s : PancakeState σ)
    (o : Nat) (st : State) (ho : o + 8 ≤ msg.length) (hg : SipGiven kv pv key msg s)
    (hoff : s.locals "off" = some (BitVec.ofNat 64 o)) (hh : Holds st s)
    (habs : absorb (initOf key) msg = absorb st (msg.drop o)) (hm : ∃ x, s.locals "m" = some x)
    (hj : ∃ x, s.locals "j" = some x) :
    wp (.seq (.assign "m" (c 0)) <| bytesDown (.op .add (v "p") (v "off")) 8 <|
      .seq (.assign "v3" (xorE "v3" (v "m"))) <| roundK <| roundK <|
      .seq (.assign "v0" (xorE "v0" (v "m"))) <| .assign "off" (.op .add (v "off") (c 8)))
      (Blocks (σ := σ) kv pv key msg) s := by
  obtain ⟨mx, hmx⟩ := hm
  obtain ⟨jx, hjx⟩ := hj
  have hbs : ((msg.drop o).take 8).length = 8 := by simp; omega
  refine wp_seq (wp_assign (val := 0#64) (by simp [eval, c, PancakeExp.c]) hmx
    (Q := fun s1 => Frame ["m"] s s1 ∧
      s1.locals "m" = some (word (((msg.drop o).take 8).drop 8)).toBitVec)
    ⟨frame_set (by decide) _ _, by simp [setLocal, word]⟩) fun s1 ⟨f1, hm1⟩ => ?_
  refine bytesDown_wp (qv := pv + BitVec.ofNat 64 o) s1 (fun t ft => ?_)
    (fun i hi => by rw [f1.2.1, f1.2.2.1, f1.2.2.2]; exact block_bytes hg.2.2.2.2.2 ho i hi)
    (fun t ft hmt => ?_) 8 s1 (by omega) (frame_refl _ _) hm1
  · have := frame_trans f1 ft
    simp [eval, v, this.1 "p" (by decide), this.1 "off" (by decide), hg.2.1, hoff]
  · have ft' := frame_trans f1 ft
    refine compress_wp st _ t (holds_frame hh ft' (by decide)) hmt fun u hu fu => ?_
    have fall : Frame mvs s u :=
      frame_trans (frame_mono ft' (by decide)) (frame_mono fu (by decide))
    have hoffu : u.locals "off" = some (BitVec.ofNat 64 o) := by rw [fall.1 _ (by decide), hoff]
    refine wp_assign (val := BitVec.ofNat 64 (o + 8)) (by simp [eval, v, c, PancakeExp.c, hoffu,
      BitVec.ofNat_add]) hoffu ⟨o + 8, compress st (word ((msg.drop o).take 8)), ho,
      sipGiven_frame hg (frame_trans (frame_mono (ys := work) fall (by decide))
        (frame_set (xs := work) (by decide) _ _)) (by decide) (by decide) (by decide) (by decide),
      by simp [setLocal], holds_frame hu (frame_set (xs := ["off"]) (by decide) _ _) (by decide),
      ?_,
      ⟨(word ((msg.drop o).take 8)).toBitVec, ?_⟩, ⟨jx, ?_⟩⟩
    · rw [habs, absorb_block st _ (by simp; omega), List.drop_drop]
    · simp only [setLocal_ne _ _ (show "m" ≠ "off" by decide)]
      rw [fu.1 "m" (by decide)]
      exact hmt
    · simp only [setLocal_ne _ _ (show "j" ≠ "off" by decide)]
      rw [fall.1 "j" (by decide)]
      exact hjx

theorem ofNat_sub_ofNat {a b : Nat} (h : b ≤ a) (ha : a < 2 ^ 64) :
    BitVec.ofNat 64 a - BitVec.ofNat 64 b = BitVec.ofNat 64 (a - b) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
  omega

/-- Leaving the blocks: the octets left, fewer than eight, all still to read. -/
theorem blocks_exit (kv pv : Word) (key msg : Bytes) (hlen : msg.length < 2 ^ 62)
    (s : PancakeState σ) (o : Nat) (st : State) (ho : o ≤ msg.length) (hlt : msg.length < o + 8)
    (hg : SipGiven kv pv key msg s) (hoff : s.locals "off" = some (BitVec.ofNat 64 o))
    (hh : Holds st s) (habs : absorb (initOf key) msg = absorb st (msg.drop o))
    (hm : ∃ x, s.locals "m" = some x) (hj : ∃ x, s.locals "j" = some x) {after : AProg σ}
    {Q : Assn σ} :
    wp (.seq (.assign "j" (.op .sub (v "n") (v "off"))) (.seq (.assign "m" (c 0))
      (.seq (.while_ (TailInv kv pv key msg) (.cmp .less (c 0) (v "j"))
        (.seq (.assign "j" (.op .sub (v "j") (c 1)))
          (.assign "m" (byteE (.op .add (v "p") (v "off")) (v "j"))))) after))) Q s := by
  obtain ⟨mx, hmx⟩ := hm
  obtain ⟨jx, hjx⟩ := hj
  refine wp_seq (wp_assign (val := BitVec.ofNat 64 (msg.length - o))
    (by simp [eval, v, hg.2.2.1, hoff, ofNat_sub_ofNat ho (by omega)]) hjx
    (Q := fun s1 => s1 =
      { s with locals := (setLocal s.locals "j" (BitVec.ofNat 64 (msg.length - o))) })
    rfl) fun s1 h1 => ?_
  subst h1
  refine wp_assign (val := 0#64) (by simp [eval, c, PancakeExp.c])
    (by simp only [setLocal_ne _ _ (show "m" ≠ "j" by decide)]; exact hmx) ?_
  have f := frame_trans
    (frame_set (x := "j") (xs := ["j", "m"]) (by decide) s (BitVec.ofNat 64 (msg.length - o)))
    (frame_set (x := "m") (xs := ["j", "m"]) (by decide)
      { s with locals := setLocal s.locals "j" (BitVec.ofNat 64 (msg.length - o)) } (0#64))
  simp only [wp]
  refine ⟨o, st, msg.length - o, ho, hlt, Nat.le_refl _, sipGiven_frame hg f (by decide) (by decide)
    (by decide) (by decide), by rw [f.1 _ (by decide), hoff], holds_frame hh f (by decide),
    by rw [habs, absorb_short st _ (by simp; omega)], ?_, ?_⟩
  · simp [setLocal]
  · rw [List.drop_eq_nil_of_le (by simp)]
    simp [setLocal, word]

/-- One octet of the tail, the last not yet read, below the ones `m` holds. -/
theorem tail_step (kv pv : Word) (key msg : Bytes)
    (s : PancakeState σ) (o : Nat) (st : State) (i : Nat) (ho : o ≤ msg.length)
    (hlt : msg.length < o + 8) (hi : i ≤ msg.length - o) (hi0 : 0 < i)
    (hg : SipGiven kv pv key msg s) (hoff : s.locals "off" = some (BitVec.ofNat 64 o))
    (hh : Holds st s) (habs : absorb (initOf key) msg = (st, msg.drop o))
    (hj : s.locals "j" = some (BitVec.ofNat 64 i))
    (hm : s.locals "m" = some (word ((msg.drop o).drop i)).toBitVec) :
    wp (.seq (.assign "j" (.op .sub (v "j") (c 1)))
      (.assign "m" (byteE (.op .add (v "p") (v "off")) (v "j"))))
      (TailInv (σ := σ) kv pv key msg) s := by
  have hlt' : i - 1 < (msg.drop o).length := by simp; omega
  have hd : (msg.drop o).drop (i - 1) = (msg.drop o)[i - 1] :: (msg.drop o).drop i := by
    rw [List.drop_eq_getElem_cons hlt']
    congr 2
    omega
  refine wp_seq (wp_assign (val := BitVec.ofNat 64 (i - 1))
    (by simp [eval, v, c, PancakeExp.c, hj, ofNat_sub_ofNat hi0 (by omega)]) hj
    (Q := fun s1 => s1 = { s with locals := setLocal s.locals "j" (BitVec.ofNat 64 (i - 1)) })
    rfl) fun s1 h1 => ?_
  subst h1
  have hb :
      memLoadByte s.memory s.memaddrs s.be (pv + BitVec.ofNat 64 o + BitVec.ofNat 64 (i - 1)) =
      some (msg.drop o)[i - 1] := by
    rw [BitVec.add_assoc, ← BitVec.ofNat_add,
      readByteArray_get hg.2.2.2.2.2 (o + (i - 1)) (by omega),
      List.getElem?_eq_getElem (by omega)]
    simp [List.getElem_drop]
  have h8 : (decide ((8#64).toNat ≠ 0) && decide ((8#64).toNat ≥ 64)) = false := by decide
  have hm1 : (setLocal s.locals "j" (BitVec.ofNat 64 (i - 1))) "m" =
      some (word ((msg.drop o).drop i)).toBitVec := by
    rw [setLocal_ne _ _ (by decide)]; exact hm
  refine wp_assign (val := (word ((msg.drop o).drop (i - 1))).toBitVec) ?_ hm1 ?_
  · simp only [byteE, eval, v, c, PancakeExp.c, hm1, setLocal_same,
      setLocal_ne _ _ (show "p" ≠ "j" by decide), setLocal_ne _ _ (show "off" ≠ "j" by decide),
      hg.2.1, hoff, hb, h8, Bool.false_eq_true, if_false]
    rw [hd, word_cons]
    rfl
  · have f := frame_trans
      (frame_set (x := "j") (xs := ["j", "m"]) (by decide) s (BitVec.ofNat 64 (i - 1)))
      (frame_set (x := "m") (xs := ["j", "m"]) (by decide)
        { s with locals := setLocal s.locals "j" (BitVec.ofNat 64 (i - 1)) }
        (word ((msg.drop o).drop (i - 1))).toBitVec)
    exact ⟨o, st, i - 1, ho, hlt, by omega, sipGiven_frame hg f (by decide) (by decide) (by decide)
      (by decide), by rw [f.1 _ (by decide), hoff], holds_frame hh f (by decide), habs,
      by simp [setLocal], by simp [setLocal]⟩

/-- The tag from the state after the last block: `v2` flipped, four rounds, the four words. -/
def fin (st : State) : UInt64 :=
  let s := sipRound (sipRound (sipRound (sipRound { st with v2 := st.v2 ^^^ 0xff })))
  s.v0 ^^^ s.v1 ^^^ s.v2 ^^^ s.v3

theorem tag_eq (key msg : Bytes) (st : State) (rest : Bytes)
    (h : absorb (initOf key) msg = (st, rest)) :
    tag key msg = fin (compress st ((msg.length.toUInt64 <<< 56) ||| word rest)) := by
  unfold tag siphash
  simp only [initOf] at h
  simp only [h]
  rfl

theorem final_wp (st : State) (s : PancakeState σ) (h : Holds st s)
    (hr : ∃ x, s.locals "r" = some x)
    {Q : Assn σ} (hq : ∀ t, t.locals "r" = some (fin st).toBitVec → Q t) :
    wp (.seq (.assign "v2" (xorE "v2" (c 255))) <| roundK <| roundK <| roundK <| roundK <|
      .assign "r" (.op .xor (.op .xor (.op .xor (v "v0") (v "v1")) (v "v2")) (v "v3"))) Q s := by
  obtain ⟨rx, hrx⟩ := hr
  refine wp_seq (wp_assign (val := (st.v2 ^^^ 0xff).toBitVec)
    (by simp [eval, xorE, v, c, PancakeExp.c, h.2.2.1]) h.2.2.1
    (Q := fun s1 => Holds { st with v2 := st.v2 ^^^ 0xff } s1 ∧ s1.locals "r" = some rx)
    ⟨holds_v2 h _, by simp [setLocal, hrx]⟩) fun s1 ⟨h1, hr1⟩ => ?_
  refine round_wp _ s1 h1 fun s2 h2 f2 => round_wp _ s2 h2 fun s3 h3 f3 =>
    round_wp _ s3 h3 fun s4 h4 f4 => round_wp _ s4 h4 fun s5 h5 f5 => ?_
  have hr5 : s5.locals "r" = some rx := by
    rw [f5.1 _ (by decide), f4.1 _ (by decide), f3.1 _ (by decide), f2.1 _ (by decide), hr1]
  refine wp_assign (val := (fin st).toBitVec) ?_ hr5 (hq _ (by simp [setLocal]))
  simp [eval, v, h5.1, h5.2.1, h5.2.2.1, h5.2.2.2, fin]

/-- The last block, the length in its top octet, then the tag into `r`. -/
theorem tail_exit (kv pv : Word) (key msg : Bytes)
    (s : PancakeState σ) (o : Nat) (st : State) (hg : SipGiven kv pv key msg s) (hh : Holds st s)
    (habs : absorb (initOf key) msg = (st, msg.drop o))
    (hm : s.locals "m" = some (word (msg.drop o)).toBitVec) :
    wp (.seq (.assign "m" (.op .or_ (.shiftL (v "n") (c 56)) (v "m"))) <|
      .seq (.assign "v3" (xorE "v3" (v "m"))) <| roundK <| roundK <|
      .seq (.assign "v0" (xorE "v0" (v "m"))) <|
      .seq (.assign "v2" (xorE "v2" (c 255))) <| roundK <| roundK <| roundK <| roundK <|
      .assign "r" (.op .xor (.op .xor (.op .xor (v "v0") (v "v1")) (v "v2")) (v "v3")))
      (fun t => t.locals "r" = some (tag key msg).toBitVec) s := by
  have hm56 : (decide ((56#64).toNat ≠ 0) && decide ((56#64).toNat ≥ 64)) = false := by decide
  refine wp_seq (wp_assign
    (val := ((msg.length.toUInt64 <<< 56) ||| word (msg.drop o)).toBitVec) ?_ hm
    (Q := fun s1 => s1 = { s with locals := (setLocal s.locals "m"
      ((msg.length.toUInt64 <<< 56) ||| word (msg.drop o)).toBitVec) }) rfl) fun s1 h1 => ?_
  · simp only [eval, v, c, PancakeExp.c, hg.2.2.1, hm, hm56, Bool.false_eq_true, if_false]
    simp
    rfl
  · subst h1
    have f := frame_set (x := "m") (xs := ["m"]) (by decide) s
      ((msg.length.toUInt64 <<< 56) ||| word (msg.drop o)).toBitVec
    refine compress_wp st ((msg.length.toUInt64 <<< 56) ||| word (msg.drop o)) _
      (holds_frame hh f (by decide)) (by simp [setLocal])
      fun t ht ft => final_wp _ t ht ?_ fun u hu => by rw [tag_eq key msg st _ habs]; exact hu
    obtain ⟨rx, hrx⟩ := hg.2.2.2.1
    exact ⟨rx, by rw [ft.1 _ (by decide), f.1 _ (by decide), hrx]⟩

/-- The key's octets from `8 * h`: those of its word `h`. -/
theorem key_bytes {s : PancakeState σ} {kv : Word} {key : Bytes} (h : Nat) (hh : h < 2)
    (hbuf : readByteArray s.memory s.memaddrs s.be kv 16 = some key) :
    ∀ i (hi : i < ((key.drop (8 * h)).take 8).length),
      memLoadByte s.memory s.memaddrs s.be (kv + BitVec.ofNat 64 (8 * h) + BitVec.ofNat 64 i) =
        some ((key.drop (8 * h)).take 8)[i] := by
  intro i hi
  have hk := readByteArray_length hbuf
  have hi' : i < 8 := by simp at hi; omega
  rw [BitVec.add_assoc, ← BitVec.ofNat_add, readByteArray_get hbuf (8 * h + i) (by omega),
    List.getElem?_eq_getElem (by omega)]
  simp [List.getElem_take, List.getElem_drop]

/-- `m := 0`, then the eight octets from `q` into `m`. -/
theorem word_wp {q : PancakeExp} {qv : Word} {bs : Bytes} {rest : AProg σ} {Q : Assn σ}
    (s : PancakeState σ) (hlen : bs.length = 8) (hm : ∃ x, s.locals "m" = some x)
    (hq : ∀ t, Frame ["m"] s t → eval t q = some qv)
    (hbytes : ∀ i (hi : i < bs.length),
      memLoadByte s.memory s.memaddrs s.be (qv + BitVec.ofNat 64 i) = some bs[i])
    (k : ∀ t, Frame ["m"] s t → t.locals "m" = some (word bs).toBitVec → wp rest Q t) :
    wp (.seq (.assign "m" (c 0)) (bytesDown q 8 rest)) Q s := by
  obtain ⟨mx, hmx⟩ := hm
  have f := frame_set (x := "m") (xs := ["m"]) (by decide) s (0#64)
  refine wp_seq (wp_assign (val := 0#64) (by simp [eval, c, PancakeExp.c]) hmx
    (Q := fun s1 => s1 = { s with locals := setLocal s.locals "m" (0#64) }) rfl) fun s1 h1 => ?_
  subst h1
  refine bytesDown_wp _ (fun t ft => hq t (frame_trans f ft))
    (fun i hi => by rw [f.2.1, f.2.2.1, f.2.2.2]; exact hbytes i hi)
    (fun t ft hmt => k t (frame_trans f ft) hmt) 8 _ (by omega) (frame_refl _ _) ?_
  rw [List.drop_eq_nil_of_le (by omega)]
  simp [setLocal, word]

/-- Besides what `SipGiven` names, every local the hash sets is bound. -/
def SipPre (kv pv : Word) (key msg : Bytes) (s : PancakeState σ) : Prop :=
  SipGiven kv pv key msg s ∧ ∀ y, y ∈ work → ∃ x, s.locals y = some x

/-- The key's two words into the state, `off := 0`: the blocks' invariant, none absorbed. -/
theorem sip_entry (kv pv : Word) (key msg : Bytes) (s : PancakeState σ) (h : SipPre kv pv key msg s)
    {body after : AProg σ} {Q : Assn σ} :
    wp (.seq (.assign "m" (c 0)) <| bytesDown (v "k") 8 <|
      .seq (.assign "v0" (xorE "m" (c 0x736f6d6570736575))) <|
      .seq (.assign "v2" (xorE "m" (c 0x6c7967656e657261))) <|
      .seq (.assign "m" (c 0)) <| bytesDown (.op .add (v "k") (c 8)) 8 <|
      .seq (.assign "v1" (xorE "m" (c 0x646f72616e646f6d))) <|
      .seq (.assign "v3" (xorE "m" (c 0x7465646279746573))) <|
      .seq (.assign "off" (c 0)) <| .seq (.while_ (Blocks kv pv key msg) (.cmp .notLess (v "n")
        (.op .add (v "off") (c 8))) body) after) Q s := by
  obtain ⟨hg, hb⟩ := h
  have hk := readByteArray_length hg.2.2.2.2.1
  have k0 := key_bytes (s := s) 0 (by decide) hg.2.2.2.2.1
  simp only [Nat.mul_zero, BitVec.add_zero, List.drop_zero] at k0
  refine word_wp (qv := kv) (bs := key.take 8) s (by simp; omega) (hb "m" (by decide))
    (fun t ft => by simp [eval, v, ft.1 "k" (by decide), hg.1]) k0 fun s1 f1 hm1 => ?_
  obtain ⟨v0x, hv0⟩ := hb "v0" (by decide)
  obtain ⟨v1x, hv1⟩ := hb "v1" (by decide)
  obtain ⟨v2x, hv2⟩ := hb "v2" (by decide)
  obtain ⟨v3x, hv3⟩ := hb "v3" (by decide)
  obtain ⟨ox, hox⟩ := hb "off" (by decide)
  obtain ⟨jx, hjx⟩ := hb "j" (by decide)
  -- `v0` and `v2` from the first word
  refine wp_seq (wp_assign (val := (initOf key).v0.toBitVec)
    (by simp [eval, xorE, v, c, PancakeExp.c, hm1, initOf]) (by rw [f1.1 _ (by decide)]; exact hv0)
    (Q := fun s2 => s2 = { s1 with locals := setLocal s1.locals "v0" (initOf key).v0.toBitVec })
    rfl) fun s2 h2 => ?_
  subst h2
  refine wp_seq (wp_assign (val := (initOf key).v2.toBitVec)
    (by simp [eval, xorE, v, c, PancakeExp.c, setLocal_ne _ _ (show "m" ≠ "v0" by decide), hm1,
      initOf])
    (by simp only [setLocal_ne _ _ (show "v2" ≠ "v0" by decide)]; rw [f1.1 _ (by decide)]
        exact hv2)
    (Q := fun s2 => s2 = { s1 with locals :=
      (setLocal (setLocal s1.locals "v0" (initOf key).v0.toBitVec)
      "v2" (initOf key).v2.toBitVec) }) rfl) fun s2 h2 => ?_
  subst h2
  -- the second word
  have k1 := key_bytes (s := s) 1 (by decide) hg.2.2.2.2.1
  simp only [Nat.mul_one] at k1
  refine word_wp (qv := kv + BitVec.ofNat 64 8) (bs := (key.drop 8).take 8) _ (by simp; omega)
    ⟨_, by simp only [setLocal_ne _ _ (show "m" ≠ "v2" by decide),
      setLocal_ne _ _ (show "m" ≠ "v0" by decide)]; exact hm1⟩
    (fun t ft => by simp [eval, v, c, PancakeExp.c, ft.1 "k" (by decide), setLocal_ne,
      f1.1 "k" (by decide), hg.1])
    (fun i hi => by rw [f1.2.1, f1.2.2.1, f1.2.2.2]; exact k1 i hi) fun s3 f3 hm3 => ?_
  have l3 : ∀ y, y ∉ ["m"] → s3.locals y = _ := f3.1
  have hv1' : s3.locals "v1" = some v1x := by
    rw [l3 _ (by decide)]; simp [setLocal, f1.1 "v1" (by decide), hv1]
  have hv3' : s3.locals "v3" = some v3x := by
    rw [l3 _ (by decide)]; simp [setLocal, f1.1 "v3" (by decide), hv3]
  refine wp_seq (wp_assign (val := (initOf key).v1.toBitVec)
    (by simp [eval, xorE, v, c, PancakeExp.c, hm3, initOf]) hv1'
    (Q := fun s4 => s4 = { s3 with locals := setLocal s3.locals "v1" (initOf key).v1.toBitVec })
    rfl) fun s4 h4 => ?_
  subst h4
  refine wp_seq (wp_assign (val := (initOf key).v3.toBitVec)
    (by simp [eval, xorE, v, c, PancakeExp.c, setLocal_ne _ _ (show "m" ≠ "v1" by decide), hm3,
      initOf])
    (by simp only [setLocal_ne _ _ (show "v3" ≠ "v1" by decide)]; exact hv3')
    (Q := fun s4 => s4 = { s3 with locals := (setLocal (setLocal s3.locals "v1"
      (initOf key).v1.toBitVec) "v3" (initOf key).v3.toBitVec) }) rfl) fun s4 h4 => ?_
  subst h4
  refine wp_seq (wp_assign (val := 0#64) (old := ox) (by simp [eval, c, PancakeExp.c])
    (by simp only [setLocal_ne _ _ (show "off" ≠ "v3" by decide),
      setLocal_ne _ _ (show "off" ≠ "v1" by decide)]
        rw [l3 _ (by decide)]; simp [setLocal, f1.1 "off" (by decide), hox])
    (Q := fun s5 => s5 = { s3 with locals := (setLocal (setLocal (setLocal s3.locals "v1"
      (initOf key).v1.toBitVec) "v3" (initOf key).v3.toBitVec) "off" (0#64)) }) rfl) fun s5 h5 => ?_
  subst h5
  simp only [wp]
  have fw : Frame work s _ := frame_trans (frame_mono f1 (by decide)) (frame_trans
    (frame_set (x := "v0") (xs := work) (by decide) _ (initOf key).v0.toBitVec) (frame_trans
      (frame_set (x := "v2") (xs := work) (by decide) _ (initOf key).v2.toBitVec)
        (frame_trans (frame_mono f3 (by decide))
        (frame_trans (frame_set (x := "v1") (xs := work) (by decide) _ (initOf key).v1.toBitVec)
          (frame_trans (frame_set (x := "v3") (xs := work) (by decide) _ (initOf key).v3.toBitVec)
          (frame_set (x := "off") (xs := work) (by decide) _ (0#64)))))))
  refine ⟨0, initOf key, Nat.zero_le _, sipGiven_frame hg fw (by decide) (by decide) (by decide)
    (by decide), by simp [setLocal], ⟨?_, ?_, ?_, ?_⟩, by simp,
    ⟨(word ((key.drop 8).take 8)).toBitVec, ?_⟩, ⟨jx, ?_⟩⟩
  · simp [setLocal]; rw [l3 _ (by decide)]; simp [setLocal]
  · simp [setLocal]
  · simp [setLocal]; rw [l3 _ (by decide)]; simp [setLocal]
  · simp [setLocal]
  · simp [setLocal]; exact hm3
  · simp [setLocal]; rw [l3 _ (by decide)]; simp [setLocal, f1.1 "j" (by decide), hjx]

theorem vc_roundK (rest : AProg σ) (Q : Assn σ) : vc (roundK rest) Q = vc rest Q := by
  simp only [roundK, vc_seq, vc_assign, true_and]

theorem vc_bytesDown (q : PancakeExp) (rest : AProg σ) (Q : Assn σ) :
    ∀ i, vc (bytesDown q i rest) Q = vc rest Q
  | 0 => rfl
  | i + 1 => by simp only [bytesDown, vc_seq, vc_assign, vc_bytesDown q rest Q i, true_and]

theorem sip_vc (kv pv : Word) (key msg : Bytes) (hlen : msg.length < 2 ^ 62) :
    vc (sipA (σ := σ) kv pv key msg) (fun t => t.locals "r" = some (tag key msg).toBitVec) := by
  simp only [sipA, vc_seq, vc_assign, vc_while, vc_bytesDown, vc_roundK, true_and, and_true]
  refine ⟨⟨fun s k h => h, fun s ⟨o, st, ho, hg, hoff, hh, habs, hm, hj⟩ => ?_⟩,
    ⟨fun s k h => h, fun s ⟨o, st, i, ho, hlt, hi, hg, hoff, hh, habs, hj, hm⟩ => ?_⟩⟩
  · have e8 : BitVec.ofNat 64 o + BitVec.ofNat 64 8 = BitVec.ofNat 64 (o + 8) := by
      rw [BitVec.ofNat_add]
    simp only [eval, v, c, PancakeExp.c, hg.2.2.1, hoff, e8,
      signedLt_small (by omega : msg.length < 2 ^ 63) (by omega : o + 8 < 2 ^ 63)]
    by_cases hb : msg.length < o + 8
    · simp only [hb, decide_true, if_true]
      exact blocks_exit kv pv key msg hlen s o st ho hb hg hoff hh habs hm hj
    · simp only [hb, decide_false, Bool.false_eq_true, if_false,
        show ((1 : Word) = 0) = False by decide]
      exact block_step kv pv key msg s o st (by omega) hg hoff hh habs hm ⟨_, hj.choose_spec⟩
  · simp only [eval, v, c, PancakeExp.c, hj,
      signedLt_small (by omega : (0 : Nat) < 2 ^ 63) (by omega : i < 2 ^ 63)]
    by_cases h0 : 0 < i
    · simp only [h0, decide_true, if_true, show ((1 : Word) = 0) = False by decide, if_false]
      exact tail_step kv pv key msg s o st i ho hlt hi h0 hg hoff hh habs hj hm
    · have : i = 0 := by omega
      subst this
      simp only [h0, decide_false, Bool.false_eq_true, if_false, if_true]
      exact tail_exit kv pv key msg s o st hg hh habs (by simpa using hm)

theorem sip_wp (kv pv : Word) (key msg : Bytes) (s : PancakeState σ) (h : SipPre kv pv key msg s) :
    wp (sipA kv pv key msg) (fun t => t.locals "r" = some (tag key msg).toBitVec) s := by
  unfold sipA
  exact sip_entry kv pv key msg s h

/-- **The program computes SipHash-2-4**: from a state where `k` names a key of sixteen octets and
`p` and `n` a message in memory, a run that finishes normally has `r` equal to the tag. -/
theorem sip_safe (o : Oracle σ) (kv pv : Word) (key msg : Bytes) (hlen : msg.length < 2 ^ 62) :
    Safe.Safe o (SipPre kv pv key msg) (sipA (σ := σ) kv pv key msg).erase
      (fun t => t.locals "r" = some (tag key msg).toBitVec) :=
  Safe.conseq (wp_sound o _ _ (fun _ _ h => h) (sip_vc kv pv key msg hlen))
    (fun s h => sip_wp kv pv key msg s h) (fun _ h => h)

private def sipLocals : String → Option Value :=
  setLocal (setLocal (setLocal (setLocal (setLocal (setLocal (setLocal (setLocal (setLocal (setLocal
    (setLocal (fun _ => none) "k" 64) "p" 64) "n" 0) "r" 0) "m" 0) "v0" 0) "v1" 0) "v2" 0) "v3" 0)
    "off" 0) "j" 0

/-- The hash's premise can hold: a key of zeros, an empty message. -/
theorem sipPre_witness :
    SipPre (σ := Unit) 64 64 (List.replicate 16 0) [] { bareState () with locals := sipLocals } :=
  ⟨⟨by simp [sipLocals, setLocal], by simp [sipLocals, setLocal], by simp [sipLocals, setLocal],
    ⟨0, by simp [sipLocals, setLocal]⟩, by decide, rfl⟩,
    fun y hy => by simp [work] at hy; rcases hy with h | h | h | h | h | h | h <;> subst h <;>
      exact ⟨0, by simp [sipLocals, setLocal]⟩⟩

/-- The hash's premise without the locals it sets can hold. -/
theorem sipGiven_witness :
    SipGiven (σ := Unit) 64 64 (List.replicate 16 0) [] { bareState () with locals := sipLocals } :=
  sipPre_witness.1

open DN.News.SipProg in
/-- The printed hash is the one `sip_safe` is about. -/
theorem sip_lowering (kv pv : Word) (key msg : Bytes) :
    Lower.lowerStmtsFold sipSrc = some (sipA (σ := σ) kv pv key msg).erase := rfl

private def fourLocals : String → Option Value :=
  setLocal (setLocal (setLocal (setLocal (fun _ => none) "v0" 1) "v1" 2) "v2" 3) "v3" 4

/-- The locals can hold a state. -/
theorem holds_witness : Holds ⟨1, 2, 3, 4⟩ { bareState () with locals := fourLocals } := by
  simp [Holds, fourLocals, setLocal]

end DN.News.SipHashCode
