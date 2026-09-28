-- SPDX-License-Identifier: AGPL-3.0-or-later
import DN.News.Framer
import DN.Compiler.Kernels
import DN.Compiler.Clock

/-!
# DN.News.FramerCode

The framer as a program of the subset the compiler prints, and the proof that the program makes
exactly the framer's steps (`DN.News.Framer`), so that what it reports is the specification's
verdict (`DN.News.FrameSpec`).

The state of a connection lives in memory at `blk`: the words at `blk`, `blk + 8` and `blk + 16`
hold the length of the line so far, whether its last byte was a CR, and whether it is already
spoiled; the verdict goes to `blk + 24` (its kind, zero when no line ended) and `blk + 32` (how many
bytes it keeps); the bytes of the line are kept from `blk + 40`. `dn_frame_line(blk, p, n, i)`
reads the received bytes at `p` from position `i` up to `n`, stops after the first line that ends,
and returns the position it stopped at; a negative `n` or `i`, or `i` past `n`, it refuses before
reading anything. `dn_frame_block` does the same for a block, whose phase, whether it is spoiled
and its size are the first three words, and the bytes it holds are kept from `blk + 40`.

The framer's statements are proven apart from the function around them, as a session will run
them inside its `main`: from a state holding the framer's state they spend one clock tick a byte
and then run whatever follows them, or time out when the clock is short (`lineFrag_run`,
`blockFrag_run`). The exported functions add the checks of their arguments and the return
(`frameLine_run`, `frameBlock_run`, `frameLine_refuses`, `frameBlock_refuses`).
-/

namespace DN.News.FramerCode

open DN.Compiler DN.Compiler.Syntax DN.Compiler.Region DN.Compiler.Bytes DN.Compiler.Clock
open DN.News.FrameSpec DN.News.Framer

variable {σ : Type}

/-! ## The program -/

/-- What a line's verdict is called in memory. -/
def kindCode : Kind → Nat
  | .command => 1
  | .malformed => 2
  | .overlong => 3

/-- Reading bytes until the chunk is read or a line ends. -/
def lineLoop (lim : Nat) : PStmt :=
  .while (eAnd (eLt (v "i") (v "n")) (eEq (v "kind") (n 0)))
    [.assign "b" (.loadb (eAdd (v "p") (v "i"))),
     .assign "i" (eAdd (v "i") (n 1)),
     .ite (eEq (v "b") (n 10))
       [.ite (eLe (n lim) (v "len"))
          [.assign "kind" (n 3), .assign "kept" (v "len")]
          [.ite (eAnd (v "cr") (eEq (v "bad") (n 0)))
             [.assign "kind" (n 1), .assign "kept" (eSub (v "len") (n 1))]
             [.assign "kind" (n 2), .assign "kept" (v "len")]],
        .assign "len" (n 0), .assign "cr" (n 0), .assign "bad" (n 0)]
       [.ite (v "cr") [.assign "bad" (n 1)] [],
        .ite (eEq (v "b") (n 0)) [.assign "bad" (n 1)] [],
        .assign "cr" (eEq (v "b") (n 13)),
        .ite (eLt (v "len") (n lim))
          [.storeb (eAdd (eAdd (v "blk") (n 40)) (v "len")) (v "b"),
           .assign "len" (eAdd (v "len") (n 1))]
          []]]

/-- The framer as statements that declare nothing: the state is read from `blk`, the loop runs,
the state and the verdict are written back. `len`, `cr`, `bad`, `kind`, `kept` and `b` are the
caller's working names, and `i` is where reading starts and where it stopped. -/
def lineFrag (lim : Nat) : List PStmt :=
  [.assign "len" (.loadw 1 (v "blk")),
   .assign "cr" (.loadw 1 (eAdd (v "blk") (n 8))),
   .assign "bad" (.loadw 1 (eAdd (v "blk") (n 16))),
   .assign "kind" (n 0),
   .assign "kept" (n 0),
   lineLoop lim,
   .store (v "blk") (v "len"),
   .store (eAdd (v "blk") (n 8)) (v "cr"),
   .store (eAdd (v "blk") (n 16)) (v "bad"),
   .store (eAdd (v "blk") (n 24)) (v "kind"),
   .store (eAdd (v "blk") (n 32)) (v "kept")]

/-- The working names, declared. -/
def lineDecs : List PStmt :=
  [.dec "len" (n 0), .dec "cr" (n 0), .dec "bad" (n 0), .dec "kind" (n 0), .dec "kept" (n 0),
   .dec "b" (n 0)]

/-- The exported function's run: the working names, the framer, the position it stopped at. -/
def lineRun (lim : Nat) : List PStmt := lineDecs ++ lineFrag lim ++ [.ret (v "i")]

/-- A negative length or position, or a position past the length, is refused before anything is
read. -/
def refused : Nat := 2 ^ 32 - 1

/-- `dn_frame_line(blk, p, n, i)`, for lines of at most `lim` octets. -/
def frameLine (name : String) (lim : Nat) : PFun :=
  { name, exported := true, params := [(1, "blk"), (1, "p"), (1, "n"), (1, "i")],
    body := Kernels.rejectNegative ["n", "i"] [.ret (n refused)]
      [.ite (eLt (v "n") (v "i")) [.ret (n refused)] (lineRun lim)] }

/-! ## The program as the model runs it -/

private def c (k : Nat) : PancakeExp := .const (BitVec.ofNat 64 k)
private def x (name : String) : PancakeExp := .var name
private def add (a b : PancakeExp) : PancakeExp := .op .add a b
private def set (name : String) (k : Nat) : PancakeProg := .assign name (c k)

def lineEndP (lim : Nat) : PancakeProg :=
  .seq
    (.cond (.cmp .notLess (x "len") (c lim))
      (.seq (set "kind" 3) (.assign "kept" (x "len")))
      (.cond (.op .and_ (x "cr") (.cmp .equal (x "bad") (c 0)))
        (.seq (set "kind" 1) (.assign "kept" (.op .sub (x "len") (c 1))))
        (.seq (set "kind" 2) (.assign "kept" (x "len")))))
    (.seq (set "len" 0) (.seq (set "cr" 0) (set "bad" 0)))

def lineMoreP (lim : Nat) : PancakeProg :=
  .seq (.cond (x "cr") (set "bad" 1) .skip)
  (.seq (.cond (.cmp .equal (x "b") (c 0)) (set "bad" 1) .skip)
  (.seq (.assign "cr" (.cmp .equal (x "b") (c 13)))
    (.cond (.cmp .less (x "len") (c lim))
      (.seq (.storeByte (add (add (x "blk") (c 40)) (x "len")) (x "b"))
        (.assign "len" (add (x "len") (c 1))))
      .skip)))

def lineBodyP (lim : Nat) : PancakeProg :=
  .seq (.assign "b" (.loadByte (add (x "p") (x "i"))))
  (.seq (.assign "i" (add (x "i") (c 1)))
    (.cond (.cmp .equal (x "b") (c 10)) (lineEndP lim) (lineMoreP lim)))

def lineGuardP : PancakeExp := .op .and_ (.cmp .less (x "i") (x "n")) (.cmp .equal (x "kind") (c 0))

theorem lineLoop_lower (lim : Nat) :
    Lower.lowerStmt1 (lineLoop lim) = some (.while_ lineGuardP (lineBodyP lim)) := rfl

/-! ## One byte -/

/-- A flag as the program holds it. -/
def bw (b : Bool) : Word := if b then 1 else 0

/-- The locals of the loop: the arguments, the framer's state `A`, and the verdict so far. -/
structure LineLocals (s : PancakeState σ) (st p nw : Word) (i : Nat) (A : LineState)
    (kind kept : Word) : Prop where
  st : s.locals "blk" = some st
  p : s.locals "p" = some p
  n : s.locals "n" = some nw
  i : s.locals "i" = some (BitVec.ofNat 64 i)
  len : s.locals "len" = some (BitVec.ofNat 64 A.len)
  cr : s.locals "cr" = some (bw A.cr)
  bad : s.locals "bad" = some (bw A.bad)
  kind : s.locals "kind" = some kind
  kept : s.locals "kept" = some kept
  b : ∃ w, s.locals "b" = some w

/-- The bytes `bs` are kept from `st + 40`. -/
def Kept (s : PancakeState σ) (st : Word) (bs : List Byte) : Prop :=
  ∀ j (h : j < bs.length),
    memLoadByte s.memory s.memaddrs s.be (st + 40#64 + BitVec.ofNat 64 j) = some bs[j]

/-- The received bytes are at `p`. -/
def Chunk (s : PancakeState σ) (p : Word) (q : List Byte) : Prop :=
  ∀ j (h : j < q.length), memLoadByte s.memory s.memaddrs s.be (p + BitVec.ofNat 64 j) = some q[j]

theorem widen_eq (y : Byte) (k : Nat) (hk : k < 256) :
    (y.setWidth 64 = BitVec.ofNat 64 k) ↔ y = BitVec.ofNat 8 k := by
  constructor
  · intro h
    apply BitVec.eq_of_toNat_eq
    have := congrArg BitVec.toNat h
    have := y.isLt
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat] at *
    omega
  · rintro rfl
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    omega

/-- A state the program can hold: the kept bytes are the line so far, within the limit, and a
line whose last byte is a CR has one. -/
def Fits (lim : Nat) (A : LineState) : Prop :=
  A.buf.length = A.len ∧ A.len ≤ lim ∧ (A.cr = true → 0 < A.len)

theorem bw_ne_zero (b : Bool) : bw b ≠ 0#64 ↔ b = true := by cases b <;> decide

theorem lf_code : (10#64 : Word) = BitVec.ofNat 64 10 := rfl

/-- The byte that does not end the line: the program's flags and length are the framer's. -/
theorem lineMore_run (o : Oracle σ) (lim : Nat) (hlim : lim < 2 ^ 62) (s : PancakeState σ)
    (st : Word) (A : LineState) (y : Byte) (hA : A.len ≤ lim) (hy : y ≠ LF)
    (hst : s.locals "blk" = some st)
    (hlen : s.locals "len" = some (BitVec.ofNat 64 A.len))
    (hcr : s.locals "cr" = some (bw A.cr))
    (hbad : s.locals "bad" = some (bw A.bad))
    (hb : s.locals "b" = some (y.setWidth 64))
    (hdm : A.len < lim → s.memaddrs (byteAlign (st + 40#64 + BitVec.ofNat 64 A.len)) = true) :
    ∃ s', PancakeSem o (lineMoreP lim) s = (none, s') ∧
      s'.locals "len" = some (BitVec.ofNat 64 (lineStep lim A y).1.len) ∧
      s'.locals "cr" = some (bw (lineStep lim A y).1.cr) ∧
      s'.locals "bad" = some (bw (lineStep lim A y).1.bad) ∧
      (∀ v, v ≠ "len" → v ≠ "cr" → v ≠ "bad" → s'.locals v = s.locals v) ∧
      s'.memory = (if A.len < lim then putByte s.memory s.be (st + 40#64 + BitVec.ofNat 64 A.len) y
        else s.memory) ∧
      s'.memaddrs = s.memaddrs ∧ s'.be = s.be ∧ s'.clock = s.clock ∧ s'.ffi = s.ffi ∧
      s'.baseAddr = s.baseAddr := by
  have hy0 : (y.setWidth 64 = 0#64) ↔ y = NUL := widen_eq y 0 (by decide)
  have hy13 : (y.setWidth 64 = 13#64) ↔ y = CR := widen_eq y 13 (by decide)
  have hlt : signedLt (BitVec.ofNat 64 A.len) (BitVec.ofNat 64 lim) = decide (A.len < lim) :=
    signedLt_ofNat _ _ (by omega) (by omega)
  have hsucc : BitVec.ofNat 64 A.len + 1#64 = BitVec.ofNat 64 (A.len + 1) := (ofNat_succ _).symm
  by_cases hl : A.len < lim
  · have hst8 := memStore_eq s.memory s.memaddrs s.be
      (st + 40#64 + BitVec.ofNat 64 A.len) y (hdm hl)
    by_cases hn : y = NUL
    · subst hn
      cases hc : A.cr <;>
        simp [lineMoreP, PancakeSem, eval, x, c, add, set, hst, hlen, hcr, hbad, hb, hc, bw,
          clampClock, hy0, hy13, hlt, hl, hst8, hsucc, lineStep, hy, setLocal] <;>
              (intro v h1 h2 h3; simp [h1, h2, h3])
    · cases hc : A.cr <;>
        simp [lineMoreP, PancakeSem, eval, x, c, add, set, hst, hlen, hcr, hbad, hb, hc, bw,
          clampClock, hy0, hy13, hlt, hl, hst8, hsucc, lineStep, hy, hn, setLocal] <;>
              (intro v h1 h2 h3; simp [h1, h2, h3])
  · by_cases hn : y = NUL
    · subst hn
      cases hc : A.cr <;>
        simp [lineMoreP, PancakeSem, eval, x, c, add, set, hlen, hcr, hbad, hb, hc, bw,
          clampClock, hy0, hy13, hlt, hl, lineStep, hy, setLocal] <;>
              (intro v _ h2 h3; simp [h2, h3])
    · cases hc : A.cr <;>
        simp [lineMoreP, PancakeSem, eval, x, c, add, set, hlen, hcr, hbad, hb, hc, bw,
          clampClock, hy0, hy13, hlt, hl, lineStep, hy, hn, setLocal] <;>
              (intro v _ h2 h3; simp [h2, h3])

/-- The verdict at the end of a line, from the state before its LF. -/
def lineVerdict (lim : Nat) (A : LineState) : Line :=
  if lim ≤ A.len then ⟨.overlong, A.buf⟩
  else if A.cr ∧ ¬ A.bad then ⟨.command, A.buf.take (A.len - 1)⟩
  else ⟨.malformed, A.buf⟩

theorem lineStep_lf (lim : Nat) (A : LineState) :
    lineStep lim A LF = (.fresh, some (lineVerdict lim A)) := by
  simp [lineStep, lineVerdict]

/-- The line end: the program's verdict and the number of bytes it keeps are the framer's, and the
state starts afresh. -/
theorem lineEnd_run (o : Oracle σ) (lim : Nat) (hlim : lim < 2 ^ 62) (s : PancakeState σ)
    (A : LineState) (hA : Fits lim A)
    (hlen : s.locals "len" = some (BitVec.ofNat 64 A.len))
    (hcr : s.locals "cr" = some (bw A.cr))
    (hbad : s.locals "bad" = some (bw A.bad))
    (hkind : ∃ w, s.locals "kind" = some w) (hkept : ∃ w, s.locals "kept" = some w) :
    ∃ s', PancakeSem o (lineEndP lim) s = (none, s') ∧
      s'.locals "kind" = some (BitVec.ofNat 64 (kindCode (lineVerdict lim A).kind)) ∧
      s'.locals "kept" = some (BitVec.ofNat 64 (lineVerdict lim A).kept.length) ∧
      s'.locals "len" = some (BitVec.ofNat 64 LineState.fresh.len) ∧
      s'.locals "cr" = some (bw LineState.fresh.cr) ∧
      s'.locals "bad" = some (bw LineState.fresh.bad) ∧
      (∀ v, v ≠ "kind" → v ≠ "kept" → v ≠ "len" → v ≠ "cr" → v ≠ "bad" →
        s'.locals v = s.locals v) ∧
      s'.memory = s.memory ∧ s'.memaddrs = s.memaddrs ∧ s'.be = s.be ∧ s'.clock = s.clock ∧
      s'.ffi = s.ffi ∧ s'.baseAddr = s.baseAddr := by
  obtain ⟨hbuf, hle, hpos⟩ := hA
  obtain ⟨wk, hwk⟩ := hkind
  obtain ⟨wp, hwp⟩ := hkept
  have hlt : signedLt (BitVec.ofNat 64 A.len) (BitVec.ofNat 64 lim) = decide (A.len < lim) :=
    signedLt_ofNat _ _ (by omega) (by omega)
  by_cases hl : lim ≤ A.len
  · have hl' : ¬ A.len < lim := by omega
    simp [lineEndP, PancakeSem, eval, x, c, set, hlen, hcr, hbad, hwk, hwp, clampClock, hlt, hl',
      lineVerdict, hl, hbuf, kindCode, bw, LineState.fresh, setLocal]
    intro v h1 h2 h3 h4 h5; simp [h1, h2, h3, h4, h5]
  · have hl' : A.len < lim := by omega
    by_cases hcmd : A.cr = true ∧ A.bad = false
    · obtain ⟨hc, hb⟩ := hcmd
      have hsub : BitVec.ofNat 64 A.len - 1#64 = BitVec.ofNat 64 (A.len - 1) := by
        have := hpos hc
        rw [show A.len = (A.len - 1) + 1 by omega, ofNat_succ, BitVec.add_sub_cancel]
        simp
      simp [lineEndP, PancakeSem, eval, x, c, set, hlen, hcr, hbad, hwk, hwp, clampClock, hlt, hl',
        lineVerdict, hl, hbuf, kindCode, bw, LineState.fresh, setLocal, hc, hb, hsub]
      intro v h1 h2 h3 h4 h5; simp [h1, h2, h3, h4, h5]
    · have hand : ((if A.cr = true then 1#64 else 0#64) &&&
          (if A.bad = false then 1#64 else 0#64) : Word) = 0#64 := by
        cases hc : A.cr <;> cases hb : A.bad <;> simp_all
      simp [lineEndP, PancakeSem, eval, x, c, set, hlen, hcr, hbad, hwk, hwp, clampClock, hlt, hl',
        lineVerdict, hl, hbuf, kindCode, LineState.fresh, setLocal, hand, hcmd, bw]
      intro v h1 h2 h3 h4 h5; simp [h1, h2, h3, h4, h5]

/-- A statement after one that ends normally without spending clock. -/
theorem seq_run (o : Oracle σ) {c1 c2 : PancakeProg} {s s1 s' : PancakeState σ}
    (h1 : PancakeSem o c1 s = (none, s1)) (hclk : s1.clock = s.clock)
    (h2 : PancakeSem o c2 s1 = (none, s')) : PancakeSem o (.seq c1 c2) s = (none, s') := by
  rw [sem_seq_none h1, show min s.clock s1.clock = s1.clock by omega]; exact h2

/-- What a line's verdict leaves in the locals. -/
def kindW : Option Line → Word
  | none => 0#64
  | some l => BitVec.ofNat 64 (kindCode l.kind)

def keptW (w : Word) : Option Line → Word
  | none => w
  | some l => BitVec.ofNat 64 l.kept.length

/-- The names the loop writes. -/
def lineNames : List String := ["b", "i", "len", "cr", "bad", "kind", "kept"]

theorem fits_step (lim : Nat) (hpos : 0 < lim) (A : LineState) (y : Byte) (hA : Fits lim A) :
    Fits lim (lineStep lim A y).1 := by
  obtain ⟨hb, hl, hc⟩ := hA
  by_cases hy : y = LF
  · simp [lineStep, hy, Fits, LineState.fresh]
  · simp only [lineStep, hy, if_false, Fits]
    by_cases h : A.len < lim
    · simp only [h, if_true, List.length_append, List.length_singleton]
      exact ⟨by omega, by omega, fun _ => by omega⟩
    · simp only [h, if_false]
      exact ⟨hb, hl, fun _ => by omega⟩

/-- **One byte of the loop is one step of the framer.** -/
theorem lineBody_run (o : Oracle σ) (lim : Nat) (hlim : lim < 2 ^ 62)
    (s : PancakeState σ) (st p nw : Word) (q : List Byte) (i : Nat) (A : LineState) (kept : Word)
    (hA : Fits lim A) (hi : i < q.length)
    (hL : LineLocals s st p nw i A 0#64 kept) (hK : Kept s st A.buf) (hC : Chunk s p q)
    (hdom : ∀ j, j < lim → s.memaddrs (byteAlign (st + 40#64 + BitVec.ofNat 64 j)) = true)
    (hsep : ∀ j j', j < lim → j' < q.length →
      st + 40#64 + BitVec.ofNat 64 j ≠ p + BitVec.ofNat 64 j') :
    ∃ s2, PancakeSem o (lineBodyP lim) (decClock s) = (none, s2) ∧ s2.clock = s.clock - 1 ∧
      LineLocals s2 st p nw (i + 1) (lineStep lim A q[i]).1 (kindW (lineStep lim A q[i]).2)
        (keptW kept (lineStep lim A q[i]).2) ∧
      Kept s2 st (if (lineStep lim A q[i]).2.isSome then A.buf else (lineStep lim A q[i]).1.buf) ∧
      Chunk s2 p q ∧ s2.memaddrs = s.memaddrs ∧ s2.be = s.be ∧ s2.ffi = s.ffi ∧
      s2.baseAddr = s.baseAddr ∧
      (∀ a, (∀ j, j < lim → a ≠ st + 40#64 + BitVec.ofNat 64 j) →
        memLoadByte s2.memory s.memaddrs s.be a = memLoadByte s.memory s.memaddrs s.be a) ∧
      (∀ w, (∀ j, j < lim → byteAlign (st + 40#64 + BitVec.ofNat 64 j) ≠ w) →
        s2.memory w = s.memory w) ∧
      (∀ v, v ∉ lineNames → s2.locals v = s.locals v) := by
  obtain ⟨hst, hp, hn, hiL, hlen, hcr, hbad, hkind, hkept, ⟨wb, hwb⟩⟩ := hL
  obtain ⟨y, hydef⟩ : ∃ y, q[i] = y := ⟨_, rfl⟩
  rw [hydef]
  have hload : memLoadByte s.memory s.memaddrs s.be (p + BitVec.ofNat 64 i) = some y := by
    rw [← hydef]; exact hC i hi
  -- the byte and the position
  let s1 : PancakeState σ := { decClock s with locals := setLocal s.locals "b" (y.setWidth 64) }
  let s2 : PancakeState σ :=
    { s1 with locals := setLocal s1.locals "i" (BitVec.ofNat 64 (i + 1)) }
  have hrun1 : PancakeSem o (.assign "b" (.loadByte (add (x "p") (x "i")))) (decClock s) =
      (none, s1) := by
    apply sem_assign (old := wb)
    · simp [eval, x, add, decClock, hp, hiL, hload]
    · exact hwb
  have hrun2 : PancakeSem o (.assign "i" (add (x "i") (c 1))) s1 = (none, s2) := by
    apply sem_assign (old := BitVec.ofNat 64 i)
    · rw [ofNat_succ]; simp [eval, x, c, add, s1, setLocal, hiL, decClock]
    · simp [s1, setLocal, hiL]
  have l2 : ∀ v, v ≠ "i" → v ≠ "b" → s2.locals v = s.locals v := by
    intro v h1 h2; simp [s2, s1, setLocal, h1, h2]
  have hcond : eval s2 (.cmp .equal (x "b") (c 10)) =
      some (if y = LF then 1#64 else 0#64) := by
    have := widen_eq y 10 (by decide)
    simp [eval, x, c, s2, s1, setLocal, decClock, this, LF]
  have hclk2 : s2.clock = s.clock - 1 := rfl
  have hframeL : ∀ v, v ∉ lineNames → v ≠ "i" ∧ v ≠ "b" ∧ v ≠ "len" ∧ v ≠ "cr" ∧ v ≠ "bad" ∧
      v ≠ "kind" ∧ v ≠ "kept" := by
    intro v hv; simp only [lineNames, List.mem_cons, List.not_mem_nil, or_false, not_or] at hv
    exact ⟨hv.2.1, hv.1, hv.2.2.1, hv.2.2.2.1, hv.2.2.2.2.1, hv.2.2.2.2.2.1, hv.2.2.2.2.2.2⟩
  by_cases hy : y = LF
  · -- the line ends
    obtain ⟨s3, hrun3, hk3, hkp3, hl3, hc3, hb3, hfr3, hm3, hma3, hbe3, hclk3, hffi3, hba3⟩ :=
      lineEnd_run o lim hlim s2 A hA (by rw [l2 _ (by decide) (by decide)]; exact hlen)
        (by rw [l2 _ (by decide) (by decide)]; exact hcr)
        (by rw [l2 _ (by decide) (by decide)]; exact hbad)
        ⟨_, by rw [l2 _ (by decide) (by decide)]; exact hkind⟩
        ⟨_, by rw [l2 _ (by decide) (by decide)]; exact hkept⟩
    have hstep : lineStep lim A y = (.fresh, some (lineVerdict lim A)) := by
      rw [hy]; exact lineStep_lf lim A
    refine ⟨s3, ?_, by rw [hclk3]; rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · apply seq_run o hrun1 rfl
      apply seq_run o hrun2 rfl
      rw [sem_cond o hcond]; simp only [hy, if_true, ne_eq]; exact hrun3
    · rw [hstep]
      refine ⟨?_, ?_, ?_, ?_, hl3, hc3, hb3, hk3, hkp3, ⟨y.setWidth 64, ?_⟩⟩
      · rw [hfr3 _ (by decide) (by decide) (by decide) (by decide) (by decide),
          l2 _ (by decide) (by decide)]; exact hst
      · rw [hfr3 _ (by decide) (by decide) (by decide) (by decide) (by decide),
          l2 _ (by decide) (by decide)]; exact hp
      · rw [hfr3 _ (by decide) (by decide) (by decide) (by decide) (by decide),
          l2 _ (by decide) (by decide)]; exact hn
      · rw [hfr3 _ (by decide) (by decide) (by decide) (by decide) (by decide)]
        simp [s2, setLocal]
      · rw [hfr3 _ (by decide) (by decide) (by decide) (by decide) (by decide)]
        simp [s2, s1, setLocal]
    · rw [hstep]; simp only [Option.isSome_some, if_true]
      intro j hj; rw [hm3, hma3, hbe3]; exact hK j hj
    · intro j hj; rw [hm3, hma3, hbe3]; exact hC j hj
    · rw [hma3]; rfl
    · rw [hbe3]; rfl
    · rw [hffi3]; rfl
    · rw [hba3]; rfl
    · intro a _; rw [hm3]; rfl
    · intro w _; rw [hm3]; rfl
    · intro v hv
      obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hframeL v hv
      rw [hfr3 v h6 h7 h3 h4 h5, l2 v h1 h2]
  · -- a byte of the line
    have hdm : A.len < lim → s2.memaddrs (byteAlign (st + 40#64 + BitVec.ofNat 64 A.len)) = true :=
      fun h => hdom _ h
    obtain ⟨s3, hrun3, hl3, hc3, hb3, hfr3, hm3, hma3, hbe3, hclk3, hffi3, hba3⟩ :=
      lineMore_run o lim hlim s2 st A y hA.2.1 hy
        (by rw [l2 _ (by decide) (by decide)]; exact hst)
        (by rw [l2 _ (by decide) (by decide)]; exact hlen)
        (by rw [l2 _ (by decide) (by decide)]; exact hcr)
        (by rw [l2 _ (by decide) (by decide)]; exact hbad)
        (by simp [s2, s1, setLocal]) hdm
    have hstep2 : (lineStep lim A y).2 = none := by simp [lineStep, hy]
    have hm3' : s3.memory = if A.len < lim then putByte s.memory s.be
        (st + 40#64 + BitVec.ofNat 64 A.len) y
        else s.memory := hm3
    -- a byte of the kept region, of the chunk, or elsewhere, after the store
    have hother : ∀ a, a ≠ st + 40#64 + BitVec.ofNat 64 A.len →
        memLoadByte s3.memory s.memaddrs s.be a = memLoadByte s.memory s.memaddrs s.be a := by
      intro a ha; rw [hm3']; split
      · exact load_putByte_diff _ _ _ _ _ _ ha
      · rfl
    refine ⟨s3, ?_, by rw [hclk3]; rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · apply seq_run o hrun1 rfl
      apply seq_run o hrun2 rfl
      rw [sem_cond o hcond]; simp only [hy, if_false, ne_eq]; exact hrun3
    · rw [hstep2]
      refine ⟨?_, ?_, ?_, ?_, hl3, hc3, hb3, ?_, ?_, ⟨y.setWidth 64, ?_⟩⟩
      · rw [hfr3 _ (by decide) (by decide) (by decide), l2 _ (by decide) (by decide)]; exact hst
      · rw [hfr3 _ (by decide) (by decide) (by decide), l2 _ (by decide) (by decide)]; exact hp
      · rw [hfr3 _ (by decide) (by decide) (by decide), l2 _ (by decide) (by decide)]; exact hn
      · rw [hfr3 _ (by decide) (by decide) (by decide)]; simp [s2, setLocal]
      · rw [hfr3 _ (by decide) (by decide) (by decide), l2 _ (by decide) (by decide)]
        simpa [kindW] using hkind
      · rw [hfr3 _ (by decide) (by decide) (by decide), l2 _ (by decide) (by decide)]
        simpa [keptW] using hkept
      · rw [hfr3 _ (by decide) (by decide) (by decide)]; simp [s2, s1, setLocal]
    · rw [hstep2]; simp only [Option.isSome_none, Bool.false_eq_true, if_false]
      intro j hj
      rw [hma3, hbe3]
      show memLoadByte s3.memory s.memaddrs s.be _ = _
      simp only [lineStep, hy, if_false] at hj ⊢
      by_cases hl : A.len < lim
      · simp only [hl, if_true] at hj ⊢
        have hbl := hA.1
        by_cases hjl : j < A.len
        · rw [hother _ (region_addr_inj (st + 40#64) j A.len (by omega) (by omega) (by omega))]
          rw [List.getElem_append_left (by omega)]; exact hK j (by omega)
        · have hjeq : j = A.len := by simp at hj; omega
          subst hjeq
          rw [hm3']; simp only [hl, if_true]
          rw [List.getElem_append_right (by omega)]
          simp only [hbl, Nat.sub_self, List.getElem_singleton]
          exact load_putByte_same _ _ _ _ _ (hdom _ hl)
      · simp only [hl, if_false] at hj ⊢
        rw [hm3']; simp only [hl, if_false]; exact hK j hj
    · intro j hj
      rw [hma3, hbe3]
      show memLoadByte s3.memory s.memaddrs s.be _ = _
      by_cases hl : A.len < lim
      · rw [hother _ (Ne.symm (hsep A.len j hl hj))]; exact hC j hj
      · rw [hm3', if_neg hl]; exact hC j hj
    · rw [hma3]; rfl
    · rw [hbe3]; rfl
    · rw [hffi3]; rfl
    · rw [hba3]; rfl
    · intro a ha
      by_cases hl : A.len < lim
      · exact hother a (ha _ hl)
      · rw [hm3']; simp [hl]
    · intro w hw
      rw [hm3']; split
      · rename_i hl; simp only [putByte]; rw [if_neg (Ne.symm (hw _ hl))]
      · rfl
    · intro v hv
      obtain ⟨h1, h2, h3, h4, h5, _, _⟩ := hframeL v hv
      rw [hfr3 v h3 h4 h5, l2 v h1 h2]

/-! ## The loop -/

/-- The bytes kept after reading: the line's, once one ended, or the line so far. -/
def keptOf (f : LineState × List Line) : List Byte :=
  match f.2 with
  | l :: _ => l.kept
  | [] => f.1.buf

/-- Bytes kept at `st + 40` stay kept when fewer of them are asked for. -/
theorem kept_prefix {s : PancakeState σ} {st : Word} {bs bs' : List Byte} (h : Kept s st bs)
    (hp : bs' <+: bs) : Kept s st bs' := by
  intro j hj
  rw [h j (by have := hp.length_le; omega)]
  obtain ⟨t, rfl⟩ := hp
  simp [List.getElem_append_left hj]

theorem verdict_prefix (lim : Nat) (A : LineState) : (lineVerdict lim A).kept <+: A.buf := by
  unfold lineVerdict
  split
  · exact List.prefix_refl _
  · split
    · exact List.take_prefix _ _
    · exact List.prefix_refl _

/-- After `k` bytes: the locals and the kept bytes are the framer's after the first `k` bytes from
`i0`, and nothing else the loop could reach has changed since `s0`. -/
structure LoopInv (lim : Nat) (s0 s : PancakeState σ) (st p : Word) (q : List Byte) (i0 : Nat)
    (A : LineState) (kept0 : Word) (k : Nat) : Prop where
  loc : LineLocals s st p (BitVec.ofNat 64 q.length) (i0 + k)
    (feed lim A ((q.drop i0).take k)).1 (kindW (feed lim A ((q.drop i0).take k)).2.head?)
    (keptW kept0 (feed lim A ((q.drop i0).take k)).2.head?)
  kept : Kept s st (keptOf (feed lim A ((q.drop i0).take k)))
  chunk : Chunk s p q
  ma : s.memaddrs = s0.memaddrs
  be : s.be = s0.be
  ffi : s.ffi = s0.ffi
  base : s.baseAddr = s0.baseAddr
  bytes : ∀ a, (∀ j, j < lim → a ≠ st + 40#64 + BitVec.ofNat 64 j) →
    memLoadByte s.memory s0.memaddrs s0.be a = memLoadByte s0.memory s0.memaddrs s0.be a
  words : ∀ w, (∀ j, j < lim → byteAlign (st + 40#64 + BitVec.ofNat 64 j) ≠ w) →
    s.memory w = s0.memory w
  names : ∀ v, v ∉ lineNames → s.locals v = s0.locals v
  fits : Fits lim (feed lim A ((q.drop i0).take k)).1

theorem feed_take_succ (lim : Nat) (A : LineState) (q : List Byte) (k : Nat) (hk : k < q.length) :
    feed lim A (q.take (k + 1)) =
      let f := feed lim A (q.take k)
      let r := lineStep lim f.1 q[k]
      (r.1, f.2 ++ r.2.toList) := by
  rw [List.take_add_one, List.getElem?_eq_getElem hk, Option.toList_some, feed_append]
  simp [feed]

/-- **The loop is the framer's call**: it reads up to the end of the first line or of the chunk,
and leaves the framer's state and verdict. -/
theorem lineLoop_run (o : Oracle σ) (lim : Nat) (hlim : lim < 2 ^ 62) (hpos : 0 < lim)
    (s0 : PancakeState σ) (st p : Word) (q : List Byte) (i0 : Nat) (A : LineState) (kept0 : Word)
    (hA : Fits lim A) (hi0 : i0 ≤ q.length) (hq : q.length < 2 ^ 62)
    (hL : LineLocals s0 st p (BitVec.ofNat 64 q.length) i0 A 0#64 kept0) (hK : Kept s0 st A.buf)
    (hC : Chunk s0 p q)
    (hdom : ∀ j, j < lim → s0.memaddrs (byteAlign (st + 40#64 + BitVec.ofNat 64 j)) = true)
    (hsep : ∀ j j', j < lim → j' < q.length →
      st + 40#64 + BitVec.ofNat 64 j ≠ p + BitVec.ofNat 64 j')
    :
    ((frameOnce lim A (q.drop i0)).1 ≤ s0.clock →
      ∃ s', PancakeSem o (.while_ lineGuardP (lineBodyP lim)) s0 = (none, s') ∧
        s'.clock + (frameOnce lim A (q.drop i0)).1 = s0.clock ∧
        LoopInv lim s0 s' st p q i0 A kept0 (frameOnce lim A (q.drop i0)).1) ∧
    (s0.clock < (frameOnce lim A (q.drop i0)).1 →
      ∃ t, PancakeSem o (.while_ lineGuardP (lineBodyP lim)) s0 = (some .timeout, t)) := by
  let K := (frameOnce lim A (q.drop i0)).1
  have hKle : K ≤ q.length - i0 := by
    have := (frameOnce_len lim A (q.drop i0)).1; simpa using this
  have hlt : ∀ a b : Nat, a < 2 ^ 62 → b < 2 ^ 62 →
      signedLt (BitVec.ofNat 64 a) (BitVec.ofNat 64 b) = decide (a < b) :=
    fun a b ha hb => signedLt_ofNat a b (by omega) (by omega)
  let I : Nat → PancakeState σ → Prop := fun rem s =>
    rem ≤ K ∧ LoopInv lim s0 s st p q i0 A kept0 (K - rem)
  have hg : ∀ rem s, I rem s → eval s lineGuardP = some (if rem = 0 then (0 : Word) else 1) := by
        intro rem s ⟨hrem, hI⟩
        have hloc := hI.loc
        by_cases h0 : rem = 0
        · subst h0
          have hfeed := frameOnce_feed lim A (q.drop i0)
          simp only [Nat.sub_zero] at hloc ⊢
          rw [show K = (frameOnce lim A (q.drop i0)).1 from rfl] at hloc
          rw [hfeed] at hloc
          rcases hout : (frameOnce lim A (q.drop i0)).2.2 with _ | l
          · have hend : K = q.length - i0 := by
              by_cases hs : K < (q.drop i0).length
              · have := frameOnce_short lim A (q.drop i0) hs; rw [hout] at this; simp at this
              · simp at hs; omega
            rw [hout] at hloc
            have hg : signedLt (BitVec.ofNat 64 (i0 + K)) (BitVec.ofNat 64 q.length) = false := by
              rw [hlt _ _ (by omega) hq]; simp; omega
            simp [lineGuardP, eval, x, c, hloc.i, hloc.n, hloc.kind, kindW]
            simp only [K] at hg; simp [hg]
          · rw [hout] at hloc
            have hcode : (BitVec.ofNat 64 (kindCode l.kind) : Word) ≠ 0#64 := by
              cases l.kind <;> decide
            simp [lineGuardP, eval, x, c, hloc.i, hloc.n, hloc.kind, kindW, hcode]
        · have hk : K - rem < K := by omega
          have hquiet := frameOnce_quiet lim A (q.drop i0) (K - rem) hk
          rw [hquiet] at hloc
          have hg : signedLt (BitVec.ofNat 64 (i0 + (K - rem)))
              (BitVec.ofNat 64 q.length) = true := by
            rw [hlt _ _ (by omega) hq]; simp; omega
          simp [lineGuardP, eval, x, c, hloc.i, hloc.n, hloc.kind, kindW, h0, hg]
  have hb : ∀ rem s, I (rem + 1) s →
      ∃ s2, PancakeSem o (lineBodyP lim) (decClock s) = (none, s2) ∧ I rem s2 ∧
        s2.clock = s.clock - 1 := by
        intro rem s ⟨hrem, hI⟩
        have hk : K - (rem + 1) < K := by omega
        obtain ⟨k, hkdef⟩ : ∃ k, k = K - (rem + 1) := ⟨_, rfl⟩
        rw [← hkdef] at hk hI
        have hquiet := frameOnce_quiet lim A (q.drop i0) k hk
        have hloc := hI.loc
        rw [hquiet] at hloc
        have hkq : i0 + k < q.length := by omega
        have hkq' : k < (q.drop i0).length := by simp; omega
        have hkept := hI.kept
        simp only [keptOf, hquiet] at hkept
        obtain ⟨s2, hrun2, hclk2, hL2, hK2, hC2, hma2, hbe2, hffi2, hba2, hby2, hw2, hn2⟩ :=
          lineBody_run o lim hlim s st p (BitVec.ofNat 64 q.length) q (i0 + k)
            (feed lim A ((q.drop i0).take k)).1 kept0 hI.fits hkq
                (by simpa [kindW, keptW] using hloc)
            hkept hI.chunk (fun j hj => by rw [hI.ma]; exact hdom j hj) hsep
        have hy : q[i0 + k] = (q.drop i0)[k] := by simp
        have hfeed := feed_take_succ lim A (q.drop i0) k hkq'
        refine ⟨s2, hrun2, ⟨by omega, ?_⟩, hclk2⟩
        have hk1 : K - rem = k + 1 := by omega
        rw [hk1]
        refine ⟨?_, ?_, hC2, by rw [hma2, hI.ma], by rw [hbe2, hI.be], by rw [hffi2, hI.ffi],
          by rw [hba2, hI.base], ?_, ?_, ?_, ?_⟩
        · rw [hfeed]; simp only [hquiet, List.nil_append]
          rw [← hy, show i0 + (k + 1) = i0 + k + 1 by omega]
          cases h : (lineStep lim (feed lim A (List.take k (List.drop i0 q))).1 q[i0 + k]).2 <;>
            simp_all [kindW, keptW]
        · rw [hfeed]; simp only [hquiet, List.nil_append]
          rw [← hy]
          rcases h : (lineStep lim (feed lim A (List.take k (List.drop i0 q))).1
              q[i0 + k]) with ⟨A', _ | l⟩
          · rw [h] at hK2; simpa [keptOf] using hK2
          · rw [h] at hK2
            simp only [Option.isSome_some, if_true] at hK2
            simp only [keptOf, Option.toList_some]
            have hl : l = lineVerdict lim (feed lim A (List.take k (List.drop i0 q))).1 := by
              by_cases hy' : q[i0 + k] = LF
              · rw [hy', lineStep_lf] at h; simp at h; exact h.2.symm
              · simp [lineStep, hy'] at h
            rw [hl]; exact kept_prefix hK2 (verdict_prefix _ _)
        · intro a ha
          rw [← hI.ma, ← hI.be, hby2 a ha, hI.ma, hI.be]; exact hI.bytes a ha
        · intro w hw; rw [hw2 w hw]; exact hI.words w hw
        · intro v hv; rw [hn2 v hv]; exact hI.names v hv
        · rw [hfeed, ← hy]; exact fits_step lim hpos _ _ hI.fits
  have hI0 : I K s0 :=
      ⟨Nat.le_refl _, by
        rw [Nat.sub_self]
        exact ⟨by simpa [feed, kindW, keptW] using hL, by simpa [feed, keptOf] using hK, hC,
            rfl, rfl,
          rfl, rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl, by simpa [feed] using hA⟩⟩
  refine ⟨fun hk => ?_,
      fun hk => while_inv_timeout o lineGuardP (lineBodyP lim) I hg hb K s0 hI0 hk⟩
  obtain ⟨s', hrun, ⟨_, hinv⟩, hclk'⟩ :=
    while_inv_cond_exact o lineGuardP (lineBodyP lim) I hg hb K s0 hI0 hk
  exact ⟨s', hrun, hclk', by simpa using hinv⟩

/-! ## The whole run -/

/-- The stores, then whatever follows. -/
def lineStoresP (k : PancakeProg) : PancakeProg :=
  .seq (.store (x "blk") (x "len"))
  (.seq (.store (add (x "blk") (c 8)) (x "cr"))
  (.seq (.store (add (x "blk") (c 16)) (x "bad"))
  (.seq (.store (add (x "blk") (c 24)) (x "kind"))
  (.seq (.store (add (x "blk") (c 32)) (x "kept")) k))))

/-- The framer, then whatever follows it: `k`. -/
def lineFragP (lim : Nat) (k : PancakeProg) : PancakeProg :=
  .seq (.assign "len" (.loadWord (x "blk")))
  (.seq (.assign "cr" (.loadWord (add (x "blk") (c 8))))
  (.seq (.assign "bad" (.loadWord (add (x "blk") (c 16))))
  (.seq (set "kind" 0)
  (.seq (set "kept" 0)
  (.seq (.while_ lineGuardP (lineBodyP lim)) (lineStoresP k))))))

def lineRunP (lim : Nat) : PancakeProg :=
  .dec "len" (c 0) (.dec "cr" (c 0) (.dec "bad" (c 0) (.dec "kind" (c 0) (.dec "kept" (c 0)
    (.dec "b" (c 0) (lineFragP lim (.ret (x "i"))))))))

theorem lineRun_lower (lim : Nat) : Lower.lowerStmtsFold (lineRun lim) = some (lineRunP lim) := rfl

/-- The framer followed by other statements lowers to the framer followed by their lowering, as
a program that calls it from its own loop will have it. -/
theorem lineFrag_lower (lim : Nat) (x0 : PStmt) (rest : List PStmt) (r : PancakeProg)
    (h : Lower.lowerStmtsFold (x0 :: rest) = some r) :
    Lower.lowerStmtsFold (lineFrag lim ++ x0 :: rest) = some (lineFragP lim r) := by
  simp only [lineFrag, lineLoop, List.cons_append, List.nil_append, Lower.lowerStmtsFold,
    Lower.lowerStmt1, Lower.lowerExp, h, v, n, eAdd]
  rfl

/-- The framer's state is in memory at `st`. -/
def Holds (s : PancakeState σ) (st : Word) (A : LineState) : Prop :=
  s.memory st = BitVec.ofNat 64 A.len ∧ s.memory (st + 8#64) = bw A.cr ∧
    s.memory (st + 16#64) = bw A.bad ∧ Kept s st A.buf

/-- A block whose first words are zero holds a fresh line framer: zeroing them starts one. -/
theorem holds_zero (s : PancakeState σ) (st : Word) (h0 : s.memory st = 0#64)
    (h8 : s.memory (st + 8#64) = 0#64) (h16 : s.memory (st + 16#64) = 0#64) :
    Holds s st .fresh :=
  ⟨h0, h8, h16, fun j h => absurd h (by simp [LineState.fresh])⟩

/-- The verdict is in memory at `st + 24`: none, or the line's kind, how many bytes it keeps, and
those bytes from `st + 40`. -/
def Reported (s : PancakeState σ) (st : Word) : Option Line → Prop
  | none => s.memory (st + 24#64) = 0#64
  | some l => s.memory (st + 24#64) = BitVec.ofNat 64 (kindCode l.kind) ∧
      s.memory (st + 32#64) = BitVec.ofNat 64 l.kept.length ∧ Kept s st l.kept

/-- The words of the block at `st` are memory, and so is the word of each byte it keeps. -/
def Room (lim : Nat) (s : PancakeState σ) (st : Word) : Prop :=
  s.memaddrs st = true ∧ s.memaddrs (st + 8#64) = true ∧ s.memaddrs (st + 16#64) = true ∧
    s.memaddrs (st + 24#64) = true ∧ s.memaddrs (st + 32#64) = true ∧
    ∀ j, j < lim → s.memaddrs (byteAlign (st + 40#64 + BitVec.ofNat 64 j)) = true

/-- A byte outside the block at `st`. -/
def Outside (lim : Nat) (st a : Word) : Prop :=
  byteAlign a ≠ st ∧ byteAlign a ≠ st + 8#64 ∧ byteAlign a ≠ st + 16#64 ∧
    byteAlign a ≠ st + 24#64 ∧ byteAlign a ≠ st + 32#64 ∧
    ∀ j, j < lim → a ≠ st + 40#64 + BitVec.ofNat 64 j

theorem memStoreWord_some (m : Word → Word) (dm : Word → Bool) (a w : Word) (h : dm a = true) :
    memStoreWord m dm a w = some (fun k => if k = a then w else m k) := by
  simp [memStoreWord, h]

theorem load_after_word (m : Word → Word) (dm : Word → Bool) (be : Bool) (a w x : Word)
    (h : byteAlign x ≠ a) :
    memLoadByte (fun k => if k = a then w else m k) dm be x = memLoadByte m dm be x := by
  simp [memLoadByte, h]

/-- The kept bytes are not in the five words of the block. -/
theorem kept_word_ne (lim : Nat) (st : Word) (hal : st.toNat % 8 = 0)
    (hfit : st.toNat + 40 + lim ≤ 2 ^ 64) (j : Nat) (hj : j < lim) (k : Nat) (hk : k < 5) :
    byteAlign (st + 40#64 + BitVec.ofNat 64 j) ≠ st + BitVec.ofNat 64 (8 * k) := by
  intro h
  have := congrArg BitVec.toNat h
  rw [byteAlign_toNat] at this
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat] at this
  omega

/-- After a line, the framer starts afresh. -/
theorem frameOnce_fresh (lim : Nat) :
    ∀ (A : LineState) (q : List Byte) (l : Line), (frameOnce lim A q).2.2 = some l →
      (frameOnce lim A q).2.1 = .fresh := by
  intro A q
  induction q generalizing A with
  | nil => intro l h; simp [frameOnce] at h
  | cons y rest ih =>
    intro l h
    rcases hstep : lineStep lim A y with ⟨A', _ | l'⟩
    · simp only [frameOnce, hstep] at h ⊢; exact ih A' l h
    · simp only [frameOnce, hstep]
      by_cases hy : y = LF
      · rw [hy, lineStep_lf] at hstep; simp at hstep; exact hstep.1.symm
      · simp [lineStep, hy] at hstep

/-- A line keeps no more than the limit. -/
theorem frameOnce_kept_le (lim : Nat) (hpos : 0 < lim) :
    ∀ (A : LineState) (q : List Byte) (l : Line), Fits lim A → (frameOnce lim A q).2.2 = some l →
      l.kept.length ≤ lim := by
  intro A q
  induction q generalizing A with
  | nil => intro l _ h; simp [frameOnce] at h
  | cons y rest ih =>
    intro l hA h
    rcases hstep : lineStep lim A y with ⟨A', _ | l'⟩
    · simp only [frameOnce, hstep] at h
      exact ih A' l (by have := fits_step lim hpos A y hA; rw [hstep] at this; exact this) h
    · simp only [frameOnce, hstep, Option.some.injEq] at h
      subst h
      by_cases hy : y = LF
      · rw [hy, lineStep_lf] at hstep
        simp only [Prod.mk.injEq, Option.some.injEq] at hstep
        rw [← hstep.2]
        have := (verdict_prefix lim A).length_le
        have := hA.1
        have := hA.2.1
        omega
      · simp [lineStep, hy] at hstep

/-- The memory after the stores. -/
def written (m : Word → Word) (st len cr bad kind kept : Word) : Word → Word :=
  fun k => if k = st + 32#64 then kept else if k = st + 24#64 then kind
    else if k = st + 16#64 then bad else if k = st + 8#64 then cr else if k = st then len else m k

theorem lineStores_run (o : Oracle σ) (k : PancakeProg) (s : PancakeState σ)
    (st len cr bad kind kept : Word)
    (hst : s.locals "blk" = some st) (hlen : s.locals "len" = some len)
    (hcr : s.locals "cr" = some cr) (hbad : s.locals "bad" = some bad)
    (hkind : s.locals "kind" = some kind) (hkept : s.locals "kept" = some kept)
    (h0 : s.memaddrs st = true) (h8 : s.memaddrs (st + 8#64) = true)
    (h16 : s.memaddrs (st + 16#64) = true) (h24 : s.memaddrs (st + 24#64) = true)
    (h32 : s.memaddrs (st + 32#64) = true) :
    PancakeSem o (lineStoresP k) s =
      PancakeSem o k { s with memory := written s.memory st len cr bad kind kept } := by
  simp only [lineStoresP, PancakeSem, eval, x, c, add, hst, hlen, hcr, hbad, hkind, hkept,
    memStoreWord, h0, h8, h16, h24, h32, if_true, clampClock, Nat.min_self]
  rfl

/-- The five words of the block are distinct. -/
theorem words_ne (st : Word) :
    st + 32#64 ≠ st + 24#64 ∧ st + 32#64 ≠ st + 16#64 ∧ st + 32#64 ≠ st + 8#64 ∧ st + 32#64 ≠ st ∧
    st + 24#64 ≠ st + 16#64 ∧ st + 24#64 ≠ st + 8#64 ∧ st + 24#64 ≠ st ∧ st + 16#64 ≠ st + 8#64 ∧
    st + 16#64 ≠ st ∧ st + 8#64 ≠ st := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> bv_omega

/-- Writing the five words leaves every byte outside them as it was. -/
theorem written_outside (lim : Nat) (st : Word) (m : Word → Word) (dm : Word → Bool) (be : Bool)
    (w0 w8 w16 w24 w32 a : Word) (h : Outside lim st a) :
    memLoadByte (written m st w0 w8 w16 w24 w32) dm be a = memLoadByte m dm be a := by
  obtain ⟨a0, a8, a16, a24, a32, _⟩ := h
  simp [written, memLoadByte, a0, a8, a16, a24, a32]

/-- …and every byte kept after them. -/
theorem written_kept (lim : Nat) (st : Word) (hal : st.toNat % 8 = 0)
    (hfit : st.toNat + 40 + lim ≤ 2 ^ 64) (m : Word → Word) (dm : Word → Bool) (be : Bool)
    (w0 w8 w16 w24 w32 : Word) (j : Nat) (hj : j < lim) :
    memLoadByte (written m st w0 w8 w16 w24 w32) dm be (st + 40#64 + BitVec.ofNat 64 j) =
      memLoadByte m dm be (st + 40#64 + BitVec.ofNat 64 j) := by
  have k0 := kept_word_ne lim st hal hfit j hj 0 (by decide)
  have k1 := kept_word_ne lim st hal hfit j hj 1 (by decide)
  have k2 := kept_word_ne lim st hal hfit j hj 2 (by decide)
  have k3 := kept_word_ne lim st hal hfit j hj 3 (by decide)
  have k4 := kept_word_ne lim st hal hfit j hj 4 (by decide)
  simp only [Nat.mul_zero, Nat.mul_one, BitVec.add_zero] at k0 k1 k2 k3 k4
  simp [written, memLoadByte, k0, k1, k2, k3, k4]

/-- A statement that ends normally without spending clock, then the rest. -/
theorem seq_into (o : Oracle σ) {c1 c2 : PancakeProg} {s s1 : PancakeState σ}
    (h1 : PancakeSem o c1 s = (none, s1)) (hc : s1.clock ≤ s.clock) :
    PancakeSem o (.seq c1 c2) s = PancakeSem o c2 s1 := by
  rw [sem_seq_none h1, show min s.clock s1.clock = s1.clock by omega]

/-- A statement that stops the run stops what follows it too. -/
theorem seq_stop (o : Oracle σ) {c1 c2 : PancakeProg} {s t : PancakeState σ} {r : Result}
    (h1 : PancakeSem o c1 s = (some r, t)) :
    PancakeSem o (.seq c1 c2) s = (some r, { t with clock := min s.clock t.clock }) := by
  rw [PancakeSem, h1]; rfl

/-- The locals the framer writes. -/
def lineWrites : List String := ["len", "cr", "bad", "kind", "kept", "b", "i"]

/-- What a run leaves in memory, from the state `s` it started in: the framer's state `A'` and
verdict `out` in the block at `st`, and every byte and word outside the block as they were. -/
structure LineMem (lim : Nat) (s s' : PancakeState σ) (st : Word) (A' : LineState)
    (out : Option Line) : Prop where
  holds : Holds s' st A'
  reported : Reported s' st out
  ma : s'.memaddrs = s.memaddrs
  be : s'.be = s.be
  ffi : s'.ffi = s.ffi
  base : s'.baseAddr = s.baseAddr
  bytes : ∀ a, Outside lim st a →
    memLoadByte s'.memory s.memaddrs s.be a = memLoadByte s.memory s.memaddrs s.be a
  words : ∀ w, w ≠ st → w ≠ st + 8#64 → w ≠ st + 16#64 → w ≠ st + 24#64 → w ≠ st + 32#64 →
    (∀ j, j < lim → byteAlign (st + 40#64 + BitVec.ofNat 64 j) ≠ w) → s'.memory w = s.memory w

/-- What the framer leaves: where it stopped (`i`), every local it does not write, and memory. -/
structure LineAfter (lim : Nat) (s s' : PancakeState σ) (st : Word) (i : Nat) (A' : LineState)
    (out : Option Line) : Prop where
  i : s'.locals "i" = some (BitVec.ofNat 64 i)
  locals : ∀ v, v ∉ lineWrites → s'.locals v = s.locals v
  mem : LineMem lim s s' st A' out

/-- **The framer is the framer's call.** From a state whose block at `st` holds the framer's state
`A`, and whose locals name the block, the received bytes `q`, their number and the position `i0`,
the fragment reads up to the end of the first line or of the chunk: with clock enough it spends
one tick a byte and then whatever follows it runs on a state holding the framer's state and
verdict after those bytes; with too little it times out, and it never ends otherwise. -/
theorem lineFrag_run (o : Oracle σ) (lim : Nat) (hlim : lim < 2 ^ 62) (hpos : 0 < lim)
    (s : PancakeState σ) (st p : Word) (q : List Byte) (i0 : Nat) (A : LineState)
    (hA : Fits lim A) (hi0 : i0 ≤ q.length) (hq : q.length < 2 ^ 62)
    (hst : s.locals "blk" = some st) (hp : s.locals "p" = some p)
    (hn : s.locals "n" = some (BitVec.ofNat 64 q.length))
    (hi : s.locals "i" = some (BitVec.ofNat 64 i0))
    (hw : ∀ v, v ∈ ["len", "cr", "bad", "kind", "kept", "b"] → ∃ w, s.locals v = some w)
    (hH : Holds s st A) (hC : Chunk s p q) (hR : Room lim s st)
    (hal : st.toNat % 8 = 0) (hfit : st.toNat + 40 + lim ≤ 2 ^ 64)
    (hsep : ∀ j j', j < lim → j' < q.length →
      st + 40#64 + BitVec.ofNat 64 j ≠ p + BitVec.ofNat 64 j') :
    ((frameOnce lim A (q.drop i0)).1 ≤ s.clock →
      ∃ s', s'.clock = s.clock - (frameOnce lim A (q.drop i0)).1 ∧
        LineAfter lim s s' st (i0 + (frameOnce lim A (q.drop i0)).1)
          (frameOnce lim A (q.drop i0)).2.1 (frameOnce lim A (q.drop i0)).2.2 ∧
        ∀ k, PancakeSem o (lineFragP lim k) s = PancakeSem o k s') ∧
    (s.clock < (frameOnce lim A (q.drop i0)).1 →
      ∀ k, ∃ t, PancakeSem o (lineFragP lim k) s = (some .timeout, t)) := by
  obtain ⟨hH0, hH8, hH16, hHK⟩ := hH
  obtain ⟨hR0, hR8, hR16, hR24, hR32, hRb⟩ := hR
  obtain ⟨wlen, hwlen⟩ := hw "len" (by simp)
  obtain ⟨wcr, hwcr⟩ := hw "cr" (by simp)
  obtain ⟨wbad, hwbad⟩ := hw "bad" (by simp)
  obtain ⟨wkind, hwkind⟩ := hw "kind" (by simp)
  obtain ⟨wkept, hwkept⟩ := hw "kept" (by simp)
  obtain ⟨wb, hwb⟩ := hw "b" (by simp)
  -- the state read into the working names
  let s1 : PancakeState σ := { s with locals := setLocal s.locals "len" (BitVec.ofNat 64 A.len) }
  let s2 : PancakeState σ := { s1 with locals := setLocal s1.locals "cr" (bw A.cr) }
  let s3 : PancakeState σ := { s2 with locals := setLocal s2.locals "bad" (bw A.bad) }
  let s4 : PancakeState σ := { s3 with locals := setLocal s3.locals "kind" (BitVec.ofNat 64 0) }
  let s5 : PancakeState σ := { s4 with locals := setLocal s4.locals "kept" (BitVec.ofNat 64 0) }
  have h1 : PancakeSem o (.assign "len" (.loadWord (x "blk"))) s = (none, s1) :=
    sem_assign (old := wlen) (by simp [eval, x, hst, hR0, hH0]) hwlen
  have h2 : PancakeSem o (.assign "cr" (.loadWord (add (x "blk") (c 8)))) s1 = (none, s2) :=
    sem_assign (old := wcr) (by simp [eval, x, c, add, s1, setLocal, hst, hR8, hH8])
      (by simp [s1, setLocal, hwcr])
  have h3 : PancakeSem o (.assign "bad" (.loadWord (add (x "blk") (c 16)))) s2 = (none, s3) :=
    sem_assign (old := wbad) (by simp [eval, x, c, add, s2, s1, setLocal, hst, hR16, hH16])
      (by simp [s2, s1, setLocal, hwbad])
  have h4 : PancakeSem o (set "kind" 0) s3 = (none, s4) :=
    sem_assign (old := wkind) rfl (by simp [s3, s2, s1, setLocal, hwkind])
  have h5 : PancakeSem o (set "kept" 0) s4 = (none, s5) :=
    sem_assign (old := wkept) rfl (by simp [s4, s3, s2, s1, setLocal, hwkept])
  have l5 : ∀ v, v ≠ "len" → v ≠ "cr" → v ≠ "bad" → v ≠ "kind" → v ≠ "kept" →
      s5.locals v = s.locals v := by
    intro v a1 a2 a3 a4 a5; simp [s5, s4, s3, s2, s1, setLocal, a1, a2, a3, a4, a5]
  have hloc5 : LineLocals s5 st p (BitVec.ofNat 64 q.length) i0 A 0#64 0#64 :=
    ⟨by rw [l5 _ (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hst,
     by rw [l5 _ (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hp,
     by rw [l5 _ (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hn,
     by rw [l5 _ (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hi,
     by simp [s5, s4, s3, s2, s1, setLocal], by simp [s5, s4, s3, s2, setLocal],
     by simp [s5, s4, s3, setLocal], by simp [s5, s4, setLocal],
     by simp [s5, setLocal],
     ⟨wb, by rw [l5 _ (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hwb⟩⟩
  have hreads : ∀ k, PancakeSem o (lineFragP lim k) s =
      PancakeSem o (.seq (.while_ lineGuardP (lineBodyP lim)) (lineStoresP k)) s5 := by
    intro k
    unfold lineFragP
    rw [seq_into o h1 (Nat.le_refl _), seq_into o h2 (Nat.le_refl _), seq_into o h3 (Nat.le_refl _),
      seq_into o h4 (Nat.le_refl _), seq_into o h5 (Nat.le_refl _)]
  obtain ⟨hnorm, htime⟩ :=
    lineLoop_run o lim hlim hpos s5 st p q i0 A 0#64 hA hi0 hq hloc5 hHK hC hRb hsep
  refine ⟨fun hk => ?_, fun hk k => ?_⟩
  case refine_2 =>
    obtain ⟨t, ht⟩ := htime hk
    exact ⟨_, (hreads k).trans (seq_stop o ht)⟩
  obtain ⟨s6, hrun6, hclk6, hI⟩ := hnorm hk
  have hfeed := frameOnce_feed lim A (q.drop i0)
  have hloc6 := hI.loc
  have hkept6 := hI.kept
  simp only [hfeed] at hloc6 hkept6
  have hma6 : s6.memaddrs = s.memaddrs := hI.ma
  have hhead : ∀ o : Option Line, o.toList.head? = o := by intro o; cases o <;> rfl
  simp only [hhead] at hloc6 hkept6
  let m7 := written s6.memory st (BitVec.ofNat 64 (frameOnce lim A (q.drop i0)).2.1.len)
    (bw (frameOnce lim A (q.drop i0)).2.1.cr) (bw (frameOnce lim A (q.drop i0)).2.1.bad)
    (kindW (frameOnce lim A (q.drop i0)).2.2) (keptW 0#64 (frameOnce lim A (q.drop i0)).2.2)
  obtain ⟨s7, hs7⟩ : ∃ s7 : PancakeState σ, s7 = { s6 with memory := m7 } := ⟨_, rfl⟩
  have hstores : ∀ k, PancakeSem o (lineStoresP k) s6 = PancakeSem o k s7 := fun k => hs7 ▸
    lineStores_run o k s6 st _ _ _ _ _ hloc6.st hloc6.len hloc6.cr hloc6.bad hloc6.kind hloc6.kept
      (by rw [hma6]; exact hR0) (by rw [hma6]; exact hR8) (by rw [hma6]; exact hR16)
      (by rw [hma6]; exact hR24) (by rw [hma6]; exact hR32)
  obtain ⟨w1, w2, w3, w4, w5, w6, w7, w8, w9, w10⟩ := words_ne st
  have hwritten := written_outside lim st
  have hbyte := written_kept lim st hal hfit
  have hfits : Fits lim (frameOnce lim A (q.drop i0)).2.1 := by
    have := hI.fits; rw [hfeed] at this; exact this
  have hmem7 : s7.memory = written s6.memory st
      (BitVec.ofNat 64 (frameOnce lim A (q.drop i0)).2.1.len)
      (bw (frameOnce lim A (q.drop i0)).2.1.cr) (bw (frameOnce lim A (q.drop i0)).2.1.bad)
      (kindW (frameOnce lim A (q.drop i0)).2.2) (keptW 0#64 (frameOnce lim A (q.drop i0)).2.2) := by
    rw [hs7]
  have hrun : ∀ k, PancakeSem o (lineFragP lim k) s = PancakeSem o k s7 := fun k =>
    (hreads k).trans ((seq_into o hrun6 (by omega)).trans (hstores k))
  have hk1 := hkept6
  simp only [keptOf] at hk1
  have hfr := frameOnce_fresh lim A (q.drop i0)
  have hle := frameOnce_kept_le lim hpos A (q.drop i0)
  have hi6 := hloc6.i
  have hn6 := hI.names
  have hw6 := hI.words
  have hby6 := hI.bytes
  have hclk7 : s7.clock = s.clock - (frameOnce lim A (q.drop i0)).1 := by
    have e1 := hclk6
    have e2 : s5.clock = s.clock := rfl
    rw [hs7]; show s6.clock = _; omega
  have hma7 : s7.memaddrs = s.memaddrs := by rw [hs7]; exact hma6
  have hbe7 : s7.be = s.be := by rw [hs7]; exact hI.be
  have hloc7 : ∀ v, s7.locals v = s6.locals v := by intro v; rw [hs7]
  have hmem7' : s7.memory = m7 := by rw [hs7]
  refine ⟨s7, hclk7, ?_, hrun⟩
  have hnames : ∀ v, v ∉ lineWrites → v ∉ lineNames := by
    intro v hv h
    apply hv
    simp only [lineNames, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h <;> simp [lineWrites, h]
  have hwr : ∀ v, v ∉ lineWrites → v ≠ "len" ∧ v ≠ "cr" ∧ v ≠ "bad" ∧ v ≠ "kind" ∧ v ≠ "kept" := by
    intro v hv; simp only [lineWrites, List.mem_cons, List.not_mem_nil, or_false, not_or] at hv
    exact ⟨hv.1, hv.2.1, hv.2.2.1, hv.2.2.2.1, hv.2.2.2.2.1⟩
  generalize hr : frameOnce lim A (q.drop i0) = r at hmem7 hk1 hfits hfr hle hi6 hmem7' ⊢
  obtain ⟨K, A', out⟩ := r
  simp only at hfits hk1 hmem7 hi6 hmem7' ⊢
  have hlen : A'.buf.length ≤ lim := by have := hfits.1; have := hfits.2.1; omega
  refine ⟨by rw [hloc7]; exact hi6, fun v hv => ?_,
      ⟨⟨?_, ?_, ?_, ?_⟩, ?_, hma7, hbe7, ?_, ?_, ?_, ?_⟩⟩
  · obtain ⟨a1, a2, a3, a4, a5⟩ := hwr v hv
    rw [hloc7, hn6 v (hnames v hv), l5 v a1 a2 a3 a4 a5]
  · rw [hmem7]; simp only [written, Ne.symm w4, Ne.symm w7, Ne.symm w9, Ne.symm w10, if_false,
      if_true]
  · rw [hmem7]; simp only [written, Ne.symm w3, Ne.symm w6, Ne.symm w8, if_false, if_true]
  · rw [hmem7]; simp only [written, Ne.symm w2, Ne.symm w5, if_false, if_true]
  · intro j hj
    rw [hmem7, hma7, hbe7, ← hma6, ← hI.be, hbyte _ _ _ _ _ _ _ _ j (by omega)]
    cases out with
    | none => exact hk1 j hj
    | some l =>
      have := hfr l rfl
      simp only at this; subst this
      simp [LineState.fresh] at hj
  · cases out with
    | none =>
      show s7.memory (st + 24#64) = 0#64
      rw [hmem7]; simp only [written, Ne.symm w1, if_false, if_true, kindW]
    | some l =>
      have hle' := hle l hA rfl
      refine ⟨?_, ?_, ?_⟩
      · rw [hmem7]; simp only [written, Ne.symm w1, if_false, if_true, kindW]
      · rw [hmem7]; simp only [written, if_true, keptW]
      · intro j hj
        rw [hmem7, hma7, hbe7, ← hma6, ← hI.be, hbyte _ _ _ _ _ _ _ _ j (by omega)]
        exact hk1 j hj
  · rw [hs7]; exact hI.ffi
  · rw [hs7]; exact hI.base
  · intro a ha
    rw [hmem7, hwritten _ _ _ _ _ _ _ _ a ha]
    exact hI.bytes a ha.2.2.2.2.2
  · intro w a0 a8 a16 a24 a32 hw
    rw [hmem7]
    simp only [written, a0, a8, a16, a24, a32, if_false]
    exact hI.words w hw
/-- **The exported function's run is the framer's call**: its working names declared, the
framer, and the position it stopped at returned. -/
theorem lineRun_run (o : Oracle σ) (lim : Nat) (hlim : lim < 2 ^ 62) (hpos : 0 < lim)
    (s : PancakeState σ) (st p : Word) (q : List Byte) (i0 : Nat) (A : LineState)
    (hA : Fits lim A) (hi0 : i0 ≤ q.length) (hq : q.length < 2 ^ 62)
    (hst : s.locals "blk" = some st) (hp : s.locals "p" = some p)
    (hn : s.locals "n" = some (BitVec.ofNat 64 q.length))
    (hi : s.locals "i" = some (BitVec.ofNat 64 i0))
    (hH : Holds s st A) (hC : Chunk s p q) (hR : Room lim s st)
    (hal : st.toNat % 8 = 0) (hfit : st.toNat + 40 + lim ≤ 2 ^ 64)
    (hsep : ∀ j j', j < lim → j' < q.length →
      st + 40#64 + BitVec.ofNat 64 j ≠ p + BitVec.ofNat 64 j') :
    ((frameOnce lim A (q.drop i0)).1 ≤ s.clock →
      ∃ s', PancakeSem o (lineRunP lim) s =
          (some (.return_ (BitVec.ofNat 64 (i0 + (frameOnce lim A (q.drop i0)).1))), s') ∧
        s'.clock = s.clock - (frameOnce lim A (q.drop i0)).1 ∧
        LineMem lim s s' st (frameOnce lim A (q.drop i0)).2.1 (frameOnce lim A (q.drop i0)).2.2) ∧
    (s.clock < (frameOnce lim A (q.drop i0)).1 →
      ∃ t, PancakeSem o (lineRunP lim) s = (some .timeout, t)) := by
  let sA : PancakeState σ := { s with locals := setLocal s.locals "len" (BitVec.ofNat 64 0) }
  let sB : PancakeState σ := { sA with locals := setLocal sA.locals "cr" (BitVec.ofNat 64 0) }
  let sC : PancakeState σ := { sB with locals := setLocal sB.locals "bad" (BitVec.ofNat 64 0) }
  let sD : PancakeState σ := { sC with locals := setLocal sC.locals "kind" (BitVec.ofNat 64 0) }
  let sE : PancakeState σ := { sD with locals := setLocal sD.locals "kept" (BitVec.ofNat 64 0) }
  let sF : PancakeState σ := { sE with locals := setLocal sE.locals "b" (BitVec.ofNat 64 0) }
  obtain ⟨hnorm, htime⟩ := lineFrag_run o lim hlim hpos sF st p q i0 A hA hi0 hq
    (by simp +zetaDelta [setLocal, hst]) (by simp +zetaDelta [setLocal, hp])
    (by simp +zetaDelta [setLocal, hn]) (by simp +zetaDelta [setLocal, hi])
    (by intro v hv; simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
        rcases hv with rfl | rfl | rfl | rfl | rfl | rfl <;>
          exact ⟨BitVec.ofNat 64 0, by simp +zetaDelta [setLocal]⟩)
    hH hC hR hal hfit hsep
  refine ⟨fun hk => ?_, fun hk => ?_⟩
  · obtain ⟨s7, hclk7, la, hrun7⟩ := hnorm hk
    have hret : PancakeSem o (.ret (x "i")) s7 =
        (some (.return_ (BitVec.ofNat 64 (i0 + (frameOnce lim A (q.drop i0)).1))),
            emptyLocals s7) := by
      rw [PancakeSem]; simp [eval, x, la.i]
    have hrun : PancakeSem o (lineRunP lim) s = _ :=
      sem_dec o rfl (sem_dec o rfl (sem_dec o rfl (sem_dec o rfl (sem_dec o rfl (sem_dec o rfl
        ((hrun7 (.ret (x "i"))).trans hret))))))
    exact ⟨_, hrun, hclk7, ⟨la.mem.holds, la.mem.reported, la.mem.ma, la.mem.be, la.mem.ffi,
      la.mem.base, la.mem.bytes, la.mem.words⟩⟩
  · obtain ⟨t, ht⟩ := htime hk (.ret (x "i"))
    exact ⟨_, sem_dec o rfl (sem_dec o rfl (sem_dec o rfl (sem_dec o rfl (sem_dec o rfl
      (sem_dec o rfl ht)))))⟩

/-! ## The exported function -/

/-- The checks before the run: a negative length or position, or a position past the length. -/
def guardP (run : PancakeProg) : PancakeProg :=
  .cond (.cmp .less (x "n") (c 0)) (.ret (c refused))
    (.cond (.cmp .less (x "i") (c 0)) (.ret (c refused))
      (.cond (.cmp .less (x "n") (x "i")) (.ret (c refused)) run))

theorem frameLine_lower (name : String) (lim : Nat) :
    Lower.lower (frameLine name lim) = some (guardP (lineRunP lim)) := rfl

/-- The checks let a sound call through to the run. -/
theorem guard_pass (o : Oracle σ) (run : PancakeProg) (s : PancakeState σ) (n i : Nat)
    (hn : s.locals "n" = some (BitVec.ofNat 64 n)) (hi : s.locals "i" = some (BitVec.ofNat 64 i))
    (hin : i ≤ n) (hn62 : n < 2 ^ 62) :
    PancakeSem o (guardP run) s = PancakeSem o run s := by
  have h1 : signedLt (BitVec.ofNat 64 n) (BitVec.ofNat 64 0) = false := by
    rw [signedLt_ofNat _ _ (by omega) (by omega)]; simp
  have h2 : signedLt (BitVec.ofNat 64 i) (BitVec.ofNat 64 0) = false := by
    rw [signedLt_ofNat _ _ (by omega) (by omega)]; simp
  have h3 : signedLt (BitVec.ofNat 64 n) (BitVec.ofNat 64 i) = false := by
    rw [signedLt_ofNat _ _ (by omega) (by omega)]; simp; omega
  have z : ¬ ((0#64 : Word) ≠ 0) := by decide
  rw [guardP, sem_cond o (show eval s (.cmp .less (x "n") (c 0)) = some 0#64 by
      simp [eval, x, c, hn, h1]), if_neg z,
    sem_cond o (show eval s (.cmp .less (x "i") (c 0)) = some 0#64 by simp [eval, x, c, hi, h2]),
    if_neg z,
    sem_cond o (show eval s (.cmp .less (x "n") (x "i")) = some 0#64 by simp [eval, x, hn, hi, h3]),
    if_neg z]

/-- **`dn_frame_line` is the framer's call**, for the function the gate prints. The chunk is shorter
than the refusal code, so the position returned is never mistaken for it. -/
theorem frameLine_run (o : Oracle σ) (name : String) (lim : Nat) (hlim : lim < 2 ^ 62)
    (hpos : 0 < lim) (s : PancakeState σ) (st p : Word) (q : List Byte) (i0 : Nat) (A : LineState)
    (hA : Fits lim A) (hi0 : i0 ≤ q.length) (hq : q.length < refused)
    (hst : s.locals "blk" = some st) (hp : s.locals "p" = some p)
    (hn : s.locals "n" = some (BitVec.ofNat 64 q.length))
    (hi : s.locals "i" = some (BitVec.ofNat 64 i0))
    (hH : Holds s st A) (hC : Chunk s p q) (hR : Room lim s st)
    (hal : st.toNat % 8 = 0) (hfit : st.toNat + 40 + lim ≤ 2 ^ 64)
    (hsep : ∀ j j', j < lim → j' < q.length →
      st + 40#64 + BitVec.ofNat 64 j ≠ p + BitVec.ofNat 64 j')
    {prog : PancakeProg} (hprog : Lower.lower (frameLine name lim) = some prog) :
    ((frameOnce lim A (q.drop i0)).1 ≤ s.clock →
      ∃ s', PancakeSem o prog s =
          (some (.return_ (BitVec.ofNat 64 (i0 + (frameOnce lim A (q.drop i0)).1))), s') ∧
        s'.clock = s.clock - (frameOnce lim A (q.drop i0)).1 ∧
        LineMem lim s s' st (frameOnce lim A (q.drop i0)).2.1 (frameOnce lim A (q.drop i0)).2.2) ∧
    (s.clock < (frameOnce lim A (q.drop i0)).1 →
      ∃ t, PancakeSem o prog s = (some .timeout, t)) := by
  have hq62 : q.length < 2 ^ 62 := by unfold refused at hq; omega
  rw [frameLine_lower] at hprog
  cases hprog
  rw [guard_pass o _ s q.length i0 hn hi hi0 hq62]
  exact lineRun_run o lim hlim hpos s st p q i0 A hA hi0 hq62 hst hp hn hi hH hC hR hal hfit hsep

/-- The checks refuse a negative length or position, or a position past the length, with the
refusal code and before anything is read or written. -/
theorem guard_refuses (o : Oracle σ) (run : PancakeProg) (s : PancakeState σ) (nw iw : Word)
    (hn : s.locals "n" = some nw) (hi : s.locals "i" = some iw)
    (h : signedLt nw (BitVec.ofNat 64 0) = true ∨ signedLt iw (BitVec.ofNat 64 0) = true ∨
      signedLt nw iw = true) :
    PancakeSem o (guardP run) s = (some (.return_ (BitVec.ofNat 64 refused)), emptyLocals s) := by
  have one : (1#64 : Word) ≠ 0 := by decide
  have z : ¬ ((0#64 : Word) ≠ 0) := by decide
  unfold guardP
  by_cases h1 : signedLt nw (BitVec.ofNat 64 0) = true
  · rw [sem_cond o
      (show eval s (.cmp .less (x "n") (c 0)) = some 1#64 by simp [eval, x, c, hn, h1]),
      if_pos one]
    exact sem_ret_const o s _
  rw [sem_cond o (show eval s (.cmp .less (x "n") (c 0)) = some 0#64 by simp [eval, x, c, hn, h1]),
    if_neg z]
  by_cases h2 : signedLt iw (BitVec.ofNat 64 0) = true
  · rw [sem_cond o
      (show eval s (.cmp .less (x "i") (c 0)) = some 1#64 by simp [eval, x, c, hi, h2]),
      if_pos one]
    exact sem_ret_const o s _
  rw [sem_cond o (show eval s (.cmp .less (x "i") (c 0)) = some 0#64 by simp [eval, x, c, hi, h2]),
    if_neg z]
  have h3 : signedLt nw iw = true := by
    rcases h with h | h | h
    · exact absurd h h1
    · exact absurd h h2
    · exact h
  rw [sem_cond o
      (show eval s (.cmp .less (x "n") (x "i")) = some 1#64 by simp [eval, x, hn, hi, h3]),
    if_pos one]
  exact sem_ret_const o s _

theorem frameLine_refuses (o : Oracle σ) (name : String) (lim : Nat) (s : PancakeState σ)
    (nw iw : Word) (hn : s.locals "n" = some nw) (hi : s.locals "i" = some iw)
    (h : signedLt nw (BitVec.ofNat 64 0) = true ∨ signedLt iw (BitVec.ofNat 64 0) = true ∨
      signedLt nw iw = true) {prog : PancakeProg}
    (hprog : Lower.lower (frameLine name lim) = some prog) :
    PancakeSem o prog s = (some (.return_ (BitVec.ofNat 64 refused)), emptyLocals s) := by
  rw [frameLine_lower] at hprog
  cases hprog
  exact guard_refuses o _ s nw iw hn hi h

/-! ## The block framer

The state of a block lives at `blk` too: the phase at `blk`, whether the block is already refused
at `blk + 8`, how many bytes it holds at `blk + 16`; the verdict at `blk + 24` and the number of
bytes the block holds at `blk + 32`; the bytes it holds from `blk + 40`, up to `cap` of them.
`dn_frame_block(blk, p, n, i)` reads up to the end of the block or of the chunk. -/

def phaseCode : Phase → Nat
  | .bol => 0 | .data => 1 | .cr => 2 | .dot => 3 | .dotcr => 4

def blockCode : BlockKind → Nat
  | .accepted => 1 | .refused => 2 | .tooLarge => 3

def spoilS : List PStmt :=
  [.ite (eEq (v "b") (n 10)) [.assign "bad" (n 1)] [],
   .ite (eEq (v "b") (n 0)) [.assign "bad" (n 1)] []]

/-- A byte inside a line: hold it, and see whether it spoils the block. -/
def dataS : List PStmt := [.assign "post" (n 1)] ++ spoilS ++ [.assign "ph" (n 1)]

/-- A CR after a CR held back: the first is inside the line. -/
def crCrS : List PStmt := [.assign "pre" (n 1), .assign "bad" (n 1), .assign "ph" (n 2)]

/-- Another byte after a CR held back. -/
def crByteS : List PStmt :=
  [.assign "pre" (n 1), .assign "post" (n 1), .assign "bad" (n 1), .assign "ph" (n 1)]

/-- The end of the block: the verdict, and a fresh state. -/
def endS (cap : Nat) : List PStmt :=
  [.ite (v "bad") [.assign "kind" (n 2), .assign "held" (n 0)]
     [.ite (eLt (n cap) (v "size")) [.assign "kind" (n 3), .assign "held" (n 0)]
        [.assign "kind" (n 1), .assign "held" (v "size")]],
   .assign "ph" (n 0), .assign "bad" (n 0)]

/-- What the byte does, decided from the phase and the byte. -/
def logicS (cap : Nat) : List PStmt :=
  [.assign "pre" (n 0), .assign "post" (n 0),
   .ite (eEq (v "ph") (n 0))
     [.ite (eEq (v "b") (n 46)) [.assign "ph" (n 3)]
        [.ite (eEq (v "b") (n 13)) [.assign "ph" (n 2)] dataS]]
     [.ite (eEq (v "ph") (n 1))
        [.ite (eEq (v "b") (n 13)) [.assign "ph" (n 2)] dataS]
        [.ite (eEq (v "ph") (n 2))
           [.ite (eEq (v "b") (n 10))
              [.assign "pre" (n 1), .assign "post" (n 1), .assign "ph" (n 0)]
              [.ite (eEq (v "b") (n 13)) crCrS crByteS]]
           [.ite (eEq (v "ph") (n 3))
              [.ite (eEq (v "b") (n 13)) [.assign "ph" (n 4)] dataS]
              [.ite (eEq (v "b") (n 10)) (endS cap)
                 [.ite (eEq (v "b") (n 13)) crCrS crByteS]]]]]]

/-- Hold one byte: kept while there is room, only counted past it. -/
def putS (cap : Nat) (e : PExpr) : List PStmt :=
  [.ite (eLt (v "size") (n cap))
     [.storeb (eAdd (eAdd (v "blk") (n 40)) (v "size")) e,
      .assign "size" (eAdd (v "size") (n 1))]
     [.assign "size" (eAdd (v "size") (eEq (v "size") (n cap)))]]

def blockLoop (cap : Nat) : PStmt :=
  .while (eAnd (eLt (v "i") (v "n")) (eEq (v "kind") (n 0)))
    ([.assign "b" (.loadb (eAdd (v "p") (v "i"))), .assign "i" (eAdd (v "i") (n 1))] ++
     logicS cap ++
     [.ite (v "pre") (putS cap (n 13)) [], .ite (v "post") (putS cap (v "b")) [],
      .ite (v "kind") [.assign "size" (n 0)] []])

/-- The block framer as statements that declare nothing, like `lineFrag`: its working names are
`ph`, `bad`, `size`, `kind`, `held`, `b`, `pre` and `post`. -/
def blockFrag (cap : Nat) : List PStmt :=
  [.assign "ph" (.loadw 1 (v "blk")),
   .assign "bad" (.loadw 1 (eAdd (v "blk") (n 8))),
   .assign "size" (.loadw 1 (eAdd (v "blk") (n 16))),
   .assign "kind" (n 0),
   .assign "held" (n 0),
   blockLoop cap,
   .store (v "blk") (v "ph"),
   .store (eAdd (v "blk") (n 8)) (v "bad"),
   .store (eAdd (v "blk") (n 16)) (v "size"),
   .store (eAdd (v "blk") (n 24)) (v "kind"),
   .store (eAdd (v "blk") (n 32)) (v "held")]

def blockDecs : List PStmt :=
  [.dec "ph" (n 0), .dec "bad" (n 0), .dec "size" (n 0), .dec "kind" (n 0), .dec "held" (n 0),
   .dec "b" (n 0), .dec "pre" (n 0), .dec "post" (n 0)]

def blockRun (cap : Nat) : List PStmt := blockDecs ++ blockFrag cap ++ [.ret (v "i")]

/-- `dn_frame_block(blk, p, n, i)`, for blocks of at most `cap` bytes. -/
def frameBlock (name : String) (cap : Nat) : PFun :=
  { name, exported := true, params := [(1, "blk"), (1, "p"), (1, "n"), (1, "i")],
    body := Kernels.rejectNegative ["n", "i"] [.ret (n refused)]
      [.ite (eLt (v "n") (v "i")) [.ret (n refused)] (blockRun cap)] }

/-! ### The block program as the model runs it -/

private def eqc (name : String) (k : Nat) : PancakeExp := .cmp .equal (x name) (c k)

def dataP : PancakeProg :=
  .seq (set "post" 1) (.seq (.cond (eqc "b" 10) (set "bad" 1) .skip)
    (.seq (.cond (eqc "b" 0) (set "bad" 1) .skip) (set "ph" 1)))

def crCrP : PancakeProg := .seq (set "pre" 1) (.seq (set "bad" 1) (set "ph" 2))

def crByteP : PancakeProg := .seq (set "pre" 1)
    (.seq (set "post" 1) (.seq (set "bad" 1) (set "ph" 1)))

def endP (cap : Nat) : PancakeProg :=
  .seq (.cond (x "bad") (.seq (set "kind" 2) (set "held" 0))
      (.cond (.cmp .less (c cap) (x "size")) (.seq (set "kind" 3) (set "held" 0))
        (.seq (set "kind" 1) (.assign "held" (x "size")))))
    (.seq (set "ph" 0) (set "bad" 0))

def phaseP (cap : Nat) : PancakeProg :=
  .cond (eqc "ph" 0)
    (.cond (eqc "b" 46) (set "ph" 3) (.cond (eqc "b" 13) (set "ph" 2) dataP))
    (.cond (eqc "ph" 1)
      (.cond (eqc "b" 13) (set "ph" 2) dataP)
      (.cond (eqc "ph" 2)
        (.cond (eqc "b" 10) (.seq (set "pre" 1) (.seq (set "post" 1) (set "ph" 0)))
          (.cond (eqc "b" 13) crCrP crByteP))
        (.cond (eqc "ph" 3)
          (.cond (eqc "b" 13) (set "ph" 4) dataP)
          (.cond (eqc "b" 10) (endP cap) (.cond (eqc "b" 13) crCrP crByteP)))))

def putP (cap : Nat) (e : PancakeExp) : PancakeProg :=
  .cond (.cmp .less (x "size") (c cap))
    (.seq (.storeByte (add (add (x "blk") (c 40)) (x "size")) e)
        (.assign "size" (add (x "size") (c 1))))
    (.assign "size" (add (x "size") (.cmp .equal (x "size") (c cap))))

def blockBodyP (cap : Nat) : PancakeProg :=
  .seq (.assign "b" (.loadByte (add (x "p") (x "i"))))
  (.seq (.assign "i" (add (x "i") (c 1)))
  (.seq (set "pre" 0)
  (.seq (set "post" 0)
  (.seq (phaseP cap)
  (.seq (.cond (x "pre") (putP cap (c 13)) .skip)
  (.seq (.cond (x "post") (putP cap (x "b")) .skip)
    (.cond (x "kind") (set "size" 0) .skip)))))))

theorem blockLoop_lower (cap : Nat) :
    Lower.lowerStmt1 (blockLoop cap) = some (.while_ lineGuardP (blockBodyP cap)) := rfl

/-- How many bytes the block holds, as its verdict reports it. -/
def heldLen (cap : Nat) (S : BlockState) : Nat :=
  if S.bad then 0 else if cap < S.size then 0 else S.size

theorem result_kind_code (cap : Nat) (S : BlockState) :
    blockCode (result cap S).kind = if S.bad then 2 else if cap < S.size then 3 else 1 := by
  unfold result; split <;> (try split) <;> rfl

/-- What the phase logic leaves: the memory as it was, and in the locals what the byte is planned
to do, or the verdict at the end of the block. -/
def PhaseOut (cap : Nat) (s s' : PancakeState σ) (S : BlockState) (y : Byte) : Prop :=
  s'.memory = s.memory ∧ s'.memaddrs = s.memaddrs ∧ s'.be = s.be ∧ s'.clock = s.clock ∧
  s'.ffi = s.ffi ∧ s'.baseAddr = s.baseAddr ∧
  (∀ v, v ≠ "pre" → v ≠ "post" → v ≠ "ph" → v ≠ "bad" → v ≠ "size" → v ≠ "kind" →
    v ≠ "held" → s'.locals v = s.locals v) ∧
  if (plan S y).ends then
    s'.locals "pre" = some 0#64 ∧ s'.locals "post" = some 0#64 ∧
    s'.locals "ph" = some 0#64 ∧ s'.locals "bad" = some 0#64 ∧ s'.locals "size" = s.locals "size" ∧
    s'.locals "kind" = some (BitVec.ofNat 64 (blockCode (result cap S).kind)) ∧
    s'.locals "held" = some (BitVec.ofNat 64 (heldLen cap S))
  else
    s'.locals "pre" = some (bw (plan S y).pre) ∧ s'.locals "post" = some (bw (plan S y).post) ∧
    s'.locals "ph" = some (BitVec.ofNat 64 (phaseCode (plan S y).phase)) ∧
    s'.locals "bad" = some (bw (plan S y).bad) ∧ s'.locals "size" = s.locals "size" ∧
    s'.locals "kind" = s.locals "kind" ∧ s'.locals "held" = s.locals "held"

/-- The locals the phase logic reads. -/
structure PhaseIn (s : PancakeState σ) (S : BlockState) (y : Byte) : Prop where
  ph : s.locals "ph" = some (BitVec.ofNat 64 (phaseCode S.phase))
  bad : s.locals "bad" = some (bw S.bad)
  size : s.locals "size" = some (BitVec.ofNat 64 S.size)
  b : s.locals "b" = some (y.setWidth 64)
  pre : s.locals "pre" = some 0#64
  post : s.locals "post" = some 0#64
  kind : ∃ w, s.locals "kind" = some w
  held : ∃ w, s.locals "held" = some w

theorem wLF : (LF.setWidth 64 : Word) = 10#64 := rfl
theorem wCR : (CR.setWidth 64 : Word) = 13#64 := rfl
theorem wDOT : (DOT.setWidth 64 : Word) = 46#64 := rfl
theorem wNUL : (NUL.setWidth 64 : Word) = 0#64 := rfl

theorem widen_facts (y : Byte) :
    ((y.setWidth 64 = 10#64) ↔ y = LF) ∧ ((y.setWidth 64 = 13#64) ↔ y = CR) ∧
      ((y.setWidth 64 = 46#64) ↔ y = DOT) ∧ ((y.setWidth 64 = 0#64) ↔ y = NUL) :=
  ⟨widen_eq y 10 (by decide), widen_eq y 13 (by decide), widen_eq y 46 (by decide),
    widen_eq y 0 (by decide)⟩

/-- The phase logic at the start of a line. -/
theorem phase_bol (o : Oracle σ) (cap : Nat) (s : PancakeState σ) (S : BlockState) (y : Byte)
    (hP : S.phase = .bol) (h : PhaseIn s S y) :
    ∃ s', PancakeSem o (phaseP cap) s = (none, s') ∧ PhaseOut cap s s' S y := by
  obtain ⟨hph, hbad, hsize, hb, hpre, hpost, ⟨wk, hwk⟩, ⟨wh, hwh⟩⟩ := h
  obtain ⟨e10, e13, e46, e0⟩ := widen_facts y
  by_cases hL : y = LF <;> by_cases hC : y = CR <;> by_cases hD : y = DOT <;>
      by_cases hN : y = NUL <;>
    simp +contextual [cr_ne_dot, lf_ne_cr, lf_ne_dot, nul_ne_cr, lf_ne_nul, nul_ne_dot, nul_ne_lf,
        PhaseOut, phaseP, dataP, eqc, set, x, c, PancakeSem, eval, clampClock,
      setLocal, hph, hbad, hsize, hb, hpre, hpost, hwk, hwh, e10, e13, e46, e0, plan, hP, hL, hC,
      hD, hN, phaseCode, bw, spoils, wLF, wCR, wDOT, wNUL]

/-- The phase logic inside a line. -/
theorem phase_data (o : Oracle σ) (cap : Nat) (s : PancakeState σ) (S : BlockState) (y : Byte)
    (hP : S.phase = .data) (h : PhaseIn s S y) :
    ∃ s', PancakeSem o (phaseP cap) s = (none, s') ∧ PhaseOut cap s s' S y := by
  obtain ⟨hph, hbad, hsize, hb, hpre, hpost, ⟨wk, hwk⟩, ⟨wh, hwh⟩⟩ := h
  obtain ⟨e10, e13, _, e0⟩ := widen_facts y
  by_cases hL : y = LF <;> by_cases hC : y = CR <;> by_cases hD : y = DOT <;>
      by_cases hN : y = NUL <;>
    simp +contextual [dot_ne_cr, lf_ne_cr, dot_ne_lf, nul_ne_cr, dot_ne_nul, lf_ne_nul, nul_ne_lf,
        PhaseOut, phaseP, dataP, crCrP, crByteP, eqc, set, x, c, PancakeSem, eval,
      clampClock, setLocal, hph, hbad, hsize, hb, hpre, hpost, hwk, hwh, e10, e13, e0, plan, hP,
      hL, hC, hD, hN, phaseCode, bw, spoils, wLF, wCR, wDOT, wNUL]

/-- The phase logic after a CR held back. -/
theorem phase_cr (o : Oracle σ) (cap : Nat) (s : PancakeState σ) (S : BlockState) (y : Byte)
    (hP : S.phase = .cr) (h : PhaseIn s S y) :
    ∃ s', PancakeSem o (phaseP cap) s = (none, s') ∧ PhaseOut cap s s' S y := by
  obtain ⟨hph, hbad, hsize, hb, hpre, hpost, ⟨wk, hwk⟩, ⟨wh, hwh⟩⟩ := h
  obtain ⟨e10, e13, _, _⟩ := widen_facts y
  by_cases hL : y = LF <;> by_cases hC : y = CR <;> by_cases hD : y = DOT <;>
      by_cases hN : y = NUL <;>
    simp +contextual [dot_ne_cr, cr_ne_lf, dot_ne_lf, nul_ne_cr, nul_ne_lf, PhaseOut, phaseP, dataP,
        crCrP, crByteP, eqc, set, x, c, PancakeSem, eval,
      clampClock, setLocal, hph, hbad, hsize, hb, hpre, hpost, hwk, hwh, e10, e13, plan, hP,
      hL, hC, hD, hN, phaseCode, bw, wLF, wCR, wDOT, wNUL]

/-- The phase logic after a dot at the start of a line. -/
theorem phase_dot (o : Oracle σ) (cap : Nat) (s : PancakeState σ) (S : BlockState) (y : Byte)
    (hP : S.phase = .dot) (h : PhaseIn s S y) :
    ∃ s', PancakeSem o (phaseP cap) s = (none, s') ∧ PhaseOut cap s s' S y := by
  obtain ⟨hph, hbad, hsize, hb, hpre, hpost, ⟨wk, hwk⟩, ⟨wh, hwh⟩⟩ := h
  obtain ⟨e10, e13, _, e0⟩ := widen_facts y
  by_cases hL : y = LF <;> by_cases hC : y = CR <;> by_cases hD : y = DOT <;>
      by_cases hN : y = NUL <;>
    simp +contextual [dot_ne_cr, lf_ne_cr, dot_ne_lf, nul_ne_cr, dot_ne_nul, lf_ne_nul, nul_ne_lf,
        PhaseOut, phaseP, dataP, crCrP, crByteP, eqc, set, x, c, PancakeSem, eval,
      clampClock, setLocal, hph, hbad, hsize, hb, hpre, hpost, hwk, hwh, e10, e13, e0, plan, hP,
      hL, hC, hD, hN, phaseCode, bw, spoils, wLF, wCR, wDOT, wNUL]

/-- The phase logic after a dot and a CR at the start of a line: the end of the block, or more. -/
theorem phase_dotcr (o : Oracle σ) (cap : Nat) (hcap : cap < 2 ^ 62) (s : PancakeState σ)
    (S : BlockState) (y : Byte) (hsz : S.size ≤ cap + 1) (hP : S.phase = .dotcr)
        (h : PhaseIn s S y) :
    ∃ s', PancakeSem o (phaseP cap) s = (none, s') ∧ PhaseOut cap s s' S y := by
  obtain ⟨hph, hbad, hsize, hb, hpre, hpost, ⟨wk, hwk⟩, ⟨wh, hwh⟩⟩ := h
  obtain ⟨e10, e13, _, _⟩ := widen_facts y
  have hlt : signedLt (BitVec.ofNat 64 cap) (BitVec.ofNat 64 S.size) = decide (cap < S.size) :=
    signedLt_ofNat _ _ (by omega) (by omega)
  by_cases hL : y = LF
  · subst hL
    cases hB : S.bad <;> by_cases hS : cap < S.size <;>
      simp +contextual [PhaseOut, phaseP, endP, eqc, set, x, c, PancakeSem, eval, clampClock,
        setLocal, hph, hbad, hsize, hb, hpre, hpost, hwk, hwh, plan, hP, phaseCode, bw, hB, hS, hlt,
        result_kind_code, heldLen, wLF]
  · by_cases hC : y = CR <;> by_cases hD : y = DOT <;> by_cases hN : y = NUL <;>
      simp +contextual [dot_ne_cr, cr_ne_lf, dot_ne_lf, nul_ne_cr, nul_ne_lf, PhaseOut, phaseP,
          crCrP, crByteP, eqc, set, x, c, PancakeSem, eval,
        clampClock, setLocal, hph, hbad, hsize, hb, hpre, hpost, hwk, hwh, e10, e13, plan, hP,
        hL, hC, hD, hN, phaseCode, bw, wCR, wDOT, wNUL]

/-- **The phase logic plans what the framer's step does.** -/
theorem phase_run (o : Oracle σ) (cap : Nat) (hcap : cap < 2 ^ 62) (s : PancakeState σ)
    (S : BlockState) (y : Byte) (hsz : S.size ≤ cap + 1) (h : PhaseIn s S y) :
    ∃ s', PancakeSem o (phaseP cap) s = (none, s') ∧ PhaseOut cap s s' S y := by
  cases hP : S.phase
  · exact phase_bol o cap s S y hP h
  · exact phase_data o cap s S y hP h
  · exact phase_cr o cap s S y hP h
  · exact phase_dot o cap s S y hP h
  · exact phase_dotcr o cap hcap s S y hsz hP h

/-! ### Holding a byte -/

/-- A block state the program can hold: it keeps the first `cap` bytes it counts, and counts one
past the buffer at most. -/
def BFits (cap : Nat) (S : BlockState) : Prop := S.buf.length = min S.size cap ∧ S.size ≤ cap + 1

theorem bfits_put (cap : Nat) (S : BlockState) (z : Byte) (h : BFits cap S) :
    BFits cap (put cap S z) := by
  obtain ⟨hb, hs⟩ := h
  unfold put
  split
  · rename_i hlt
    exact ⟨show (S.buf ++ [z]).length = min (S.size + 1) cap by simp; omega,
      show S.size + 1 ≤ cap + 1 by omega⟩
  · rename_i hlt
    exact ⟨show S.buf.length = min (cap + 1) cap by rw [hb]; omega, Nat.le_refl _⟩

theorem bfits_putIf (cap : Nat) (f : Bool) (S : BlockState) (z : Byte) (h : BFits cap S) :
    BFits cap (putIf cap f S z) := by
  unfold putIf; split
  · exact bfits_put cap S z h
  · exact h

/-- Holding a byte: kept at `st + 40 + size` while there is room, only counted past it. -/
theorem putP_run (o : Oracle σ) (cap : Nat) (hcap : cap < 2 ^ 62) (s : PancakeState σ) (st : Word)
    (S : BlockState) (e : PancakeExp) (z : Byte) (hS : BFits cap S)
    (hst : s.locals "blk" = some st) (hsize : s.locals "size" = some (BitVec.ofNat 64 S.size))
    (he : eval s e = some (z.setWidth 64))
    (hdm : S.size < cap → s.memaddrs (byteAlign (st + 40#64 + BitVec.ofNat 64 S.size)) = true) :
    ∃ s', PancakeSem o (putP cap e) s = (none, s') ∧
      s'.locals "size" = some (BitVec.ofNat 64 (put cap S z).size) ∧
      (∀ v, v ≠ "size" → s'.locals v = s.locals v) ∧
      s'.memory = (if S.size < cap then putByte s.memory s.be
          (st + 40#64 + BitVec.ofNat 64 S.size) z
        else s.memory) ∧
      s'.memaddrs = s.memaddrs ∧ s'.be = s.be ∧ s'.clock = s.clock ∧ s'.ffi = s.ffi ∧
      s'.baseAddr = s.baseAddr := by
  have hlt : signedLt (BitVec.ofNat 64 S.size) (BitVec.ofNat 64 cap) = decide (S.size < cap) :=
    signedLt_ofNat _ _ (by have := hS.2; omega) (by omega)
  have hsucc : BitVec.ofNat 64 S.size + 1#64 = BitVec.ofNat 64 (S.size + 1) := (ofNat_succ _).symm
  by_cases hl : S.size < cap
  · have hst8 := memStore_eq s.memory s.memaddrs s.be
      (st + 40#64 + BitVec.ofNat 64 S.size) z (hdm hl)
    simp +contextual [putP, PancakeSem, eval, x, c, add, hst, hsize, he, hlt, hl, hst8,
      clampClock, setLocal, put, hsucc]
  · have hw : BitVec.ofNat 64 S.size +
      (if BitVec.ofNat 64 S.size = BitVec.ofNat 64 cap then 1#64 else 0#64) =
        BitVec.ofNat 64 (cap + 1) := by
      have := hS.2
      by_cases he : S.size = cap
      · rw [he, if_pos rfl, ofNat_succ cap]
      · have h1 : S.size = cap + 1 := by omega
        have h2 : BitVec.ofNat 64 S.size ≠ BitVec.ofNat 64 cap := by
          intro h; have := congrArg BitVec.toNat h; simp at this; omega
        rw [if_neg h2, BitVec.add_zero, h1]
    simp +contextual [putP, PancakeSem, eval, x, c, add, hsize, hlt, hl, setLocal, put, hw]

/-- After holding a byte, the kept bytes are the framer's, and the received bytes are untouched. -/
theorem kept_after_put (cap : Nat) (hcap : cap < 2 ^ 62) (s s' : PancakeState σ) (st p : Word)
    (S : BlockState) (z : Byte) (q : List Byte) (hS : BFits cap S) (hK : Kept s st S.buf)
    (hC : Chunk s p q)
    (hdom : ∀ j, j < cap → s.memaddrs (byteAlign (st + 40#64 + BitVec.ofNat 64 j)) = true)
    (hsep : ∀ j j', j < cap → j' < q.length →
      st + 40#64 + BitVec.ofNat 64 j ≠ p + BitVec.ofNat 64 j')
    (hm : s'.memory =
        (if S.size < cap then putByte s.memory s.be (st + 40#64 + BitVec.ofNat 64 S.size) z
        else s.memory))
    (hma : s'.memaddrs = s.memaddrs) (hbe : s'.be = s.be) :
    Kept s' st (put cap S z).buf ∧ Chunk s' p q ∧
      (∀ a, (∀ j, j < cap → a ≠ st + 40#64 + BitVec.ofNat 64 j) →
        memLoadByte s'.memory s.memaddrs s.be a = memLoadByte s.memory s.memaddrs s.be a) ∧
      (∀ w, (∀ j, j < cap → byteAlign (st + 40#64 + BitVec.ofNat 64 j) ≠ w) →
        s'.memory w = s.memory w) := by
  obtain ⟨hb, hs⟩ := hS
  have hother : ∀ a, a ≠ st + 40#64 + BitVec.ofNat 64 S.size →
      memLoadByte s'.memory s.memaddrs s.be a = memLoadByte s.memory s.memaddrs s.be a := by
    intro a ha; rw [hm]; split
    · exact load_putByte_diff _ _ _ _ _ _ ha
    · rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro j hj
    rw [hma, hbe]
    by_cases hl : S.size < cap
    · have hbuf : (put cap S z).buf = S.buf ++ [z] := by simp [put, hl]
      simp only [hbuf, List.length_append, List.length_singleton] at hj ⊢
      by_cases hjl : j < S.buf.length
      · rw [hother _ (region_addr_inj (st + 40#64) j S.size (by omega) (by omega) (by omega)),
          List.getElem_append_left hjl]
        exact hK j hjl
      · have hjeq : j = S.size := by omega
        subst hjeq
        rw [hm, if_pos hl, List.getElem_append_right (by omega)]
        simp only [show S.size - S.buf.length = 0 by omega, List.getElem_singleton]
        exact load_putByte_same _ _ _ _ _ (hdom _ hl)
    · have hbuf : (put cap S z).buf = S.buf := by simp [put, hl]
      simp only [hbuf] at hj ⊢
      rw [hm, if_neg hl]; exact hK j hj
  · intro j hj
    rw [hma, hbe]
    by_cases hl : S.size < cap
    · rw [hother _ (Ne.symm (hsep S.size j hl hj))]; exact hC j hj
    · rw [hm, if_neg hl]; exact hC j hj
  · intro a ha
    by_cases hl : S.size < cap
    · exact hother a (ha _ hl)
    · rw [hm, if_neg hl]
  · intro w hw
    rw [hm]; split
    · rename_i hl; simp only [putByte]; rw [if_neg (Ne.symm (hw _ hl))]
    · rfl

/-- Holding a byte when the plan says so. -/
theorem putIf_run (o : Oracle σ) (cap : Nat) (hcap : cap < 2 ^ 62)
    (s : PancakeState σ) (st p : Word)
    (S : BlockState) (flag : String) (f : Bool) (e : PancakeExp) (z : Byte) (q : List Byte)
    (hS : BFits cap S) (hK : Kept s st S.buf) (hC : Chunk s p q)
    (hdom : ∀ j, j < cap → s.memaddrs (byteAlign (st + 40#64 + BitVec.ofNat 64 j)) = true)
    (hsep : ∀ j j', j < cap → j' < q.length →
      st + 40#64 + BitVec.ofNat 64 j ≠ p + BitVec.ofNat 64 j')
    (hflag : s.locals flag = some (bw f)) (hst : s.locals "blk" = some st)
    (hsize : s.locals "size" = some (BitVec.ofNat 64 S.size))
    (he : eval s e = some (z.setWidth 64)) :
    ∃ s', PancakeSem o (.cond (x flag) (putP cap e) .skip) s = (none, s') ∧
      s'.locals "size" = some (BitVec.ofNat 64 (putIf cap f S z).size) ∧
      (∀ v, v ≠ "size" → s'.locals v = s.locals v) ∧
      Kept s' st (putIf cap f S z).buf ∧ Chunk s' p q ∧ BFits cap (putIf cap f S z) ∧
      s'.memaddrs = s.memaddrs ∧ s'.be = s.be ∧ s'.clock = s.clock ∧ s'.ffi = s.ffi ∧
      s'.baseAddr = s.baseAddr ∧
      (∀ a, (∀ j, j < cap → a ≠ st + 40#64 + BitVec.ofNat 64 j) →
        memLoadByte s'.memory s.memaddrs s.be a = memLoadByte s.memory s.memaddrs s.be a) ∧
      (∀ w, (∀ j, j < cap → byteAlign (st + 40#64 + BitVec.ofNat 64 j) ≠ w) →
        s'.memory w = s.memory w) := by
  cases f
  · refine ⟨s, ?_, by simpa [putIf] using hsize, fun _ _ => rfl, by simpa [putIf] using hK, hC,
      by simpa [putIf] using hS, rfl, rfl, rfl, rfl, rfl, fun _ _ => rfl, fun _ _ => rfl⟩
    rw [sem_cond o (show eval s (x flag) = some 0#64 by simp [eval, x, hflag, bw])]
    simp [PancakeSem]
  · obtain ⟨s', hrun, hsz', hfr', hm', hma', hbe', hclk', hffi', hba'⟩ :=
      putP_run o cap hcap s st S e z hS hst hsize he (fun h => hdom _ h)
    obtain ⟨hK', hC', hby', hw'⟩ :=
      kept_after_put cap hcap s s' st p S z q hS hK hC hdom hsep hm' hma' hbe'
    refine ⟨s', ?_, by simpa [putIf] using hsz', hfr', by simpa [putIf] using hK', hC',
      by simpa [putIf] using bfits_put cap S z hS, hma', hbe', hclk', hffi', hba', hby', hw'⟩
    rw [sem_cond o (show eval s (x flag) = some 1#64 by simp [eval, x, hflag, bw])]
    simpa using hrun

/-! ### One byte of a block -/

/-- The locals of the block loop: the arguments, the framer's state `S`, and the verdict so far. -/
structure BlockLocals (s : PancakeState σ) (st p nw : Word) (i : Nat) (S : BlockState)
    (kind held : Word) : Prop where
  st : s.locals "blk" = some st
  p : s.locals "p" = some p
  n : s.locals "n" = some nw
  i : s.locals "i" = some (BitVec.ofNat 64 i)
  ph : s.locals "ph" = some (BitVec.ofNat 64 (phaseCode S.phase))
  bad : s.locals "bad" = some (bw S.bad)
  size : s.locals "size" = some (BitVec.ofNat 64 S.size)
  kind : s.locals "kind" = some kind
  held : s.locals "held" = some held
  b : ∃ w, s.locals "b" = some w
  pre : ∃ w, s.locals "pre" = some w
  post : ∃ w, s.locals "post" = some w

def kindB : Option BlockResult → Word
  | none => 0#64
  | some r => BitVec.ofNat 64 (blockCode r.kind)

def heldB (w : Word) : Option BlockResult → Word
  | none => w
  | some r => BitVec.ofNat 64 r.held.length

def blockNames : List String := ["b", "i", "pre", "post", "ph", "bad", "size", "kind", "held"]

theorem heldLen_eq (cap : Nat) (S : BlockState) (hS : BFits cap S) :
    heldLen cap S = (result cap S).held.length := by
  obtain ⟨hb, hs⟩ := hS
  unfold heldLen result
  split
  · rfl
  · split
    · rfl
    · simp only; omega

theorem result_prefix (cap : Nat) (S : BlockState) : (result cap S).held <+: S.buf := by
  unfold result
  split
  · exact List.nil_prefix
  · split
    · exact List.nil_prefix
    · exact List.prefix_refl _

/-- **One byte of the block loop is one step of the block framer.** -/
theorem blockBody_run (o : Oracle σ) (cap : Nat) (hcap : cap < 2 ^ 62)
    (s : PancakeState σ) (st p nw : Word) (q : List Byte) (i : Nat) (S : BlockState) (held0 : Word)
    (hS : BFits cap S) (hi : i < q.length)
    (hL : BlockLocals s st p nw i S 0#64 held0) (hK : Kept s st S.buf) (hC : Chunk s p q)
    (hdom : ∀ j, j < cap → s.memaddrs (byteAlign (st + 40#64 + BitVec.ofNat 64 j)) = true)
    (hsep : ∀ j j', j < cap → j' < q.length →
      st + 40#64 + BitVec.ofNat 64 j ≠ p + BitVec.ofNat 64 j') :
    ∃ s2, PancakeSem o (blockBodyP cap) (decClock s) = (none, s2) ∧ s2.clock = s.clock - 1 ∧
      BlockLocals s2 st p nw (i + 1) (blockStep cap S q[i]).1 (kindB (blockStep cap S q[i]).2)
        (heldB held0 (blockStep cap S q[i]).2) ∧
      Kept s2 st (if (blockStep cap S q[i]).2.isSome then S.buf else (blockStep cap S q[i]).1.buf) ∧
      Chunk s2 p q ∧ s2.memaddrs = s.memaddrs ∧ s2.be = s.be ∧ s2.ffi = s.ffi ∧
      s2.baseAddr = s.baseAddr ∧
      (∀ a, (∀ j, j < cap → a ≠ st + 40#64 + BitVec.ofNat 64 j) →
        memLoadByte s2.memory s.memaddrs s.be a = memLoadByte s.memory s.memaddrs s.be a) ∧
      (∀ w, (∀ j, j < cap → byteAlign (st + 40#64 + BitVec.ofNat 64 j) ≠ w) →
        s2.memory w = s.memory w) ∧
      (∀ v, v ∉ blockNames → s2.locals v = s.locals v) := by
  obtain ⟨hst, hp, hn, hiL, hph, hbad, hsize, hkind, hheld, ⟨wb, hwb⟩, ⟨wpr, hwpr⟩,
      ⟨wpo, hwpo⟩⟩ := hL
  obtain ⟨y, hydef⟩ : ∃ y, q[i] = y := ⟨_, rfl⟩
  rw [hydef]
  have hload : memLoadByte s.memory s.memaddrs s.be (p + BitVec.ofNat 64 i) = some y := by
    rw [← hydef]; exact hC i hi
  -- the byte, the position, and the plan cleared
  let s1 : PancakeState σ := { decClock s with locals := setLocal s.locals "b" (y.setWidth 64) }
  let s2 : PancakeState σ := { s1 with locals := setLocal s1.locals "i" (BitVec.ofNat 64 (i + 1)) }
  let s3 : PancakeState σ := { s2 with locals := setLocal s2.locals "pre" 0#64 }
  let s4 : PancakeState σ := { s3 with locals := setLocal s3.locals "post" 0#64 }
  have h1 : PancakeSem o (.assign "b" (.loadByte (add (x "p") (x "i")))) (decClock s) =
      (none, s1) := by
    apply sem_assign (old := wb)
    · simp [eval, x, add, decClock, hp, hiL, hload]
    · exact hwb
  have h2 : PancakeSem o (.assign "i" (add (x "i") (c 1))) s1 = (none, s2) := by
    apply sem_assign (old := BitVec.ofNat 64 i)
    · rw [ofNat_succ]; simp +zetaDelta [eval, x, c, add, setLocal, hiL, decClock]
    · simp +zetaDelta [setLocal, hiL]
  have h3 : PancakeSem o (set "pre" 0) s2 = (none, s3) := by
    apply sem_assign (old := wpr)
    · rfl
    · simp +zetaDelta [setLocal, hwpr]
  have h4 : PancakeSem o (set "post" 0) s3 = (none, s4) := by
    apply sem_assign (old := wpo)
    · rfl
    · simp +zetaDelta [setLocal, hwpo]
  have l4 : ∀ v, v ≠ "b" → v ≠ "i" → v ≠ "pre" → v ≠ "post" → s4.locals v = s.locals v := by
    intro v h1 h2 h3 h4; simp +zetaDelta [setLocal, h1, h2, h3, h4]
  have hin : PhaseIn s4 S y :=
    ⟨by rw [l4 _ (by decide) (by decide) (by decide) (by decide)]; exact hph,
     by rw [l4 _ (by decide) (by decide) (by decide) (by decide)]; exact hbad,
     by rw [l4 _ (by decide) (by decide) (by decide) (by decide)]; exact hsize,
     by simp +zetaDelta [setLocal], by simp +zetaDelta [setLocal], by simp +zetaDelta [setLocal],
     ⟨_, by rw [l4 _ (by decide) (by decide) (by decide) (by decide)]; exact hkind⟩,
     ⟨_, by rw [l4 _ (by decide) (by decide) (by decide) (by decide)]; exact hheld⟩⟩
  obtain ⟨s5, hrun5, hm5, hma5, hbe5, hclk5, hffi5, hba5, hfr5, hout5⟩ :=
    phase_run o cap hcap s4 S y hS.2 hin
  have hstep := blockStep_plan cap S y
  have hbody : ∀ s8, PancakeSem o (.seq (.cond (x "pre") (putP cap (c 13)) .skip)
      (.seq (.cond (x "post") (putP cap (x "b")) .skip) (.cond (x "kind") (set "size" 0) .skip)))
      s5 = (none, s8) → PancakeSem o (blockBodyP cap) (decClock s) = (none, s8) := by
    intro s8 h8
    exact seq_run o h1 rfl (seq_run o h2 rfl (seq_run o h3 rfl (seq_run o h4 rfl
      (seq_run o hrun5 hclk5 h8))))
  have n7 : ∀ v, v ∉ blockNames → v ≠ "b" ∧ v ≠ "i" ∧ v ≠ "pre" ∧ v ≠ "post" ∧ v ≠ "ph" ∧
      v ≠ "bad" ∧ v ≠ "size" ∧ v ≠ "kind" ∧ v ≠ "held" := by
    intro v hv; simp only [blockNames, List.mem_cons, List.not_mem_nil, or_false, not_or] at hv
    exact hv
  have s5eq : ∀ v, v ∉ blockNames → s5.locals v = s.locals v := by
    intro v hv; obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9⟩ := n7 v hv
    rw [hfr5 v a3 a4 a5 a6 a7 a8 a9, l4 v a1 a2 a3 a4]
  have hK5 : Kept s5 st S.buf := by
    intro j hj; rw [hm5, hma5, hbe5]; exact hK j hj
  have hC5 : Chunk s5 p q := by
    intro j hj; rw [hm5, hma5, hbe5]; exact hC j hj
  have hi5 : s5.locals "i" = some (BitVec.ofNat 64 (i + 1)) := by
    rw [hfr5 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    simp +zetaDelta [setLocal]
  have hb5 : s5.locals "b" = some (y.setWidth 64) := by
    rw [hfr5 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    simp +zetaDelta [setLocal]
  have hst5 : s5.locals "blk" = some st := by rw [s5eq _ (by decide)]; exact hst
  by_cases hend : (plan S y).ends
  · -- the block ends here: nothing is held, the verdict is given
    rw [if_pos hend] at hout5
    obtain ⟨p0, q0, ph0, b0, sz0, k0, hd0⟩ := hout5
    have hr : blockStep cap S y = (.fresh, some (result cap S)) := by rw [hstep, if_pos hend]
    have hcode : (BitVec.ofNat 64 (blockCode (result cap S).kind) : Word) ≠ 0 := by
      cases (result cap S).kind <;> decide
    let s8 : PancakeState σ := { s5 with locals := setLocal s5.locals "size" 0#64 }
    have hc1 : PancakeSem o (.cond (x "pre") (putP cap (c 13)) .skip) s5 = (none, s5) := by
      rw [sem_cond o (show eval s5 (x "pre") = some 0#64 by simp [eval, x, p0]), if_neg (by decide)]
      exact sem_skip o s5
    have hc2 : PancakeSem o (.cond (x "post") (putP cap (x "b")) .skip) s5 = (none, s5) := by
      rw [sem_cond o (show eval s5 (x "post") = some 0#64 by simp [eval, x, q0]),
          if_neg (by decide)]
      exact sem_skip o s5
    have hc3 : PancakeSem o (.cond (x "kind") (set "size" 0) .skip) s5 = (none, s8) := by
      rw [sem_cond o
          (show eval s5 (x "kind") = some (BitVec.ofNat 64 (blockCode (result cap S).kind))
        by simp [eval, x, k0]), if_pos hcode]
      exact sem_assign (old := BitVec.ofNat 64 S.size) rfl
          (by rw [sz0, l4 _ (by decide) (by decide) (by decide) (by decide)]; exact hsize)
    have e8 : ∀ v, v ≠ "size" → s8.locals v = s5.locals v := by
      intro v hv; simp [s8, setLocal, hv]
    rw [hr]
    refine ⟨s8, hbody s8 (seq_run o hc1 rfl (seq_run o hc2 rfl hc3)),
      by rw [show s8.clock = s5.clock from rfl, hclk5]; rfl,
      ?_, ?_, ?_, by rw [show s8.memaddrs = s5.memaddrs from rfl, hma5]; rfl,
      by rw [show s8.be = s5.be from rfl, hbe5]; rfl,
      by rw [show s8.ffi = s5.ffi from rfl, hffi5]; rfl,
      by rw [show s8.baseAddr = s5.baseAddr from rfl, hba5]; rfl, ?_, ?_, ?_⟩
    · refine ⟨by rw [e8 _ (by decide)]; exact hst5,
        by rw [e8 _ (by decide), s5eq _ (by decide)]; exact hp,
        by rw [e8 _ (by decide), s5eq _ (by decide)]; exact hn, by rw [e8 _ (by decide)]; exact hi5,
        by rw [e8 _ (by decide)]; simpa [phaseCode, BlockState.fresh] using ph0,
        by rw [e8 _ (by decide)]; simpa [bw, BlockState.fresh] using b0,
        by simp [s8, setLocal, BlockState.fresh],
        by rw [e8 _ (by decide)]; simpa [kindB] using k0, ?_,
        ⟨_, by rw [e8 _ (by decide)]; exact hb5⟩, ⟨_, by rw [e8 _ (by decide)]; exact p0⟩,
        ⟨_, by rw [e8 _ (by decide)]; exact q0⟩⟩
      rw [e8 _ (by decide), hd0, heldLen_eq cap S hS]; rfl
    · simpa using hK5
    · exact hC5
    · intro a _; rw [show s8.memory = s5.memory from rfl, hm5]; rfl
    · intro w _; rw [show s8.memory = s5.memory from rfl, hm5]; rfl
    · intro v hv
      obtain ⟨_, _, _, _, _, _, a7, _, _⟩ := n7 v hv
      rw [e8 v a7]; exact s5eq v hv
  · -- the block goes on: the planned bytes are held
    rw [if_neg hend] at hout5
    obtain ⟨hpre5, hpost5, hph5, hbad5, hsz5, hk5, hhd5⟩ := hout5
    have hr : blockStep cap S y =
        ((putIf cap (plan S y).post (putIf cap (plan S y).pre S CR) y).at (plan S y).phase
          (plan S y).bad, none) := by rw [hstep, if_neg hend]
    have hsize5 : s5.locals "size" = some (BitVec.ofNat 64 S.size) := by
      rw [hsz5, l4 _ (by decide) (by decide) (by decide) (by decide)]; exact hsize
    have hdom5 :
        ∀ j, j < cap → s5.memaddrs (byteAlign (st + 40#64 + BitVec.ofNat 64 j)) = true := by
      intro j hj; rw [hma5]; exact hdom j hj
    obtain ⟨s6, hrun6, hsz6, hfr6, hK6, hC6, hS6, hma6, hbe6, hclk6, hffi6, hba6, hby6, hw6⟩ :=
      putIf_run o cap hcap s5 st p S "pre" (plan S y).pre (c 13) CR q hS hK5 hC5 hdom5 hsep hpre5
        hst5 hsize5 (by simp [eval, c, wCR])
    have hdom6 :
        ∀ j, j < cap → s6.memaddrs (byteAlign (st + 40#64 + BitVec.ofNat 64 j)) = true := by
      intro j hj; rw [hma6]; exact hdom5 j hj
    obtain ⟨s7, hrun7, hsz7, hfr7, hK7, hC7, hS7, hma7, hbe7, hclk7, hffi7, hba7, hby7, hw7⟩ :=
      putIf_run o cap hcap s6 st p (putIf cap (plan S y).pre S CR) "post"
          (plan S y).post (x "b") y q
        hS6 hK6 hC6 hdom6 hsep (by rw [hfr6 _ (by decide)]; exact hpost5)
        (by rw [hfr6 _ (by decide)]; exact hst5) hsz6
        (by simp [eval, x]; rw [hfr6 _ (by decide)]; exact hb5)
    have hk7 : s7.locals "kind" = some 0#64 := by
      rw [hfr7 _ (by decide), hfr6 _ (by decide), hk5, l4 _ (by decide) (by decide) (by decide)
        (by decide)]; exact hkind
    have hc3 : PancakeSem o (.cond (x "kind") (set "size" 0) .skip) s7 = (none, s7) := by
      rw [sem_cond o (show eval s7 (x "kind") = some 0#64 by simp [eval, x, hk7]),
          if_neg (by decide)]
      exact sem_skip o s7
    have h7 : PancakeSem o (.seq (.cond (x "pre") (putP cap (c 13)) .skip)
        (.seq (.cond (x "post") (putP cap (x "b")) .skip) (.cond (x "kind") (set "size" 0) .skip)))
        s5 = (none, s7) :=
      seq_run o hrun6 hclk6 (seq_run o hrun7 hclk7 hc3)
    have e7 : ∀ v, v ≠ "size" → s7.locals v = s5.locals v := by
      intro v hv; rw [hfr7 v hv, hfr6 v hv]
    rw [hr]
    refine ⟨s7, hbody s7 h7, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hclk7, hclk6, hclk5]; rfl
    · refine ⟨by rw [e7 _ (by decide)]; exact hst5,
        by rw [e7 _ (by decide), s5eq _ (by decide)]; exact hp,
        by rw [e7 _ (by decide), s5eq _ (by decide)]; exact hn, by rw [e7 _ (by decide)]; exact hi5,
        by rw [e7 _ (by decide)]; simpa [BlockState.at, putIf_phase] using hph5,
        by rw [e7 _ (by decide)]; simpa [BlockState.at] using hbad5,
        by simpa [BlockState.at] using hsz7,
        by rw [e7 _ (by decide), hk5, l4 _ (by decide) (by decide) (by decide) (by decide)]
           simpa [kindB] using hkind,
        by rw [e7 _ (by decide), hhd5, l4 _ (by decide) (by decide) (by decide) (by decide)]
           simpa [heldB] using hheld,
        ⟨_, by rw [e7 _ (by decide)]; exact hb5⟩, ⟨_, by rw [e7 _ (by decide)]; exact hpre5⟩,
        ⟨_, by rw [e7 _ (by decide)]; exact hpost5⟩⟩
    · simpa [BlockState.at] using hK7
    · exact hC7
    · rw [hma7, hma6, hma5]; rfl
    · rw [hbe7, hbe6, hbe5]; rfl
    · rw [hffi7, hffi6, hffi5]; rfl
    · rw [hba7, hba6, hba5]; rfl
    · intro a ha
      show memLoadByte s7.memory s4.memaddrs s4.be a = memLoadByte s4.memory s4.memaddrs s4.be a
      have e1 := hby7 a ha
      have e2 := hby6 a ha
      rw [hma6, hbe6] at e1
      rw [hma5, hbe5] at e1 e2
      rw [e1, e2, hm5]
    · intro w hw; rw [hw7 w hw, hw6 w hw, hm5]; rfl
    · intro v hv
      obtain ⟨_, _, _, _, _, _, a7, _, _⟩ := n7 v hv
      rw [e7 v a7]; exact s5eq v hv

/-! ### The block loop -/

theorem bfits_step (cap : Nat) (S : BlockState) (y : Byte) (h : BFits cap S) :
    BFits cap (blockStep cap S y).1 := by
  rw [blockStep_plan]
  split
  · exact ⟨by simp [BlockState.fresh], by simp [BlockState.fresh]⟩
  · have := bfits_putIf cap (plan S y).post _ y (bfits_putIf cap (plan S y).pre S CR h)
    exact this

/-- The bytes kept after reading: the block's, once it ended, or the block so far. -/
def keptOfB (f : Nat × BlockState × Option BlockResult) : List Byte :=
  match f.2.2 with
  | some r => r.held
  | none => f.2.1.buf

/-- After `k` bytes of the block loop. -/
structure BlockInv (cap : Nat) (s0 s : PancakeState σ) (st p : Word) (q : List Byte) (i0 : Nat)
    (S : BlockState) (held0 : Word) (k : Nat) : Prop where
  loc : BlockLocals s st p (BitVec.ofNat 64 q.length) (i0 + k)
    (feedBlock cap S ((q.drop i0).take k)).2.1 (kindB (feedBlock cap S ((q.drop i0).take k)).2.2)
    (heldB held0 (feedBlock cap S ((q.drop i0).take k)).2.2)
  kept : Kept s st (keptOfB (feedBlock cap S ((q.drop i0).take k)))
  chunk : Chunk s p q
  ma : s.memaddrs = s0.memaddrs
  be : s.be = s0.be
  ffi : s.ffi = s0.ffi
  base : s.baseAddr = s0.baseAddr
  bytes : ∀ a, (∀ j, j < cap → a ≠ st + 40#64 + BitVec.ofNat 64 j) →
    memLoadByte s.memory s0.memaddrs s0.be a = memLoadByte s0.memory s0.memaddrs s0.be a
  words : ∀ w, (∀ j, j < cap → byteAlign (st + 40#64 + BitVec.ofNat 64 j) ≠ w) →
    s.memory w = s0.memory w
  names : ∀ v, v ∉ blockNames → s.locals v = s0.locals v
  fits : BFits cap (feedBlock cap S ((q.drop i0).take k)).2.1

/-- **The block loop is the block framer's call.** -/
theorem blockLoop_run (o : Oracle σ) (cap : Nat) (hcap : cap < 2 ^ 62)
    (s0 : PancakeState σ) (st p : Word) (q : List Byte) (i0 : Nat) (S : BlockState) (held0 : Word)
    (hS : BFits cap S) (hi0 : i0 ≤ q.length) (hq : q.length < 2 ^ 62)
    (hL : BlockLocals s0 st p (BitVec.ofNat 64 q.length) i0 S 0#64 held0) (hK : Kept s0 st S.buf)
    (hC : Chunk s0 p q)
    (hdom : ∀ j, j < cap → s0.memaddrs (byteAlign (st + 40#64 + BitVec.ofNat 64 j)) = true)
    (hsep : ∀ j j', j < cap → j' < q.length →
      st + 40#64 + BitVec.ofNat 64 j ≠ p + BitVec.ofNat 64 j')
    :
    ((feedBlock cap S (q.drop i0)).1 ≤ s0.clock →
      ∃ s', PancakeSem o (.while_ lineGuardP (blockBodyP cap)) s0 = (none, s') ∧
        s'.clock + (feedBlock cap S (q.drop i0)).1 = s0.clock ∧
        BlockInv cap s0 s' st p q i0 S held0 (feedBlock cap S (q.drop i0)).1) ∧
    (s0.clock < (feedBlock cap S (q.drop i0)).1 →
      ∃ t, PancakeSem o (.while_ lineGuardP (blockBodyP cap)) s0 = (some .timeout, t)) := by
  let K := (feedBlock cap S (q.drop i0)).1
  have hKle : K ≤ q.length - i0 := by
    have := feedBlock_len cap S (q.drop i0); simpa using this
  have hlt : ∀ a b : Nat, a < 2 ^ 62 → b < 2 ^ 62 →
      signedLt (BitVec.ofNat 64 a) (BitVec.ofNat 64 b) = decide (a < b) :=
    fun a b ha hb => signedLt_ofNat a b (by omega) (by omega)
  let I : Nat → PancakeState σ → Prop := fun rem s =>
    rem ≤ K ∧ BlockInv cap s0 s st p q i0 S held0 (K - rem)
  have hg : ∀ rem s, I rem s → eval s lineGuardP = some (if rem = 0 then (0 : Word) else 1) := by
        intro rem s ⟨hrem, hI⟩
        have hloc := hI.loc
        by_cases h0 : rem = 0
        · subst h0
          simp only [Nat.sub_zero] at hloc ⊢
          rw [show K = (feedBlock cap S (q.drop i0)).1 from rfl, feedBlock_take] at hloc
          rcases hout : (feedBlock cap S (q.drop i0)).2.2 with _ | r
          · have hend : K = q.length - i0 := by
              by_cases hs : K < (q.drop i0).length
              · have := feedBlock_short cap S (q.drop i0) hs; rw [hout] at this; simp at this
              · simp at hs; omega
            rw [hout] at hloc
            have hg : signedLt (BitVec.ofNat 64 (i0 + K)) (BitVec.ofNat 64 q.length) = false := by
              rw [hlt _ _ (by omega) hq]; simp; omega
            simp [lineGuardP, eval, x, c, hloc.i, hloc.n, hloc.kind, kindB]
            simp only [K] at hg; simp [hg]
          · rw [hout] at hloc
            have hcode : (BitVec.ofNat 64 (blockCode r.kind) : Word) ≠ 0#64 := by
              cases r.kind <;> decide
            simp [lineGuardP, eval, x, c, hloc.i, hloc.n, hloc.kind, kindB, hcode]
        · have hk : K - rem < K := by omega
          obtain ⟨_, hquiet⟩ := feedBlock_quiet cap S (q.drop i0) (K - rem) hk
          rw [hquiet] at hloc
          have hg : signedLt (BitVec.ofNat 64 (i0 + (K - rem)))
              (BitVec.ofNat 64 q.length) = true := by
            rw [hlt _ _ (by omega) hq]; simp; omega
          simp [lineGuardP, eval, x, c, hloc.i, hloc.n, hloc.kind, kindB, h0, hg]
  have hb : ∀ rem s, I (rem + 1) s →
      ∃ s2, PancakeSem o (blockBodyP cap) (decClock s) = (none, s2) ∧ I rem s2 ∧
        s2.clock = s.clock - 1 := by
        intro rem s ⟨hrem, hI⟩
        have hk : K - (rem + 1) < K := by omega
        obtain ⟨k, hkdef⟩ : ∃ k, k = K - (rem + 1) := ⟨_, rfl⟩
        rw [← hkdef] at hk hI
        obtain ⟨hklen, hquiet⟩ := feedBlock_quiet cap S (q.drop i0) k hk
        have hloc := hI.loc
        rw [hquiet] at hloc
        have hkq : i0 + k < q.length := by omega
        have hkq' : k < (q.drop i0).length := by simp; omega
        have hkept := hI.kept
        simp only [keptOfB, hquiet] at hkept
        obtain ⟨s2, hrun2, hclk2, hL2, hK2, hC2, hma2, hbe2, hffi2, hba2, hby2, hw2, hn2⟩ :=
          blockBody_run o cap hcap s st p (BitVec.ofNat 64 q.length) q (i0 + k)
            (feedBlock cap S ((q.drop i0).take k)).2.1 held0 hI.fits hkq
            (by simpa [kindB, heldB] using hloc) hkept hI.chunk
            (fun j hj => by rw [hI.ma]; exact hdom j hj) hsep
        have hy : q[i0 + k] = (q.drop i0)[k] := by simp
        have hfeed := feedBlock_take_succ cap S (q.drop i0) k hk hkq'
        refine ⟨s2, hrun2, ⟨by omega, ?_⟩, hclk2⟩
        have hk1 : K - rem = k + 1 := by omega
        rw [hk1]
        refine ⟨?_, ?_, hC2, by rw [hma2, hI.ma], by rw [hbe2, hI.be], by rw [hffi2, hI.ffi],
          by rw [hba2, hI.base], ?_, ?_, ?_, ?_⟩
        · rw [hfeed]; simp only
          rw [← hy, show i0 + (k + 1) = i0 + k + 1 by omega]
          exact hL2
        · rw [hfeed]; simp only [keptOfB]
          rw [← hy]
          rcases h : blockStep cap (feedBlock cap S (List.take k (List.drop i0 q))).2.1
              q[i0 + k] with
            ⟨S', _ | r⟩
          · rw [h] at hK2; simpa using hK2
          · rw [h] at hK2
            simp only [Option.isSome_some, if_true] at hK2
            have := (blockStep_some cap _ _ r (by rw [h])).1
            rw [this]; exact kept_prefix hK2 (result_prefix _ _)
        · intro a ha
          rw [← hI.ma, ← hI.be, hby2 a ha, hI.ma, hI.be]; exact hI.bytes a ha
        · intro w hw; rw [hw2 w hw]; exact hI.words w hw
        · intro v hv; rw [hn2 v hv]; exact hI.names v hv
        · rw [hfeed, ← hy]; exact bfits_step cap _ _ hI.fits
  have hI0 : I K s0 :=
      ⟨Nat.le_refl _, by
        rw [Nat.sub_self]
        exact ⟨by simpa [feedBlock, kindB, heldB] using hL,
            by simpa [feedBlock, keptOfB] using hK, hC,
          rfl, rfl, rfl, rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl,
          by simpa [feedBlock] using hS⟩⟩
  refine ⟨fun hk => ?_,
      fun hk => while_inv_timeout o lineGuardP (blockBodyP cap) I hg hb K s0 hI0 hk⟩
  obtain ⟨s', hrun, ⟨_, hinv⟩, hclk'⟩ :=
    while_inv_cond_exact o lineGuardP (blockBodyP cap) I hg hb K s0 hI0 hk
  exact ⟨s', hrun, hclk', by simpa using hinv⟩

/-! ### The block run -/

def blockStoresP (k : PancakeProg) : PancakeProg :=
  .seq (.store (x "blk") (x "ph"))
  (.seq (.store (add (x "blk") (c 8)) (x "bad"))
  (.seq (.store (add (x "blk") (c 16)) (x "size"))
  (.seq (.store (add (x "blk") (c 24)) (x "kind"))
  (.seq (.store (add (x "blk") (c 32)) (x "held")) k))))

def blockFragP (cap : Nat) (k : PancakeProg) : PancakeProg :=
  .seq (.assign "ph" (.loadWord (x "blk")))
  (.seq (.assign "bad" (.loadWord (add (x "blk") (c 8))))
  (.seq (.assign "size" (.loadWord (add (x "blk") (c 16))))
  (.seq (set "kind" 0)
  (.seq (set "held" 0)
  (.seq (.while_ lineGuardP (blockBodyP cap)) (blockStoresP k))))))

def blockRunP (cap : Nat) : PancakeProg :=
  .dec "ph" (c 0) (.dec "bad" (c 0) (.dec "size" (c 0) (.dec "kind" (c 0) (.dec "held" (c 0)
    (.dec "b" (c 0) (.dec "pre" (c 0) (.dec "post" (c 0) (blockFragP cap (.ret (x "i"))))))))))

theorem blockRun_lower (cap : Nat) :
    Lower.lowerStmtsFold (blockRun cap) = some (blockRunP cap) := rfl

theorem blockFrag_lower (cap : Nat) (x0 : PStmt) (rest : List PStmt) (r : PancakeProg)
    (h : Lower.lowerStmtsFold (x0 :: rest) = some r) :
    Lower.lowerStmtsFold (blockFrag cap ++ x0 :: rest) = some (blockFragP cap r) := by
  simp only [blockFrag, blockLoop, List.cons_append, List.nil_append, Lower.lowerStmtsFold,
    Lower.lowerStmt1, Lower.lowerExp, h, v, n, eAdd]
  rfl

theorem frameBlock_lower (name : String) (cap : Nat) :
    Lower.lower (frameBlock name cap) = some (guardP (blockRunP cap)) := rfl

/-- The block framer's state is in memory at `st`. -/
def HoldsB (s : PancakeState σ) (st : Word) (S : BlockState) : Prop :=
  s.memory st = BitVec.ofNat 64 (phaseCode S.phase) ∧ s.memory (st + 8#64) = bw S.bad ∧
    s.memory (st + 16#64) = BitVec.ofNat 64 S.size ∧ Kept s st S.buf

/-- The block's verdict is in memory at `st + 24`: none, or its kind, how many bytes it holds, and
those bytes from `st + 40`. -/
def ReportedB (s : PancakeState σ) (st : Word) : Option BlockResult → Prop
  | none => s.memory (st + 24#64) = 0#64
  | some r => s.memory (st + 24#64) = BitVec.ofNat 64 (blockCode r.kind) ∧
      s.memory (st + 32#64) = BitVec.ofNat 64 r.held.length ∧ Kept s st r.held

/-- A block whose first words are zero holds a fresh block framer, as `holds_zero` for lines. -/
theorem holdsB_zero (s : PancakeState σ) (st : Word) (h0 : s.memory st = 0#64)
    (h8 : s.memory (st + 8#64) = 0#64) (h16 : s.memory (st + 16#64) = 0#64) :
    HoldsB s st .fresh :=
  ⟨h0, h8, h16, fun j h => absurd h (by simp [BlockState.fresh])⟩

theorem blockStores_run (o : Oracle σ) (k : PancakeProg) (s : PancakeState σ)
    (st ph bad size kind held : Word)
    (hst : s.locals "blk" = some st) (hph : s.locals "ph" = some ph)
    (hbad : s.locals "bad" = some bad) (hsize : s.locals "size" = some size)
    (hkind : s.locals "kind" = some kind) (hheld : s.locals "held" = some held)
    (h0 : s.memaddrs st = true) (h8 : s.memaddrs (st + 8#64) = true)
    (h16 : s.memaddrs (st + 16#64) = true) (h24 : s.memaddrs (st + 24#64) = true)
    (h32 : s.memaddrs (st + 32#64) = true) :
    PancakeSem o (blockStoresP k) s =
      PancakeSem o k { s with memory := written s.memory st ph bad size kind held } := by
  simp only [blockStoresP, PancakeSem, eval, x, c, add, hst, hph, hbad, hsize, hkind, hheld,
    memStoreWord, h0, h8, h16, h24, h32, if_true, clampClock, Nat.min_self]
  rfl

/-- A call ends the block only once, and then the state is fresh. -/
theorem feedBlock_fresh (cap : Nat) (S : BlockState) (q : List Byte) (r : BlockResult)
    (h : (feedBlock cap S q).2.2 = some r) : (feedBlock cap S q).2.1 = .fresh := by
  induction q generalizing S with
  | nil => simp [feedBlock] at h
  | cons y rest ih =>
    rcases hs : blockStep cap S y with ⟨S', _ | v⟩
    · simp only [feedBlock, hs] at h ⊢; exact ih S' h
    · simp only [feedBlock, hs]
      exact (blockStep_some cap S y v (by rw [hs])).2.symm ▸ (by rw [hs])

/-- A block holds no more than its buffer. -/
theorem feedBlock_held_le (cap : Nat) (S : BlockState) (q : List Byte) (r : BlockResult)
    (hS : BFits cap S) (h : (feedBlock cap S q).2.2 = some r) : r.held.length ≤ cap := by
  induction q generalizing S with
  | nil => simp [feedBlock] at h
  | cons y rest ih =>
    rcases hs : blockStep cap S y with ⟨S', _ | v⟩
    · simp only [feedBlock, hs] at h
      exact ih S' (by have := bfits_step cap S y hS; rw [hs] at this; exact this) h
    · simp only [feedBlock, hs, Option.some.injEq] at h
      subst h
      have := (blockStep_some cap S y v (by rw [hs])).1
      subst this
      have hp := (result_prefix cap S).length_le
      have := hS.1
      omega

/-- The locals the block framer writes. -/
def blockWrites : List String := ["ph", "bad", "size", "kind", "held", "b", "pre", "post", "i"]

/-- What a block run leaves in memory, as `LineMem` says of a line run. -/
structure BlockMem (cap : Nat) (s s' : PancakeState σ) (st : Word) (S' : BlockState)
    (out : Option BlockResult) : Prop where
  holds : HoldsB s' st S'
  reported : ReportedB s' st out
  ma : s'.memaddrs = s.memaddrs
  be : s'.be = s.be
  ffi : s'.ffi = s.ffi
  base : s'.baseAddr = s.baseAddr
  bytes : ∀ a, Outside cap st a →
    memLoadByte s'.memory s.memaddrs s.be a = memLoadByte s.memory s.memaddrs s.be a
  words : ∀ w, w ≠ st → w ≠ st + 8#64 → w ≠ st + 16#64 → w ≠ st + 24#64 → w ≠ st + 32#64 →
    (∀ j, j < cap → byteAlign (st + 40#64 + BitVec.ofNat 64 j) ≠ w) → s'.memory w = s.memory w

/-- What the block framer leaves, as `LineAfter` says of the line framer. -/
structure BlockAfter (cap : Nat) (s s' : PancakeState σ) (st : Word) (i : Nat) (S' : BlockState)
    (out : Option BlockResult) : Prop where
  i : s'.locals "i" = some (BitVec.ofNat 64 i)
  locals : ∀ v, v ∉ blockWrites → s'.locals v = s.locals v
  mem : BlockMem cap s s' st S' out

/-- **The block framer is the block framer's call**, as `lineFrag_run` says of lines: it reads to
the end of the block or of the chunk. -/
theorem blockFrag_run (o : Oracle σ) (cap : Nat) (hcap : cap < 2 ^ 62)
    (s : PancakeState σ) (st p : Word) (q : List Byte) (i0 : Nat) (S : BlockState)
    (hS : BFits cap S) (hi0 : i0 ≤ q.length) (hq : q.length < 2 ^ 62)
    (hst : s.locals "blk" = some st) (hp : s.locals "p" = some p)
    (hn : s.locals "n" = some (BitVec.ofNat 64 q.length))
    (hi : s.locals "i" = some (BitVec.ofNat 64 i0))
    (hw : ∀ v, v ∈ ["ph", "bad", "size", "kind", "held", "b", "pre", "post"] →
        ∃ w, s.locals v = some w)
    (hH : HoldsB s st S) (hC : Chunk s p q) (hR : Room cap s st)
    (hal : st.toNat % 8 = 0) (hfit : st.toNat + 40 + cap ≤ 2 ^ 64)
    (hsep : ∀ j j', j < cap → j' < q.length →
      st + 40#64 + BitVec.ofNat 64 j ≠ p + BitVec.ofNat 64 j') :
    ((feedBlock cap S (q.drop i0)).1 ≤ s.clock →
      ∃ s', s'.clock = s.clock - (feedBlock cap S (q.drop i0)).1 ∧
        BlockAfter cap s s' st (i0 + (feedBlock cap S (q.drop i0)).1)
          (feedBlock cap S (q.drop i0)).2.1 (feedBlock cap S (q.drop i0)).2.2 ∧
        ∀ k, PancakeSem o (blockFragP cap k) s = PancakeSem o k s') ∧
    (s.clock < (feedBlock cap S (q.drop i0)).1 →
      ∀ k, ∃ t, PancakeSem o (blockFragP cap k) s = (some .timeout, t)) := by
  obtain ⟨hH0, hH8, hH16, hHK⟩ := hH
  obtain ⟨hR0, hR8, hR16, hR24, hR32, hRb⟩ := hR
  obtain ⟨wph, hwph⟩ := hw "ph" (by simp)
  obtain ⟨wbad, hwbad⟩ := hw "bad" (by simp)
  obtain ⟨wsize, hwsize⟩ := hw "size" (by simp)
  obtain ⟨wkind, hwkind⟩ := hw "kind" (by simp)
  obtain ⟨wheld, hwheld⟩ := hw "held" (by simp)
  obtain ⟨wb, hwb⟩ := hw "b" (by simp)
  obtain ⟨wpre, hwpre⟩ := hw "pre" (by simp)
  obtain ⟨wpost, hwpost⟩ := hw "post" (by simp)
  -- the state read into the working names
  let s1 : PancakeState σ :=
    { s with locals := setLocal s.locals "ph" (BitVec.ofNat 64 (phaseCode S.phase)) }
  let s2 : PancakeState σ := { s1 with locals := setLocal s1.locals "bad" (bw S.bad) }
  let s3 : PancakeState σ :=
    { s2 with locals := setLocal s2.locals "size" (BitVec.ofNat 64 S.size) }
  let s4 : PancakeState σ := { s3 with locals := setLocal s3.locals "kind" (BitVec.ofNat 64 0) }
  let s5 : PancakeState σ := { s4 with locals := setLocal s4.locals "held" (BitVec.ofNat 64 0) }
  have h1 : PancakeSem o (.assign "ph" (.loadWord (x "blk"))) s = (none, s1) :=
    sem_assign (old := wph) (by simp [eval, x, hst, hR0, hH0]) hwph
  have h2 : PancakeSem o (.assign "bad" (.loadWord (add (x "blk") (c 8)))) s1 = (none, s2) :=
    sem_assign (old := wbad) (by simp [eval, x, c, add, s1, setLocal, hst, hR8, hH8])
      (by simp [s1, setLocal, hwbad])
  have h3 : PancakeSem o (.assign "size" (.loadWord (add (x "blk") (c 16)))) s2 = (none, s3) :=
    sem_assign (old := wsize) (by simp [eval, x, c, add, s2, s1, setLocal, hst, hR16, hH16])
      (by simp [s2, s1, setLocal, hwsize])
  have h4 : PancakeSem o (set "kind" 0) s3 = (none, s4) :=
    sem_assign (old := wkind) rfl (by simp [s3, s2, s1, setLocal, hwkind])
  have h5 : PancakeSem o (set "held" 0) s4 = (none, s5) :=
    sem_assign (old := wheld) rfl (by simp [s4, s3, s2, s1, setLocal, hwheld])
  have l5 : ∀ v, v ≠ "ph" → v ≠ "bad" → v ≠ "size" → v ≠ "kind" → v ≠ "held" →
      s5.locals v = s.locals v := by
    intro v a1 a2 a3 a4 a5; simp [s5, s4, s3, s2, s1, setLocal, a1, a2, a3, a4, a5]
  have hloc5 : BlockLocals s5 st p (BitVec.ofNat 64 q.length) i0 S 0#64 0#64 :=
    ⟨by rw [l5 _ (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hst,
     by rw [l5 _ (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hp,
     by rw [l5 _ (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hn,
     by rw [l5 _ (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hi,
     by simp [s5, s4, s3, s2, s1, setLocal], by simp [s5, s4, s3, s2, setLocal],
     by simp [s5, s4, s3, setLocal], by simp [s5, s4, setLocal],
     by simp [s5, setLocal],
     ⟨wb, by rw [l5 _ (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hwb⟩,
     ⟨wpre, by rw [l5 _ (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hwpre⟩,
     ⟨wpost, by
       rw [l5 _ (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hwpost⟩⟩
  have hreads : ∀ k, PancakeSem o (blockFragP cap k) s =
      PancakeSem o (.seq (.while_ lineGuardP (blockBodyP cap)) (blockStoresP k)) s5 := by
    intro k
    unfold blockFragP
    rw [seq_into o h1 (Nat.le_refl _), seq_into o h2 (Nat.le_refl _), seq_into o h3 (Nat.le_refl _),
      seq_into o h4 (Nat.le_refl _), seq_into o h5 (Nat.le_refl _)]
  obtain ⟨hnorm, htime⟩ :=
    blockLoop_run o cap hcap s5 st p q i0 S 0#64 hS hi0 hq hloc5 hHK hC hRb hsep
  refine ⟨fun hk => ?_, fun hk k => ?_⟩
  case refine_2 =>
    obtain ⟨t, ht⟩ := htime hk
    exact ⟨_, (hreads k).trans (seq_stop o ht)⟩
  obtain ⟨s6, hrun6, hclk6, hI⟩ := hnorm hk
  have hfeed := feedBlock_take cap S (q.drop i0)
  have hloc6 := hI.loc
  have hkept6 := hI.kept
  simp only [hfeed] at hloc6 hkept6
  have hma6 : s6.memaddrs = s.memaddrs := hI.ma
  let m7 := written s6.memory st
      (BitVec.ofNat 64 (phaseCode (feedBlock cap S (q.drop i0)).2.1.phase))
    (bw (feedBlock cap S (q.drop i0)).2.1.bad)
        (BitVec.ofNat 64 (feedBlock cap S (q.drop i0)).2.1.size)
    (kindB (feedBlock cap S (q.drop i0)).2.2) (heldB 0#64 (feedBlock cap S (q.drop i0)).2.2)
  obtain ⟨s7, hs7⟩ : ∃ s7 : PancakeState σ, s7 = { s6 with memory := m7 } := ⟨_, rfl⟩
  have hstores : ∀ k, PancakeSem o (blockStoresP k) s6 = PancakeSem o k s7 := fun k => hs7 ▸
    blockStores_run o k s6 st _ _ _ _ _ hloc6.st hloc6.ph hloc6.bad hloc6.size hloc6.kind
      hloc6.held (by rw [hma6]; exact hR0) (by rw [hma6]; exact hR8) (by rw [hma6]; exact hR16)
      (by rw [hma6]; exact hR24) (by rw [hma6]; exact hR32)
  obtain ⟨w1, w2, w3, w4, w5, w6, w7, w8, w9, w10⟩ := words_ne st
  have hwritten := written_outside cap st
  have hbyte := written_kept cap st hal hfit
  have hfits : BFits cap (feedBlock cap S (q.drop i0)).2.1 := by
    have := hI.fits; rw [hfeed] at this; exact this
  have hmem7 : s7.memory = written s6.memory st
      (BitVec.ofNat 64 (phaseCode (feedBlock cap S (q.drop i0)).2.1.phase))
      (bw (feedBlock cap S (q.drop i0)).2.1.bad)
          (BitVec.ofNat 64 (feedBlock cap S (q.drop i0)).2.1.size)
      (kindB (feedBlock cap S (q.drop i0)).2.2) (heldB 0#64 (feedBlock cap S (q.drop i0)).2.2) := by
    rw [hs7]
  have hrun : ∀ k, PancakeSem o (blockFragP cap k) s = PancakeSem o k s7 := fun k =>
    (hreads k).trans ((seq_into o hrun6 (by omega)).trans (hstores k))
  have hk1 := hkept6
  simp only [keptOfB] at hk1
  have hfr := feedBlock_fresh cap S (q.drop i0)
  have hle := feedBlock_held_le cap S (q.drop i0)
  have hi6 := hloc6.i
  have hn6 := hI.names
  have hclk7 : s7.clock = s.clock - (feedBlock cap S (q.drop i0)).1 := by
    have e1 := hclk6
    have e2 : s5.clock = s.clock := rfl
    rw [hs7]; show s6.clock = _; omega
  have hma7 : s7.memaddrs = s.memaddrs := by rw [hs7]; exact hma6
  have hbe7 : s7.be = s.be := by rw [hs7]; exact hI.be
  have hloc7 : ∀ v, s7.locals v = s6.locals v := by intro v; rw [hs7]
  refine ⟨s7, hclk7, ?_, hrun⟩
  have hwr : ∀ v, v ∉ blockWrites → v ∉ blockNames ∧ v ≠ "ph" ∧ v ≠ "bad" ∧ v ≠ "size" ∧
      v ≠ "kind" ∧ v ≠ "held" := by
    intro v hv
    simp only [blockWrites, List.mem_cons, List.not_mem_nil, or_false, not_or] at hv
    refine ⟨fun h => ?_, hv.1, hv.2.1, hv.2.2.1, hv.2.2.2.1, hv.2.2.2.2.1⟩
    simp only [blockNames, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h <;> simp_all
  generalize hr : feedBlock cap S (q.drop i0) = r at hmem7 hk1 hfits hfr hle hi6 ⊢
  obtain ⟨K, S', out⟩ := r
  simp only at hfits hk1 hmem7 hi6 ⊢
  have hlen : S'.buf.length ≤ cap := by have := hfits.1; omega
  refine ⟨by rw [hloc7]; exact hi6, fun v hv => ?_,
      ⟨⟨?_, ?_, ?_, ?_⟩, ?_, hma7, hbe7, ?_, ?_, ?_, ?_⟩⟩
  · obtain ⟨a0, a1, a2, a3, a4, a5⟩ := hwr v hv
    rw [hloc7, hn6 v a0, l5 v a1 a2 a3 a4 a5]
  · rw [hmem7]; simp only [written, Ne.symm w4, Ne.symm w7, Ne.symm w9, Ne.symm w10, if_false,
      if_true]
  · rw [hmem7]; simp only [written, Ne.symm w3, Ne.symm w6, Ne.symm w8, if_false, if_true]
  · rw [hmem7]; simp only [written, Ne.symm w2, Ne.symm w5, if_false, if_true]
  · intro j hj
    rw [hmem7, hma7, hbe7, ← hma6, ← hI.be, hbyte _ _ _ _ _ _ _ _ j (by omega)]
    cases out with
    | none => exact hk1 j hj
    | some r =>
      have e := hfr r rfl
      simp only at e
      rw [e] at hj
      simp [BlockState.fresh] at hj
  · cases out with
    | none =>
      show s7.memory (st + 24#64) = 0#64
      rw [hmem7]; simp only [written, Ne.symm w1, if_false, if_true, kindB]
    | some r =>
      have hle' := hle r hS rfl
      refine ⟨?_, ?_, ?_⟩
      · rw [hmem7]; simp only [written, Ne.symm w1, if_false, if_true, kindB]
      · rw [hmem7]; simp only [written, if_true, heldB]
      · intro j hj
        rw [hmem7, hma7, hbe7, ← hma6, ← hI.be, hbyte _ _ _ _ _ _ _ _ j (by omega)]
        exact hk1 j hj
  · rw [hs7]; exact hI.ffi
  · rw [hs7]; exact hI.base
  · intro a ha
    rw [hmem7, hwritten _ _ _ _ _ _ _ _ a ha]
    exact hI.bytes a ha.2.2.2.2.2
  · intro w a0 a8 a16 a24 a32 hw
    rw [hmem7]
    simp only [written, a0, a8, a16, a24, a32, if_false]
    exact hI.words w hw

/-- **The exported block function's run is the block framer's call.** -/
theorem blockRun_run (o : Oracle σ) (cap : Nat) (hcap : cap < 2 ^ 62)
    (s : PancakeState σ) (st p : Word) (q : List Byte) (i0 : Nat) (S : BlockState)
    (hS : BFits cap S) (hi0 : i0 ≤ q.length) (hq : q.length < 2 ^ 62)
    (hst : s.locals "blk" = some st) (hp : s.locals "p" = some p)
    (hn : s.locals "n" = some (BitVec.ofNat 64 q.length))
    (hi : s.locals "i" = some (BitVec.ofNat 64 i0))
    (hH : HoldsB s st S) (hC : Chunk s p q) (hR : Room cap s st)
    (hal : st.toNat % 8 = 0) (hfit : st.toNat + 40 + cap ≤ 2 ^ 64)
    (hsep : ∀ j j', j < cap → j' < q.length →
      st + 40#64 + BitVec.ofNat 64 j ≠ p + BitVec.ofNat 64 j') :
    ((feedBlock cap S (q.drop i0)).1 ≤ s.clock →
      ∃ s', PancakeSem o (blockRunP cap) s =
          (some (.return_ (BitVec.ofNat 64 (i0 + (feedBlock cap S (q.drop i0)).1))), s') ∧
        s'.clock = s.clock - (feedBlock cap S (q.drop i0)).1 ∧
        BlockMem cap s s' st (feedBlock cap S (q.drop i0)).2.1 (feedBlock cap S (q.drop i0)).2.2) ∧
    (s.clock < (feedBlock cap S (q.drop i0)).1 →
      ∃ t, PancakeSem o (blockRunP cap) s = (some .timeout, t)) := by
  let sA : PancakeState σ := { s with locals := setLocal s.locals "ph" (BitVec.ofNat 64 0) }
  let sB : PancakeState σ := { sA with locals := setLocal sA.locals "bad" (BitVec.ofNat 64 0) }
  let sC : PancakeState σ := { sB with locals := setLocal sB.locals "size" (BitVec.ofNat 64 0) }
  let sD : PancakeState σ := { sC with locals := setLocal sC.locals "kind" (BitVec.ofNat 64 0) }
  let sE : PancakeState σ := { sD with locals := setLocal sD.locals "held" (BitVec.ofNat 64 0) }
  let sF : PancakeState σ := { sE with locals := setLocal sE.locals "b" (BitVec.ofNat 64 0) }
  let sG : PancakeState σ := { sF with locals := setLocal sF.locals "pre" (BitVec.ofNat 64 0) }
  let sH : PancakeState σ := { sG with locals := setLocal sG.locals "post" (BitVec.ofNat 64 0) }
  obtain ⟨hnorm, htime⟩ := blockFrag_run o cap hcap sH st p q i0 S hS hi0 hq
    (by simp +zetaDelta [setLocal, hst]) (by simp +zetaDelta [setLocal, hp])
    (by simp +zetaDelta [setLocal, hn]) (by simp +zetaDelta [setLocal, hi])
    (by intro v hv; simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
        rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          exact ⟨BitVec.ofNat 64 0, by simp +zetaDelta [setLocal]⟩)
    hH hC hR hal hfit hsep
  refine ⟨fun hk => ?_, fun hk => ?_⟩
  · obtain ⟨s7, hclk7, la, hrun7⟩ := hnorm hk
    have hret : PancakeSem o (.ret (x "i")) s7 =
        (some (.return_ (BitVec.ofNat 64 (i0 + (feedBlock cap S (q.drop i0)).1))),
            emptyLocals s7) := by
      rw [PancakeSem]; simp [eval, x, la.i]
    have hrun : PancakeSem o (blockRunP cap) s = _ :=
      sem_dec o rfl (sem_dec o rfl (sem_dec o rfl (sem_dec o rfl (sem_dec o rfl (sem_dec o rfl
        (sem_dec o rfl (sem_dec o rfl ((hrun7 (.ret (x "i"))).trans hret))))))))
    exact ⟨_, hrun, hclk7, ⟨la.mem.holds, la.mem.reported, la.mem.ma, la.mem.be, la.mem.ffi,
      la.mem.base, la.mem.bytes, la.mem.words⟩⟩
  · obtain ⟨t, ht⟩ := htime hk (.ret (x "i"))
    exact ⟨_, sem_dec o rfl (sem_dec o rfl (sem_dec o rfl (sem_dec o rfl (sem_dec o rfl
      (sem_dec o rfl (sem_dec o rfl (sem_dec o rfl ht)))))))⟩

/-- **`dn_frame_block` is the block framer's call**, for the function the gate prints. -/
theorem frameBlock_run (o : Oracle σ) (name : String) (cap : Nat) (hcap : cap < 2 ^ 62)
    (s : PancakeState σ) (st p : Word) (q : List Byte) (i0 : Nat) (S : BlockState)
    (hS : BFits cap S) (hi0 : i0 ≤ q.length) (hq : q.length < refused)
    (hst : s.locals "blk" = some st) (hp : s.locals "p" = some p)
    (hn : s.locals "n" = some (BitVec.ofNat 64 q.length))
    (hi : s.locals "i" = some (BitVec.ofNat 64 i0))
    (hH : HoldsB s st S) (hC : Chunk s p q) (hR : Room cap s st)
    (hal : st.toNat % 8 = 0) (hfit : st.toNat + 40 + cap ≤ 2 ^ 64)
    (hsep : ∀ j j', j < cap → j' < q.length →
      st + 40#64 + BitVec.ofNat 64 j ≠ p + BitVec.ofNat 64 j')
    {prog : PancakeProg} (hprog : Lower.lower (frameBlock name cap) = some prog) :
    ((feedBlock cap S (q.drop i0)).1 ≤ s.clock →
      ∃ s', PancakeSem o prog s =
          (some (.return_ (BitVec.ofNat 64 (i0 + (feedBlock cap S (q.drop i0)).1))), s') ∧
        s'.clock = s.clock - (feedBlock cap S (q.drop i0)).1 ∧
        BlockMem cap s s' st (feedBlock cap S (q.drop i0)).2.1 (feedBlock cap S (q.drop i0)).2.2) ∧
    (s.clock < (feedBlock cap S (q.drop i0)).1 →
      ∃ t, PancakeSem o prog s = (some .timeout, t)) := by
  have hq62 : q.length < 2 ^ 62 := by unfold refused at hq; omega
  rw [frameBlock_lower] at hprog
  cases hprog
  rw [guard_pass o _ s q.length i0 hn hi hi0 hq62]
  exact blockRun_run o cap hcap s st p q i0 S hS hi0 hq62 hst hp hn hi hH hC hR hal hfit hsep

theorem frameBlock_refuses (o : Oracle σ) (name : String) (cap : Nat) (s : PancakeState σ)
    (nw iw : Word) (hn : s.locals "n" = some nw) (hi : s.locals "i" = some iw)
    (h : signedLt nw (BitVec.ofNat 64 0) = true ∨ signedLt iw (BitVec.ofNat 64 0) = true ∨
      signedLt nw iw = true) {prog : PancakeProg}
    (hprog : Lower.lower (frameBlock name cap) = some prog) :
    PancakeSem o prog s = (some (.return_ (BitVec.ofNat 64 refused)), emptyLocals s) := by
  rw [frameBlock_lower] at hprog
  cases hprog
  exact guard_refuses o _ s nw iw hn hi h

/-! ## The premises hold of real states -/

/-- A block at 0 holding the line "A" so far, with the received byte "H" at 64. -/
def demoLocals : String → Option Value := fun name =>
  if name = "blk" then some 0 else if name = "p" then some 64 else if name = "n" then some 1
  else if name = "i" then some 0 else if name = "len" then some 1 else if name = "cr" then some 0
  else if name = "bad" then some 0 else if name = "kind" then some 0
  else if name = "kept" then some 0 else if name = "b" then some 72 else if name = "ph" then some 1
  else if name = "size" then some 1 else if name = "held" then some 0
  else if name = "pre" then some 0 else if name = "post" then some 0
  else none

def demo : PancakeState Unit :=
  { locals := demoLocals,
    memory := fun w => if w = 0 then 1 else if w = 40 then 65 else if w = 64 then 72 else 0,
    memaddrs := fun _ => true, be := false, clock := 1, ffi := (), baseAddr := 0 }

/-- The same, with a block in the data of its first line at 0. -/
def demoB : PancakeState Unit :=
  { demo with memory := fun w => if w = 0 then 1 else if w = 16 then 1 else if w = 40 then 65 else
      if w = 64 then 72 else 0 }

def demoLine : LineState := ⟨1, false, false, [65#8]⟩

def demoBlock : BlockState := ⟨.data, false, 1, [65#8]⟩

theorem fits_witness : Fits 4 demoLine := by unfold Fits; decide

theorem bfits_witness : BFits 4 demoBlock := by unfold BFits; decide

theorem kept_witness : Kept demo 0 [65#8] := by
  intro j hj
  have : j = 0 := by simpa using hj
  subst this
  rfl

theorem chunk_witness : Chunk demo 64 [72#8] := by
  intro j hj
  have : j = 0 := by simpa using hj
  subst this
  rfl

theorem holds_witness : Holds demo 0 demoLine := ⟨rfl, rfl, rfl, kept_witness⟩

theorem holdsB_witness : HoldsB demoB 0 demoBlock := by
  refine ⟨rfl, rfl, rfl, fun j hj => ?_⟩
  have : j = 0 := by simp [demoBlock] at hj; omega
  subst this
  rfl

theorem room_witness : Room 4 demo 0 := ⟨rfl, rfl, rfl, rfl, rfl, fun _ _ => rfl⟩

/-- A byte past the block. -/
theorem outside_witness : Outside 4 0 100 := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, fun j hj => ?_⟩
  intro h
  have := congrArg BitVec.toNat h
  simp at this
  omega

theorem lineLocals_witness : LineLocals demo 0 64 1 0 demoLine 0 0 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ⟨_, rfl⟩⟩

theorem blockLocals_witness : BlockLocals demoB 0 64 1 0 demoBlock 0 0 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ⟨_, rfl⟩, ⟨_, rfl⟩, ⟨_, rfl⟩⟩

theorem phaseIn_witness : PhaseIn demoB demoBlock 72#8 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, ⟨_, rfl⟩, ⟨_, rfl⟩⟩

/-- What a run leaves holds of the demo state as it is: the line framer's state is in its block and
no line is reported. -/
theorem lineMem_witness : LineMem 4 demo demo 0 demoLine none :=
  ⟨holds_witness, rfl, rfl, rfl, rfl, rfl, fun _ _ => rfl, fun _ _ _ _ _ _ _ => rfl⟩

theorem lineAfter_witness : LineAfter 4 demo demo 0 0 demoLine none :=
  ⟨rfl, fun _ _ => rfl, lineMem_witness⟩

/-- The chunk at 64 lies apart from the demo block's bytes. -/
theorem apart_witness : ∀ j j', j < 4 → j' < [72#8].length →
    (0 : Word) + 40#64 + BitVec.ofNat 64 j ≠ 64 + BitVec.ofNat 64 j' := by
  intro j j' hj hj' h
  have := congrArg BitVec.toNat h
  simp at hj' this
  omega

/-- **The exported line framer's premises hold together**: `dn_frame_line_4` reads the chunk "H"
from the demo state, keeps "AH" and reports no line yet. -/
theorem frameLine_demo : ∃ s', PancakeSem (Oracle.idle (σ := Unit)) (guardP (lineRunP 4)) demo =
    (some (.return_ (BitVec.ofNat 64 1)), s') ∧ s'.clock = 0 ∧
    Holds s' 0 ⟨2, false, false, [65#8, 72#8]⟩ ∧ Reported s' 0 none := by
  obtain ⟨s', h1, h2, h3⟩ := (frameLine_run (Oracle.idle (σ := Unit)) "f" 4 (by decide) (by decide)
    demo 0 64 [72#8] 0 demoLine fits_witness (by decide) (by decide) rfl rfl rfl rfl holds_witness
    chunk_witness room_witness (by decide) (by decide) apart_witness (frameLine_lower "f" 4)).1
    (by decide)
  exact ⟨s', h1, h2, h3.holds, h3.reported⟩

/-- …and with no clock left it times out. -/
theorem frameLine_demo_timeout : ∃ t,
    PancakeSem (Oracle.idle (σ := Unit)) (guardP (lineRunP 4)) { demo with clock := 0 } =
      (some .timeout, t) :=
  (frameLine_run (Oracle.idle (σ := Unit)) "f" 4 (by decide) (by decide) { demo with clock := 0 }
    0 64 [72#8] 0 demoLine fits_witness (by decide) (by decide) rfl rfl rfl rfl holds_witness
    chunk_witness room_witness (by decide) (by decide) apart_witness (frameLine_lower "f" 4)).2
    (by decide)

/-- The demo state called from past the end of its chunk. -/
def demoPast : PancakeState Unit :=
  { demo with locals := fun v => if v = "i" then some 2 else demo.locals v }

/-- …which the framer refuses before reading anything. -/
theorem frameLine_demo_refused :
    PancakeSem (Oracle.idle (σ := Unit)) (guardP (lineRunP 4)) demoPast =
      (some (.return_ (BitVec.ofNat 64 refused)), emptyLocals demoPast) :=
  frameLine_refuses _ "f" 4 demoPast 1 2 rfl rfl (.inr (.inr (by decide))) (frameLine_lower "f" 4)

/-- The loop's invariant holds where the loop starts, on the demo state. -/
theorem loopInv_witness : LoopInv 4 demo demo 0 64 [72#8] 0 demoLine 0 0 :=
  ⟨lineLocals_witness, kept_witness, chunk_witness, rfl, rfl, rfl, rfl, fun _ _ => rfl,
    fun _ _ => rfl, fun _ _ => rfl, fits_witness⟩

theorem keptB_witness : Kept demoB 0 [65#8] := by
  intro j hj
  have : j = 0 := by simpa using hj
  subst this
  rfl

theorem chunkB_witness : Chunk demoB 64 [72#8] := by
  intro j hj
  have : j = 0 := by simpa using hj
  subst this
  rfl

/-- …and the block loop's, on the demo state with a block. -/
theorem blockInv_witness : BlockInv 4 demoB demoB 0 64 [72#8] 0 demoBlock 0 0 :=
  ⟨blockLocals_witness, keptB_witness, chunkB_witness, rfl, rfl, rfl, rfl, fun _ _ => rfl,
    fun _ _ => rfl, fun _ _ => rfl, bfits_witness⟩

/-- **The exported block framer's premises hold together**: `dn_frame_block_4` reads the chunk
"H" from the demo state, holds "AH" and reports no block yet. -/
theorem frameBlock_demo : ∃ s',
    PancakeSem (Oracle.idle (σ := Unit)) (guardP (blockRunP 4)) demoB =
      (some (.return_ (BitVec.ofNat 64 1)), s') ∧ s'.clock = 0 ∧
    HoldsB s' 0 ⟨.data, false, 2, [65#8, 72#8]⟩ ∧ ReportedB s' 0 none := by
  obtain ⟨s', h1, h2, h3⟩ := (frameBlock_run (Oracle.idle (σ := Unit)) "f" 4 (by decide) demoB 0 64
    [72#8] 0 demoBlock bfits_witness (by decide) (by decide) rfl rfl rfl rfl holdsB_witness
    chunkB_witness ⟨rfl, rfl, rfl, rfl, rfl, fun _ _ => rfl⟩ (by decide) (by decide) apart_witness
    (frameBlock_lower "f" 4)).1 (by decide)
  exact ⟨s', h1, h2, h3.holds, h3.reported⟩

theorem frameBlock_demo_timeout : ∃ t,
    PancakeSem (Oracle.idle (σ := Unit)) (guardP (blockRunP 4)) { demoB with clock := 0 } =
      (some .timeout, t) :=
  (frameBlock_run (Oracle.idle (σ := Unit)) "f" 4 (by decide) { demoB with clock := 0 } 0 64
    [72#8] 0 demoBlock bfits_witness (by decide) (by decide) rfl rfl rfl rfl holdsB_witness
    chunkB_witness ⟨rfl, rfl, rfl, rfl, rfl, fun _ _ => rfl⟩ (by decide) (by decide) apart_witness
    (frameBlock_lower "f" 4)).2 (by decide)

theorem frameBlock_demo_refused :
    PancakeSem (Oracle.idle (σ := Unit)) (guardP (blockRunP 4)) demoPast =
      (some (.return_ (BitVec.ofNat 64 refused)), emptyLocals demoPast) :=
  frameBlock_refuses _ "f" 4 demoPast 1 2 rfl rfl (.inr (.inr (by decide))) (frameBlock_lower "f" 4)

/-- …and of the demo state with a block. -/
theorem blockMem_witness : BlockMem 4 demoB demoB 0 demoBlock none :=
  ⟨holdsB_witness, rfl, rfl, rfl, rfl, rfl, fun _ _ => rfl, fun _ _ _ _ _ _ _ => rfl⟩

theorem blockAfter_witness : BlockAfter 4 demoB demoB 0 0 demoBlock none :=
  ⟨rfl, fun _ _ => rfl, blockMem_witness⟩

end DN.News.FramerCode
