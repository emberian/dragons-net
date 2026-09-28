-- SPDX-License-Identifier: AGPL-3.0-or-later
import DN.News.FrameSpec

/-!
# DN.News.Framer

The framer as the program runs it: a state per connection that one byte at a time turns into
the next state and, at the end of a line or of a block, a verdict. `DN.News.FramerCode` holds the
program and proves that it makes exactly these steps.

The state after some bytes is not defined by running the framer: `absLine` computes it from the
bytes of the unfinished line alone, in the vocabulary of `DN.News.FrameSpec`. Each step is proven
to take `absLine` of the bytes before to `absLine` of the bytes after (`lineStep_abs`), and the end
of a line to give `classify` of its bytes (`lineStep_end`); so feeding any stream gives the
specification's lines (`feed_lines`), however the stream is cut into received chunks
(`feedChunks_lines`). The same holds of blocks (`feedBlock_block`).

Each rule of the specification is shown to matter: a framer with one of them broken
(`LineMutant`, `BlockMutant`) gives another answer on a stream written for it.
-/

namespace DN.News.Framer

open DN.News.FrameSpec

/-! ## Command lines -/

/-- The state of the line framer: how many bytes of the line it has seen, up to `lim`; whether the
last of them was a CR; whether the line already cannot be a command because of a NUL or of a CR
not followed by the line end; and the bytes it keeps, the first `lim` of the line. -/
structure LineState where
  len : Nat
  cr : Bool
  bad : Bool
  buf : List Byte
  deriving DecidableEq, Repr

def LineState.fresh : LineState := ⟨0, false, false, []⟩

/-- One byte. At an LF the line ends: the verdict is given and the state starts afresh. -/
def lineStep (lim : Nat) (s : LineState) (b : Byte) : LineState × Option Line :=
  if b = LF then
    let line : Line :=
      if lim ≤ s.len then ⟨.overlong, s.buf⟩
      else if s.cr ∧ ¬ s.bad then ⟨.command, s.buf.take (s.len - 1)⟩
      else ⟨.malformed, s.buf⟩
    (.fresh, some line)
  else
    ({ len := if s.len < lim then s.len + 1 else s.len,
       cr := decide (b = CR),
       bad := s.bad || s.cr || decide (b = NUL),
       buf := if s.len < lim then s.buf ++ [b] else s.buf }, none)

/-- Feed bytes, collecting the lines that end among them. -/
def feed (lim : Nat) : LineState → List Byte → LineState × List Line
  | s, [] => (s, [])
  | s, b :: rest =>
    let r := lineStep lim s b
    let t := feed lim r.1 rest
    (t.1, r.2.toList ++ t.2)

/-- The state after the bytes `p` of a line that has not ended, computed from `p` alone. -/
def absLine (lim : Nat) (p : List Byte) : LineState :=
  { len := min p.length lim,
    cr := decide (p.getLast? = some CR),
    bad := decide (NUL ∈ p ∨ CR ∈ p.dropLast),
    buf := p.take lim }

theorem absLine_nil (lim : Nat) : absLine lim [] = .fresh := by
  simp [absLine, LineState.fresh]

/-- A byte of a list is its last one or one of those before it. -/
theorem mem_iff_dropLast (p : List Byte) (x : Byte) :
    x ∈ p ↔ x ∈ p.dropLast ∨ p.getLast? = some x := by
  by_cases hp : p = []
  · subst hp; simp
  · have e := List.dropLast_concat_getLast hp
    rw [List.getLast?_eq_some_getLast hp]
    conv => lhs; rw [← e]
    simp only [List.mem_append, List.mem_singleton, Option.some.injEq]
    exact or_congr_right eq_comm

/-- **A byte that does not end the line takes the state of the bytes before it to the state of
the bytes with it.** -/
theorem lineStep_abs (lim : Nat) (p : List Byte) (b : Byte) (hb : b ≠ LF) :
    lineStep lim (absLine lim p) b = (absLine lim (p ++ [b]), none) := by
  simp only [lineStep, hb, if_false, absLine, Prod.mk.injEq, and_true]
  have hmem := mem_iff_dropLast p CR
  simp only [LineState.mk.injEq]
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [List.length_append, List.length_singleton]; split <;> omega
  · simp
  · simp only [List.mem_append, List.mem_singleton, List.dropLast_concat, Bool.decide_or]
    have hsym : (NUL = b) ↔ (b = NUL) := eq_comm
    by_cases h1 : NUL ∈ p <;> by_cases h2 : CR ∈ p.dropLast <;>
      by_cases h3 : p.getLast? = some CR <;> by_cases h4 : b = NUL <;> simp_all
  · by_cases h : p.length < lim
    · have : min p.length lim < lim := by omega
      simp only [this, if_true, List.take_of_length_le (show p.length ≤ lim by omega),
        List.take_of_length_le (show (p ++ [b]).length ≤ lim by simp; omega)]
    · have : ¬ min p.length lim < lim := by omega
      simp only [this, if_false]
      rw [List.take_append_of_le_length (by omega)]

/-- **The end of a line gives the specification's verdict on its bytes.** -/
theorem lineStep_end (lim : Nat) (p : List Byte) :
    lineStep lim (absLine lim p) LF = (.fresh, some (classify lim p)) := by
  simp only [lineStep, if_true, absLine, classify, Prod.mk.injEq, true_and, Option.some.injEq]
  by_cases hlong : lim < p.length + 1
  · have : lim ≤ min p.length lim := by omega
    simp only [this, if_true, hlong]
  · have hmin : min p.length lim = p.length := by omega
    have h1 : ¬ lim ≤ p.length := by omega
    have htake : p.take lim = p := List.take_of_length_le (by omega)
    have hkept : p.take (p.length - 1) = p.dropLast := (List.dropLast_eq_take).symm
    simp only [hmin, h1, if_false, hlong, htake, hkept]
    by_cases hc : p.getLast? = some CR <;> by_cases hn : NUL ∈ p <;>
      by_cases hd : CR ∈ p.dropLast <;> simp_all

/-- Bytes with no LF among them extend the unfinished line. -/
theorem feed_open (lim : Nat) (p q : List Byte) (hq : LF ∉ q) :
    feed lim (absLine lim p) q = (absLine lim (p ++ q), []) := by
  induction q generalizing p with
  | nil => simp [feed]
  | cons b rest ih =>
    have hb : b ≠ LF := fun h => hq (by simp [h])
    have hrest : LF ∉ rest := fun h => hq (by simp [h])
    simp only [feed, lineStep_abs lim p b hb, ih (p ++ [b]) hrest, List.append_assoc,
      List.singleton_append, Option.toList_none, List.nil_append]

/-- A line's bytes and its LF, from the state of an unfinished line `p`. -/
theorem feed_line (lim : Nat) (p body rest : List Byte) (hbody : LF ∉ body) :
    feed lim (absLine lim p) (body ++ LF :: rest) =
      let t := feed lim .fresh rest
      (t.1, classify lim (p ++ body) :: t.2) := by
  induction body generalizing p with
  | nil => simp [feed, lineStep_end]
  | cons b more ih =>
    have hb : b ≠ LF := fun h => hbody (by simp [h])
    have hmore : LF ∉ more := fun h => hbody (by simp [h])
    simp only [List.cons_append, feed, lineStep_abs lim p b hb, Option.toList_none,
      List.nil_append]
    rw [ih (p ++ [b]) hmore]
    simp

/-- **Feeding a stream gives the specification's lines, and leaves the state of its tail.** -/
theorem feed_lines (lim : Nat) {s : List Byte} {bodies : List (List Byte)} {tail : List Byte}
    (h : Lines s bodies tail) :
    feed lim .fresh s = (absLine lim tail, bodies.map (classify lim)) := by
  obtain ⟨rfl, hb, ht⟩ := h
  induction bodies with
  | nil =>
    simpa [absLine_nil] using feed_open lim [] tail ht
  | cons body more ih =>
    have hbody : LF ∉ body := hb body (by simp)
    have hmore : ∀ b ∈ more, LF ∉ b := fun b h => hb b (by simp [h])
    have := feed_line lim [] body ((more.map (· ++ [LF])).flatten ++ tail) hbody
    rw [absLine_nil] at this
    simp only [List.map_cons, List.flatten_cons, List.append_assoc, List.cons_append,
      List.nil_append] at this ⊢
    rw [this, ih hmore]

/-- Feeding in chunks is feeding their concatenation: the state carries across the cut. -/
def feedChunks (lim : Nat) : LineState → List (List Byte) → LineState × List Line
  | s, [] => (s, [])
  | s, c :: cs =>
    let r := feed lim s c
    let t := feedChunks lim r.1 cs
    (t.1, r.2 ++ t.2)

theorem feed_append (lim : Nat) (s : LineState) (a b : List Byte) :
    feed lim s (a ++ b) =
      let r := feed lim s a
      let t := feed lim r.1 b
      (t.1, r.2 ++ t.2) := by
  induction a generalizing s with
  | nil => simp [feed]
  | cons x more ih => simp [feed, ih]

theorem feedChunks_eq (lim : Nat) (s : LineState) (cs : List (List Byte)) :
    feedChunks lim s cs = feed lim s cs.flatten := by
  induction cs generalizing s with
  | nil => simp [feedChunks, feed]
  | cons c more ih => simp [feedChunks, ih, feed_append]

/-- **However the stream arrives in chunks, the framer gives the specification's lines.** -/
theorem feedChunks_lines (lim : Nat) {cs : List (List Byte)} {bodies : List (List Byte)}
    {tail : List Byte} (h : Lines cs.flatten bodies tail) :
    feedChunks lim .fresh cs = (absLine lim tail, bodies.map (classify lim)) := by
  rw [feedChunks_eq, feed_lines lim h]

/-! ### The call the program makes

The program reads a received chunk from a position and stops at the end of the first line it
finishes, so that the session answers one command before it reads the next. -/

/-- Bytes read up to and including the first line end: how many, the state, and the line. -/
def frameOnce (lim : Nat) : LineState → List Byte → Nat × LineState × Option Line
  | s, [] => (0, s, none)
  | s, b :: rest =>
    match lineStep lim s b with
    | (s', some l) => (1, s', some l)
    | (s', none) =>
      let t := frameOnce lim s' rest
      (t.1 + 1, t.2.1, t.2.2)

/-- A call reads at most the bytes it is given, and at least one when it is given any. -/
theorem frameOnce_len (lim : Nat) (s : LineState) (q : List Byte) :
    (frameOnce lim s q).1 ≤ q.length ∧ (q ≠ [] → 0 < (frameOnce lim s q).1) := by
  induction q generalizing s with
  | nil => simp [frameOnce]
  | cons b rest ih =>
    simp only [frameOnce]
    split
    · simp
    · rename_i s' _
      have := ih s'
      simp only [List.length_cons]
      exact ⟨by omega, fun _ => by omega⟩

/-- **A call is the framer on the bytes it reads**, and it stops at the first line. -/
theorem frameOnce_feed (lim : Nat) (s : LineState) (q : List Byte) :
    let r := frameOnce lim s q
    feed lim s (q.take r.1) = (r.2.1, r.2.2.toList) := by
  induction q generalizing s with
  | nil => simp [frameOnce, feed]
  | cons b rest ih =>
    simp only [frameOnce]
    split
    · rename_i s' l h
      simp [feed, h]
    · rename_i s' h
      simp only [List.take_succ_cons, feed, h, Option.toList_none, List.nil_append]
      exact ih s'

/-- Before the byte that ends the first line, the framer has given no line yet. -/
theorem frameOnce_quiet (lim : Nat) :
    ∀ (s : LineState) (q : List Byte) (k : Nat), k < (frameOnce lim s q).1 →
      (feed lim s (q.take k)).2 = [] := by
  intro s q
  induction q generalizing s with
  | nil => intro k hk; simp [frameOnce] at hk
  | cons b rest ih =>
    intro k hk
    cases k with
    | zero => simp [feed]
    | succ k =>
      simp only [frameOnce] at hk
      split at hk
      · simp at hk
      · rename_i s' h
        simp only [List.take_succ_cons, feed, h, Option.toList_none, List.nil_append]
        exact ih s' k (by omega)

/-- A call that stops before the end of what it was given stopped at a line. -/
theorem frameOnce_short (lim : Nat) :
    ∀ (s : LineState) (q : List Byte), (frameOnce lim s q).1 < q.length →
      (frameOnce lim s q).2.2.isSome := by
  intro s q
  induction q generalizing s with
  | nil => simp [frameOnce]
  | cons b rest ih =>
    intro h
    rcases hstep : lineStep lim s b with ⟨s', _ | l⟩
    · simp only [frameOnce, hstep, List.length_cons] at h ⊢
      exact ih s' (by omega)
    · simp [frameOnce, hstep]

/-- Calls repeated until the chunk is read, as the session makes them: at most one per byte. -/
def drain (lim : Nat) : Nat → LineState → List Byte → LineState × List Line
  | 0, s, _ => (s, [])
  | fuel + 1, s, q =>
    if q = [] then (s, [])
    else
      let r := frameOnce lim s q
      let t := drain lim fuel r.2.1 (q.drop r.1)
      (t.1, r.2.2.toList ++ t.2)

/-- **Calling until the chunk is read is feeding the chunk.** -/
theorem drain_feed (lim : Nat) (fuel : Nat) (s : LineState) (q : List Byte)
    (hfuel : q.length ≤ fuel) : drain lim fuel s q = feed lim s q := by
  induction fuel generalizing s q with
  | zero =>
    have : q = [] := List.eq_nil_of_length_eq_zero (by omega)
    simp [drain, this, feed]
  | succ fuel ih =>
    by_cases hq : q = []
    · simp [drain, hq, feed]
    · simp only [drain, hq, if_false]
      have hlen := frameOnce_len lim s q
      have hk := hlen.2 hq
      have hfeed := frameOnce_feed lim s q
      rw [ih _ _ (by simp only [List.length_drop]; omega)]
      conv => rhs; rw [← List.take_append_drop (frameOnce lim s q).1 q, feed_append]
      simp only [hfeed]

/-! ### Every rule matters

A framer with one rule broken, each against a stream that shows it. -/

inductive LineMutant
  | none
  /-- a line of exactly the limit is taken for a command -/
  | limitOffByOne
  /-- a CR followed by another byte does not spoil the line -/
  | crForgotten
  /-- a NUL does not spoil the line -/
  | nulAllowed
  /-- a bare LF ends a command -/
  | bareLF
  /-- the state is not started afresh after a line -/
  | noReset
  /-- a command keeps its CR -/
  | keepCR
  deriving DecidableEq, Repr

def lineStepM (m : LineMutant) (lim : Nat) (s : LineState) (b : Byte) : LineState × Option Line :=
  if b = LF then
    let line : Line :=
      if (if m = .limitOffByOne then lim < s.len else lim ≤ s.len) then ⟨.overlong, s.buf⟩
      else if (s.cr || m = .bareLF) ∧ ¬ s.bad then
        ⟨.command, if m = .keepCR then s.buf else s.buf.take (s.len - 1)⟩
      else ⟨.malformed, s.buf⟩
    (if m = .noReset then s else .fresh, some line)
  else
    ({ len := if s.len < lim then s.len + 1 else s.len,
       cr := decide (b = CR),
       bad := s.bad || (s.cr && m ≠ .crForgotten) || (decide (b = NUL) && m ≠ .nulAllowed),
       buf := if s.len < lim then s.buf ++ [b] else s.buf }, none)

def feedM (m : LineMutant) (lim : Nat) : LineState → List Byte → LineState × List Line
  | s, [] => (s, [])
  | s, b :: rest =>
    let r := lineStepM m lim s b
    let t := feedM m lim r.1 rest
    (t.1, r.2.toList ++ t.2)

theorem lineStepM_none : lineStepM .none = lineStep := by
  funext lim s b
  simp [lineStepM, lineStep]

theorem feedM_none : feedM .none = feed := by
  funext lim s q
  induction q generalizing s with
  | nil => rfl
  | cons b rest ih => simp [feedM, feed, lineStepM_none, ih]

/-- A stream that tells the mutant from the framer, for lines of at most four octets. -/
def lineWitness : LineMutant → List Byte
  | .none => []
  | .limitOffByOne => [65#8, 65#8, 65#8, 13#8, 10#8]
  | .crForgotten => [13#8, 65#8, 13#8, 10#8]
  | .nulAllowed => [65#8, 0#8, 13#8, 10#8]
  | .bareLF => [65#8, 10#8]
  | .noReset => [65#8, 10#8, 13#8, 10#8]
  | .keepCR => [65#8, 13#8, 10#8]

/-- **Each broken rule changes the answer on its stream.** The framer's answer there is the
specification's (`feed_lines`); the mutant's is not. -/
theorem mutants_differ :
    ∀ m, m ≠ .none → feedM m 4 .fresh (lineWitness m) ≠ feed 4 .fresh (lineWitness m) := by
  intro m hm
  cases m <;> first | exact absurd rfl hm | decide

/-! ## Multi-line blocks -/

theorem unbroken_nil : Unbroken [] := by
  intro h; have := h.length_le; simp [CRLF] at this

theorem unbroken_single (x : Byte) : Unbroken [x] := by
  intro h; have := h.length_le; simp [CRLF] at this

theorem unbroken_cons₂ (a b : Byte) (rest : List Byte) :
    Unbroken (a :: b :: rest) ↔ ¬ (a = CR ∧ b = LF) ∧ Unbroken (b :: rest) := by
  simp only [Unbroken, CRLF, List.infix_cons_iff, List.cons_prefix_cons, List.nil_prefix, and_true]
  constructor
  · intro h; exact ⟨fun ⟨h1, h2⟩ => h (Or.inl ⟨h1.symm, h2.symm⟩), fun h' => h (Or.inr h')⟩
  · rintro ⟨h1, h2⟩ (⟨e1, e2⟩ | h')
    · exact h1 ⟨e1.symm, e2.symm⟩
    · exact h2 h'

/-- A byte added to a line breaks it exactly when it is an LF after a CR. -/
theorem unbroken_snoc (r : List Byte) (x : Byte) :
    Unbroken (r ++ [x]) ↔ Unbroken r ∧ ¬ (r.getLast? = some CR ∧ x = LF) := by
  induction r with
  | nil => simp [unbroken_single, unbroken_nil]
  | cons a r ih =>
    cases r with
    | nil =>
      simp only [List.cons_append, List.nil_append, unbroken_cons₂, List.getLast?_singleton,
        Option.some.injEq]
      simp [unbroken_single]
    | cons b r =>
      simp only [List.cons_append] at ih ⊢
      rw [unbroken_cons₂, ih, unbroken_cons₂, List.getLast?_cons_cons]
      exact and_assoc.symm

/-- Where the framer is in the line it reads. -/
inductive Phase
  /-- at the start of a line -/
  | bol
  /-- inside a line -/
  | data
  /-- after a CR that may end the line -/
  | cr
  /-- after a dot at the start of a line -/
  | dot
  /-- after a dot and a CR at the start of a line -/
  | dotcr
  deriving DecidableEq, Repr

/-- The state of the block framer: where it is in the line; whether a line already made the
block refused; how many bytes the block holds so far, up to `cap + 1`; and the first `cap` of
them. -/
structure BlockState where
  phase : Phase
  bad : Bool
  size : Nat
  buf : List Byte
  deriving DecidableEq, Repr

def BlockState.fresh : BlockState := ⟨.bol, false, 0, []⟩

/-- The same content, in another phase and with another verdict so far. -/
def BlockState.at (s : BlockState) (ph : Phase) (bad : Bool) : BlockState :=
  { s with phase := ph, bad := bad }

/-- One more byte of what the block holds. -/
def put (cap : Nat) (s : BlockState) (x : Byte) : BlockState :=
  if s.size < cap then { s with size := s.size + 1, buf := s.buf ++ [x] }
  else { s with size := cap + 1 }

/-- The verdict at the end of a block. -/
def result (cap : Nat) (s : BlockState) : BlockResult :=
  if s.bad then ⟨.refused, []⟩ else if cap < s.size then ⟨.tooLarge, []⟩ else ⟨.accepted, s.buf⟩

/-- Whether a byte inside a line spoils the block. -/
def spoils (x : Byte) : Bool := decide (x = LF) || decide (x = NUL)

/-- One byte. The dot that ends a block, and the one a sender put before a line starting with a
dot, are not held; a CR is held back until the next byte shows whether it ends the line. -/
def blockStep (cap : Nat) (s : BlockState) (x : Byte) : BlockState × Option BlockResult :=
  match s.phase with
  | .bol =>
    if x = DOT then (s.at .dot s.bad, none)
    else if x = CR then (s.at .cr s.bad, none)
    else ((put cap s x).at .data (s.bad || spoils x), none)
  | .data =>
    if x = CR then (s.at .cr s.bad, none)
    else ((put cap s x).at .data (s.bad || spoils x), none)
  | .cr =>
    if x = LF then ((put cap (put cap s CR) LF).at .bol s.bad, none)
    else if x = CR then ((put cap s CR).at .cr true, none)
    else ((put cap (put cap s CR) x).at .data true, none)
  | .dot =>
    if x = CR then (s.at .dotcr s.bad, none)
    else ((put cap s x).at .data (s.bad || spoils x), none)
  | .dotcr =>
    if x = LF then (.fresh, some (result cap s))
    else if x = CR then ((put cap s CR).at .cr true, none)
    else ((put cap (put cap s CR) x).at .data true, none)

/-- Bytes read up to and including the end of the block: how many, the state, and the verdict. -/
def feedBlock (cap : Nat) : BlockState → List Byte → Nat × BlockState × Option BlockResult
  | s, [] => (0, s, none)
  | s, x :: rest =>
    match blockStep cap s x with
    | (s', some v) => (1, s', some v)
    | (s', none) =>
      let t := feedBlock cap s' rest
      (t.1 + 1, t.2.1, t.2.2)

/-! ### The state computed from the bytes read

The lines of the block read so far, `ls`, and the line being read, `r`, determine the state. -/

/-- The line being read without a CR at its end, which the next byte may yet make its end. -/
def held (r : List Byte) : List Byte := if r.getLast? = some CR then r.dropLast else r

def phaseOf (r : List Byte) : Phase :=
  if r = [] then .bol else if r = [DOT] then .dot else if r = [DOT, CR] then .dotcr
  else if r.getLast? = some CR then .cr else .data

def mk (cap : Nat) (ph : Phase) (bad : Bool) (c : List Byte) : BlockState :=
  ⟨ph, bad, min c.length (cap + 1), c.take cap⟩

/-- Whether a line is clean, as a value the state can hold. -/
def cleanB (l : List Byte) : Bool := decide (Clean l)

/-- The state after the lines `ls` and the unfinished line `r`, from those bytes alone. -/
def absBlock (cap : Nat) (ls : List (List Byte)) (r : List Byte) : BlockState :=
  mk cap (phaseOf r) (!(ls.all cleanB && cleanB (held r))) (content ls ++ unstuff (held r))

theorem dot_ne_cr : ¬ DOT = CR := by decide
theorem cr_ne_dot : ¬ CR = DOT := by decide
theorem lf_ne_cr : ¬ LF = CR := by decide
theorem cr_ne_lf : ¬ CR = LF := by decide
theorem dot_ne_lf : ¬ DOT = LF := by decide
theorem lf_ne_dot : ¬ LF = DOT := by decide
theorem nul_ne_cr : ¬ NUL = CR := by decide
theorem cr_ne_nul : ¬ CR = NUL := by decide
theorem dot_ne_nul : ¬ DOT = NUL := by decide
theorem lf_ne_nul : ¬ LF = NUL := by decide
theorem nul_ne_dot : ¬ NUL = DOT := by decide
theorem nul_ne_lf : ¬ NUL = LF := by decide

theorem cleanB_nil : cleanB [] = true := by decide
theorem cleanB_dot : cleanB [DOT] = true := by decide

theorem put_mk (cap : Nat) (ph : Phase) (bad : Bool) (c : List Byte) (x : Byte) :
    put cap (mk cap ph bad c) x = mk cap ph bad (c ++ [x]) := by
  simp only [put, mk]
  by_cases h : c.length < cap
  · have : min c.length (cap + 1) < cap := by omega
    simp only [this, if_true, BlockState.mk.injEq, true_and, List.length_append,
      List.length_singleton]
    refine ⟨by omega, ?_⟩
    rw [List.take_of_length_le (by omega), List.take_of_length_le (by simp; omega)]
  · have : ¬ min c.length (cap + 1) < cap := by omega
    simp only [this, if_false, BlockState.mk.injEq, true_and, List.length_append,
      List.length_singleton]
    refine ⟨by omega, ?_⟩
    rw [List.take_append_of_le_length (by omega)]

theorem mk_at (cap : Nat) (ph ph' : Phase) (bad bad' : Bool) (c : List Byte) :
    (mk cap ph bad c).at ph' bad' = mk cap ph' bad' c := rfl

theorem mk_phase (cap : Nat) (ph : Phase) (bad : Bool) (c : List Byte) :
    (mk cap ph bad c).phase = ph := rfl

theorem mk_bad (cap : Nat) (ph : Phase) (bad : Bool) (c : List Byte) :
    (mk cap ph bad c).bad = bad := rfl

theorem absBlock_nil (cap : Nat) : absBlock cap [] [] = .fresh := by
  simp [cleanB_nil, absBlock, mk, held, phaseOf, content, unstuff, BlockState.fresh]

theorem clean_snoc (q : List Byte) (x : Byte) :
    Clean (q ++ [x]) ↔ Clean q ∧ x ≠ CR ∧ x ≠ LF ∧ x ≠ NUL := by
  simp only [Clean, List.mem_append, List.mem_singleton, not_or]
  constructor
  · rintro ⟨⟨a, b⟩, ⟨c, d⟩, ⟨e, f⟩⟩; exact ⟨⟨a, c, e⟩, fun h => b h.symm, fun h => d h.symm,
      fun h => f h.symm⟩
  · rintro ⟨⟨a, c, e⟩, b, d, f⟩; exact ⟨⟨a, fun h => b h.symm⟩, ⟨c, fun h => d h.symm⟩,
      ⟨e, fun h => f h.symm⟩⟩

theorem cleanB_snoc (q : List Byte) (x : Byte) :
    cleanB (q ++ [x]) = (cleanB q && !decide (x = CR) && !spoils x) := by
  simp only [cleanB, spoils]
  rw [Bool.eq_iff_iff]
  simp only [decide_eq_true_eq, Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not,
    Bool.or_eq_false_iff, clean_snoc]
  constructor
  · rintro ⟨h1, h2, h3, h4⟩; exact ⟨⟨h1, h2⟩, h3, h4⟩
  · rintro ⟨⟨h1, h2⟩, h3, h4⟩; exact ⟨h1, h2, h3, h4⟩

theorem unstuff_snoc (q : List Byte) (x : Byte) (h : q ≠ [] ∨ x ≠ DOT) :
    unstuff (q ++ [x]) = unstuff q ++ [x] := by
  cases q with
  | nil => simp only [List.nil_append, unstuff]; simp_all
  | cons a q => simp only [List.cons_append, unstuff]; split <;> simp

theorem held_snoc_cr (q : List Byte) : held (q ++ [CR]) = q := by simp [held]

theorem held_snoc (q : List Byte) (x : Byte) (hx : x ≠ CR) : held (q ++ [x]) = q ++ [x] := by
  simp [held, hx]

theorem held_of_last (r : List Byte) (h : r.getLast? ≠ some CR) : held r = r := by
  simp [held, h]

theorem getLast_snoc_cr {r : List Byte} (h : r.getLast? = some CR) : r = r.dropLast ++ [CR] := by
  have hne : r ≠ [] := by rintro rfl; simp at h
  have e := List.dropLast_concat_getLast hne
  rw [List.getLast?_eq_some_getLast hne, Option.some.injEq] at h
  rw [h] at e; exact e.symm

/-- **A byte that does not end a line takes the state of the bytes before it to the state of the
bytes with it.** -/
theorem blockStep_abs (cap : Nat) (ls : List (List Byte)) (r : List Byte) (x : Byte)
    (hend : ¬ (r.getLast? = some CR ∧ x = LF)) :
    blockStep cap (absBlock cap ls r) x = (absBlock cap ls (r ++ [x]), none) := by
  by_cases h0 : r = []
  · subst h0
    by_cases hd : x = DOT
    · subst hd; simp [dot_ne_cr, cleanB_nil, cleanB_dot, mk_at, mk_phase, mk_bad, absBlock,
        blockStep, phaseOf, held, unstuff]
    by_cases hc : x = CR
    · subst hc; simp [cr_ne_dot, cleanB_nil, mk_at, mk_phase, mk_bad, absBlock, blockStep, phaseOf,
        held, unstuff]
    have hx : cleanB [x] = !spoils x := by
      simpa [hc] using cleanB_snoc [] x
    simp [cleanB_nil, mk_at, mk_phase, mk_bad, absBlock, blockStep, phaseOf, held, unstuff, hd,
        hc, put_mk, hx]
  by_cases h1 : r = [DOT]
  · subst h1
    by_cases hc : x = CR
    · subst hc; simp [dot_ne_cr, cleanB_dot, mk_at, mk_phase, mk_bad, absBlock, blockStep, phaseOf,
        held, unstuff]
    have hx : cleanB [DOT, x] = !spoils x := by
      simpa [hc] using cleanB_snoc [DOT] x
    simp [dot_ne_cr, cleanB_dot, mk_at, mk_phase, mk_bad, absBlock, blockStep, phaseOf, held,
        unstuff, hc, put_mk, hx]
  by_cases h2 : r = [DOT, CR]
  · subst h2
    have hlf : x ≠ LF := fun h => hend ⟨by simp, h⟩
    have hdc : cleanB [DOT, CR] = false := by decide
    by_cases hc : x = CR
    · subst hc
      simp [cr_ne_lf, cleanB_dot, mk_at, mk_phase, absBlock, blockStep, phaseOf, held,
          unstuff, put_mk, hdc]
    have e : cleanB [DOT, CR, x] = false := by
      simpa using cleanB_snoc [DOT, CR] x
    simp [cleanB_dot, mk_at, mk_phase, absBlock, blockStep, phaseOf, held, unstuff, hc,
        hlf, put_mk, e]
  have hsnoc : ∀ y, phaseOf (r ++ [y]) = if y = CR then .cr else .data := by
    intro y
    have e1 : r ++ [y] ≠ [] := by simp
    have e2 : r ++ [y] ≠ [DOT] := by
      intro h
      have := congrArg List.length h
      simp only [List.length_append, List.length_singleton] at this
      exact h0 (List.eq_nil_of_length_eq_zero (by omega))
    have e3 : r ++ [y] ≠ [DOT, CR] := by
      intro h
      have := (List.append_inj' (h.trans (show [DOT, CR] = [DOT] ++ [CR] from rfl)) rfl).1
      exact h1 this
    simp only [phaseOf, e1, e2, e3, if_false, List.getLast?_append, List.getLast?_singleton,
      Option.some_or, Option.some.injEq]
  by_cases h3 : r.getLast? = some CR
  · have hlf : x ≠ LF := fun h => hend ⟨h3, h⟩
    obtain ⟨q, rfl⟩ : ∃ q, r = q ++ [CR] := ⟨_, getLast_snoc_cr h3⟩
    have hph : phaseOf (q ++ [CR]) = .cr := by
      simp only [phaseOf, h0, h1, h2, if_false, h3, if_true]
    have hq : cleanB (q ++ [CR]) = false := by simp [cleanB_snoc]
    have e1 : unstuff (q ++ [CR]) = unstuff q ++ [CR] := unstuff_snoc q CR
        (Or.inr (by simp [cr_ne_dot]))
    have hs : absBlock cap ls (q ++ [CR]) =
        mk cap .cr (!(ls.all cleanB && cleanB q)) (content ls ++ unstuff q) := by
      simp only [absBlock, hph, held_snoc_cr]
    rw [hs]
    by_cases hc : x = CR
    · subst hc
      have ht : absBlock cap ls (q ++ [CR] ++ [CR]) = mk cap .cr true
          (content ls ++ unstuff q ++ [CR]) := by
        unfold absBlock
        rw [hsnoc, held_snoc_cr, e1, hq]
        simp
      rw [ht]
      simp [cr_ne_lf, mk_at, mk_phase, blockStep, put_mk]
    have e2 : unstuff (q ++ [CR] ++ [x]) = unstuff q ++ [CR] ++ [x] := by
      rw [unstuff_snoc _ x (Or.inl (by simp)), e1]
    have hq' : cleanB (q ++ [CR] ++ [x]) = false := by rw [cleanB_snoc, hq]; rfl
    have ht : absBlock cap ls (q ++ [CR] ++ [x]) =
        mk cap .data true (content ls ++ unstuff q ++ [CR] ++ [x]) := by
      unfold absBlock
      rw [hsnoc, held_snoc _ x hc, e2, hq']
      simp [hc]
    rw [ht]
    simp [mk_at, mk_phase, blockStep, put_mk, hc, hlf]
  · have hph : phaseOf r = .data := by simp only [phaseOf, h0, h1, h2, h3, if_false]
    have hheld : held r = r := held_of_last r h3
    have hs : absBlock cap ls r =
        mk cap .data (!(ls.all cleanB && cleanB r)) (content ls ++ unstuff r) := by
      simp only [absBlock, hph, hheld]
    rw [hs]
    by_cases hc : x = CR
    · subst hc
      have ht : absBlock cap ls (r ++ [CR]) =
          mk cap .cr (!(ls.all cleanB && cleanB r)) (content ls ++ unstuff r) := by
        unfold absBlock
        rw [hsnoc, held_snoc_cr]
        simp
      rw [ht]
      simp [mk_at, mk_phase, mk_bad, blockStep]
    have e : unstuff (r ++ [x]) = unstuff r ++ [x] := unstuff_snoc r x (Or.inl h0)
    have ht : absBlock cap ls (r ++ [x]) =
        mk cap .data (!(ls.all cleanB && cleanB r) || spoils x)
            (content ls ++ unstuff r ++ [x]) := by
      unfold absBlock
      rw [hsnoc, held_snoc _ x hc, e, cleanB_snoc]
      simp only [hc, if_false, decide_false, Bool.not_false, Bool.and_true, List.append_assoc]
      congr 1
      cases (ls.all cleanB) <;> cases (cleanB r) <;> cases (spoils x) <;> rfl
    rw [ht]
    simp [mk_at, mk_phase, mk_bad, blockStep, put_mk, hc]

/-- A prefix of a line without a CRLF has none either. -/
theorem unbroken_left {a b : List Byte} (h : Unbroken (a ++ b)) : Unbroken a :=
  fun h' => h (h'.trans (List.prefix_append a b).isInfix)

theorem allClean_iff (ls : List (List Byte)) : ls.all cleanB = true ↔ ∀ l ∈ ls, Clean l := by
  simp [List.all_eq_true, cleanB]

theorem content_snoc (ls : List (List Byte)) (q : List Byte) :
    content (ls ++ [q]) = content ls ++ unstuff q ++ CRLF := by
  simp [content]

/-- **The end of a line**: the lines read so far grow by one, or, when the line is a single dot,
the block ends with the specification's verdict. -/
theorem blockStep_crlf (cap : Nat) (ls : List (List Byte)) (q : List Byte) :
    blockStep cap (absBlock cap ls (q ++ [CR])) LF =
      if q = [DOT] then (.fresh, some (blockResult cap ls))
      else (absBlock cap (ls ++ [q]) [], none) := by
  by_cases hq : q = [DOT]
  · subst hq
    simp only [if_true]
    have hs : absBlock cap ls ([DOT] ++ [CR]) = mk cap .dotcr (!(ls.all cleanB)) (content ls) := by
      unfold absBlock
      rw [held_snoc_cr]
      simp [cleanB_dot, phaseOf, unstuff]
    rw [hs]
    simp only [blockStep, mk_phase, if_true, Prod.mk.injEq, true_and, Option.some.injEq]
    unfold result blockResult
    rw [mk_bad]
    by_cases hc : ls.all cleanB = true
    · have hc' := (allClean_iff ls).1 hc
      rw [if_pos hc']
      simp only [hc, Bool.not_true, Bool.false_eq_true, if_false, mk]
      by_cases hl : (content ls).length ≤ cap
      · rw [if_neg (by omega), if_pos hl, List.take_of_length_le hl]
      · rw [if_pos (by omega), if_neg hl]
    · have hc' : ¬ ∀ l ∈ ls, Clean l := fun h => hc ((allClean_iff ls).2 h)
      rw [if_neg hc']
      simp [hc]
  · simp only [hq, if_false]
    have hph : phaseOf (q ++ [CR]) = .cr := by
      have e1 : q ++ [CR] ≠ [] := by simp
      have e2 : q ++ [CR] ≠ [DOT] := by
        intro h
        have := (List.append_inj' (h.trans (show [DOT] = [] ++ [DOT] from rfl)) rfl).2
        simp [cr_ne_dot] at this
      have e3 : q ++ [CR] ≠ [DOT, CR] := by
        intro h
        exact hq (List.append_inj' (h.trans (show [DOT, CR] = [DOT] ++ [CR] from rfl)) rfl).1
      simp [phaseOf, e1, e2, e3]
    simp only [blockStep, absBlock, hph, mk_phase, if_true, held_snoc_cr, put_mk, mk_bad, mk_at,
      Prod.mk.injEq, and_true]
    simp [cleanB_nil, phaseOf, held, content_snoc, CRLF, List.all_append, unstuff]

/-- Bytes that do not break the line being read extend it, and the block goes on. -/
theorem feedBlock_on (cap : Nat) (ls : List (List Byte)) (r q more : List Byte)
    (h : Unbroken (r ++ q)) :
    feedBlock cap (absBlock cap ls r) (q ++ more) =
      let t := feedBlock cap (absBlock cap ls (r ++ q)) more
      (q.length + t.1, t.2.1, t.2.2) := by
  induction q generalizing r with
  | nil => simp
  | cons x q ih =>
    have h1 : Unbroken (r ++ [x]) := unbroken_left (by simpa using h)
    have hend := ((unbroken_snoc r x).1 h1).2
    have h2 : Unbroken (r ++ [x] ++ q) := by simpa using h
    simp only [List.cons_append, feedBlock, blockStep_abs cap ls r x hend]
    rw [ih (r ++ [x]) h2]
    simp only [List.append_assoc, List.singleton_append, List.length_cons, Prod.mk.injEq, and_true]
    omega

/-- The lines of a block and the line with the single dot, from a state that has read `ls0`. -/
theorem feedBlock_lines (cap : Nat) (ls0 ls : List (List Byte)) (rest : List Byte)
    (hls : ∀ l ∈ ls, Unbroken l ∧ l ≠ [DOT]) :
    feedBlock cap (absBlock cap ls0 []) (((ls ++ [[DOT]]).map (· ++ CRLF)).flatten ++ rest) =
      ((((ls ++ [[DOT]]).map (· ++ CRLF)).flatten).length, .fresh,
        some (blockResult cap (ls0 ++ ls))) := by
  induction ls generalizing ls0 with
  | nil =>
    have hu : Unbroken ([] ++ [DOT, CR]) := by decide
    have := feedBlock_on cap ls0 [] [DOT, CR] (LF :: rest) hu
    simp only [List.nil_append, List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil,
      List.append_nil, List.cons_append, CRLF] at this ⊢
    rw [this]
    have e := blockStep_crlf cap ls0 [DOT]
    simp only [List.singleton_append, if_true] at e
    simp [feedBlock, e]
  | cons l more ih =>
    have hl := hls l (by simp)
    have hmore : ∀ l ∈ more, Unbroken l ∧ l ≠ [DOT] := fun l' h => hls l' (by simp [h])
    have hu : Unbroken ([] ++ (l ++ [CR])) := by
      simpa using (unbroken_snoc l CR).2 ⟨hl.1, by simp [cr_ne_lf]⟩
    have := feedBlock_on cap ls0 [] (l ++ [CR])
      (LF :: ((((more ++ [[DOT]]).map (· ++ CRLF)).flatten) ++ rest)) hu
    simp only [List.cons_append, List.map_cons, List.flatten_cons, List.append_assoc, CRLF,
      List.nil_append] at this ⊢
    rw [this]
    have e := blockStep_crlf cap ls0 l
    simp only [hl.2, if_false] at e
    simp only [feedBlock, e]
    have := ih (ls0 ++ [l]) hmore
    simp only [CRLF] at this
    rw [this]
    simp [List.append_assoc]
    omega

/-- **A whole block gives the specification's verdict, and the framer reads exactly the block.** -/
theorem feedBlock_block (cap : Nat) {s : List Byte} {ls : List (List Byte)} {rest : List Byte}
    (h : Block s ls rest) :
    feedBlock cap .fresh s = (s.length - rest.length, .fresh, some (blockResult cap ls)) := by
  obtain ⟨rfl, hls⟩ := h
  have := feedBlock_lines cap [] ls rest hls
  rw [absBlock_nil] at this
  rw [this]
  simp
  omega

/-- **A block that has not ended leaves the state of its lines and its unfinished line.** -/
theorem feedBlock_open (cap : Nat) {s : List Byte} {ls : List (List Byte)} {r : List Byte}
    (h : Open s ls r) : feedBlock cap .fresh s = (s.length, absBlock cap ls r, none) := by
  obtain ⟨rfl, hls, hr⟩ := h
  rw [← absBlock_nil cap]
  suffices ∀ ls0, feedBlock cap (absBlock cap ls0 []) ((ls.map (· ++ CRLF)).flatten ++ r) =
      (((ls.map (· ++ CRLF)).flatten ++ r).length, absBlock cap (ls0 ++ ls) r, none) by
    simpa using this []
  induction ls with
  | nil =>
    intro ls0
    have := feedBlock_on cap ls0 [] r [] (by simpa using hr)
    simp only [List.append_nil, List.nil_append] at this
    simp [this, feedBlock]
  | cons l more ih =>
    intro ls0
    have hl := hls l (by simp)
    have hmore : ∀ l ∈ more, Unbroken l ∧ l ≠ [DOT] := fun l' h => hls l' (by simp [h])
    have hu : Unbroken ([] ++ (l ++ [CR])) := by
      simpa using (unbroken_snoc l CR).2 ⟨hl.1, by simp [cr_ne_lf]⟩
    have := feedBlock_on cap ls0 [] (l ++ [CR]) (LF :: ((more.map (· ++ CRLF)).flatten ++ r)) hu
    simp only [List.cons_append, List.map_cons, List.flatten_cons, List.append_assoc, CRLF,
      List.nil_append] at this ⊢
    rw [this]
    have e := blockStep_crlf cap ls0 l
    simp only [hl.2, if_false] at e
    simp only [feedBlock, e]
    have := ih hmore (ls0 ++ [l])
    simp only [CRLF] at this
    rw [this]
    simp [List.append_assoc]
    omega

/-- **Chunks**: a block read in two pieces is the block read at once; the state carries across. -/
theorem feedBlock_append (cap : Nat) (s : BlockState) (a b : List Byte) :
    feedBlock cap s (a ++ b) =
      let r := feedBlock cap s a
      match r.2.2 with
      | some v => (r.1, r.2.1, some v)
      | none =>
        let t := feedBlock cap r.2.1 b
        (r.1 + t.1, t.2.1, t.2.2) := by
  induction a generalizing s with
  | nil => simp [feedBlock]
  | cons x a ih =>
    simp only [List.cons_append, feedBlock]
    split
    · rfl
    · rename_i s' _
      rw [ih s']
      simp only
      split <;> simp_all <;> omega

/-! ### The block step as the program takes it

The program decides first, from the phase and the byte alone, whether to hold a CR and whether to
hold the byte, and what the phase and the verdict so far become; then it holds those bytes. -/

/-- What one byte does: the CR held back is held (`pre`), the byte is held (`post`), the phase and
the verdict so far that follow, and whether the block ends here. -/
structure Plan where
  pre : Bool
  post : Bool
  phase : Phase
  bad : Bool
  ends : Bool
  deriving DecidableEq, Repr

def plan (s : BlockState) (x : Byte) : Plan :=
  match s.phase with
  | .bol =>
    if x = DOT then ⟨false, false, .dot, s.bad, false⟩
    else if x = CR then ⟨false, false, .cr, s.bad, false⟩
    else ⟨false, true, .data, s.bad || spoils x, false⟩
  | .data =>
    if x = CR then ⟨false, false, .cr, s.bad, false⟩
    else ⟨false, true, .data, s.bad || spoils x, false⟩
  | .cr =>
    if x = LF then ⟨true, true, .bol, s.bad, false⟩
    else if x = CR then ⟨true, false, .cr, true, false⟩
    else ⟨true, true, .data, true, false⟩
  | .dot =>
    if x = CR then ⟨false, false, .dotcr, s.bad, false⟩
    else ⟨false, true, .data, s.bad || spoils x, false⟩
  | .dotcr =>
    if x = LF then ⟨false, false, .bol, false, true⟩
    else if x = CR then ⟨true, false, .cr, true, false⟩
    else ⟨true, true, .data, true, false⟩

/-- Hold a byte when asked to. -/
def putIf (cap : Nat) (f : Bool) (s : BlockState) (x : Byte) : BlockState :=
  if f then put cap s x else s

theorem putIf_bad (cap : Nat) (f : Bool) (s : BlockState) (x : Byte) :
    (putIf cap f s x).bad = s.bad := by
  unfold putIf put; split <;> (try split) <;> rfl

theorem putIf_phase (cap : Nat) (f : Bool) (s : BlockState) (x : Byte) :
    (putIf cap f s x).phase = s.phase := by
  unfold putIf put; split <;> (try split) <;> rfl

/-- **The step is the plan carried out**: the bytes held, then the phase and the verdict so far;
or, at the end of the block, the verdict. -/
theorem blockStep_plan (cap : Nat) (s : BlockState) (x : Byte) :
    blockStep cap s x =
      if (plan s x).ends then (.fresh, some (result cap s))
      else ((putIf cap (plan s x).post (putIf cap (plan s x).pre s CR) x).at
        (plan s x).phase (plan s x).bad, none) := by
  unfold blockStep plan
  split <;> simp only [putIf] <;> (repeat' split) <;> simp_all [cr_ne_dot, cr_ne_lf]

/-! ### Where a block call stops -/

theorem feedBlock_len (cap : Nat) :
    ∀ (s : BlockState) (q : List Byte), (feedBlock cap s q).1 ≤ q.length := by
  intro s q
  induction q generalizing s with
  | nil => simp [feedBlock]
  | cons x rest ih =>
    rcases h : blockStep cap s x with ⟨s', _ | v⟩
    · simp only [feedBlock, h, List.length_cons]; have := ih s'; omega
    · simp [feedBlock, h]

/-- Before the end of the block, a call on a prefix reads it all and gives no verdict. -/
theorem feedBlock_quiet (cap : Nat) :
    ∀ (s : BlockState) (q : List Byte) (k : Nat), k < (feedBlock cap s q).1 →
      (feedBlock cap s (q.take k)).1 = k ∧ (feedBlock cap s (q.take k)).2.2 = none := by
  intro s q
  induction q generalizing s with
  | nil => intro k hk; simp [feedBlock] at hk
  | cons x rest ih =>
    intro k hk
    cases k with
    | zero => simp [feedBlock]
    | succ k =>
      rcases h : blockStep cap s x with ⟨s', _ | v⟩
      · simp only [feedBlock, h] at hk
        have := ih s' k (by omega)
        simp only [List.take_succ_cons, feedBlock, h]
        exact ⟨by omega, this.2⟩
      · simp [feedBlock, h] at hk

/-- A call that stops before the end of what it was given stopped at the end of the block. -/
theorem feedBlock_short (cap : Nat) :
    ∀ (s : BlockState) (q : List Byte), (feedBlock cap s q).1 < q.length →
      (feedBlock cap s q).2.2.isSome := by
  intro s q
  induction q generalizing s with
  | nil => simp [feedBlock]
  | cons x rest ih =>
    intro h
    rcases hs : blockStep cap s x with ⟨s', _ | v⟩
    · simp only [feedBlock, hs, List.length_cons] at h ⊢
      exact ih s' (by omega)
    · simp [feedBlock, hs]

/-- A call on the bytes up to where it stops is the call. -/
theorem feedBlock_take (cap : Nat) :
    ∀ (s : BlockState) (q : List Byte),
      feedBlock cap s (q.take (feedBlock cap s q).1) = feedBlock cap s q := by
  intro s q
  induction q generalizing s with
  | nil => simp [feedBlock]
  | cons x rest ih =>
    rcases hs : blockStep cap s x with ⟨s', _ | v⟩
    · simp only [feedBlock, hs, List.take_succ_cons]
      rw [ih s']
    · simp [feedBlock, hs]

/-- One more byte of a prefix that has not ended the block is one step. -/
theorem feedBlock_take_succ (cap : Nat) (s : BlockState) (q : List Byte) (k : Nat)
    (hk : k < (feedBlock cap s q).1) (hkq : k < q.length) :
    feedBlock cap s (q.take (k + 1)) =
      let f := feedBlock cap s (q.take k)
      let r := blockStep cap f.2.1 q[k]
      (k + 1, r.1, r.2) := by
  obtain ⟨h1, h2⟩ := feedBlock_quiet cap s q k hk
  rw [List.take_add_one, List.getElem?_eq_getElem hkq, Option.toList_some, feedBlock_append]
  simp only [h2, h1]
  rcases hr : blockStep cap (feedBlock cap s (List.take k q)).2.1 q[k] with ⟨s', _ | v⟩ <;>
    simp [feedBlock, hr]

/-- A verdict comes only at the end of a block, and it is the state's. -/
theorem blockStep_some (cap : Nat) (s : BlockState) (x : Byte) (v : BlockResult)
    (h : (blockStep cap s x).2 = some v) : v = result cap s ∧ (blockStep cap s x).1 = .fresh := by
  rw [blockStep_plan] at h ⊢
  split at h
  · simp at h; exact ⟨h.symm, by rename_i he; simp [he]⟩
  · simp at h

/-! ### Every rule matters, for blocks too -/

inductive BlockMutant
  | none
  /-- a dot and a bare LF end the block, as some readers take them -/
  | dotBareLF
  /-- a bare LF ends a line -/
  | bareLFLine
  /-- the dot a sender put before a line is kept -/
  | keepStuffing
  /-- a CR inside a line does not spoil the block -/
  | crAllowed
  /-- a NUL does not spoil the block -/
  | nulAllowed
  /-- a block of exactly the buffer's size is taken for too large -/
  | limitOffByOne
  /-- a block both spoiled and too large is called too large -/
  | tooLargeFirst
  /-- an LF inside a line does not spoil the block -/
  | lfAllowed
  /-- the CRLF that ends a line is not held -/
  | dropLineEnd
  deriving DecidableEq, Repr

def resultM (m : BlockMutant) (cap : Nat) (s : BlockState) : BlockResult :=
  if m = .tooLargeFirst ∧ cap < s.size then ⟨.tooLarge, []⟩
  else if s.bad then ⟨.refused, []⟩
  else if (if m = .limitOffByOne then cap ≤ s.size else cap < s.size) then ⟨.tooLarge, []⟩
  else ⟨.accepted, s.buf⟩

def spoilsM (m : BlockMutant) (x : Byte) : Bool :=
  (decide (x = LF) && m ≠ .lfAllowed) || (decide (x = NUL) && m ≠ .nulAllowed)

def blockStepM (m : BlockMutant) (cap : Nat) (s : BlockState) (x : Byte) :
    BlockState × Option BlockResult :=
  match s.phase with
  | .bol =>
    if x = DOT then (s.at .dot s.bad, none)
    else if x = CR then (s.at .cr s.bad, none)
    else ((put cap s x).at .data (s.bad || spoilsM m x), none)
  | .data =>
    if x = CR then (s.at .cr s.bad, none)
    else if x = LF ∧ m = .bareLFLine then ((put cap (put cap s CR) LF).at .bol s.bad, none)
    else ((put cap s x).at .data (s.bad || spoilsM m x), none)
  | .cr =>
    if x = LF then
      (if m = .dropLineEnd then s.at .bol s.bad
        else (put cap (put cap s CR) LF).at .bol s.bad, none)
    else if x = CR then ((put cap s CR).at .cr (s.bad || m ≠ .crAllowed), none)
    else ((put cap (put cap s CR) x).at .data (s.bad || m ≠ .crAllowed), none)
  | .dot =>
    if x = CR then (s.at .dotcr s.bad, none)
    else if x = LF ∧ m = .dotBareLF then (.fresh, some (resultM m cap s))
    else if m = .keepStuffing then
      ((put cap (put cap s DOT) x).at .data (s.bad || spoilsM m x), none)
    else ((put cap s x).at .data (s.bad || spoilsM m x), none)
  | .dotcr =>
    if x = LF then (.fresh, some (resultM m cap s))
    else if x = CR then ((put cap s CR).at .cr (s.bad || m ≠ .crAllowed), none)
    else ((put cap (put cap s CR) x).at .data (s.bad || m ≠ .crAllowed), none)

def feedBlockM (m : BlockMutant) (cap : Nat) : BlockState → List Byte →
    Nat × BlockState × Option BlockResult
  | s, [] => (0, s, none)
  | s, x :: rest =>
    match blockStepM m cap s x with
    | (s', some v) => (1, s', some v)
    | (s', none) =>
      let t := feedBlockM m cap s' rest
      (t.1 + 1, t.2.1, t.2.2)

theorem blockStepM_none : blockStepM .none = blockStep := by
  funext cap s x
  simp only [blockStepM, blockStep, resultM, result, spoilsM, spoils]
  split <;> simp

theorem feedBlockM_none : feedBlockM .none = feedBlock := by
  funext cap s q
  induction q generalizing s with
  | nil => rfl
  | cons x rest ih => simp only [feedBlockM, feedBlock, blockStepM_none, ih]

/-- A block that tells the mutant from the framer, for a buffer of four bytes. -/
def blockWitness : BlockMutant → List Byte
  | .none => []
  | .dotBareLF => [46#8, 10#8, 46#8, 13#8, 10#8]
  | .bareLFLine => [65#8, 10#8, 46#8, 13#8, 10#8]
  | .keepStuffing => [46#8, 46#8, 13#8, 10#8, 46#8, 13#8, 10#8]
  | .crAllowed => [65#8, 13#8, 65#8, 13#8, 10#8, 46#8, 13#8, 10#8]
  | .nulAllowed => [0#8, 13#8, 10#8, 46#8, 13#8, 10#8]
  | .limitOffByOne => [65#8, 66#8, 13#8, 10#8, 46#8, 13#8, 10#8]
  | .tooLargeFirst => [0#8, 65#8, 65#8, 65#8, 13#8, 10#8, 46#8, 13#8, 10#8]
  | .lfAllowed => [65#8, 10#8, 13#8, 10#8, 46#8, 13#8, 10#8]
  | .dropLineEnd => [65#8, 13#8, 10#8, 46#8, 13#8, 10#8]

/-- **Each broken rule changes the answer on its block.** -/
theorem blockMutants_differ : ∀ m, m ≠ .none →
    feedBlockM m 4 .fresh (blockWitness m) ≠ feedBlock 4 .fresh (blockWitness m) := by
  intro m hm
  cases m <;> first | exact absurd rfl hm | decide

end DN.News.Framer
