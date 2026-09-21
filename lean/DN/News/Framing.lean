-- SPDX-License-Identifier: AGPL-3.0-or-later

/-!
# DN.News.Framing

A framing seed: counting CRLF delimiters across arbitrary transport chunks.

`crlfFrom` is the specification, written from the delimiter grammar; `feed` is
the implementation, a left fold over the bytes; `feed_counts_crlf` is the bridge.
Chunk invariance (`feed_append`) holds for *any* left fold, so it is a property
of the shape, not evidence that the counter counts CRLF — that is what the
specification is for, and `feedBad` is a counter that satisfies the one and
violates the other.

What this does not do, all of it still open for RFC 3977 parsing: line
boundaries and their contents (the counter keeps no positions, so no command can
be extracted), the 512-octet line limit (§3.1), the ban on NUL and on bare CR or
LF inside blocks (§3.1.1), dot-stuffing and the `.CRLF` terminator (§3.1.1),
UTF-8 (§3.1), end of input mid-line, and recovery after an overlong line
(§3.2.1).
-/

namespace DN.News.Framing

structure State where
  previousCR : Bool := false
  delimiters : Nat := 0
deriving DecidableEq, Repr

def step (s : State) (byte : UInt8) : State :=
  { previousCR := byte == 13
    delimiters := s.delimiters + if s.previousCR && byte == 10 then 1 else 0 }

def feed (s : State) (bytes : List UInt8) : State := bytes.foldl step s

/-- Transport chunk boundaries cannot change the delimiter count or carry state.
True for every left fold, including a wrong one: see `feedBad_append`. -/
theorem feed_append (s : State) (a b : List UInt8) :
    feed s (a ++ b) = feed (feed s a) b := by
  simp [feed, List.foldl_append]

/-- How many CRLF pairs a byte list carries, given whether the byte before it
was CR. The carry makes the induction go through; `crlfPairs` below is the same
count written without one, and `crlfCount_eq_pairs` connects them. -/
def crlfFrom : Bool → List UInt8 → Nat
  | _, [] => 0
  | prev, b :: rest => (if prev && b == 10 then 1 else 0) + crlfFrom (b == 13) rest

/-- The CRLF count of a byte list read from the start of a stream. -/
def crlfCount (l : List UInt8) : Nat := crlfFrom false l

/-- The same count with no carried state at all: how many adjacent byte pairs
are CR followed by LF. This is the form to read as the specification — it shares
no structure with the implementation's fold. -/
def crlfPairs (l : List UInt8) : Nat :=
  ((l.zip l.tail).filter (fun p => p.1 == 13 && p.2 == 10)).length

theorem crlfPairs_cons (b : UInt8) (rest : List UInt8) :
    crlfPairs (b :: rest)
      = (if b == 13 && rest.head? == some 10 then 1 else 0) + crlfPairs rest := by
  cases rest with
  | nil => simp [crlfPairs]
  | cons c rest' =>
      by_cases h : b == 13 && c == 10
      · simp [crlfPairs, h]; omega
      · simp [crlfPairs, h]

/-- The stateful count and the pair count agree, carry included. -/
theorem crlfFrom_eq_pairs : ∀ (l : List UInt8) (prev : Bool),
    crlfFrom prev l = (if prev && l.head? == some 10 then 1 else 0) + crlfPairs l := by
  intro l
  induction l with
  | nil => intro prev; simp [crlfFrom, crlfPairs]
  | cons b rest ih =>
      intro prev
      rw [crlfPairs_cons]
      show (if prev && b == 10 then 1 else 0) + crlfFrom (b == 13) rest = _
      rw [ih (b == 13)]
      simp [List.head?_cons]

/-- **The two specifications are the same count.** -/
theorem crlfCount_eq_pairs (l : List UInt8) : crlfCount l = crlfPairs l := by
  simpa [crlfCount] using crlfFrom_eq_pairs l false

/-- The implementation counts the specification, carrying the CR flag across the
fold; the second conjunct is what makes the induction go through. -/
theorem feed_spec : ∀ (l : List UInt8) (s : State),
    (feed s l).delimiters = s.delimiters + crlfFrom s.previousCR l ∧
    (feed s l).previousCR = l.foldl (fun _ b => b == 13) s.previousCR := by
  intro l
  induction l with
  | nil => intro s; simp [feed, crlfFrom]
  | cons b rest ih =>
    intro s
    have h := ih (step s b)
    refine ⟨?_, ?_⟩
    · show (feed (step s b) rest).delimiters = _
      rw [h.1]
      show s.delimiters + (if s.previousCR && b == 10 then 1 else 0)
          + crlfFrom (step s b).previousCR rest = _
      simp [crlfFrom, step, Nat.add_assoc]
    · show (feed (step s b) rest).previousCR = _
      rw [h.2]
      rfl

/-- **The delimiter counter is the CRLF counter**: implementation equals
specification on every input. -/
theorem feed_counts_crlf (l : List UInt8) : (feed {} l).delimiters = crlfCount l := by
  simpa [crlfCount] using (feed_spec l {}).1

/-! ## The specification is load-bearing

`feedBad` counts every LF, CR or not. It satisfies chunk invariance exactly as
`feed` does, and fails the specification on the first bare LF. -/

def stepBad (s : State) (byte : UInt8) : State :=
  { previousCR := byte == 13, delimiters := s.delimiters + if byte == 10 then 1 else 0 }

def feedBad (s : State) (bytes : List UInt8) : State := bytes.foldl stepBad s

theorem feedBad_append (s : State) (a b : List UInt8) :
    feedBad s (a ++ b) = feedBad (feedBad s a) b := by
  simp [feedBad, List.foldl_append]

theorem feedBad_violates_spec : (feedBad {} [10]).delimiters ≠ crlfCount [10] := by decide

theorem split_crlf :
    feed (feed {} [13]) [10] = { previousCR := false, delimiters := 1 } := by decide

theorem bare_lf_is_not_crlf : (feed {} [10]).delimiters = 0 := by decide

theorem repeated_cr_retains_last : (feed {} [13, 13, 10]).delimiters = 1 := by decide

end DN.News.Framing
