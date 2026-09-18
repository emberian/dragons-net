/-! A small framing specification seed: CRLF detection across arbitrary chunks.
This recognizes delimiters only. Command length/error recovery, article
dot-transparency, and a concrete buffer implementation remain separate work. -/

namespace DN.News.Framing

structure State where
  previousCR : Bool := false
  delimiters : Nat := 0
deriving DecidableEq, Repr

def step (s : State) (byte : UInt8) : State :=
  { previousCR := byte == 13
    delimiters := s.delimiters + if s.previousCR && byte == 10 then 1 else 0 }

def feed (s : State) (bytes : List UInt8) : State := bytes.foldl step s

/-- Transport chunk boundaries cannot change the delimiter count or carry state. -/
theorem feed_append (s : State) (a b : List UInt8) :
    feed s (a ++ b) = feed (feed s a) b := by
  simp [feed, List.foldl_append]

theorem split_crlf :
    feed (feed {} [13]) [10] = { previousCR := false, delimiters := 1 } := by decide

theorem bare_lf_is_not_crlf : (feed {} [10]).delimiters = 0 := by decide

theorem repeated_cr_retains_last : (feed {} [13, 13, 10]).delimiters = 1 := by decide

end DN.News.Framing
