-- SPDX-License-Identifier: AGPL-3.0-or-later
import DN.News.FrameSpec

/-!
# DN.News.SipHash

SipHash-2-4 with a tag of 64 bits, as J.-P. Aumasson and D. J. Bernstein define it ("SipHash: a
fast short-input PRF", INDOCRYPT 2012): a key of sixteen octets, a message of any length taken
eight octets at a time, least significant first, two rounds for each block and four to finish.
-/

namespace DN.News.SipHash

open DN.News.FrameSpec (Byte)

abbrev Bytes := List Byte

/-- `x` rotated left by `b` bits. -/
def rotl (x b : UInt64) : UInt64 := (x <<< b) ||| (x >>> (64 - b))

structure State where
  v0 : UInt64
  v1 : UInt64
  v2 : UInt64
  v3 : UInt64

/-- One SipRound. -/
def sipRound (s : State) : State :=
  let v0 := s.v0 + s.v1
  let v1 := rotl s.v1 13 ^^^ v0
  let v0 := rotl v0 32
  let v2 := s.v2 + s.v3
  let v3 := rotl s.v3 16 ^^^ v2
  let v0 := v0 + v3
  let v3 := rotl v3 21 ^^^ v0
  let v2 := v2 + v1
  let v1 := rotl v1 17 ^^^ v2
  let v2 := rotl v2 32
  ⟨v0, v1, v2, v3⟩

/-- Octets as a word, least significant first. -/
def word (bs : Bytes) : UInt64 := bs.foldr (fun b acc => (acc <<< 8) ||| b.toNat.toUInt64) 0

/-- A block into the state: two rounds between the word's two uses. -/
def compress (s : State) (m : UInt64) : State :=
  let s := sipRound (sipRound { s with v3 := s.v3 ^^^ m })
  { s with v0 := s.v0 ^^^ m }

/-- The message's whole blocks into the state, and the octets left, fewer than eight. -/
def absorb : State → Bytes → State × Bytes
  | s, b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: rest =>
    absorb (compress s (word [b0, b1, b2, b3, b4, b5, b6, b7])) rest
  | s, rest => (s, rest)

/-- SipHash-2-4 of `msg` under the key `k0 ‖ k1`. The last block holds the octets left and, in its
top octet, the message's length modulo 256. -/
def siphash (k0 k1 : UInt64) (msg : Bytes) : UInt64 :=
  let s : State := ⟨k0 ^^^ 0x736f6d6570736575, k1 ^^^ 0x646f72616e646f6d,
    k0 ^^^ 0x6c7967656e657261, k1 ^^^ 0x7465646279746573⟩
  let (s, rest) := absorb s msg
  let s := compress s ((msg.length.toUInt64 <<< 56) ||| word rest)
  let s := sipRound (sipRound (sipRound (sipRound { s with v2 := s.v2 ^^^ 0xff })))
  s.v0 ^^^ s.v1 ^^^ s.v2 ^^^ s.v3

/-- The tag of `msg` under a key of sixteen octets, its halves least significant first. -/
def tag (key msg : Bytes) : UInt64 := siphash (word (key.take 8)) (word ((key.drop 8).take 8)) msg

end DN.News.SipHash
