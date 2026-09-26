-- SPDX-License-Identifier: AGPL-3.0-or-later
import Lean.Data.Json
import DN.Dsl.Correct

/-!
# DN.Dsl.Example

A reply table written in the language and emitted as `dn_reply`. Keywords are matched as exact
byte prefixes, so this exercises the language and is not an NNTP command parser: NNTP commands
are case-insensitive and end at a word boundary, and neither is expressed here. The third
keyword is not text: its bytes above `0x7f` and its NUL are what tell a byte load that extends
with zeros from one that extends the sign.
-/

namespace DN.Dsl.Example

open DN.Compiler DN.Compiler.Syntax DN.Compiler.Lower DN.Compiler.Bytes Lean

def replies : Act :=
  .ifPrefix (ascii "QUIT") (.lit (ascii "205 closing connection\r\n"))
    (.ifPrefix (ascii "MODE READER") (.lit (ascii "201 reader mode, posting prohibited\r\n"))
      (.ifPrefix [0xc8, 0x80, 0xff, 0x00] (.lit (ascii "501 not text\r\n"))
        (.seq
          (.ifPrefix (ascii "HELP") (.lit (ascii "100 help text follows\r\n."))
            (.lit (ascii "500 unknown command")))
          (.lit (ascii "\r\n")))))

def name : String := "dn_reply"

/-! ## The inputs the native check runs -/

def Act.keywords : Act → List (List (BitVec 8))
  | .lit _ => []
  | .ifPrefix keyword thn els => keyword :: (Act.keywords thn ++ Act.keywords els)
  | .seq first second => Act.keywords first ++ Act.keywords second

/-- Around a keyword: every prefix of it, the keyword with more after it and after a space, and
the keyword with one byte changed — by the ASCII case bit, the high bit or the lowest bit. -/
def around (keyword : List (BitVec 8)) : List (List (BitVec 8)) :=
  (List.range (keyword.length + 1)).map keyword.take ++
  [keyword ++ ascii "\r\n", keyword ++ ascii " x", ascii " " ++ keyword] ++
  (List.range keyword.length).flatMap fun i =>
    [0x20, 0x80, 0x01].map fun bit => keyword.set i (keyword[i]! ^^^ bit)

def step (x : Nat) : Nat := (x * 6364136223846793005 + 1442695040888963407) % 2 ^ 64

/-- Pseudo-random inputs of up to sixteen bytes over the keywords' bytes and a few others. -/
def scattered (count : Nat) : List (List (BitVec 8)) :=
  let alphabet := (Act.keywords replies).flatten ++ ascii " \r\nq" ++ [0, 0xff]
  (List.range count).map fun i =>
    let seed := step (step i)
    (List.range (seed >>> 40 % 17)).map fun j => alphabet[(step (seed + j) >>> 33) % alphabet.length]!

def inputs : List (List (BitVec 8)) :=
  ((Act.keywords replies).flatMap around ++ (List.range 256).map (fun b => [BitVec.ofNat 8 b]) ++
    scattered 256).eraseDups

/-- What `Act.run` makes of every input, for the native check. -/
def cases : Json :=
  let bytes (bs : List (BitVec 8)) := toJson (bs.map BitVec.toNat)
  Json.mkObj [("function", toJson name), ("max_len", toJson replies.maxLen),
    ("cases", Json.arr (inputs.map fun inp =>
      Json.mkObj [("input", bytes inp), ("output", bytes (replies.run inp []))]).toArray)]

def regression_701 : Bool := (emit name replies).isOk
def regression_702 : Bool :=
  replies.run (ascii "QUIT\r\n") [] == ascii "205 closing connection\r\n"
def regression_703 : Bool :=
  replies.run (ascii "MODE READER\r\n") [] == ascii "201 reader mode, posting prohibited\r\n"
def regression_704 : Bool := replies.run (ascii "HELP") [] == ascii "100 help text follows\r\n.\r\n"
-- One byte short of a keyword, and a keyword in lower case, are unknown commands.
def regression_705 : Bool := replies.run (ascii "MODE READE") [] == ascii "500 unknown command\r\n"
def regression_706 : Bool := replies.run (ascii "quit") [] == ascii "500 unknown command\r\n"
-- The inputs reach every keyword boundary, and the buffer the function asks for is filled.
def regression_707 : Bool :=
  (Act.keywords replies).all fun k =>
    (List.range (k.length + 1)).all (fun i => inputs.contains (k.take i)) &&
      inputs.contains (k ++ ascii "\r\n") &&
      (List.range k.length).all fun i => inputs.contains (k.set i (k[i]! ^^^ 0x01))
def regression_708 : Bool :=
  replies.maxLen == (inputs.map fun inp => (replies.run inp []).length).foldl max 0

-- The two actions `emit` refuses. Neither is built: the lists are far too long to exist.
theorem emit_refuses_a_long_reply :
    emit name (.lit (List.replicate refusal 0)) = .error "reply may not fit the 32-bit result" := by
  have h1 : (Act.lit (List.replicate refusal 0)).fitsB = true := rfl
  have h2 : refusal ≤ (Act.lit (List.replicate refusal 0)).maxLen := by
    simp only [Act.maxLen, List.length_replicate, Nat.le_refl]
  unfold emit
  rw [h1, if_neg (by decide), if_pos h2]

theorem emit_refuses_a_long_keyword :
    emit name (.ifPrefix (List.replicate (2 ^ 63) 0) (.lit []) (.lit []))
      = .error "keyword too long for a signed length comparison" := by
  have h1 : (Act.ifPrefix (List.replicate (2 ^ 63) 0) (.lit []) (.lit [])).fitsB = false := by
    simp only [Act.fitsB, List.length_replicate, Nat.lt_irrefl, decide_false, Bool.false_and]
  unfold emit
  rw [h1, if_pos (by decide)]

/-! ## The premises hold of a concrete call in the model -/

/-- `QUIT` in the last four bytes before 4096, and room for the longest reply from 4096 on. -/
def quitCall : PancakeState Unit :=
  { locals := fun x => if x = "inp" then some 4092 else if x = "inlen" then some 4
      else if x = "out" then some 4096 else if x = "cap" then some 37 else none,
    memory := fun a => if a = 4088 then 0x5449555100000000 else 0,
    memaddrs := fun a => a == 4088 || (decide (4096 ≤ a.toNat) && decide (a.toNat < 4136)),
    be := false, clock := 0, ffi := (), baseAddr := 0 }

def noCalls : Oracle Unit := ⟨fun st _ _ array => .ret st array⟩

theorem replies_fits : replies.Fits := Act.fits_of_fitsB replies (by decide)

theorem quitCall_input :
    memBytesAt quitCall.memory quitCall.memaddrs quitCall.be 4092 (ascii "QUIT") := by
  have h : ∀ i, i < 4 → memLoadByte quitCall.memory quitCall.memaddrs quitCall.be
      (4092 + BitVec.ofNat 64 i) = some ((ascii "QUIT")[i]!) := by
    decide
  intro i hi
  exact h i (by simpa [ascii] using hi)

theorem quitCall_room :
    ∀ j, j < 37 → quitCall.memaddrs (byteAlign (4096 + BitVec.ofNat 64 j)) = true := by
  decide

theorem quitCall_apart : ∀ i j, i < (ascii "QUIT").length → j < 37 →
    (4092 : Word) + BitVec.ofNat 64 i ≠ 4096 + BitVec.ofNat 64 j := by
  have h : ∀ i, i < 4 → ∀ j, j < 37 →
      (4092 : Word) + BitVec.ofNat 64 i ≠ 4096 + BitVec.ofNat 64 j := by
    decide
  intro i j hi hj
  exact h i (by simpa [ascii] using hi) j hj

theorem quitCall_rep : Rep 4092 4096 (ascii "QUIT") 37 0 [] (entryState quitCall) :=
  Rep.entry rfl rfl rfl quitCall_input quitCall_room quitCall_apart (by decide) (by decide)

theorem quitCall_keeps : Keeps 4096 0 quitCall quitCall := Keeps.refl 4096 0 quitCall

/-- The whole call: `dn_reply` on `QUIT` returns 24 with the reply at 4096. -/
theorem quitCall_reply :
    ∃ c t, lower (respond name replies) = some c ∧
      PancakeSem noCalls c quitCall = (some (.return_ (BitVec.ofNat 64 24)), t) ∧
      memBytesAt t.memory t.memaddrs t.be 4096 (ascii "205 closing connection\r\n") := by
  obtain ⟨cb, hcb⟩ := Act.compile_lowers replies [.ret (v "pos")] (.ret (.var "pos")) rfl
  have hc := respond_lower name replies hcb
  have hrun : replies.run (ascii "QUIT") [] = ascii "205 closing connection\r\n" := by decide
  obtain ⟨t, hst, _, hout, _⟩ := respond_correct noCalls name replies hc replies_fits
    (by decide) (inpA := 4092) (outA := 4096) (inp := ascii "QUIT") (cap := 37) rfl rfl rfl rfl
    quitCall_input quitCall_room quitCall_apart (by decide) (by decide) (by decide)
  rw [hrun] at hst hout
  exact ⟨_, t, hc, hst, hout⟩

end DN.Dsl.Example
