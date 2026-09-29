-- SPDX-License-Identifier: AGPL-3.0-or-later
import DN.News.Framer

/-!
# DN.News.FrameModel

The framers run as a program, for `scripts/framing_check.py` to hold the compiled code and an
independent reference against. A case is one line of text: `L LIM CHUNK...` feeds command lines
of at most `LIM` octets, `B CAP CHUNK...` feeds a block for a buffer of `CAP` bytes; each chunk is
hex, `-` for an empty one. The answer is one line:

    L lines KIND:HEX ... state LEN CR BAD HEX
    B end KIND:HEX READ ... open PHASE BAD SIZE HEX

with the lines in order and the state after the last chunk; or, for blocks, each block that ends,
with its verdict and how many bytes it read, the next one starting from the state the last one
left, then the state after the last chunk. `linePath` and `blockPath` name the way each byte takes
through the program, which `runAll` counts for each program, so that the lane can require every
way through each of them to be taken.
-/

namespace DN.News.FrameModel

open DN.News.FrameSpec DN.News.Framer

def hexDigit (c : Char) : Option Nat :=
  if '0' ≤ c ∧ c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c ∧ c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else none

/-- Bytes from hex; `-` is none. -/
def parseHex (s : String) : Option (List Byte) :=
  if s == "-" then some []
  else
    let rec go : List Char → Option (List Byte)
      | [] => some []
      | a :: b :: rest => do
        let hi ← hexDigit a
        let lo ← hexDigit b
        return BitVec.ofNat 8 (hi * 16 + lo) :: (← go rest)
      | [_] => none
    go s.toList

def hex (bs : List Byte) : String :=
  if bs.isEmpty then "-"
  else String.join (bs.map fun b =>
    let d (n : Nat) : Char := "0123456789abcdef".toList.getD n '0'
    String.ofList [d (b.toNat / 16), d (b.toNat % 16)])

def kindName : Kind → String
  | .command => "command" | .malformed => "malformed" | .overlong => "overlong"

def blockName : BlockKind → String
  | .accepted => "accepted" | .refused => "refused" | .tooLarge => "too-large"

def phaseName : Phase → String
  | .bol => "bol" | .data => "data" | .cr => "cr" | .dot => "dot" | .dotcr => "dotcr"

def flag (b : Bool) : String := if b then "1" else "0"

/-- The way a byte takes through the line program. -/
def linePath (lim : Nat) (s : LineState) (b : Byte) : String :=
  if b = LF then
    if lim ≤ s.len then "lf-overlong" else if s.cr ∧ ¬ s.bad then "lf-command" else "lf-malformed"
  else
    "byte-cr" ++ flag s.cr ++ "-nul" ++ flag (decide (b = NUL)) ++
      "-room" ++ flag (decide (s.len < lim))

/-- The way a byte takes through the block program: the phase logic, then each byte held with or
without room for it. -/
def blockPath (cap : Nat) (s : BlockState) (b : Byte) : String :=
  let cls := if b = LF then "lf" else if b = CR then "cr" else if b = DOT then "dot"
    else if b = NUL then "nul" else "other"
  let p := plan s b
  if p.ends then
    "end-" ++ (if s.bad then "refused" else if cap < s.size then "too-large" else "accepted")
  else
    let room (n : Nat) : String := if s.size + n < cap then "room" else "full"
    phaseName s.phase ++ "-" ++ cls ++
      (if p.pre then "-pre-" ++ room 0 else "") ++
      (if p.post then "-post-" ++ room (if p.pre then 1 else 0) else "")

def lineRun (lim : Nat) (chunks : List (List Byte)) : String × List String :=
  let bytes := chunks.flatten
  let (st, lines) := feedChunks lim .fresh chunks
  let paths := (bytes.foldl (fun (acc : LineState × List String) b =>
    ((lineStep lim acc.1 b).1, linePath lim acc.1 b :: acc.2)) (.fresh, [])).2.reverse
  ("L lines" ++ String.join (lines.map fun l => " " ++ kindName l.kind ++ ":" ++ hex l.kept) ++
    " state " ++ toString st.len ++ " " ++ flag st.cr ++ " " ++ flag st.bad ++ " " ++ hex st.buf,
   paths)

/-- The blocks that end among `bytes`, each read from the state the last one left, and the state
after them. Each block that ends reads at least one byte, so `fuel` of one more than the bytes is
enough. -/
def blocks (cap : Nat) : Nat → BlockState → List Byte → List (Nat × BlockResult) × BlockState
  | 0, s, _ => ([], s)
  | fuel + 1, s, bytes =>
    match feedBlock cap s bytes with
    | (read, s', some v) =>
      let (rest, t) := blocks cap fuel s' (bytes.drop read)
      ((read, v) :: rest, t)
    | (_, s', none) => ([], s')

def blockRun (cap : Nat) (chunks : List (List Byte)) : String × List String :=
  let bytes := chunks.flatten
  let (ended, st) := blocks cap (bytes.length + 1) .fresh bytes
  let paths := (bytes.foldl (fun (acc : BlockState × List String) b =>
    ((blockStep cap acc.1 b).1, blockPath cap acc.1 b :: acc.2)) (.fresh, [])).2.reverse
  ("B" ++ String.join (ended.map fun (read, v) =>
      " end " ++ blockName v.kind ++ ":" ++ hex v.held ++ " " ++ toString read) ++
    " open " ++ phaseName st.phase ++ " " ++ flag st.bad ++ " " ++ toString st.size ++ " " ++
    hex st.buf,
   paths)

/-- One case, answered, with the ways its bytes took, each named with its program (`L512`,
`B64`, ...). -/
def runCase (line : String) : Except String (String × List String) := do
  match line.splitOn " " |>.filter (· ≠ "") with
  | mode :: size :: chunks =>
    let some n := size.toNat? | throw s!"bad size in: {line}"
    let some cs := chunks.mapM parseHex | throw s!"bad chunk in: {line}"
    let named (r : String × List String) := (r.1, r.2.map fun way => mode ++ size ++ " " ++ way)
    if mode == "L" then return named (lineRun n cs)
    else if mode == "B" then return named (blockRun n cs)
    else throw s!"bad mode in: {line}"
  | _ => throw s!"bad case: {line}"

/-- The answers to a batch of cases, then how often each way was taken. -/
def runAll (input : String) : Except String String := do
  let cases := input.splitOn "\n" |>.filter (· ≠ "")
  let results ← cases.mapM runCase
  let counts := results.foldl (fun (acc : List (String × Nat)) r =>
    r.2.foldl (fun acc p =>
      match acc.find? (·.1 == p) with
      | some _ => acc.map fun (q, k) => if q == p then (q, k + 1) else (q, k)
      | none => (p, 1) :: acc) acc) []
  let sorted := counts.toArray.qsort (fun a b => a.1 < b.1) |>.toList
  return String.join (results.map (·.1 ++ "\n")) ++
    String.join (sorted.map fun (p, k) => "path " ++ p ++ " " ++ toString k ++ "\n")

/-- The model answers the specification's examples: a command, a bare LF, a stuffed block and
what follows it. -/
def regression_819 : Bool :=
  (runCase "L 512 410d0a 410a").toOption.map (·.1) ==
    some "L lines command:41 malformed:41 state 0 0 0 -"

def regression_820 : Bool :=
  (runCase "B 64 2e2e0d0a 2e0d0a58").toOption.map (·.1) ==
    some "B end accepted:2e0d0a 7 open data 0 1 58"

end DN.News.FrameModel
