-- SPDX-License-Identifier: AGPL-3.0-or-later
import DN.Compiler.Semantics

/-!
# DN.Compiler.StateCorpus — cases that reach the states the model can stop in

The differential lanes compare this model against native code on programs that
run to completion: they agree on the value a computation produces. What they
never reach is the other half of the semantics — the states in which a run stops.
A transcription can drift there without any of those lanes noticing, because a
missing local, an address outside the memory domain, an exhausted clock, a return
and an external call that ends the run all leave the value untouched and change
the *state*: which constructor the result carries, what the locals hold
afterwards, what was written back into memory, and what the external world saw.

This module is the corpus for that half. Each case is a closed program with a
finite initial state and a fixed sequence of oracle answers, so the whole run is
determined by data that can be printed. `dn-compiler dump-states` prints every
case together with the state the model ends in, and `scripts/state_check.py`
recomputes the same answer from the same input with an independent
implementation of the Pancake clauses and compares every field — the result
constructor, the locals, the memory, the external trace, the base address and the
clock — not merely a computed word.

The cases below are chosen for the stopping branches the review asked for:
a missing local, an address outside the domain, a timeout, a return (at the top
level and out of a loop), an external call that ends the run (refused by name, by
a reply of the wrong length, and by the oracle itself) and a partial writeback.
-/

namespace DN.Compiler.StateCorpus

open DN.Compiler

/-- What the oracle answers on one call. -/
inductive Answer
  /-- Hand back these bytes (a correct-length reply writes them into the array). -/
  | ret (bytes : List (BitVec 8))
  /-- Hand back one byte fewer than asked: `callFFI` turns that into a failure. -/
  | short
  /-- End the run with this outcome. -/
  | final (outcome : Outcome)
deriving Repr

/-- The ffi state of a corpus run: the call index and what the world was told,
oldest first. Both are observable, so a difference in either is a difference. -/
abbrev World := Nat × List String

/-- One hex digit. -/
def hexDigit (n : Nat) : Char :=
  if n < 10 then Char.ofNat (48 + n) else Char.ofNat (87 + n)

/-- Two hex digits of a byte. -/
def hexByte (b : BitVec 8) : String :=
  String.ofList [hexDigit ((b.toNat / 16) % 16), hexDigit (b.toNat % 16)]

/-- A byte list as hex, `-` when empty. -/
def hexBytes (bs : List (BitVec 8)) : String :=
  if bs.isEmpty then "-" else String.join (bs.map hexByte)

/-- The oracle a case describes: answer `i` to call `i`, and record what was
passed. Calls past the end of the list are answered with the array unchanged,
which is a successful call that writes back what it read. -/
def oracleOf (answers : List Answer) : Oracle World where
  call := fun (i, trace) name conf arr =>
    let record := name ++ ":" ++ hexBytes conf ++ ":" ++ hexBytes arr
    match answers[i]? with
    | some (.ret bytes) => .ret (i + 1, trace ++ [record]) bytes
    | some .short => .ret (i + 1, trace ++ [record]) (arr.drop 1)
    | some (.final outcome) => .final outcome
    | none => .ret (i + 1, trace ++ [record]) arr

/-- One case: a program, a finite state, and the answers the world gives. -/
structure Case where
  /-- What the case is about; also its key in the printed corpus. -/
  name : String
  /-- The program to run. -/
  prog : PancakeProg
  /-- The bound locals; every other name is unbound. -/
  locals : List (String × Word)
  /-- The words in memory; every other address reads as zero. -/
  memory : List (Word × Word)
  /-- The memory domain; an address outside it cannot be read or written. -/
  memaddrs : List Word
  /-- Big-endian byte order. -/
  be : Bool
  /-- The clock the run starts with. -/
  clock : Nat
  /-- The base address `@base` evaluates to. -/
  baseAddr : Word
  /-- What the oracle answers, call by call. -/
  answers : List Answer

/-- The state a case starts in. -/
def stateOf (c : Case) : PancakeState World where
  locals := fun k => (c.locals.find? (fun p => p.1 == k)).map (·.2)
  memory := fun a => ((c.memory.find? (fun p => p.1 == a)).map (·.2)).getD 0
  memaddrs := fun a => c.memaddrs.contains a
  be := c.be
  clock := c.clock
  ffi := (0, [])
  baseAddr := c.baseAddr

/-- Running a case is running its program from its state under its oracle. -/
def run (c : Case) : Option Result × PancakeState World :=
  PancakeSem (oracleOf c.answers) c.prog (stateOf c)

/-! ## Printing: the input and the answer, in a form another implementation can read -/

/-- A word as a decimal literal. -/
def ppWord (w : Word) : String := toString w.toNat

/-- The expression as an S-expression. -/
def ppExp : PancakeExp → String
  | .const w => "(const " ++ ppWord w ++ ")"
  | .var name => "(var " ++ name ++ ")"
  | .base => "(base)"
  | .op .add l r => "(add " ++ ppExp l ++ " " ++ ppExp r ++ ")"
  | .op .and_ l r => "(and " ++ ppExp l ++ " " ++ ppExp r ++ ")"
  | .op .sub l r => "(sub " ++ ppExp l ++ " " ++ ppExp r ++ ")"
  | .mul l r => "(mul " ++ ppExp l ++ " " ++ ppExp r ++ ")"
  | .cmp .less l r => "(less " ++ ppExp l ++ " " ++ ppExp r ++ ")"
  | .cmp .equal l r => "(equal " ++ ppExp l ++ " " ++ ppExp r ++ ")"
  | .cmp .notLess l r => "(notless " ++ ppExp l ++ " " ++ ppExp r ++ ")"
  | .loadByte a => "(loadb " ++ ppExp a ++ ")"
  | .loadWord a => "(loadw " ++ ppExp a ++ ")"
  | .shiftR l r => "(shr " ++ ppExp l ++ " " ++ ppExp r ++ ")"

/-- The program as an S-expression. -/
def ppProg : PancakeProg → String
  | .skip => "(skip)"
  | .dec v e c => "(dec " ++ v ++ " " ++ ppExp e ++ " " ++ ppProg c ++ ")"
  | .assign v e => "(assign " ++ v ++ " " ++ ppExp e ++ ")"
  | .store d s => "(store " ++ ppExp d ++ " " ++ ppExp s ++ ")"
  | .storeByte d s => "(storeb " ++ ppExp d ++ " " ++ ppExp s ++ ")"
  | .extCall n cp cl ap al =>
    "(extcall " ++ (if n.isEmpty then "_" else n) ++ " " ++ ppExp cp ++ " " ++ ppExp cl ++ " "
      ++ ppExp ap ++ " " ++ ppExp al ++ ")"
  | .seq a b => "(seq " ++ ppProg a ++ " " ++ ppProg b ++ ")"
  | .cond e a b => "(if " ++ ppExp e ++ " " ++ ppProg a ++ " " ++ ppProg b ++ ")"
  | .while_ e c => "(while " ++ ppExp e ++ " " ++ ppProg c ++ ")"
  | .ret e => "(ret " ++ ppExp e ++ ")"

/-- Every variable name the program mentions, so the locals can be compared over
a known set rather than over a function nobody can print. -/
def expNames : PancakeExp → List String
  | .const _ | .base => []
  | .var name => [name]
  | .op _ l r | .mul l r | .cmp _ l r | .shiftR l r => expNames l ++ expNames r
  | .loadByte a | .loadWord a => expNames a

/-- The names a program binds or reads. -/
def progNames : PancakeProg → List String
  | .skip => []
  | .dec v e c => v :: (expNames e ++ progNames c)
  | .assign v e => v :: expNames e
  | .store d s | .storeByte d s => expNames d ++ expNames s
  | .extCall _ cp cl ap al => expNames cp ++ expNames cl ++ expNames ap ++ expNames al
  | .seq a b => progNames a ++ progNames b
  | .cond e a b => expNames e ++ progNames a ++ progNames b
  | .while_ e c => expNames e ++ progNames c
  | .ret e => expNames e

/-- The names to compare for a case: the ones it binds and the ones its program
mentions, without repetitions. -/
def caseNames (c : Case) : List String :=
  (c.locals.map (·.1) ++ progNames c.prog).foldl
    (fun acc n => if acc.contains n then acc else acc ++ [n]) []

/-- The result constructor and its payload. -/
def ppResult : Option Result → String
  | none => "none"
  | some .error => "error"
  | some .timeout => "timeout"
  | some .break_ => "break"
  | some .continue_ => "continue"
  | some (.return_ v) => "return:" ++ ppWord v
  | some (.finalFFI e) =>
    "final:" ++ (if e.name.isEmpty then "_" else e.name) ++ ":" ++ hexBytes e.conf ++ ":"
      ++ hexBytes e.array ++ ":" ++ (match e.outcome with | .failed => "failed" | .diverged => "diverged")

/-- `name=value` for each compared local, with an empty value when unbound. -/
def ppLocals (names : List String) (lc : String → Option Word) : String :=
  String.intercalate ","
    (names.map fun n => n ++ "=" ++ (match lc n with | some v => ppWord v | none => ""))

/-- `addr=word` for each address of the domain. -/
def ppMemory (dom : List Word) (m : Word → Word) : String :=
  String.intercalate "," (dom.map fun a => ppWord a ++ "=" ++ ppWord (m a))

/-- What a case answers, as the lines `state_check.py` reads. -/
def ppAnswer : Answer → String
  | .ret bytes => "ret:" ++ hexBytes bytes
  | .short => "short"
  | .final .failed => "final:failed"
  | .final .diverged => "final:diverged"

/-- The whole case: what it is, and what the model makes of it. -/
def ppCase (c : Case) : String :=
  let (res, s') := run c
  let names := caseNames c
  String.intercalate "\n"
    [ "CASE " ++ c.name
    , "PROG " ++ ppProg c.prog
    , "LOCALS " ++ ppLocals (c.locals.map (·.1)) (stateOf c).locals
    , "MEM " ++ ppMemory c.memaddrs (stateOf c).memory
    , "DOM " ++ String.intercalate "," (c.memaddrs.map ppWord)
    , "BE " ++ (if c.be then "1" else "0")
    , "CLOCK " ++ toString c.clock
    , "BASE " ++ ppWord c.baseAddr
    , "ANSWERS " ++ String.intercalate ";" (c.answers.map ppAnswer)
    , "NAMES " ++ String.intercalate "," names
    , "RESULT " ++ ppResult res
    , "FLOCALS " ++ ppLocals names s'.locals
    , "FMEM " ++ ppMemory c.memaddrs s'.memory
    , "FCALLS " ++ toString s'.ffi.1
    , "FTRACE " ++ String.intercalate ";" s'.ffi.2
    , "FCLOCK " ++ toString s'.clock
    , "FBASE " ++ ppWord s'.baseAddr
    , "END" ]

/-! ## The corpus -/

private def word (n : Nat) : Word := BitVec.ofNat 64 n

/-- A domain of four aligned words, the shape the compiler theorem gives. -/
private def dom : List Word := [word 0, word 8, word 16, word 24]

/-- The bytes `0..7` packed into one little-endian word. -/
private def packed : Word := word 0x0706050403020100

/-- The cases. Each one names the branch it is there for. -/
def corpus : List Case :=
  [ { name := "assign-unbound", prog := .assign "x" (.const (word 1)), locals := [],
      memory := [], memaddrs := dom, be := false, clock := 4, baseAddr := word 0, answers := [] }
  , { name := "read-unbound", prog := .ret (.var "y"), locals := [("x", word 5)],
      memory := [], memaddrs := dom, be := false, clock := 4, baseAddr := word 0, answers := [] }
  , { name := "dec-restores-shadow",
      prog := .seq (.dec "x" (.const (word 9)) (.assign "x" (.const (word 10))))
        (.ret (.var "x")),
      locals := [("x", word 5)], memory := [], memaddrs := dom, be := false, clock := 4,
      baseAddr := word 0, answers := [] }
  , { name := "dec-unbinds-fresh",
      prog := .seq (.dec "t" (.const (word 1)) .skip) (.assign "t" (.const (word 2))),
      locals := [], memory := [], memaddrs := dom, be := false, clock := 4,
      baseAddr := word 0, answers := [] }
  , { name := "load-outside-domain", prog := .ret (.loadWord (.const (word 32))),
      locals := [], memory := [], memaddrs := dom, be := false, clock := 4,
      baseAddr := word 0, answers := [] }
  , { name := "store-outside-domain",
      prog := .store (.const (word 32)) (.const (word 7)), locals := [],
      memory := [], memaddrs := dom, be := false, clock := 4, baseAddr := word 0, answers := [] }
  , { name := "load-byte-outside-domain", prog := .ret (.loadByte (.const (word 33))),
      locals := [], memory := [], memaddrs := dom, be := false, clock := 4,
      baseAddr := word 0, answers := [] }
  , { name := "store-byte-truncates",
      prog := .seq (.storeByte (.const (word 1)) (.const (word 0x1ff)))
        (.ret (.loadWord (.const (word 0)))),
      locals := [], memory := [(word 0, packed)], memaddrs := dom, be := false, clock := 4,
      baseAddr := word 0, answers := [] }
  , { name := "store-byte-big-endian",
      prog := .seq (.storeByte (.const (word 1)) (.const (word 0xab)))
        (.ret (.loadWord (.const (word 0)))),
      locals := [], memory := [(word 0, packed)], memaddrs := dom, be := true, clock := 4,
      baseAddr := word 0, answers := [] }
  , { name := "timeout-empties-locals",
      prog := .while_ (.const (word 1)) .skip, locals := [("x", word 5)],
      memory := [], memaddrs := dom, be := false, clock := 0, baseAddr := word 0, answers := [] }
  , { name := "timeout-after-two-turns",
      prog := .while_ (.const (word 1)) (.assign "x" (.op .add (.var "x") (.const (word 1)))),
      locals := [("x", word 0)], memory := [], memaddrs := dom, be := false, clock := 2,
      baseAddr := word 0, answers := [] }
  , { name := "loop-counts-down",
      prog := .seq
        (.while_ (.var "n") (.assign "n" (.op .sub (.var "n") (.const (word 1)))))
        (.ret (.var "n")),
      locals := [("n", word 3)], memory := [], memaddrs := dom, be := false, clock := 8,
      baseAddr := word 0, answers := [] }
  , { name := "return-empties-locals",
      prog := .seq (.ret (.const (word 42))) (.assign "x" (.const (word 1))),
      locals := [("x", word 5)], memory := [], memaddrs := dom, be := false, clock := 4,
      baseAddr := word 0, answers := [] }
  , { name := "return-out-of-loop",
      prog := .while_ (.const (word 1)) (.ret (.op .add (.var "x") (.const (word 1)))),
      locals := [("x", word 41)], memory := [], memaddrs := dom, be := false, clock := 4,
      baseAddr := word 0, answers := [] }
  , { name := "base-address-reads",
      prog := .ret (.op .add .base (.const (word 8))), locals := [], memory := [],
      memaddrs := dom, be := false, clock := 4, baseAddr := word 64, answers := [] }
  , { name := "shift-whole-word",
      prog := .ret (.shiftR (.const (word 1)) (.const (word 64))), locals := [],
      memory := [], memaddrs := dom, be := false, clock := 4, baseAddr := word 0, answers := [] }
  , { name := "signed-comparison",
      prog := .ret (.cmp .less (.const (word 0xffffffffffffffff)) (.const (word 1))),
      locals := [], memory := [], memaddrs := dom, be := false, clock := 4,
      baseAddr := word 0, answers := [] }
  , { name := "ffi-empty-name-writes-back",
      prog := .seq (.extCall "" (.const (word 0)) (.const (word 0)) (.const (word 0))
        (.const (word 2))) (.ret (.loadWord (.const (word 0)))),
      locals := [], memory := [(word 0, packed)], memaddrs := dom, be := false, clock := 4,
      baseAddr := word 0, answers := [.ret [0xaa, 0xbb]] }
  , { name := "ffi-writes-reply",
      prog := .seq (.extCall "read" (.const (word 0)) (.const (word 0)) (.const (word 0))
        (.const (word 2))) (.ret (.loadWord (.const (word 0)))),
      locals := [], memory := [(word 0, packed)], memaddrs := dom, be := false, clock := 4,
      baseAddr := word 0, answers := [.ret [0xaa, 0xbb]] }
  , { name := "ffi-short-reply-ends-run",
      prog := .seq (.extCall "read" (.const (word 0)) (.const (word 0)) (.const (word 0))
        (.const (word 2))) (.ret (.const (word 1))),
      locals := [("x", word 5)], memory := [(word 0, packed)], memaddrs := dom, be := false,
      clock := 4, baseAddr := word 0, answers := [.short] }
  , { name := "ffi-oracle-ends-run",
      prog := .extCall "read" (.const (word 0)) (.const (word 1)) (.const (word 8))
        (.const (word 2)),
      locals := [("x", word 5)], memory := [(word 0, packed), (word 8, packed)],
      memaddrs := dom, be := false, clock := 4, baseAddr := word 0,
      answers := [.final .diverged] }
  , { name := "ffi-array-outside-domain",
      prog := .extCall "read" (.const (word 0)) (.const (word 0)) (.const (word 32))
        (.const (word 1)),
      locals := [], memory := [], memaddrs := dom, be := false, clock := 4,
      baseAddr := word 0, answers := [.ret [0xaa]] }
  , { name := "ffi-twice-advances-the-world",
      prog := .seq
        (.extCall "a" (.const (word 0)) (.const (word 1)) (.const (word 8)) (.const (word 1)))
        (.extCall "b" (.const (word 0)) (.const (word 1)) (.const (word 8)) (.const (word 1))),
      locals := [], memory := [(word 0, packed), (word 8, packed)], memaddrs := dom,
      be := false, clock := 4, baseAddr := word 0, answers := [.ret [0x11], .ret [0x22]] }
  , { name := "seq-stops-at-the-first-error",
      prog := .seq (.assign "x" (.const (word 1))) (.ret (.const (word 7))),
      locals := [], memory := [], memaddrs := dom, be := false, clock := 4,
      baseAddr := word 0, answers := [] }
  ]

/-- A generated case: the same small world for all of them, so the printed
difference between two cases is the construct they exercise. -/
private def gen (name : String) (prog : PancakeProg) : Case :=
  { name := name, prog := prog, locals := [("n", word 2)],
    memory := [(word 0, packed), (word 8, packed)], memaddrs := dom, be := false,
    clock := 4, baseAddr := word 16, answers := [] }

/-- Generated cases: one construct at a time, over the boundaries that decide a
branch — addresses inside and outside the memory domain, shift distances around
the word width, comparisons around the sign boundary, clocks around the loop
bound, and reply lengths around the array's. The enumeration is bounded and
deterministic, so the corpus is the same on every run. -/
def generated : List Case :=
  let addrs : List Nat := [0, 8, 24, 31, 32]
  let memory := addrs.flatMap fun a =>
    [ gen ("gen-loadw-" ++ toString a) (.ret (.loadWord (.const (word a))))
    , gen ("gen-loadb-" ++ toString a) (.ret (.loadByte (.const (word a))))
    , gen ("gen-store-" ++ toString a)
        (.seq (.store (.const (word a)) (.const (word 7))) (.ret (.loadWord (.const (word 0)))))
    , gen ("gen-storeb-" ++ toString a)
        (.seq (.storeByte (.const (word a)) (.const (word 0xcd)))
          (.ret (.loadWord (.const (word 0)))))
    , { gen ("gen-storeb-be-" ++ toString a)
          (.seq (.storeByte (.const (word a)) (.const (word 0xcd)))
            (.ret (.loadWord (.const (word 0))))) with be := true } ]
  let shifts := ([0, 1, 63, 64, 65] : List Nat).map fun k =>
    gen ("gen-shr-" ++ toString k)
      (.ret (.shiftR (.const (word 0x8000000000000001)) (.const (word k))))
  let edges : List Nat := [0, 1, 0x7fffffffffffffff, 0x8000000000000000, 0xffffffffffffffff]
  let comparisons := edges.flatMap fun v =>
    [ gen ("gen-less-" ++ toString v) (.ret (.cmp .less (.const (word v)) (.const (word 1))))
    , gen ("gen-notless-" ++ toString v)
        (.ret (.cmp .notLess (.const (word v)) (.const (word 1))))
    , gen ("gen-equal-" ++ toString v)
        (.ret (.cmp .equal (.const (word v)) (.const (word 1)))) ]
  let loop : PancakeProg :=
    .seq (.while_ (.var "n") (.assign "n" (.op .sub (.var "n") (.const (word 1)))))
      (.ret (.var "n"))
  let clocks := ([0, 1, 2, 3] : List Nat).map fun k =>
    { gen ("gen-clock-" ++ toString k) loop with clock := k }
  let replies := ([0, 1, 2, 3] : List Nat).flatMap fun n =>
    [ { gen ("gen-ffi-len-" ++ toString n)
          (.seq (.extCall "read" (.const (word 0)) (.const (word 1)) (.const (word 8))
            (.const (word n))) (.ret (.loadWord (.const (word 8))))) with
        answers := [.ret [0x11, 0x22]] }
    , { gen ("gen-ffi-short-" ++ toString n)
          (.extCall "read" (.const (word 0)) (.const (word 1)) (.const (word 8))
            (.const (word n))) with answers := [.short] } ]
  let arithmetic :=
    [ gen "gen-mul" (.ret (.mul (.const (word 0xffffffffffffffff)) (.const (word 3))))
    , gen "gen-and" (.ret (.op .and_ (.const (word 0xff00ff00ff00ff00)) (.const (word 0x0f0f0f0f0f0f0f0f))))
    , gen "gen-if-true" (.cond (.const (word 1)) (.ret (.const (word 1))) (.ret (.const (word 2))))
    , gen "gen-if-false" (.cond (.const (word 0)) (.ret (.const (word 1))) (.ret (.const (word 2))))
    , gen "gen-if-guard-unbound" (.cond (.var "missing") .skip .skip)
    , gen "gen-if-guard-bad-load" (.cond (.loadWord (.const (word 32))) .skip .skip) ]
  -- Every clause that stops because a subexpression has no value at all.
  let novalue :=
    [ gen "gen-dec-no-value" (.dec "t" (.var "missing") .skip)
    , gen "gen-assign-no-value" (.assign "n" (.var "missing"))
    , gen "gen-store-no-value" (.store (.var "missing") (.const (word 1)))
    , gen "gen-store-src-no-value" (.store (.const (word 0)) (.var "missing"))
    , gen "gen-storeb-no-value" (.storeByte (.var "missing") (.const (word 1)))
    , gen "gen-ret-no-value" (.ret (.var "missing"))
    , gen "gen-while-guard-no-value" (.while_ (.var "missing") .skip)
    , gen "gen-extcall-no-value"
        (.extCall "read" (.var "missing") (.const (word 1)) (.const (word 8)) (.const (word 1)))
    , gen "gen-extcall-conf-outside"
        (.extCall "read" (.const (word 32)) (.const (word 1)) (.const (word 8)) (.const (word 1)))
    , gen "gen-dec-return-restores"
        (.seq (.dec "n" (.const (word 9)) (.ret (.var "n"))) (.ret (.var "n"))) ]
  memory ++ shifts ++ comparisons ++ clocks ++ replies ++ arithmetic ++ novalue

/-! ## The write-back clause on its own

`write_bytearray` returns the memory *the failing call was given*, so a store out
of range drops the writes of the tail as well. Through `ExtCall` that branch is
unreachable: the array was read through the same domain a moment earlier, so
every write-back store is in range. It is checked here directly instead, as its
own kind of case, against the same independent implementation.
-/

/-- One write-back: bytes written at an address over a memory domain. -/
structure WriteCase where
  /-- What the case is about. -/
  name : String
  /-- The memory domain. -/
  memaddrs : List Word
  /-- Big-endian byte order. -/
  be : Bool
  /-- Where the write starts. -/
  addr : Word
  /-- The bytes to write. -/
  bytes : List (BitVec 8)
  /-- The words in memory before the write. -/
  memory : List (Word × Word)

/-- The write cases: in range, starting out of range, and running off the end. -/
def writes : List WriteCase :=
  [ { name := "write-in-range", memaddrs := dom, be := false, addr := word 0,
      bytes := [0xaa, 0xbb], memory := [(word 0, packed)] }
  , { name := "write-head-outside", memaddrs := [word 8], be := false, addr := word 7,
      bytes := [0xaa, 0xbb], memory := [] }
  , { name := "write-tail-outside", memaddrs := [word 0], be := false, addr := word 6,
      bytes := [0xaa, 0xbb, 0xcc], memory := [(word 0, packed)] }
  , { name := "write-big-endian", memaddrs := dom, be := true, addr := word 1,
      bytes := [0xaa, 0xbb], memory := [(word 0, packed)] }
  , { name := "write-nothing", memaddrs := dom, be := false, addr := word 32,
      bytes := [], memory := [(word 0, packed)] } ]

/-- What a write case leaves in memory. -/
def runWrite (w : WriteCase) : Word → Word :=
  writeByteArray (fun a => w.memaddrs.contains a) w.be w.addr w.bytes
    (fun a => ((w.memory.find? (fun p => p.1 == a)).map (·.2)).getD 0)

/-- A write case and its answer. -/
def ppWrite (w : WriteCase) : String :=
  String.intercalate "\n"
    [ "WRITE " ++ w.name
    , "WDOM " ++ String.intercalate "," (w.memaddrs.map ppWord)
    , "WBE " ++ (if w.be then "1" else "0")
    , "WADDR " ++ ppWord w.addr
    , "WBYTES " ++ hexBytes w.bytes
    , "WMEM " ++ ppMemory w.memaddrs
        (fun a => ((w.memory.find? (fun p => p.1 == a)).map (·.2)).getD 0)
    , "WRESULT " ++ ppMemory w.memaddrs (runWrite w)
    , "END" ]

/-- The corpus as the printer emits it. -/
def dump : String :=
  String.intercalate "\n" ((corpus ++ generated).map ppCase ++ writes.map ppWrite)

/-! ## Non-vacuity: the corpus really reaches the branches it names -/

-- Every case has a distinct name, so a comparison can key on it.
def regression_601 : Bool :=
  let names := corpus.map (·.name)
  let distinct := names.foldl (fun acc n => if acc.contains n then acc else n :: acc) []
  distinct.length == corpus.length

-- The stopping branches are all reached by some case.
def regression_602 : Bool :=
  let errors := corpus.filter (fun c => (run c).1 == some Result.error)
  let timeouts := corpus.filter (fun c => (run c).1 == some Result.timeout)
  let returns := corpus.filter (fun c =>
    match (run c).1 with | some (.return_ _) => true | _ => false)
  let finals := corpus.filter (fun c =>
    match (run c).1 with | some (.finalFFI _) => true | _ => false)
  (errors.length >= 5) && (timeouts.length >= 2) && (returns.length >= 5) && (finals.length >= 2)

-- A timeout empties the locals, which is the state half no value comparison sees.
def regression_603 : Bool :=
  match corpus.find? (fun c => c.name == "timeout-empties-locals") with
  | some c => ((run c).2.locals "x" == none) && ((run c).1 == some Result.timeout)
  | none => false

-- No case uses the name the printer spells the empty external name with, so the
-- encoding is unambiguous for this corpus.
def regression_488 : Bool :=
  (corpus ++ generated).all fun c =>
    let rec names : PancakeProg → Bool
      | .extCall n _ _ _ _ => n != "_"
      | .seq a b => names a && names b
      | .cond _ a b => names a && names b
      | .while_ _ p => names p
      | .dec _ _ p => names p
      | _ => true
    names c.prog

-- A reply of the wrong length ends the run and writes nothing back.
def regression_604 : Bool :=
  match corpus.find? (fun c => c.name == "ffi-short-reply-ends-run") with
  | some c =>
    (match (run c).1 with
     | some (.finalFFI e) => (e.outcome == Outcome.failed) && (e.name == "read")
     | _ => false)
    && ((run c).2.memory (BitVec.ofNat 64 0) == packed)
  | none => false

end DN.Compiler.StateCorpus
