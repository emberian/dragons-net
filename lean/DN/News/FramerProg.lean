-- SPDX-License-Identifier: AGPL-3.0-or-later
import DN.News.Framer
import DN.Compiler.Kernels

/-!
# DN.News.FramerProg

The framers as programs of the subset the compiler prints; `DN.News.FramerCode` proves that they
make exactly the framer's steps (`DN.News.Framer`).

The state of a connection lives in memory at `blk`: the words at `blk`, `blk + 8` and `blk + 16`
hold the length of the line so far, whether its last byte was a CR, and whether it is already
spoiled; the verdict goes to `blk + 24` (its kind, zero when no line ended) and `blk + 32` (how many
bytes it keeps); the bytes of the line are kept from `blk + 40`. `dn_frame_line(blk, p, n, i)`
reads the received bytes at `p` from position `i` up to `n`, stops after the first line that ends,
and returns the position it stopped at; a negative `n` or `i`, or `i` past `n`, it refuses before
reading anything. `dn_frame_block` does the same for a block, whose phase, whether it is spoiled
and its size are the first three words, and the bytes it holds are kept from `blk + 40`.

The framers' statements come apart from the functions around them (`lineFrag`, `blockFrag`), so
that the session's `main` (`DN.Server.Session`) runs the line framer's in place.
-/

namespace DN.News.FramerProg

open DN.Compiler DN.Compiler.Syntax DN.News.FrameSpec DN.News.Framer

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
          [.assign "kind" (n (kindCode .overlong)), .assign "kept" (v "len")]
          [.ite (eAnd (v "cr") (eEq (v "bad") (n 0)))
             [.assign "kind" (n (kindCode .command)), .assign "kept" (eSub (v "len") (n 1))]
             [.assign "kind" (n (kindCode .malformed)), .assign "kept" (v "len")]],
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
def dataS : List PStmt := [.assign "post" (n 1)] ++ spoilS ++ [.assign "ph" (n (phaseCode .data))]

/-- A CR after a CR held back: the first is inside the line. -/
def crCrS : List PStmt :=
  [.assign "pre" (n 1), .assign "bad" (n 1), .assign "ph" (n (phaseCode .cr))]

/-- Another byte after a CR held back. -/
def crByteS : List PStmt :=
  [.assign "pre" (n 1), .assign "post" (n 1), .assign "bad" (n 1),
   .assign "ph" (n (phaseCode .data))]

/-- The end of the block: the verdict, and a fresh state. -/
def endS (cap : Nat) : List PStmt :=
  [.ite (v "bad") [.assign "kind" (n (blockCode .refused)), .assign "held" (n 0)]
     [.ite (eLt (n cap) (v "size")) [.assign "kind" (n (blockCode .tooLarge)), .assign "held" (n 0)]
        [.assign "kind" (n (blockCode .accepted)), .assign "held" (v "size")]],
   .assign "ph" (n (phaseCode .bol)), .assign "bad" (n 0)]

/-- What the byte does, decided from the phase and the byte. -/
def logicS (cap : Nat) : List PStmt :=
  [.assign "pre" (n 0), .assign "post" (n 0),
   .ite (eEq (v "ph") (n (phaseCode .bol)))
     [.ite (eEq (v "b") (n 46)) [.assign "ph" (n (phaseCode .dot))]
        [.ite (eEq (v "b") (n 13)) [.assign "ph" (n (phaseCode .cr))] dataS]]
     [.ite (eEq (v "ph") (n (phaseCode .data)))
        [.ite (eEq (v "b") (n 13)) [.assign "ph" (n (phaseCode .cr))] dataS]
        [.ite (eEq (v "ph") (n (phaseCode .cr)))
           [.ite (eEq (v "b") (n 10))
              [.assign "pre" (n 1), .assign "post" (n 1), .assign "ph" (n (phaseCode .bol))]
              [.ite (eEq (v "b") (n 13)) crCrS crByteS]]
           [.ite (eEq (v "ph") (n (phaseCode .dot)))
              [.ite (eEq (v "b") (n 13)) [.assign "ph" (n (phaseCode .dotcr))] dataS]
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

end DN.News.FramerProg
