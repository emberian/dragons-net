-- SPDX-License-Identifier: AGPL-3.0-or-later
import DN.Compiler.Checked
import DN.News.FramerCode
import DN.News.SessionSpec
import DN.Server.SessionLayout

/-!
# DN.Server.Session

The NNTP session of `DN.News.SessionSpec` as the server's `main`: each turn it fetches a batch of
events from its host, runs the session's turn over its table of connections in the heap, hands
the host the actions, reads back how much of each send the kernel took, and names the time it
needs its next turn (docs/decisions/0003-nntp-slice.md). The layout is `DN.Server.SessionLayout`.

Lines are framed by the statements of `DN.News.FramerCode.lineFrag`, run on a connection's held
input; the reply to a line follows `DN.News.CommandSpec.reply`; the texts of the replies are laid
out once in the program's own area and copied from there, with the revision and the address of the
source the host gives in its first batch.

Every number the host writes is checked before it is used; one out of range stops the run with
the code of `DN.News.SessionSpec.Breach`, or `SessionLayout.unknownEvent`,
`SessionLayout.badIdentity`, written where the host reads it at exit. The loop itself never
finishes, so the run never falls off the end of `main`.
-/

namespace DN.Server.Session

open DN.Compiler DN.Compiler.Syntax DN.Server.SessionLayout

/-- `@base + off`. -/
def at_ (off : Nat) : PExpr := atOff .base off
def ld (a : PExpr) : PExpr := .loadw 1 a
/-- The word at `off` in the record the local `r` points to. -/
def fld (r : String) (off : Nat) : PExpr := ld (atOff (v r) off)
def setf (r : String) (off : Nat) (e : PExpr) : PStmt := .store (atOff (v r) off) e
def ne (a b : PExpr) : PExpr := eEq (eEq a b) (n 0)
/-- Either of two flags, each zero or one. -/
def or2 (a b : PExpr) : PExpr := eLt (n 0) (eAdd a b)
def inc (x : String) : PStmt := .assign x (eAdd (v x) (n 1))

/-- Stop the run with `code`: written where the host reads it at exit, then returned. -/
def stop (code : Nat) : List PStmt := [.store (at_ (ownOff + ownStop)) (n code), .ret (n code)]
def breach (b : News.SessionSpec.Breach) : List PStmt := stop b.code

def copyLoop (j : String) (dst src len : PExpr) : PStmt :=
  .while (eLt (v j) len) [.storeb (eAdd dst (v j)) (.loadb (eAdd src (v j))), inc j]

/-- Copy `len` bytes from `src` to `dst`, with the counter `j` the caller has declared. -/
def copy (j : String) (dst src len : PExpr) : List PStmt :=
  [.assign j (n 0), copyLoop j dst src len]

/-- The same with a counter `j` of its own. -/
def copyNew (j : String) (dst src len : PExpr) : List PStmt :=
  [.dec j (n 0), copyLoop j dst src len]

/-! ## The texts of the replies -/

/-- The texts, one byte at a time, into the program's own area. -/
def textsInit : List PStmt :=
  (List.range texts.length).flatMap fun k =>
    (texts.getD k []).zipIdx.map fun (b, j) =>
      .storeb (at_ (ownOff + ownTexts + textAt k + j)) (n b.toNat)

def textAddr (k : Nat) : PExpr := at_ (ownOff + ownTexts + textAt k)
def textLen (k : Nat) : Nat := (texts.getD k []).length

/-- The texts by their place in `SessionLayout.texts`. -/
def tGreetingHead : Nat := 0
def tGreetingMid : Nat := 1
def tCrlf : Nat := 2
def tCapabilitiesHead : Nat := 3
def tBlockEnd : Nat := 4
def tHelpHead : Nat := 5
def tHelpMid : Nat := 6
def tQuit : Nat := 7
def tNoGroup : Nat := 8
def tNoSuchId : Nat := 9
def tUnknown : Nat := 10
def tSyntax : Nat := 11
def tNames : Nat := 12

/-- Append a text at `ob + o`, moving `o` past it; `j` counts. -/
def appendText (k : Nat) : List PStmt :=
  copy "j" (eAdd (v "ob") (v "o")) (textAddr k) (n (textLen k)) ++
    [.assign "o" (eAdd (v "o") (n (textLen k)))]

/-- The revision, of the length `rl` holds. -/
def appendRevision : List PStmt :=
  copy "j" (eAdd (v "ob") (v "o")) (at_ (ownOff + ownRev)) (v "rl") ++
    [.assign "o" (eAdd (v "o") (v "rl"))]

/-- The address of the source, of the length `sl` holds. -/
def appendSource : List PStmt :=
  copy "j" (eAdd (v "ob") (v "o")) (at_ (ownOff + ownSrc)) (v "sl") ++
    [.assign "o" (eAdd (v "o") (v "sl"))]

/-- Where a text is put together: the record's output, from its start, and the identity's
lengths. -/
def outputDecs : List PStmt :=
  [.dec "ob" (atOff (v "cb") cOut), .dec "o" (n 0), .dec "j" (n 0),
   .dec "rl" (ld (at_ (ownOff + ownRevLen))), .dec "sl" (ld (at_ (ownOff + ownSrcLen)))]

/-- The greeting into the output of the record `cb`. -/
def writeGreeting : List PStmt :=
  outputDecs ++
    appendText tGreetingHead ++ appendRevision ++ appendText tGreetingMid ++ appendSource ++
    appendText tCrlf ++ [setf "cb" cOutLen (v "o")]

/-- The reply `r` (1 capabilities, 2 help, 3 quit, 4 no group, 5 no such id, 6 unknown, 7 syntax)
into the output of the record `cb`. -/
def writeReply : List PStmt :=
  outputDecs ++
  [.ite (eEq (v "r") (n 1)) (appendText tCapabilitiesHead ++ appendRevision ++ appendText tBlockEnd)
    [.ite (eEq (v "r") (n 2))
      (appendText tHelpHead ++ appendRevision ++ appendText tHelpMid ++ appendSource ++
        appendText tBlockEnd)
      [.ite (eEq (v "r") (n 3)) (appendText tQuit)
        [.ite (eEq (v "r") (n 4)) (appendText tNoGroup)
          [.ite (eEq (v "r") (n 5)) (appendText tNoSuchId)
            [.ite (eEq (v "r") (n 6)) (appendText tUnknown) (appendText tSyntax)]]]]],
   setf "cb" cOutLen (v "o")]

/-! ## The reply to a line -/

/-- The byte of the kept line at `off`. -/
def kept (off : PExpr) : PExpr := .loadb (eAdd (eAdd (v "blk") (n framerHead)) off)

def isAlphaE (e : PExpr) : PExpr :=
  or2 (eAnd (eLt (n 64) e) (eLt e (n 91))) (eAnd (eLt (n 96) e) (eLt e (n 123)))
def isDigitE (e : PExpr) : PExpr := eAnd (eLt (n 47) e) (eLt e (n 58))
/-- An ASCII letter in upper case. -/
def fold (e : PExpr) : PExpr := eSub e (eMul (n 32) (eAnd (eLt (n 96) e) (eLt e (n 123))))

/-- Where a word ends at `pos`: the first and second words' lengths. -/
def endWord (pos : PExpr) : List PStmt :=
  [.ite (eEq (v "w") (n 1)) [.assign "l0" (eSub pos (v "ws"))] [],
   .ite (eEq (v "w") (n 2)) [.assign "l1" (eSub pos (v "ws"))] [],
   .assign "inw" (n 0)]

/-- The words of the kept line: how many (`w`), and where the first two start and how long they
are; words are runs of bytes other than SP and TAB. -/
def scanWords : List PStmt :=
  [.dec "w" (n 0), .dec "s0" (n 0), .dec "l0" (n 0), .dec "s1" (n 0), .dec "l1" (n 0),
   .dec "inw" (n 0), .dec "ws" (n 0), .dec "q" (n 0),
   .while (eLt (v "q") (v "kept"))
     [.dec "cq" (kept (v "q")),
      .ite (or2 (eEq (v "cq") (n 32)) (eEq (v "cq") (n 9)))
        [.ite (v "inw") (endWord (v "q")) []]
        [.ite (eEq (v "inw") (n 0))
          [inc "w", .assign "ws" (v "q"), .assign "inw" (n 1),
           .ite (eEq (v "w") (n 1)) [.assign "s0" (v "q")] [],
           .ite (eEq (v "w") (n 2)) [.assign "s1" (v "q")] []]
          []],
      inc "q"],
   .ite (v "inw") (endWord (v "kept")) []]

/-- `eqk` is one when the first word is the `k`-th command name, in any case. -/
def nameIs (k : Nat) : List PStmt :=
  [.assign "eqk" (eEq (v "l0") (n (textLen (tNames + k)))),
   .assign "jq" (n 0),
   .while (eAnd (v "eqk") (eLt (v "jq") (v "l0")))
     [.ite (ne (fold (kept (eAdd (v "s0") (v "jq"))))
          (.loadb (eAdd (textAddr (tNames + k)) (v "jq"))))
        [.assign "eqk" (n 0)] [],
      inc "jq"]]

/-- `ok` is one when the second word is a keyword (RFC 3977 §9.8). -/
def keywordCheck : List PStmt :=
  [.assign "ok" (eLe (n 3) (v "l1")),
   .ite (v "ok") [.assign "ok" (isAlphaE (kept (v "s1")))] [],
   .assign "jq" (n 1),
   .while (eAnd (v "ok") (eLt (v "jq") (v "l1")))
     [.dec "cz" (kept (eAdd (v "s1") (v "jq"))),
      .assign "ok" (or2 (or2 (isAlphaE (v "cz")) (isDigitE (v "cz")))
        (or2 (eEq (v "cz") (n 46)) (eEq (v "cz") (n 45)))),
      inc "jq"]]

/-- `ok` is one when the second word is an article number (§6, §9.8). -/
def numberCheck : List PStmt :=
  [.assign "ok" (eAnd (eLe (n 1) (v "l1")) (eLe (v "l1") (n 16))),
   .assign "val" (n 0),
   .assign "jq" (n 0),
   .while (eAnd (v "ok") (eLt (v "jq") (v "l1")))
     [.dec "cz" (kept (eAdd (v "s1") (v "jq"))),
      .assign "ok" (isDigitE (v "cz")),
      .assign "val" (eAdd (eMul (v "val") (n 10)) (eSub (v "cz") (n 48))),
      inc "jq"],
   .ite (v "ok") [.assign "ok" (eLe (v "val") (n 2147483647))] []]

/-- `ok` is one when the second word is a message-id (§3.6, §9.8). -/
def messageIdCheck : List PStmt :=
  [.assign "ok" (eAnd (eLe (n 3) (v "l1")) (eLe (v "l1") (n 250))),
   .ite (v "ok")
     [.assign "ok" (eAnd (eEq (kept (v "s1")) (n 60))
        (eEq (kept (eSub (eAdd (v "s1") (v "l1")) (n 1))) (n 62)))] [],
   .assign "jq" (n 1),
   .while (eAnd (v "ok") (eLt (v "jq") (eSub (v "l1") (n 1))))
     [.dec "cz" (kept (eAdd (v "s1") (v "jq"))),
      .assign "ok" (or2 (eAnd (eLt (n 32) (v "cz")) (eLt (v "cz") (n 62)))
        (eAnd (eLt (n 62) (v "cz")) (eLt (v "cz") (n 127)))),
      inc "jq"]]

/-- The reply `r` to the line the framer reported (`kind`, `kept`, the bytes from `blk + 40`),
as `DN.News.CommandSpec.reply` gives it. -/
def classify : List PStmt :=
  scanWords ++
  [.dec "cmd" (n 0), .dec "eqk" (n 0), .dec "jq" (n 0), .dec "ok" (n 0), .dec "val" (n 0),
   .ite (eEq (v "w") (n 0))
     [.ite (eEq (v "kind") (n 3)) [.assign "r" (n 6)] [.assign "r" (n 0)]]
     ((List.range 5).flatMap (fun k => nameIs k ++
        [.ite (v "eqk") [.assign "cmd" (n (k + 1))] []]) ++
      [.ite (eEq (v "cmd") (n 0)) [.assign "r" (n 6)]
        [.ite (ne (v "kind") (n 1)) [.assign "r" (n 7)]
          [.dec "args" (eSub (v "w") (n 1)),
           .ite (eEq (v "cmd") (n 1))
             [.ite (eEq (v "args") (n 0)) [.assign "r" (n 1)]
               [.ite (eEq (v "args") (n 1))
                 (keywordCheck ++ [.ite (v "ok") [.assign "r" (n 1)] [.assign "r" (n 7)]])
                 [.assign "r" (n 7)]]]
             [.ite (eEq (v "cmd") (n 2))
               [.ite (eEq (v "args") (n 0)) [.assign "r" (n 2)] [.assign "r" (n 7)]]
               [.ite (eEq (v "cmd") (n 3))
                 [.ite (eEq (v "args") (n 0)) [.assign "r" (n 3)] [.assign "r" (n 7)]]
                 [.ite (eEq (v "args") (n 0)) [.assign "r" (n 4)]
                   [.ite (eEq (v "args") (n 1))
                     (numberCheck ++
                      [.ite (v "ok") [.assign "r" (n 4)]
                        (messageIdCheck ++
                         [.ite (v "ok") [.assign "r" (n 5)] [.assign "r" (n 7)]])])
                     [.assign "r" (n 7)]]]]]]]])]

/-! ## A connection's turn -/

/-- The record's fields as expressions. -/
def outLen : PExpr := fld "cb" cOutLen
def phase : PExpr := fld "cb" cPhase
def heldEmpty : PExpr := eEq (fld "cb" cHeldPos) (fld "cb" cHeldLen)

/-- Answer the first held line that gets a reply and frame on past the lines that get none, as
`DN.News.SessionSpec.serve` does. -/
def serve : List PStmt :=
  [.dec "blk" (atOff (v "cb") cFramer), .dec "p" (atOff (v "cb") cHeld),
   .dec "n" (fld "cb" cHeldLen), .dec "i" (fld "cb" cHeldPos), .dec "sv" (n 1),
   .while (v "sv")
     [.ite (eEq (v "i") (v "n")) [.assign "sv" (n 0)]
       ([.dec "i0" (v "i")] ++ News.FramerCode.lineDecs ++
        News.FramerCode.lineFrag News.SessionSpec.lineLimit ++
        [.ite (eEq (v "kind") (n 0)) [.assign "sv" (n 0)]
          ([.dec "r" (n 0)] ++ classify ++
           [.ite (eEq (v "r") (n 0)) []
             [.ite (ne outLen (n 0)) [.assign "i" (v "i0"), .assign "sv" (n 0)]
               (writeReply ++
                [setf "cb" cFirst (n 0),
                 setf "cb" cIdle (eAdd (v "now") (n News.SessionSpec.inactivity)),
                 .ite (eEq (v "r") (n 3))
                   [setf "cb" cPhase (n 1), .assign "i" (v "n"), .assign "sv" (n 0)] []])]])])],
   .ite (eEq (v "i") (v "n")) [setf "cb" cHeldPos (n 0), setf "cb" cHeldLen (n 0)]
     [setf "cb" cHeldPos (v "i")]]

/-- The action slot the `a`-th action of the turn lies in. -/
def slotOf (a : PExpr) : PExpr := eAdd (at_ (emitOff + emitActions)) (eMul a (n actionSlot))

/-- An action with no bytes for the connection `c`. -/
def closing (kind : Nat) : List PStmt :=
  [.dec "slot" (slotOf (v "m")), setf "slot" actionKind (n kind), setf "slot" actionIdx (v "c"),
   setf "slot" actionGen (fld "cb" cGen), setf "slot" actionLen (n 0),
   setf "slot" actionRead (n 0), setf "slot" actionTaken (n 0), inc "m",
   setf "cb" cActed (n 1), setf "cb" cLive (n 0)]

/-- The connection's output as a send, and whether to read once it is taken. -/
def sending : List PStmt :=
  [.dec "slot" (slotOf (v "m")), .dec "ol" outLen, setf "slot" actionKind (n send),
   setf "slot" actionIdx (v "c"), setf "slot" actionGen (fld "cb" cGen),
   setf "slot" actionLen (v "ol"), setf "slot" actionRead (v "wants"),
   setf "slot" actionTaken (n 0)] ++
  copyNew "aj" (atOff (v "slot") actionHead) (atOff (v "cb") cOut) (v "ol") ++
  [inc "m", setf "cb" cActed (n 1), setf "cb" cReading (v "wants")]

/-- The line's deadline runs while the program waits for the rest of a line, as
`DN.News.SessionSpec.Conn.waitLine` says. -/
def waitLine : List PStmt :=
  [.ite (eAnd (eAnd (eEq outLen (n 0)) (eEq phase (n 0)))
      (eLt (n 0)
        (eAdd (eAdd (fld "cb" cFramer) (fld "cb" (cFramer + 8))) (fld "cb" (cFramer + 16)))))
     [.ite (eEq (fld "cb" cLineDue) (n 0))
       [setf "cb" cLineDue (eAdd (v "now") (n News.SessionSpec.lineTime))] []]
     [setf "cb" cLineDue (n 0)]]

/-- One connection in use, after the batch's events. -/
def act : List PStmt :=
  [.dec "due" (or2 (or2
      (eAnd (ne (fld "cb" cFirst) (n 0)) (eLe (fld "cb" cFirst) (v "now")))
      (eLe (fld "cb" cIdle) (v "now")))
      (eAnd (ne (fld "cb" cLineDue) (n 0)) (eLe (fld "cb" cLineDue) (v "now")))),
   .ite (v "due") (closing closeNow)
     [.ite (eAnd (eEq outLen (n 0)) (ne phase (n 1))) serve [],
      .dec "wants" (eAnd (eEq phase (n 0)) heldEmpty),
      .ite (ne outLen (n 0))
        [.ite (eEq (fld "cb" cBlocked) (n 0)) sending []]
        [.ite (or2 (eEq phase (n 1)) (eAnd (eEq phase (n 2)) heldEmpty))
          (closing closeGracefully) []],
      .ite (fld "cb" cLive) waitLine []]]

/-! ## A turn -/

def record (idx : PExpr) : PExpr := eAdd (at_ tableOff) (eMul idx (n connSlot))

/-- A new connection, greeted. -/
def openConn : List PStmt :=
  [.ite (fld "cb" cLive) (breach .reopened)
    ([setf "cb" cLive (n 1), setf "cb" cGen (v "eg"), setf "cb" cPhase (n 0),
      setf "cb" cReading (n 0), setf "cb" cBlocked (n 0),
      setf "cb" cFirst (eAdd (v "now") (n News.SessionSpec.firstCommand)),
      setf "cb" cIdle (eAdd (v "now") (n News.SessionSpec.inactivity)),
      setf "cb" cLineDue (n 0), setf "cb" cHeldLen (n 0), setf "cb" cHeldPos (n 0),
      setf "cb" cFramer (n 0), setf "cb" (cFramer + 8) (n 0), setf "cb" (cFramer + 16) (n 0)] ++
     writeGreeting)]

/-- Whether the connection may report input: it takes commands, asked to read, and has nothing
untaken and nothing held. -/
def asked : PExpr :=
  eAnd (eAnd (eEq phase (n 0)) (fld "cb" cReading)) (eAnd (eEq outLen (n 0)) heldEmpty)

/-- One event of the batch. -/
def event : List PStmt :=
  [.dec "ev" (eAdd (at_ (nextOff + nextEvents)) (eMul (v "e") (n eventSlot))),
   .dec "ek" (fld "ev" eventKind), .dec "ex" (fld "ev" eventIdx), .dec "eg" (fld "ev" eventGen),
   .dec "el" (fld "ev" eventLen),
   .ite (or2 (eLt (v "ex") (n 0)) (eLe (n conns) (v "ex"))) (breach .noSuchIndex) [],
   .ite (or2 (eLt (v "ek") (n opened)) (eLt (n closed) (v "ek"))) (stop unknownEvent) [],
   .dec "cb" (record (v "ex")),
   .dec "lv" (eAnd (fld "cb" cLive) (eEq (fld "cb" cGen) (v "eg"))),
   .ite (eEq (v "ek") (n opened)) openConn [],
   .ite (eEq (v "ek") (n received))
     [.ite (or2 (eLt (v "el") (n 0)) (eLt (n data) (v "el"))) (breach .tooLong) [],
      .ite (v "lv")
        [.ite asked
          (copyNew "hj" (atOff (v "cb") cHeld) (atOff (v "ev") eventHead) (v "el") ++
           [setf "cb" cHeldLen (v "el"), setf "cb" cHeldPos (n 0)])
          (breach .unasked)] []] [],
   .ite (eEq (v "ek") (n writable)) [.ite (v "lv") [setf "cb" cBlocked (n 0)] []] [],
   .ite (eEq (v "ek") (n inputEnded))
     [.ite (v "lv")
       [.ite asked [setf "cb" cPhase (n 2), setf "cb" cLineDue (n 0)] (breach .unasked)] []] [],
   .ite (eEq (v "ek") (n closed)) [.ite (v "lv") [setf "cb" cLive (n 0)] []] [],
   inc "e"]

/-- What the host took of the connection `sc`'s action, the `a`-th of the turn: for a send, the
output left, whether to wait for the host, and activity. Of the action slot only the count the
host wrote back is read; the rest the program knows from its own record. -/
def settle : List PStmt :=
  [.dec "cb" (record (v "sc")),
   .ite (fld "cb" cActed)
     [setf "cb" cActed (n 0),
      .ite (fld "cb" cLive)
        ([.dec "tk" (ld (atOff (slotOf (v "a")) actionTaken)), .dec "al" outLen,
          .ite (or2 (eLt (v "tk") (n 0)) (eLt (v "al") (v "tk"))) (breach .overTaken) [],
          .dec "ob" (atOff (v "cb") cOut), .dec "sj" (v "tk"),
          .while (eLt (v "sj") (v "al"))
            [.storeb (eAdd (v "ob") (eSub (v "sj") (v "tk"))) (.loadb (eAdd (v "ob") (v "sj"))),
             inc "sj"],
          setf "cb" cOutLen (eSub (v "al") (v "tk")), setf "cb" cBlocked (eLt (v "tk") (v "al")),
          .ite (eLt (n 0) (v "tk"))
            [setf "cb" cIdle (eAdd (v "now") (n News.SessionSpec.inactivity))] []] ++
         waitLine) [],
      inc "a"] [],
   inc "sc"]

/-- The time of the next turn, as `DN.News.SessionSpec.deadline` gives it, where the host reads it
in the next call. -/
def wake : List PStmt :=
  [.dec "dl" (n 0), .dec "rd" (n 0), .dec "dt" (n 0),
   .while (eLt (v "dt") (n conns))
     [.dec "cb" (record (v "dt")),
      .ite (fld "cb" cLive)
        [.ite (eAnd (eEq outLen (n 0)) (or2 (eEq heldEmpty (n 0)) (ne phase (n 0))))
           [.assign "rd" (n 1)] [],
         .dec "ea" (fld "cb" cIdle),
         .ite (eAnd (ne (fld "cb" cFirst) (n 0)) (eLt (fld "cb" cFirst) (v "ea")))
           [.assign "ea" (fld "cb" cFirst)] [],
         .ite (eAnd (ne (fld "cb" cLineDue) (n 0)) (eLt (fld "cb" cLineDue) (v "ea")))
           [.assign "ea" (fld "cb" cLineDue)] [],
         .ite (or2 (eEq (v "dl") (n 0)) (eLt (v "ea") (v "dl"))) [.assign "dl" (v "ea")] []] [],
      inc "dt"],
   .ite (v "rd") [.ite (eLt (v "now") (n 1)) [.assign "dl" (n 1)] [.assign "dl" (v "now")]] [],
   .store (at_ (nextOff + nextWake)) (v "dl")]

/-- The revision and the address of the source, taken in once from the first batch: each of a
length that fits the replies and of visible bytes only. -/
def identity : List PStmt :=
  [.ite (eEq (ld (at_ (ownOff + ownReady))) (n 0))
    ([.dec "rvl" (ld (at_ (nextOff + nextRevLen))), .dec "scl" (ld (at_ (nextOff + nextSrcLen))),
     .ite (or2 (or2 (eLt (v "rvl") (n 1)) (eLt (n revMax) (v "rvl")))
        (or2 (eLt (v "scl") (n 1)) (eLt (n srcMax) (v "scl")))) (stop badIdentity) [],
     .dec "ij" (n 0),
     .while (eLt (v "ij") (v "rvl"))
       [.dec "cz" (.loadb (eAdd (at_ (nextOff + nextRev)) (v "ij"))),
        .ite (or2 (eLt (v "cz") (n 33)) (eLt (n 126) (v "cz"))) (stop badIdentity) [],
        inc "ij"],
     .assign "ij" (n 0),
     .while (eLt (v "ij") (v "scl"))
       [.dec "cz" (.loadb (eAdd (at_ (nextOff + nextSrc)) (v "ij"))),
        .ite (or2 (eLt (v "cz") (n 33)) (eLt (n 126) (v "cz"))) (stop badIdentity) [],
        inc "ij"],
     .dec "ik" (n 0)] ++
    copy "ik" (at_ (ownOff + ownRev)) (at_ (nextOff + nextRev)) (v "rvl") ++
    copy "ik" (at_ (ownOff + ownSrc)) (at_ (nextOff + nextSrc)) (v "scl") ++
    [.store (at_ (ownOff + ownRevLen)) (v "rvl"), .store (at_ (ownOff + ownSrcLen)) (v "scl"),
     .store (at_ (ownOff + ownReady)) (n 1)])
    []]

/-- The external calls, each with the configuration word and one of the two arrays. -/
def fetch : PStmt := .ffi nextName [at_ confOff, n confLen, at_ nextOff, n nextLen]
def hand : PStmt := .ffi emitName [at_ confOff, n confLen, at_ emitOff, n emitLen]

/-- One turn of the loop. -/
def turn : List PStmt :=
  [fetch,
   .dec "k" (ld (at_ (nextOff + nextCount))),
   .ite (or2 (eLt (v "k") (n 0)) (eLt (n batch) (v "k"))) (breach .tooManyEvents) [],
   .dec "now" (ld (at_ (nextOff + nextClock))),
   .ite (or2 (eLt (v "now") (ld (at_ (ownOff + ownClock))))
      (eLe (n News.SessionSpec.clockLimit) (v "now"))) (breach .badClock) [],
   .store (at_ (ownOff + ownClock)) (v "now")] ++
  identity ++
  [.dec "e" (n 0), .while (eLt (v "e") (v "k")) event,
   .dec "m" (n 0), .dec "c" (n 0),
   .while (eLt (v "c") (n conns))
     [.dec "cb" (record (v "c")), .ite (fld "cb" cLive) act [], inc "c"],
   .store (at_ (emitOff + emitCount)) (v "m"),
   hand,
   .dec "a" (n 0), .dec "sc" (n 0), .while (eLt (v "sc") (n conns)) settle] ++
  wake

/-- `main`: the version, the texts, an empty table, then the loop. -/
def main : PFun :=
  { name := "main", body :=
    [.store (at_ confOff) (n version), .store (at_ (ownOff + ownClock)) (n 0),
     .store (at_ (ownOff + ownReady)) (n 0), .store (at_ (ownOff + ownStop)) (n 0)] ++
    textsInit ++
    [.dec "zt" (n 0),
     .while (eLt (v "zt") (n conns))
       [.store (atOff (record (v "zt")) cLive) (n 0), .store (atOff (record (v "zt")) cActed) (n 0),
        inc "zt"],
     .store (at_ (nextOff + nextWake)) (n 0),
     .dec "going" (n 1),
     .while (v "going") turn,
     .ret (n 0)] }

/-- The source the gate prints. -/
def source : Except Checked.Reason String := Checked.emitMain [nextName, emitName] main

def regression_824 : Bool := source.isOk

end DN.Server.Session
