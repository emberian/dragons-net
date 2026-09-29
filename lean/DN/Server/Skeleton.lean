-- SPDX-License-Identifier: AGPL-3.0-or-later
import DN.Compiler.Checked
import DN.Server.Layout

/-!
# DN.Server.Skeleton

The server's loop with nothing of NNTP in it yet: `main` fetches a batch of events from its host,
answers every batch of received bytes by sending the same bytes back, and hands the host the
batch of actions, for ever. It is the shape the NNTP session is built in
(docs/decisions/0003-nntp-slice.md), and the program the safety theorem is first proved for.

Every count and length the host writes is checked before it is used, so no host can make the
program read or write outside its layout; a host that writes one out of range ends the run with a
return (1 for the count of events, 2 for a length, as the model sees it: the start-up code of a
program built without `--main_return` passes the host no value). The number of actions is checked
against the batch as well (3), though the count of events already bounds it: the safety analysis
sees ranges, not that one counter stays below another. The loop itself never finishes, so the run
never falls off the end of `main`.
-/

namespace DN.Server.Skeleton

open DN.Compiler DN.Compiler.Syntax DN.Server.Layout

/-- `@base + off`. -/
def at_ (off : Nat) : PExpr := atOff .base off

/-- The external calls, each with the configuration word and one of the two arrays. -/
def fetch : PStmt := .ffi nextName [at_ confOff, n confLen, at_ nextOff, n nextLen]
def hand : PStmt := .ffi emitName [at_ confOff, n confLen, at_ emitOff, n emitLen]

/-- Copy `len` bytes of the event's data into the action's data. -/
def copyData : List PStmt :=
  [.dec "j" (n 0),
   .while (eLt (v "j") (v "len"))
     [.storeb (eAdd (eAdd (v "ac") (n actionHead)) (v "j"))
        (.loadb (eAdd (eAdd (v "ev") (n eventHead)) (v "j"))),
      .assign "j" (eAdd (v "j") (n 1))]]

/-- Answer received bytes with a send of the same bytes, reading on afterwards. -/
def echo : List PStmt :=
  [.ite (eLt (v "len") (n 0)) [.ret (n 2)] [],
   .ite (eLt (n data) (v "len")) [.ret (n 2)] [],
   .ite (eLt (n (batch - 1)) (v "m")) [.ret (n 3)] [],
   .dec "ac" (eAdd (at_ (emitOff + emitActions)) (eMul (v "m") (n actionSlot))),
   .store (v "ac") (n send),
   .store (eAdd (v "ac") (n actionIdx)) (.loadw 1 (eAdd (v "ev") (n eventIdx))),
   .store (eAdd (v "ac") (n actionGen)) (.loadw 1 (eAdd (v "ev") (n eventGen))),
   .store (eAdd (v "ac") (n actionLen)) (v "len"),
   .store (eAdd (v "ac") (n actionRead)) (n 1),
   .store (eAdd (v "ac") (n actionTaken)) (n 0)] ++ copyData ++
  [.assign "m" (eAdd (v "m") (n 1))]

/-- One event: received bytes are echoed, every other event is left alone. -/
def event : List PStmt :=
  [.dec "ev" (eAdd (at_ (nextOff + nextEvents)) (eMul (v "i") (n eventSlot))),
   .dec "len" (.loadw 1 (eAdd (v "ev") (n eventLen))),
   .ite (eEq (.loadw 1 (v "ev")) (n received)) echo [],
   .assign "i" (eAdd (v "i") (n 1))]

/-- One turn of the loop: fetch a batch, answer it, hand over the answers. -/
def turn : List PStmt :=
  [fetch,
   .dec "k" (.loadw 1 (at_ nextOff)),
   .ite (eLt (v "k") (n 0)) [.ret (n 1)] [],
   .ite (eLt (n batch) (v "k")) [.ret (n 1)] [],
   .dec "i" (n 0),
   .dec "m" (n 0),
   .while (eLt (v "i") (v "k")) event,
   .store (at_ emitOff) (v "m"),
   .store (at_ (emitOff + emitWake)) (n 0),
   hand]

/-- `main`: write the layout's version where both calls read it, then loop. -/
def main : PFun :=
  { name := "main", body :=
    [.store (at_ confOff) (n version),
     .dec "going" (n 1),
     .while (v "going") turn,
     .ret (n 0)] }

/-- The source the gate prints. -/
def source : Except Checked.Reason String := Checked.emitMain [nextName, emitName] main

/-- The gate accepts the loop. -/
def regression_818 : Bool := source.isOk

end DN.Server.Skeleton
