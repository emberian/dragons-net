-- SPDX-License-Identifier: AGPL-3.0-or-later
import DN.News.ArticleProg
import DN.News.CrcProg
import DN.News.FramerProg
import DN.News.SipProg
import DN.Server.SessionLayout

/-!
# DN.Server.SessionStore

The store's side of `DN.News.PostSpec` as functions of the session's program (`DN.Server.Session`),
each after those it calls. A slot frames an article's octets as they come, checks its header section
with `DN.News.ArticleProg`'s `artCheck` in that program's area, and reserves its Message-ID and
number; its file is written by jobs, one in flight a slot, and its commit appended to the journal; a
completion moves the slot on. The Message-IDs the store holds are found in an index of `indexCells`
cells by SipHash-2-4 under the index's key, probed one after another; the commits are recovery's,
in its area, and each one the store makes after them.

A read keeps only the octets of its last job: each is checked as it comes, the check carried from
one job to the next, and what it gives is made from them, its 220, 221 or 222 line and its Xref,
made when it starts, an octet at a time from where it has given to.

A function returns zero, or the code it stopped the run with, written where the host reads it at
exit, which its caller returns in turn; what it finds it leaves in `ownRet`. Each checks a word it
reads back from the heap before it makes an address of it, and stops on one out of range with
`SessionLayout.brokenState`, as `main` does; on a completion the host may not report, with the code
of its `DN.News.PostSpec.Fault`. Tested against `dn-compiler session-model`, not proven.
-/

namespace DN.Server.SessionStore

open DN.Compiler DN.Compiler.Syntax DN.Server.SessionLayout
open DN.News.Journal (headerLength maxPayload maxFrame)

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
def ifs (c : PExpr) (t : List PStmt) : PStmt := .ite c t []
/-- `a` below `b`, both as numbers of 64 bits. -/
def ult (a b : PExpr) : PExpr := eLt (eXor a (n (2 ^ 63))) (eXor b (n (2 ^ 63)))

/-- Stop the run with `code`: written where the host reads it at exit, then returned. -/
def stop (code : Nat) : List PStmt := [.store (at_ (ownOff + ownStop)) (n code), .ret (n code)]

/-- Stop if `e` lies outside `[0, hi]`: a word the program reads back from its own area is checked
to be as the program keeps it. -/
def keptIn (e : PExpr) (hi : Nat) : PStmt :=
  .ite (or2 (eLt e (n 0)) (eLt (n hi) e)) (stop brokenState) []

def copyLoop (j : String) (dst src len : PExpr) : PStmt :=
  .while (eLt (v j) len) [.storeb (eAdd dst (v j)) (.loadb (eAdd src (v j))), inc j]

/-- Copy `len` bytes from `src` to `dst`, with the counter `j` the caller has declared. -/
def copy (j : String) (dst src len : PExpr) : List PStmt :=
  [.assign j (n 0), copyLoop j dst src len]

/-- The same with a counter `j` of its own. -/
def copyNew (j : String) (dst src len : PExpr) : List PStmt :=
  [.dec j (n 0), copyLoop j dst src len]

/-- A function called, and the run stopped if it stopped. -/
def callS (r f : String) (args : List PExpr) : List PStmt :=
  [.call r f args, .ite (v r) [.ret (v r)] []]

/-- What the function called last found. -/
def found : PExpr := ld (at_ (ownOff + ownRet))
def give (e : PExpr) : List PStmt := [.store (at_ (ownOff + ownRet)) e, .ret (n 0)]
def done0 : PStmt := .ret (n 0)

/-- The store's words, recovery's area, which holds the commits, and the article's area. -/
def sw (o : Nat) : PExpr := ld (at_ (ownOff + o))
def sset (o : Nat) (e : PExpr) : PStmt := .store (at_ (ownOff + o)) e
def rw (o : Nat) : PExpr := ld (at_ (recOff + o))
def rset (o : Nat) (e : PExpr) : PStmt := .store (at_ (recOff + o)) e
def aw (o : Nat) : PExpr := ld (at_ (artOff + o))
def aset (o : Nat) (e : PExpr) : PStmt := .store (at_ (artOff + o)) e

/-- The slot the local `x` numbers, checked, as the local `zs`. -/
def slotOf (x : String) : List PStmt :=
  [keptIn (v x) (posts - 1), .dec "zs" (eAdd (at_ slotsOff) (eMul (v x) (n slotLen)))]
def zw (f : Nat) : PExpr := fld "zs" f
def zset (f : Nat) (e : PExpr) : PStmt := setf "zs" f e
def zbuf (i : PExpr) : PExpr := eAdd (atOff (v "zs") zBuf) i

/-- For each slot, as `zs`, `body`, counted by `kk`. -/
def eachSlot (body : List PStmt) : List PStmt :=
  [.dec "kk" (n 0),
   .while (eLt (v "kk") (n posts))
     ([.dec "zs" (eAdd (at_ slotsOff) (eMul (v "kk") (n slotLen)))] ++ body ++ [inc "kk"])]

/-- The codes of a file, a task and an outcome (`DN.News.PostSpec`). -/
def fileNone : Nat := 0
def fileOpen : Nat := 1
def fileClosed : Nat := 2
def fileFinal : Nat := 3
def filePlaced : Nat := 4
def taskCreate : Nat := 1
def taskWrite : Nat := 2
def taskFinish : Nat := 3
def taskPlace : Nat := 4
def taskCommit : Nat := 5
def taskClean : Nat := 6
def outPosted : Nat := 1
def outFailed : Nat := 2
def outLost : Nat := 3

def rules : News.PostSpec.Rules := {}
def jobData : Nat := News.PostSpec.jobData
def headerMax : Nat := News.PostSpec.headerMax
def capacity : Nat := rules.capacity

/-- Whether the slot at `zs` holds a Message-ID reserved: an article not refused. -/
def reserving : PExpr := eAnd (eAnd (zw zLive) (zw zHas)) (eEq (zw zRefused) (n 0))
def busyWith (t : Nat) : PExpr := eAnd (zw zBusy) (eEq (zw zTask) (n t))

/-- An operation of a file job (decision 0005). -/
structure Op where
  code : Nat
  place : PExpr := n 0
  gen : PExpr := n 0
  name : PExpr := n 0
  number : PExpr := n 0
  toName : PExpr := n 0
  toNumber : PExpr := n 0
  offset : PExpr := n 0
  length : PExpr := n 0

/-- Operation `i` of the job at `jb`; its bytes, if it has any, are the job's first. -/
def putOpAt (jb : PExpr) (i : Nat) (o : Op) : List PStmt :=
  [(opCode, n o.code), (opHandle, o.place), (opHandleGen, o.gen), (opName, o.name),
   (opNumber, o.number), (opToName, o.toName), (opToNumber, o.toNumber), (opOffset, o.offset),
   (opLength, o.length), (opData, n 0)].map fun (f, e) =>
    .store (atOff jb (jobOpsAt + i * opSlot + f)) e

/-! ## A slot's state -/

/-- `Slot.takes`: the block goes on and fewer than a job's octets wait to be written. -/
def takesE : PExpr :=
  eAnd (eEq (zw zEnded) (n 0)) (or2 (eEq (zw zHas) (n 0)) (eLt (zw zPend) (n jobData)))

def postTakes : PFun :=
  { name := "postTakes", params := [(1, "k")], body := slotOf "k" ++ give takesE }

/-- `Slot.tidy` of slot `k`, as the store accepts or not. -/
def postTidy : PFun :=
  { name := "postTidy", params := [(1, "k")], body := slotOf "k" ++
    [ifs (zw zLive)
      [ifs (eAnd (eAnd (eEq (sw ownAccepting) (n 0)) (eEq (zw zOutcome) (n 0)))
          (eEq (busyWith taskCommit) (n 0))) [zset zRefused (n 1)],
       ifs (eAnd (eAnd (eEq (zw zOutcome) (n 0)) (zw zRefused))
          (eAnd (zw zEnded) (eEq (zw zBusy) (n 0)))) [zset zOutcome (n outFailed)],
       ifs (eAnd (eAnd (zw zRefused) (eEq (zw zBusy) (n 0)))
          (eAnd (zw zHas) (eEq (zw zFile) (n fileNone)))) [zset zHas (n 0)],
       ifs (eAnd (eAnd (eEq (zw zOwner) (n 0)) (eEq (zw zBusy) (n 0))) (eEq (zw zHas) (n 0)))
         [zset zLive (n 0)]],
     done0] }

/-- The codes of a read's file and task (`DN.News.PostSpec.ReadFile`, `ReadTask`). -/
def readNone : Nat := 0
def readOpen : Nat := 1
def readGone : Nat := 2
def taskOpen : Nat := 1
def taskRead : Nat := 2
def taskReadLast : Nat := 3
def taskClose : Nat := 4

/-- The read the local `x` numbers, checked, as the local `rs`. -/
def readOf (x : String) : List PStmt :=
  [keptIn (v x) (reads - 1), .dec "rs" (eAdd (at_ readsOff) (eMul (v x) (n readLen)))]
def rdw (f : Nat) : PExpr := fld "rs" f
def rdset (f : Nat) (e : PExpr) : PStmt := setf "rs" f e

/-- For each read, as `rs`, `body`, counted by `kr`. -/
def eachRead (body : List PStmt) : List PStmt :=
  [.dec "kr" (n 0),
   .while (eLt (v "kr") (n reads))
     ([.dec "rs" (eAdd (at_ readsOff) (eMul (v "kr") (n readLen)))] ++ body ++ [inc "kr"])]

/-- `Store.tidy`: each slot's `Slot.tidy`, and each read forgotten once it has no owner, no job in
flight and no file open (`Read.tidy`). -/
def postTidyAll : PFun :=
  { name := "postTidyAll", body :=
    [.dec "kk" (n 0),
     .while (eLt (v "kk") (n posts)) (callS "t" "postTidy" [v "kk"] ++ [inc "kk"])] ++
    eachRead [ifs (eAnd (eAnd (rdw rLive) (eEq (rdw rOwner) (n 0)))
        (eAnd (eEq (rdw rBusy) (n 0)) (ne (rdw rFile) (n readOpen)))) [rdset rLive (n 0)]] ++
    [done0] }

/-! ## The connections that wait -/

/-- The queues: the POSTs that wait for a slot (`Store.waiters`), zero, and the connections that
wait for a read (`Store.readers`), one; each a count, then an index and a generation each. -/
def waiters : PExpr := n 0
def readers : PExpr := n 1

/-- The queue the local `qs` names, as `q`. -/
def queueOf : List PStmt :=
  [keptIn (v "qs") 1, .dec "q" (eAdd (at_ (ownOff + ownWaitN)) (eMul (v "qs") (n (ownReadN - ownWaitN))))]

def waitAt (w : PExpr) : PExpr := eAdd (atOff (v "q") 8) (eMul w (n 16))

/-- The connection `x` of generation `g` waits in queue `qs` after those that came before it. -/
def queueAdd : PFun :=
  { name := "queueAdd", params := [(1, "qs"), (1, "x"), (1, "g")], body := queueOf ++
    [.dec "wn" (ld (v "q")), keptIn (v "wn") (conns - 1),
     .store (waitAt (v "wn")) (v "x"), .store (atOff (waitAt (v "wn")) 8) (v "g"),
     .store (v "q") (eAdd (v "wn") (n 1)), done0] }

/-- Where in queue `q` the connection `x` of generation `g` is, as `at`; the count, as `wn`, when
it is not there. -/
def placeOf : List PStmt :=
  [.dec "wn" (ld (v "q")), keptIn (v "wn") conns, .dec "w" (n 0), .dec "at" (v "wn"),
   .while (eLt (v "w") (v "wn"))
     [ifs (eAnd (eEq (v "at") (v "wn"))
         (eAnd (eEq (ld (waitAt (v "w"))) (v "x")) (eEq (ld (atOff (waitAt (v "w")) 8)) (v "g"))))
        [.assign "at" (v "w")],
      inc "w"]]

/-- It no longer waits in queue `qs`. -/
def queueDrop : PFun :=
  { name := "queueDrop", params := [(1, "qs"), (1, "x"), (1, "g")], body := queueOf ++ placeOf ++
    [ifs (eLt (v "at") (v "wn"))
      [.dec "u" (v "at"),
       .while (eLt (eAdd (v "u") (n 1)) (v "wn"))
         [.store (waitAt (v "u")) (ld (waitAt (eAdd (v "u") (n 1)))),
          .store (atOff (waitAt (v "u")) 8) (ld (atOff (waitAt (eAdd (v "u") (n 1))) 8)), inc "u"],
       .store (v "q") (eSub (v "wn") (n 1))],
     done0] }

/-- `Store.admits`: fewer came before it than slots are free. -/
def postAdmits : PFun :=
  { name := "postAdmits", params := [(1, "x"), (1, "g")], body :=
    [.dec "qs" waiters] ++ queueOf ++ placeOf ++
    [.dec "fr" (n 0)] ++ eachSlot [ifs (eEq (zw zLive) (n 0)) [inc "fr"]] ++
    give (eAnd (eLt (v "at") (v "wn")) (eLt (v "at") (v "fr"))) }

/-- `Store.admitsRead`: fewer came before it than reads are free. -/
def readAdmits : PFun :=
  { name := "readAdmits", params := [(1, "x"), (1, "g")], body :=
    [.dec "qs" readers] ++ queueOf ++ placeOf ++
    [.dec "fr" (n 0)] ++ eachRead [ifs (eEq (rdw rLive) (n 0)) [inc "fr"]] ++
    give (eAnd (eLt (v "at") (v "wn")) (eLt (v "at") (v "fr"))) }

/-- `Store.abandon`: the connection `x` of generation `g` gone, or no longer reading. -/
def postAbandon : PFun :=
  { name := "postAbandon", params := [(1, "x"), (1, "g")], body :=
    eachSlot [ifs (eAnd (eAnd (zw zLive) (zw zOwner))
        (eAnd (eEq (zw zOwnIdx) (v "x")) (eEq (zw zOwnGen) (v "g"))))
      [zset zOwner (n 0), ifs (eEq (zw zEnded) (n 0)) [zset zRefused (n 1)]]] ++
    eachRead [ifs (eAnd (eAnd (rdw rLive) (rdw rOwner))
        (eAnd (eEq (rdw rOwnIdx) (v "x")) (eEq (rdw rOwnGen) (v "g")))) [rdset rOwner (n 0)]] ++
    callS "u" "queueDrop" [waiters, v "x", v "g"] ++ callS "u2" "queueDrop" [readers, v "x", v "g"] ++
    callS "t" "postTidyAll" [] ++ [done0] }

/-- Slot `k` given to the POST of the connection `x` of generation `g`, of number `num`. -/
def postClaim : PFun :=
  { name := "postClaim", params := [(1, "k"), (1, "x"), (1, "g"), (1, "num")], body := slotOf "k" ++
    ([(zLive, n 1), (zOwner, n 1), (zOwnIdx, v "x"), (zOwnGen, v "g"), (zConn, v "num"),
      (zPh, n 0), (zBad, n 0), (zArrived, n 0), (zEnded, n 0), (zBody, n 0), (zBol, n 1),
      (zRefused, n 0), (zOutcome, n 0), (zHas, n 0), (zPend, n 0), (zBusy, n 0)].map
      fun (f, e) => zset f e) ++ [done0] }

/-! ## The index of Message-IDs -/

def cell (x : PExpr) : PExpr := eAdd (at_ indexOff) (eMul x (n 8))

/-- The cell the `n` octets at `ownId` hash to under the index's key. -/
def idHash : PFun :=
  { name := "idHash", params := [(1, "n")], body :=
    [keptIn (v "n") 250, .dec "k" (at_ (ownOff + ownIndexKey)), .dec "p" (at_ (ownOff + ownId))] ++
    ["r", "m", "v0", "v1", "v2", "v3", "off", "j"].map (.dec · (n 0)) ++ News.SipProg.sipSrc ++
    give (eAnd (v "r") (n (indexCells - 1))) }

/-- The commit numbered by the local `ci` in recovery's area, checked, as `sl`, the length of its
Message-ID as `sn`. -/
def commitAt (ci : String) : List PStmt :=
  [keptIn (v ci) (capacity - 1),
   .dec "sl" (eAdd (at_ (recOff + News.RecoverProg.rSlots))
     (eMul (v ci) (n News.RecoverProg.slotSize))),
   .dec "sn" (eAnd (.shr (fld "sl" News.RecoverProg.slotMisc) (n 8)) (n 255))]

/-- Whether the store holds the `n` octets at `ownId` as a Message-ID: zero, or one more than its
commit's place in recovery's area. -/
def idFind : PFun :=
  { name := "idFind", params := [(1, "n")], body :=
    [keptIn (v "n") 250] ++ callS "h" "idHash" [v "n"] ++
    [.dec "x" found, keptIn (v "x") (indexCells - 1), .dec "t" (n 0),
     .while (eLt (v "t") (n indexCells))
       ([.dec "ce" (ld (cell (v "x"))),
         ifs (eEq (v "ce") (n 0)) (give (n 0)),
         .dec "ci" (eSub (v "ce") (n 1))] ++ commitAt "ci" ++
        [ifs (eEq (v "sn") (v "n"))
          [.dec "same" (n 1), .dec "j" (n 0),
           .while (eLt (v "j") (v "n"))
             [ifs (ne (.loadb (eAdd (atOff (v "sl") News.RecoverProg.slotId) (v "j")))
                 (.loadb (eAdd (at_ (ownOff + ownId)) (v "j")))) [.assign "same" (n 0)],
              inc "j"],
           ifs (v "same") (give (v "ce"))],
         .assign "x" (eAnd (eAdd (v "x") (n 1)) (n (indexCells - 1))), inc "t"])] ++
    give (n 0) }

/-- The commit `ci` put in the index. -/
def idAdd : PFun :=
  { name := "idAdd", params := [(1, "ci")], body := commitAt "ci" ++
    [keptIn (v "sn") 250] ++
    copyNew "j" (at_ (ownOff + ownId)) (atOff (v "sl") News.RecoverProg.slotId) (v "sn") ++
    callS "h" "idHash" [v "sn"] ++
    [.dec "x" found, keptIn (v "x") (indexCells - 1), .dec "t" (n 0),
     .while (eLt (v "t") (n indexCells))
       [ifs (eEq (ld (cell (v "x"))) (n 0)) [.store (cell (v "x")) (eAdd (v "ci") (n 1)), done0],
        .assign "x" (eAnd (eAdd (v "x") (n 1)) (n (indexCells - 1))), inc "t"]] ++
    stop brokenState }

/-- The index of the commits recovery found. -/
def idBuild : PFun :=
  { name := "idBuild", body :=
    [.dec "x" (n 0), .while (eLt (v "x") (n indexCells)) [.store (cell (v "x")) (n 0), inc "x"],
     .dec "cm" (rw News.RecoverProg.rCommits), keptIn (v "cm") capacity, .dec "ci" (n 0),
     .while (eLt (v "ci") (v "cm")) (callS "a" "idAdd" [v "ci"] ++ [inc "ci"]),
     done0] }

/-- The CRC-32C's table. -/
def crcTable : PFun :=
  { name := "crcTable", body :=
    [.dec "t" (at_ (ownOff + ownCrc)), .dec "i" (n 0), .dec "c" (n 0)] ++ News.CrcProg.fillSrc ++
      [done0] }

/-! ## An article's header section -/

/-- Whether a slot other than `k` holds the `n` octets at `ownId` reserved. -/
def postReserved : PFun :=
  { name := "postReserved", params := [(1, "k"), (1, "n")], body :=
    [keptIn (v "n") 250] ++ eachSlot
      [ifs (eAnd (ne (v "kk") (v "k")) (eAnd reserving (eEq (zw zMsgLen) (v "n"))))
        [.dec "same" (n 1), .dec "j" (n 0),
         .while (eLt (v "j") (v "n"))
           [ifs (ne (.loadb (eAdd (atOff (v "zs") zMsg) (v "j")))
               (.loadb (eAdd (at_ (ownOff + ownId)) (v "j")))) [.assign "same" (n 0)],
            inc "j"],
         ifs (v "same") (give (n 1))]] ++
    give (n 0) }

/-- How many slots other than `k` hold a Message-ID reserved. -/
def postReserving : PFun :=
  { name := "postReserving", params := [(1, "k")], body :=
    [.dec "cnt" (n 0)] ++ eachSlot [ifs (eAnd (ne (v "kk") (v "k")) reserving) [inc "cnt"]] ++
    give (v "cnt") }

/-- `Store.accept`: the header section of slot `k` checked in the article's area, as its context
says; then refused, or its Message-ID and a sequence number reserved and the file's first octets
made — the header section stored, stuffed, and the empty line. -/
def postAccept : PFun :=
  open News.ArticleProg in
  { name := "postAccept", params := [(1, "k")], body := slotOf "k" ++
    [.dec "hl" (zw zPend), keptIn (v "hl") (headerMax + 2)] ++
    copyNew "j" (at_ (artOff + News.AbnfProg.aInput)) (atOff (v "zs") zBuf) (v "hl") ++
    [aset xLen (v "hl"), aset xSeq (sw ownNext), aset xWall (sw ownWall), aset xConn (zw zConn),
     .call "vd" "artCheck" [],
     ifs (aw News.AbnfProg.aBroken) (stop brokenState),
     ifs (v "vd") [zset zRefused (n 1), zset zBody (n 1), done0],
     .dec "ml" (aw xMsgLen), keptIn (v "ml") 250] ++
    copyNew "mj" (at_ (ownOff + ownId)) (at_ (artOff + xMsg)) (v "ml") ++
    callS "f1" "idFind" [v "ml"] ++ [.dec "dup" found] ++
    callS "f2" "postReserved" [v "k", v "ml"] ++ [.dec "rsv" found] ++
    callS "f3" "postReserving" [v "k"] ++
    [.dec "nres" found, .dec "nx" (sw ownNext),
     ifs (or2 (or2 (v "dup") (v "rsv"))
         (or2 (eLe (n capacity)
             (eAdd (eAdd (rw News.RecoverProg.rCommits) (sw ownAside)) (v "nres")))
           (ult (n (2 ^ 64 - 3)) (v "nx"))))
       [zset zRefused (n 1), zset zBody (n 1), done0],
     zset zSeq (v "nx"), sset ownNext (eAdd (v "nx") (n 1)), zset zMsgLen (v "ml")] ++
    copyNew "mk" (atOff (v "zs") zMsg) (at_ (ownOff + ownId)) (v "ml") ++
    [.dec "gn" (aw xKnownN), keptIn (v "gn") 16, zset zGroupN (v "gn"), .dec "gi" (n 0),
     .while (eLt (v "gi") (v "gn"))
       [.dec "gx" (ld (eAdd (at_ (artOff + xKnown)) (eMul (v "gi") (n 8)))),
        keptIn (v "gx") (groupsMax - 1),
        .store (eAdd (atOff (v "zs") zGroups) (eMul (v "gi") (n 8))) (v "gx"), inc "gi"],
     .dec "ol" (aw xOutLen), keptIn (v "ol") outMax,
     .dec "pd" (n 0), .dec "bl" (n 1), .dec "oj" (n 0),
     .while (eLt (v "oj") (v "ol"))
       [keptIn (v "pd") (bufMax - 2),
        .dec "y" (.loadb (eAdd (at_ (artOff + xOut)) (v "oj"))),
        ifs (eAnd (v "bl") (eEq (v "y") (n 46))) [.storeb (zbuf (v "pd")) (n 46), inc "pd"],
        .storeb (zbuf (v "pd")) (v "y"), inc "pd", .assign "bl" (eEq (v "y") (n 10)), inc "oj"],
     keptIn (v "pd") (bufMax - 2), zset zHeadSize (v "pd"),
     .storeb (zbuf (v "pd")) (n 13), .storeb (zbuf (eAdd (v "pd") (n 1))) (n 10),
     zset zPend (eAdd (v "pd") (n 2)), zset zSize (eAdd (v "pd") (n 2)), zset zWritten (n 0),
     zset zCrc (n 0xFFFFFFFF), zset zFile (n fileNone), zset zHas (n 1), zset zBody (n 1),
     zset zBol (n 1), done0] }

/-! ## An article's octets -/

/-- An octet `y` the block holds, into the slot: into the header section until it has ended, then
stuffed into the file. `tag` keeps the locals of each apart. -/
def octetAdd (tag : String) (y : PExpr) : List PStmt :=
  let pd := s!"pd{tag}"
  let p0 := s!"p0{tag}"
  let hl := s!"hl{tag}"
  [.ite (zw zBody)
    [ifs (zw zHas)
      [.dec pd (zw zPend), keptIn (v pd) (bufMax - 2), .dec p0 (v pd),
       ifs (eAnd (zw zBol) (eEq y (n 46))) [.storeb (zbuf (v pd)) (n 46), inc pd],
       .storeb (zbuf (v pd)) y, inc pd, zset zPend (v pd),
       zset zSize (eAdd (zw zSize) (eSub (v pd) (v p0))), zset zBol (eEq y (n 10))]]
    [.dec hl (zw zPend), keptIn (v hl) (headerMax + 1),
     .storeb (zbuf (v hl)) y, zset zPend (eAdd (v hl) (n 1))]]

/-- The header section so far ended by the empty line: checked; past its bound otherwise, the
article refused. -/
def headerEnd : List PStmt :=
  let at4 (i : Nat) (b : Nat) : PExpr := eEq (.loadb (zbuf (eSub (v "hn") (n (4 - i))))) (n b)
  [.dec "hn" (zw zPend), keptIn (v "hn") (headerMax + 2),
   .dec "ends" (or2
     (eAnd (eEq (v "hn") (n 2))
       (eAnd (eEq (.loadb (zbuf (n 0))) (n 13)) (eEq (.loadb (zbuf (n 1))) (n 10))))
     (eAnd (eLe (n 4) (v "hn")) (eAnd (eAnd (at4 0 13) (at4 1 10)) (eAnd (at4 2 13) (at4 3 10))))),
   .ite (eAnd (eLt (n headerMax) (v "hn")) (eEq (v "ends") (n 0))) [zset zRefused (n 1)]
     [ifs (v "ends") (callS "ac" "postAccept" [v "k"])]]

/-- `Store.feed`: the octets connection `c` holds framed into slot `k` while it takes them, a
framed octet at a time (`PostSpec.frameOctet`); what is left of them held. -/
def postFeed : PFun :=
  { name := "postFeed", params := [(1, "c"), (1, "k")], body :=
    [keptIn (v "c") (conns - 1), .dec "cb" (eAdd (at_ tableOff) (eMul (v "c") (n connSlot)))] ++
    slotOf "k" ++
    [.dec "p" (atOff (v "cb") cHeld), .dec "nn" (fld "cb" cHeldLen), .dec "i" (fld "cb" cHeldPos),
     keptIn (v "nn") data, keptIn (v "i") data,
     .dec "ph" (n 0), .dec "bad" (n 0), .dec "size" (n 0), .dec "kind" (n 0), .dec "held" (n 0),
     .dec "b" (n 0), .dec "pre" (n 0), .dec "post" (n 0), .dec "go" (n 1),
     .while (v "go")
       [.ite (eAnd (eLt (v "i") (v "nn")) takesE)
         ([.assign "b" (.loadb (eAdd (v "p") (v "i"))), inc "i",
           .assign "ph" (zw zPh), .assign "bad" (zw zBad), .assign "size" (n 0),
           .assign "kind" (n 0)] ++
          News.FramerProg.logicS 2 ++
          [.dec "ar" (eAdd (zw zArrived) (n 1)), zset zArrived (v "ar"),
           .ite (v "kind")
             [zset zEnded (n 1),
              ifs (or2 (or2 (ne (v "kind") (n (News.FramerProg.blockCode .accepted)))
                  (eLt (n rules.articleMax) (v "ar"))) (eEq (zw zBody) (n 0)))
                [zset zRefused (n 1)]]
             [ifs (eEq (zw zRefused) (n 0))
               [.ite (or2 (v "bad") (eLt (n rules.articleMax) (v "ar"))) [zset zRefused (n 1)]
                 [ifs (v "pre") (octetAdd "a" (n 13)), ifs (v "post") (octetAdd "b" (v "b")),
                  ifs (eEq (zw zBody) (n 0)) headerEnd]]],
           zset zPh (v "ph"), zset zBad (v "bad")])
         [.assign "go" (n 0)]],
     .ite (eEq (v "i") (v "nn")) [setf "cb" cHeldPos (n 0), setf "cb" cHeldLen (n 0)]
       [setf "cb" cHeldPos (v "i")],
     done0] }

/-! ## Jobs -/

/-- The job slot of the local `j`. -/
def jobAt : PExpr := eAdd (at_ (emitOff + emitJobs)) (eMul (v "j") (n jobSlot))

/-- The lowest job slot no job in flight holds (`Store.freeJob`). -/
def postFreeJob : PFun :=
  { name := "postFreeJob", body :=
    [.dec "j" (n 0), .dec "fj" (n jobs),
     .while (eLt (v "j") (n jobs))
       ([.dec "hj" (n 0)] ++
        eachSlot [ifs (eAnd (zw zLive) (eAnd (zw zBusy) (eEq (zw zJob) (v "j"))))
          [.assign "hj" (n 1)]] ++
        eachRead [ifs (eAnd (rdw rLive) (eAnd (rdw rBusy) (eEq (rdw rJob) (v "j"))))
          [.assign "hj" (n 1)]] ++
        [ifs (eAnd (eEq (v "hj") (n 0)) (eEq (v "fj") (n jobs))) [.assign "fj" (v "j")], inc "j"]),
     ifs (eEq (v "fj") (n jobs)) [.assign "fj" (n 0)]] ++
    give (v "fj") }

/-- A job of `ops` for task `t`, with its numbers `a` and `b`, started in the job slot of the
local `j`: the next generation, the job handed over, the slot busy with it. -/
def startJob (ops : List Op) (t : Nat) (a b : PExpr) : List PStmt :=
  [.dec "gen" (eAdd (ld (at_ (drvOff + dGen))) (n 1)), .store (at_ (drvOff + dGen)) (v "gen"),
   .dec "jb" jobAt, setf "jb" jobKind (n job), setf "jb" jobGen (v "gen"),
   setf "jb" jobCount (n ops.length)] ++
  (ops.zipIdx.flatMap fun (o, i) => putOpAt (v "jb") i o) ++
  [zset zBusy (n 1), zset zJob (v "j"), zset zJGen (v "gen"), zset zJOps (n ops.length),
   zset zTask (n t), zset zTaskA a, zset zTaskB b]

/-- The first `len` octets waiting into the job's bytes, the CRC-32C taken on over them. -/
def chunkOut (len : PExpr) : List PStmt :=
  [.dec "acc" (zw zCrc), .dec "cj" (n 0),
   .while (eLt (v "cj") len)
     [.dec "y" (.loadb (zbuf (v "cj"))), .storeb (eAdd (atOff (v "jb") jobHead) (v "cj")) (v "y"),
      .assign "acc" (eXor
        (ld (eAdd (at_ (ownOff + ownCrc)) (eMul (eAnd (eXor (v "acc") (v "y")) (n 255)) (n 8))))
        (.shr (v "acc") (n 8))),
      inc "cj"],
   zset zCrc (v "acc")]

/-- An octet into the commit's payload at `fp + q`, checked to lie in it. -/
def putB (e : PExpr) : List PStmt :=
  [keptIn (v "q") (maxPayload - 1), .storeb (eAdd (v "fp") (v "q")) e, inc "q"]

def putLe (e : PExpr) (k : Nat) : List PStmt :=
  (List.range k).flatMap fun i => putB (eAnd (.shr e (n (8 * i))) (n 255))

/-- The frame of slot `sk`'s commit (`Store.commitOf`, `Record.encode`) into the bytes of job slot
`sj`, at the journal's end, tagged under its key; its length found. -/
def postFrame : PFun :=
  { name := "postFrame", params := [(1, "sk"), (1, "sj")], body := slotOf "sk" ++
    [keptIn (v "sj") (jobs - 1),
     .dec "jb" (eAdd (at_ (emitOff + emitJobs)) (eMul (v "sj") (n jobSlot))),
     .dec "fp" (atOff (v "jb") (jobHead + headerLength)), .dec "q" (n 0)] ++
    putLe (zw zSeq) 8 ++
    [.dec "ml" (zw zMsgLen), keptIn (v "ml") 250] ++ putB (v "ml") ++
    [.dec "mi" (n 0),
     .while (eLt (v "mi") (v "ml"))
       (putB (.loadb (eAdd (atOff (v "zs") zMsg) (v "mi"))) ++ [inc "mi"]),
     .dec "gn" (zw zGroupN), keptIn (v "gn") 16] ++ putB (v "gn") ++
    [.dec "gi" (n 0),
     .while (eLt (v "gi") (v "gn"))
       ([.dec "gx" (ld (eAdd (atOff (v "zs") zGroups) (eMul (v "gi") (n 8)))),
         keptIn (v "gx") (groupsMax - 1),
         .dec "gp" (eAdd (at_ (recOff + News.RecoverProg.rGroups))
           (eMul (v "gx") (n News.RecoverProg.rGroupSlot))),
         .dec "gl" (ld (v "gp")), keptIn (v "gl") groupMax] ++ putB (v "gl") ++
        [.dec "gj" (n 0),
         .while (eLt (v "gj") (v "gl"))
           (putB (.loadb (eAdd (atOff (v "gp") 8) (v "gj"))) ++ [inc "gj"])] ++
        putLe (ld (eAdd (atOff (v "zs") zNums) (eMul (v "gi") (n 8)))) 4 ++ [inc "gi"])] ++
    putLe (zw zHeadSize) 4 ++ putLe (zw zSize) 4 ++ putLe (eXor (zw zCrc) (n 0xFFFFFFFF)) 4 ++
    [keptIn (v "q") maxPayload,
     .dec "mp" (at_ (ownOff + ownMsg)),
     .storeb (atOff (v "mp") 8) (n News.Journal.commitType)] ++
    ((List.range 8).map fun i =>
      .storeb (atOff (v "mp") i) (eAnd (.shr (sw ownJournalEnd) (n (8 * i))) (n 255))) ++
    copyNew "cj" (atOff (v "mp") 9) (v "fp") (v "q") ++
    [.dec "k" (at_ (ownOff + ownKey)), .dec "p" (v "mp"), .dec "n" (eAdd (v "q") (n 9))] ++
    ["r", "m", "v0", "v1", "v2", "v3", "off", "j"].map (.dec · (n 0)) ++ News.SipProg.sipSrc ++
    ((List.range 4).map fun i =>
      .storeb (atOff (v "jb") (jobHead + i)) (eAnd (.shr (v "q") (n (8 * i))) (n 255))) ++
    ((List.range 8).map fun i =>
      .storeb (atOff (v "jb") (jobHead + 4 + i)) (eAnd (.shr (v "r") (n (8 * i))) (n 255))) ++
    [.storeb (atOff (v "jb") (jobHead + 12)) (n News.Journal.commitType),
     .storeb (eAdd (v "fp") (v "q")) (n News.Journal.endMark.toNat)] ++
    give (eAdd (v "q") (n (headerLength + 1))) }

/-- The names of the article of number `sq`. -/
def temp : PExpr := n nameTemp
def final : PExpr := n nameFinal

/-- The job that removes a refused article's names, closing its file first if it is open
(`cleanOps`). -/
def cleanJob : List PStmt :=
  [.ite (eEq (v "fl") (n fileOpen))
    (startJob [{ code := opClose, place := v "pl", gen := v "pg" },
               { code := opRemove, name := temp, number := v "sq" }] taskClean (n 1) (n 0))
    [.ite (eEq (v "fl") (n fileClosed))
      (startJob [{ code := opRemove, name := temp, number := v "sq" }] taskClean (n 0) (n 0))
      [ifs (or2 (eEq (v "fl") (n fileFinal)) (eEq (v "fl") (n filePlaced)))
        (startJob [{ code := opRemove, name := final, number := v "sq" }] taskClean (n 0) (n 0))]]]

/-- Whether a slot's job in flight is of task `t`, as `any`. -/
def anyBusy (t : Nat) : List PStmt :=
  [.dec "any" (n 0), .dec "ka" (n 0),
   .while (eLt (v "ka") (n posts))
     [.dec "za" (eAdd (at_ slotsOff) (eMul (v "ka") (n slotLen))),
      ifs (eAnd (fld "za" zLive) (eAnd (fld "za" zBusy) (eEq (fld "za" zTask) (n t))))
        [.assign "any" (n 1)],
      inc "ka"]]

/-- The numbers the commit gives the article in its groups, each one above the group's highest;
`ovf` when one is past what a group may number. -/
def numbers : List PStmt :=
  [.dec "gn" (zw zGroupN), keptIn (v "gn") 16, .dec "ovf" (n 0), .dec "gi" (n 0),
   .while (eLt (v "gi") (v "gn"))
     [.dec "gx" (ld (eAdd (atOff (v "zs") zGroups) (eMul (v "gi") (n 8)))),
      keptIn (v "gx") (groupsMax - 1),
      .dec "num"
        (eAdd (ld (eAdd (at_ (recOff + News.RecoverProg.rHigh)) (eMul (v "gx") (n 8)))) (n 1)),
      ifs (ult (n (2 ^ 31 - 1)) (v "num")) [.assign "ovf" (n 1)],
      .store (eAdd (atOff (v "zs") zNums) (eMul (v "gi") (n 8))) (v "num"), inc "gi"]]

/-- The file open at `pl`, `pg`: a write of a job's octets once that many wait, or, once the block
has ended, the rest written, the file synced and closed. -/
def writeJob : List PStmt :=
  let on (code : Nat) : Op := { code, place := v "pl", gen := v "pg" }
  [.dec "pd" (zw zPend), keptIn (v "pd") bufMax,
   .ite (eLe (n jobData) (v "pd"))
     (startJob [{ on opWrite with offset := zw zWritten, length := n jobData }] taskWrite
        (n jobData) (n 0) ++ chunkOut (n jobData))
     [ifs (zw zEnded)
       [.ite (v "pd")
         (startJob [{ on opWrite with offset := zw zWritten, length := v "pd" }, on opDataSync,
            on opClose] taskFinish (n 1) (v "pd") ++ chunkOut (v "pd"))
         (startJob [on opDataSync, on opClose] taskFinish (n 0) (n 0))]]]

/-- The commit appended where the journal ends and the journal synced, unless an article number is
past what a group may number: then the article refused. -/
def commitJob : List PStmt :=
  let journal (code : Nat) : Op :=
    { code, place := ld (at_ (drvOff + dJnl)), gen := ld (at_ (drvOff + dJnlGen)) }
  numbers ++
  [.ite (v "ovf") (zset zRefused (n 1) :: cleanJob)
    (callS "fr" "postFrame" [v "k", v "j"] ++
     [.dec "flen" found, keptIn (v "flen") maxFrame] ++
     startJob [{ journal opWrite with offset := sw ownJournalEnd, length := v "flen" },
               journal opDataSync] taskCommit (v "flen") (n 0))]

/-- `Store.plan` of slot `k`: its next job started, if it has one. -/
def postPlan : PFun :=
  { name := "postPlan", params := [(1, "k")], body := slotOf "k" ++
    [ifs (eEq (zw zLive) (n 0)) [done0], ifs (zw zBusy) [done0],
     ifs (eEq (zw zHas) (n 0)) [done0]] ++
    callS "fj" "postFreeJob" [] ++
    [.dec "j" found, keptIn (v "j") (jobs - 1),
     .dec "sq" (zw zSeq), .dec "fl" (zw zFile), .dec "pl" (zw zPlace), .dec "pg" (zw zPGen),
     .ite (zw zRefused) cleanJob
      [ifs (zw zOutcome) [done0],
       .ite (eEq (v "fl") (n fileNone))
         (startJob [{ code := opCreate, name := temp, number := v "sq" }] taskCreate (n 0) (n 0))
         [.ite (eEq (v "fl") (n fileOpen)) writeJob
           [.ite (eEq (v "fl") (n fileClosed))
             (anyBusy taskPlace ++
              [.ite (v "any") []
                (startJob [{ code := opRename, name := temp, number := v "sq", toName := final,
                             toNumber := v "sq" }, { code := opSyncDir }] taskPlace (n 0) (n 0))])
             [ifs (eEq (v "fl") (n filePlaced))
               (anyBusy taskCommit ++ [.ite (v "any") [] commitJob])]]]],
     done0] }

/-! ## Reads -/

/-- The fixed texts of reads, by their place in `SessionLayout.texts`: the 220, 221 and 222 lines'
starts, six octets each, the 223 line's, the 403, Xref's name and the terminating dot. -/
def textOf (k : Nat) : PExpr := at_ (ownOff + ownTexts + textAt k)
def tStatus : Nat := 29
def tStat : Nat := 32
def tUnreadable : Nat := 33
def tXref : Nat := 34
def tDot : Nat := 35

/-- Whether a file is open at place `p`: the journal's, an article's or a read's
(`Store.placeTaken`). -/
def placeTaken : PFun :=
  { name := "placeTaken", params := [(1, "p")], body :=
    [.dec "tk" (eEq (ld (at_ (drvOff + dJnl))) (v "p"))] ++
    eachSlot [ifs (eAnd (eAnd (zw zLive) (zw zHas))
        (eAnd (eEq (zw zFile) (n fileOpen)) (eEq (zw zPlace) (v "p")))) [.assign "tk" (n 1)]] ++
    eachRead [ifs (eAnd (rdw rLive) (eAnd (eEq (rdw rFile) (n readOpen)) (eEq (rdw rPlace) (v "p"))))
      [.assign "tk" (n 1)]] ++
    give (v "tk") }

/-- `x`, below 2^32, divided by ten. -/
def div10 (x : PExpr) : PExpr := .shr (eMul x (n 3435973837)) (n 35)

/-- An octet into the read's Xref at `xo`, checked to lie in it. -/
def putX (e : PExpr) : List PStmt :=
  [keptIn (v "xo") (xrefMax - 1), .storeb (eAdd (atOff (v "rs") rXref) (v "xo")) e, inc "xo"]

/-- Read `k` given to the connection `x` of generation `g`, for command `cmd`, of the commit at
`ci`: its numbers from the commit; its 220, 221 or 222 line, the number 0 and the Message-ID; its
Xref field (`PostSpec.xref`): the path identity, then each group and its number, a line folded before
one that would take it past 998 octets. -/
def readClaim : PFun :=
  { name := "readClaim", params := [(1, "k"), (1, "x"), (1, "g"), (1, "cmd"), (1, "ci")], body :=
    readOf "k" ++ [keptIn (v "cmd") 3, ifs (eEq (v "cmd") (n 0)) (stop brokenState)] ++
    commitAt "ci" ++
    [keptIn (v "sn") 250,
     .dec "sz" (fld "sl" News.RecoverProg.slotSizes),
     .dec "ms" (fld "sl" News.RecoverProg.slotMisc)] ++
    ([(rLive, n 1), (rOwner, n 1), (rOwnIdx, v "x"), (rOwnGen, v "g"), (rCmd, v "cmd"),
      (rCi, v "ci"), (rFile, n readNone), (rPlace, n 0), (rPGen, n 0), (rGot, n 0), (rGiven, n 0),
      (rBad, n 0), (rBusy, n 0), (rHead, .shr (v "sz") (n 32)), (rSize, eAnd (v "sz") (n 0xFFFFFFFF)),
      (rCrcWant, eAnd (.shr (v "ms") (n 16)) (n 0xFFFFFFFF)), (rAcc, n 0xFFFFFFFF), (rBol, n 1),
      (rCr, n 0), (rDot, n 0), (rBufAt, n 0), (rBufLen, n 0)].map fun (f, e) => rdset f e) ++
    copyNew "sj" (atOff (v "rs") rLine)
      (eAdd (textOf tStatus) (eMul (eSub (v "cmd") (n 1)) (n 6))) (n 6) ++
    copyNew "si" (atOff (v "rs") (rLine + 6)) (atOff (v "sl") News.RecoverProg.slotId) (v "sn") ++
    [.storeb (eAdd (atOff (v "rs") (rLine + 6)) (v "sn")) (n 13),
     .storeb (eAdd (atOff (v "rs") (rLine + 7)) (v "sn")) (n 10),
     rdset rLineLen (eAdd (v "sn") (n 8)),
     .dec "xo" (n 0), .dec "xj" (n 0),
     .while (eLt (v "xj") (n 6)) (putX (.loadb (eAdd (textOf tXref) (v "xj"))) ++ [inc "xj"]),
     .dec "il" (aw News.ArticleProg.xIdLen), keptIn (v "il") identityMax, .assign "xj" (n 0),
     .while (eLt (v "xj") (v "il"))
       (putX (.loadb (eAdd (at_ (artOff + News.ArticleProg.xId)) (v "xj"))) ++ [inc "xj"]),
     .dec "wd" (v "xo"), .dec "gn" (eAnd (v "ms") (n 255)), keptIn (v "gn") 16, .dec "gi" (n 0),
     .while (eLt (v "gi") (v "gn"))
       ([.dec "gw" (ld (eAdd (atOff (v "sl") News.RecoverProg.slotGroups) (eMul (v "gi") (n 8)))),
         .dec "gx" (.shr (v "gw") (n 32)), keptIn (v "gx") (groupsMax - 1),
         .dec "num" (eAnd (v "gw") (n 0xFFFFFFFF)),
         .dec "gp" (eAdd (at_ (recOff + News.RecoverProg.rGroups))
           (eMul (v "gx") (n News.RecoverProg.rGroupSlot))),
         .dec "gl" (ld (v "gp")), keptIn (v "gl") groupMax,
         .dec "nd" (n 1), .dec "t" (v "num"),
         .while (eLt (n 9) (v "t")) [.assign "t" (div10 (v "t")), inc "nd"],
         .dec "ll" (eAdd (eAdd (v "gl") (n 1)) (v "nd")),
         ifs (eLt (n 998) (eAdd (eAdd (v "wd") (n 1)) (v "ll")))
           (putX (n 13) ++ putX (n 10) ++ [.assign "wd" (n 0)])] ++
        putX (n 32) ++
        [.assign "xj" (n 0),
         .while (eLt (v "xj") (v "gl")) (putX (.loadb (eAdd (atOff (v "gp") 8) (v "xj"))) ++ [inc "xj"])] ++
        putX (n 58) ++
        [keptIn (v "xo") (xrefMax - 10), .assign "t" (v "num"), .dec "dq" (v "nd"),
         .while (eLt (n 0) (v "dq"))
           [.assign "dq" (eSub (v "dq") (n 1)), keptIn (v "dq") 9,
            .storeb (eAdd (eAdd (atOff (v "rs") rXref) (v "xo")) (v "dq"))
              (eAdd (n 48) (eSub (v "t") (eMul (div10 (v "t")) (n 10)))),
            .assign "t" (div10 (v "t"))],
         .assign "xo" (eAdd (v "xo") (v "nd")),
         .assign "wd" (eAdd (eAdd (v "wd") (n 1)) (v "ll")), inc "gi"])] ++
    putX (n 13) ++ putX (n 10) ++ [rdset rXrefLen (v "xo"), done0] }

/-- Whether read `rs` is whole: its commit's size read and checked, and its file closed by the read
past it (`Read.whole`). -/
def readWhole : PExpr := eAnd (eEq (rdw rGot) (rdw rSize)) (eEq (rdw rFile) (n readGone))

/-- How many octets read `k` gives (`Read.output`): nothing before octets are checked, then its
220, 221 or 222 line, for ARTICLE the file with Xref after the header fields once the empty line is
read, for HEAD the header fields and Xref, for BODY what follows the empty line; and once whole the
dot. -/
def readOutSize : PFun :=
  { name := "readOutSize", params := [(1, "k")], body := readOf "k" ++
    [.dec "gt" (rdw rGot), .dec "h" (rdw rHead), .dec "cm" (rdw rCmd),
     ifs (eEq (v "gt") (n 0)) (give (n 0)),
     .dec "known" (eLe (eAdd (v "h") (n 2)) (v "gt")),
     .dec "hm" (v "h"), ifs (eLt (v "gt") (v "h")) [.assign "hm" (v "gt")],
     .dec "os" (rdw rLineLen),
     .ite (eEq (v "cm") (n 3))
       [ifs (eLt (eAdd (v "h") (n 2)) (v "gt"))
         [.assign "os" (eAdd (v "os") (eSub (v "gt") (eAdd (v "h") (n 2))))]]
       [.assign "os" (eAdd (v "os") (v "hm")),
        ifs (v "known") [.assign "os" (eAdd (v "os") (rdw rXrefLen)),
          ifs (eEq (v "cm") (n 1)) [.assign "os" (eAdd (v "os") (eSub (v "gt") (v "h")))]]],
     ifs readWhole [.assign "os" (eAdd (v "os") (n 3))]] ++
    give (v "os") }

/-- A job of `ops` for task `t` asking `asked` octets, started in the job slot of the local `j`
for read `rs`. -/
def startRead (ops : List Op) (t : Nat) (asked : PExpr) : List PStmt :=
  [.dec "gen" (eAdd (ld (at_ (drvOff + dGen))) (n 1)), .store (at_ (drvOff + dGen)) (v "gen"),
   .dec "jb" jobAt, setf "jb" jobKind (n job), setf "jb" jobGen (v "gen"),
   setf "jb" jobCount (n ops.length)] ++
  (ops.zipIdx.flatMap fun (o, i) => putOpAt (v "jb") i o) ++
  [rdset rBusy (n 1), rdset rJob (v "j"), rdset rJGen (v "gen"), rdset rJOps (n ops.length),
   rdset rTask (n t), rdset rAsked asked]

/-- `Store.nextRead` of read `k`, started if it has one: its file opened; once everything checked
has been given, the next octets read, a job's or, when the rest fits, one more than are left with
the file closed after them; a file a failure or the connection gone leaves open closed. -/
def readPlan : PFun :=
  let free : List PStmt := callS "fj" "postFreeJob" [] ++ [.dec "j" found, keptIn (v "j") (jobs - 1)]
  { name := "readPlan", params := [(1, "k")], body := readOf "k" ++
    [ifs (eEq (rdw rLive) (n 0)) [done0], ifs (rdw rBusy) [done0],
     .dec "fl" (rdw rFile), .dec "pl" (rdw rPlace), .dec "pg" (rdw rPGen),
     .dec "quit" (or2 (rdw rBad) (eEq (rdw rOwner) (n 0))),
     ifs (eEq (v "fl") (n readGone)) [done0],
     ifs (eAnd (eEq (v "fl") (n readNone)) (v "quit")) [done0],
     .dec "ci" (rdw rCi), keptIn (v "ci") (capacity - 1),
     .dec "sl" (eAdd (at_ (recOff + News.RecoverProg.rSlots))
       (eMul (v "ci") (n News.RecoverProg.slotSize))),
     .ite (eEq (v "fl") (n readNone))
       (free ++ startRead [{ code := opOpen, name := final, number := fld "sl" News.RecoverProg.slotSeq }]
         taskOpen (n 0))
       [.ite (v "quit") (free ++ startRead [{ code := opClose, place := v "pl", gen := v "pg" }] taskClose (n 0))
         (callS "os" "readOutSize" [v "k"] ++
          [ifs (eLt (rdw rGiven) found) [done0],
           .dec "left" (eSub (rdw rSize) (rdw rGot))] ++ free ++
          [.ite (eLe (eAdd (v "left") (n 1)) (n jobData))
             (startRead [{ code := opRead, place := v "pl", gen := v "pg", offset := rdw rGot,
                           length := eAdd (v "left") (n 1) },
                         { code := opClose, place := v "pl", gen := v "pg" }]
               taskReadLast (eAdd (v "left") (n 1)))
             (startRead [{ code := opRead, place := v "pl", gen := v "pg", offset := rdw rGot,
                           length := n jobData }] taskRead (n jobData))])],
     done0] }

/-! ## Completions -/

/-- The store stopped accepting, by a failed sync or close. -/
def storeStop : PStmt := sset ownAccepting (n 0)

/-- The commit of slot `zs` among those the store holds: in recovery's area as recovery puts one,
its groups' highest numbers raised, and in the index. -/
def commitApply : List PStmt :=
  [.dec "ci" (rw News.RecoverProg.rCommits), keptIn (v "ci") (capacity - 1),
   .dec "sl" (eAdd (at_ (recOff + News.RecoverProg.rSlots))
     (eMul (v "ci") (n News.RecoverProg.slotSize))),
   .dec "ml" (zw zMsgLen), keptIn (v "ml") 250, .dec "gn" (zw zGroupN), keptIn (v "gn") 16,
   setf "sl" News.RecoverProg.slotSeq (zw zSeq),
   setf "sl" News.RecoverProg.slotSizes (eOr (.shl (zw zHeadSize) (n 32)) (zw zSize)),
   setf "sl" News.RecoverProg.slotMisc
     (eOr (eOr (.shl (eXor (zw zCrc) (n 0xFFFFFFFF)) (n 16)) (.shl (v "ml") (n 8))) (v "gn")),
   .dec "gi" (n 0),
   .while (eLt (v "gi") (v "gn"))
     [.dec "gx" (ld (eAdd (atOff (v "zs") zGroups) (eMul (v "gi") (n 8)))),
      keptIn (v "gx") (groupsMax - 1),
      .dec "num" (ld (eAdd (atOff (v "zs") zNums) (eMul (v "gi") (n 8)))),
      .store (eAdd (atOff (v "sl") News.RecoverProg.slotGroups) (eMul (v "gi") (n 8)))
        (eOr (.shl (v "gx") (n 32)) (v "num")),
      .store (eAdd (at_ (recOff + News.RecoverProg.rHigh)) (eMul (v "gx") (n 8))) (v "num"),
      inc "gi"]] ++
  copyNew "mj" (atOff (v "sl") News.RecoverProg.slotId) (atOff (v "zs") zMsg) (v "ml") ++
  [rset News.RecoverProg.rCommits (eAdd (v "ci") (n 1))] ++ callS "ia" "idAdd" [v "ci"]

/-- Result word `w` of operation `i` of the completion at `d`. -/
def result (i w : Nat) : PExpr := fld "d" (doneResults + 16 * i + 8 * w)

/-- A completion's octets of a read checked on from where the read's check stopped
(`PostSpec.fileOk` a job at a time): CRLF only, no NUL, a line that starts with a dot starting with
two, the empty line where the header section's size says — an LF before and after it, each line
ending in CRLF — and once all are read, the last line ended, the size and the CRC-32C; checked, they
are the read's buffer. -/
def readCheck : List PStmt :=
  let crcStep (x : PExpr) : PStmt := .assign "acc" (eXor
    (ld (eAdd (at_ (ownOff + ownCrc)) (eMul (eAnd (eXor (v "acc") x) (n 255)) (n 8))))
    (.shr (v "acc") (n 8)))
  let bad : PStmt := .assign "bad" (n 1)
  [.dec "gn" (result 0 0), .dec "asked" (rdw rAsked), keptIn (v "asked") jobData,
   ifs (or2 (eLt (v "gn") (n 0)) (eLt (v "asked") (v "gn")))
     (stop (News.SessionSpec.Breach.job .badDone).code),
   keptIn (v "gn") jobData,
   .dec "gt" (rdw rGot), .dec "sz" (rdw rSize), .dec "h" (rdw rHead),
   keptIn (v "gt") 4294967295, keptIn (v "sz") 4294967295,
   ifs (eLt (v "sz") (v "gt")) (stop brokenState),
   .dec "left" (eSub (v "sz") (v "gt")), .dec "mn" (v "left"),
   ifs (eLt (v "asked") (v "left")) [.assign "mn" (v "asked")],
   .dec "bad" (or2 (eLt (v "gn") (v "mn")) (eLt (v "left") (v "gn"))),
   .dec "acc" (rdw rAcc), .dec "bol" (rdw rBol), .dec "cr" (rdw rCr), .dec "dt" (rdw rDot),
   .dec "q" (n 0),
   .while (eAnd (eEq (v "bad") (n 0)) (eLt (v "q") (v "gn")))
     [.dec "x" (.loadb (eAdd (atOff (v "d") doneHead) (v "q"))), .dec "f" (eAdd (v "gt") (v "q")),
      crcStep (v "x"),
      .ite (v "cr")
        [ifs (ne (v "x") (n 10)) [bad], .assign "cr" (n 0), .assign "bol" (n 1)]
        [.ite (or2 (eEq (v "x") (n 0)) (eEq (v "x") (n 10))) [bad]
          [.ite (v "dt")
            [ifs (ne (v "x") (n 46)) [bad], .assign "dt" (n 0), .assign "bol" (n 0)]
            [.ite (eEq (v "x") (n 13)) [.assign "cr" (n 1)]
              [.ite (eAnd (v "bol") (eEq (v "x") (n 46))) [.assign "dt" (n 1), .assign "bol" (n 0)]
                [.assign "bol" (n 0)]]]]],
      ifs (or2 (eEq (eAdd (v "f") (n 1)) (v "h")) (eEq (v "f") (eAdd (v "h") (n 1))))
        [ifs (ne (v "x") (n 10)) [bad]],
      inc "q"],
   .dec "ng" (eAdd (v "gt") (v "gn")),
   ifs (eAnd (eLe (eAdd (v "h") (n 2)) (v "ng")) (eLt (v "h") (n 2))) [bad],
   ifs (eLe (v "sz") (v "ng"))
     [ifs (or2 (eEq (v "bol") (n 0)) (or2 (v "cr") (v "dt"))) [bad],
      ifs (eLt (v "ng") (eAdd (v "h") (n 2))) [bad],
      ifs (ne (eXor (v "acc") (n 0xFFFFFFFF)) (rdw rCrcWant)) [bad]],
   .ite (v "bad") [rdset rBad (n 1)]
     (copyNew "cj" (atOff (v "rs") rBuf) (atOff (v "d") doneHead) (v "gn") ++
      [rdset rBufAt (v "gt"), rdset rBufLen (v "gn"), rdset rGot (v "ng"), rdset rAcc (v "acc"),
       rdset rBol (v "bol"), rdset rCr (v "cr"), rdset rDot (v "dt")])]

/-- The completion in slot `j` of read `k`'s job (`Store.completeRead`): its file opened at a place
in the table and in use by no other file, or the read failed; the octets read
checked (`readCheck`), fewer than asked or than are left, or more than are left, failing the read;
the file gone once the last read's close was tried, or once closed. -/
def readDone : PFun :=
  { name := "readDone", params := [(1, "k"), (1, "j")], body := readOf "k" ++
    [keptIn (v "j") (jobs - 1),
     .dec "d" (eAdd (at_ (nextOff + nextDone)) (eMul (v "j") (n doneSlot))),
     .dec "ok" (fld "d" doneOps), .dec "nops" (rdw rJOps),
     ifs (or2 (eLt (v "ok") (n 0)) (eLt (v "nops") (v "ok")))
       (stop (News.SessionSpec.Breach.job .badDone).code),
     rdset rBusy (n 0), .dec "tt" (rdw rTask),
     .ite (eEq (v "tt") (n taskOpen))
       [.ite (eEq (v "ok") (n 1))
         ([.dec "rp" (result 0 0), .dec "rg" (result 0 1),
           ifs (or2 (eLt (v "rp") (n 0)) (eLe (n handles) (v "rp")))
             (stop (News.SessionSpec.Breach.job .badDone).code)] ++
          callS "pt" "placeTaken" [v "rp"] ++
          [ifs found (stop (News.SessionSpec.Breach.job .badDone).code),
           rdset rFile (n readOpen), rdset rPlace (v "rp"), rdset rPGen (v "rg")])
         [rdset rFile (n readGone), rdset rBad (n 1)]]
       [.ite (eEq (v "tt") (n taskClose)) [rdset rFile (n readGone)]
         [.ite (eEq (v "ok") (n 0)) [rdset rBad (n 1)] readCheck,
          ifs (eAnd (eEq (v "tt") (n taskReadLast)) (eLe (n 1) (v "ok"))) [rdset rFile (n readGone)]]],
     done0] }

/-- The next octets read `k` gives, at most an action's, into the output of connection `c`, made an
octet at a time from where the read has given to: its 220, 221 or 222 line, the file's octets from
the buffer — or, for ARTICLE, the empty line's CRLF when the buffer starts past it — Xref, and the
dot. Once it has given everything and is whole, the read ends: it has no owner, and the connection no
read. How many it gave. -/
def readPiece : PFun :=
  { name := "readPiece", params := [(1, "c"), (1, "k")], body := readOf "k" ++
    [keptIn (v "c") (conns - 1), .dec "cb" (eAdd (at_ tableOff) (eMul (v "c") (n connSlot)))] ++
    callS "o" "readOutSize" [v "k"] ++
    [.dec "os" found, .dec "gv" (rdw rGiven),
     ifs (or2 (eLt (v "gv") (n 0)) (eLt (v "os") (v "gv"))) (stop brokenState),
     .dec "m" (eSub (v "os") (v "gv")), ifs (eLt (n data) (v "m")) [.assign "m" (n data)],
     keptIn (v "m") data,
     .dec "sl" (rdw rLineLen), .dec "h" (rdw rHead), .dec "xl" (rdw rXrefLen),
     .dec "sz" (rdw rSize), .dec "cm" (rdw rCmd), .dec "ba" (rdw rBufAt), .dec "bn" (rdw rBufLen),
     keptIn (v "sl") statusMax, keptIn (v "xl") xrefMax, keptIn (v "bn") jobData,
     .dec "i" (n 0),
     .while (eLt (v "i") (v "m"))
       [.dec "pos" (eAdd (v "gv") (v "i")), .dec "b" (n 0), .dec "isf" (n 0), .dec "fp" (n 0),
        .dec "di" (n 0), .dec "isd" (n 0), .dec "xi" (n 0), .dec "isx" (n 0),
        .ite (eLt (v "pos") (v "sl"))
          [keptIn (v "pos") (statusMax - 1), .assign "b" (.loadb (eAdd (atOff (v "rs") rLine) (v "pos")))]
          [.dec "q" (eSub (v "pos") (v "sl")),
           .ite (eEq (v "cm") (n 3))
             [.dec "bl" (eSub (eSub (v "sz") (v "h")) (n 2)),
              .ite (eLt (v "q") (v "bl")) [.assign "isf" (n 1), .assign "fp" (eAdd (eAdd (v "h") (n 2)) (v "q"))]
                [.assign "isd" (n 1), .assign "di" (eSub (v "q") (v "bl"))]]
             [.ite (eLt (v "q") (v "h")) [.assign "isf" (n 1), .assign "fp" (v "q")]
               [.ite (eLt (v "q") (eAdd (v "h") (v "xl"))) [.assign "isx" (n 1), .assign "xi" (eSub (v "q") (v "h"))]
                 [.ite (eEq (v "cm") (n 1))
                   [.ite (eLt (v "q") (eAdd (v "xl") (v "sz")))
                     [.assign "isf" (n 1), .assign "fp" (eSub (v "q") (v "xl"))]
                     [.assign "isd" (n 1), .assign "di" (eSub (v "q") (eAdd (v "xl") (v "sz")))]]
                   [.assign "isd" (n 1), .assign "di" (eSub (v "q") (eAdd (v "h") (v "xl")))]]]]],
        ifs (v "isx") [keptIn (v "xi") (xrefMax - 1),
          .assign "b" (.loadb (eAdd (atOff (v "rs") rXref) (v "xi")))],
        ifs (v "isd") [keptIn (v "di") 2, .assign "b" (.loadb (eAdd (textOf tDot) (v "di")))],
        ifs (v "isf")
          [.ite (eLe (v "ba") (v "fp"))
            [.dec "bi" (eSub (v "fp") (v "ba")), keptIn (v "bi") (jobData - 1),
             ifs (eLe (v "bn") (v "bi")) (stop brokenState),
             .assign "b" (.loadb (eAdd (atOff (v "rs") rBuf) (v "bi")))]
            [.ite (eEq (v "fp") (v "h")) [.assign "b" (n 13)]
              [.ite (eEq (v "fp") (eAdd (v "h") (n 1))) [.assign "b" (n 10)] (stop brokenState)]]],
        .storeb (eAdd (atOff (v "cb") cOut) (v "i")) (v "b"), inc "i"],
     setf "cb" cOutLen (v "m"), rdset rGiven (eAdd (v "gv") (v "m")),
     ifs (eAnd readWhole (eEq (eAdd (v "gv") (v "m")) (v "os")))
       [rdset rOwner (n 0), setf "cb" cRead (n 0), setf "cb" cWant (n 0)]] ++
    give (v "m") }

/-- `Store.completeAny` of the completion in slot `j`, if it holds one: the read or the slot whose
job it ends moved on; one of no job in flight, or with more operations done than its job had, or a
file at a place past the table or in use, stops the run. -/
def postDone : PFun :=
  { name := "postDone", params := [(1, "j")], body :=
    [keptIn (v "j") (jobs - 1),
     .dec "d" (eAdd (at_ (nextOff + nextDone)) (eMul (v "j") (n doneSlot))),
     ifs (eEq (fld "d" doneKind) (n 0)) [done0],
     .dec "dg" (fld "d" doneGen), .dec "ok" (fld "d" doneOps), .dec "fk" (n posts)] ++
    eachSlot [ifs (eAnd (eEq (v "fk") (n posts)) (eAnd (eAnd (zw zLive) (zw zBusy))
        (eAnd (eEq (zw zJob) (v "j")) (eEq (zw zJGen) (v "dg"))))) [.assign "fk" (v "kk")]] ++
    [.dec "fr" (n reads)] ++
    eachRead [ifs (eAnd (eEq (v "fr") (n reads)) (eAnd (eAnd (rdw rLive) (rdw rBusy))
        (eAnd (eEq (rdw rJob) (v "j")) (eEq (rdw rJGen) (v "dg"))))) [.assign "fr" (v "kr")]] ++
    [ifs (eLt (v "fr") (n reads)) (callS "rd" "readDone" [v "fr", v "j"] ++ [done0]),
     ifs (eEq (v "fk") (n posts)) (stop (News.SessionSpec.Breach.job .unknownJob).code)] ++
    slotOf "fk" ++
    [.dec "nops" (zw zJOps),
     ifs (or2 (eLt (v "ok") (n 0)) (eLt (v "nops") (v "ok")))
       (stop (News.SessionSpec.Breach.job .badDone).code),
     zset zBusy (n 0),
     .dec "all" (eEq (v "ok") (v "nops")), .dec "ta" (zw zTaskA), .dec "tb" (zw zTaskB),
     .dec "tt" (zw zTask),
     .ite (eEq (v "tt") (n taskCreate))
       [.ite (eEq (v "ok") (n 1))
         ([.dec "rp" (result 0 0), .dec "rg" (result 0 1),
           ifs (or2 (eLt (v "rp") (n 0)) (eLe (n handles) (v "rp")))
             (stop (News.SessionSpec.Breach.job .badDone).code)] ++
          callS "pt" "placeTaken" [v "rp"] ++
          [ifs found (stop (News.SessionSpec.Breach.job .badDone).code),
           zset zFile (n fileOpen), zset zPlace (v "rp"), zset zPGen (v "rg")])
         [zset zRefused (n 1)]]
     [.ite (eEq (v "tt") (n taskWrite))
       [.ite (v "all")
         [.dec "pd" (zw zPend), keptIn (v "pd") bufMax, keptIn (v "ta") jobData,
          .dec "sj" (v "ta"),
          .while (eLt (v "sj") (v "pd"))
            [.storeb (zbuf (eSub (v "sj") (v "ta"))) (.loadb (zbuf (v "sj"))), inc "sj"],
          zset zPend (eSub (v "pd") (v "ta")), zset zWritten (eAdd (zw zWritten) (v "ta"))]
         [zset zRefused (n 1)]]
     [.ite (eEq (v "tt") (n taskFinish))
       [.ite (v "all")
         [zset zFile (n fileClosed), zset zWritten (eAdd (zw zWritten) (v "tb")),
          zset zPend (eSub (zw zPend) (v "tb"))]
         [.ite (eLt (v "ok") (v "ta")) [zset zRefused (n 1)]
           [.ite (eLt (eAdd (v "ok") (n 1)) (v "nops")) [zset zRefused (n 1), storeStop]
             [zset zFile (n fileClosed), zset zRefused (n 1), storeStop]]]]
     [.ite (eEq (v "tt") (n taskPlace))
       [.ite (v "all") [zset zFile (n filePlaced)]
         [.ite (eEq (v "ok") (n 1)) [zset zFile (n fileFinal), zset zRefused (n 1), storeStop]
           [zset zRefused (n 1)]]]
     [.ite (eEq (v "tt") (n taskCommit))
       [.ite (eAnd (v "all") (sw ownAccepting))
         ([zset zOutcome (n outPosted), zset zHas (n 0)] ++ commitApply ++
          [sset ownJournalEnd (eAdd (sw ownJournalEnd) (v "ta"))])
         [zset zOutcome (n outLost), zset zHas (n 0), storeStop]]
       [ifs (eEq (v "tt") (n taskClean))
         [.ite (eAnd (v "ta") (eEq (v "ok") (n 0))) [zset zFile (n fileClosed), storeStop]
           [zset zHas (n 0)]]]]]]],
     done0] }

/-- The store's functions, each after those it calls. -/
def functions : List PFun :=
  [crcTable, postTakes, postTidy, postTidyAll, queueAdd, queueDrop, postAdmits, readAdmits,
   postAbandon, postClaim, idHash, idFind, idAdd, idBuild, postReserved, postReserving, postAccept,
   postFeed, postFreeJob, postFrame, postPlan, placeTaken, readClaim, readOutSize, readPlan,
   readDone, readPiece, postDone]

end DN.Server.SessionStore
