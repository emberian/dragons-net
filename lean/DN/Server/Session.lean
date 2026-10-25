-- SPDX-License-Identifier: AGPL-3.0-or-later
import DN.Compiler.Checked
import DN.News.FramerProg
import DN.News.RecoverProg
import DN.News.SessionSpec
import DN.Server.SessionStore

/-!
# DN.Server.Session

The NNTP session of `DN.News.SessionSpec` as the server's program: each turn its `main` fetches a
batch of events and completions from its host, runs the session's turn over its table of
connections in the heap, hands the host the actions and the jobs, reads back how much of each send
the kernel took, and names the time it needs its next turn (docs/decisions/0003-nntp-slice.md). The
layout is `DN.Server.SessionLayout`. What makes no external call is a function: an event, a
connection's turn and what the host took of it, the next turn's time, a step of recovery; the
store's side of POST and of reading is `DN.Server.SessionStore`'s, and an article's header section
is checked by `DN.News.ArticleProg`'s.

Lines are framed by the statements of `DN.News.FramerProg.lineFrag`, run on a connection's held
input; the reply to a line follows `DN.News.CommandSpec.replyIn`, as `SessionSpec.resolve` makes it
with a store; the texts of the replies are laid out once in the program's own area and copied from
there, with the revision and the address of the source the host gives in its first batch.

Every number the host writes that the program takes as a count, an index, a length or a time is
checked before it is used, a flag read as zero or not; one out of range stops the run with
the code of `DN.News.SessionSpec.Breach`, or `SessionLayout.unknownEvent`,
`SessionLayout.badIdentity`, written where the host reads it at exit. So does a word the program
reads back from its own area and uses as a length or a position, checked against the range it
keeps it in (`SessionLayout.brokenState`). The loop itself never
finishes, so the run never falls off the end of `main`.
-/

namespace DN.Server.Session

open DN.Compiler DN.Compiler.Syntax DN.Server.SessionLayout
open DN.Server.SessionStore (at_ ld fld setf ne or2 inc ifs stop keptIn copy copyNew callS found
  Op outPosted outLost waiters readers textOf tStat tUnreadable digits)
open DN.News.SessionSpec (inactivity firstCommand lineTime articleTime lineLimit clockLimit
  wallLimit)

def breach (b : News.SessionSpec.Breach) : List PStmt := stop b.code

/-- The store's words. -/
def ownW (o : Nat) : PExpr := ld (at_ (ownOff + o))
def hasStore : PExpr := ownW ownStore

/-! ## Codes -/

/-- The code the local `r` holds for a reply; zero is none. -/
def replyCode : News.CommandSpec.Reply → Nat
  | .ignore => 0 | .capabilities => 1 | .help => 2 | .quit => 3 | .noGroup => 4
  | .noSuchId => 5 | .unknown => 6 | .syntax => 7 | .post => 8 | .posted => 9 | .failed => 10
  | .notPermitted => 11 | .unavailable => 12 | .capabilitiesPost => 13 | .helpPost => 14
  | .lookup .. => 17 | .stat .. => 18 | .unreadable => 19 | .select _ => 20 | .byNumber .. => 21
  | .current _ => 22 | .move _ => 23 | .selected .. => 24 | .noSuchGroup => 25 | .noCurrent => 26
  | .noNext => 27 | .noPrevious => 28 | .noNumber => 29 | .listGroup .. => 30 | .listed .. => 31
  | .active _ => 32 | .newsgroups => 33 | .newGroups => 34 | .date => 35 | .time _ => 36

/-- The codes `connText` takes for the greetings, past the replies'. -/
def greetCode : Nat := 15
def greetPostCode : Nat := 16

/-- The code a connection's record keeps for its phase. -/
def phaseCode : News.SessionSpec.Phase → Nat
  | .open_ => 0 | .quitting => 1 | .ending => 2

def reply (r : News.CommandSpec.Reply) : PStmt := .assign "r" (n (replyCode r))
def isReply (r : News.CommandSpec.Reply) : PExpr := eEq (v "r") (n (replyCode r))
/-- Whether the line the framer reported is of kind `k`. -/
def isKind (k : News.FrameSpec.Kind) : PExpr := eEq (v "kind") (n (News.FramerProg.kindCode k))

/-! ## The texts of the replies -/

/-- Bytes as words, eight a word, its first byte lowest, as the machines the host runs on lay out
a word; the last word filled with zeros. `j` bytes of the word `acc` are taken. -/
def textWords : List (BitVec 8) → Nat → Nat → List Nat
  | [], 0, _ => []
  | [], _, acc => [acc]
  | b :: rest, j, acc =>
    if j = 7 then (acc + b.toNat * 256 ^ 7) :: textWords rest 0 0
    else textWords rest (j + 1) (acc + b.toNat * 256 ^ j)

/-- The texts, a word at a time, into the program's own area. -/
def textsInit : List PStmt :=
  (textWords texts.flatten 0 0).mapIdx fun w x => .store (at_ (ownOff + ownTexts + 8 * w)) (n x)

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
def tGreetingPostHead : Nat := 18
def tGreetingPostMid : Nat := 19
def tCapabilitiesPostTail : Nat := 20
def tHelpPostHead : Nat := 21
def tPost : Nat := 22
def tPosted : Nat := 23
def tFailed : Nat := 24
def tNotPermitted : Nat := 25
def tUnavailable : Nat := 26

/-- Append a text at `ob + o`, moving `o` past it; `j` counts. -/
def appendText (k : Nat) : List PStmt :=
  copy "j" (eAdd (v "ob") (v "o")) (textAddr k) (n (textLen k)) ++
    [.assign "o" (eAdd (v "o") (n (textLen k)))]

/-- The revision, of the length `rl` holds. -/
def appendRevision : List PStmt :=
  copy "j" (eAdd (v "ob") (v "o")) (at_ (ownOff + ownRev)) (v "rl") ++
    [.assign "o" (eAdd (v "o") (v "rl"))]

/-- The Message-ID looked up last. -/
def appendId : List PStmt :=
  [.dec "il" (ld (at_ (ownOff + ownIdLen))), keptIn (v "il") 250] ++
  copy "j" (eAdd (v "ob") (v "o")) (at_ (ownOff + ownId)) (v "il") ++
  [.assign "o" (eAdd (v "o") (v "il"))]

/-- A number, below 2^32, then a space; the locals named from `p` count. -/
def appendNumber (p : String) (x : PExpr) : List PStmt :=
  digits p (v "ob") "o" x (data - 1) ++ [.storeb (eAdd (v "ob") (v "o")) (n 32), inc "o"]

/-- The texts of the group's commands and replies, by their place in `SessionLayout.texts`. -/
def tGroup : Nat := 36
def tNext : Nat := 37
def tLast : Nat := 38
def tSelected : Nat := 39
def tNoSuchGroup : Nat := 40
def tNoCurrent : Nat := 41
def tNoNext : Nat := 42
def tNoPrevious : Nat := 43
def tNoNumber : Nat := 44

/-- The address of the source, of the length `sl` holds. -/
def appendSource : List PStmt :=
  copy "j" (eAdd (v "ob") (v "o")) (at_ (ownOff + ownSrc)) (v "sl") ++
    [.assign "o" (eAdd (v "o") (v "sl"))]

def record (idx : PExpr) : PExpr := eAdd (at_ tableOff) (eMul idx (n connSlot))

/-- The text `t` — a reply's code, or one of the greetings' — into the output of connection `c`,
from its start. -/
def connText : PFun :=
  let text (code : Nat) (parts : List (List PStmt)) : PStmt :=
    ifs (eEq (v "t") (n code)) parts.flatten
  { name := "connText", params := [(1, "c"), (1, "t")], body :=
    [keptIn (v "c") (conns - 1), .dec "cb" (record (v "c")),
     .dec "ob" (atOff (v "cb") cOut), .dec "o" (n 0), .dec "j" (n 0),
     .dec "rl" (ld (at_ (ownOff + ownRevLen))), .dec "sl" (ld (at_ (ownOff + ownSrcLen))),
     keptIn (v "rl") revMax, keptIn (v "sl") srcMax,
     text greetCode [appendText tGreetingHead, appendRevision, appendText tGreetingMid,
       appendSource, appendText tCrlf],
     text greetPostCode [appendText tGreetingPostHead, appendRevision, appendText tGreetingPostMid,
       appendSource, appendText tCrlf],
     text (replyCode .capabilities)
       [appendText tCapabilitiesHead, appendRevision, appendText tBlockEnd],
     text (replyCode .capabilitiesPost) [appendText tCapabilitiesHead, appendRevision,
       appendText tCapabilitiesPostTail, appendText tBlockEnd],
     text (replyCode .help) [appendText tHelpHead, appendRevision, appendText tHelpMid,
       appendSource, appendText tBlockEnd],
     text (replyCode .helpPost) [appendText tHelpPostHead, appendRevision, appendText tHelpMid,
       appendSource, appendText tBlockEnd],
     text (replyCode (.stat 0 []))
       [appendText tStat, appendNumber "sn" (ownW ownNum), appendId, appendText tCrlf],
     text (replyCode (.selected 0 0 0 []))
       [appendText tSelected, appendNumber "nc" (ownW ownCount), appendNumber "nl" (ownW ownLow),
        appendNumber "nh" (ownW ownHigh),
        [.dec "sg" (fld "cb" cGroup), keptIn (v "sg") groupsMax,
         ifs (eEq (v "sg") (n 0)) (stop brokenState),
         .dec "gp" (eAdd (at_ (recOff + News.RecoverProg.rGroups))
           (eMul (eSub (v "sg") (n 1)) (n News.RecoverProg.rGroupSlot))),
         .dec "gl" (ld (v "gp")), keptIn (v "gl") groupMax, keptIn (v "o") (data - groupMax - 2)],
        copy "j" (eAdd (v "ob") (v "o")) (atOff (v "gp") 8) (v "gl"),
        [.assign "o" (eAdd (v "o") (v "gl"))], appendText tCrlf]] ++
    ([(.quit, tQuit), (.noGroup, tNoGroup), (.noSuchId, tNoSuchId), (.unknown, tUnknown),
      (.syntax, tSyntax), (.post, tPost), (.posted, tPosted), (.failed, tFailed),
      (.notPermitted, tNotPermitted), (.unavailable, tUnavailable), (.unreadable, tUnreadable),
      (.noSuchGroup, tNoSuchGroup), (.noCurrent, tNoCurrent), (.noNext, tNoNext),
      (.noPrevious, tNoPrevious), (.noNumber, tNoNumber)].map
      fun ((r : News.CommandSpec.Reply), k) => text (replyCode r) [appendText k]) ++
    [setf "cb" cOutLen (v "o"), .ret (n 0)] }

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

/-- `eqk` is one when the first word is the name the text `t` holds, in any case. -/
def nameIsAt (t : Nat) : List PStmt :=
  [.assign "eqk" (eEq (v "l0") (n (textLen t))),
   .assign "jq" (n 0),
   .while (eAnd (v "eqk") (eLt (v "jq") (v "l0")))
     [.ite (ne (fold (kept (eAdd (v "s0") (v "jq")))) (.loadb (eAdd (textAddr t) (v "jq"))))
        [.assign "eqk" (n 0)] [],
      inc "jq"]]

/-- `eqk` is one when the first word is the `k`-th command name, in any case. -/
def nameIs (k : Nat) : List PStmt := nameIsAt (tNames + k)

/-- The names of ARTICLE and BODY, by their place in `SessionLayout.texts`. -/
def tArticle : Nat := 27
def tBody : Nat := 28

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

/-- `ok` is one when the second word is a newsgroup name: `wildmat-exact` characters (§9.8), the
US-ASCII ones printable but for `!*,?[\]`, past US-ASCII UTF-8 as RFC 3629 §4 writes it; `nd`
counts the continuation octets a character still needs, the first of them between `clo` and
`chi`. -/
def groupNameCheck : List PStmt :=
  let between (lo hi : Nat) (e : PExpr) : PExpr := eAnd (eLe (n lo) e) (eLe e (n hi))
  [.assign "ok" (eLe (n 1) (v "l1")), .dec "nd" (n 0), .dec "clo" (n 128), .dec "chi" (n 191),
   .assign "jq" (n 0),
   .while (eAnd (v "ok") (eLt (v "jq") (v "l1")))
     [.dec "cz" (kept (eAdd (v "s1") (v "jq"))),
      .ite (eLt (n 0) (v "nd"))
        [ifs (or2 (eLt (v "cz") (v "clo")) (eLt (v "chi") (v "cz"))) [.assign "ok" (n 0)],
         .assign "nd" (eSub (v "nd") (n 1)), .assign "clo" (n 128), .assign "chi" (n 191)]
        [.ite (eLt (v "cz") (n 128))
          [.assign "ok" (or2 (or2 (or2 (between 34 41 (v "cz")) (eEq (v "cz") (n 43)))
              (or2 (between 45 62 (v "cz")) (between 64 90 (v "cz")))) (between 94 126 (v "cz")))]
          [.ite (between 194 223 (v "cz")) [.assign "nd" (n 1)]
            [.ite (eEq (v "cz") (n 224)) [.assign "nd" (n 2), .assign "clo" (n 160)]
              [.ite (or2 (between 225 236 (v "cz")) (between 238 239 (v "cz"))) [.assign "nd" (n 2)]
                [.ite (eEq (v "cz") (n 237)) [.assign "nd" (n 2), .assign "chi" (n 159)]
                  [.ite (eEq (v "cz") (n 240)) [.assign "nd" (n 3), .assign "clo" (n 144)]
                    [.ite (between 241 243 (v "cz")) [.assign "nd" (n 3)]
                      [.ite (eEq (v "cz") (n 244)) [.assign "nd" (n 3), .assign "chi" (n 143)]
                        [.assign "ok" (n 0)]]]]]]]]],
      inc "jq"],
   ifs (eLt (n 0) (v "nd")) [.assign "ok" (n 0)]]

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
as `DN.News.CommandSpec.replyIn` gives it, POST, ARTICLE, BODY, GROUP, NEXT and LAST commands when
there is a store, which looks up a message-id (`lookup`), a number (`byNumber`, its value in `val`),
the current article (`current`), a group (`select`) and the next or previous article (`move`). -/
def classify : List PStmt :=
  scanWords ++
  [.dec "cmd" (n 0), .dec "eqk" (n 0), .dec "jq" (n 0), .dec "ok" (n 0), .dec "val" (n 0),
   .ite (eEq (v "w") (n 0))
     [.ite (isKind .overlong) [reply .unknown] [reply .ignore]]
     ((List.range 5).flatMap (fun k => nameIs k ++
        [.ite (v "eqk") [.assign "cmd" (n (k + 1))] []]) ++
      [ifs hasStore (nameIs 5 ++ [ifs (v "eqk") [.assign "cmd" (n 6)]] ++
         nameIsAt tArticle ++ [ifs (v "eqk") [.assign "cmd" (n 7)]] ++
         nameIsAt tBody ++ [ifs (v "eqk") [.assign "cmd" (n 8)]] ++
         nameIsAt tGroup ++ [ifs (v "eqk") [.assign "cmd" (n 9)]] ++
         nameIsAt tNext ++ [ifs (v "eqk") [.assign "cmd" (n 10)]] ++
         nameIsAt tLast ++ [ifs (v "eqk") [.assign "cmd" (n 11)]]),
       .ite (eEq (v "cmd") (n 0)) [reply .unknown]
        [.ite (ne (v "kind") (n (News.FramerProg.kindCode .command))) [reply .syntax]
          [.dec "args" (eSub (v "w") (n 1)),
           .ite (eEq (v "cmd") (n 1))
             [.ite (eEq (v "args") (n 0)) [reply .capabilities]
               [.ite (eEq (v "args") (n 1))
                 (keywordCheck ++ [.ite (v "ok") [reply .capabilities] [reply .syntax]])
                 [reply .syntax]]]
             [.ite (eEq (v "cmd") (n 2))
               [.ite (eEq (v "args") (n 0)) [reply .help] [reply .syntax]]
               [.ite (eEq (v "cmd") (n 3))
                 [.ite (eEq (v "args") (n 0)) [reply .quit] [reply .syntax]]
                 [.ite (eEq (v "cmd") (n 6))
                   [.ite (eEq (v "args") (n 0)) [reply .post] [reply .syntax]]
                   [.ite (eEq (v "cmd") (n 9))
                     [.ite (eEq (v "args") (n 1))
                       (groupNameCheck ++
                        [.ite (v "ok")
                          [.ite (eLe (v "l1") (n News.CommandSpec.groupNameMax))
                            [reply (.select [])] [reply .noSuchGroup]]
                          [reply .syntax]])
                       [reply .syntax]]
                     [.ite (or2 (eEq (v "cmd") (n 10)) (eEq (v "cmd") (n 11)))
                       [.ite (eEq (v "args") (n 0)) [reply (.move true)] [reply .syntax]]
                       [.ite (eEq (v "args") (n 0))
                         [.ite hasStore [reply (.current .head)] [reply .noGroup]]
                         [.ite (eEq (v "args") (n 1))
                           (numberCheck ++
                            [.ite (v "ok")
                              [.ite hasStore [reply (.byNumber .head 0)] [reply .noGroup]]
                              (messageIdCheck ++
                               [.ite (v "ok")
                                 [.ite hasStore [reply (.lookup .head 0 [])] [reply .noSuchId]]
                                 [reply .syntax]])])
                           [reply .syntax]]]]]]]]]]])]

/-- The read an ARTICLE (one), HEAD (two) or BODY (three) is answered by, as `wc`, of the commit at
`wci`, its first line giving the number `no`; or, for STAT, 223. -/
def readOrStat (no : PExpr) : List PStmt :=
  [.ite (eEq (v "cmd") (n 5)) [reply (.stat 0 []), SessionStore.sset ownNum no]
    [.assign "wci" (eSub found (n 1)), .assign "wc" (n 2), .assign "wno" no,
     ifs (eEq (v "cmd") (n 7)) [.assign "wc" (n 1)],
     ifs (eEq (v "cmd") (n 8)) [.assign "wc" (n 3)]]]

/-- GROUP (`SessionSpec.resolve`): the group of the store whose name is the second word, its count
and its lowest and highest numbers, an empty group's 1 and 0, to be selected and its first article
made current; or 411. -/
def selectGroup : List PStmt :=
  [.dec "gc" (ld (at_ (recOff + News.RecoverProg.rGroupCount))), keptIn (v "gc") groupsMax,
   .dec "gx" (n groupsMax), .dec "gq" (n 0),
   .while (eLt (v "gq") (v "gc"))
     [.dec "gp" (eAdd (at_ (recOff + News.RecoverProg.rGroups))
        (eMul (v "gq") (n News.RecoverProg.rGroupSlot))),
      .dec "gl" (ld (v "gp")), keptIn (v "gl") groupMax,
      ifs (eAnd (eEq (v "gx") (n groupsMax)) (eEq (v "gl") (v "l1")))
        [.dec "same" (n 1), .dec "jg" (n 0),
         .while (eLt (v "jg") (v "gl"))
           [ifs (ne (.loadb (eAdd (atOff (v "gp") 8) (v "jg"))) (kept (eAdd (v "s1") (v "jg"))))
              [.assign "same" (n 0)],
            inc "jg"],
         ifs (v "same") [.assign "gx" (v "gq")]],
      inc "gq"],
   .ite (eEq (v "gx") (n groupsMax)) [reply .noSuchGroup]
     (callS "gs" "groupScan" [v "gx", n 0, n 0] ++
      [.dec "gk" (ownW ownCount),
       ifs (eEq (v "gk") (n 0)) [SessionStore.sset ownLow (n 1), SessionStore.sset ownHigh (n 0)],
       reply (.selected 0 0 0 []), .assign "setg" (n 1), .assign "gnew" (eAdd (v "gx") (n 1)),
       .assign "setc" (n 1), .assign "cnew" (n 0),
       ifs (ne (v "gk") (n 0)) [.assign "cnew" (ownW ownLow)]])]

/-- By number or of the current article (`SessionSpec.resolve`): with no group selected 412; the
article of that number in the selected group, else 423, or the current one, else 420. -/
def numberLookup : List PStmt :=
  [.dec "gg" (fld "cb" cGroup), keptIn (v "gg") groupsMax, .dec "isc" (isReply (.current .head)),
   .ite (eEq (v "gg") (n 0)) [reply .noGroup]
     [.dec "wn" (v "val"),
      ifs (v "isc") [.assign "wn" (fld "cb" cCurrent)], keptIn (v "wn") 2147483647,
      .ite (eAnd (v "isc") (eEq (v "wn") (n 0))) [reply .noCurrent]
        (callS "gs" "groupScan" [eSub (v "gg") (n 1), n 1, v "wn"] ++
         [.ite (eEq found (n 0)) [.ite (v "isc") [reply .noCurrent] [reply .noNumber]]
           ([.dec "fci" (eSub found (n 1))] ++ callS "io" "idOf" [v "fci"] ++ readOrStat (v "wn") ++
            [ifs (eEq (v "cmd") (n 5)) [.assign "setc" (n 1), .assign "cnew" (v "wn")]])])]]

/-- NEXT and LAST (`SessionSpec.resolve`): with no group selected 412, with no current article 420;
the article of the lowest number above the current one, or the highest below, made current with
223, else 421 and 422. -/
def moveLookup : List PStmt :=
  [.dec "gm" (fld "cb" cGroup), keptIn (v "gm") groupsMax,
   .ite (eEq (v "gm") (n 0)) [reply .noGroup]
     [.dec "cur" (fld "cb" cCurrent), keptIn (v "cur") 2147483647,
      .ite (eEq (v "cur") (n 0)) [reply .noCurrent]
        (callS "gs" "groupScan" [eSub (v "gm") (n 1), eAdd (n 2) (eEq (v "cmd") (n 11)), v "cur"] ++
         [.ite (eEq found (n 0)) [.ite (eEq (v "cmd") (n 10)) [reply .noNext] [reply .noPrevious]]
           ([.dec "mn" (ownW ownNum), .dec "mci" (eSub found (n 1))] ++
            callS "im" "idOf" [v "mci"] ++
            [reply (.stat 0 []), .assign "setc" (n 1), .assign "cnew" (v "mn")])])]]

/-- The reply as a store makes it (`SessionSpec.resolve`): the capabilities with POST while the
connection may post, the help with POST, for a POST 440 or 403 unless it may have a slot, and for a
message-id 430 when the store does not hold it, 223 for STAT when it does; else the ARTICLE (one),
HEAD (two) or BODY (three) to be answered by a read, as `wc`, of the commit at `wci`, its first line
giving the number `wno`; the replies of the selected group and the current article, and where they
leave them (`setg`, `gnew`, `setc`, `cnew`). -/
def resolve : List PStmt :=
  [.dec "wc" (n 0), .dec "wci" (n 0), .dec "wno" (n 0), .dec "setg" (n 0), .dec "gnew" (n 0),
   .dec "setc" (n 0), .dec "cnew" (n 0),
   ifs (eAnd (isReply .capabilities) (eAnd (fld "cb" cGreeted) (ownW ownAccepting)))
     [reply .capabilitiesPost],
   ifs (eAnd (isReply .help) hasStore) [reply .helpPost],
   ifs (isReply .post)
     [.ite (eEq (fld "cb" cGreeted) (n 0)) [reply .notPermitted]
       [ifs (eEq (ownW ownAccepting) (n 0)) [reply .unavailable]]],
   ifs (isReply (.lookup .head 0 []))
     ([keptIn (v "l1") 250, .store (at_ (ownOff + ownIdLen)) (v "l1"), .dec "ij" (n 0),
       .while (eLt (v "ij") (v "l1"))
         [.storeb (eAdd (at_ (ownOff + ownId)) (v "ij")) (kept (eAdd (v "s1") (v "ij"))), inc "ij"]] ++
      callS "fi" "idFind" [v "l1"] ++
      [.ite (eEq found (n 0)) [reply .noSuchId] (readOrStat (n 0))]),
   ifs (isReply (.select [])) selectGroup,
   ifs (or2 (isReply (.byNumber .head 0)) (isReply (.current .head))) numberLookup,
   ifs (isReply (.move true)) moveLookup]

/-! ## A connection's turn -/

/-- The record's fields as expressions. -/
def outLen : PExpr := fld "cb" cOutLen
def phase : PExpr := fld "cb" cPhase
def inPhase (ph : News.SessionSpec.Phase) : PExpr := eEq phase (n (phaseCode ph))
def toPhase (ph : News.SessionSpec.Phase) : PStmt := setf "cb" cPhase (n (phaseCode ph))
def heldEmpty : PExpr := eEq (fld "cb" cHeldPos) (fld "cb" cHeldLen)

/-- Answer the first held line that gets a reply and frame on past the lines that get none, as
`DN.News.SessionSpec.serve` does; a POST that may have a slot waits for one, and an ARTICLE, HEAD or
BODY of an article the store holds for a read, framing on. -/
def serve : List PStmt :=
  [.dec "blk" (atOff (v "cb") cFramer), .dec "p" (atOff (v "cb") cHeld),
   .dec "n" (fld "cb" cHeldLen), .dec "i" (fld "cb" cHeldPos), .dec "sv" (n 1),
   keptIn (v "n") data, keptIn (v "i") data,
   .while (v "sv")
     [.ite (eEq (v "i") (v "n")) [.assign "sv" (n 0)]
       ([keptIn (ld (v "blk")) lineLimit, .dec "i0" (v "i")] ++
        News.FramerProg.lineDecs ++
        News.FramerProg.lineFrag lineLimit ++
        [.ite (eEq (v "kind") (n 0)) [.assign "sv" (n 0)]
          ([.dec "r" (n (replyCode .ignore))] ++ classify ++ resolve ++
           [.ite (isReply .ignore) []
             [.ite (or2 (ne outLen (n 0)) (ne (fld "cb" cWant) (n 0)))
               [.assign "i" (v "i0"), .assign "sv" (n 0)]
               [.ite (isReply .post)
                 [setf "cb" cWaiting (n 1), setf "cb" cFirst (n 0), setf "cb" cIdle (n 0),
                  .assign "sv" (n 0)]
                 [.ite (v "wc")
                   [setf "cb" cWant (v "wc"), setf "cb" cWantCi (v "wci"),
                    setf "cb" cWantNo (v "wno"), setf "cb" cFirst (n 0), setf "cb" cIdle (n 0)]
                 ([ifs (v "setg") [setf "cb" cGroup (v "gnew")],
                   ifs (v "setc") [setf "cb" cCurrent (v "cnew")]] ++
                  callS "wt" "connText" [v "c", v "r"] ++
                  [setf "cb" cFirst (n 0),
                   setf "cb" cIdle (eAdd (v "now") (n inactivity)),
                   .ite (isReply .quit)
                     [toPhase .quitting, .assign "i" (v "n"), .assign "sv" (n 0)] []])]]]])])],
   .ite (eEq (v "i") (v "n")) [setf "cb" cHeldPos (n 0), setf "cb" cHeldLen (n 0)]
     [setf "cb" cHeldPos (v "i")]]

/-- The action slot of the connection `x`. -/
def actionAt (x : PExpr) : PExpr := eAdd (at_ (emitOff + emitActions)) (eMul x (n actionSlot))

/-- One more action in the turn. -/
def bump : PStmt := .store (at_ (ownOff + ownActs)) (eAdd (ownW ownActs) (n 1))

/-- An action with no bytes for the connection `c`. -/
def closing (kind : Nat) : List PStmt :=
  [.dec "slot" (actionAt (v "c")), setf "slot" actionKind (n kind), setf "slot" actionIdx (v "c"),
   setf "slot" actionGen (fld "cb" cGen), setf "slot" actionLen (n 0),
   setf "slot" actionRead (n 0), setf "slot" actionTaken (n 0), bump,
   setf "cb" cActed (n 1), setf "cb" cLive (n 0)]

/-- The connection's output as a send, and whether to read once it is taken. -/
def sending : List PStmt :=
  [.dec "slot" (actionAt (v "c")), .dec "ol" outLen, keptIn (v "ol") data,
   setf "slot" actionKind (n send),
   setf "slot" actionIdx (v "c"), setf "slot" actionGen (fld "cb" cGen),
   setf "slot" actionLen (v "ol"), setf "slot" actionRead (v "wants"),
   setf "slot" actionTaken (n 0)] ++
  copyNew "aj" (atOff (v "slot") actionHead) (atOff (v "cb") cOut) (v "ol") ++
  [bump, setf "cb" cActed (n 1), setf "cb" cReading (v "wants")]

/-- A send of no bytes, that tells the host whether to read. -/
def emptySend : List PStmt :=
  [.dec "slot" (actionAt (v "c")), setf "slot" actionKind (n send),
   setf "slot" actionIdx (v "c"), setf "slot" actionGen (fld "cb" cGen),
   setf "slot" actionLen (n 0), setf "slot" actionRead (v "wants"), setf "slot" actionTaken (n 0),
   bump, setf "cb" cActed (n 1), setf "cb" cReading (v "wants")]

/-- The line's deadline runs while the program waits for the rest of a line, as
`DN.News.SessionSpec.Conn.waitLine` says. -/
def waitLine : List PStmt :=
  [.ite (eAnd (eAnd (eAnd (eEq outLen (n 0)) (inPhase .open_)) (eEq (fld "cb" cWant) (n 0)))
      (eLt (n 0)
        (eAdd (eAdd (fld "cb" cFramer) (fld "cb" (cFramer + 8))) (fld "cb" (cFramer + 16)))))
     [.ite (eEq (fld "cb" cLineDue) (n 0))
       [setf "cb" cLineDue (eAdd (v "now") (n lineTime))] []]
     [setf "cb" cLineDue (n 0)]]

/-- The store told that the connection `x` of generation `g` is gone or no longer reads. -/
def abandon (x g : PExpr) : List PStmt := [ifs hasStore (callS "ab" "postAbandon" [x, g])]

/-- `SessionSpec.progress`: the octets held framed into the slot of the connection's POST; the
article's deadline stopped once its block has ended; once the slot has an outcome, the slot left,
and its reply put to send, or the connection to close (`lost`) when the outcome is unknown. -/
def progress : List PStmt :=
  [ifs (eAnd (eAnd (ne (fld "cb" cPost) (n 0)) hasStore)
        (eAnd (eEq outLen (n 0)) (ne phase (n (phaseCode .quitting)))))
    ([.dec "pk" (eSub (fld "cb" cPost) (n 1)), keptIn (v "pk") (posts - 1)] ++
     callS "fd" "postFeed" [v "c", v "pk"] ++ callS "td" "postTidyAll" [] ++
     [.dec "zs" (eAdd (at_ slotsOff) (eMul (v "pk") (n slotLen))),
      .ite (fld "zs" zLive)
        [ifs (fld "zs" zEnded) [setf "cb" cArticleDue (n 0)],
         .dec "oc" (fld "zs" zOutcome),
         ifs (v "oc")
           ([setf "zs" zOwner (n 0)] ++ callS "tf" "postTidyAll" [] ++
            [.ite (eEq (v "oc") (n outLost)) [.assign "lost" (n 1)]
              ([.dec "rr" (n (replyCode .failed)),
                ifs (eEq (v "oc") (n outPosted)) [.assign "rr" (n (replyCode .posted))]] ++
               callS "wo" "connText" [v "c", v "rr"] ++
               [setf "cb" cPost (n 0), setf "cb" cIdle (eAdd (v "now") (n inactivity)),
                .assign "said" (n 1)])])]
        [setf "cb" cPost (n 0)]])]

/-- The read of the connection, as `rs`. -/
def readRec : List PStmt :=
  [.dec "rk" (eSub (fld "cb" cRead) (n 1)), keptIn (v "rk") (reads - 1),
   .dec "rs" (eAdd (at_ readsOff) (eMul (v "rk") (n readLen)))]

/-- `SessionSpec.progressRead`: with nothing untaken, the read's next octets put to send, the
inactivity deadline started, or stopped while there are none; a read that failed answered 403 when
it gave nothing, the read over, or the connection to close (`rlost`). -/
def progressRead : List PStmt :=
  [ifs (eAnd (eAnd (ne (fld "cb" cRead) (n 0)) hasStore)
        (eAnd (eEq outLen (n 0)) (ne phase (n (phaseCode .quitting)))))
    (readRec ++
     [.ite (fld "rs" rBad)
       [.ite (eEq (fld "rs" rGiven) (n 0))
         (callS "wu" "connText" [v "c", n (replyCode .unreadable)] ++
          [setf "rs" rOwner (n 0), setf "cb" cRead (n 0), setf "cb" cWant (n 0),
           setf "cb" cIdle (eAdd (v "now") (n inactivity))] ++ callS "tr" "postTidyAll" [])
         [.assign "rlost" (n 1)]]
       (callS "rp" "readPiece" [v "c", v "rk"] ++
        [.ite found ([setf "cb" cIdle (eAdd (v "now") (n inactivity))] ++ callS "tp" "postTidyAll" [])
          [setf "cb" cIdle (n 0)]])])]

/-- `SessionSpec.claimRead`: an ARTICLE, HEAD or BODY that waits gets the first free read when fewer
came before it than reads are free. -/
def claimRead : List PStmt :=
  [ifs (eAnd (eAnd (ne (fld "cb" cWant) (n 0)) (eEq (fld "cb" cRead) (n 0)))
        (eAnd (eAnd (eEq outLen (n 0)) (inPhase .open_)) hasStore))
    (callS "ra" "readAdmits" [v "c", fld "cb" cGen] ++
     [ifs found
       [.dec "fq" (n reads), .dec "q" (n 0),
        .while (eLt (v "q") (n reads))
          [ifs (eAnd (eEq (v "fq") (n reads))
              (eEq (ld (eAdd (at_ (readsOff + rLive)) (eMul (v "q") (n readLen)))) (n 0)))
             [.assign "fq" (v "q")],
           inc "q"],
        ifs (eLt (v "fq") (n reads))
          (callS "u3" "queueDrop" [readers, v "c", fld "cb" cGen] ++
           [setf "cb" cRead (eAdd (v "fq") (n 1))] ++
           callS "rc" "readClaim"
             [v "fq", v "c", fld "cb" cGen, fld "cb" cWant, fld "cb" cWantCi, fld "cb" cWantNo])]])]

/-- `SessionSpec.claim`: a POST that waits gets the first free slot and 340 when fewer came before
it than slots are free, or 403 once the store has stopped accepting. -/
def claim : List PStmt :=
  [ifs (eAnd (eAnd (fld "cb" cWaiting) hasStore) (eAnd (eEq outLen (n 0)) (inPhase .open_)))
    [.ite (eEq (ownW ownAccepting) (n 0))
      (callS "uw" "queueDrop" [waiters, v "c", fld "cb" cGen] ++ [setf "cb" cWaiting (n 0)] ++
       callS "w3" "connText" [v "c", n (replyCode .unavailable)] ++
       [setf "cb" cIdle (eAdd (v "now") (n inactivity))])
      (callS "ad" "postAdmits" [v "c", fld "cb" cGen] ++
       [ifs found
         [.dec "fk" (n posts), .dec "q" (n 0),
          .while (eLt (v "q") (n posts))
            [ifs (eAnd (eEq (v "fk") (n posts))
                (eEq (ld (eAdd (at_ slotsOff) (eMul (v "q") (n slotLen)))) (n 0)))
               [.assign "fk" (v "q")],
             inc "q"],
          ifs (eLt (v "fk") (n posts))
            (callS "u2" "queueDrop" [waiters, v "c", fld "cb" cGen] ++
             [setf "cb" cWaiting (n 0), setf "cb" cPost (eAdd (v "fk") (n 1))] ++
             callS "w4" "connText" [v "c", n (replyCode .post)] ++
             [setf "cb" cArticleDue (eAdd (v "now") (n articleTime))] ++
             callS "cl" "postClaim" [v "fk", v "c", fld "cb" cGen, fld "cb" cNumber])]])]]

/-- `SessionSpec.emit`: the output as a send, unless the host has not yet reported the connection
ready; a graceful close once everything is answered and taken after a QUIT or the end of input;
or a send of nothing when whether to read has changed. No POST or read waits or answers the
connection when it is asked to read. -/
def emit : List PStmt :=
  [.dec "wants" (eAnd (eAnd (inPhase .open_) heldEmpty)
      (eAnd (eEq (fld "cb" cWaiting) (n 0)) (eEq (fld "cb" cWant) (n 0)))),
   ifs (eAnd (v "wants") (ne (fld "cb" cPost) (n 0)))
     ([.dec "tk" (eSub (fld "cb" cPost) (n 1))] ++ callS "tq" "postTakes" [v "tk"] ++
      [.assign "wants" found]),
   .ite (ne outLen (n 0))
     [ifs (eEq (fld "cb" cBlocked) (n 0)) sending]
     [.ite (or2 (inPhase .quitting) (eAnd (inPhase .ending) heldEmpty)) (closing closeGracefully)
       [ifs (eAnd (inPhase .open_) (ne (fld "cb" cReading) (v "wants"))) emptySend]],
   ifs (fld "cb" cLive) waitLine]

/-- One connection in use, after the batch's events and completions (`SessionSpec.act`). -/
def act : List PStmt :=
  [.dec "due" (or2 (or2
      (eAnd (ne (fld "cb" cFirst) (n 0)) (eLe (fld "cb" cFirst) (v "now")))
      (eAnd (ne (fld "cb" cIdle) (n 0)) (eLe (fld "cb" cIdle) (v "now"))))
      (or2 (eAnd (ne (fld "cb" cLineDue) (n 0)) (eLe (fld "cb" cLineDue) (v "now")))
        (eAnd (ne (fld "cb" cArticleDue) (n 0)) (eLe (fld "cb" cArticleDue) (v "now"))))),
   .ite (v "due") (closing closeNow ++ abandon (v "c") (fld "cb" cGen))
     ([.dec "lost" (n 0), .dec "rlost" (n 0), .dec "said" (n 0), .dec "was" (fld "cb" cWaiting)] ++
      progress ++
      [.ite (v "lost") (closing closeNow)
        (progressRead ++
         [.ite (v "rlost") (closing closeNow ++ abandon (v "c") (fld "cb" cGen))
           ([.dec "wasw" (fld "cb" cWant),
             .ite (or2 (v "said") (eAnd (eAnd (eEq outLen (n 0)) (ne phase (n (phaseCode .quitting))))
                (eAnd (eAnd (eEq (fld "cb" cPost) (n 0)) (eEq (fld "cb" cWaiting) (n 0)))
                  (eEq (fld "cb" cWant) (n 0))))) serve [],
             ifs (eAnd (fld "cb" cWaiting) (eEq (v "was") (n 0)))
               (callS "pw" "queueAdd" [waiters, v "c", fld "cb" cGen]),
             ifs (eAnd (ne (fld "cb" cWant) (n 0)) (eEq (v "wasw") (n 0)))
               (callS "rw" "queueAdd" [readers, v "c", fld "cb" cGen])] ++
            claim ++ claimRead ++ emit)])])]

/-! ## A turn -/

/-- A new connection, greeted: with 200 when it may post, the store accepts and carries a
group. -/
def openConn : List PStmt :=
  [.ite (fld "cb" cLive) (breach .reopened)
    ([.dec "op" (eAdd (ownW ownOpened) (n 1)), .store (at_ (ownOff + ownOpened)) (v "op"),
      .dec "gr" (eAnd (eAnd (ne (fld "ev" eventPost) (n 0)) hasStore)
        (eAnd (ownW ownAccepting)
          (ne (ld (at_ (recOff + News.RecoverProg.rGroupCount))) (n 0)))),
      setf "cb" cLive (n 1), setf "cb" cGen (v "eg"), toPhase .open_,
      setf "cb" cReading (n 0), setf "cb" cBlocked (n 0),
      setf "cb" cFirst (eAdd (v "now") (n firstCommand)),
      setf "cb" cIdle (eAdd (v "now") (n inactivity)),
      setf "cb" cLineDue (n 0), setf "cb" cHeldLen (n 0), setf "cb" cHeldPos (n 0),
      setf "cb" cFramer (n 0), setf "cb" (cFramer + 8) (n 0), setf "cb" (cFramer + 16) (n 0),
      setf "cb" cNumber (v "op"), setf "cb" cGreeted (v "gr"), setf "cb" cWaiting (n 0),
      setf "cb" cPost (n 0), setf "cb" cArticleDue (n 0), setf "cb" cWant (n 0),
      setf "cb" cWantCi (n 0), setf "cb" cRead (n 0), setf "cb" cGroup (n 0),
      setf "cb" cCurrent (n 0), setf "cb" cWantNo (n 0),
      .dec "gt" (n greetCode), ifs (v "gr") [.assign "gt" (n greetPostCode)]] ++
     callS "wg" "connText" [v "ex", v "gt"])]

/-- Whether the connection may report input: it takes commands, asked to read, and has nothing
untaken and nothing held. -/
def asked : PExpr :=
  eAnd (eAnd (inPhase .open_) (fld "cb" cReading)) (eAnd (eEq outLen (n 0)) heldEmpty)

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
       [.ite asked
         ([toPhase .ending, setf "cb" cLineDue (n 0), setf "cb" cPost (n 0),
           setf "cb" cArticleDue (n 0), setf "cb" cWant (n 0), setf "cb" cRead (n 0)] ++
          abandon (v "ex") (v "eg"))
         (breach .unasked)] []] [],
   .ite (eEq (v "ek") (n closed))
     [.ite (v "lv") (setf "cb" cLive (n 0) :: abandon (v "ex") (v "eg")) []] []]

/-- What the host took of the connection `sc`'s action: for a send, the output left, whether to
wait for the host, and activity, which output taken is but in a POST. Of the action slot only the
count the host wrote back is read; the rest the program knows from its own record. -/
def settle : List PStmt :=
  [.dec "cb" (record (v "sc")),
   .ite (fld "cb" cActed)
     [setf "cb" cActed (n 0),
      .ite (fld "cb" cLive)
        ([.dec "tk" (ld (atOff (actionAt (v "sc")) actionTaken)), .dec "al" outLen,
          keptIn (v "al") data,
          .ite (or2 (eLt (v "tk") (n 0)) (eLt (v "al") (v "tk"))) (breach .overTaken) [],
          .dec "ob" (atOff (v "cb") cOut), .dec "sj" (v "tk"),
          .while (eLt (v "sj") (v "al"))
            [.storeb (eAdd (v "ob") (eSub (v "sj") (v "tk"))) (.loadb (eAdd (v "ob") (v "sj"))),
             inc "sj"],
          setf "cb" cOutLen (eSub (v "al") (v "tk")), setf "cb" cBlocked (eLt (v "tk") (v "al")),
          .ite (eAnd (ne (fld "cb" cRead) (n 0)) (eLe (v "al") (v "tk"))) [setf "cb" cIdle (n 0)]
            [ifs (eAnd (eLt (n 0) (v "tk"))
                (eAnd (eEq (fld "cb" cPost) (n 0)) (eEq (fld "cb" cWaiting) (n 0))))
              [setf "cb" cIdle (eAdd (v "now") (n inactivity))]]] ++
         waitLine) []] []]

/-- The time of the next turn, as `DN.News.SessionSpec.deadline` gives it, where the host reads it
in the next call: now if a connection can go on without the host (`Conn.ready`), else the
earliest deadline running. -/
def wake : List PStmt :=
  [.dec "dl" (n 0), .dec "rd" (n 0), .dec "dt" (n 0),
   .while (eLt (v "dt") (n conns))
     [.dec "cb" (record (v "dt")),
      ifs (fld "cb" cLive)
        ([.dec "ry" (n 0),
          ifs (eEq outLen (n 0))
            [.ite (ne phase (n (phaseCode .open_))) [.assign "ry" (n 1)]
              [.ite (fld "cb" cWaiting)
                [ifs hasStore
                  [.ite (eEq (ownW ownAccepting) (n 0)) [.assign "ry" (n 1)]
                    (callS "wa" "postAdmits" [v "dt", fld "cb" cGen] ++ [.assign "ry" found])]]
                [.ite (ne (fld "cb" cWant) (n 0))
                  [ifs hasStore
                    [.ite (eEq (fld "cb" cRead) (n 0))
                      (callS "wr" "readAdmits" [v "dt", fld "cb" cGen] ++ [.assign "ry" found])
                      ([.dec "wq" (eSub (fld "cb" cRead) (n 1)), keptIn (v "wq") (reads - 1),
                        .dec "ws" (eAdd (at_ readsOff) (eMul (v "wq") (n readLen)))] ++
                       callS "wo" "readOutSize" [v "wq"] ++
                       [.assign "ry" (or2 (fld "ws" rBad) (eLt (fld "ws" rGiven) found))])]]
                [ifs (eEq heldEmpty (n 0))
                  [.ite (eEq (fld "cb" cPost) (n 0)) [.assign "ry" (n 1)]
                    ([.dec "wk" (eSub (fld "cb" cPost) (n 1))] ++
                     callS "wt" "postTakes" [v "wk"] ++ [.assign "ry" found])]]]]],
          ifs (v "ry") [.assign "rd" (n 1)],
          .dec "ea" (n 0)] ++
         [cFirst, cIdle, cLineDue, cArticleDue].map (fun f =>
           ifs (eAnd (ne (fld "cb" f) (n 0)) (or2 (eEq (v "ea") (n 0)) (eLt (fld "cb" f) (v "ea"))))
             [.assign "ea" (fld "cb" f)]) ++
         [ifs (eAnd (ne (v "ea") (n 0)) (or2 (eEq (v "dl") (n 0)) (eLt (v "ea") (v "dl"))))
           [.assign "dl" (v "ea")]]),
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

/-! ## Recovery at start -/

section Start
open DN.News
open DN.News.RecoverProg (rw rset sw sset rp rKey rGroupCount rGroups rGroupSlot rFirst rName
  rNameLen rEnd rJournalSize rSeq rFound rFileSize rActAt rActLen rActA rActB rAct rFresh
  rJournalEnd rStatus rPhase asksName asksJournal asksOctets asksFile asksAside gives givesAside
  refused actKeep actRename actRemove actSyncDir actCut actCreate)
open DN.News.Journal (magic keyLength formatType startType headerLength firstFrame maxFrame)

def drv (off : Nat) : PExpr := at_ (drvOff + off)
def jobW (off : Nat) : PExpr := at_ (emitOff + emitJobs + off)
def opW (i off : Nat) : PExpr := jobW (jobOpsAt + i * opSlot + off)
def doneW (off : Nat) : PExpr := at_ (nextOff + nextDone + off)
/-- Word `w` of the results of operation `i` of the job that completed. -/
def result (i w : Nat) : PExpr := ld (doneW (doneResults + 16 * i + 8 * w))
/-- The bytes of the job handed over, and of its completion. -/
def jobBytes : PExpr := jobW jobHead
def doneBytes : PExpr := doneW doneHead

def putOp (i : Nat) (o : Op) : List PStmt :=
  [(opCode, n o.code), (opHandle, o.place), (opHandleGen, o.gen), (opName, o.name),
   (opNumber, o.number), (opToName, o.toName), (opToNumber, o.toNumber), (opOffset, o.offset),
   (opLength, o.length), (opData, n 0)].map fun (f, e) => .store (opW i f) e

/-- An operation on the journal. -/
def onJournal (code : Nat) : Op := { code, place := ld (drv dJnl), gen := ld (drv dJnlGen) }

/-- The job of `ops` in the first slot, handed over, and its completion awaited, the host not
listening yet: into `dok` whether every operation succeeded, into `dcl` the error's class. -/
def runJob (ops : List Op) : List PStmt :=
  [.store (drv dGen) (eAdd (ld (drv dGen)) (n 1)), .store (jobW jobKind) (n job),
   .store (jobW jobGen) (ld (drv dGen)), .store (jobW jobCount) (n ops.length)] ++
  (ops.zipIdx.flatMap fun (o, i) => putOp i o) ++
  [hand, .store (jobW jobKind) (n 0), .assign "dw" (n 1),
   .while (v "dw")
     [fetch,
      .ite (eAnd (eEq (ld (doneW doneKind)) (n done)) (eEq (ld (doneW doneGen)) (ld (drv dGen))))
        [.assign "dw" (n 0)] [hand]],
   .assign "dok" (eEq (ld (doneW doneOps)) (n ops.length)), .assign "dcl" (ld (doneW doneClass))]

/-- Stop when a job failed, its class where the host reads it. -/
def failed : List PStmt := .store (drv dClass) (v "dcl") :: stop recoveryFailed
def mustSucceed : PStmt := .ite (v "dok") [] failed

/-- `x` into `k` octets at `a`, least significant first. -/
def putLe (a x : PExpr) (k : Nat) : List PStmt :=
  (List.range k).map fun i => .storeb (atOff a i) (eAnd (.shr x (n (8 * i))) (n 255))

def putBytes (a : PExpr) (bs : List (BitVec 8)) : List PStmt :=
  bs.zipIdx.map fun (b, i) => .storeb (atOff a i) (n b.toNat)

/-- The frame of a record of `type` at journal offset `off` in the job's bytes, around the `len`
octets of payload already there, tagged under the key at `key`: the message the tag is computed
over is put together in the scanner's area. -/
def frameAround (off : PExpr) (type len : Nat) (key : PExpr) : List PStmt :=
  let msg := atOff (v "jsc") ScanProg.sMessage
  putLe msg off 8 ++ [.storeb (atOff msg 8) (n type)] ++
  copy "dj" (atOff msg 9) (atOff jobBytes headerLength) (n len) ++
  [.assign "k" key, .assign "p" msg, .assign "n" (n (9 + len))] ++ SipProg.sipSrc ++
  putLe jobBytes (n len) 4 ++ putLe (atOff jobBytes 4) (v "r") 8 ++
  [.storeb (atOff jobBytes 12) (n type),
   .storeb (atOff jobBytes (headerLength + len)) (n Journal.endMark.toNat)]

/-- The configuration into recovery's area: the key of a new journal and the groups. -/
def configure : List PStmt :=
  copy "dj" (atOff rp rKey) (at_ (nextOff + nextRandom + runValueLen)) (n keyLength) ++
  [.assign "dx" (ld (at_ (nextOff + nextGroupCount))),
   .ite (or2 (eLt (v "dx") (n 0)) (eLt (n groupsMax) (v "dx"))) (stop badIdentity) [],
   rset rGroupCount (v "dx"), .assign "da" (n 0),
   .while (eLt (v "da") (v "dx"))
     ([.assign "dl" (ld (eAdd (at_ (nextOff + nextGroups)) (eMul (v "da") (n groupSlot)))),
       .ite (or2 (eLt (v "dl") (n 0)) (eLt (n groupMax) (v "dl"))) (stop badIdentity) [],
       .store (eAdd (atOff rp rGroups) (eMul (v "da") (n rGroupSlot))) (v "dl")] ++
      copy "dj" (eAdd (atOff rp (rGroups + 8)) (eMul (v "da") (n rGroupSlot)))
        (eAdd (at_ (nextOff + nextGroups + 8)) (eMul (v "da") (n groupSlot))) (v "dl") ++
      [inc "da"])]

/-- The next name of the directory as it was opened, a page of the listing at a time, from the
first again when a pass begins; or none left. -/
def askName : List PStmt :=
  [.ite (ld (drv dDirOpen)) []
     (runJob [{ code := opOpenDir }] ++
      [mustSucceed, .store (drv dDir) (result 0 0), .store (drv dDirGen) (result 0 1),
       .store (drv dDirOpen) (n 1)]),
   .ite (rw rFirst)
     [.store (drv dIndex) (n 0), .store (drv dPageLen) (n 0), .store (drv dPagePos) (n 0)] [],
   .assign "dpos" (ld (drv dPagePos)), .assign "dlen" (ld (drv dPageLen)),
   keptIn (v "dlen") jobData, keptIn (v "dpos") jobData,
   .ite (eLe (v "dlen") (v "dpos"))
     (runJob [{ code := opList, place := ld (drv dDir), gen := ld (drv dDirGen),
                offset := ld (drv dIndex), length := n jobData }] ++
      [mustSucceed, .assign "dlen" (result 0 1), keptIn (v "dlen") jobData] ++
      copy "dj" (drv dPage) doneBytes (v "dlen") ++
      [.store (drv dPageLen) (v "dlen"), .assign "dpos" (n 0)]) [],
   .ite (eLt (v "dpos") (v "dlen"))
     ([.assign "dl" (.loadb (eAdd (drv dPage) (v "dpos"))),
       .ite (eLt (v "dlen") (eAdd (eAdd (v "dpos") (v "dl")) (n 1))) (stop brokenState) []] ++
      copy "dj" (atOff rp rName) (eAdd (eAdd (drv dPage) (v "dpos")) (n 1)) (v "dl") ++
      [rset rNameLen (v "dl"), rset rEnd (n 0),
       .store (drv dPagePos) (eAdd (eAdd (v "dpos") (v "dl")) (n 1)),
       .store (drv dIndex) (eAdd (ld (drv dIndex)) (n 1))])
     [rset rEnd (n 1)]]

/-- The journal opened, synced and its length given. -/
def askJournal : List PStmt :=
  [.ite (ld (drv dJnlOpen)) []
     (runJob [{ code := opOpen, name := n nameJournal }] ++
      [mustSucceed, .store (drv dJnl) (result 0 0), .store (drv dJnlGen) (result 0 1),
       .store (drv dJnlOpen) (n 1)])] ++
  runJob [onJournal opSync, onJournal opSize] ++ [mustSucceed, rset rJournalSize (result 1 0)]

/-- The octets of the journal the scanner wants, read after its window. -/
def askOctets : List PStmt :=
  [.assign "da" (sw ScanProg.sBase), .assign "dx" (sw ScanProg.sLen),
   .assign "dy" (sw ScanProg.sWant),
   keptIn (v "dx") ScanProg.windowMax, keptIn (v "dy") ScanProg.chunk,
   .ite (eLt (n ScanProg.windowMax) (eAdd (v "dx") (v "dy"))) (stop brokenState) []] ++
  runJob [{ onJournal opRead with offset := eAdd (v "da") (v "dx"), length := v "dy" }] ++
  [mustSucceed,
   .ite (ne (result 0 0) (v "dy")) (.store (drv dClass) (n 0) :: stop recoveryFailed) []] ++
  copy "dj" (eAdd (atOff (v "jsc") ScanProg.sWindow) (v "dx")) doneBytes (v "dy") ++
  [sset ScanProg.sLen (eAdd (v "dx") (v "dy"))]

/-- Whether the file of kind `kind` and number `rSeq` is there: with `sized`, its size too. -/
def askFile (kind : Nat) (sized : Bool) : List PStmt :=
  runJob [{ code := opOpen, name := n kind, number := rw rSeq }] ++
  [.ite (v "dok")
     ([.assign "dx" (result 0 0), .assign "dy" (result 0 1)] ++
      runJob ((if sized then [{ code := opSize, place := v "dx", gen := v "dy" }] else []) ++
        [{ code := opClose, place := v "dx", gen := v "dy" }]) ++
      [mustSucceed, rset rFound (n 1)] ++
      (if sized then [rset rFileSize (result 0 0)] else []))
     [.ite (eEq (v "dcl") (n classNotFound)) [rset rFound (n 0)] failed]]

/-- A torn tail kept: after its offset in eight octets, the octets the action names in the area. -/
def keep : List PStmt :=
  [.assign "dx" (rw rActAt), .assign "dl" (rw rActLen), keptIn (v "dl") maxFrame,
   keptIn (v "dx") (RecoverProg.size - maxFrame)] ++
  runJob [{ code := opCreate, name := n nameTail, number := rw rActA }] ++
  [mustSucceed, .assign "da" (result 0 0), .assign "dy" (result 0 1)] ++
  putLe jobBytes (rw rActB) 8 ++ copy "dj" (atOff jobBytes 8) (eAdd rp (v "dx")) (v "dl") ++
  runJob [{ code := opWrite, place := v "da", gen := v "dy", length := eAdd (v "dl") (n 8) },
          { code := opSync, place := v "da", gen := v "dy" },
          { code := opClose, place := v "da", gen := v "dy" }] ++ [mustSucceed]

/-- A new journal: made again over an empty one, or created; its format, under the configured
key, written and synced. -/
def create : List PStmt :=
  [.ite (ld (drv dJnlOpen))
     (runJob [{ onJournal opTruncate with length := n 0 }] ++ [mustSucceed])
     (runJob [{ code := opCreate, name := n nameJournal }] ++
      [mustSucceed, .store (drv dJnl) (result 0 0), .store (drv dJnlGen) (result 0 1),
       .store (drv dJnlOpen) (n 1)])] ++
  putBytes (atOff jobBytes headerLength) magic ++
  copy "dj" (atOff jobBytes (headerLength + magic.length)) (atOff rp rKey) (n keyLength) ++
  frameAround (n 0) formatType (magic.length + keyLength) (atOff rp rKey) ++
  runJob [{ onJournal opWrite with length := n firstFrame }, onJournal opSync] ++ [mustSucceed]

/-- The action recovery gives, carried out. -/
def give : List PStmt :=
  [.assign "da" (rw rAct),
   .ite (eEq (v "da") (n actKeep)) keep
    [.ite (eEq (v "da") (n actRename))
      (runJob [{ code := opRename, name := n nameFinal, number := rw rActA,
                 toName := n nameQuarantine, toNumber := rw rActA }] ++ [mustSucceed])
     [.ite (eEq (v "da") (n actRemove))
       (runJob [{ code := opRemove, name := rw rActB, number := rw rActA }] ++ [mustSucceed])
      [.ite (eEq (v "da") (n actSyncDir)) (runJob [{ code := opSyncDir }] ++ [mustSucceed])
       [.ite (eEq (v "da") (n actCut))
         (runJob [{ onJournal opTruncate with length := rw rActA }, onJournal opSync] ++
          [mustSucceed])
         [.ite (eEq (v "da") (n actCreate)) create (stop brokenState)]]]]]]

/-- The store recovered: a start record appended where the journal ends and synced, the listing
closed, and the host told to listen. -/
def finish : List PStmt :=
  [.ite (rw rFresh) [.assign "dx" (atOff rp rKey)]
    [.assign "dx" (atOff (v "jsc") ScanProg.sKey)]] ++
  frameAround (rw rJournalEnd) startType 0 (v "dx") ++
  runJob [{ onJournal opWrite with offset := rw rJournalEnd, length := n (headerLength + 1) },
          onJournal opDataSync] ++
  [mustSucceed,
   .ite (ld (drv dDirOpen))
     (runJob [{ code := opClose, place := ld (drv dDir), gen := ld (drv dDirGen) }] ++
      [mustSucceed, .store (drv dDirOpen) (n 0)]) [],
   .store (at_ (emitOff + emitListen)) (n 1), hand, fetch, .assign "dgo" (n 0)]

/-- What a step of recovery asks or gives, answered by file jobs. -/
def answer : List PStmt :=
  [.assign "dst" (rw rStatus),
   .ite (eEq (v "dst") (n asksName)) askName
    [.ite (eEq (v "dst") (n asksJournal)) askJournal
     [.ite (eEq (v "dst") (n asksOctets)) askOctets
      [.ite (eEq (v "dst") (n asksFile)) (askFile nameFinal true)
       [.ite (eEq (v "dst") (n asksAside)) (askFile nameQuarantine false)
        [.ite (eEq (v "dst") (n gives)) give
         [.ite (eEq (v "dst") (n givesAside))
           [.store (at_ (ownOff + ownAside)) (eAdd (ld (at_ (ownOff + ownAside))) (n 1))]
          [.ite (eEq (v "dst") (n RecoverProg.done)) finish
           [.ite (eEq (v "dst") (n refused)) (stop storeRefused) (stop brokenState)]]]]]]]]]

/-- **Recovery at start** (decision 0005), after the first batch: the configuration taken in, the
directory synced, and recovery's steps answered by file jobs until the store is recovered — the
host told to listen and the next batch fetched — or refused, the run stopped with the reason in
recovery's area. A word of the program's own area out of range stops it as anywhere else. -/
def recoverStore : List PStmt :=
  [.dec "jz" (n 0), .dec "rsc" (at_ recOff)] ++ RecoverProg.locals.map (.dec · (n 0)) ++
  ["dw", "dok", "dcl", "dst", "dx", "dy", "da", "dl", "dlen", "dpos", "dj", "dgo"].map
    (.dec · (n 0)) ++
  [.assign "jsc" (at_ (recOff + RecoverProg.rScan))] ++
  [.store (drv dDirOpen) (n 0), .store (drv dJnlOpen) (n 0), .store (drv dGen) (n 0),
   .store (drv dIndex) (n 0), .store (drv dPageLen) (n 0), .store (drv dPagePos) (n 0),
   .store (drv dClass) (n 0), .store (at_ (emitOff + emitCount)) (n 0),
   .store (at_ (emitOff + emitListen)) (n 0), rset rPhase (n 0)] ++
  configure ++ runJob [{ code := opSyncDir }] ++
  [mustSucceed, .assign "dgo" (n 1),
   .while (v "dgo") (callS "rs" "recoverStep" [] ++ answer)]

end Start

/-! ## The store -/

section Store
open DN.News.ArticleProg (xIdLen xId xRandLen xRand xRun xGroupsN xGroups groupSize)

/-- A hexadecimal digit, in lower case, of the nibble `d`. -/
def hexDigit (d : PExpr) : PExpr := eAdd (eAdd (n 48) d) (eMul (n 39) (eLt (n 9) d))

/-- The article's context from the first batch, before the batches recovery fetches: the path
identity, the run's value as Message-IDs carry it and as a number, and the groups, checked as the
store checks its configuration; and the key of the index. -/
def storeContext : List PStmt :=
  let aset (o : Nat) (e : PExpr) : PStmt := .store (at_ (artOff + o)) e
  [.dec "xil" (ld (at_ (nextOff + nextIdentityLen))),
   ifs (or2 (eLt (v "xil") (n 0)) (eLt (n identityMax) (v "xil"))) (stop badIdentity),
   aset xIdLen (v "xil")] ++
  copyNew "xij" (at_ (artOff + xId)) (at_ (nextOff + nextIdentity)) (v "xil") ++
  [.dec "xrn" (n 0), .dec "xrj" (n 0),
   .while (eLt (v "xrj") (n runValueLen))
     [.dec "xrb" (.loadb (eAdd (at_ (nextOff + nextRandom)) (v "xrj"))),
      .assign "xrn" (eOr (.shl (v "xrn") (n 8)) (v "xrb")),
      .storeb (eAdd (at_ (artOff + xRand)) (eMul (v "xrj") (n 2)))
        (hexDigit (.shr (v "xrb") (n 4))),
      .storeb (eAdd (at_ (artOff + xRand + 1)) (eMul (v "xrj") (n 2)))
        (hexDigit (eAnd (v "xrb") (n 15))),
      inc "xrj"],
   aset xRandLen (n (2 * runValueLen)), aset xRun (v "xrn"),
   .dec "xgc" (ld (at_ (nextOff + nextGroupCount))),
   ifs (or2 (eLt (v "xgc") (n 0)) (eLt (n groupsMax) (v "xgc"))) (stop badIdentity),
   aset xGroupsN (v "xgc"), .dec "xgk" (n 0),
   .while (eLt (v "xgk") (v "xgc"))
     ([.dec "xgs" (eAdd (at_ (nextOff + nextGroups)) (eMul (v "xgk") (n groupSlot))),
       .dec "xgt" (eAdd (at_ (artOff + xGroups)) (eMul (v "xgk") (n groupSize))),
       .dec "xgl" (ld (v "xgs")),
       ifs (or2 (eLt (v "xgl") (n 0)) (eLt (n groupMax) (v "xgl"))) (stop badIdentity),
       .store (v "xgt") (v "xgl")] ++
      copyNew "xgj" (atOff (v "xgt") 8) (atOff (v "xgs") 8) (v "xgl") ++ [inc "xgk"]),
   .call "xcx" "artContext" [],
   ifs (ld (at_ (artOff + News.AbnfProg.aBroken))) (stop brokenState),
   ifs (eEq (v "xcx") (n 0)) (stop badIdentity)] ++
  copyNew "xik" (at_ (ownOff + ownIndexKey))
    (at_ (nextOff + nextRandom + runValueLen + News.Journal.keyLength)) (n indexKeyLen)

/-- The store as recovery leaves it (`PostSpec.Store.start`): accepting, its next number, the
journal's end past the start record, its key; no slot in use, and the index of what it holds. -/
def storeStart : List PStmt :=
  let sset (o : Nat) (e : PExpr) : PStmt := .store (at_ (ownOff + o)) e
  let rw (o : Nat) : PExpr := ld (at_ (recOff + o))
  [sset ownStore (n 1), sset ownAccepting (n 1), sset ownNext (rw News.RecoverProg.rNext),
   sset ownJournalEnd (eAdd (rw News.RecoverProg.rJournalEnd) (n (News.Journal.headerLength + 1))),
   .dec "xkq" (at_ (recOff + News.RecoverProg.rScan + News.ScanProg.sKey)),
   ifs (rw News.RecoverProg.rFresh) [.assign "xkq" (at_ (recOff + News.RecoverProg.rKey))]] ++
  copyNew "xkj" (at_ (ownOff + ownKey)) (v "xkq") (n News.Journal.keyLength) ++
  ((List.range posts).map fun k => .store (at_ (slotsOff + k * slotLen + zLive)) (n 0)) ++
  ((List.range reads).map fun k => .store (at_ (readsOff + k * readLen + rLive)) (n 0)) ++
  callS "xib" "idBuild" []

end Store

/-! ## The session's functions -/

def textsSet : PFun := { name := "textsSet", body := textsInit ++ [.ret (n 0)] }

def identityTake : PFun := { name := "identityTake", body := identity ++ [.ret (n 0)] }

/-- Event `e` of the batch fetched at `now`. -/
def connEvent : PFun :=
  { name := "connEvent", params := [(1, "e"), (1, "now")],
    body := keptIn (v "e") (batch - 1) :: event ++ [.ret (n 0)] }

/-- The action of connection `c` at `now`, if it is in use. -/
def connAct : PFun :=
  { name := "connAct", params := [(1, "c"), (1, "now")], body :=
    [keptIn (v "c") (conns - 1), .store (atOff (actionAt (v "c")) actionKind) (n 0),
     .dec "cb" (record (v "c")), .ite (fld "cb" cLive) act [], .ret (n 0)] }

/-- What the host took of connection `sc`'s action at `now`. -/
def connSettle : PFun :=
  { name := "connSettle", params := [(1, "sc"), (1, "now")],
    body := keptIn (v "sc") (conns - 1) :: settle ++ [.ret (n 0)] }

def wakeAt : PFun := { name := "wakeAt", params := [(1, "now")], body := wake ++ [.ret (n 0)] }

def storeContextF : PFun := { name := "storeContext", body := storeContext ++ [.ret (n 0)] }

def storeStartF : PFun := { name := "storeStart", body := storeStart ++ [.ret (n 0)] }

/-- A step of recovery on its area (`RecoverProg.stepWith`). -/
def recoverStep : PFun :=
  { name := "recoverStep", body :=
    [.dec "jz" (n 0), .dec "rsc" (at_ recOff)] ++ News.RecoverProg.locals.map (.dec · (n 0)) ++
    News.RecoverProg.stepWith (stop brokenState) ++ [.ret (n 0)] }

/-- One turn of the loop, on the batch fetched before it: the events, the completions, each
connection's action, the slots' next jobs; the next batch is fetched at its end. -/
def turn : List PStmt :=
  [.dec "k" (ld (at_ (nextOff + nextCount))),
   .ite (or2 (eLt (v "k") (n 0)) (eLt (n batch) (v "k"))) (breach .tooManyEvents) [],
   .dec "now" (ld (at_ (nextOff + nextClock))),
   .dec "wl" (ld (at_ (nextOff + nextWall))),
   .ite (or2 (or2 (eLt (v "now") (ld (at_ (ownOff + ownClock)))) (eLe (n clockLimit) (v "now")))
      (or2 (eLt (v "wl") (n 0)) (eLe (n wallLimit) (v "wl")))) (breach .badClock) [],
   .store (at_ (ownOff + ownClock)) (v "now"),
   .call "wsec" "artDiv" [v "wl", n 1000],
   ifs (ld (at_ (artOff + News.AbnfProg.aBroken))) (stop brokenState),
   .store (at_ (ownOff + ownWall)) (v "wsec")] ++
  callS "it" "identityTake" [] ++
  [.dec "e" (n 0),
   .while (eLt (v "e") (v "k")) (callS "ce" "connEvent" [v "e", v "now"] ++ [inc "e"]),
   .dec "dj" (n 0),
   .while (eLt (v "dj") (n jobs))
     [ifs (ne (ld (eAdd (at_ (nextOff + nextDone + doneKind)) (eMul (v "dj") (n doneSlot)))) (n 0))
        [.ite hasStore (callS "dn" "postDone" [v "dj"]) (breach (.job .unknownJob))],
      inc "dj"],
   ifs hasStore (callS "ta" "postTidyAll" []),
   .store (at_ (ownOff + ownActs)) (n 0), .dec "c" (n 0),
   .while (eLt (v "c") (n conns)) (callS "ca" "connAct" [v "c", v "now"] ++ [inc "c"]),
   .dec "jc" (n 0),
   .while (eLt (v "jc") (n jobs))
     [.store (eAdd (at_ (emitOff + emitJobs + jobKind)) (eMul (v "jc") (n jobSlot))) (n 0),
      inc "jc"],
   ifs hasStore
     [.dec "pj" (n 0),
      .while (eLt (v "pj") (n posts)) (callS "pp" "postPlan" [v "pj"] ++ [inc "pj"]),
      .dec "rj" (n 0),
      .while (eLt (v "rj") (n reads)) (callS "rl" "readPlan" [v "rj"] ++ [inc "rj"])],
   .store (at_ (emitOff + emitCount)) (ownW ownActs),
   hand,
   .dec "sc" (n 0),
   .while (eLt (v "sc") (n conns)) (callS "cs" "connSettle" [v "sc", v "now"] ++ [inc "sc"])] ++
  callS "cw" "wakeAt" [v "now"] ++ [fetch]

/-- The functions: the grammar's and the article's, the store's, and the replies' texts. -/
def functions : List PFun :=
  (News.ArticleProg.program).1 ++ SessionStore.functions ++
    [connText, textsSet, identityTake, connEvent, connAct, connSettle, wakeAt, storeContextF,
     storeStartF, recoverStep]

/-- `main`: the version, no check of the article's failed, the tables and the texts, no store, an
empty table and no action or job, the first batch; then with a store, the article's context taken
in, the store recovered and started — else the host told to listen from the first turn — and the
loop. -/
def main : PFun :=
  { name := "main", body :=
    [.store (at_ confOff) (n version)] ++
    ([ownClock, ownReady, ownStop, ownStore, ownAccepting, ownOpened, ownWaitN, ownReadN,
      ownAside].map fun o => .store (at_ (ownOff + o)) (n 0)) ++
    [.store (at_ (artOff + News.AbnfProg.aBroken)) (n 0),
     .call "t1" "tables" [], .call "t2" "artTables" [], .call "t3" "crcTable" [],
     .call "t4" "textsSet" []] ++
    [.dec "zt" (n 0),
     .while (eLt (v "zt") (n conns))
       [.store (atOff (record (v "zt")) cLive) (n 0), .store (atOff (record (v "zt")) cActed) (n 0),
        .store (atOff (actionAt (v "zt")) actionKind) (n 0), inc "zt"]] ++
    (List.range jobs).map (fun k =>
      .store (at_ (emitOff + emitJobs + k * jobSlot + jobKind)) (n 0)) ++
    [.store (at_ (nextOff + nextWake)) (n 0), fetch,
     .ite (ld (at_ (nextOff + nextStore)))
       (callS "sx" "storeContext" [] ++ recoverStore ++ callS "sy" "storeStart" [])
       [.store (at_ (emitOff + emitListen)) (n 1)],
     .dec "going" (n 1),
     .while (v "going") turn,
     .ret (n 0)] }

/-- The source the gate prints. -/
def source : Except Checked.Reason String := Checked.emitProgram [nextName, emitName] functions main

def regression_824 : Bool := source.isOk

/-- The texts' places name the texts they stand for. -/
def regression_967 : Bool :=
  let i : News.CommandSpec.Identity := ⟨[], []⟩
  [(tGreetingPostHead, News.CommandSpec.greetingPostHead),
   (tGreetingPostMid, News.CommandSpec.greetingPostMid),
   (tCapabilitiesPostTail, News.CommandSpec.capabilitiesPostTail),
   (tHelpPostHead, News.CommandSpec.helpPostHead), (tPost, News.CommandSpec.text i .post),
   (tPosted, News.CommandSpec.text i .posted), (tFailed, News.CommandSpec.text i .failed),
   (tNotPermitted, News.CommandSpec.text i .notPermitted),
   (tUnavailable, News.CommandSpec.text i .unavailable),
   (tNames + 5, News.CommandSpec.ascii "POST"), (tArticle, News.CommandSpec.ascii "ARTICLE"),
   (tBody, News.CommandSpec.ascii "BODY"), (SessionStore.tStat, News.CommandSpec.ascii "223 "),
   (SessionStore.tUnreadable, News.CommandSpec.text i .unreadable),
   (SessionStore.tXref, News.CommandSpec.ascii "Xref: "),
   (SessionStore.tDot, News.CommandSpec.ascii ".\r\n"), (tGroup, News.CommandSpec.ascii "GROUP"),
   (tNext, News.CommandSpec.ascii "NEXT"), (tLast, News.CommandSpec.ascii "LAST"),
   (tSelected, News.CommandSpec.ascii "211 "), (tNoSuchGroup, News.CommandSpec.text i .noSuchGroup),
   (tNoCurrent, News.CommandSpec.text i .noCurrent), (tNoNext, News.CommandSpec.text i .noNext),
   (tNoPrevious, News.CommandSpec.text i .noPrevious),
   (tNoNumber, News.CommandSpec.text i .noNumber)].all (fun (k, t) => texts[k]? == some t) &&
  [(0, News.CommandSpec.Cmd.article), (1, .head), (2, .body)].all fun (j, c) =>
    (texts[SessionStore.tStatus + j]?).map
      (· ++ News.CommandSpec.decimal 0 ++ [News.CommandSpec.SP] ++ News.CommandSpec.crlf) ==
      some (News.CommandSpec.found c 0 [])

end DN.Server.Session
