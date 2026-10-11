-- SPDX-License-Identifier: AGPL-3.0-or-later
import DN.News.Recovery
import DN.News.ScanProg
import DN.Compiler.Analyzer

/-!
# DN.News.RecoverProg

Recovery at start (`DN.News.Recovery.recover`) as the gate prints it. A step runs until it needs
something of its caller — the next name of the directory, the journal's length, octets of the
journal for its scanner (`DN.News.ScanProg`), whether an article's final file is there and its size,
whether a name set aside is — or has something for it: an action, a number set aside, the store it
starts with, or why it does not start. Commits go into the index, a slot each. The configuration's
key is of sixteen octets, so `badKey` is never found. Tested against `dn-compiler recovery-model`,
not proven. As the scanner does, it checks each word it reads back before it makes an address of
it, and runs `fail` on one out of range.
-/

namespace DN.News.RecoverProg

open DN.Compiler DN.Compiler.Syntax
open DN.News.ScanProg (lit bytesAre leS inc ne or2 kept)
open DN.News.Journal (keyLength firstFrame commitType journalName)

/-! ## The area -/

/-- What a step asks or gives, its phase, a counter, whether it waits for a reply. -/
def rStatus : Nat := 0
def rPhase : Nat := 8
def rI : Nat := 16
def rWait : Nat := 24
/-- The directory, a name at a time: whether to start from its first (the step's), whether it has
no more (the caller's), and the name. -/
def rFirst : Nat := 32
def rEnd : Nat := 40
def rNameLen : Nat := 48
def rName : Nat := 56
def nameMax : Nat := 256
/-- A number asked about or given, and the caller's replies: whether a file is there, its size,
the journal's length. -/
def rSeq : Nat := rName + nameMax
def rFound : Nat := rSeq + 8
def rFileSize : Nat := rFound + 8
def rJournalSize : Nat := rFileSize + 8
/-- What the names showed: how many, whether the journal is among them, the highest number one
carries, whether a tail is kept and the highest it carries. -/
def rNames : Nat := rJournalSize + 8
def rJournal : Nat := rNames + 8
def rMaxSeq : Nat := rJournal + 8
def rTails : Nat := rMaxSeq + 8
def rMaxTail : Nat := rTails + 8
/-- What the journal showed: commits, records, the first group the configuration lacks, whether it
ends torn and where. Its first record is its format: the scanner reads none before. -/
def rCommits : Nat := rMaxTail + 8
def rRecords : Nat := rCommits + 8
def rUnknown : Nat := rRecords + 8
def rUnknownLen : Nat := rUnknown + 8
def rUnknownName : Nat := rUnknownLen + 8
def rTorn : Nat := rUnknownName + 64
def rCut : Nat := rTorn + 8
/-- The store it starts with: whether new, the next number before and after a torn tail, where
the journal ends; and how many names were tidied. -/
def rFresh : Nat := rCut + 8
def rNext0 : Nat := rFresh + 8
def rNext : Nat := rNext0 + 8
def rJournalEnd : Nat := rNext + 8
def rTidied : Nat := rJournalEnd + 8
/-- An action: its kind, a number, a second, and octets. -/
def rAct : Nat := rTidied + 8
def rActA : Nat := rAct + 8
def rActB : Nat := rActA + 8
def rActAt : Nat := rActB + 8
def rActLen : Nat := rActAt + 8
/-- Why the store does not start: the fault, a number, a second, and octets. -/
def rFault : Nat := rActLen + 8
def rFaultA : Nat := rFault + 8
def rFaultB : Nat := rFaultA + 8
def rFaultAt : Nat := rFaultB + 8
def rFaultLen : Nat := rFaultAt + 8
/-- The configuration: the key of a new journal and the groups, each a length and its name. -/
def rKey : Nat := rFaultLen + 8
def rGroupCount : Nat := rKey + keyLength
def rGroups : Nat := rGroupCount + 8
def groupsMax : Nat := 64
def groupNameMax : Nat := 64
def rGroupSlot : Nat := 8 + groupNameMax
/-- The highest article number the commits so far gave each group. -/
def rHigh : Nat := rGroups + groupsMax * rGroupSlot
def rScan : Nat := rHigh + groupsMax * 8
/-- The index: a slot for each commit, in the journal's order — its number, the header's size
above the file's, the CRC-32C above the Message-ID's length above the number of groups, each
group's index above its article number, and the Message-ID. -/
def rSlots : Nat := rScan + ScanProg.size
def slotSeq : Nat := 0
def slotSizes : Nat := 8
def slotMisc : Nat := 16
def slotGroups : Nat := 24
def slotId : Nat := slotGroups + ScanProg.groupsMax * 8
def slotSize : Nat := (slotId + 250 + 7) / 8 * 8
def size : Nat := rSlots + Recovery.capacity * slotSize

/-- What a step asks for, and what it gives. -/
def asksName : Nat := 1
def asksJournal : Nat := 2
def asksOctets : Nat := 3
def asksFile : Nat := 4
def asksAside : Nat := 5
def gives : Nat := 6
def givesAside : Nat := 7
def done : Nat := 8
def refused : Nat := 9

/-- Kinds of action, and of a name in one. -/
def actKeep : Nat := 1
def actRename : Nat := 2
def actRemove : Nat := 3
def actSyncDir : Nat := 4
def actCut : Nat := 5
def actCreate : Nat := 6
def nameFinal : Nat := 2
def nameTemp : Nat := 3

/-- The code of each fault. -/
def faultCode : Recovery.Fault → Nat
  | .badName _ => 1 | .noJournal => 2 | .journal _ _ => 3 | .seqTwice _ => 4
  | .numberNotAbove _ _ => 5 | .unknownGroup _ => 6 | .missingFile _ => 7 | .wrongSize _ => 8
  | .exhausted => 9 | .badKey => 10 | .tooMany _ => 11

/-! ## Statements -/

def rp : PExpr := v "rsc"
def rw (o : Nat) : PExpr := .loadw 1 (atOff rp o)
def rset (o : Nat) (e : PExpr) : PStmt := .store (atOff rp o) e
def sw (o : Nat) : PExpr := .loadw 1 (atOff (v "jsc") o)
def sset (o : Nat) (e : PExpr) : PStmt := .store (atOff (v "jsc") o) e
def top : Nat := 2 ^ 63
/-- `a` below `b`, as numbers of sixteen hexadecimal digits. -/
def ult (a b : PExpr) : PExpr := eLt (eXor a (n top)) (eXor b (n top))
/-- `x` raised to `e` if below it. -/
def raise (x : String) (e : PExpr) : PStmt := .ite (ult (v x) e) [.assign x e] []

/-- The step stops, asking or giving `code`. -/
def stop (code : Nat) : List PStmt := [rset rStatus (n code), .assign "rgo" (lit 0)]
/-- The step goes on in `phase`. -/
def next (phase : Nat) : PStmt := rset rPhase (n phase)
def refuse (f : Recovery.Fault) (fields : List PStmt) : List PStmt :=
  fields ++ [rset rFault (n (faultCode f))] ++ stop refused
def act (kind : Nat) (fields : List PStmt) : List PStmt :=
  rset rAct (n kind) :: fields ++ stop gives

/-- The word of group `g` of the slot at `rsl`. -/
def groupW (g : String) : PExpr := .loadw 1 (eAdd (atOff (v "rsl") slotGroups) (eMul (v g) (n 8)))

/-- How many commits the index holds, into `x`: more are refused, but no slot past it is ever
read. -/
def held (x : String) : List PStmt :=
  [.assign x (rw rCommits),
   .ite (eLt (n Recovery.capacity) (v x)) [.assign x (lit Recovery.capacity)] []]

/-- Slot `i`'s address, into `rsl`. -/
def slotOf (i : PExpr) : PStmt := .assign "rsl" (eAdd (atOff rp rSlots) (eMul i (n slotSize)))
def slotW (o : Nat) : PExpr := .loadw 1 (atOff (v "rsl") o)

/-- The name at `rName`: its kind into `rk` — 1 the journal, 2 to 5 a final, temporary,
quarantine or tail name, 0 none the store gives — and its number into `rv`. -/
def classify : List PStmt :=
  [.assign "rk" (lit 0), .assign "rl" (rw rNameLen), .assign "rq" (atOff rp rName),
   .ite (eAnd (eEq (v "rl") (n journalName.length)) (bytesAre (v "rq") journalName))
     [.assign "rk" (lit 1)]
     [.ite (eEq (v "rl") (n 17))
       [.assign "rc" (.loadb (v "rq")), .assign "rlet" (lit 0),
        .ite (eEq (v "rc") (n 97)) [.assign "rlet" (lit 2)] [],
        .ite (eEq (v "rc") (n 116)) [.assign "rlet" (lit 3)] [],
        .ite (eEq (v "rc") (n 113)) [.assign "rlet" (lit 4)] [],
        .ite (eEq (v "rc") (n 106)) [.assign "rlet" (lit 5)] [],
        .assign "rv" (lit 0), .assign "rok" (lit 1), .assign "rj" (lit 1),
        .while (eLt (v "rj") (n 17))
          [.assign "rc" (.loadb (eAdd (v "rq") (v "rj"))),
           .ite (eAnd (eLe (n 48) (v "rc")) (eLe (v "rc") (n 57)))
             [.assign "rv" (eOr (.shl (v "rv") (n 4)) (eSub (v "rc") (n 48)))]
             [.ite (eAnd (eLe (n 97) (v "rc")) (eLe (v "rc") (n 102)))
               [.assign "rv" (eOr (.shl (v "rv") (n 4)) (eSub (v "rc") (n 87)))]
               [.assign "rok" (lit 0)]],
           inc "rj"],
        .ite (v "rok") [.assign "rk" (v "rlet")] []] []]]

/-- Phase 0: the first name asked for. -/
def begin : List PStmt :=
  [rset rNames (n 0), rset rJournal (n 0), rset rMaxSeq (n 0), rset rTails (n 0),
   rset rMaxTail (n 0), rset rCommits (n 0), rset rRecords (n 0), rset rUnknown (n 0),
   rset rTorn (n 0), rset rFresh (n 0), rset rTidied (n 0), rset rWait (n 0), rset rFirst (n 1),
   next 1] ++ stop asksName

/-- A new journal, and the directory synced when it held no file at all. -/
def fresh (synced : Bool) : List PStmt :=
  [rset rFresh (n 1), rset rNext (n 1), rset rJournalEnd (n firstFrame), rset rI (n 0),
   rset rWait (n (if synced then 1 else 0)), next 10]

/-- Phase 1: a name of the first pass, or none left. -/
def firstPass : List PStmt :=
  [.ite (rw rEnd)
    [.ite (rw rJournal) ([next 2] ++ stop asksJournal)
      [.ite (eEq (rw rNames) (n 0)) (fresh true) (refuse .noJournal [])]]
    (classify ++
     [.ite (eEq (v "rk") (n 0)) (refuse (.badName []) [])
       ([rset rNames (eAdd (rw rNames) (n 1)),
         .ite (eEq (v "rk") (n 1)) [rset rJournal (n 1)]
           [.assign "rm" (rw rMaxSeq), raise "rm" (v "rv"), rset rMaxSeq (v "rm"),
            .ite (eEq (v "rk") (n 5))
              [rset rTails (n 1), .assign "rm" (rw rMaxTail), raise "rm" (v "rv"),
               rset rMaxTail (v "rm")] []],
         rset rFirst (n 0)] ++ stop asksName)])]

/-- Phase 2: the journal's length given, the scanner set to read it. -/
def journalGiven : List PStmt :=
  [sset ScanProg.sSize (rw rJournalSize), sset ScanProg.sBase (n 0), sset ScanProg.sLen (n 0),
   sset ScanProg.sPos (n 0), sset ScanProg.sKeyed (n 0), sset ScanProg.sCount (n 0), next 3]

section
variable (fail : List PStmt)

/-- A commit read: into its slot while there is one, its groups by their index in the
configuration, and the first group the configuration lacks noted. -/
def commitRead : List PStmt :=
  [.assign "rcm" (eAdd (rw rCommits) (n 1)), rset rCommits (v "rcm"),
   .ite (eAnd (eLt (n 0) (v "rcm")) (eLe (v "rcm") (n Recovery.capacity)))
     ([slotOf (eSub (v "rcm") (n 1)), .store (v "rsl") (sw ScanProg.sSeq),
       .store (atOff (v "rsl") slotSizes)
         (eOr (.shl (sw ScanProg.sHeader) (n 32)) (sw ScanProg.sFileSize)),
       .assign "rgc" (sw ScanProg.sGroupCount), kept fail "rgc" ScanProg.groupsMax,
       .assign "ril" (sw ScanProg.sIdLen), kept fail "ril" 250,
       .assign "rio" (sw ScanProg.sIdAt), kept fail "rio" ScanProg.windowRoom,
       .assign "rwp" (atOff (v "jsc") ScanProg.sWindow),
       .store (atOff (v "rsl") slotMisc) (eOr (eOr (.shl (sw ScanProg.sCrc) (n 16))
         (.shl (v "ril") (n 8))) (v "rgc")),
       .assign "rj" (lit 0),
       .while (eLt (v "rj") (v "ril"))
         [.storeb (eAdd (atOff (v "rsl") slotId) (v "rj"))
            (.loadb (eAdd (eAdd (v "rwp") (v "rio")) (v "rj"))), inc "rj"],
       .assign "rg" (lit 0),
       .while (eLt (v "rg") (v "rgc"))
         [.assign "rgs" (eAdd (atOff (v "jsc") ScanProg.sGroups)
            (eMul (v "rg") (n ScanProg.groupSlot))),
          .assign "rga" (.loadw 1 (v "rgs")), kept fail "rga" ScanProg.windowRoom,
          .assign "rgl" (.loadw 1 (atOff (v "rgs") 8)), kept fail "rgl" groupNameMax,
          .assign "rx" (lit groupsMax), .assign "rc" (lit 0), .assign "rgn" (rw rGroupCount),
          .ite (eLt (n groupsMax) (v "rgn")) [.assign "rgn" (lit groupsMax)] [],
          .while (eLt (v "rc") (v "rgn"))
            [.assign "rcp" (eAdd (atOff rp rGroups) (eMul (v "rc") (n rGroupSlot))),
             .ite (eEq (.loadw 1 (v "rcp")) (v "rgl"))
               [.assign "rok" (lit 1), .assign "rj" (lit 0),
                .while (eLt (v "rj") (v "rgl"))
                  [.ite (ne (.loadb (eAdd (atOff (v "rcp") 8) (v "rj")))
                      (.loadb (eAdd (eAdd (v "rwp") (v "rga")) (v "rj"))))
                    [.assign "rok" (lit 0)] [],
                   inc "rj"],
                .ite (v "rok") [.assign "rx" (v "rc")] []] [],
             inc "rc"],
          .ite (eEq (v "rx") (n groupsMax))
            [.ite (rw rUnknown) []
              [rset rUnknown (n 1), rset rUnknownLen (v "rgl"), .assign "rj" (lit 0),
               .while (eLt (v "rj") (v "rgl"))
                 [.storeb (eAdd (atOff rp rUnknownName) (v "rj"))
                    (.loadb (eAdd (eAdd (v "rwp") (v "rga")) (v "rj"))), inc "rj"]]] [],
          .store (eAdd (atOff (v "rsl") slotGroups) (eMul (v "rg") (n 8)))
            (eOr (.shl (v "rx") (n 32)) (.loadw 1 (atOff (v "rgs") 16))),
          inc "rg"]]) []]

/-- Phase 3: the scanner run until it wants octets or the journal ends. -/
def scanning : List PStmt :=
  ScanProg.stepWith fail ++
  [.assign "rst" (sw ScanProg.sStatus),
   .ite (eEq (v "rst") (n ScanProg.wanted)) (stop asksOctets)
     [.ite (eEq (v "rst") (n ScanProg.record))
       [rset rRecords (eAdd (rw rRecords) (n 1)),
        .ite (eEq (sw ScanProg.sType) (n commitType)) (commitRead fail) []]
       [.ite (eEq (v "rst") (n ScanProg.corrupt))
         (refuse (.journal 0 .short) [rset rFaultA (sw ScanProg.sPos),
           rset rFaultB (sw ScanProg.sWhy)])
         [.ite (eEq (rw rRecords) (n 0))
           [.ite (eEq (rw rNames) (n 1)) (fresh false) (refuse .noJournal [])]
           [rset rJournalEnd (sw ScanProg.sSize),
            .ite (eEq (v "rst") (n ScanProg.torn))
              [rset rTorn (n 1), rset rCut (sw ScanProg.sPos),
               rset rJournalEnd (sw ScanProg.sPos)] [],
            next 4]]]]]

/-- Phase 4: the rules across records, in the specification's order. -/
def rules : List PStmt :=
  [.assign "rcm" (rw rCommits),
   .ite (eLe (n (Recovery.capacity + 1)) (v "rcm"))
     (refuse (.tooMany 0) [rset rFaultA (v "rcm")])
     (held "rcm" ++ [.assign "rdup" (lit 0), .assign "ri" (lit 0),
      .while (eAnd (eEq (v "rdup") (n 0)) (eLt (v "ri") (v "rcm")))
        [slotOf (v "ri"), .assign "rv" (slotW slotSeq), .assign "rj" (eAdd (v "ri") (n 1)),
         .while (eLt (v "rj") (v "rcm"))
           [slotOf (v "rj"), .ite (eEq (slotW slotSeq) (v "rv")) [.assign "rdup" (lit 1)] [],
            inc "rj"],
         .ite (v "rdup") [] [inc "ri"]],
      .ite (v "rdup") (refuse (.seqTwice 0) [rset rFaultA (v "rv")])
        [.ite (eEq (rw rUnknown) (n 1))
          (refuse (.unknownGroup []) [rset rFaultAt (atOff rp rUnknownName),
            rset rFaultLen (rw rUnknownLen)])
          [.assign "rc" (lit 0),
           .while (eLt (v "rc") (n groupsMax))
             [.store (eAdd (atOff rp rHigh) (eMul (v "rc") (n 8))) (n 0), inc "rc"],
           .assign "rbad" (lit 0), .assign "ri" (lit 0),
           .while (eAnd (eEq (v "rbad") (n 0)) (eLt (v "ri") (v "rcm")))
             [slotOf (v "ri"), .assign "rgc" (eAnd (slotW slotMisc) (n 255)),
              kept fail "rgc" ScanProg.groupsMax,
              .assign "rg" (lit 0),
              .while (eAnd (eEq (v "rbad") (n 0)) (eLt (v "rg") (v "rgc")))
                [.assign "rx" (groupW "rg"),
                 .assign "rc" (eAdd (v "jz") (.shr (v "rx") (n 32))),
                 kept fail "rc" (groupsMax - 1),
                 .assign "rv" (eAnd (v "rx") (n (2 ^ 32 - 1))),
                 .ite (eLe (v "rv") (.loadw 1 (eAdd (atOff rp rHigh) (eMul (v "rc") (n 8)))))
                   [.assign "rbad" (lit 1)] [inc "rg"]],
              .ite (v "rbad") []
                [.assign "rg" (lit 0),
                 .while (eLt (v "rg") (v "rgc"))
                   [.assign "rx" (groupW "rg"),
                    .assign "rc" (eAdd (v "jz") (.shr (v "rx") (n 32))),
                 kept fail "rc" (groupsMax - 1),
                    .store (eAdd (atOff rp rHigh) (eMul (v "rc") (n 8)))
                      (eAnd (v "rx") (n (2 ^ 32 - 1))), inc "rg"],
                 inc "ri"]],
           .ite (v "rbad")
             (refuse (.numberNotAbove [] 0) [rset rFaultA (v "rv"),
               rset rFaultAt (eAdd (atOff rp (rGroups + 8)) (eMul (v "rc") (n rGroupSlot))),
               rset rFaultLen (.loadw 1 (eAdd (atOff rp rGroups) (eMul (v "rc") (n rGroupSlot))))])
             [rset rI (n 0), rset rWait (n 0), next 5]]]])]

/-- Phase 5: each commit's final file, there and of its size, in the journal's order. -/
def files : List PStmt :=
  [.assign "ri" (rw rI), kept fail "ri" Recovery.capacity] ++ held "rcm" ++
  [.ite (rw rWait)
     [kept fail "ri" (Recovery.capacity - 1), slotOf (v "ri"), rset rWait (n 0),
      .ite (eEq (rw rFound) (n 0)) (refuse (.missingFile 0) [rset rFaultA (slotW slotSeq)])
        [.ite (ne (rw rFileSize) (eAnd (slotW slotSizes) (n (2 ^ 32 - 1))))
          (refuse (.wrongSize 0) [rset rFaultA (slotW slotSeq)])
          [rset rI (eAdd (v "ri") (n 1))]]]
     [.ite (eLt (v "ri") (v "rcm"))
       ([slotOf (v "ri"), rset rSeq (slotW slotSeq), rset rWait (n 1)] ++ stop asksFile)
       [next 6]]]

/-- Phase 6: the next sequence number, while numbers last. -/
def numbered : List PStmt :=
  held "rcm" ++
  [.assign "rm" (rw rMaxSeq), .assign "ri" (lit 0),
   .while (eLt (v "ri") (v "rcm")) [slotOf (v "ri"), raise "rm" (slotW slotSeq), inc "ri"],
   .ite (or2 (eEq (v "rm") (n (2 ^ 64 - 1))) (eAnd (rw rTorn) (eEq (v "rm") (n (2 ^ 64 - 2)))))
     (refuse .exhausted [])
     [rset rNext0 (eAdd (v "rm") (n 1)), rset rNext (eAdd (eAdd (v "rm") (n 1)) (rw rTorn)),
      rset rI (n 0), next 7]]

/-- Phase 7: a torn tail kept under the next number, the directory synced, the journal cut; then
the first name of the second pass asked for. -/
def tail : List PStmt :=
  [.assign "ri" (rw rI),
   .ite (or2 (eEq (rw rTorn) (n 0)) (eEq (v "ri") (n 3)))
     ([rset rFirst (n 1), next 8] ++ stop asksName)
     [rset rI (eAdd (v "ri") (n 1)),
      .ite (eEq (v "ri") (n 0))
        (act actKeep [rset rActA (rw rNext0), rset rActB (rw rCut),
          rset rActAt (eAdd (atOff (v "jsc") ScanProg.sWindow)
            (eSub (rw rCut) (sw ScanProg.sBase))),
          rset rActLen (eSub (sw ScanProg.sSize) (rw rCut))])
        [.ite (eEq (v "ri") (n 1)) (act actSyncDir []) (act actCut [rset rActA (rw rCut)])]]]

/-- Whether final file `rv` has a commit: into `rok`. -/
def recorded : List PStmt :=
  held "rcm" ++
  [.assign "rok" (lit 0), .assign "ri" (lit 0),
   .while (eAnd (eEq (v "rok") (n 0)) (eLt (v "ri") (v "rcm")))
     [slotOf (v "ri"), .ite (eEq (slotW slotSeq) (v "rv")) [.assign "rok" (lit 1)] [], inc "ri"]]

/-- Phase 8: a name of the second pass: a temporary file removed; a final file no commit names
set aside, or removed when set aside already or not to be; a name set aside counted. -/
def secondPass : List PStmt :=
  [.ite (rw rEnd) [rset rI (n 0), next 11]
    (classify ++ [rset rFirst (n 0), rset rSeq (v "rv"),
     .ite (eEq (v "rk") (n 3))
       (act actRemove [rset rActA (v "rv"), rset rActB (n nameTemp),
         rset rTidied (eAdd (rw rTidied) (n 1)), next 13])
       [.ite (eEq (v "rk") (n 2))
         (recorded ++
          [.ite (v "rok") (stop asksName)
            [.ite (or2 (rw rTorn) (eAnd (rw rTails) (ult (v "rv") (rw rMaxTail))))
              ([next 9] ++ stop asksAside)
              (act actRemove [rset rActA (v "rv"), rset rActB (n nameFinal),
                rset rTidied (eAdd (rw rTidied) (n 1)), next 13])]])
         [.ite (eLt (n 3) (v "rk")) ([rset rActA (v "rv"), next 13] ++ stop givesAside)
           (stop asksName)]]])]

/-- Phase 9: whether the name a final file is set aside under holds one already. -/
def asideGiven : List PStmt :=
  [rset rTidied (eAdd (rw rTidied) (n 1)), rset rActA (rw rSeq),
   .ite (rw rFound) ([rset rActB (n nameFinal), next 13] ++ act actRemove [])
     ([next 12] ++ act actRename [])]

/-- Phase 12: the number of a final file just set aside. -/
def renamed : List PStmt := [rset rActA (rw rSeq), next 13] ++ stop givesAside

/-- Phase 13: the next name of the second pass asked for, once one was answered. -/
def askNext : List PStmt := [rset rFirst (n 0), next 8] ++ stop asksName

/-- Phase 11: the directory synced after names are tidied, the torn tail's number set aside, and
the store recovery starts with. -/
def finish : List PStmt :=
  [.assign "ri" (rw rI), rset rI (eAdd (v "ri") (n 1)),
   .ite (eAnd (eEq (v "ri") (n 0)) (eLt (n 0) (rw rTidied))) (act actSyncDir [])
     [.ite (eAnd (eLe (v "ri") (n 1)) (rw rTorn))
       ([rset rI (n 2), rset rActA (rw rNext0)] ++ stop givesAside) (stop done)]]

/-- Phase 10: a new journal created, and the directory synced if it held no file. -/
def created : List PStmt :=
  [.assign "ri" (rw rI), rset rI (eAdd (v "ri") (n 1)),
   .ite (eEq (v "ri") (n 0)) (act actCreate [])
     [.ite (eAnd (eEq (v "ri") (n 1)) (rw rWait)) (act actSyncDir []) (stop done)]]

/-- **One step**: the phases until one asks or gives. A name asked for arrives in phase 1 or 8,
the step that asked having left the phase there. -/
def stepWith : List PStmt :=
  [.assign "jsc" (atOff rp rScan), .assign "rgo" (lit 1),
   .while (v "rgo")
     [.assign "rph" (rw rPhase),
      .ite (eEq (v "rph") (n 0)) begin
       [.ite (eEq (v "rph") (n 1)) firstPass
        [.ite (eEq (v "rph") (n 2)) journalGiven
         [.ite (eEq (v "rph") (n 3)) (scanning fail)
          [.ite (eEq (v "rph") (n 4)) (rules fail)
           [.ite (eEq (v "rph") (n 5)) (files fail)
            [.ite (eEq (v "rph") (n 6)) numbered
             [.ite (eEq (v "rph") (n 7)) tail
              [.ite (eEq (v "rph") (n 8)) secondPass
               [.ite (eEq (v "rph") (n 9)) asideGiven
                [.ite (eEq (v "rph") (n 10)) created
                 [.ite (eEq (v "rph") (n 11)) finish
                  [.ite (eEq (v "rph") (n 12)) renamed askNext]]]]]]]]]]]]]]

end

/-- One step, ending with `ScanProg.broken` on a word out of range. -/
def stepSrc : List PStmt := stepWith [.ret (n ScanProg.broken)]

/-- The step's locals, its own and the scanner's. -/
def locals : List String :=
  ["rgo", "rph", "rk", "rl", "rq", "rc", "rlet", "rv", "rok", "rj", "rm", "rcm", "rsl", "rgc",
   "rgn", "rg", "rgs", "rga", "rgl", "rx", "rcp", "rst", "rdup", "ri", "rbad", "ril", "rio", "rwp",
   "jsc"] ++
  ScanProg.locals

/-- One step on the area at `rsc`, its status returned. -/
def recoverKernel : PFun :=
  { name := "dn_recover_step", exported := true, params := [(1, "rsc")],
    body := .dec "jz" (eSub rp rp) :: locals.map (.dec · (v "jz")) ++ stepSrc ++
      [.ret (rw rStatus)] }

/-- Where the analysis takes the area to lie: above the heap's header. -/
def analysisAt : Nat := 64

/-- The step run in a whole program's loop, its area at `@base + analysisAt` and its caller an
external call that may write all of it, `fail` run on a word out of range: what the analysis of
decision 0004 is run on. -/
def analysisWith (fail : List PStmt) : PFun :=
  { name := "main", body :=
    [.dec "jz" (n 0), .dec "rsc" (atOff .base analysisAt)] ++ locals.map (.dec · (n 0)) ++
    [.while (n 1) (stepWith fail ++ [.ffi "dn_next" [rp, n 8, rp, n size]]), .ret (n 0)] }

def analysisMain : PFun := analysisWith [.ret (n 1)]

/-- Whether the analysis accepts the program, its heap reaching to the area's end. -/
def accepted (f : PFun) : Bool :=
  match Lower.lower f with
  | some p => (Analyzer.check (analysisAt + size) p).toBool
  | none => false

/-- The analysis accepts the step, and refuses it when a word out of range goes on as one in it. -/
def regression_945 (_ : Unit) : Bool := accepted analysisMain && !accepted (analysisWith [])

/-- The area as a C header for the test's host. -/
def header : String :=
  let defs : List (String × Nat) :=
    [("STATUS", rStatus), ("FIRST", rFirst), ("END", rEnd), ("NAME_LEN", rNameLen),
     ("NAME", rName), ("NAME_MAX", nameMax), ("SEQ", rSeq), ("FOUND", rFound),
     ("FILE_SIZE", rFileSize), ("JOURNAL_SIZE", rJournalSize), ("COMMITS", rCommits),
     ("FRESH", rFresh), ("NEXT", rNext), ("JOURNAL_END", rJournalEnd), ("ACT", rAct),
     ("ACT_A", rActA), ("ACT_B", rActB), ("ACT_AT", rActAt), ("ACT_LEN", rActLen),
     ("FAULT", rFault), ("FAULT_A", rFaultA), ("FAULT_B", rFaultB), ("FAULT_AT", rFaultAt),
     ("FAULT_LEN", rFaultLen), ("KEY", rKey), ("GROUP_COUNT", rGroupCount), ("GROUPS", rGroups),
     ("GROUP_SLOT", rGroupSlot), ("GROUPS_MAX", groupsMax), ("SCAN", rScan), ("SLOTS", rSlots),
     ("SLOT_SIZE", slotSize), ("SLOT_SEQ", slotSeq), ("SLOT_SIZES", slotSizes),
     ("SLOT_MISC", slotMisc), ("SLOT_GROUPS", slotGroups), ("SLOT_ID", slotId), ("AREA", size),
     ("CAPACITY", Recovery.capacity),
     ("ASKS_NAME", asksName), ("ASKS_JOURNAL", asksJournal), ("ASKS_OCTETS", asksOctets),
     ("ASKS_FILE", asksFile), ("ASKS_ASIDE", asksAside), ("GIVES", gives),
     ("GIVES_ASIDE", givesAside), ("DONE", done), ("REFUSED", refused), ("KEEP", actKeep),
     ("RENAME", actRename), ("REMOVE", actRemove), ("SYNC_DIR", actSyncDir), ("CUT", actCut),
     ("CREATE", actCreate), ("NAME_FINAL", nameFinal), ("NAME_TEMP", nameTemp)]
  "/* Generated by dn-compiler emit-recover-layout from DN.News.RecoverProg. */\n" ++
  "#ifndef DN_RECOVER_LAYOUT_H\n#define DN_RECOVER_LAYOUT_H\n" ++
  String.join (defs.map fun (name, value) => s!"#define DN_RECOVER_{name} {value}\n") ++
  "#endif\n"

def regression_939 : Bool := (Checked.emit recoverKernel).isOk

end DN.News.RecoverProg
