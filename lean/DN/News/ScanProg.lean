-- SPDX-License-Identifier: AGPL-3.0-or-later
import DN.News.Journal
import DN.News.SipProg

/-!
# DN.News.ScanProg

The journal read back as `DN.News.Journal.scan` reads it, as the gate prints it. A step reads one frame from a
caller-filled window, leaving octets wanted, a record, or the journal's end. Proven if it goes on: the step is
`ScanSpec.stepSpec`, and its steps read the journal as `scan` does.
-/

namespace DN.News.ScanProg

open DN.Compiler DN.Compiler.Syntax
open DN.News.Journal (headerLength maxPayload maxFrame firstFrame magic journalTitle keyLength
  formatType commitType startType)

/-! ## The scanner's area -/

/-- Words the caller sets before the first step: the journal's length; and the step keeps the
others: where the window starts in the journal, how many octets it holds, where the next frame
starts, whether the format's key is read, how many records were read. -/
def sSize : Nat := 0
def sBase : Nat := 8
def sLen : Nat := 16
def sPos : Nat := 24
def sKeyed : Nat := 32
def sCount : Nat := 40
/-- What a step found, why the journal is corrupt, and how many octets it wants. -/
def sStatus : Nat := 48
def sWhy : Nat := 56
def sWant : Nat := 64
/-- A record: its type, and of a commit its sequence number, where its Message-ID lies in the window
and its length, how many groups, the header's and the file's sizes, the CRC-32C, then for each group
where its name lies in the window, its length and the article number. -/
def sType : Nat := 72
def sSeq : Nat := 80
def sIdAt : Nat := 88
def sIdLen : Nat := 96
def sGroupCount : Nat := 104
def sHeader : Nat := 112
def sFileSize : Nat := 120
def sCrc : Nat := 128
def sGroups : Nat := 136
def groupSlot : Nat := 24
def groupsMax : Nat := 16
/-- The journal's key, the message a tag is computed over, and the window. -/
def sKey : Nat := sGroups + groupsMax * groupSlot
def sMessage : Nat := sKey + keyLength
def messageMax : Nat := 8 + 1 + maxPayload
def sWindow : Nat := sMessage + (messageMax + 7) / 8 * 8
/-- What one read adds to the window at most. -/
def chunk : Nat := 16384
def windowMax : Nat := (maxFrame + chunk + 7) / 8 * 8
/-- The window, and a frame's room past it, which a frame read where the window ends may reach. -/
def windowRoom : Nat := windowMax + (maxFrame + 7) / 8 * 8
def size : Nat := sWindow + windowRoom

/-- What a step found. -/
def wanted : Nat := 1
def record : Nat := 2
def clean : Nat := 3
def torn : Nat := 4
def corrupt : Nat := 5

/-- Why the journal is corrupt, as `DN.News.Journal.Why` lists it. -/
def whyCode : DN.News.Journal.Why → Nat
  | .short => 1 | .tooLong => 2 | .unterminated => 3 | .tag => 4 | .notARecord => 5
  | .formatAgain => 6

/-! ## Statements -/

def sp : PExpr := v "jsc"
def word (o : Nat) : PExpr := .loadw 1 (atOff sp o)
def setw (o : Nat) (e : PExpr) : PStmt := .store (atOff sp o) e
def byte (a : PExpr) : PExpr := .loadb a
def ne (a b : PExpr) : PExpr := eEq (eEq a b) (n 0)
/-- Either of two flags, each zero or one. -/
def or2 (a b : PExpr) : PExpr := eLt (n 0) (eAdd a b)
def inc (x : String) : PStmt := .assign x (eAdd (v x) (n 1))
/-- A number given to a local, made from `jz`, a zero of the area's address: CakeML's static
checker (`DN.Compiler.StaticCheck`) then sees each local of one kind wherever it is set, and every
address made from one as made from the area's. -/
def lit (k : Nat) : PExpr := eAdd (v "jz") (n k)

/-- The `k` octets at `p`, least significant first, as a number into `x`. -/
def leS (x : String) (p : PExpr) (k : Nat) : List PStmt :=
  .assign x (n 0) :: (List.range k).reverse.map fun i =>
    .assign x (eOr (.shl (v x) (n 8)) (byte (atOff p i)))

/-- Whether the octets at `p` are `bs`: one when each is. -/
def bytesAre (p : PExpr) (bs : List (BitVec 8)) : PExpr :=
  (bs.zipIdx.map fun (b, i) => eEq (byte (atOff p i)) (n b.toNat)).foldl eAnd (n 1)

section
variable (fail : List PStmt)

/-- `fail` unless the local `x` lies in `[0, hi]`, as the step keeps the word it read it from. -/
def kept (x : String) (hi : Nat) : PStmt := .ite (or2 (eLt (v x) (n 0)) (eLt (n hi) (v x))) fail []

/-- The key a frame is checked under, into `k`, and whether there is one into `jhk`: with `keyed`,
the journal's; else the journal's once read, or the key a frame of the format's shape carries. -/
def keySel : Bool → List PStmt
  | true => [.assign "k" (atOff sp sKey), .assign "jhk" (lit 1)]
  | false =>
    [.assign "k" (atOff sp sKey), .assign "jhk" (v "jky"),
     .ite (v "jky") []
       [.ite (eAnd (eEq (v "jt") (n formatType)) (eEq (v "jpl") (n (magic.length + keyLength))))
         [.ite (bytesAre (atOff (v "jf") headerLength) journalTitle)
           [.assign "k" (atOff (v "jf") (headerLength + magic.length)), .assign "jhk" (lit 1)]
           []] []]]

/-- The message a frame's tag is computed over — its offset in eight octets, its type and its
payload — at `p`, and its length into `n`. -/
def message : List PStmt :=
  [.assign "p" (atOff sp sMessage)] ++
  (List.range 8).map (fun i =>
    .storeb (atOff (v "p") i) (eAnd (.shr (v "jq") (n (8 * i))) (n 255))) ++
  [.storeb (atOff (v "p") 8) (v "jt"), .assign "ji" (lit 0),
   .while (eLt (v "ji") (v "jpl"))
     [.storeb (eAdd (atOff (v "p") 9) (v "ji"))
        (byte (eAdd (atOff (v "jf") headerLength) (v "ji"))),
      inc "ji"],
   .assign "n" (eAdd (v "jpl") (n 9))]

/-- The tag, once there is a key: SipHash-2-4 over the message, against the frame's. -/
def tagPart : List PStmt :=
  [.ite (eEq (v "jhk") (n 0)) [.assign "jwhy" (lit (whyCode .tag))]
    (message ++ SipProg.sipSrc ++ leS "jtag" (atOff (v "jf") 4) 8 ++
      [.ite (ne (v "r") (v "jtag")) [.assign "jwhy" (lit (whyCode .tag))] []])]

/-- The type and the key, then the tag. -/
def markPart (keyed : Bool) : List PStmt := [.assign "jt" (byte (atOff (v "jf") 12))] ++ keySel keyed ++ tagPart

/-- The end mark, then the rest. -/
def endPart (keyed : Bool) : List PStmt :=
  [.ite (ne (byte (eAdd (v "jf") (eAdd (v "jpl") (n headerLength)))) (n 0xA5))
    [.assign "jwhy" (lit (whyCode .unterminated))] (markPart keyed)]

/-- The octets the length says, then the rest. -/
def cutPart (keyed : Bool) : List PStmt :=
  [.ite (eLt (v "jr") (eAdd (v "jpl") (n (headerLength + 1)))) [.assign "jwhy" (lit (whyCode .short))]
    (endPart keyed)]

/-- A length any payload may have, then the rest. A length below zero cannot come from four octets; refusing it as too
long lets the analysis see the bound. -/
def longPart (keyed : Bool) : List PStmt :=
  [.ite (or2 (eLt (n maxPayload) (v "jpl")) (eLt (v "jpl") (n 0))) [.assign "jwhy" (lit (whyCode .tooLong))]
    (cutPart keyed)]

/-- Why the frame at journal offset `jq`, at `jf` in the window, `jr` octets left, does not check. The code goes into
`jwhy`, zero if it does; its payload's length into `jpl`, its type into `jt`. -/
def frameWhy (keyed : Bool) : List PStmt :=
  [.assign "jwhy" (lit 0),
   .ite (eLt (v "jr") (n headerLength)) [.assign "jwhy" (lit (whyCode .short))]
     (leS "jpl" (v "jf") 4 ++ longPart keyed)]

/-- Group `g`'s slot in the area. -/
def slot (g : String) : PExpr := eAdd (atOff sp sGroups) (eMul (v g) (n groupSlot))

/-- Where octet `i` of the payload lies in the window. -/
def inWindow (i : PExpr) : PExpr := eAdd (eAdd (v "jo") (n headerLength)) i

/-- Octet `jx` of the two names, compared. -/
def alikeOctet : List PStmt :=
  [.ite (ne (byte (eAdd (eAdd (v "jw") (v "jna")) (v "jx"))) (byte (eAdd (eAdd (v "jw") (v "jnb")) (v "jx"))))
     [.assign "jeq" (lit 0)] [],
   inc "jx"]

/-- Whether the names of groups `ja` and `jbb` are alike, into `jeq`. -/
def namesAlike : List PStmt :=
  [.assign "jga" (slot "ja"), .assign "jgb" (slot "jbb"), .assign "jeq" (lit 0),
   .assign "jla" (.loadw 1 (atOff (v "jga") 8)), kept fail "jla" 64,
   .ite (eEq (v "jla") (.loadw 1 (atOff (v "jgb") 8)))
     [.assign "jna" (.loadw 1 (v "jga")), kept fail "jna" windowRoom,
      .assign "jnb" (.loadw 1 (v "jgb")), kept fail "jnb" windowRoom,
      .assign "jeq" (lit 1), .assign "jx" (lit 0),
      .while (eLt (v "jx") (v "jla")) alikeOctet] []]

/-- The commit's sequence number, eight octets. -/
def seqPart : List PStmt :=
  [.assign "jok" (lit 1), .assign "ji" (lit 8),
   .ite (eLt (v "jpl") (n 8)) [.assign "jok" (lit 0)] (leS "jseq" (v "jpp") 8)]

/-- Its Message-ID, a counted run: where it lies in the window and how long it is, into the area. -/
def idPart : List PStmt :=
  [.ite (v "jok")
     [.ite (eLt (v "jpl") (eAdd (v "ji") (n 1))) [.assign "jok" (lit 0)]
       [.assign "jml" (byte (eAdd (v "jpp") (v "ji"))), inc "ji",
        .ite (eLt (v "jpl") (eAdd (v "ji") (v "jml"))) [.assign "jok" (lit 0)]
          [setw sIdAt (inWindow (v "ji")), setw sIdLen (v "jml"),
           .assign "ji" (eAdd (v "ji") (v "jml"))]]] []]

/-- How many groups, sixteen at most. -/
def countPart : List PStmt :=
  [.ite (v "jok")
     [.ite (eLt (v "jpl") (eAdd (v "ji") (n 1))) [.assign "jok" (lit 0)]
       [.assign "jgc" (byte (eAdd (v "jpp") (v "ji"))), inc "ji",
        .ite (eLt (n groupsMax) (v "jgc")) [.assign "jok" (lit 0)] []]] []]

/-- Group `jgi`: its name, a counted run, and its article number, into its slot, and checked. -/
def groupBody : List PStmt :=
  [kept fail "ji" maxPayload,
   .ite (eLt (v "jpl") (eAdd (v "ji") (n 1))) [.assign "jok" (lit 0)]
    [.assign "jnl" (byte (eAdd (v "jpp") (v "ji"))), inc "ji",
     .ite (eLt (v "jpl") (eAdd (v "ji") (v "jnl"))) [.assign "jok" (lit 0)]
       ([.assign "jgp" (slot "jgi"), .store (v "jgp") (inWindow (v "ji")),
         .store (atOff (v "jgp") 8) (v "jnl"), .assign "ji" (eAdd (v "ji") (v "jnl")),
         .ite (eLt (v "jpl") (eAdd (v "ji") (n 4))) [.assign "jok" (lit 0)]
           (leS "jnum" (eAdd (v "jpp") (v "ji")) 4 ++
            [.store (atOff (v "jgp") 16) (v "jnum"), .assign "ji" (eAdd (v "ji") (n 4)),
             .ite (or2 (or2 (eLt (v "jnl") (n 1)) (eLt (n 64) (v "jnl")))
                 (or2 (eLt (v "jnum") (n 1)) (eLt (n (2 ^ 31 - 1)) (v "jnum"))))
               [.assign "jok" (lit 0)] []])])],
   inc "jgi"]

/-- The groups, each read, until one is not one or all are read. -/
def groupsPart : List PStmt :=
  [.assign "jgi" (lit 0), .while (eAnd (v "jok") (eLt (v "jgi") (v "jgc"))) (groupBody fail)]

/-- The header's and the file's sizes and the file's CRC, four octets each. -/
def tailPart : List PStmt :=
  [kept fail "ji" maxPayload,
   .ite (v "jok")
     [.ite (eLt (v "jpl") (eAdd (v "ji") (n 12))) [.assign "jok" (lit 0)]
       (leS "jhs" (eAdd (v "jpp") (v "ji")) 4 ++
        leS "jfs" (eAdd (v "jpp") (eAdd (v "ji") (n 4))) 4 ++
        leS "jcrc" (eAdd (v "jpp") (eAdd (v "ji") (n 8))) 4 ++
        [.assign "ji" (eAdd (v "ji") (n 12))])] []]

/-- No octet after the commit. -/
def exactPart : List PStmt := [.ite (eAnd (v "jok") (ne (v "ji") (v "jpl"))) [.assign "jok" (lit 0)] []]

/-- What a correct store writes: a sequence number, a Message-ID of 1 to 250 octets, a group. A header no larger than
its file. -/
def checkPart : List PStmt :=
  [.ite (eAnd (v "jok") (or2 (or2 (eEq (v "jseq") (n 0)) (eLt (v "jml") (n 1)))
       (or2 (or2 (eLt (n 250) (v "jml")) (eLt (v "jgc") (n 1))) (eLt (v "jfs") (v "jhs")))))
     [.assign "jok" (lit 0)] []]

/-- Group `ja`'s name against group `jbb`'s. -/
def pairBody : List PStmt := namesAlike fail ++ [.ite (v "jeq") [.assign "jok" (lit 0)] [], inc "jbb"]

/-- Group `ja`'s name against those after it. -/
def pairRow : List PStmt :=
  [.assign "jbb" (eAdd (v "ja") (n 1)), .while (eLt (v "jbb") (v "jgc")) (pairBody fail), inc "ja"]

/-- No two group names alike. -/
def pairsPart : List PStmt :=
  [.assign "ja" (lit 0), .while (eAnd (v "jok") (eLt (v "ja") (v "jgc"))) (pairRow fail)]

/-- The commit's fields into the area, its type into `jrec`. -/
def storePart : List PStmt :=
  [.ite (v "jok")
     [.assign "jrec" (lit commitType), setw sSeq (v "jseq"), setw sGroupCount (v "jgc"),
      setw sHeader (v "jhs"), setw sFileSize (v "jfs"), setw sCrc (v "jcrc")] []]

/-- The commit the payload at `jpp`, `jpl` octets, holds, if exactly one a correct store writes. Its fields go into the
area, and `jrec` is set to its type. -/
def decode : List PStmt :=
  seqPart ++ idPart ++ countPart ++ groupsPart fail ++ tailPart fail ++ exactPart ++ checkPart ++
    pairsPart fail ++ storePart

/-- The record the checked frame at `jf` holds, its type into `jrec`; else `jwhy` says it holds
none. -/
def recordOf : List PStmt :=
  [.assign "jrec" (lit 0), .assign "jpp" (atOff (v "jf") headerLength),
   .ite (eEq (v "jt") (n formatType))
     [.ite (eAnd (eEq (v "jpl") (n (magic.length + keyLength))) (bytesAre (v "jpp") magic))
       [.assign "jrec" (lit formatType)] []]
     [.ite (eEq (v "jt") (n commitType)) (decode fail)
       [.ite (eAnd (eEq (v "jt") (n startType)) (eEq (v "jpl") (n 0)))
         [.assign "jrec" (lit startType)] []]],
   .ite (eEq (v "jrec") (n 0)) [.assign "jwhy" (lit (whyCode .notARecord))] []]

/-- The record read when the frame checks. -/
def recordPart : PStmt := .ite (eEq (v "jwhy") (n 0)) (recordOf fail) []

/-- The key's `i`th octet, from a format record's payload at `jpp`. -/
def keyStore (i : Nat) : PStmt := .storeb (atOff sp (sKey + i)) (byte (atOff (v "jpp") (magic.length + i)))

/-- The key, from a format record's payload. -/
def keyCopy : List PStmt := (List.range keyLength).map keyStore

/-- A record taken: one more counted, its type, where the next frame starts, the status. -/
def acceptTail : List PStmt :=
  [setw sCount (eAdd (word sCount) (n 1)), setw sType (v "jrec"),
   setw sPos (eAdd (v "jp") (eAdd (v "jpl") (n (headerLength + 1)))), setw sStatus (n record)]

/-- The record read, unless it is a second format: the journal's key taken from the first. -/
def accept : List PStmt :=
  [.ite (eAnd (eLt (n 0) (word sCount)) (eEq (v "jrec") (n formatType)))
    [setw sStatus (n corrupt), setw sWhy (n (whyCode .formatAgain))]
    (.ite (eEq (v "jrec") (n formatType)) (keyCopy ++ [setw sKeyed (n 1)]) [] :: acceptTail)]

/-- The frame at journal offset `jq` found in the window: its offset there into `jo`, which the
step keeps within the window, its address into `jf` and its payload's into `jpp`. -/
def frameAt : List PStmt :=
  [.assign "jo" (eSub (v "jq") (v "jb")), kept fail "jo" windowMax,
   .assign "jf" (eAdd (v "jw") (v "jo")), .assign "jpp" (atOff (v "jf") headerLength)]

/-- A frame that checks ends the search. -/
def tornNext : PStmt := .ite (eEq (v "jwhy") (n 0)) [.assign "jtorn" (lit 0)] []

/-- Whether the search goes on: none found yet, and the journal not at its end. -/
def tornGo : PExpr := eAnd (v "jtorn") (eLt (v "jq") (v "jsz"))

/-- The frame at `jq`, checked under the journal's key: one that checks ends the search. -/
def tornLoop : List PStmt :=
  frameAt fail ++ [.assign "jr" (eSub (v "jsz") (v "jq"))] ++ frameWhy true ++
    [tornNext, inc "jq"]

/-- Whether a frame that checks starts after the first octet of the one at `jp`. -/
def tornSearch : List PStmt :=
  [.assign "jq" (eAdd (v "jp") (n 1)), .while tornGo (tornLoop fail)]

/-- Whether what is left, `jrem`, fits the append that can have been cut, `jx`. With the key, also whether no checking
frame starts in it after its first octet. -/
def tornCheck : PStmt :=
  .ite (eLe (v "jrem") (v "jx")) [.assign "jtorn" (lit 1), .ite (v "jky") (tornSearch fail) []] []

/-- A frame a torn append can leave: whether what is left fits the append. With the key, also whether no checking frame
starts in it after its first octet. -/
def tornPart : List PStmt :=
  [.assign "jx" (lit firstFrame), .ite (v "jky") [.assign "jx" (lit maxFrame)] [], tornCheck fail]

/-- The status where reading stops: torn tail with `jtorn`, else corruption and why, `jmw`. -/
def stopStatus : PStmt :=
  .ite (v "jtorn") [setw sStatus (n torn)] [setw sStatus (n corrupt), setw sWhy (v "jmw")]

/-- The frame at `jp` is no record, for `jwhy`: a torn tail if a torn append can leave it, what is
left fits the append that can have been cut, and no frame that checks starts in it after its first
octet; else corruption. -/
def stopped : List PStmt :=
  [.assign "jmw" (v "jwhy"), .assign "jtorn" (lit 0),
   .ite (eLt (v "jmw") (n (whyCode .notARecord))) (tornPart fail) [], stopStatus]

/-- The window's octet `ji` from `jx` past its start. -/
def copyByte : List PStmt :=
  [.storeb (eAdd (v "jw") (v "ji")) (byte (eAdd (eAdd (v "jw") (v "jx")) (v "ji"))), inc "ji"]

/-- The window's `jcnt` octets from `jx` on moved to its start, unless `jx` is zero. -/
def windowCopy : PStmt := .ite (v "jx") [.while (eLt (v "ji") (v "jcnt")) copyByte] []

/-- The window moved to start at `jp`, and the octets wanted after it: as many as one read adds,
or as the journal has left. -/
def want : List PStmt :=
  [.assign "jx" (eSub (v "jp") (v "jb")), kept fail "jx" windowMax,
   .assign "jcnt" (eSub (v "jwl") (v "jx")), .assign "ji" (lit 0),
   windowCopy,
   .assign "jwl" (v "jcnt"), setw sBase (v "jp"), setw sLen (v "jwl"),
   .assign "jx" (eSub (v "jsz") (eAdd (v "jp") (v "jwl"))),
   .ite (eLt (n chunk) (v "jx")) [.assign "jx" (lit chunk)] [],
   setw sWant (v "jx"), setw sStatus (n wanted)]

/-- The step's head: the area's words it keeps, into locals. -/
def stepHead : List PStmt :=
  [.assign "jsz" (word sSize), .assign "jb" (word sBase), .assign "jwl" (word sLen),
   kept fail "jwl" windowMax,
   .assign "jp" (word sPos), .assign "jky" (word sKeyed), .assign "jw" (atOff sp sWindow),
   .assign "jrem" (eSub (v "jsz") (v "jp"))]

/-- The frame at `jp` found in the window and checked. -/
def frameRead : List PStmt :=
  [.assign "jq" (v "jp")] ++ frameAt fail ++ [.assign "jr" (v "jrem")] ++ frameWhy false

/-- The frame at `jp` read: its record taken, or why reading stops. -/
def readPart : List PStmt :=
  frameRead fail ++ [recordPart fail, .ite (v "jwhy") (stopped fail) accept]

/-- **One step**: the end of the journal, octets wanted, or the frame at `jp` read. -/
def stepWith : List PStmt :=
  stepHead fail ++
  [.ite (eEq (v "jrem") (n 0)) [setw sStatus (n clean)]
     [.assign "jneed" (v "jrem"),
      .ite (eLt (n maxFrame) (v "jneed")) [.assign "jneed" (lit maxFrame)] [],
      .ite (eLt (eAdd (v "jb") (v "jwl")) (eAdd (v "jp") (v "jneed"))) (want fail) (readPart fail)]]

end

/-- What the test's kernel returns when it finds a word of its area out of range. -/
def broken : Nat := 99

/-- One step, ending with `broken` on a word out of range. -/
def stepSrc : List PStmt := stepWith [.ret (n broken)]

/-- The step's locals, its own and SipHash's. -/
def locals : List String :=
  ["jsz", "jb", "jwl", "jp", "jky", "jw", "jrem", "jneed", "jx", "jcnt", "ji", "jq", "jo", "jf",
   "jr", "jwhy", "jpl", "jt", "jhk", "jtag", "jmw", "jtorn", "jrec", "jpp", "jok", "jseq", "jml",
   "jgc", "jgi", "jnl", "jgp", "jnum", "jhs", "jfs", "jcrc", "ja", "jbb", "jga", "jgb", "jla",
   "jna", "jnb", "jeq", "k", "p", "n", "r", "m", "v0", "v1", "v2", "v3", "off", "j"]

/-- `jz`, then the step's locals, each set to it. -/
def decls : List PStmt := .dec "jz" (eSub sp sp) :: locals.map (.dec · (v "jz"))

/-- One step on the area at `jsc`, its status returned. -/
def scanKernel : PFun :=
  { name := "dn_scan_step", exported := true, params := [(1, "jsc")],
    body := decls ++ stepSrc ++ [.ret (word sStatus)] }

/-- The area as a C header for the test's host. -/
def header : String :=
  let defs : List (String × Nat) :=
    [("SIZE", sSize), ("BASE", sBase), ("LEN", sLen), ("POS", sPos), ("KEYED", sKeyed),
     ("COUNT", sCount), ("STATUS", sStatus), ("WHY", sWhy), ("WANT", sWant), ("TYPE", sType),
     ("SEQ", sSeq), ("ID_AT", sIdAt), ("ID_LEN", sIdLen), ("GROUP_COUNT", sGroupCount),
     ("HEADER", sHeader), ("FILE_SIZE", sFileSize), ("CRC", sCrc), ("GROUPS", sGroups),
     ("GROUP_SLOT", groupSlot), ("KEY", sKey), ("WINDOW", sWindow), ("WINDOW_MAX", windowMax),
     ("AREA", size), ("WANTED", wanted), ("RECORD", record), ("CLEAN", clean), ("TORN", torn),
     ("CORRUPT", corrupt)]
  "/* Generated by dn-compiler emit-scan-layout from DN.News.ScanProg. */\n" ++
  "#ifndef DN_SCAN_LAYOUT_H\n#define DN_SCAN_LAYOUT_H\n" ++
  String.join (defs.map fun (name, value) => s!"#define DN_SCAN_{name} {value}\n") ++
  "#endif\n"

def regression_938 : Bool := (Checked.emit scanKernel).isOk

end DN.News.ScanProg
