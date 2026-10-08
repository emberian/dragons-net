-- SPDX-License-Identifier: AGPL-3.0-or-later
import DN.News.Journal
import DN.News.SipProg

/-!
# DN.News.ScanProg

A journal read back as `DN.News.Journal.scan` reads it, as the gate prints it: a step reads one
frame from a window of the journal that the caller fills, and leaves in the scanner's area at `jsc`
what it found — octets wanted (how many, from where the window ends), a record (its fields), or how
the journal ends; the area is all it keeps between steps. A frame's tag is computed by
`DN.News.SipProg.sipSrc`. Tested against `dn-compiler journal-model`, not proven.
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
/-- A record: its type, and of a commit its sequence number, where its Message-ID lies and its
length, how many groups, the header's and the file's sizes, the CRC-32C, then for each group where
its name lies, its length and the article number. -/
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
def size : Nat := sWindow + windowMax

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

/-- The key a frame is checked under, into `k`, zero for none: with `keyed`, the journal's;
else the journal's once read, or the key a frame of the format's shape carries. -/
def keySel : Bool → List PStmt
  | true => [.assign "k" (atOff sp sKey)]
  | false =>
    [.ite (v "jky") [.assign "k" (atOff sp sKey)]
      [.assign "k" (lit 0),
       .ite (eAnd (eEq (v "jt") (n formatType)) (eEq (v "jpl") (n (magic.length + keyLength))))
         [.ite (bytesAre (atOff (v "jf") headerLength) journalTitle)
           [.assign "k" (atOff (v "jf") (headerLength + magic.length))] []] []]]

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

/-- Why the frame at journal offset `jq`, at `jf` in the window, `jr` octets of the journal from
it, does not check, into `jwhy`, zero if it does; its payload's length into `jpl` and its type into
`jt`. -/
def frameWhy (keyed : Bool) : List PStmt :=
  [.assign "jwhy" (lit 0),
   .ite (eLt (v "jr") (n headerLength)) [.assign "jwhy" (lit (whyCode .short))]
     (leS "jpl" (v "jf") 4 ++
      [.ite (eLt (n maxPayload) (v "jpl"))
        [.assign "jwhy" (lit (whyCode .tooLong))]
        [.ite (eLt (v "jr") (eAdd (v "jpl") (n (headerLength + 1))))
          [.assign "jwhy" (lit (whyCode .short))]
          [.ite (ne (byte (eAdd (v "jf") (eAdd (v "jpl") (n headerLength)))) (n 0xA5))
            [.assign "jwhy" (lit (whyCode .unterminated))]
            ([.assign "jt" (byte (atOff (v "jf") 12))] ++ keySel keyed ++
             [.ite (eEq (v "k") (n 0)) [.assign "jwhy" (lit (whyCode .tag))]
               (message ++ SipProg.sipSrc ++ leS "jtag" (atOff (v "jf") 4) 8 ++
                [.ite (ne (v "r") (v "jtag")) [.assign "jwhy" (lit (whyCode .tag))] []])])]]])]

/-- Group `g`'s slot in the area. -/
def slot (g : String) : PExpr := eAdd (atOff sp sGroups) (eMul (v g) (n groupSlot))

/-- The commit the payload at `jpp`, `jpl` octets, holds, if it holds exactly one that a correct
store writes: its fields into the area, and `jrec` set to the commit's type. -/
def decode : List PStmt :=
  [.assign "jok" (lit 1), .assign "ji" (lit 8),
   .ite (eLt (v "jpl") (n 8)) [.assign "jok" (lit 0)] (leS "jseq" (v "jpp") 8),
   .ite (v "jok")
     [.ite (eLt (v "jpl") (eAdd (v "ji") (n 1))) [.assign "jok" (lit 0)]
       [.assign "jml" (byte (eAdd (v "jpp") (v "ji"))), inc "ji",
        .ite (eLt (v "jpl") (eAdd (v "ji") (v "jml"))) [.assign "jok" (lit 0)]
          [setw sIdAt (eAdd (v "jpp") (v "ji")), setw sIdLen (v "jml"),
           .assign "ji" (eAdd (v "ji") (v "jml"))]]] [],
   .ite (v "jok")
     [.ite (eLt (v "jpl") (eAdd (v "ji") (n 1))) [.assign "jok" (lit 0)]
       [.assign "jgc" (byte (eAdd (v "jpp") (v "ji"))), inc "ji",
        .ite (eLt (n groupsMax) (v "jgc")) [.assign "jok" (lit 0)] []]] [],
   .assign "jgi" (lit 0),
   .while (eAnd (v "jok") (eLt (v "jgi") (v "jgc")))
     [.ite (eLt (v "jpl") (eAdd (v "ji") (n 1))) [.assign "jok" (lit 0)]
       [.assign "jnl" (byte (eAdd (v "jpp") (v "ji"))), inc "ji",
        .ite (eLt (v "jpl") (eAdd (v "ji") (v "jnl"))) [.assign "jok" (lit 0)]
          ([.assign "jgp" (slot "jgi"), .store (v "jgp") (eAdd (v "jpp") (v "ji")),
            .store (atOff (v "jgp") 8) (v "jnl"), .assign "ji" (eAdd (v "ji") (v "jnl")),
            .ite (eLt (v "jpl") (eAdd (v "ji") (n 4))) [.assign "jok" (lit 0)]
              (leS "jnum" (eAdd (v "jpp") (v "ji")) 4 ++
               [.store (atOff (v "jgp") 16) (v "jnum"), .assign "ji" (eAdd (v "ji") (n 4)),
                .ite (or2 (or2 (eLt (v "jnl") (n 1)) (eLt (n 64) (v "jnl")))
                    (or2 (eLt (v "jnum") (n 1)) (eLt (n (2 ^ 31 - 1)) (v "jnum"))))
                  [.assign "jok" (lit 0)] []])])],
      inc "jgi"],
   .ite (v "jok")
     [.ite (eLt (v "jpl") (eAdd (v "ji") (n 12))) [.assign "jok" (lit 0)]
       (leS "jhs" (eAdd (v "jpp") (v "ji")) 4 ++
        leS "jfs" (eAdd (v "jpp") (eAdd (v "ji") (n 4))) 4 ++
        leS "jcrc" (eAdd (v "jpp") (eAdd (v "ji") (n 8))) 4 ++
        [.assign "ji" (eAdd (v "ji") (n 12))])] [],
   .ite (eAnd (v "jok") (ne (v "ji") (v "jpl"))) [.assign "jok" (lit 0)] [],
   .ite (eAnd (v "jok") (or2 (or2 (eEq (v "jseq") (n 0)) (eLt (v "jml") (n 1)))
       (or2 (or2 (eLt (n 250) (v "jml")) (eLt (v "jgc") (n 1))) (eLt (v "jfs") (v "jhs")))))
     [.assign "jok" (lit 0)] [],
   .assign "ja" (lit 0),
   .while (eAnd (v "jok") (eLt (v "ja") (v "jgc")))
     [.assign "jbb" (eAdd (v "ja") (n 1)),
      .while (eLt (v "jbb") (v "jgc"))
        [.assign "jga" (slot "ja"), .assign "jgb" (slot "jbb"),
         .ite (eEq (.loadw 1 (atOff (v "jga") 8)) (.loadw 1 (atOff (v "jgb") 8)))
           [.assign "jeq" (lit 1), .assign "jx" (lit 0),
            .while (eLt (v "jx") (.loadw 1 (atOff (v "jga") 8)))
              [.ite (ne (byte (eAdd (.loadw 1 (v "jga")) (v "jx")))
                  (byte (eAdd (.loadw 1 (v "jgb")) (v "jx")))) [.assign "jeq" (lit 0)] [],
               inc "jx"],
            .ite (v "jeq") [.assign "jok" (lit 0)] []] [],
         inc "jbb"],
      inc "ja"],
   .ite (v "jok")
     [.assign "jrec" (lit commitType), setw sSeq (v "jseq"), setw sGroupCount (v "jgc"),
      setw sHeader (v "jhs"), setw sFileSize (v "jfs"), setw sCrc (v "jcrc")] []]

/-- The record the checked frame at `jf` holds, its type into `jrec`; else `jwhy` says it holds
none. -/
def recordOf : List PStmt :=
  [.assign "jrec" (lit 0), .assign "jpp" (atOff (v "jf") headerLength),
   .ite (eEq (v "jt") (n formatType))
     [.ite (eAnd (eEq (v "jpl") (n (magic.length + keyLength))) (bytesAre (v "jpp") magic))
       [.assign "jrec" (lit formatType)] []]
     [.ite (eEq (v "jt") (n commitType)) decode
       [.ite (eAnd (eEq (v "jt") (n startType)) (eEq (v "jpl") (n 0)))
         [.assign "jrec" (lit startType)] []]],
   .ite (eEq (v "jrec") (n 0)) [.assign "jwhy" (lit (whyCode .notARecord))] []]

/-- The record read, unless it is a second format: the journal's key taken from the first. -/
def accept : List PStmt :=
  [.ite (eAnd (eLt (n 0) (word sCount)) (eEq (v "jrec") (n formatType)))
    [setw sStatus (n corrupt), setw sWhy (n (whyCode .formatAgain))]
    [.ite (eEq (v "jrec") (n formatType))
       ((List.range keyLength).map (fun i => .storeb (atOff sp (sKey + i))
          (byte (atOff (v "jpp") (magic.length + i)))) ++ [setw sKeyed (n 1)]) [],
     setw sCount (eAdd (word sCount) (n 1)), setw sType (v "jrec"),
     setw sPos (eAdd (v "jp") (eAdd (v "jpl") (n (headerLength + 1)))),
     setw sStatus (n record)]]

/-- The frame at `jp` is no record, for `jwhy`: a torn tail if a torn append can leave it, what is
left fits the append that can have been cut, and no frame that checks starts in it after its first
octet; else corruption. -/
def stopped : List PStmt :=
  [.assign "jmw" (v "jwhy"), .assign "jtorn" (lit 0),
   .ite (eLt (v "jmw") (n (whyCode .notARecord)))
     [.assign "jx" (lit firstFrame), .ite (v "jky") [.assign "jx" (lit maxFrame)] [],
      .ite (eLe (v "jrem") (v "jx"))
        [.assign "jtorn" (lit 1),
         .ite (v "jky")
           [.assign "jq" (eAdd (v "jp") (n 1)),
            .while (eAnd (v "jtorn") (eLt (v "jq") (v "jsz")))
              ([.assign "jf" (eAdd (v "jw") (eSub (v "jq") (v "jb"))),
                .assign "jr" (eSub (v "jsz") (v "jq"))] ++ frameWhy true ++
               [.ite (eEq (v "jwhy") (n 0)) [.assign "jtorn" (lit 0)] [], inc "jq"])] []] []] [],
   .ite (v "jtorn") [setw sStatus (n torn)] [setw sStatus (n corrupt), setw sWhy (v "jmw")]]

/-- The window moved to start at `jp`, and the octets wanted after it: as many as one read adds,
or as the journal has left. -/
def want : List PStmt :=
  [.assign "jx" (eSub (v "jp") (v "jb")), .assign "ji" (lit 0),
   .ite (v "jx")
     [.while (eLt (eAdd (v "ji") (v "jx")) (v "jwl"))
       [.storeb (eAdd (v "jw") (v "ji")) (byte (eAdd (eAdd (v "jw") (v "jx")) (v "ji"))),
        inc "ji"]] [],
   .assign "jwl" (eSub (v "jwl") (v "jx")), setw sBase (v "jp"), setw sLen (v "jwl"),
   .assign "jx" (eSub (v "jsz") (eAdd (v "jp") (v "jwl"))),
   .ite (eLt (n chunk) (v "jx")) [.assign "jx" (lit chunk)] [],
   setw sWant (v "jx"), setw sStatus (n wanted)]

/-- **One step**: the end of the journal, octets wanted, or the frame at `jp` read. -/
def stepSrc : List PStmt :=
  [.assign "jsz" (word sSize), .assign "jb" (word sBase), .assign "jwl" (word sLen),
   .assign "jp" (word sPos), .assign "jky" (word sKeyed), .assign "jw" (atOff sp sWindow),
   .assign "jrem" (eSub (v "jsz") (v "jp")),
   .ite (eEq (v "jrem") (n 0)) [setw sStatus (n clean)]
     [.assign "jneed" (v "jrem"),
      .ite (eLt (n maxFrame) (v "jneed")) [.assign "jneed" (lit maxFrame)] [],
      .ite (eLt (eAdd (v "jb") (v "jwl")) (eAdd (v "jp") (v "jneed"))) want
        ([.assign "jq" (v "jp"), .assign "jf" (eAdd (v "jw") (eSub (v "jp") (v "jb"))),
          .assign "jr" (v "jrem")] ++ frameWhy false ++
         [.ite (eEq (v "jwhy") (n 0)) recordOf [], .ite (v "jwhy") stopped accept])]]

/-- The step's locals, its own and SipHash's. -/
def locals : List String :=
  ["jsz", "jb", "jwl", "jp", "jky", "jw", "jrem", "jneed", "jx", "ji", "jq", "jf", "jr", "jwhy",
   "jpl", "jt", "jtag", "jmw", "jtorn", "jrec", "jpp", "jok", "jseq", "jml", "jgc", "jgi", "jnl",
   "jgp", "jnum", "jhs", "jfs", "jcrc", "ja", "jbb", "jga", "jgb", "jeq",
   "k", "p", "n", "r", "m", "v0", "v1", "v2", "v3", "off", "j"]

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
