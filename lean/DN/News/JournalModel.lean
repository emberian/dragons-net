-- SPDX-License-Identifier: AGPL-3.0-or-later
import DN.News.Journal
import DN.News.FrameModel

/-!
# DN.News.JournalModel

The journal of `DN.News.Journal` run on cases, as `dn-compiler journal-model` answers them, a line
each; bytes are hex, `-` for none:

    crc BYTES              the CRC-32C, in decimal
    encode SEQ ID HEADER SIZE CRC GROUPS
                           the commit's frame, or `not-ok` if a frame cannot hold it; GROUPS is
                           `NAME=NUMBER` for each group, separated by commas
    scan BYTES             the records read and how the journal ends
    name BYTES             what a name in the spool directory is
    names SEQ              the final and the temporary name of an article

A record reads as `F` for the format and `C:SEQ:ID:HEADER:SIZE:CRC:GROUPS` for a commit; the end
as `clean`, `torn OFFSET` or `corrupt OFFSET WHY`. Numbers are decimal digits only, and a sequence
number past sixteen hexadecimal digits has no names. With a mutant, reading follows its rules.
-/

namespace DN.News.JournalModel

open DN.News.Journal
open DN.News.FrameModel (parseHex hex)
open DN.News.CommandSpec (ascii)

/-- A number written in decimal digits and nothing else. -/
def natOf (s : String) : Option Nat :=
  if !s.isEmpty && s.all Char.isDigit then s.toNat? else none

def groupsText (gs : List Group) : String :=
  ",".intercalate (gs.map fun g => s!"{hex g.name}={g.number}")

def parseGroups (s : String) : Option (List Group) :=
  if s == "-" then some []
  else (s.splitOn ",").mapM fun g =>
    match g.splitOn "=" with
    | [name, number] => do pure ⟨← parseHex name, ← natOf number⟩
    | _ => none

def recordText : Record → String
  | .format => "F"
  | .commit c =>
    s!"C:{c.seq}:{hex c.messageId}:{c.headerSize}:{c.fileSize}:{c.fileCrc}:{groupsText c.groups}"

def whyText : Why → String
  | .short => "short" | .tooLong => "too-long" | .unterminated => "unterminated"
  | .checksum => "checksum" | .notARecord => "not-a-record" | .noFormat => "no-format"
  | .formatAgain => "format-again"

def endText : End → String
  | .clean => "clean"
  | .torn o => s!"torn {o}"
  | .corrupt o w => s!"corrupt {o} {whyText w}"

def scanText (sc : Scan) : String :=
  " ".intercalate (sc.records.map recordText ++ ["end", endText sc.ending])

def nameText : Option Name → String
  | some .journal => "journal"
  | some (.final s) => s!"final {s}"
  | some (.temp s) => s!"temp {s}"
  | none => "none"

/-- The answer to one case, or why the line is not one. -/
def answer (r : Rules) (line : String) : Except String String :=
  match line.splitOn " " with
  | ["crc", bytes] =>
    match parseHex bytes with
    | some bs => .ok s!"{(crc32c bs).toNat}"
    | none => .error s!"not hex: {bytes}"
  | ["encode", seq, id, header, size, crc, groups] =>
    match natOf seq, parseHex id, natOf header, natOf size, natOf crc, parseGroups groups with
    | some s, some i, some h, some z, some c, some gs =>
      let commit : Commit := ⟨s, i, gs, h, z, c⟩
      .ok (if commit.ok then hex (Record.commit commit).encode else "not-ok")
    | _, _, _, _, _, _ => .error s!"not a commit: {line}"
  | ["scan", bytes] =>
    match parseHex bytes with
    | some bs => .ok (scanText (scanWith r bs))
    | none => .error s!"not hex: {bytes}"
  | ["name", bytes] =>
    match parseHex bytes with
    | some bs => .ok (nameText (parseName bs))
    | none => .error s!"not hex: {bytes}"
  | ["names", seq] =>
    match natOf seq with
    | some s =>
      if s < 2 ^ 64 then .ok s!"{hex (finalName s)} {hex (tempName s)}"
      else .error s!"not a sequence number: {seq}"
    | none => .error s!"not a number: {seq}"
  | _ => .error s!"not a case: {line}"

/-- The answers to every line of `input`, one line each. -/
def runAll (r : Rules) (input : String) : Except String String := do
  let lines := (input.splitOn "\n").filter (!·.isEmpty)
  let answers ← lines.mapM (answer r)
  pure (String.join (answers.map (· ++ "\n")))

/-! ## Examples: RFC 7143's CRCs, the usual check value, and a journal read back -/

def bytesOf (ns : List Nat) : Bytes := ns.map (BitVec.ofNat 8 ·)

/-- RFC 7143 appendix A.4: thirty-two octets of zeros, of ones, rising and falling. -/
def regression_874 : Bool := (crc32c (bytesOf (List.replicate 32 0))).toNat == 0x8A9136AA
def regression_875 : Bool := (crc32c (bytesOf (List.replicate 32 0xFF))).toNat == 0x62A8AB43
def regression_876 : Bool := (crc32c (bytesOf (List.range 32))).toNat == 0x46DD794E
def regression_877 : Bool := (crc32c (bytesOf (List.range 32).reverse)).toNat == 0x113FDB5C
/-- RFC 7143 appendix A.4's iSCSI read command. -/
def regression_878 : Bool :=
  (crc32c (bytesOf [0x01, 0xC0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0x14, 0, 0, 0, 0, 0,
    0x04, 0, 0, 0, 0, 0x14, 0, 0, 0, 0x18, 0x28, 0, 0, 0, 0, 0, 0, 0, 0x02, 0, 0, 0, 0, 0, 0,
    0])).toNat == 0xD9963A56
/-- The CRC-32C of "123456789", the check value CRC catalogues give. -/
def regression_879 : Bool := (crc32c (ascii "123456789")).toNat == 0xE3069283
/-- A journal and a torn record after it. -/
def regression_880 : Bool :=
  let j := encodeAll [.format, .commit sample]
  scan (j ++ ((Record.commit sample).encode.take 12)) == ⟨[.format, .commit sample], .torn j.length⟩
/-- A frame that checks but is no record is corruption even last: a journal of a later format. -/
def regression_881 : Bool :=
  scan (frame formatType (ascii "dragons-net journal" ++ [BitVec.ofNat 8 2])) ==
    ⟨[], .corrupt 0 .notARecord⟩
/-- Article numbers are those RFC 3977 §6 allows, 1 to 2,147,483,647. -/
def regression_882 : Bool :=
  let numbered (n : Nat) : Commit := { sample with groups := [⟨ascii "local.test", n⟩] }
  !(numbered 0).ok && (numbered 1).ok && (numbered (2 ^ 31 - 1)).ok && !(numbered (2 ^ 31)).ok
/-- An append cut short and filled with zeros reads as a torn tail: its end mark is gone. -/
def regression_883 : Bool :=
  let j := encodeAll [.format, .commit sample]
  let f := (Record.commit sample).encode
  scan (j ++ f.take 12 ++ List.replicate (f.length - 12) 0) ==
    ⟨[.format, .commit sample], .torn j.length⟩
/-- Before any record, a torn tail is at most the format's frame; past it, corruption. -/
def regression_884 : Bool :=
  scan (List.replicate firstFrame 0) == ⟨[], .torn 0⟩ &&
    scan (List.replicate (firstFrame + 1) 0) == ⟨[], .corrupt 0 .unterminated⟩
/-- A correct store numbers from 1, names a group once and writes a header no larger than its
file. -/
def regression_885 : Bool :=
  !{ sample with seq := 0 }.ok &&
    !{ sample with groups := [⟨ascii "g", 1⟩, ⟨ascii "g", 2⟩] }.ok &&
    { sample with headerSize := 200 }.ok && !{ sample with headerSize := 201 }.ok

end DN.News.JournalModel
