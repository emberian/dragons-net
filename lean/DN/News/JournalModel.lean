-- SPDX-License-Identifier: AGPL-3.0-or-later
import DN.News.Journal
import DN.News.FrameModel

/-!
# DN.News.JournalModel

The journal of `DN.News.Journal` run on cases, as `dn-compiler journal-model` answers them, a line
each; bytes are hex, `-` for none:

    crc BYTES              the CRC-32C, in decimal
    siphash KEY BYTES      the SipHash-2-4 tag under a key of sixteen octets, in decimal
    format KEY             the frame of a journal's format carrying the key
    start KEY OFFSET       the frame of a start at OFFSET under KEY
    encode KEY OFFSET SEQ ID HEADER SIZE CRC GROUPS
                           the commit's frame at OFFSET under KEY, or `not-ok` if a correct store
                           does not write it; GROUPS is `NAME=NUMBER` for each group, separated by
                           commas
    scan BYTES             the records read and how the journal ends
    name BYTES             what a name in the spool directory is
    names SEQ              the final, the temporary and the quarantine name of an article, and the
                           name of a tail kept, all numbered SEQ

A record reads as `F:KEY` for the format, `S` for a start and `C:SEQ:ID:HEADER:SIZE:CRC:GROUPS` for
a commit; the end as `clean`, `torn OFFSET` or `corrupt OFFSET WHY`. Numbers are decimal digits
only, and a sequence number past sixteen hexadecimal digits has no names. With a mutant, reading
follows its rules.
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
  | .format key => s!"F:{hex key}"
  | .commit c =>
    s!"C:{c.seq}:{hex c.messageId}:{c.headerSize}:{c.fileSize}:{c.fileCrc}:{groupsText c.groups}"
  | .start => "S"

def whyText : Why → String
  | .short => "short" | .tooLong => "too-long" | .unterminated => "unterminated"
  | .tag => "tag" | .notARecord => "not-a-record" | .formatAgain => "format-again"

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
  | some (.quarantine s) => s!"quarantine {s}"
  | some (.tail s) => s!"tail {s}"
  | none => "none"

/-- The answer to one case, or why the line is not one. -/
def answer (r : Rules) (line : String) : Except String String :=
  match line.splitOn " " with
  | ["crc", bytes] =>
    match parseHex bytes with
    | some bs => .ok s!"{(crc32c bs).toNat}"
    | none => .error s!"not hex: {bytes}"
  | ["siphash", key, bytes] =>
    match parseHex key, parseHex bytes with
    | some k, some bs =>
      if k.length = keyLength then .ok s!"{(SipHash.tag k bs).toNat}"
      else .error s!"not a key: {key}"
    | _, _ => .error s!"not hex: {line}"
  | ["format", key] =>
    match parseHex key with
    | some k =>
      if k.length = keyLength then .ok (hex ((Record.format k).encode k 0))
      else .error s!"not a key: {key}"
    | none => .error s!"not hex: {key}"
  | ["start", key, offset] =>
    match parseHex key, natOf offset with
    | some k, some o =>
      if k.length = keyLength ∧ o < 2 ^ 64 then .ok (hex (Record.start.encode k o))
      else .error s!"not a key or an offset: {line}"
    | _, _ => .error s!"not a start: {line}"
  | ["encode", key, offset, seq, id, header, size, crc, groups] =>
    match parseHex key, natOf offset, natOf seq, parseHex id, natOf header, natOf size, natOf crc,
        parseGroups groups with
    | some k, some o, some s, some i, some h, some z, some c, some gs =>
      let commit : Commit := ⟨s, i, gs, h, z, c⟩
      if k.length = keyLength ∧ o < 2 ^ 64 then
        .ok (if commit.ok then hex ((Record.commit commit).encode k o) else "not-ok")
      else .error s!"not a key or an offset: {line}"
    | _, _, _, _, _, _, _, _ => .error s!"not a commit: {line}"
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
      if s < 2 ^ 64 then
        .ok s!"{hex (finalName s)} {hex (tempName s)} {hex (quarantineName s)} {hex (tailName s)}"
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
  let j := journal sampleKey [.commit sample]
  scan (j ++ (((Record.commit sample).encode sampleKey j.length).take 12)) ==
    ⟨[.format sampleKey, .commit sample], .torn j.length⟩
/-- A frame that checks but is no record is corruption even last: a journal of a later format,
whose first frame still carries a key. -/
def regression_881 : Bool :=
  scan (frame sampleKey 0 formatType (journalTitle ++ [BitVec.ofNat 8 2] ++ sampleKey)) ==
    ⟨[], .corrupt 0 .notARecord⟩
/-- Article numbers are those RFC 3977 §6 allows, 1 to 2,147,483,647. -/
def regression_882 : Bool :=
  let numbered (n : Nat) : Commit := { sample with groups := [⟨ascii "local.test", n⟩] }
  !(numbered 0).ok && (numbered 1).ok && (numbered (2 ^ 31 - 1)).ok && !(numbered (2 ^ 31)).ok
/-- An append cut short and filled with zeros reads as a torn tail: its end mark is gone. -/
def regression_883 : Bool :=
  let j := journal sampleKey [.commit sample]
  let f := (Record.commit sample).encode sampleKey j.length
  scan (j ++ f.take 20 ++ List.replicate (f.length - 20) 0) ==
    ⟨[.format sampleKey, .commit sample], .torn j.length⟩
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
/-- SipHash-2-4 under the key 00 to 0f, as the authors' reference implementation gives it for the
empty message and for the octets 00 to 0e. -/
def regression_886 : Bool := (SipHash.tag sampleKey []).toNat == 0x726FDB47DD0E0E31
def regression_887 : Bool :=
  (SipHash.tag sampleKey (bytesOf (List.range 15))).toNat == 0xA129CA6149BE45E5
/-- A frame copied to another place in the journal does not check there: its tag names its
offset. -/
def regression_888 : Bool :=
  let j := journal sampleKey [.commit sample]
  let f := (Record.commit sample).encode sampleKey (journal sampleKey []).length
  scan (j ++ f) == ⟨[.format sampleKey, .commit sample], .torn j.length⟩
/-- A journal that does not begin with its format has no key to check its first frame with. -/
def regression_889 : Bool :=
  let f := (Record.commit sample).encode sampleKey 0
  scan (f ++ f) == ⟨[], .corrupt 0 .tag⟩
/-- A start reads back as one, a commit after it too, and its frame is fourteen octets. -/
def regression_890 : Bool :=
  scan (journal sampleKey [.start, .commit sample, .start]) ==
      ⟨[.format sampleKey, .start, .commit sample, .start], .clean⟩ &&
    (Record.start.encode sampleKey firstFrame).length == 14
/-- A byte changed in a record with another after it is corruption, not a torn tail. -/
def regression_891 : Bool :=
  let j := journal sampleKey [.commit sample, .commit { sample with seq := 2 }]
  scan (j.set (firstFrame + headerLength) 7) == ⟨[.format sampleKey], .corrupt firstFrame .tag⟩
/-- A first frame of another type does not carry a key, whatever its payload holds. -/
def regression_892 : Bool :=
  scan (frame sampleKey 0 commitType (magic ++ sampleKey)) == ⟨[], .torn 0⟩

end DN.News.JournalModel
