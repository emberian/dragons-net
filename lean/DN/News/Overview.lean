-- SPDX-License-Identifier: AGPL-3.0-or-later
import DN.News.CommandSpec
import DN.News.Journal

/-!
# DN.News.Overview

What OVER and HDR give of an article (RFC 3977 §8), from its file as the store keeps it
(docs/decisions/0005-article-store.md): the header section, lines ending in CRLF, a line that starts
with a dot starting with two, then the empty line and the body. There is no overview database: each
line is made from the article's file, read and checked whole, so every field LIST OVERVIEW.FMT names
is there for every article (§8.2).

A field of the header section is a line that does not start with SP or TAB and the lines after it
that do, its lines joined without their CRLF; its name is what comes before its first colon,
compared without regard to case (§8.5.2), and the first field of a name is the one taken. Its
content is what follows the colon, the SP after it left out — the first octet after the colon once
the lines are joined, as §8.5.2 counts it — and each TAB, NUL, CR and LF made one SP (§8.3.2).
`:bytes` counts the octets of the article as ARTICLE gives it, Xref and the empty line among them, a
CRLF as two, but none of the dots put before a line that starts with one (§8.1.1); `:lines` the lines
of the body (§8.1.2).

The rules a version with one broken shows to matter (`DN.News.SessionMutant`) are the fields of
`Style`, the specification's being the defaults.
-/

namespace DN.News.Overview

open DN.News.FrameSpec (Byte CR LF DOT NUL)
open DN.News.CommandSpec (ascii SP TAB upper decimal crlf)
open DN.News.Journal (Commit Group)

/-- How the fields are taken: the specification's, or with one rule broken. -/
structure Style where
  /-- §8.3.2: the CRLF between a field's lines removed -/
  unfolds : Bool := true
  /-- §8.3.2: a TAB made one SP -/
  spaces : Bool := true
  /-- §8.5.2: names compared without regard to case -/
  caseless : Bool := true
  /-- §8.5.2: the first field of a name taken -/
  firstField : Bool := true
  /-- §8.3.2: the SP after the colon left out -/
  dropsSpace : Bool := true
  /-- §8.1.1: the dots put before lines not counted -/
  unstuffed : Bool := true
  /-- §8.1.1: Xref counted, as ARTICLE gives it -/
  countsXref : Bool := true
  /-- §8.1.2: the lines of the body alone counted -/
  bodyOnly : Bool := true
  /-- §8.3.2, §8.4.2: the overview line ends with Xref whole -/
  xrefField : Bool := true
  /-- §8.5.2: HDR's line for an article that lacks the field -/
  keepsAbsent : Bool := true
  /-- RFC 2980 §2.6, as INN: no XHDR line for an article that lacks the field -/
  skipsAbsent : Bool := true
  /-- RFC 2980 §2.6, as INN: XHDR's line of an article named by its message-id labelled with it -/
  labelsId : Bool := true
  /-- RFC 3977 §3.1.1: the dot put before a header line that starts with one left out -/
  unstuffsHeader : Bool := true
  /-- §8.3.2: Xref in the overview line on one line -/
  unfoldsXref : Bool := true
  /-- §8.1: metadata items named without regard to case -/
  metaCaseless : Bool := true
  deriving DecidableEq, Repr

/-- The lines of the octets, each without its line end; octets after the last LF are no line. -/
def linesOf (bs : List Byte) : List (List Byte) :=
  (bs.splitOn LF).dropLast.map fun l => if l.getLast? == some CR then l.dropLast else l

/-- A line as a reader gets it: the dot put before one that starts with a dot left out. -/
def unstuff : List Byte → List Byte
  | d :: e :: rest => if d == DOT && e == DOT then e :: rest else d :: e :: rest
  | l => l

def isWSP (b : Byte) : Bool := b == SP || b == TAB

/-- The byte in lower case, for ASCII letters. -/
def lower (b : Byte) : Byte := if 65 ≤ b.toNat ∧ b.toNat ≤ 90 then b + 32#8 else b

/-- The fields of a header section's lines: each a line that does not start with SP or TAB and the
lines after it that do, joined without their CRLF; such lines before the first field belong to
none. -/
def fieldsOf (st : Style) (ls : List (List Byte)) : List (List Byte) :=
  (ls.foldl (fun acc l =>
    if l.head?.any isWSP then
      match acc with
      | f :: rest => (f ++ (if st.unfolds then [] else crlf) ++ l) :: rest
      | [] => []
    else l :: acc) []).reverse

/-- A field's name and what follows its first colon, if it has one. -/
def split (f : List Byte) : Option (List Byte × List Byte) :=
  match f.span (· != 58#8) with
  | (name, _ :: rest) => some (name, rest)
  | (_, []) => none

/-- A field's content as §8.3.2 gives it: what follows the colon, the SP after it left out, each
TAB, NUL, CR and LF made one SP. -/
def content (st : Style) (rest : List Byte) : List Byte :=
  let rest := match rest with
    | b :: r => if b == SP && st.dropsSpace then r else b :: r
    | [] => []
  rest.map fun b => if (b == TAB && st.spaces) || b == NUL || b == CR || b == LF then SP else b

/-- **The content of the header section's field named `name`**, the first of that name, if there
is one. -/
def headerValue (st : Style) (header name : List Byte) : Option (List Byte) :=
  let lines := (linesOf header).map fun l => if st.unstuffsHeader then unstuff l else l
  let named := (fieldsOf st lines).filterMap fun f =>
    match split f with
    | some (n, rest) =>
      if (if st.caseless then n.map upper == name.map upper else n == name) then some (content st rest)
      else none
    | none => none
  if st.firstField then named.head? else named.getLast?

/-- The dots put before the lines of a file that start with one. -/
def stuffed (file : List Byte) : Nat := ((linesOf file).filter fun l => l.head? == some DOT).length

/-- `:bytes` of an article whose file is `file`, its Xref field as ARTICLE gives it `xref`. -/
def bytes (st : Style) (file xref : List Byte) : Nat :=
  file.length + (if st.countsXref then xref.length else 0) - (if st.unstuffed then stuffed file else 0)

/-- `:lines`: the lines after the header section of `h` octets and the empty line. -/
def bodyLines (st : Style) (file : List Byte) (h : Nat) : Nat :=
  if st.bodyOnly then (linesOf (file.drop (h + 2))).length else (linesOf file).length

/-- The Xref field whole, as an overview line carries it: the path identity, then each group and
its number, on one line and without its line end (RFC 5536 §3.2.14, RFC 3977 §8.3.2). -/
def xrefFull (identity : List Byte) (gs : List Group) : List Byte :=
  ascii "Xref: " ++ identity ++ gs.flatMap fun g => SP :: g.name ++ ascii ":" ++ decimal g.number

/-- **The overview line of an article** (§8.3.2): the number given, Subject, From, Date,
Message-ID, References, `:bytes` and `:lines`, then Xref whole, TAB between them, the content of a
field the article lacks empty; `xref` is the Xref field as ARTICLE gives it. -/
def line (st : Style) (identity : List Byte) (c : Commit) (file : List Byte) (number : Nat)
    (xref : List Byte) : List Byte :=
  let get (name : String) := (headerValue st (file.take c.headerSize) (ascii name)).getD []
  decimal number ++ TAB :: get "Subject" ++ TAB :: get "From" ++ TAB :: get "Date" ++ TAB ::
    get "Message-ID" ++ TAB :: get "References" ++ TAB :: decimal (bytes st file xref) ++ TAB ::
    decimal (bodyLines st file c.headerSize) ++
    (if st.xrefField then TAB :: (if st.unfoldsXref then xrefFull identity c.groups else xref.dropLast.dropLast)
      else []) ++ crlf

/-- **HDR's content of field `f`** (§8.5.2): `:bytes` and `:lines` as above, of Xref what follows its
name, and of another the content of the article's field of that name; none when it has none. -/
def field (st : Style) (identity : List Byte) (c : Commit) (file xref : List Byte) (f : List Byte) :
    Option (List Byte) :=
  let named (m : String) := if st.metaCaseless then f.map upper == ascii m else f == (ascii m).map lower
  if named ":BYTES" then some (decimal (bytes st file xref))
  else if named ":LINES" then some (decimal (bodyLines st file c.headerSize))
  else if f.map upper == ascii "XREF" then some ((xrefFull identity c.groups).drop 6)
  else headerValue st (file.take c.headerSize) f

/-- HDR's line for an article, `label` and the content, the SP after the label kept when the content
is empty, as INN gives it; XHDR's (RFC 2980 §2.6), none for an article whose field is absent or
empty, as INN gives it. -/
def hdrLine (st : Style) (legacy : Bool) (label : List Byte) (v : Option (List Byte)) : List Byte :=
  let v := v.getD []
  if v.isEmpty && (if legacy then st.skipsAbsent else !st.keepsAbsent) then [] else label ++ SP :: v ++ crlf

/-! ## Worked cases -/

/-- A stored article's header section: a folded Subject with a TAB, a From named in lower case, a
second Keywords and a line that starts with a dot; then the article, a body line starting with one. -/
def sampleHeader : List Byte :=
  ascii "Subject: one\r\n\ttwo\r\nfrom: a@b.example\r\nKeywords: x\r\n..odd: y\r\nKeywords: z\r\n"
def sample : List Byte := sampleHeader ++ ascii "\r\nbody\r\n..dot\r\n"

def sampleCommit : Commit :=
  ⟨1, ascii "<1@b.example>", [⟨ascii "local.test", 3⟩, ⟨ascii "local.other", 7⟩], sampleHeader.length,
    sample.length, 0⟩

/-- The sample's fields, `:bytes` and `:lines`, as the rules above take them. -/
theorem sample_fields :
    sampleHeader.length = 75 ∧ sample.length = 90 ∧
    headerValue {} sampleHeader (ascii "subject") = some (ascii "one two") ∧
    headerValue {} sampleHeader (ascii "From") = some (ascii "a@b.example") ∧
    headerValue {} sampleHeader (ascii "Keywords") = some (ascii "x") ∧
    headerValue {} sampleHeader (ascii ".odd") = some (ascii "y") ∧
    headerValue {} sampleHeader (ascii "Date") = none ∧
    bytes {} sample (List.replicate 10 SP) = 98 ∧ bodyLines {} sample 75 = 2 ∧
    field {} (ascii "news.example") sampleCommit sample [] (ascii "xref") =
      some (ascii "news.example local.test:3 local.other:7") := by
  decide +kernel

/-- The sample's overview line, and HDR's and XHDR's lines of a field it lacks. -/
theorem sample_lines :
    line {} (ascii "news.example") sampleCommit sample 3 (List.replicate 10 SP) =
      ascii "3\tone two\ta@b.example\t\t\t\t98\t2\tXref: news.example local.test:3 local.other:7\r\n" ∧
    hdrLine {} false (ascii "3") (field {} [] sampleCommit sample [] (ascii "Date")) = ascii "3 \r\n" ∧
    hdrLine {} true (ascii "3") (field {} [] sampleCommit sample [] (ascii "Date")) = [] := by
  decide +kernel

end DN.News.Overview
