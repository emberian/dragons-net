-- SPDX-License-Identifier: AGPL-3.0-or-later
import DN.News.ArticleSpec
import DN.News.FrameModel

/-!
# DN.News.ArticleModel

The checks of `DN.News.ArticleSpec` run on cases, as `dn-compiler article-model` answers them, a
line each:

    check WALL SEQ RUN CONN IDENTITY RANDOM GROUPS ARTICLE
    format WALL
    parse VALUE

The identity, the random value, the article and a date's value are hex, `-` for none; the groups
are hex separated by commas, `-` for none. `check` answers `refused REASON NAME`, the name in hex
or `-`, or `accepted HEADER MESSAGE-ID GROUPS`; `format` answers the date the server writes for
the wall clock, in hex; `parse` the seconds a date's value says, or `-` if it says none. With a
mutant, the checks run under its rules.
-/

namespace DN.News.ArticleModel

open DN.News.FrameSpec DN.News.ArticleSpec
open DN.News.CommandSpec (ascii)
open DN.News.FrameModel (parseHex hex)

def reason : Refusal → String × Bytes
  | .noHeader => ("no-header", []) | .noSeparator => ("no-separator", [])
  | .headerTooLong => ("header-too-long", []) | .lineTooLong => ("line-too-long", [])
  | .malformed => ("malformed", []) | .injected n => ("injected", n)
  | .traced n => ("traced", n) | .deprecated n => ("deprecated", n)
  | .notOffered n => ("not-offered", n) | .blankLine n => ("blank-line", n)
  | .badField n => ("bad-field", n) | .repeated n => ("repeated", n)
  | .missing n => ("missing", n) | .posted => ("posted", [])
  | .longMessageId n => ("long-message-id", n) | .noSender => ("no-sender", [])
  | .distributionAll => ("distribution-all", []) | .badDate n => ("bad-date", n)
  | .dateAhead n => ("date-ahead", n) | .datePast n => ("date-past", n)
  | .tooManyGroups => ("too-many-groups", []) | .reservedGroup => ("reserved-group", [])
  | .noKnownGroup => ("no-known-group", [])

def groupsText (gs : List Bytes) : String :=
  if gs.isEmpty then "-" else ",".intercalate (gs.map hex)

def parseGroups (s : String) : Option (List Bytes) :=
  if s == "-" then some [] else (s.splitOn ",").mapM parseHex

def verdictText : Verdict → String
  | .refused r => let (w, n) := reason r; s!"refused {w} {hex n}"
  | .accepted a => s!"accepted {hex a.header} {hex a.messageId} {groupsText a.groups}"

/-- The answer to one case, or why the line is not one. -/
def answer (r : Rules) (line : String) : Except String String :=
  match line.splitOn " " with
  | ["check", wall, seq, run, conn, identity, random, groups, article] =>
    match wall.toNat?, seq.toNat?, run.toNat?, conn.toNat?, parseHex identity, parseHex random,
        parseGroups groups, parseHex article with
    | some w, some s, some ru, some c, some i, some ra, some gs, some a =>
      let ctx : Context :=
        { groups := gs, identity := i, wall := w, seq := s, random := ra, run := ru, conn := c }
      if ctx.ok then .ok (verdictText (checkWith r ctx a))
      else .error s!"the context does not fit: {line}"
    | _, _, _, _, _, _, _, _ => .error s!"not a case: {line}"
  | ["format", wall] =>
    match wall.toNat? with
    | some w => .ok (hex (formatDate w))
    | none => .error s!"not a number: {wall}"
  | ["parse", v] =>
    match parseHex v with
    | some bs => .ok (((dateValue bs).map toString).getD "-")
    | none => .error s!"not hex: {v}"
  | _ => .error s!"not a case: {line}"

/-- The answers to every line of `input`, one line each. -/
def runAll (r : Rules) (input : String) : Except String String := do
  let lines := (input.splitOn "\n").filter (!·.isEmpty)
  let answers ← lines.mapM (answer r)
  pure (String.join (answers.map (· ++ "\n")))

/-! ## Examples -/

def says (a : String) : String := verdictText (check sample (ascii a))

/-- A proto-article with only what it may not omit gets every field RFC 5537 §3.5 adds. -/
def regression_859 : Bool :=
  says minimal == "accepted " ++ FrameModel.hex (ascii ("Path: news.example.org!.POSTED!" ++
    "not-for-mail\r\nFrom: a@b.example\r\nNewsgroups: local.test\r\nSubject: hi\r\n" ++
    "Message-ID: <7.5f3a@news.example.org>\r\nDate: Mon, 21 Sep 2026 14:13:20 +0000\r\n" ++
    "Injection-Info: news.example.org; logging-data=1.2\r\n" ++
    "Injection-Date: Mon, 21 Sep 2026 14:13:20 +0000\r\n")) ++ " " ++
    FrameModel.hex (ascii "<7.5f3a@news.example.org>") ++ " " ++ FrameModel.hex (ascii "local.test")
/-- With both Message-ID and Date, no Injection-Date (RFC 5537 §3.5 step 11), and Path goes on
from what it held. -/
def regression_860 : Bool :=
  says ("Path: a.example!not-for-mail\r\nMessage-ID: <x@y.example>\r\n" ++
    "Date: Mon, 21 Sep 2026 14:00:00 +0000\r\n" ++ minimal) ==
    "accepted " ++ FrameModel.hex (ascii ("Path: news.example.org!.POSTED!a.example!" ++
      "not-for-mail\r\nMessage-ID: <x@y.example>\r\nDate: Mon, 21 Sep 2026 14:00:00 +0000\r\n" ++
      "From: a@b.example\r\nNewsgroups: local.test\r\nSubject: hi\r\n" ++
      "Injection-Info: news.example.org; logging-data=1.2\r\n")) ++ " " ++
    FrameModel.hex (ascii "<x@y.example>") ++ " " ++ FrameModel.hex (ascii "local.test")
/-- RFC 5537 §3.2.2's Path, which an injecting agent made. -/
def regression_861 : Bool :=
  says ("Path: foo.isp.example!.SEEN.isp.example!foo-news\r\n" ++
    " !.MISMATCH.2001:DB8:0:0:8:800:200C:417A!bar.isp.example\r\n" ++
    " !!old.site.example!barbaz!!baz.isp.example\r\n" ++
    " !.POSTED.dialup123.baz.isp.example!not-for-mail\r\n" ++ minimal) == "refused posted -"
/-- A day later than the wall clock by 24 hours and a second, and by 24 hours. -/
def regression_862 : Bool :=
  says ("Date: Tue, 22 Sep 2026 14:13:21 +0000\r\n" ++ minimal) ==
    "refused date-ahead " ++ FrameModel.hex (ascii "Date")
def regression_863 : Bool :=
  (says ("Date: Tue, 22 Sep 2026 14:13:20 +0000\r\n" ++ minimal)).startsWith "accepted "
/-- 31 September is no date (RFC 5322 §3.3), nor a Monday that is a Tuesday. -/
def regression_864 : Bool :=
  says ("Date: Thu, 31 Sep 2026 14:13:20 +0000\r\n" ++ minimal) ==
    "refused bad-date " ++ FrameModel.hex (ascii "Date")
def regression_865 : Bool :=
  says ("Date: Mon, 22 Sep 2026 14:13:20 +0000\r\n" ++ minimal) ==
    "refused bad-date " ++ FrameModel.hex (ascii "Date")
/-- A group reserved, and none the server carries. -/
def regression_866 : Bool :=
  says "From: a@b.example\r\nNewsgroups: local.test,example.test\r\nSubject: hi\r\n\r\n" ==
    "refused reserved-group -"
def regression_867 : Bool :=
  says "From: a@b.example\r\nNewsgroups: alt.test\r\nSubject: hi\r\n\r\n" ==
    "refused no-known-group -"
/-- No empty line after the header section (RFC 3977 §3.6). -/
def regression_868 : Bool :=
  says "From: a@b.example\r\nNewsgroups: local.test\r\nSubject: hi\r\n" == "refused no-separator -"
/-- The dates the server writes are read back as the wall clock that wrote them. -/
def regression_869 : Bool :=
  [0, 1790000000, 951782400, 4107542399, 253402300799].all fun w =>
    dateValue (formatDate w) == some (w : Int)

/-- A date with no white space after the comma of its day of the week (RFC 5322 §3.3). -/
def regression_870 : Bool :=
  (says ("Date: Mon,21 Sep 2026 14:12:20 +0000\r\n" ++ minimal)).startsWith "accepted "
/-- Keywords at most once (RFC 5536 §3.2). -/
def regression_871 : Bool :=
  says ("Keywords: a\r\nKeywords: b\r\n" ++ minimal) ==
    "refused repeated " ++ FrameModel.hex (ascii "Keywords")
/-- The date of a Received field, after the `;` no quoted string or comment holds, means a date. -/
def regression_872 : Bool :=
  says ("Received: from \"a;b\" (c;d) by e.example; Mon, 31 Sep 2026 14:12:20 +0000\r\n" ++
    minimal) == "refused bad-date " ++ FrameModel.hex (ascii "Received")

/-- Every rule the checks name is a rule of the grammar. -/
def regression_873 : Bool :=
  ["mailbox", "path-identity", "newsgroup-name"].all fun n =>
    (AbnfRules.names.findIdx? (· == n)).isSome

end DN.News.ArticleModel
