-- SPDX-License-Identifier: AGPL-3.0-or-later
import DN.News.FrameSpec

/-!
# DN.News.CommandSpec

Which reply a command line gets, written from RFC 3977 and docs/decisions/0003-nntp-slice.md
("What the slice answers"), with nothing of the code that decides it.

A line comes from the framer (`DN.News.FrameSpec.classify`): a command, a malformed line or an
overlong one, and the bytes it keeps. Its words are its runs of bytes other than space and TAB
(§3.1), so a NUL or a CR joined to a keyword makes another word. The checks go in the order 0003
fixes: an empty or white-space-only line is ignored; a
line whose first word is not a command the server has gets 500, whatever else is wrong with it; a
line naming such a command that is malformed, too long or has arguments the command does not
take gets 501. An overlong line is never ignored: only its first bytes are kept, so white space
there says nothing of the rest. Keywords are compared without regard to case (§3.1); the arguments
follow the grammar of §9.8 and the range of article numbers in §6.

With a store (docs/decisions/0005-article-store.md), POST, ARTICLE, BODY, GROUP, NEXT, LAST,
LISTGROUP, LIST, DATE and NEWGROUPS are commands too (`replyIn`), and the session decides what a
well-formed POST gets, what an ARTICLE, HEAD, BODY or STAT finds — by message-id (`lookup`), by
number (`byNumber`) or the current article (`current`) — which group a GROUP or a LISTGROUP selects
(`select`, `listGroup`), where a NEXT or LAST moves (`move`), and what DATE gives (`date`). A
wildmat (§4) matches a name as `wildmatch` says. MODE READER is a command of every server, and the
session decides what it gets (`modeReader`, §5.3.2).

Each rule is shown to matter: a version with it broken (`Mutant`) answers some line otherwise.
-/

namespace DN.News.CommandSpec

open DN.News.FrameSpec

/-- The bytes of an ASCII string. -/
def ascii (s : String) : List Byte := s.toList.map fun c => BitVec.ofNat 8 c.toNat

def SP : Byte := 32#8
def TAB : Byte := 9#8

def isWS (b : Byte) : Bool := b == SP || b == TAB

/-- The words of `l` read so far, the current one reversed in `cur`. -/
def wordsFrom : List Byte → List Byte → List (List Byte)
  | [], cur => if cur.isEmpty then [] else [cur.reverse]
  | b :: rest, cur =>
    if isWS b then (if cur.isEmpty then wordsFrom rest [] else cur.reverse :: wordsFrom rest [])
    else wordsFrom rest (b :: cur)

/-- The words of a line: its runs of bytes other than SP and TAB, in order. -/
def words (l : List Byte) : List (List Byte) := wordsFrom l []

/-- The byte in upper case, for ASCII letters. -/
def upper (b : Byte) : Byte := if 97 ≤ b.toNat ∧ b.toNat ≤ 122 then b - 32#8 else b

inductive Cmd | capabilities | help | quit | head | stat | post | article | body | group | next | last
  | listgroup | list | date | newgroups | mode
  deriving DecidableEq, Repr

/-- The command a word names, in any case. -/
def command? (w : List Byte) : Option Cmd :=
  let u := w.map upper
  if u = ascii "CAPABILITIES" then some .capabilities
  else if u = ascii "HELP" then some .help
  else if u = ascii "QUIT" then some .quit
  else if u = ascii "HEAD" then some .head
  else if u = ascii "STAT" then some .stat
  else if u = ascii "MODE" then some .mode
  else none

/-- The command a word names, POST, ARTICLE, BODY, GROUP, NEXT, LAST, LISTGROUP, LIST, DATE and NEWGROUPS
among them when the server has a store. -/
def commandIn (offered : Bool) (w : List Byte) : Option Cmd :=
  let u := w.map upper
  if offered && u = ascii "POST" then some .post
  else if offered && u = ascii "ARTICLE" then some .article
  else if offered && u = ascii "BODY" then some .body
  else if offered && u = ascii "GROUP" then some .group
  else if offered && u = ascii "NEXT" then some .next
  else if offered && u = ascii "LAST" then some .last
  else if offered && u = ascii "LISTGROUP" then some .listgroup
  else if offered && u = ascii "LIST" then some .list
  else if offered && u = ascii "DATE" then some .date
  else if offered && u = ascii "NEWGROUPS" then some .newgroups
  else command? w

def isDigit (b : Byte) : Bool := 48 ≤ b.toNat && b.toNat ≤ 57
def isAlpha (b : Byte) : Bool := (65 ≤ b.toNat && b.toNat ≤ 90) || (97 ≤ b.toNat && b.toNat ≤ 122)

/-- The number the digits of `w` write. -/
def value (w : List Byte) : Nat := w.foldl (fun n b => 10 * n + (b.toNat - 48)) 0

/-- An article number: one to sixteen digits (§9.8), no more than 2,147,483,647 (§6); zero, which
stands for no article, is still written as a number. -/
def isArticleNumber (w : List Byte) : Bool :=
  1 ≤ w.length && w.length ≤ 16 && w.all isDigit && value w ≤ 2147483647

/-- `A-NOTGT` of §9.8: a printable US-ASCII byte other than `>`. -/
def isNotGt (b : Byte) : Bool := (33 ≤ b.toNat && b.toNat ≤ 61) || (63 ≤ b.toNat && b.toNat ≤ 126)

/-- A message-id: `"<" 1*248A-NOTGT ">"` (§9.8), so 3 to 250 octets (§3.6). -/
def isMessageId (w : List Byte) : Bool :=
  3 ≤ w.length && w.length ≤ 250 && w.head? == some (ascii "<").head! &&
    w.getLast? == some (ascii ">").head! && ((w.drop 1).dropLast).all isNotGt

/-- `wildmat-exact` of §9.8 among US-ASCII bytes: printable, but for `!`, `*`, `,`, `?`, `[`, `\` and
`]`. -/
def isExactAscii (b : Byte) : Bool :=
  (34 ≤ b.toNat && b.toNat ≤ 41) || b.toNat == 43 || (45 ≤ b.toNat && b.toNat ≤ 62) ||
    (64 ≤ b.toNat && b.toNat ≤ 90) || (94 ≤ b.toNat && b.toNat ≤ 126)

def inRange (lo hi : Nat) (b : Byte) : Bool := lo ≤ b.toNat && b.toNat ≤ hi
def isTail : Byte → Bool := inRange 128 191

/-- The length of the character of UTF-8 the bytes start with, as RFC 3629 §4 writes them, if they
start with one. -/
def charLength : List Byte → Option Nat
  | [] => none
  | a :: rest =>
    if a.toNat < 128 then some 1
    else match rest with
      | b :: r =>
        if inRange 194 223 a then (if isTail b then some 2 else none)
        else match r with
          | c :: r' =>
            if a.toNat == 224 then (if inRange 160 191 b && isTail c then some 3 else none)
            else if inRange 225 236 a || inRange 238 239 a then (if isTail b && isTail c then some 3 else none)
            else if a.toNat == 237 then (if inRange 128 159 b && isTail c then some 3 else none)
            else match r' with
              | d :: _ =>
                if a.toNat == 240 then (if inRange 144 191 b && isTail c && isTail d then some 4 else none)
                else if inRange 241 243 a then (if isTail b && isTail c && isTail d then some 4 else none)
                else if a.toNat == 244 then (if inRange 128 143 b && isTail c && isTail d then some 4 else none)
                else none
              | [] => none
          | [] => none
      | [] => none

/-- The characters of UTF-8 the bytes are, each by its octets, if they are UTF-8; each takes at least
one byte, so `fuel` of as many as the bytes is enough. -/
def charsFrom : Nat → List Byte → Option (List (List Byte))
  | _, [] => some []
  | 0, _ :: _ => none
  | fuel + 1, bs => do
    let k ← charLength bs
    return bs.take k :: (← charsFrom fuel (bs.drop k))

def chars (bs : List Byte) : Option (List (List Byte)) := charsFrom bs.length bs

/-- Whether the bytes are `wildmat-exact` characters (§9.8): such US-ASCII bytes, or UTF-8 of
characters past US-ASCII. -/
def exactChars (bs : List Byte) : Bool :=
  (chars bs).any (·.all fun c => c.length != 1 || c.all isExactAscii)

/-- A newsgroup name: `1*wildmat-exact` (§9.8). -/
def isGroupName (w : List Byte) : Bool := !w.isEmpty && exactChars w

/-- No group the store carries has a longer name (docs/decisions/0005-article-store.md, "Bounds"). -/
def groupNameMax : Nat := 64

/-- A keyword: `ALPHA 2*(ALPHA / DIGIT / "." / "-")` (§9.8). -/
def isKeyword : List Byte → Bool
  | a :: rest => isAlpha a && 2 ≤ rest.length &&
      rest.all fun b => isAlpha b || isDigit b || b == 46#8 || b == 45#8
  | [] => false

/-- The largest article number (§6). -/
def numberMax : Nat := 2147483647

/-- A range of article numbers (§6.1.2.2, §9.8): a number, a number and all after it, or two numbers
and those between: the lowest and the highest. -/
def range? (w : List Byte) : Option (Nat × Nat) :=
  match w.splitOn 45#8 with
  | [a] => if isArticleNumber a then some (value a, value a) else none
  | [a, []] => if isArticleNumber a then some (value a, numberMax) else none
  | [a, b] => if isArticleNumber a && isArticleNumber b then some (value a, value b) else none
  | _ => none

/-- The number the two digits at `k` write. -/
def twoAt (w : List Byte) (k : Nat) : Nat := value ((w.drop k).take 2)

/-- A date of NEWGROUPS (§7.3.2): `yymmdd` or `yyyymmdd`, the century from 19 to 99, the month from
01 to 12, the day from 01 to 31. -/
def isDate (w : List Byte) : Bool :=
  w.all isDigit && (w.length == 6 || (w.length == 8 && 19 ≤ twoAt w 0)) &&
    1 ≤ twoAt w (w.length - 4) && twoAt w (w.length - 4) ≤ 12 &&
    1 ≤ twoAt w (w.length - 2) && twoAt w (w.length - 2) ≤ 31

/-- A time of NEWGROUPS: `hhmmss`, the hour below 24, the minute below 60, the second at most 60. -/
def isTime (w : List Byte) : Bool :=
  w.length == 6 && w.all isDigit && twoAt w 0 ≤ 23 && twoAt w 2 ≤ 59 && twoAt w 4 ≤ 60

/-! ## Wildmats (§4) -/

/-- An item of a wildmat's pattern: `*`, `?`, or a `wildmat-exact` character by its octets. -/
inductive Item | star | one | exact (c : List Byte)
  deriving DecidableEq, Repr

/-- A wildmat: its patterns in order, each with whether `!` negates it. -/
abbrev Wildmat := List (Bool × List Item)

def itemOf (c : List Byte) : Option Item :=
  if c = ascii "*" then some .star else if c = ascii "?" then some .one
  else if c.length != 1 || c.all isExactAscii then some (.exact c) else none

/-- A pattern of one or more items, negated by a `!` before it where `negates` allows one. -/
def patternOf (negates : Bool) (cs : List (List Byte)) : Option (Bool × List Item) :=
  let (neg, rest) := if negates && cs.head? == some (ascii "!") then (true, cs.tail) else (false, cs)
  if rest.isEmpty then none else return (neg, ← rest.mapM itemOf)

/-- A wildmat (§4.1): patterns separated by `,`, those after the first each negated by a `!` or
not. -/
def wildmat? (w : List Byte) : Option Wildmat := do
  match (← chars w).splitOn (ascii ",") with
  | first :: rest => return (← patternOf false first) :: (← rest.mapM (patternOf true))
  | [] => none

/-- The places in the characters `s` an item can reach from the places `from_`. -/
def reach (s : List (List Byte)) (from_ : List Nat) : Item → List Nat
  | .exact c => from_.filterMap fun k => if s[k]? == some c then some (k + 1) else none
  | .one => from_.filterMap fun k => if k < s.length then some (k + 1) else none
  | .star =>
    match from_.min? with
    | some k => List.range' k (s.length + 1 - k)
    | none => []

/-- A pattern matches the characters `s` when its items, in order, take all of them (§4.2). -/
def patternMatches (s : List (List Byte)) (p : List Item) : Bool := (p.foldl (reach s) [0]).contains s.length

/-- What a wildmat says of `s` once a pattern is matched: the pattern decides when it matches. -/
def decides (s : List (List Byte)) (r : Option Bool) (x : Bool × List Item) : Option Bool :=
  if patternMatches s x.2 then some !x.1 else r

/-- **Whether a wildmat matches a name** (§4.2): the rightmost pattern that matches decides, a negated
one against; with none matching, no match. -/
def wildmatch (w : Wildmat) (name : List Byte) : Bool :=
  match chars name with
  | some s => (w.foldl (decides s) none).getD false
  | none => false

inductive Reply
  /-- no reply: an empty or white-space-only line -/
  | ignore
  /-- 101 and the capability list -/
  | capabilities
  /-- 100 and the help text -/
  | help
  /-- 205, then the connection closes -/
  | quit
  /-- a MODE READER; the session decides. A server that does not advertise READER answers 502, then
  the connection closes (§5.3.2) -/
  | modeReader
  /-- 200 and 201 to a MODE READER of a server that is not mode-switching and advertises READER: as
  the greeting, whether the client may post (§5.3.2) -/
  | readerPosting
  | readerNoPosting
  /-- the capabilities of a server with a store that does not offer POST: READER and LIST's
  keywords (§3.3.2, §7.6.2) -/
  | capabilitiesReader
  /-- 412: no newsgroup selected -/
  | noGroup
  /-- 430: no article with that message-id -/
  | noSuchId
  /-- 500: not a command the server has -/
  | unknown
  /-- 501: a command the server has, but not well formed -/
  | syntax
  /-- 340: send the article (RFC 3977 §6.3.1), for a well-formed POST; the session decides -/
  | post
  /-- 240 and 441: the article taken, or not -/
  | posted
  | failed
  /-- 440: the connection was not greeted as one that may post -/
  | notPermitted
  /-- 403: the store has stopped accepting (§3.2.1) -/
  | unavailable
  /-- the capabilities and the help text of a server that offers POST -/
  | capabilitiesPost
  | helpPost
  /-- an ARTICLE, HEAD, BODY or STAT of the article with this message-id, number 0, or with this
  number in the selected group, with a store; the session decides, and says what a store without
  the article says -/
  | lookup (c : Cmd) (n : Nat) (id : List Byte)
  /-- 223: the store holds the article, with its number in the selected group or 0 (§6.2.1.2) -/
  | stat (n : Nat) (id : List Byte)
  /-- 403: the article's file failed a read or its check before anything of it was sent -/
  | unreadable
  /-- a GROUP of a well-formed name a group the store carries may have; the session decides -/
  | select (g : List Byte)
  /-- an ARTICLE, HEAD, BODY or STAT by number, or of the current article, and a NEXT (`true`) or
  LAST; the session decides -/
  | byNumber (c : Cmd) (n : Nat)
  | current (c : Cmd)
  | move (forward : Bool)
  /-- 211: the group selected, with its count of articles and its lowest and highest numbers -/
  | selected (count low high : Nat) (g : List Byte)
  /-- 411: no such group -/
  | noSuchGroup
  /-- 420: the current article number is invalid -/
  | noCurrent
  /-- 421 and 422: no next article, and no previous one, in the group -/
  | noNext
  | noPrevious
  /-- 423: no article with that number in the group -/
  | noNumber
  /-- a LISTGROUP of the group named or the selected one, of the numbers from `lo` to `hi`; the
  session decides -/
  | listGroup (g : Option (List Byte)) (lo hi : Nat)
  /-- 211 as GROUP's, the numbers of the group's articles from `lo` to `hi` to follow -/
  | listed (count low high : Nat) (g : List Byte) (lo hi : Nat)
  /-- 215, the groups the wildmat matches, or all, to follow, as LIST ACTIVE writes them -/
  | active (w : Option Wildmat)
  /-- 215 and an empty list: no group has a description (§7.6.6) -/
  | newsgroups
  /-- 231 and an empty list: no group has a time it was created (§7.3.2) -/
  | newGroups
  /-- a DATE; the session decides -/
  | date
  /-- 111 and the date and time these digits write -/
  | time (digits : List Byte)
  deriving DecidableEq, Repr

/-- The reply to a command with these arguments, on a well-formed line. -/
def answer : Cmd → List (List Byte) → Reply
  | .capabilities, [] => .capabilities
  | .capabilities, [k] => if isKeyword k then .capabilities else .syntax
  | .help, [] => .help
  | .quit, [] => .quit
  | .mode, [k] => if k.map upper = ascii "READER" then .modeReader else .syntax
  | .head, [] | .stat, [] => .noGroup
  | .head, [a] | .stat, [a] =>
    if isArticleNumber a then .noGroup else if isMessageId a then .noSuchId else .syntax
  | .post, [] => .post
  | _, _ => .syntax

/-- The reply with a store: ARTICLE and BODY take an argument as HEAD does; a message-id is looked up,
a number in the selected group, and no argument means the current article. A GROUP or LISTGROUP of a
name no group the store carries can have is answered 411 at once. LISTGROUP's range is one of
`range?`; LIST's keyword ACTIVE, the one it takes without any, or NEWSGROUPS, in any case and each
with a wildmat or none; NEWGROUPS's date and time are `isDate` and `isTime`, `GMT` after them or not,
in any case (§3.1, §7.3, §7.6). -/
def answerIn (c : Cmd) (args : List (List Byte)) : Reply :=
  match c, args with
  | .article, [] | .body, [] | .head, [] | .stat, [] => .current c
  | .article, [a] | .body, [a] | .head, [a] | .stat, [a] =>
    if isArticleNumber a then .byNumber c (value a)
    else if isMessageId a then .lookup c 0 a else .syntax
  | .group, [g] =>
    if !isGroupName g then .syntax else if g.length ≤ groupNameMax then .select g else .noSuchGroup
  | .next, [] => .move true
  | .last, [] => .move false
  | .listgroup, [] => .listGroup none 1 numberMax
  | .listgroup, g :: rest =>
    match (match rest with | [] => some (1, numberMax) | [r] => range? r | _ => none) with
    | some (lo, hi) =>
      if !isGroupName g then .syntax else if g.length ≤ groupNameMax then .listGroup (some g) lo hi
      else .noSuchGroup
    | none => .syntax
  | .list, [] => .active none
  | .list, k :: rest =>
    match (match rest with | [] => some none | [w] => (wildmat? w).map some | _ => none) with
    | some w =>
      if k.map upper = ascii "ACTIVE" then .active w else if k.map upper = ascii "NEWSGROUPS" then .newsgroups
      else .syntax
    | none => .syntax
  | .date, [] => .date
  | .newgroups, d :: t :: rest =>
    if isDate d && isTime t && (rest.isEmpty || rest.map (·.map upper) == [ascii "GMT"]) then .newGroups
    else .syntax
  | _, _ => answer c args

/-- **The reply to a line**, POST, ARTICLE, BODY, GROUP, NEXT and LAST commands when `offered`. -/
def replyIn (offered : Bool) (l : Line) : Reply :=
  match words l.kept with
  | [] => if l.kind = .overlong then .unknown else .ignore
  | w :: args =>
    match commandIn offered w with
    | none => .unknown
    | some c => if l.kind = .command then (if offered then answerIn c args else answer c args)
      else .syntax

/-- The reply to a line of a server without a store. -/
def reply : Line → Reply := replyIn false

/-! ## What each reply says -/

/-- What the server says of itself: the revision it was built from and the address of its source,
which AGPL-3.0 §13 asks it to offer. -/
structure Identity where
  revision : List Byte
  source : List Byte

/-- A printable US-ASCII byte other than space. -/
def isVisible (b : Byte) : Bool := 33 ≤ b.toNat && b.toNat ≤ 126

/-- A revision and an address that fit the replies: visible bytes only, so neither can end a line
or start one with a dot, and short enough that every reply fits one action. -/
def Identity.ok (i : Identity) : Bool :=
  1 ≤ i.revision.length && i.revision.length ≤ 64 && i.revision.all isVisible &&
    1 ≤ i.source.length && i.source.length ≤ 200 && i.source.all isVisible

def crlf : List Byte := [CR, LF]

/-- A number in decimal digits. -/
def decimal (n : Nat) : List Byte := ascii (toString n)

theorem decimal_length (n : Nat) (h : n < 10 ^ 10) : (decimal n).length ≤ 10 := by
  simp only [decimal, ascii, List.length_map, Nat.toString_eq_ofList_toDigits, String.toList_ofList]
  exact (Nat.length_toDigits_le_iff (by decide) (by decide)).mpr h

/-! The fixed parts of the replies that carry the identity. -/
def greetingHead : List Byte := ascii "201 dragons-net "
def greetingMid : List Byte := ascii " ready, no posting; source code at "
def capabilitiesHead : List Byte :=
  ascii "101 Capability list:\r\nVERSION 2\r\nIMPLEMENTATION dragons-net "
def helpHead : List Byte :=
  ascii "100 Help text follows\r\nCAPABILITIES [keyword]\r\nHEAD [message-ID|number]\r\n" ++
    ascii "HELP\r\nQUIT\r\nSTAT [message-ID|number]\r\ndragons-net "
def helpMid : List Byte := ascii " is free software under the GNU AGPL; source code at "
def blockEnd : List Byte := ascii "\r\n.\r\n"
def greetingPostHead : List Byte := ascii "200 dragons-net "
def greetingPostMid : List Byte := ascii " ready, posting allowed; source code at "
def capabilitiesPostTail : List Byte := ascii "\r\nPOST"
def capabilitiesReaderTail : List Byte := ascii "\r\nREADER\r\nLIST ACTIVE NEWSGROUPS"
def helpPostHead : List Byte :=
  ascii "100 Help text follows\r\nARTICLE, BODY, HEAD, STAT [message-ID|number]\r\n" ++
    ascii "CAPABILITIES [keyword]\r\nDATE\r\nGROUP newsgroup\r\nHELP\r\nLAST\r\nLIST\r\nLISTGROUP\r\n" ++
    ascii "NEWGROUPS\r\nNEXT\r\nPOST\r\nQUIT\r\n" ++
    ascii "dragons-net "

/-- The greeting (§5.1): posting is not allowed, and the source is offered. -/
def greeting (i : Identity) : List Byte :=
  greetingHead ++ i.revision ++ greetingMid ++ i.source ++ crlf

/-- The greeting of a connection that may post. -/
def greetingPost (i : Identity) : List Byte :=
  greetingPostHead ++ i.revision ++ greetingPostMid ++ i.source ++ crlf

/-- The bytes of a reply; a multi-line one ends with its terminating dot line (§3.1.1). -/
def text (i : Identity) : Reply → List Byte
  | .ignore => []
  | .capabilities => capabilitiesHead ++ i.revision ++ blockEnd
  | .help => helpHead ++ i.revision ++ helpMid ++ i.source ++ blockEnd
  | .quit => ascii "205 Bye\r\n"
  | .modeReader => ascii "502 Reading service unavailable\r\n"
  | .readerPosting => ascii "200 Posting allowed\r\n"
  | .readerNoPosting => ascii "201 Posting prohibited\r\n"
  | .capabilitiesReader => capabilitiesHead ++ i.revision ++ capabilitiesReaderTail ++ blockEnd
  | .noGroup => ascii "412 No newsgroup selected\r\n"
  | .noSuchId => ascii "430 No article with that message-id\r\n"
  | .unknown => ascii "500 Unknown command\r\n"
  | .syntax => ascii "501 Syntax error\r\n"
  | .post => ascii "340 Send article to be posted\r\n"
  | .posted => ascii "240 Article received OK\r\n"
  | .failed => ascii "441 Posting failed\r\n"
  | .notPermitted => ascii "440 Posting not permitted\r\n"
  | .unavailable => ascii "403 Not accepting articles\r\n"
  | .capabilitiesPost =>
    capabilitiesHead ++ i.revision ++ capabilitiesReaderTail ++ capabilitiesPostTail ++ blockEnd
  | .helpPost => helpPostHead ++ i.revision ++ helpMid ++ i.source ++ blockEnd
  | .lookup _ _ _ => ascii "430 No article with that message-id\r\n"
  | .stat n id => ascii "223 " ++ decimal n ++ SP :: id ++ crlf
  | .unreadable => ascii "403 Article not readable\r\n"
  | .selected count low high g | .listed count low high g _ _ =>
    ascii "211 " ++ decimal count ++ SP :: decimal low ++ SP :: decimal high ++ SP :: g ++ crlf
  | .active _ => ascii "215 List of newsgroups follows\r\n"
  | .newsgroups => ascii "215 Information follows\r\n.\r\n"
  | .newGroups => ascii "231 List of new newsgroups follows\r\n.\r\n"
  | .time d => ascii "111 " ++ d ++ crlf
  | .noSuchGroup => ascii "411 No such newsgroup\r\n"
  | .noCurrent => ascii "420 Current article number is invalid\r\n"
  | .noNext => ascii "421 No next article in this group\r\n"
  | .noPrevious => ascii "422 No previous article in this group\r\n"
  | .noNumber => ascii "423 No article with that number\r\n"
  | .select _ => ascii "411 No such newsgroup\r\n"
  | .byNumber _ _ | .current _ | .move _ | .listGroup .. => ascii "412 No newsgroup selected\r\n"
  | .date => ascii "500 Unknown command\r\n"

/-- The first line of an article sent (§6.2): 220, 221 or 222, its number in the selected group or
0, and the message-id. -/
def found (c : Cmd) (n : Nat) (id : List Byte) : List Byte :=
  ascii (match c with | .head => "221 " | .body => "222 " | _ => "220 ") ++ decimal n ++ SP :: id ++ crlf

/-- The selected group after a reply: a GROUP's or a LISTGROUP's that succeeds; and the current article
number: the first of a group selected, invalid in an empty one, an article STAT found by number or
moved to.
An article to be read is made current once the read answers (`SessionSpec.progressRead`). -/
def Reply.groupAfter : Reply → Option (List Byte) → Option (List Byte)
  | .selected _ _ _ g, _ | .listed _ _ _ g _ _, _ => some g
  | _, g => g
def Reply.currentAfter : Reply → Nat → Nat
  | .selected count low _ _, _ | .listed count low _ _ _ _, _ => if count = 0 then 0 else low
  | .stat n _, k => if n = 0 then k else n
  | _, k => k

/-- A reply's message-id is one a store holds, 250 octets at most (§3.6); its numbers are article
numbers or counts no larger; its group's name is one a store may carry; a date has at most sixty
digits. -/
def Reply.bounded : Reply → Bool
  | .lookup _ n id | .stat n id => id.length ≤ 250 && n ≤ numberMax
  | .byNumber _ n => n ≤ numberMax
  | .select g => g.length ≤ groupNameMax
  | .selected count low high g | .listed count low high g _ _ =>
    count ≤ numberMax && low ≤ numberMax && high ≤ numberMax && g.length ≤ groupNameMax
  | .time d => d.length ≤ 60
  | _ => true

theorem answer_bounded (c : Cmd) (args : List (List Byte)) : (answer c args).bounded = true := by
  unfold answer
  repeat (first | rfl | split)

/-- A message-id looked up is one, 250 octets at most; a number, an article number; a group's name,
one a store may carry. -/
theorem replyIn_bounded (offered : Bool) (l : Line) : (replyIn offered l).bounded = true := by
  unfold replyIn
  split
  · split <;> rfl
  · split
    · rfl
    · split
      · split
        · unfold answerIn
          split <;> (repeat' split) <;>
            first | exact answer_bounded .. | simp_all [Reply.bounded, isMessageId, isArticleNumber, numberMax]
        · exact answer_bounded ..
      · rfl

/-- The most bytes one action carries. -/
def actionData : Nat := 512

theorem parts_short :
    greetingHead.length ≤ 16 ∧ greetingMid.length ≤ 35 ∧ capabilitiesHead.length ≤ 60 ∧
      helpHead.length ≤ 132 ∧ helpMid.length ≤ 53 ∧ blockEnd.length = 5 ∧ crlf.length = 2 ∧
      greetingPostHead.length ≤ 16 ∧ greetingPostMid.length ≤ 40 ∧
      capabilitiesPostTail.length ≤ 6 ∧ helpPostHead.length ≤ 187 ∧ capabilitiesReaderTail.length ≤ 32 ∧
      ∀ r, r ≠ .capabilities → r ≠ .help → r ≠ .capabilitiesPost → r ≠ .helpPost → r ≠ .capabilitiesReader →
        (∀ n id, r ≠ .stat n id) → (∀ count low high g, r ≠ .selected count low high g) →
        (∀ count low high g lo hi, r ≠ .listed count low high g lo hi) → (∀ d, r ≠ .time d) →
        ∀ i, (text i r).length ≤ 40 := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, rfl, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro r h1 h2 h3 h4 h9 h5 h6 h7 h8 i
  cases r <;> first
    | exact absurd rfl h1 | exact absurd rfl h2 | exact absurd rfl h3 | exact absurd rfl h4
    | exact absurd rfl h9
    | exact absurd rfl (h5 _ _) | exact absurd rfl (h6 _ _ _ _) | exact absurd rfl (h7 _ _ _ _ _ _)
    | exact absurd rfl (h8 _) | (simp only [text]; decide +kernel)

/-- **Every reply, and the greeting, fits one action** when the identity fits. -/
theorem greeting_fits (i : Identity) (h : i.ok = true) :
    (greeting i).length ≤ actionData ∧ (greetingPost i).length ≤ actionData := by
  simp only [Identity.ok, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨h1, h2, _, _, _, _, _, h8, h9, _⟩ := parts_short
  simp only [greeting, greetingPost, List.length_append, actionData]
  omega

theorem text_fits (i : Identity) (h : i.ok = true) (r : Reply) (hr : r.bounded = true) :
    (text i r).length ≤ actionData := by
  simp only [Identity.ok, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨_, _, h3, h4, h5, h6, _, _, _, h10, h11, h13, h12⟩ := parts_short
  have hd : ∀ n, n ≤ numberMax → (decimal n).length ≤ 10 := fun n hn =>
    decimal_length n (by simp only [numberMax] at hn; omega)
  by_cases hl : ∃ count low high g lo hi, r = .listed count low high g lo hi
  · obtain ⟨count, low, high, g, lo, hi, rfl⟩ := hl
    simp only [Reply.bounded, Bool.and_eq_true, decide_eq_true_eq, groupNameMax] at hr
    have := hd count hr.1.1.1
    have := hd low hr.1.1.2
    have := hd high hr.1.2
    simp only [text, List.length_append, List.length_cons, actionData, crlf, List.length_nil]
    have : (ascii "211 ").length = 4 := by decide +kernel
    omega
  replace hl : ∀ count low high g lo hi, r ≠ .listed count low high g lo hi :=
    fun count low high g lo hi e => hl ⟨count, low, high, g, lo, hi, e⟩
  by_cases ht : ∃ d, r = .time d
  · obtain ⟨d, rfl⟩ := ht
    simp only [Reply.bounded, decide_eq_true_eq] at hr
    simp only [text, List.length_append, actionData, crlf, List.length_cons, List.length_nil]
    have : (ascii "111 ").length = 4 := by decide +kernel
    omega
  replace ht : ∀ d, r ≠ .time d := fun d e => ht ⟨d, e⟩
  by_cases hs : ∃ n id, r = .stat n id
  · obtain ⟨n, id, rfl⟩ := hs
    simp only [Reply.bounded, Bool.and_eq_true, decide_eq_true_eq] at hr
    have := hd n hr.2
    simp only [text, List.length_append, List.length_cons, actionData, crlf, List.length_nil]
    have : (ascii "223 ").length = 4 := by decide +kernel
    omega
  replace hs : ∀ n id, r ≠ .stat n id := fun n id e => hs ⟨n, id, e⟩
  by_cases hg : ∃ count low high g, r = .selected count low high g
  · obtain ⟨count, low, high, g, rfl⟩ := hg
    simp only [Reply.bounded, Bool.and_eq_true, decide_eq_true_eq, groupNameMax] at hr
    have := hd count hr.1.1.1
    have := hd low hr.1.1.2
    have := hd high hr.1.2
    simp only [text, List.length_append, List.length_cons, actionData, crlf, List.length_nil]
    have : (ascii "211 ").length = 4 := by decide +kernel
    omega
  replace hg : ∀ count low high g, r ≠ .selected count low high g :=
    fun count low high g e => hg ⟨count, low, high, g, e⟩
  by_cases hc : r = .capabilities
  · subst hc; simp only [text, List.length_append, actionData]; omega
  by_cases hh : r = .help
  · subst hh; simp only [text, List.length_append, actionData]; omega
  by_cases hcp : r = .capabilitiesPost
  · subst hcp; simp only [text, List.length_append, actionData]; omega
  by_cases hhp : r = .helpPost
  · subst hhp; simp only [text, List.length_append, actionData]; omega
  by_cases hcr : r = .capabilitiesReader
  · subst hcr; simp only [text, List.length_append, actionData]; omega
  have := h12 r hc hh hcp hhp hcr hs hg hl ht i
  simp only [actionData]; omega

/-! ## Every rule matters -/

inductive Mutant
  | none
  /-- keywords compared with regard to case -/
  | caseSensitive
  /-- TAB not taken as white space -/
  | tabNotSpace
  /-- a white-space-only line answered -/
  | blankAnswered
  /-- an overlong line with no word ignored -/
  | overlongBlankIgnored
  /-- a malformed or overlong line naming a command answered as well formed -/
  | badLineAccepted
  /-- an unknown command on a malformed line taken for a syntax error -/
  | unknownAsSyntax
  /-- extra arguments ignored -/
  | extraArgsIgnored
  /-- an article number of any size -/
  | numberUnbounded
  /-- a message-id of any length -/
  | messageIdUnbounded
  /-- a keyword of two letters -/
  | shortKeyword
  /-- zero not taken for an article number -/
  | zeroRejected
  /-- a message-id answered as a number is -/
  | idAsNumber
  /-- HELP and QUIT answered with arguments -/
  | argsIgnored
  /-- a message-id of any bytes between its brackets -/
  | idAnyByte
  /-- a keyword that starts with a digit, a dot or a hyphen -/
  | keywordAnyStart
  /-- an article number of more than sixteen digits -/
  | moreDigits
  /-- an empty line answered -/
  | emptyAnswered
  /-- MODE's argument READER compared with regard to case -/
  | readerCaseSensitive
  /-- MODE with any one word answered as MODE READER -/
  | modeAnyWord
  /-- MODE READER answered as such with more arguments after it -/
  | modeArgsIgnored
  deriving DecidableEq, Repr

def isWSM (m : Mutant) (b : Byte) : Bool := b == SP || (b == TAB && m != .tabNotSpace)

def wordsFromM (m : Mutant) : List Byte → List Byte → List (List Byte)
  | [], cur => if cur.isEmpty then [] else [cur.reverse]
  | b :: rest, cur =>
    if isWSM m b then
      (if cur.isEmpty then wordsFromM m rest [] else cur.reverse :: wordsFromM m rest [])
    else wordsFromM m rest (b :: cur)

def command?M (m : Mutant) (w : List Byte) : Option Cmd :=
  if m = .caseSensitive then
    if w = ascii "CAPABILITIES" then some .capabilities else if w = ascii "HELP" then some .help
    else if w = ascii "QUIT" then some .quit else if w = ascii "HEAD" then some .head
    else if w = ascii "STAT" then some .stat else if w = ascii "MODE" then some .mode else none
  else command? w

def keywordRest (b : Byte) : Bool := isAlpha b || isDigit b || b == 46#8 || b == 45#8

def answerM (m : Mutant) (c : Cmd) (args : List (List Byte)) : Reply :=
  let args := if m = .extraArgsIgnored then args.take 1 else args
  let args := if m = .argsIgnored && (c = .help || c = .quit) then [] else args
  let args := if m = .modeArgsIgnored && c = .mode then args.take 1 else args
  match c, args with
  | .capabilities, [] => .capabilities
  | .capabilities, [k] =>
    if isKeyword k || (m = .shortKeyword && k.length = 2 && k.all isAlpha) ||
        (m = .keywordAnyStart && 3 ≤ k.length && k.all keywordRest) then .capabilities
    else .syntax
  | .help, [] => .help
  | .quit, [] => .quit
  | .mode, [k] =>
    if (if m = .readerCaseSensitive then k = ascii "READER" else k.map upper = ascii "READER") ||
        m = .modeAnyWord then .modeReader
    else .syntax
  | .head, [] | .stat, [] => .noGroup
  | .head, [a] | .stat, [a] =>
    if (isArticleNumber a && !(m = .zeroRejected && value a = 0)) ||
        (m = .numberUnbounded && 1 ≤ a.length && a.length ≤ 16 && a.all isDigit) ||
        (m = .moreDigits && 1 ≤ a.length && a.all isDigit && value a ≤ 2147483647) then .noGroup
    else if isMessageId a ||
        (m = .messageIdUnbounded && 250 < a.length && a.head? == some 60#8 &&
          a.getLast? == some 62#8 && ((a.drop 1).dropLast).all isNotGt) ||
        (m = .idAnyByte && 3 ≤ a.length && a.length ≤ 250 && a.head? == some 60#8 &&
          a.getLast? == some 62#8) then
      if m = .idAsNumber then .noGroup else .noSuchId
    else .syntax
  | .post, [] => .post
  | _, _ => .syntax

def replyM (m : Mutant) (l : Line) : Reply :=
  match wordsFromM m l.kept [] with
  | [] =>
    if l.kind = .overlong && m != .overlongBlankIgnored then .unknown
    else if m = .blankAnswered && !l.kept.isEmpty then .unknown
    else if m = .emptyAnswered && l.kept.isEmpty then .unknown else .ignore
  | w :: args =>
    match command?M m w with
    | none => if m = .unknownAsSyntax && l.kind != .command then .syntax else .unknown
    | some c => if l.kind = .command || m = .badLineAccepted then answerM m c args else .syntax

theorem wordsFromM_none : wordsFromM .none = wordsFrom := by
  funext l cur
  induction l generalizing cur with
  | nil => rfl
  | cons b rest ih => simp [wordsFromM, wordsFrom, isWSM, isWS, ih]

theorem answerM_none : answerM .none = answer := by
  funext c args
  cases c <;> rcases args with _ | ⟨a, _ | ⟨b, rest⟩⟩ <;> simp [answerM, answer]

theorem replyM_none : replyM .none = reply := by
  funext l
  unfold replyM reply replyIn words
  rw [wordsFromM_none]
  split <;> simp [command?M, commandIn, answerM_none]

/-- A line that tells the mutant from the specification. -/
def witness : Mutant → Line
  | .none => ⟨.command, []⟩
  | .caseSensitive => ⟨.command, ascii "help"⟩
  | .tabNotSpace => ⟨.command, ascii "HELP\t"⟩
  | .blankAnswered => ⟨.command, ascii " \t "⟩
  | .overlongBlankIgnored => ⟨.overlong, ascii "    "⟩
  | .badLineAccepted => ⟨.malformed, ascii "HELP"⟩
  | .unknownAsSyntax => ⟨.malformed, ascii "XYZZY"⟩
  | .extraArgsIgnored => ⟨.command, ascii "HEAD 1 2"⟩
  | .numberUnbounded => ⟨.command, ascii "HEAD 2147483648"⟩
  | .messageIdUnbounded =>
    ⟨.command, ascii "HEAD <" ++ List.replicate 249 (ascii "a").head! ++ ascii ">"⟩
  | .shortKeyword => ⟨.command, ascii "CAPABILITIES ab"⟩
  | .zeroRejected => ⟨.command, ascii "HEAD 0"⟩
  | .idAsNumber => ⟨.command, ascii "STAT <a@b>"⟩
  | .argsIgnored => ⟨.command, ascii "QUIT x"⟩
  | .idAnyByte => ⟨.command, ascii "HEAD <a>b>"⟩
  | .keywordAnyStart => ⟨.command, ascii "CAPABILITIES 1ab"⟩
  | .moreDigits => ⟨.command, ascii "HEAD 00000000000000001"⟩
  | .emptyAnswered => ⟨.command, []⟩
  | .readerCaseSensitive => ⟨.command, ascii "MODE reader"⟩
  | .modeAnyWord => ⟨.command, ascii "MODE STREAM"⟩
  | .modeArgsIgnored => ⟨.command, ascii "MODE READER x"⟩

/-- **Each broken rule changes the reply to its line.** -/
theorem mutants_differ : ∀ m, m ≠ .none → replyM m (witness m) ≠ reply (witness m) := by
  intro m hm
  cases m <;> first | exact absurd rfl hm | decide +kernel

/-! ## Worked cases, among them RFC 3977's example of too many arguments -/

def line (s : String) : Line := ⟨.command, ascii s⟩

theorem examples :
    reply (line "CAPABILITIES") = .capabilities ∧ reply (line "capabilities foo") = .capabilities ∧
    reply (line "CAPABILITIES 1x") = .syntax ∧ reply (line "HELP") = .help ∧
    reply (line "hElP") = .help ∧ reply (line "HELP x") = .syntax ∧ reply (line "QUIT") = .quit ∧
    reply (line "QUIT x") = .syntax ∧ reply (line "\tQUIT \t") = .quit ∧
    reply (line "HEAD") = .noGroup ∧ reply (line "HEAD 0") = .noGroup ∧
    reply (line "HEAD 05") = .noGroup ∧ reply (line "HEAD 2147483647") = .noGroup ∧
    reply (line "HEAD 2147483648") = .syntax ∧ reply (line "HEAD +5") = .syntax ∧
    reply (line "HEAD -1") = .syntax ∧ reply (line "HEAD 12abc") = .syntax ∧
    reply (line "HEAD <a@b>") = .noSuchId ∧ reply (line "STAT <a@b>") = .noSuchId ∧
    reply (line "HEAD <>") = .syntax ∧ reply (line "HEAD <a>b>") = .syntax ∧
    reply (line "HEAD 53 54 55") = .syntax ∧ reply (line "MODE READER") = .modeReader ∧
    reply (line "mode Reader") = .modeReader ∧ reply (line "MODE") = .syntax ∧
    reply (line "MODE STREAM") = .syntax ∧ reply (line "MODE READER x") = .syntax ∧
    replyIn true (line "MODE READER") = .modeReader ∧
    reply (line "XY") = .unknown ∧ reply (line "") = .ignore ∧ reply (line " \t") = .ignore ∧
    reply ⟨.malformed, []⟩ = .ignore ∧ reply ⟨.malformed, ascii "HELP"⟩ = .syntax ∧
    reply ⟨.malformed, ascii "FOO"⟩ = .unknown ∧ reply ⟨.overlong, ascii "HELP"⟩ = .syntax ∧
    reply ⟨.overlong, ascii "FOO"⟩ = .unknown ∧ reply ⟨.overlong, ascii "  "⟩ = .unknown ∧
    reply (line "POST") = .unknown ∧ replyIn true (line "post") = .post ∧
    replyIn true (line "POST x") = .syntax ∧ replyIn true ⟨.malformed, ascii "POST"⟩ = .syntax ∧
    replyIn true (line "HELP") = .help := by
  decide +kernel

/-- What a reply looks up: the command and the message-id. -/
def Reply.lookupOf : Reply → Option (Cmd × List Byte)
  | .lookup c _ id => some (c, id)
  | _ => none

/-- The group a reply asks to select. -/
def Reply.selectOf : Reply → Option (List Byte)
  | .select g => some g
  | _ => none

/-- With a store: ARTICLE, BODY, GROUP, NEXT and LAST are commands; a message-id is looked up, a
number found in the selected group, and no argument means the current article. -/
theorem store_examples :
    reply (line "ARTICLE <a@b>") = .unknown ∧
    (replyIn true (line "article <a@b>")).lookupOf = some (.article, ascii "<a@b>") ∧
    replyIn true (line "BODY 3") = .byNumber .body 3 ∧ replyIn true (line "ARTICLE") = .current .article ∧
    replyIn true (line "STAT 0005") = .byNumber .stat 5 ∧ replyIn true (line "HEAD") = .current .head ∧
    (replyIn true (line "HEAD <a@b>")).lookupOf = some (.head, ascii "<a@b>") ∧
    (replyIn true (line "STAT <a@b>")).lookupOf = some (.stat, ascii "<a@b>") ∧
    replyIn true (line "BODY <a@b> x") = .syntax ∧ replyIn true (line "BODY <>") = .syntax ∧
    (replyIn true (line "group local.test")).selectOf = some (ascii "local.test") ∧
    replyIn true (line "GROUP") = .syntax ∧ replyIn true (line "GROUP a b") = .syntax ∧
    replyIn true (line "GROUP a*b") = .syntax ∧ replyIn true (line "GROUP a,b") = .syntax ∧
    replyIn true ⟨.command, ascii "GROUP " ++ List.replicate 65 (ascii "a").head!⟩ = .noSuchGroup ∧
    replyIn true (line "NEXT") = .move true ∧ replyIn true (line "last") = .move false ∧
    replyIn true (line "NEXT 1") = .syntax ∧ reply (line "GROUP local.test") = .unknown ∧
    reply (line "NEXT") = .unknown := by
  decide +kernel

/-- The group and the range a LISTGROUP asks for, and the wildmat a LIST ACTIVE asks for, `none` for
every group. -/
def Reply.listGroupOf : Reply → Option (Option (List Byte) × Nat × Nat)
  | .listGroup g lo hi => some (g, lo, hi)
  | _ => none
def Reply.activeOf : Reply → Option (Option Wildmat)
  | .active w => some w
  | _ => none

/-- With a store: LISTGROUP takes a group and a range (§6.1.2). -/
theorem listgroup_examples :
    ((replyIn true (line "LISTGROUP")).listGroupOf == some (none, 1, numberMax) &&
      (replyIn true (line "listgroup local.test")).listGroupOf == some (some (ascii "local.test"), 1, numberMax) &&
      (replyIn true (line "LISTGROUP local.test 3")).listGroupOf == some (some (ascii "local.test"), 3, 3) &&
      (replyIn true (line "LISTGROUP local.test 3-")).listGroupOf == some (some (ascii "local.test"), 3, numberMax) &&
      (replyIn true (line "LISTGROUP local.test 3-7")).listGroupOf == some (some (ascii "local.test"), 3, 7) &&
      (replyIn true (line "LISTGROUP local.test 7-3")).listGroupOf == some (some (ascii "local.test"), 7, 3)) =
      true := by
  decide +kernel

/-- …and refuses a name or a range malformed, 411 for a name longer than any group's. -/
theorem listgroup_refused :
    replyIn true (line "LISTGROUP local.test -3") = .syntax ∧ replyIn true (line "LISTGROUP local.test 3-7-9") = .syntax ∧
    replyIn true (line "LISTGROUP local.test 2147483648") = .syntax ∧ replyIn true (line "LISTGROUP a*") = .syntax ∧
    replyIn true (line "LISTGROUP local.test 1 2") = .syntax ∧ replyIn true (line "LISTGROUP a*b 1") = .syntax ∧
    replyIn true ⟨.command, ascii "LISTGROUP " ++ List.replicate 65 (ascii "a").head! ++ ascii " 1"⟩ = .noSuchGroup ∧
    reply (line "LISTGROUP") = .unknown := by
  decide +kernel

/-- LIST takes a keyword, ACTIVE without one, and a wildmat (§7.6.1, §4.1). -/
theorem list_examples :
    (replyIn true (line "LIST")).activeOf = some none ∧ (replyIn true (line "list active")).activeOf = some none ∧
    replyIn true (line "LIST NEWSGROUPS") = .newsgroups ∧ replyIn true (line "LIST newsgroups loc*") = .newsgroups ∧
    (((replyIn true (line "LIST ACTIVE a,!b")).activeOf.bind id).map fun w =>
      (wildmatch w (ascii "a"), wildmatch w (ascii "b"), wildmatch w (ascii "c"))) = some (true, false, false) ∧
    replyIn true (line "LIST ACTIVE !a") = .syntax ∧ replyIn true (line "LIST ACTIVE a,,b") = .syntax ∧
    replyIn true (line "LIST ACTIVE a,") = .syntax ∧ replyIn true (line "LIST ACTIVE a,!") = .syntax ∧
    replyIn true (line "LIST ACTIVE [a]") = .syntax ∧ replyIn true (line "LIST ACTIVE a\\b") = .syntax ∧
    replyIn true (line "LIST NEWSGROUPS !a") = .syntax ∧ reply (line "LIST") = .unknown := by
  decide +kernel

/-- LIST's keywords but ACTIVE and NEWSGROUPS, and their arguments, are refused; DATE takes nothing,
NEWGROUPS a date, a time and `GMT` or not (§7.1, §7.3). -/
theorem dated_examples :
    replyIn true (line "LIST ACTIVE.TIMES") = .syntax ∧ replyIn true (line "LIST OVERVIEW.FMT") = .syntax ∧
    replyIn true (line "LIST ACTIVE a b") = .syntax ∧ replyIn true (line "LIST 1x") = .syntax ∧
    replyIn true (line "DATE") = .date ∧ replyIn true (line "DATE 1") = .syntax ∧ reply (line "DATE") = .unknown ∧
    replyIn true (line "NEWGROUPS 19990624 000000 GMT") = .newGroups ∧
    replyIn true (line "newgroups 990624 235960 gmt") = .newGroups ∧
    replyIn true (line "NEWGROUPS 20261024 120000") = .newGroups := by
  decide +kernel

/-- NEWGROUPS's dates and times out of their ranges, or of other forms, are refused (§7.3.2). -/
theorem newgroups_examples :
    replyIn true (line "NEWGROUPS 18991231 000000") = .syntax ∧ replyIn true (line "NEWGROUPS 20261324 000000") = .syntax ∧
    replyIn true (line "NEWGROUPS 20261000 000000") = .syntax ∧ replyIn true (line "NEWGROUPS 20261032 000000") = .syntax ∧
    replyIn true (line "NEWGROUPS 20261024 240000") = .syntax ∧ replyIn true (line "NEWGROUPS 20261024 126000") = .syntax ∧
    replyIn true (line "NEWGROUPS 20261024 120061") = .syntax ∧ replyIn true (line "NEWGROUPS 2026102 120000") = .syntax ∧
    replyIn true (line "NEWGROUPS 20261024 120000 UTC") = .syntax ∧ replyIn true (line "NEWGROUPS 20261024") = .syntax ∧
    replyIn true (line "NEWGROUPS 20261024 120000 GMT x") = .syntax ∧
    replyIn true (line "NEWGROUPS +0261024 120000") = .syntax := by
  decide +kernel

/-- A wildmat of ASCII. -/
def wm (s : String) : Wildmat := (wildmat? (ascii s)).getD []

/-- §4.2's and §4.4's examples; `$@` of §4.4, the pound sign, is `C2 A3`. -/
theorem wildmat_examples :
    wildmatch (wm "a*,!*b,*c*") (ascii "aaa") = true ∧ wildmatch (wm "a*,!*b,*c*") (ascii "abb") = false ∧
    wildmatch (wm "a*,!*b,*c*") (ascii "ccb") = true ∧ wildmatch (wm "a*,!*b,*c*") (ascii "xxx") = false ∧
    wildmatch (wm "abc") (ascii "abc") = true ∧ wildmatch (wm "abc") (ascii "abcd") = false ∧
    wildmatch (wm "abc,def") (ascii "def") = true ∧
    wildmatch ((wildmat? [0xC2#8, 0xA3#8]).getD []) [0xC2#8, 0xA3#8] = true ∧
    wildmatch (wm "a*") (ascii "a") = true ∧ wildmatch (wm "a*") (ascii "ba") = false ∧
    wildmatch (wm "a*b") (ascii "axxb") = true ∧ wildmatch (wm "a*b") (ascii "axxbc") = false ∧
    wildmatch (wm "a*,*b") (ascii "xb") = true ∧ wildmatch (wm "a*,!*b") (ascii "ab") = false ∧
    wildmatch (wm "a*,!*b") (ascii "ac") = true ∧ wildmatch (wm "a*,!*b,c*") (ascii "cb") = true ∧
    wildmatch (wm "a*,c*,!*b") (ascii "cb") = false ∧ wildmatch (wm "a*,c*,!*b") (ascii "ca") = true ∧
    wildmatch (wm "?a*") [0xC2#8, 0xA3#8, 0x61#8] = true ∧ wildmatch (wm "??a*") (ascii "xya") = true ∧
    wildmatch (wm "??a*") [0xC2#8, 0xA3#8, 0x61#8] = false ∧ wildmatch (wm "*a?") (ascii "xab") = true ∧
    wildmatch (wm "*a??") (ascii "abc") = true ∧ wildmatch (wm "*a??") (ascii "ab") = false ∧
    wildmatch (wm "a?") [0x61#8, 0xC2#8, 0xA3#8] = true ∧ wildmatch (wm "a??") [0x61#8, 0xC2#8, 0xA3#8] = false ∧
    wildmatch (wm "*") (ascii "local.test") = true ∧ wildmatch (wm "local.*") (ascii "local.") = true ∧
    wildmatch (wm "*.*.*") (ascii "a.b") = false ∧ wildmatch (wm "*.*.*") (ascii "a..b") = true := by
  decide +kernel

/-- A newsgroup name may hold UTF-8 past US-ASCII, and nothing else past it (§9.8, RFC 3629). -/
theorem name_examples :
    isGroupName [0x61#8, 0xC3#8, 0xA9#8] = true ∧ isGroupName [0xE2#8, 0x82#8, 0xAC#8] = true ∧
    isGroupName [0xF0#8, 0x9F#8, 0x98#8, 0x80#8] = true ∧ isGroupName [0xC3#8] = false ∧
    isGroupName [0xC0#8, 0x80#8] = false ∧ isGroupName [0xED#8, 0xA0#8, 0x80#8] = false ∧
    isGroupName [0xE0#8, 0x80#8, 0x80#8] = false ∧ isGroupName [0xF4#8, 0x90#8, 0x80#8, 0x80#8] = false ∧
    isGroupName [0x80#8] = false ∧ isGroupName [] = false ∧ isGroupName (ascii "a.b-c_d+e") = true ∧
    isGroupName (ascii "a?") = false ∧ isGroupName (ascii "[a]") = false ∧ isGroupName (ascii "a\\b") = false ∧
    isGroupName (ascii "!a") = false := by
  decide +kernel

/-- An identity that fits. -/
theorem identity_witness :
    (Identity.ok ⟨ascii "0123abc", ascii "https://example.org/src"⟩) = true := by
  decide

end DN.News.CommandSpec
