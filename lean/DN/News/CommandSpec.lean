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

inductive Cmd | capabilities | help | quit | head | stat
  deriving DecidableEq, Repr

/-- The command a word names, in any case. -/
def command? (w : List Byte) : Option Cmd :=
  let u := w.map upper
  if u = ascii "CAPABILITIES" then some .capabilities
  else if u = ascii "HELP" then some .help
  else if u = ascii "QUIT" then some .quit
  else if u = ascii "HEAD" then some .head
  else if u = ascii "STAT" then some .stat
  else none

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

/-- A keyword: `ALPHA 2*(ALPHA / DIGIT / "." / "-")` (§9.8). -/
def isKeyword : List Byte → Bool
  | a :: rest => isAlpha a && 2 ≤ rest.length &&
      rest.all fun b => isAlpha b || isDigit b || b == 46#8 || b == 45#8
  | [] => false

inductive Reply
  /-- no reply: an empty or white-space-only line -/
  | ignore
  /-- 101 and the capability list -/
  | capabilities
  /-- 100 and the help text -/
  | help
  /-- 205, then the connection closes -/
  | quit
  /-- 412: no newsgroup selected -/
  | noGroup
  /-- 430: no article with that message-id -/
  | noSuchId
  /-- 500: not a command the server has -/
  | unknown
  /-- 501: a command the server has, but not well formed -/
  | syntax
  deriving DecidableEq, Repr

/-- The reply to a command with these arguments, on a well-formed line. -/
def answer : Cmd → List (List Byte) → Reply
  | .capabilities, [] => .capabilities
  | .capabilities, [k] => if isKeyword k then .capabilities else .syntax
  | .help, [] => .help
  | .quit, [] => .quit
  | .head, [] | .stat, [] => .noGroup
  | .head, [a] | .stat, [a] =>
    if isArticleNumber a then .noGroup else if isMessageId a then .noSuchId else .syntax
  | _, _ => .syntax

/-- **The reply to a line.** -/
def reply (l : Line) : Reply :=
  match words l.kept with
  | [] => if l.kind = .overlong then .unknown else .ignore
  | w :: args =>
    match command? w with
    | none => .unknown
    | some c => if l.kind = .command then answer c args else .syntax

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

/-- The greeting (§5.1): posting is not allowed, and the source is offered. -/
def greeting (i : Identity) : List Byte :=
  greetingHead ++ i.revision ++ greetingMid ++ i.source ++ crlf

/-- The bytes of a reply; a multi-line one ends with its terminating dot line (§3.1.1). -/
def text (i : Identity) : Reply → List Byte
  | .ignore => []
  | .capabilities => capabilitiesHead ++ i.revision ++ blockEnd
  | .help => helpHead ++ i.revision ++ helpMid ++ i.source ++ blockEnd
  | .quit => ascii "205 Bye\r\n"
  | .noGroup => ascii "412 No newsgroup selected\r\n"
  | .noSuchId => ascii "430 No article with that message-id\r\n"
  | .unknown => ascii "500 Unknown command\r\n"
  | .syntax => ascii "501 Syntax error\r\n"

/-- The most bytes one action carries. -/
def actionData : Nat := 512

theorem parts_short :
    greetingHead.length ≤ 16 ∧ greetingMid.length ≤ 35 ∧ capabilitiesHead.length ≤ 60 ∧
      helpHead.length ≤ 132 ∧ helpMid.length ≤ 53 ∧ blockEnd.length = 5 ∧ crlf.length = 2 ∧
      ∀ r, r ≠ .capabilities → r ≠ .help → ∀ i, (text i r).length ≤ 40 := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, rfl, ?_⟩
  intro r h1 h2 i
  cases r <;> first | exact absurd rfl h1 | exact absurd rfl h2 | (simp only [text]; decide +kernel)

/-- **Every reply, and the greeting, fits one action** when the identity fits. -/
theorem greeting_fits (i : Identity) (h : i.ok = true) : (greeting i).length ≤ actionData := by
  simp only [Identity.ok, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨h1, h2, _, _, _, _, _, _⟩ := parts_short
  simp only [greeting, List.length_append, actionData]
  omega

theorem text_fits (i : Identity) (h : i.ok = true) (r : Reply) :
    (text i r).length ≤ actionData := by
  simp only [Identity.ok, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨_, _, h3, h4, h5, h6, _, h8⟩ := parts_short
  by_cases hc : r = .capabilities
  · subst hc; simp only [text, List.length_append, actionData]; omega
  by_cases hh : r = .help
  · subst hh; simp only [text, List.length_append, actionData]; omega
  have := h8 r hc hh i
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
    else if w = ascii "STAT" then some .stat else none
  else command? w

def keywordRest (b : Byte) : Bool := isAlpha b || isDigit b || b == 46#8 || b == 45#8

def answerM (m : Mutant) (c : Cmd) (args : List (List Byte)) : Reply :=
  let args := if m = .extraArgsIgnored then args.take 1 else args
  let args := if m = .argsIgnored && (c = .help || c = .quit) then [] else args
  match c, args with
  | .capabilities, [] => .capabilities
  | .capabilities, [k] =>
    if isKeyword k || (m = .shortKeyword && k.length = 2 && k.all isAlpha) ||
        (m = .keywordAnyStart && 3 ≤ k.length && k.all keywordRest) then .capabilities
    else .syntax
  | .help, [] => .help
  | .quit, [] => .quit
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
  unfold replyM reply words
  rw [wordsFromM_none]
  split <;> simp [command?M, answerM_none]

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
    reply (line "HEAD 53 54 55") = .syntax ∧ reply (line "MODE READER") = .unknown ∧
    reply (line "XY") = .unknown ∧ reply (line "") = .ignore ∧ reply (line " \t") = .ignore ∧
    reply ⟨.malformed, []⟩ = .ignore ∧ reply ⟨.malformed, ascii "HELP"⟩ = .syntax ∧
    reply ⟨.malformed, ascii "FOO"⟩ = .unknown ∧ reply ⟨.overlong, ascii "HELP"⟩ = .syntax ∧
    reply ⟨.overlong, ascii "FOO"⟩ = .unknown ∧ reply ⟨.overlong, ascii "  "⟩ = .unknown := by
  decide +kernel

/-- An identity that fits. -/
theorem identity_witness :
    (Identity.ok ⟨ascii "0123abc", ascii "https://example.org/src"⟩) = true := by
  decide

end DN.News.CommandSpec
