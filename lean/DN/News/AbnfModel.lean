-- SPDX-License-Identifier: AGPL-3.0-or-later
import DN.News.AbnfMutant
import DN.News.AbnfRules

/-!
# DN.News.AbnfModel

The grammar of `DN.News.AbnfRules` run on cases, as `dn-compiler abnf-model` answers them: each
line of input names a rule and gives the bytes to match in hex, `-` for none, and each answer is a
line, `1` if the rule matches all of the bytes, `0` if not, and `fuel` if the recursion ran out,
which `AbnfRules.depth` rules out and the checks require never to happen. With a mutant of
`DN.News.AbnfMutant`, the interpreter answers with that rule of its broken.
-/

namespace DN.News.AbnfModel

open DN.News.Abnf DN.News.AbnfMutant DN.News.AbnfRules

def hexDigit (c : Char) : Option Nat :=
  if '0' ≤ c ∧ c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c ∧ c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else none

/-- Bytes from hex, two digits each; `-` is none. -/
def parseHex (s : String) : Option (List Nat) :=
  if s = "-" then some [] else go s.toList
where
  go : List Char → Option (List Nat)
    | [] => some []
    | a :: b :: rest => do
      let hi ← hexDigit a
      let lo ← hexDigit b
      pure ((16 * hi + lo) :: (← go rest))
    | [_] => none

/-- The answer to one case, or why the line is not one. -/
def answer (m : Mutant) (line : String) : Except String String :=
  match line.splitOn " " with
  | [rule, hex] =>
    match AbnfRules.names.findIdx? (· == rule), parseHex hex with
    | some i, some bytes =>
      match matchesM m grammar depth i bytes with
      | .ok true => .ok "1"
      | .ok false => .ok "0"
      | .error .fuel => .ok "fuel"
      | .error (.noRule j) => .error s!"the grammar has no rule {j}"
    | none, _ => .error s!"no rule {rule}"
    | _, none => .error s!"not hex: {hex}"
  | _ => .error s!"a case is a rule and hex, not {line}"

/-- The answers to every line of `input`, one line each. -/
def runAll (m : Mutant) (input : String) : Except String String := do
  let lines := (input.splitOn "\n").filter (!·.isEmpty)
  let answers ← lines.mapM (answer m)
  pure (String.join (answers.map (· ++ "\n")))

/-! ## Examples: the RFCs' own, rules their text alone would get wrong, and RFC 5536's limits -/

/-- What rule `rule` says of the bytes of `s`. -/
def says (rule s : String) : Option Bool :=
  (AbnfRules.names.findIdx? (· == rule)).bind fun i =>
    match matches? grammar depth i (codes s) with
    | .ok b => some b
    | .error _ => none

/-- A date in the zone "GMT", with white space before it (RFC 5322, erratum 6639). -/
def regression_841 : Bool := says "orig-date" "Date: Tue, 29 Sep 2026 12:00:00 GMT\r\n" == some true
/-- Another obsolete zone. -/
def regression_842 : Bool :=
  says "orig-date" "Date: Tue, 29 Sep 2026 12:00:00 EST\r\n" == some false
def regression_843 : Bool := says "comment" "(a (nested) comment)" == some true
def regression_844 : Bool := says "comment" "(a (nested comment)" == some false
/-- A distribution of more than one letter (RFC 5536 §3.2.4, grouped as its text intends). -/
def regression_845 : Bool := says "dist-name" "world" == some true
/-- A display name with a dot and no quotes: the obsolete phrase RFC 5536 §2.1 keeps. -/
def regression_846 : Bool :=
  says "from" "From: John Q. Public <jq@example.org>\r\n" == some true
/-- No space after the colon (RFC 5536 §3.1.3). -/
def regression_847 : Bool := says "message-id" "Message-ID:<a@example.org>\r\n" == some false
/-- An empty body (RFC 5536 §2.2). -/
def regression_848 : Bool := says "optional-field" "X-Foo:\r\n" == some false
/-- RFC 5536 §3.2.8's own example of a parameter, with white space on both sides of "=". -/
def regression_849 : Bool :=
  says "injection-info"
    "Injection-Info: news.example.com; posting-host = \"posting.example.com:192.0.2.1\"\r\n" ==
    some true
/-- White space and a comment between a parameter's value and the next ";" (RFC 5536 §3.2.8). -/
def regression_850 : Bool :=
  says "injection-info" "Injection-Info: a.example; posting-host=b.example (c) ; x=1\r\n" ==
    some true
def regression_851 : Bool := says "archive" "Archive: no; x = y\r\n" == some true
/-- No space after the colon of a field RFC 5322 defines, or of any other (RFC 5536 §2.2). -/
def regression_852 : Bool := says "to" "To:x@y.example\r\n" == some false
def regression_853 : Bool := says "optional-field" "X-Foo:bar\r\n" == some false
def regression_854 : Bool := says "return" "Return-Path:<a@b.example>\r\n" == some false
def regression_855 : Bool := says "to" "To: x@y.example\r\n" == some true
/-- RFC 8315 §5.1's Cancel-Lock, and §5.3's Cancel-Key of the obsolete syntax it has agents
accept. -/
def regression_856 : Bool :=
  says "cancel-lock" "Cancel-Lock: sha256:s/pmK/3grrz++29ce2/mQydzJuc7iqHn1nqcJiQTPMc=\r\n" ==
    some true
def regression_857 : Bool :=
  says "cancel-key" "Cancel-Key: ShA1:aaaBBBcccDDDeeeFFF\r\n" == some true
/-- Comments nested 500 deep: the fuel `AbnfRules.depth` gives lasts however deep they go. -/
def regression_858 : Bool :=
  says "comment" (String.ofList (List.replicate 500 '(' ++ 'x' :: List.replicate 500 ')')) ==
    some true

end DN.News.AbnfModel
