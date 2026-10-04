-- SPDX-License-Identifier: AGPL-3.0-or-later
import DN.News.AbnfRules
import DN.News.CommandSpec

/-!
# DN.News.ArticleSpec

Which proto-articles a POST accepts and what the server adds, written from RFC 5536, RFC 5537 §3.5
and docs/decisions/0005-article-store.md, apart from the code that decides it.

An article comes from the block framer: CRLF lines, dots unstuffed, no terminator. Its header
section ends at the first empty line, which has to be there (RFC 3977 §3.6); a line starting with
white space continues the field before it. The checks go in order, the first that fails giving the
reason:

1. the header section's shape: a header, the empty line, 0005's bounds on the section and a line,
   every line a field's first or a continuation;
2. each field: its name not one RFC 5537 §3.5 step 2 or 0005 refuses (Injection-Info, Xref, the
   trace fields of injecting agents older than RFC 5536, the fields RFC 5536 §3.3 and RFC 3798 §2.1
   deprecate for Netnews, Control, Supersedes, Approved); no line of its body of white space alone
   (RFC 5536 §2.2); its grammar (`DN.News.AbnfRules`);
3. no field that may appear once twice (RFC 5536 §3 to §3.2, RFC 5322 §3.6, RFC 8315 §2, three of
   MIME's by 0005); From, Newsgroups and Subject present (RFC 5537 §3.4.1); no POSTED in Path; no
   message identifier past 250 octets (RFC 5536 §3.1.3); a Sender when From names several mailboxes
   (RFC 5322 §3.6.2); no distribution "All" (RFC 5536 §3.2.4);
4. every date one that means one (RFC 5322 §3.3), a Received's included; Date and Injection-Date at
   most 24 hours ahead of the wall clock and 72 behind (RFC 5537 §3.5 step 3);
5. the groups: at most 16 (0005), none reserved (RFC 5536 §3.1.4), one at least carried (RFC 5537
   §3.5 step 4).

An accepted article gets what RFC 5537 §3.5 steps 5 to 11 add: Path first, the server's identity
and `!.POSTED` before what it held or before `not-for-mail`; the fields as they were; Message-ID and
Date if absent; Injection-Info; Injection-Date unless it had one or had both Message-ID and Date.
Whether the store holds the message identifier is the store's to say. Not checked, by decision: the
order and rules RFC 5322 §3.6 gives blocks of trace and resent fields, which are mail transport's;
the syntax of MIME's fields (see `scripts/gen_abnf.py`). Every rule and bound is a field of
`Rules`, each shown to matter by a version with it changed (`Mutant`).
-/

namespace DN.News.ArticleSpec

open DN.News.FrameSpec DN.News.Abnf DN.News.AbnfRules
open DN.News.CommandSpec (ascii SP isWS isDigit crlf value)

abbrev Bytes := List Byte

def COLON : Byte := 58#8
def SEMICOLON : Byte := 59#8
def DQUOTE : Byte := 34#8
def LBRACKET : Byte := 91#8
def RBRACKET : Byte := 93#8
def COMMA : Byte := 44#8
def LPAREN : Byte := 40#8
def RPAREN : Byte := 41#8
def BACKSLASH : Byte := 92#8
def LT : Byte := 60#8
def GT : Byte := 62#8
def BANG : Byte := 33#8
def PLUS : Byte := 43#8
def MINUS : Byte := 45#8

def lowerB (b : Byte) : Byte := if 65 ≤ b.toNat ∧ b.toNat ≤ 90 then b + 32#8 else b

/-- Whether two names are the same, compared without regard to case (RFC 5322 §1.2.2). -/
def sameName (a b : Bytes) : Bool := a.map lowerB == b.map lowerB

def named (a : Bytes) (n : String) : Bool := sameName a (ascii n)

/-! ## The header section -/

/-- The lines of an article before its first empty line, each without its CRLF, and whether that
empty line was found. Bytes after the last CRLF, with no empty line before them, are a line that
never ended. `cr` says the byte before was a CR, not yet taken into the line. -/
def headerFrom : Bytes → Bool → Bytes → List Bytes → List Bytes × Bool
  | [], cr, cur, acc =>
    let cur := if cr then CR :: cur else cur
    ((if cur.isEmpty then acc else cur.reverse :: acc).reverse, false)
  | b :: rest, cr, cur, acc =>
    if cr && b == LF then
      if cur.isEmpty then (acc.reverse, true) else headerFrom rest false [] (cur.reverse :: acc)
    else
      let cur := if cr then CR :: cur else cur
      if b == CR then headerFrom rest true cur acc else headerFrom rest false (b :: cur) acc

def header (a : Bytes) : List Bytes × Bool := headerFrom a false [] []

/-- A byte of a field's name (RFC 5322 §3.6.8). -/
def isFtext (b : Byte) : Bool := (33 ≤ b.toNat && b.toNat ≤ 57) || (59 ≤ b.toNat && b.toNat ≤ 126)

/-- The name a line starts a field with: the bytes before its first colon, if they are one. -/
def nameOf (l : Bytes) : Option Bytes :=
  let n := l.takeWhile (· != COLON)
  if n.length < l.length && !n.isEmpty && n.all isFtext then some n else none

/-- A header field: its name as written, and its lines without their CRLF, the first starting
with the name. -/
structure Field where
  name : Bytes
  lines : List Bytes

/-- The field as it travels. -/
def Field.text (f : Field) : Bytes := (f.lines.map (· ++ crlf)).flatten

/-- The lines of the field's body: the first line after the colon, and the others. -/
def Field.body (f : Field) : List Bytes :=
  match f.lines with
  | l :: more => l.drop (f.name.length + 1) :: more
  | [] => []

/-- The field's body as one run of bytes, the folds kept, without the last CRLF. -/
def Field.value (f : Field) : Bytes :=
  match f.body with
  | l :: more => l ++ (more.map (crlf ++ ·)).flatten
  | [] => []

/-- The fields the lines make, or `none` if a line starts none and continues none. -/
def fieldsFrom : List Bytes → List Field → Option Field → Option (List Field)
  | [], acc, cur => some (cur.toList ++ acc).reverse
  | l :: more, acc, cur =>
    if l.head?.any isWS then
      match cur with
      | some f => fieldsFrom more acc (some { f with lines := f.lines ++ [l] })
      | none => none
    else
      match nameOf l with
      | some n => fieldsFrom more (cur.toList ++ acc) (some ⟨n, [l]⟩)
      | none => none

def fields (ls : List Bytes) : Option (List Field) := fieldsFrom ls [] none

/-! ## Dates -/

/-- Days since 1970-01-01 of a date of the proleptic Gregorian calendar, from its year (at least
one), month and day; the algorithm of Howard Hinnant's `days_from_civil`. -/
def daysFromCivil (y m d : Nat) : Int :=
  let y' := if m ≤ 2 then y - 1 else y
  let era := y' / 400
  let yoe := y' - era * 400
  let doy := (153 * (if m > 2 then m - 3 else m + 9) + 2) / 5 + d - 1
  let doe := yoe * 365 + yoe / 4 - yoe / 100 + doy
  ((era * 146097 + doe : Nat) : Int) - 719468

/-- The year, month and day of a day since 1970-01-01 (`civil_from_days`). -/
def civilFromDays (z : Nat) : Nat × Nat × Nat :=
  let z' := z + 719468
  let era := z' / 146097
  let doe := z' - era * 146097
  let yoe := (doe - doe / 1460 + doe / 36524 - doe / 146096) / 365
  let doy := doe - (365 * yoe + yoe / 4 - yoe / 100)
  let mp := (5 * doy + 2) / 153
  let d := doy - (153 * mp + 2) / 5 + 1
  let m := if mp < 10 then mp + 3 else mp - 9
  let y := yoe + era * 400
  (if m ≤ 2 then y + 1 else y, m, d)

def leap (y : Nat) : Bool := y % 4 == 0 && (y % 100 != 0 || y % 400 == 0)

def daysIn (y m : Nat) : Nat :=
  if m == 2 then (if leap y then 29 else 28)
  else if m == 4 || m == 6 || m == 9 || m == 11 then 30 else 31

def dayNames : List String := ["Sun", "Mon", "Tue", "Wed", "Thu", "Fri", "Sat"]
def monthNames : List String :=
  ["Jan", "Feb", "Mar", "Apr", "May", "Jun", "Jul", "Aug", "Sep", "Oct", "Nov", "Dec"]

/-- The day of the week of a day since 1970-01-01, a Thursday: 0 for Sunday. -/
def weekday (days : Int) : Nat := ((days % 7 + 7 + 4) % 7).toNat

/-- The place of `w` in `names`, compared without regard to case, counting from `k`. -/
def indexOf (w : Bytes) : List String → Nat → Option Nat
  | [], _ => none
  | n :: rest, k => if named w n then some k else indexOf w rest (k + 1)

/-- The number written by one or more digits. -/
def number? (w : Bytes) : Option Nat := if !w.isEmpty && w.all isDigit then some (value w) else none

/-- The runs of bytes other than white space and line ends. -/
def tokens (v : Bytes) : List Bytes :=
  DN.News.CommandSpec.words (v.map fun b => if b == CR || b == LF then SP else b)

/-- The time a `date-time` of the grammar says, in seconds since 1970-01-01T00:00:00Z, if it means
one (RFC 5322 §3.3): the day of the week, when given, the one of the date; the day within its
month; the time from 00:00:00 to 23:59:60; the zone's minutes below 60; the year 1900 or later.
Comments come only at its end, where the grammar of RFC 5536 puts them. -/
def dateValue (v : Bytes) : Option Int := do
  let v := v.takeWhile (· != LPAREN)
  -- The comma, the one the grammar allows, ends the day of the week, white space or not after it.
  let (wd, ts) ← match v.splitOn COMMA with
    | [w, rest] => match tokens w with
      | [name] => some (some name, tokens rest)
      | _ => none
    | [all] => some (none, tokens all)
    | _ => none
  let (dayT, monthT, yearT, rest) ← match ts with
    | a :: b :: c :: more => some (a, b, c, more.flatten)
    | _ => none
  let day ← number? dayT
  let month := (← indexOf monthT monthNames 0) + 1
  let year ← number? yearT
  let timeT := rest.takeWhile fun b => isDigit b || b == COLON
  let zoneT := rest.drop timeT.length
  let parts := timeT.splitOn COLON
  let (h, mi, s) ← match parts.map number? with
    | [some h, some mi] => some (h, mi, 0)
    | [some h, some mi, some s] => some (h, mi, s)
    | _ => none
  let offset : Int ← if named zoneT "GMT" then some 0 else
    match zoneT with
    | sign :: digits =>
      let n ← number? digits
      if digits.length != 4 || n % 100 ≥ 60 then none
      else
        let o : Int := ((n / 100) * 3600 + (n % 100) * 60 : Nat)
        if sign == PLUS then some o else if sign == MINUS then some (-o) else none
    | [] => none
  guard (1900 ≤ year && 1 ≤ day && day ≤ daysIn year month && h ≤ 23 && mi ≤ 59 && s ≤ 60)
  let days := daysFromCivil year month day
  match wd with
  | some w => guard (indexOf w dayNames 0 == some (weekday days))
  | none => pure ()
  pure (days * 86400 + (h * 3600 + mi * 60 + s : Nat) - offset)

def pad2 (n : Nat) : Bytes := ascii (if n < 10 then s!"0{n}" else s!"{n}")

/-- The wall clock as the server writes a date: `Wed, 30 Sep 2026 07:43:21 +0000`. -/
def formatDate (wall : Nat) : Bytes :=
  let days := wall / 86400
  let secs := wall % 86400
  let (y, m, d) := civilFromDays days
  ascii (dayNames.getD (weekday days) "" ++ ", ") ++ pad2 d ++ ascii " " ++
    ascii (monthNames.getD (m - 1) "") ++ ascii s!" {y} " ++ pad2 (secs / 3600) ++ ascii ":" ++
    pad2 (secs % 3600 / 60) ++ ascii ":" ++ pad2 (secs % 60) ++ ascii " +0000"

/-! ## The parts of fields the rules read -/

/-- The message identifiers of a field body in which they stand between comments and white
space, as References holds them: each from its `<` to its `>`. A comment may hold `<`, and a
message identifier `(`, so both are read as the grammar reads them. -/
def msgIdsFrom : Nat → Option Bytes → Bytes → List Bytes → List Bytes
  | _, _, [], acc => acc.reverse
  | depth, some cur, b :: rest, acc =>
    if b == GT then msgIdsFrom depth none rest ((b :: cur).reverse :: acc)
    else msgIdsFrom depth (some (b :: cur)) rest acc
  | 0, none, b :: rest, acc =>
    if b == LPAREN then msgIdsFrom 1 none rest acc
    else if b == LT then msgIdsFrom 0 (some [b]) rest acc
    else msgIdsFrom 0 none rest acc
  | depth + 1, none, b :: rest, acc =>
    if b == BACKSLASH then
      match rest with
      | _ :: after => msgIdsFrom (depth + 1) none after acc
      | [] => acc.reverse
    else if b == LPAREN then msgIdsFrom (depth + 2) none rest acc
    else if b == RPAREN then msgIdsFrom depth none rest acc
    else msgIdsFrom (depth + 1) none rest acc

def msgIds (v : Bytes) : List Bytes := msgIdsFrom 0 none v []

/-- What follows the `;` of a Received field, its date (RFC 5322 §3.6.7): the one `;` outside
quoted strings (`mode` 1), domain literals (`mode` 2) and comments (`depth`), any of which may hold
another. -/
def receivedDate : Nat → Nat → Bytes → Bytes
  | _, _, [] => []
  | mode, depth, b :: rest =>
    if (mode == 1 || depth > 0) && b == BACKSLASH then
      match rest with
      | _ :: after => receivedDate mode depth after
      | [] => []
    else if depth > 0 then
      let deeper := if b == LPAREN then depth + 1 else if b == RPAREN then depth - 1 else depth
      receivedDate mode deeper rest
    else if mode == 1 then receivedDate (if b == DQUOTE then 0 else 1) 0 rest
    else if mode == 2 then receivedDate (if b == RBRACKET then 0 else 2) 0 rest
    else if b == DQUOTE then receivedDate 1 0 rest
    else if b == LBRACKET then receivedDate 2 0 rest
    else if b == LPAREN then receivedDate 0 1 rest
    else if b == SEMICOLON then rest
    else receivedDate 0 0 rest

/-- The names of a list separated by commas, white space and folds dropped: Newsgroups' groups,
Distribution's distributions. -/
def listed (v : Bytes) : List Bytes :=
  ((v.filter fun b => !(isWS b || b == CR || b == LF)).splitOn COMMA).filter (!·.isEmpty)

/-- The elements of Path, white space and folds dropped: each path identity and each diagnostic
with its leading `.`. -/
def pathElements (v : Bytes) : List Bytes :=
  (v.filter fun b => !(isWS b || b == CR || b == LF)).splitOn BANG

/-- A diagnostic `.POSTED`, alone or followed by `.` and an identity (RFC 5536 §3.1.5); the
keyword is compared without regard to case. -/
def isPosted (e : Bytes) : Bool :=
  match e with
  | d :: rest => d == DOT && named (rest.takeWhile (· != DOT)) "POSTED"
  | [] => false

/-- A newsgroup name RFC 5536 §3.1.4 reserves: first component `example`, `to` or `control`; the
group `poster` or `junk`; a component `all` or `ctl`. Newsgroup names are compared as written, as
the server compares them with the groups it carries: `Example.x` is not reserved, and is no group
the server carries either. -/
def reserved (g : Bytes) : Bool :=
  let cs := g.splitOn DOT
  let first := cs.headD []
  first == ascii "example" || first == ascii "to" || first == ascii "control" ||
    g == ascii "poster" || g == ascii "junk" ||
    cs.any (fun c => c == ascii "all" || c == ascii "ctl")

/-! ## The rules -/

/-- Why a proto-article is refused. A name is the field's as the article writes it, or the
field's own name when it is missing. -/
inductive Refusal
  | noHeader
  | noSeparator
  | headerTooLong
  | lineTooLong
  | malformed
  | injected (name : Bytes)
  | traced (name : Bytes)
  | deprecated (name : Bytes)
  | notOffered (name : Bytes)
  | blankLine (name : Bytes)
  | badField (name : Bytes)
  | repeated (name : Bytes)
  | missing (name : Bytes)
  | posted
  | longMessageId (name : Bytes)
  | noSender
  | distributionAll
  | badDate (name : Bytes)
  | dateAhead (name : Bytes)
  | datePast (name : Bytes)
  | tooManyGroups
  | reservedGroup
  | noKnownGroup
  deriving DecidableEq

/-- The rules and bounds the checks apply, each a field so that a version with one changed can
show it matters. -/
structure Rules where
  /-- 0005: the header section, CRLFs counted -/
  headerMax : Nat := 65536
  /-- 0005, the line limit of RFC 5322 §2.1.1, CRLF not counted -/
  lineMax : Nat := 998
  /-- RFC 5537 §3.5 step 2 (MUST) -/
  injected : List String := ["Injection-Info", "Xref"]
  /-- RFC 5537 §3.5 step 2 (MAY): trace fields of injecting agents older than RFC 5536 -/
  traced : List String := ["NNTP-Posting-Host", "NNTP-Posting-Date", "X-Trace", "X-Complaints-To"]
  /-- RFC 5537 §3.5 step 2 (SHOULD): RFC 5536 §3.3's obsolete fields and RFC 3798 §2.1's -/
  deprecated : List String := ["Date-Received", "Posting-Version", "Relay-Version",
    "Also-Control", "Article-Names", "Article-Updates", "See-Also", "Disposition-Notification-To"]
  /-- 0005: no control messages, no cancels, no approval before moderation -/
  notOffered : List String := ["Control", "Supersedes", "Approved"]
  /-- RFC 5536 §2.2: every line of a field body holds a character other than white space -/
  blank : Bool := true
  /-- The fields that may appear at most once: RFC 5536 §3, §3.1 and §3.2 (Keywords), RFC 5322
  §3.6, RFC 8315 §2; and, by 0005 as INN, MIME-Version, Content-Type and Content-Transfer-Encoding,
  since RFC 2045 describes an entity by one of each -/
  once : List String := ["Date", "From", "Message-ID", "Newsgroups", "Path", "Subject",
    "Approved", "Archive", "Control", "Distribution", "Expires", "Followup-To", "Injection-Date",
    "Injection-Info", "Lines", "Organization", "Summary", "Supersedes", "User-Agent", "Xref",
    "Keywords", "Sender", "Reply-To", "To", "Cc", "Bcc", "In-Reply-To", "References",
    "Cancel-Lock", "Cancel-Key", "MIME-Version", "Content-Type", "Content-Transfer-Encoding"]
  /-- RFC 5537 §3.4.1: what a proto-article may not omit -/
  required : List String := ["From", "Newsgroups", "Subject"]
  /-- RFC 5537 §3.5 step 2: POSTED in Path marks an article injected already -/
  posted : Bool := true
  /-- RFC 5536 §3.1.3 -/
  idMax : Nat := 250
  /-- RFC 5322 §3.6.2 -/
  sender : Bool := true
  /-- RFC 5536 §3.2.4 -/
  distributionAll : Bool := true
  /-- RFC 5322 §3.3: a date means a date -/
  dates : Bool := true
  /-- RFC 5537 §3.5 step 3, in seconds -/
  ahead : Nat := 86400
  past : Nat := 259200
  /-- 0005 -/
  groupsMax : Nat := 16
  /-- RFC 5536 §3.1.4 -/
  reserved : Bool := true
  /-- RFC 5537 §3.5 step 4 -/
  known : Bool := true
  /-- RFC 5537 §3.5 step 11: whether Injection-Date is added, from whether the proto-article had
  one, a Message-ID and a Date -/
  injectionDate : Bool → Bool → Bool → Bool := fun i m d => !i && !(m && d)
  /-- RFC 5537 §3.5 step 5: whether Message-ID and Date are added when the proto-article has them -/
  replace : Bool := false

def spec : Rules := {}

/-- What the server and this connection bring to the checks and the fields added. -/
structure Context where
  /-- the groups the server carries -/
  groups : List Bytes
  /-- the server's path identity (RFC 5537 §3.2) -/
  identity : Bytes
  /-- the wall clock, seconds since 1970-01-01T00:00:00Z -/
  wall : Nat
  /-- the article's sequence number in the store, in decimal digits, and the run's random value,
  in hexadecimal digits: a message identifier added is `<seq.random@identity>` -/
  seq : Nat
  random : Bytes
  /-- the run and the connection, for `logging-data` -/
  run : Nat
  conn : Nat

/-- A proto-article accepted: its header section as stored, with what was added, its message
identifier, and the groups the server carries that it names, each once, in order. -/
structure Accepted where
  header : Bytes
  messageId : Bytes
  groups : List Bytes
  deriving DecidableEq

inductive Verdict
  | refused (r : Refusal)
  | accepted (a : Accepted)
  deriving DecidableEq

/-- Whether rule `i` of the grammar matches all of `s`; a run that stops is a mismatch. -/
def grammarSays (i : Nat) (s : Bytes) : Bool :=
  match matches? grammar depth i (s.map (·.toNat)) with
  | .ok b => b
  | .error _ => false

/-- The grammar rule a field is checked by: its own, or `optional-field`. -/
def ruleOf (f : Field) : Nat :=
  ((fieldRules.find? fun p => named f.name p.1).map (·.2)).getD optionalField

/-- The place in the grammar of the rule named `n`; the names used here are the grammar's
(`ArticleModel.regression_873`). -/
def ruleNamed (n : String) : Nat := (AbnfRules.names.findIdx? (· == n)).getD 0

def isOne (names : List String) (f : Field) : Bool := names.any (named f.name ·)

/-- What is wrong with one field, if anything. -/
def fieldRefusal (r : Rules) (f : Field) : Option Refusal :=
  if isOne r.injected f then some (.injected f.name)
  else if isOne r.traced f then some (.traced f.name)
  else if isOne r.deprecated f then some (.deprecated f.name)
  else if isOne r.notOffered f then some (.notOffered f.name)
  else if r.blank && f.body.any (·.all isWS) then some (.blankLine f.name)
  else if !grammarSays (ruleOf f) f.text then some (.badField f.name)
  else none

/-- The first field that appears again, when it may appear once. -/
def repeatedFrom (r : Rules) : List Field → List Field → Option Bytes
  | [], _ => none
  | f :: more, seen =>
    if isOne r.once f && seen.any (sameName ·.name f.name) then some f.name
    else repeatedFrom r more (f :: seen)

def find? (fs : List Field) (n : String) : Option Field := fs.find? (named ·.name n)

/-- The fields that hold message identifiers, each at most 250 octets (RFC 5536 §3.1.3). -/
def idFields : List String := ["Message-ID", "References", "In-Reply-To", "Resent-Message-ID"]

/-- The date-time a field holds, if it holds one: RFC 5322 §3.3's rule is for all of them. -/
def dateText (f : Field) : Option Bytes :=
  if ["Date", "Injection-Date", "Expires", "Resent-Date"].any (named f.name ·) then some f.value
  else if named f.name "Received" then some (receivedDate 0 0 f.value)
  else none

def has (fs : List Field) (n : String) : Bool := (find? fs n).isSome

/-- The first check after the fields' own that fails. -/
def articleRefusal (r : Rules) (ctx : Context) (fs : List Field) : Option Refusal :=
  let window (n : String) : Option Refusal :=
    match (find? fs n).bind (dateValue ·.value) with
    | some t =>
      if t - (ctx.wall : Int) > (r.ahead : Int) then some (.dateAhead (ascii n))
      else if (ctx.wall : Int) - t > (r.past : Int) then some (.datePast (ascii n))
      else none
    | none => none
  let groups := ((find? fs "Newsgroups").map (listed ·.value)).getD []
  if let some n := repeatedFrom r fs [] then some (.repeated n)
  else if let some n := r.required.find? (!has fs ·) then some (.missing (ascii n))
  else if r.posted && ((find? fs "Path").map (·.value)).any (fun v => (pathElements v).any isPosted)
    then some .posted
  else if let some f :=
      fs.find? (fun f => isOne idFields f && (msgIds f.value).any (·.length > r.idMax))
    then some (.longMessageId f.name)
  else if r.sender && !has fs "Sender" &&
      ((find? fs "From").map (fun f => !grammarSays (ruleNamed "mailbox") f.value)).getD false
    then some .noSender
  else if r.distributionAll &&
      ((find? fs "Distribution").map (fun f => (listed f.value).any (named · "all"))).getD false
    then some .distributionAll
  else if let some f :=
      fs.find? (fun f => r.dates && (dateText f).any (fun t => (dateValue t).isNone))
    then some (.badDate f.name)
  else if let some x := window "Date" then some x
  else if let some x := window "Injection-Date" then some x
  else if groups.length > r.groupsMax then some .tooManyGroups
  else if r.reserved && groups.any reserved then some .reservedGroup
  else if r.known && !groups.any (ctx.groups.contains ·) then some .noKnownGroup
  else none

/-! ## What is added -/

def decimal (n : Nat) : Bytes := ascii (toString n)

/-- Path, first: the server's identity and `!.POSTED` before what the field held (RFC 5537
§3.2.1), or before `not-for-mail` when there was none (§3.5 step 8); folded after `!.POSTED`,
as §3.2.1 allows, if the line would be longer than the bound. -/
def pathField (r : Rules) (ctx : Context) (old : Option Field) : Bytes :=
  let head := ascii "Path: " ++ ctx.identity ++ ascii "!.POSTED"
  match old.map (·.body) with
  | some (first :: more) =>
    let rest := first.dropWhile isWS
    let lead := if (head ++ [BANG] ++ rest).length ≤ r.lineMax then [head ++ [BANG] ++ rest]
      else [head, ascii " !" ++ rest]
    ((lead ++ more).map (· ++ crlf)).flatten
  | _ => head ++ ascii "!not-for-mail" ++ crlf

def generatedId (ctx : Context) : Bytes :=
  ascii "<" ++ decimal ctx.seq ++ ascii "." ++ ctx.random ++ ascii "@" ++ ctx.identity ++ ascii ">"

/-- The header section the article is stored with. -/
def added (r : Rules) (ctx : Context) (fs : List Field) : Accepted :=
  let hasId := has fs "Message-ID"
  let hasDate := has fs "Date"
  let newId := !hasId || r.replace
  let newDate := !hasDate || r.replace
  let kept := fs.filter fun f => !named f.name "Path" &&
    !(r.replace && (named f.name "Message-ID" || named f.name "Date"))
  let msgId := if newId then generatedId ctx
    else (((find? fs "Message-ID").map (msgIds ·.value)).getD []).headD []
  let groups := ((find? fs "Newsgroups").map (listed ·.value)).getD []
  let known := groups.filter (ctx.groups.contains ·)
  { header := pathField r ctx (find? fs "Path") ++ (kept.map (·.text)).flatten ++
      (if newId then ascii "Message-ID: " ++ msgId ++ crlf else []) ++
      (if newDate then ascii "Date: " ++ formatDate ctx.wall ++ crlf else []) ++
      ascii "Injection-Info: " ++ ctx.identity ++ ascii "; logging-data=" ++ decimal ctx.run ++
        ascii "." ++ decimal ctx.conn ++ crlf ++
      (if r.injectionDate (has fs "Injection-Date") hasId hasDate
        then ascii "Injection-Date: " ++ formatDate ctx.wall ++ crlf else [])
    messageId := msgId
    groups := known.eraseDups }

/-- Whether the header section, CRLFs counted, is within the bound. -/
def fits (r : Rules) (ls : List Bytes) : Bool := (ls.map (·.length + 2)).sum ≤ r.headerMax

/-- **What a POST makes of a proto-article**, under rules `r`. -/
def checkWith (r : Rules) (ctx : Context) (a : Bytes) : Verdict :=
  let (ls, separated) := header a
  if ls.isEmpty then .refused .noHeader
  else if !separated then .refused .noSeparator
  else if !fits r ls then .refused .headerTooLong
  else if ls.any (·.length > r.lineMax) then .refused .lineTooLong
  else
    match fields ls with
    | none => .refused .malformed
    | some fs =>
      match fs.findSome? (fieldRefusal r) with
      | some x => .refused x
      | none =>
        match articleRefusal r ctx fs with
        | some x => .refused x
        | none => .accepted (added r ctx fs)

def check : Context → Bytes → Verdict := checkWith spec

/-! ## A context that fits -/

def isHexDigit (b : Byte) : Bool := isDigit b || (97 ≤ b.toNat && b.toNat ≤ 102)

/-- What the server is given has to fit what it adds: a path identity of the grammar and of at
most 200 octets, a random value of one to sixteen hexadecimal digits and a sequence number below
2^64, so that a message identifier added stays within 240 octets and so within 250; a run and a
connection below 2^64; at most 64 groups, each a newsgroup name of at most 64 octets that is not
reserved, none twice (0005, "Configuration"). -/
def Context.ok (ctx : Context) : Bool :=
  grammarSays (ruleNamed "path-identity") ctx.identity && ctx.identity.length ≤ 200 &&
    1 ≤ ctx.random.length && ctx.random.length ≤ 16 && ctx.random.all isHexDigit &&
    ctx.seq < 2 ^ 64 && ctx.run < 2 ^ 64 && ctx.conn < 2 ^ 64 &&
    ctx.groups.length ≤ 64 && ctx.groups.eraseDups.length == ctx.groups.length &&
    ctx.groups.all fun g =>
      g.length ≤ 64 && !reserved g && grammarSays (ruleNamed "newsgroup-name") g

/-! ## Every rule matters -/

/-- A version of the rules with one of them changed. -/
inductive Mutant
  | none
  /-- a header section one octet longer -/
  | headerLonger
  /-- a line one octet longer -/
  | lineLonger
  /-- Injection-Info taken -/
  | injectionInfoAllowed
  /-- Xref taken -/
  | xrefAllowed
  /-- the trace fields of older injecting agents taken -/
  | tracesAllowed
  /-- the deprecated fields taken -/
  | deprecatedAllowed
  /-- Control taken -/
  | controlAllowed
  /-- Supersedes taken -/
  | supersedesAllowed
  /-- Approved taken -/
  | approvedAllowed
  /-- a line of white space alone taken -/
  | blankAllowed
  /-- any field taken more than once -/
  | repeatsAllowed
  /-- Subject not required -/
  | subjectOptional
  /-- POSTED in Path taken -/
  | postedAllowed
  /-- a message identifier one octet longer -/
  | idLonger
  /-- From with several mailboxes and no Sender taken -/
  | senderUnneeded
  /-- the distribution "All" taken -/
  | allAllowed
  /-- dates not read for what they mean -/
  | datesUnread
  /-- a date one second further ahead -/
  | aheadLonger
  /-- a date one second further past -/
  | pastLonger
  /-- one group more -/
  | groupsMore
  /-- reserved groups taken -/
  | reservedAllowed
  /-- no group the server carries needed -/
  | unknownAccepted
  /-- Injection-Date added whenever the proto-article has none -/
  | injectionDateAlways
  /-- Message-ID and Date the server's even when the proto-article has them -/
  | replaced
  deriving DecidableEq

def rulesOf : Mutant → Rules
  | .none => spec
  | .headerLonger => { headerMax := 65537 }
  | .lineLonger => { lineMax := 999 }
  | .injectionInfoAllowed => { injected := ["Xref"] }
  | .xrefAllowed => { injected := ["Injection-Info"] }
  | .tracesAllowed => { traced := [] }
  | .deprecatedAllowed => { deprecated := [] }
  | .controlAllowed => { notOffered := ["Supersedes", "Approved"] }
  | .supersedesAllowed => { notOffered := ["Control", "Approved"] }
  | .approvedAllowed => { notOffered := ["Control", "Supersedes"] }
  | .blankAllowed => { blank := false }
  | .repeatsAllowed => { once := [] }
  | .subjectOptional => { required := ["From", "Newsgroups"] }
  | .postedAllowed => { posted := false }
  | .idLonger => { idMax := 251 }
  | .senderUnneeded => { sender := false }
  | .allAllowed => { distributionAll := false }
  | .datesUnread => { dates := false }
  | .aheadLonger => { ahead := 86401 }
  | .pastLonger => { past := 259201 }
  | .groupsMore => { groupsMax := 17 }
  | .reservedAllowed => { reserved := false }
  | .unknownAccepted => { known := false }
  | .injectionDateAlways => { injectionDate := fun i _ _ => !i }
  | .replaced => { replace := true }

def names : List (String × Mutant) :=
  [("header-longer", .headerLonger), ("line-longer", .lineLonger),
   ("injection-info-allowed", .injectionInfoAllowed), ("xref-allowed", .xrefAllowed),
   ("traces-allowed", .tracesAllowed), ("deprecated-allowed", .deprecatedAllowed),
   ("control-allowed", .controlAllowed), ("supersedes-allowed", .supersedesAllowed),
   ("approved-allowed", .approvedAllowed), ("blank-allowed", .blankAllowed),
   ("repeats-allowed", .repeatsAllowed), ("subject-optional", .subjectOptional),
   ("posted-allowed", .postedAllowed), ("id-longer", .idLonger),
   ("sender-unneeded", .senderUnneeded), ("all-allowed", .allAllowed),
   ("dates-unread", .datesUnread), ("ahead-longer", .aheadLonger),
   ("past-longer", .pastLonger), ("groups-more", .groupsMore),
   ("reserved-allowed", .reservedAllowed), ("unknown-accepted", .unknownAccepted),
   ("injection-date-always", .injectionDateAlways), ("replaced", .replaced)]

theorem rulesOf_none : rulesOf .none = spec := rfl

/-- A context for the examples: two groups, the wall clock at Mon, 21 Sep 2026 14:13:20 +0000. -/
def sample : Context :=
  { groups := [ascii "local.test", ascii "local.other"], identity := ascii "news.example.org",
    wall := 1790000000, seq := 7, random := ascii "5f3a", run := 1, conn := 2 }

def rest : String := "Newsgroups: local.test\r\nSubject: hi\r\n\r\nbody\r\n"
def minimal : String := "From: a@b.example\r\n" ++ rest

/-- A proto-article that tells the rules with one changed from the rules. -/
def witness : Mutant → Bytes
  | .none => ascii minimal
  | .headerLonger => List.replicate 65535 (BitVec.ofNat 8 120) ++ ascii "\r\n\r\n"
  | .lineLonger => List.replicate 999 (BitVec.ofNat 8 120) ++ ascii "\r\n\r\n"
  | .injectionInfoAllowed => ascii "Injection-Info:\r\n\r\n"
  | .xrefAllowed => ascii "Xref:\r\n\r\n"
  | .tracesAllowed => ascii "X-Trace:\r\n\r\n"
  | .deprecatedAllowed => ascii "See-Also:\r\n\r\n"
  | .controlAllowed => ascii "Control:\r\n\r\n"
  | .supersedesAllowed => ascii "Supersedes:\r\n\r\n"
  | .approvedAllowed => ascii "Approved:\r\n\r\n"
  | .blankAllowed => ascii "Subject:\r\n\r\n"
  | .repeatsAllowed => ascii "Subject: a\r\nSubject: b\r\n\r\n"
  | .subjectOptional =>
    ascii "From: a@b.example\r\nNewsgroups: local.test\r\nPath: a!.POSTED!x\r\n\r\n"
  | .postedAllowed => ascii ("Path: a.example!.POSTED!not-for-mail\r\n" ++ minimal)
  | .idLonger => ascii ("Message-ID: <" ++ String.ofList (List.replicate 239 'a') ++
      "@b.example>\r\n" ++ minimal)
  | .senderUnneeded => ascii ("From: a@b.example, c@d.example\r\n" ++ rest)
  | .allAllowed => ascii ("Distribution: all\r\n" ++ minimal)
  | .datesUnread => ascii ("Date: Thu, 31 Sep 2026 14:13:20 +0000\r\n" ++ minimal)
  | .aheadLonger => ascii ("Date: Tue, 22 Sep 2026 14:13:21 +0000\r\n" ++ minimal)
  | .pastLonger => ascii ("Date: Fri, 18 Sep 2026 14:13:19 +0000\r\n" ++ minimal)
  | .groupsMore => ascii ("From: a@b.example\r\nNewsgroups: local.test,a.a,a.b,a.c,a.d,a.e," ++
      "a.f,a.g,a.h,a.i,a.j,a.k,a.l,a.m,a.n,a.o,a.p\r\nSubject: hi\r\n\r\n")
  | .reservedAllowed =>
    ascii "From: a@b.example\r\nNewsgroups: local.test,example.test\r\nSubject: hi\r\n\r\n"
  | .unknownAccepted => ascii "From: a@b.example\r\nNewsgroups: alt.test\r\nSubject: hi\r\n\r\n"
  | .injectionDateAlways | .replaced =>
    ascii ("Message-ID: <x@y.example>\r\nDate: Mon, 21 Sep 2026 14:00:00 +0000\r\n" ++ minimal)

/-- Bytes other than CR go into the line being read. -/
theorem headerFrom_run (x : Byte) (hx : x ≠ CR) (acc : List Bytes) :
    ∀ (n : Nat) (cur rest : Bytes),
      headerFrom (List.replicate n x ++ rest) false cur acc =
        headerFrom rest false (List.replicate n x ++ cur) acc := by
  intro n
  induction n with
  | zero => intro cur rest; rfl
  | succ n ih =>
    intro cur rest
    rw [List.replicate_succ, List.cons_append]
    simp only [headerFrom, Bool.false_and, Bool.false_eq_true, ↓reduceIte, beq_iff_eq, hx]
    have e : List.replicate n x ++ x :: cur = x :: (List.replicate n x ++ cur) := by
      rw [← List.singleton_append, ← List.append_assoc, ← List.replicate_succ',
        List.replicate_succ, List.cons_append]
    rw [ih, e, List.cons_append]

/-- A header section of one line, then the empty line. -/
theorem header_line (x : Byte) (hx : x ≠ CR) (n : Nat) :
    header (List.replicate (n + 1) x ++ [CR, LF, CR, LF]) = ([List.replicate (n + 1) x], true) := by
  simp only [header]
  rw [headerFrom_run x hx [] (n + 1) [] _, List.append_nil]
  simp [headerFrom, CR, LF, List.reverse_replicate]

/-- A header section past the bound is refused for its length. -/
theorem refused_long (r : Rules) (ctx : Context) (a : Bytes) (ls : List Bytes)
    (h : header a = (ls, true)) (hne : ls ≠ []) (hf : fits r ls = false) :
    checkWith r ctx a = .refused .headerTooLong := by
  unfold checkWith
  rw [h]
  simp [List.isEmpty_iff, hne, hf]

/-- A header section within the bound, with a line past its bound, is refused for the line. -/
theorem refused_line (r : Rules) (ctx : Context) (a : Bytes) (ls : List Bytes)
    (h : header a = (ls, true)) (hne : ls ≠ []) (hf : fits r ls = true)
    (hl : ls.any (·.length > r.lineMax) = true) :
    checkWith r ctx a = .refused .lineTooLong := by
  unfold checkWith
  rw [h]
  simp [List.isEmpty_iff, hne, hf, hl]

theorem fits_one (r : Rules) (x : Byte) (k : Nat) :
    fits r [List.replicate k x] = decide (k + 2 ≤ r.headerMax) := by
  simp only [fits, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_replicate,
    Nat.add_zero]

theorem long_one (m : Nat) (x : Byte) (k : Nat) :
    [List.replicate k x].any (·.length > m) = decide (k > m) := by
  simp only [List.any_cons, List.any_nil, List.length_replicate, Bool.or_false]

/-- The bound on the header section matters: its witness, a section of 65,537 octets, is refused
for its length, and with the bound one octet higher for the length of its line. The kernel would
take minutes to run the checks on it, so the section is read by `header_line`. -/
theorem header_bound_matters :
    check sample (witness .headerLonger) = .refused .headerTooLong ∧
      checkWith (rulesOf .headerLonger) sample (witness .headerLonger) = .refused .lineTooLong := by
  have w : witness .headerLonger =
      List.replicate (65534 + 1) (BitVec.ofNat 8 120) ++ [CR, LF, CR, LF] := rfl
  have h := header_line (BitVec.ofNat 8 120) (by decide) 65534
  rw [w]
  constructor
  · exact refused_long spec sample _ _ h (List.cons_ne_nil _ _) (by rw [fits_one]; decide)
  · exact refused_line _ sample _ _ h (List.cons_ne_nil _ _) (by rw [fits_one]; decide)
      (by rw [long_one]; decide)

set_option maxHeartbeats 2000000 in
/-- **Each rule matters**: with it changed, its witness gets another verdict. -/
theorem mutants_differ : ∀ m, m ≠ .none →
    checkWith (rulesOf m) sample (witness m) ≠ check sample (witness m) := by
  intro m hm
  cases m
  case none => exact absurd rfl hm
  case headerLonger =>
    rw [header_bound_matters.1, header_bound_matters.2]
    decide
  all_goals decide +kernel

end DN.News.ArticleSpec
