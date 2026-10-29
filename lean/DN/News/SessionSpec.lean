-- SPDX-License-Identifier: AGPL-3.0-or-later
import DN.News.CommandSpec
import DN.News.Framer
import DN.News.PostSpec

/-!
# DN.News.SessionSpec

The session of docs/decisions/0003-nntp-slice.md as a function of what the host reports, apart
from the program that runs it (`DN.Server.Session`): a table of connections, and a turn that takes
the host's batch of events and gives back at most one action per connection.

A connection is greeted when it opens. Its input is held as received and framed a line at a time
(`DN.News.Framer.frameOnce`); a line is answered only while nothing the connection was sent is
still untaken, so replies go out in the order of the commands, one per command, and a connection
that does not read stops being read from. After a QUIT the reply is the last thing sent and the
connection is closed gracefully once it is taken, and likewise after the 502 that a server without a
store gives to MODE READER, as it does not advertise READER (RFC 3977 §5.3.2); after the end of input
the connection is closed the same way once every whole line it sent is answered. A deadline that passes closes the
connection at once, dropping what was not sent: ten seconds for the first command; 1,800 seconds
with no command answered and no output taken; 180 seconds for the rest of a line, from when the
program begins waiting for it — everything sent taken, a line begun — and only while it waits.

The host reads from a connection only while the last action for it asked to and everything that
action carried has been taken, and reports its input once a batch. After a batch of actions it
reports how many bytes of each send the kernel took (`settle`); what it did not take is sent again
once the host reports the connection ready to write. The program then names the earliest time it
needs a turn (`deadline`): the current time when a connection can go on at once, otherwise its
earliest deadline. A host that reports what it may not ends the run with a code (`Breach`).

With a store (docs/decisions/0005-article-store.md), a connection is greeted with 200 when it may
post, the store accepts and carries a group, and with 201 otherwise. A well-formed POST of one
greeted so gets 340 once one of `DN.News.PostSpec`'s slots is free for it, POSTs waiting in the
order they came, unanswered and unread, with no deadline running; 440 if it was greeted with 201;
403 once the store has stopped accepting. From the 340 the article has 1,800 seconds to arrive, which its octets do not
renew; its octets go to the slot while it takes them, the host told to read or not with an empty
send when that changes; once the block has ended, no deadline runs until the slot answers 240 or
441, or closes the connection when the outcome is unknown; with the answer, what follows the
article is framed as lines are. An ARTICLE, HEAD or BODY of an article the store holds waits, like a
POST, for one of eight reads, in the order they came; the read's octets go out a send at a time as
the host takes them, the host not told to read until the read ends, and inactivity runs only while
some of them are untaken. A read that fails before giving anything is answered 403; after, the
connection is closed. STAT of an article the store holds is answered 223, and any of the four of
one it does not hold 430. Each turn, after the events, the completions of file jobs, then the
connections in order, then the slots' and the reads' next jobs.

A connection has a selected group and a current article number, both invalid at first (RFC 3977
§6.1). GROUP of a group the store carries selects it and makes its first article current, none in
an empty group, and answers 211 with the count of its articles and their lowest and highest
numbers, an empty group's highest one below its lowest; of another, 411, changing nothing. By
number, ARTICLE, HEAD, BODY and STAT find the article of that number in the selected group and make
it current, or answer 423; with no argument they take the current article, or answer 420; NEXT and
LAST move to the article of the lowest number above the current one or the highest below, answer
223 with it, or 421 and 422 when there is none. Without a group selected each of these is answered
412. An article read is made current with the first line of its reply, not after a 403 (§6.2.1.2).
By message-id nothing changes, and the number given is 0. What a group holds is what the store
holds as the line is answered.

LISTGROUP selects a group as GROUP does, the named one or the selected one, and answers 211 as GROUP
does, then the numbers of the group's articles in its range, all from 1 without one (§6.1.2): those
up to the group's highest number as it is selected, which an article the store takes later passes.
LIST ACTIVE, and LIST, answers 215, then a line for each group the store carries that its wildmat
matches, all without one, in the order the host gave them: its name, its highest and lowest numbers
as GROUP gives them, and `y` while the store accepts, else `n` (§7.6.3), as the store is when the line
is sent. Such a reply goes out a part at a time: its next lines, as many as one action carries, its
terminating line once that fits too, each when the last was taken; the host is not told to read and
no line is answered until it ends. LIST NEWSGROUPS answers 215 and an empty list, as no group has a
description, and NEWGROUPS 231 and an empty list, as no group has a time it was created (§7.6.6,
§7.3.2). DATE answers 111 with the host's wall clock in UTC (§7.1).

The capabilities name READER and LIST's keywords ACTIVE and NEWSGROUPS (§3.3.2, §7.6.2), with POST
while the connection may post. As a server that is not mode-switching and advertises READER, it
answers MODE READER as the greeting does now — 200 when POST is among the capabilities, else 201 —
changing nothing (§5.3.2).

OVER and HDR, and their RFC 2980 spellings XOVER and XHDR, name an article by its message-id, the
selected group's articles in a range as the store holds them when the line is answered, or the
current article (`viewOf`), and wait for a read as ARTICLE does: the read gives each article's line
in turn (`DN.News.PostSpec.View`), and none is made current. With none to give they are answered
430, 412, 420, or for a range 423, and XOVER and XHDR 224 and 221 with an empty list.
-/

namespace DN.News.SessionSpec

open DN.News.FrameSpec DN.News.Framer DN.News.CommandSpec
open DN.News.PostSpec (Store Slot Job Done Fault Read View)

/-- Connections the table holds. -/
def conns : Nat := 64
/-- Events in one batch. -/
def batch : Nat := 16
/-- Bytes in one event or one action. -/
def chunk : Nat := 512
/-- A command line, with its line end (RFC 3977 §3.1). -/
def lineLimit : Nat := 512
/-- Deadlines, in milliseconds of the host's clock. -/
def firstCommand : Nat := 10000
def inactivity : Nat := 1800000
def lineTime : Nat := 180000
def articleTime : Nat := 1800000
/-- The host's clock stays below this, so deadlines never overflow a signed word. -/
def clockLimit : Nat := 2 ^ 62
/-- The host's wall clock, in milliseconds, stays below this: an article's dates are read for
seconds below 2^40, past the year 36,000. -/
def wallLimit : Nat := 1000 * 2 ^ 40
/-- A connection's generation, which the host counts up at each index, stays at or below this: past
it the host no longer uses the index. -/
def genLimit : Nat := 2 ^ 62

inductive Phase
  /-- greeted, no command yet or commands being answered -/
  | open_
  /-- the reply to QUIT, or MODE READER's 502, is being sent; the connection closes when it is taken -/
  | quitting
  /-- the input has ended; what was received is answered, then the connection closes -/
  | ending
  deriving DecidableEq, Repr

/-- What is left of a reply that goes out a part at a time (`Listing.part`): the numbers of the
articles of group `g` from `from_` up to `upto`; or the groups from the `next`th the store carries, of
those the wildmat matches, all with none. -/
inductive Listing
  | numbers (g : List Byte) (from_ upto : Nat)
  | groups (w : Option Wildmat) (next : Nat)
  deriving DecidableEq, Repr

structure Conn where
  gen : Nat
  phase : Phase
  /-- the framer's state: the line being read -/
  line : LineState
  /-- bytes received and not yet framed -/
  held : List Byte
  /-- bytes to send that the host has not yet taken -/
  out : List Byte
  /-- whether the last action asked the host to read -/
  reading : Bool
  /-- whether the host left part of a send untaken and has not yet reported the connection ready -/
  blocked : Bool
  /-- deadlines, zero when not running -/
  first : Nat
  idle : Nat
  lineDue : Nat
  /-- its number among the connections of the run, from one -/
  number : Nat := 0
  /-- whether it was greeted with 200 -/
  greeted : Bool := false
  /-- whether a POST waits for a slot -/
  waiting : Bool := false
  /-- the slot of its POST, from the 340 until the answer -/
  post : Option Nat := none
  /-- the article's deadline, zero when not running -/
  articleDue : Nat := 0
  /-- the ARTICLE, HEAD or BODY it waits for a read for or is answered by one, with the number its
  first line gives and the message-id -/
  want : Option (Cmd × Nat × List Byte) := none
  /-- the read that answers it -/
  read : Option Nat := none
  /-- for an OVER or HDR, what the read gives of the article and the articles after it -/
  view : Option View := none
  /-- the selected group and the current article number, `none` and zero while invalid -/
  group : Option (List Byte) := none
  current : Nat := 0
  /-- what is left of a reply that goes out a part at a time -/
  listing : Option Listing := none
  deriving DecidableEq, Repr

def Conn.fresh (i : Identity) (greeted : Bool) (number gen now : Nat) : Conn :=
  { gen, phase := .open_, line := .fresh, held := [],
    out := if greeted then greetingPost i else greeting i, reading := false, blocked := false,
    first := now + firstCommand, idle := now + inactivity, lineDue := 0, number, greeted }

inductive Event
  /-- a connection opened, and whether it may post -/
  | opened (idx gen : Nat) (mayPost : Bool)
  | received (idx gen : Nat) (data : List Byte)
  | writable (idx gen : Nat)
  | inputEnded (idx gen : Nat)
  | closed (idx gen : Nat)
  deriving DecidableEq, Repr

inductive Action
  /-- send the bytes, and read from the connection once they are taken or not -/
  | send (idx gen : Nat) (data : List Byte) (read : Bool)
  /-- everything was taken: close after the host's lingering read -/
  | closeGracefully (idx gen : Nat)
  | closeNow (idx gen : Nat)
  deriving DecidableEq, Repr

/-- What a host may not report; each ends the run. -/
inductive Breach
  /-- more events than a batch holds -/
  | tooManyEvents
  /-- more bytes than a chunk in one event -/
  | tooLong
  /-- an index past the table -/
  | noSuchIndex
  /-- input from a connection that was not asked for it -/
  | unasked
  /-- more bytes taken than a send carried, or a count for no send -/
  | overTaken
  /-- a connection opened at an index still in use, at a generation not past the last there, or past
  `genLimit` -/
  | reopened
  /-- a clock earlier than the last batch's, or not below `clockLimit`; a wall clock not below
  `wallLimit` -/
  | badClock
  /-- a completion of a file job the host may not report -/
  | job (f : Fault)
  deriving DecidableEq, Repr

/-- The codes 8 to 12 are the program's own (`DN.Server.SessionLayout`). -/
def Breach.code : Breach → Nat
  | .tooManyEvents => 1 | .tooLong => 2 | .noSuchIndex => 3 | .unasked => 4 | .overTaken => 5
  | .reopened => 6 | .badClock => 7 | .job .unknownJob => 13 | .job .badDone => 14

abbrev Table := List (Option Conn)

def Table.empty : Table := List.replicate conns none

/-- The table, the host's clock at the last batch, the store if there is one, how many connections
have opened, and the last generation opened at each index. -/
structure Server where
  table : Table := Table.empty
  clock : Nat := 0
  store : Option Store := none
  opened : Nat := 0
  gens : List Nat := List.replicate conns 0

/-- The connection at `idx` if it is the one of generation `gen`. -/
def Table.live (t : Table) (idx gen : Nat) : Option Conn :=
  match t[idx]? with
  | some (some c) => if c.gen = gen then some c else none
  | _ => none

def checkIndex (idx : Nat) : Except Breach Unit :=
  if idx < conns then pure () else throw .noSuchIndex

/-- Whether the host may report input on the connection: it takes commands, the last action asked
it to read, everything sent was taken and nothing received waits. -/
def Conn.asked (c : Conn) : Bool :=
  c.phase == .open_ && c.reading && c.out.isEmpty && c.held.isEmpty

/-- Whether a connection is greeted with 200: it may post, and the store accepts and carries a
group. -/
def greets (st : Option Store) (mayPost : Bool) : Bool :=
  mayPost && st.any fun st => st.accepting && !st.cfg.groups.isEmpty

/-- One event. An event for a connection the table does not hold, or of an older generation, is
left alone. The end of input, or a close, abandons the article of a block not ended. -/
def applyEvent (i : Identity) (now : Nat) (s : Server) : Event → Except Breach Server
  | .opened idx gen mayPost => do
    checkIndex idx
    match s.table[idx]? with
    | some (some _) => throw .reopened
    | _ =>
      if gen ≤ s.gens.getD idx 0 || genLimit < gen then throw .reopened
      else
        let c := Conn.fresh i (greets s.store mayPost) (s.opened + 1) gen now
        return { s with table := s.table.set idx (some c), opened := s.opened + 1,
                        gens := s.gens.set idx gen }
  | .received idx gen data => do
    checkIndex idx
    if chunk < data.length then throw .tooLong
    match s.table.live idx gen with
    | some c =>
      if c.asked then return { s with table := s.table.set idx (some { c with held := data }) }
      else throw .unasked
    | none => return s
  | .writable idx gen => do
    checkIndex idx
    match s.table.live idx gen with
    | some c => return { s with table := s.table.set idx (some { c with blocked := false }) }
    | none => return s
  | .inputEnded idx gen => do
    checkIndex idx
    match s.table.live idx gen with
    | some c =>
      if c.asked then
        let c' := { c with phase := .ending, lineDue := 0, post := none, articleDue := 0, want := none,
                           read := none, view := none }
        return { s with
          table := s.table.set idx (some c'),
          store := s.store.map (Store.abandon idx gen) }
      else throw .unasked
    | none => return s
  | .closed idx gen => do
    checkIndex idx
    match s.table.live idx gen with
    | some _ =>
      return { s with table := s.table.set idx none, store := s.store.map (Store.abandon idx gen) }
    | none => return s

/-- Whether a deadline has passed. -/
def Conn.due (c : Conn) (now : Nat) : Bool :=
  (c.first != 0 && c.first ≤ now) || (c.idle != 0 && c.idle ≤ now) ||
    (c.lineDue != 0 && c.lineDue ≤ now) || (c.articleDue != 0 && c.articleDue ≤ now)

/-- Whether the host should read from the connection: it takes commands and holds none. -/
def Conn.wants (c : Conn) : Bool := c.phase == .open_ && c.held.isEmpty

/-- …and no POST or read waits or is answered, no reply goes out a part at a time, and the slot of its
POST takes octets. -/
def Conn.wantsWith (st : Option Store) (c : Conn) : Bool :=
  c.wants && !c.waiting && c.want.isNone && c.listing.isNone && match c.post with
    | none => true
    | some k => st.any fun st => (st.slot k).any Slot.takes

/-- The line's deadline runs while the program waits for the rest of a line: everything sent was
taken, the connection takes commands, is not answered by a read and has no reply going out a part at
a time, and a line is begun. It starts when the waiting starts, and nothing but the end of the
waiting moves it. -/
def Conn.waitLine (now : Nat) (c : Conn) : Conn :=
  if c.out.isEmpty && c.phase == .open_ && c.line != .fresh && c.want.isNone && c.listing.isNone then
    if c.lineDue == 0 then { c with lineDue := now + lineTime } else c
  else { c with lineDue := 0 }

/-- What a store makes of a reply: whether POST is offered, whether the store accepts, the groups it
carries and the commits of the articles it holds; and the wall clock, which DATE gives. -/
structure Posting where
  offered : Bool
  accepting : Bool
  groups : List (List Byte)
  held : List Journal.Commit
  wall : Nat

/-- What a store makes of a reply, if there is one, at the wall clock `wall`. -/
def Posting.of (wall : Nat) : Option Store → Posting
  | some st => ⟨true, st.accepting, st.cfg.groups, st.articles, wall⟩
  | none => ⟨false, false, [], [], wall⟩

/-- The articles held in group `g`: each one's number there and its message-id. -/
def numbered (held : List Journal.Commit) (g : List Byte) : List (Nat × List Byte) :=
  held.filterMap fun c => (c.groups.find? (·.name == g)).map fun x => (x.number, c.messageId)

/-- Of the articles held in group `g`, the one numbered `n`. -/
def atNumber (held : List Journal.Commit) (g : List Byte) (n : Nat) : Option (Nat × List Byte) :=
  (numbered held g).find? (·.1 == n)

/-- Of the articles held in group `g`, the one of the lowest number above `n`, and the one of the
highest below. -/
def nextAfter (held : List Journal.Commit) (g : List Byte) (n : Nat) : Option (Nat × List Byte) :=
  (numbered held g).foldl (fun best x => if n < x.1 && best.all (x.1 < ·.1) then some x else best) none
def prevBefore (held : List Journal.Commit) (g : List Byte) (n : Nat) : Option (Nat × List Byte) :=
  (numbered held g).foldl (fun best x => if x.1 < n && best.all (·.1 < x.1) then some x else best) none

/-- The 211 of group `g`: how many articles it holds and their lowest and highest numbers; of an
empty group, the highest one below the lowest, as RFC 3977 §6.1.1.2 prefers. -/
def summary (held : List Journal.Commit) (g : List Byte) : Reply :=
  match (numbered held g).map (·.1) with
  | [] => .selected 0 1 0 g
  | x :: rest => .selected (rest.length + 1) (rest.foldl min x) (rest.foldl max x) g

/-- `n` in decimal digits, at least `k` of them, zeros before it. -/
def padded (k n : Nat) : List Byte := List.replicate (k - (decimal n).length) 48#8 ++ decimal n

/-- The wall clock, in milliseconds, as DATE gives it (§7.1): `yyyymmddhhmmss` in UTC, the year in
four digits, or as many as it has past the year 9999. -/
def dateDigits (wall : Nat) : List Byte :=
  let secs := wall / 1000
  let date := ArticleSpec.civilFromDays (secs / 86400)
  let t := secs % 86400
  padded 4 date.1 ++ padded 2 date.2.1 ++ padded 2 date.2.2 ++ padded 2 (t / 3600) ++
    padded 2 (t % 3600 / 60) ++ padded 2 (t % 60)

/-- What an article of group `g` found gives: 223 for STAT, else a read. -/
def foundAs (k : Cmd) : Nat × List Byte → Reply
  | (n, id) => if k = .stat then .stat n id else .lookup k n id

/-- The articles an OVER or HDR names, read for their lines (`overview`): by message-id the one the
store holds, number 0, else 430; of a range the selected group's within it, by their numbers, as the
store holds them when the line is answered, else 423, and for XOVER and XHDR an empty list as INN
gives it; with neither the current article, else 420; with no group selected 412. Nothing is made
current (§8.3.2, §8.5.2). -/
def viewOf (p : Posting) (c : Conn) (lg : Bool) (f : Option (List Byte)) : Sel → Reply
  | .id mid => if p.held.any (·.messageId == mid) then .overview lg f true [(0, mid)] else .noSuchId
  | .range lo hi =>
    match c.group with
    | none => .noGroup
    | some g =>
      match ((numbered p.held g).filter fun x => lo ≤ x.1 && x.1 ≤ hi).mergeSort fun a b => a.1 ≤ b.1 with
      | [] => if lg then (if f.isSome then .noneHdr else .noneOver) else .noRange
      | items => .overview lg f false items
  | .current =>
    match c.group with
    | none => .noGroup
    | some g =>
      if c.current = 0 then .noCurrent
      else ((atNumber p.held g c.current).map fun x => .overview lg f false [x]).getD .noCurrent

/-- The reply a connection gets with a store: the capabilities with READER, and with POST while it
may post, and MODE READER's 200 or 201 as they name POST or not; the help with POST, for a
well-formed POST 340, 440 or 403, and for a message-id the store does not hold 430, for one it holds
with STAT 223; the replies of the selected group and the current article. Without a store, the
capabilities and the help of 0003, and MODE READER's 502. -/
def resolve (p : Posting) (c : Conn) : Reply → Reply
  | .capabilities =>
    if c.greeted && p.accepting then .capabilitiesPost else if p.offered then .capabilitiesReader
    else .capabilities
  | .modeReader =>
    if !p.offered then .modeReader else if c.greeted && p.accepting then .readerPosting
    else .readerNoPosting
  | .help => if p.offered then .helpPost else .help
  | .post => if !c.greeted then .notPermitted else if !p.accepting then .unavailable else .post
  | .lookup k n id =>
    if !p.held.any (·.messageId == id) then .noSuchId else if k = .stat then .stat n id else .lookup k n id
  | .select g => if p.groups.contains g then summary p.held g else .noSuchGroup
  | .byNumber k n =>
    match c.group with
    | none => .noGroup
    | some g => ((atNumber p.held g n).map (foundAs k)).getD .noNumber
  | .current k =>
    match c.group with
    | none => .noGroup
    | some g => if c.current = 0 then .noCurrent else ((atNumber p.held g c.current).map (foundAs k)).getD .noCurrent
  | .move fwd =>
    match c.group with
    | none => .noGroup
    | some g =>
      if c.current = 0 then .noCurrent
      else (((if fwd then nextAfter else prevBefore) p.held g c.current).map fun (n, id) => .stat n id).getD
        (if fwd then .noNext else .noPrevious)
  | .listGroup g lo hi =>
    match g.orElse fun _ => c.group with
    | none => .noGroup
    | some g =>
      if p.groups.contains g then
        match summary p.held g with
        | .selected count low high g => .listed count low high g lo hi
        | r => r
      else .noSuchGroup
  | .date => .time (dateDigits p.wall)
  | .over lg s => viewOf p c lg none s
  | .hdr lg f s => viewOf p c lg (some f) s
  | r => r

/-- The line of LIST ACTIVE for group `g`: its name, its highest and lowest numbers as GROUP gives
them, and `y` while the store accepts, else `n` (§7.6.3). No name the store carries starts with a
dot (`ArticleSpec.Context.ok`), so no line needs one put before it. -/
def activeLine (p : Posting) (g : List Byte) : List Byte :=
  match summary p.held g with
  | .selected _ low high _ =>
    g ++ SP :: decimal high ++ SP :: decimal low ++ SP :: ascii (if p.accepting then "y" else "n") ++ crlf
  | _ => []

/-- What is left to go out of a reply after its first line: LISTGROUP's numbers up to the group's
highest as it is selected, LIST ACTIVE's groups from the first. -/
def listingOf : Reply → Option Listing
  | .listed _ _ high g lo hi => some (.numbers g lo (min hi high))
  | .active w => some (.groups w 0)
  | _ => none

/-- What a reply answered by a read waits for: the command, the number its first line gives and the
message-id of its article, and for an OVER or HDR what is read of it and the articles after it, by
their commits as the store holds them when the line is answered. -/
def readOf (p : Posting) : Reply → Option (Cmd × Nat × List Byte × Option View)
  | .lookup k n id => some (k, n, id, none)
  | .overview lg f byId ((n, id) :: rest) =>
    let more := rest.filterMap fun x => (p.held.find? (·.messageId == x.2)).map fun cm => (x.1, cm)
    some (if f.isSome then .hdr else .over, n, id, some { legacy := lg, field := f, byId, rest := more })
  | _ => none

/-- A listing's next line, and the listing after it, none once it has no line left: of the groups
`takes` takes, each's line as `line` writes it. -/
def nextWith (takes : Wildmat → List Byte → Bool) (line : List Byte → List Byte) (p : Posting) :
    Listing → Option (List Byte × Listing)
  | .numbers g from_ upto =>
    match (((numbered p.held g).map (·.1)).filter fun n => from_ ≤ n && n ≤ upto).min? with
    | some n => some (decimal n ++ crlf, .numbers g (n + 1) upto)
    | none => none
  | .groups w next =>
    match ((p.groups.drop next).zipIdx next).find? (fun (g, _) => w.all (takes · g)) with
    | some (g, k) => some (line g, .groups w (k + 1))
    | none => none

def Listing.next (p : Posting) : Listing → Option (List Byte × Listing) := nextWith wildmatch (activeLine p) p

/-- After `acc`, a listing's next lines as long as they fit `most` octets, then its terminating line
once that fits too; with what is left, none once the terminating line is given. -/
def partWith (next : Listing → Option (List Byte × Listing)) (most : Nat) :
    Nat → List Byte → Listing → List Byte × Option Listing
  | 0, acc, l => (acc, some l)
  | fuel + 1, acc, l =>
    match next l with
    | some (line, l') => if acc.length + line.length ≤ most then partWith next most fuel (acc ++ line) l' else (acc, some l)
    | none => if acc.length + 3 ≤ most then (acc ++ ascii ".\r\n", none) else (acc, some l)

/-- **A listing's next part**, of one action at most. A line has at least three octets, so `fuel` of
one more than an action's is enough; each part holds a line or the terminating one, and leaves less
of the listing (`part_progress`). -/
def Listing.part (p : Posting) : Nat → List Byte → Listing → List Byte × Option Listing :=
  partWith (Listing.next p) chunk

/-- Answer the first held line that gets a reply, putting it in `out`, and frame on past the lines
that get none and into an unfinished last line, stopping before the next line that gets a reply: a
connection holds input only while such a line waits. A connection with output untaken, an ARTICLE,
HEAD or BODY to be answered by a read, or a reply going out a part at a time, answers nothing; a POST
that may have a slot waits for one. Each round frames at least one byte, so `fuel`
of one more than the held bytes is enough; a line left unanswered was framed from the start of a
line, so the framer's state is left as it was. -/
def serve (i : Identity) (p : Posting) (now : Nat) : Nat → Conn → Conn
  | 0, c => c
  | fuel + 1, c =>
    if c.held.isEmpty then c
    else
      let (k, line', v) := frameOnce lineLimit c.line c.held
      let c1 := { c with line := line', held := c.held.drop k }
      match v with
      | none => c1
      | some l =>
        match resolve p c (replyIn p.offered l) with
        | .ignore => serve i p now fuel c1
        | r =>
          if !c.out.isEmpty || c.want.isSome || c.listing.isSome then c
          else if r = .post then { c1 with waiting := true, first := 0, idle := 0 }
          else if let some (k, n, id, v) := readOf p r then
            serve i p now fuel { c1 with want := some (k, n, id), view := v, first := 0, idle := 0 }
          else
            let c2 := { c1 with out := text i r, first := 0, idle := now + inactivity,
                                group := r.groupAfter c1.group, current := r.currentAfter c1.current,
                                listing := listingOf r }
            if r = .quit ∨ r = .modeReader then { c2 with phase := .quitting, held := [] }
            else serve i p now fuel c2

/-- The reply an outcome gives. -/
def outcomeReply : PostSpec.Outcome → Reply
  | .posted => .posted
  | _ => .failed

/-- A connection in a POST with nothing untaken: its held octets framed into its slot while it
takes them, the article's deadline stopped once the block has ended, and the slot's outcome put to
send, what it holds after the article framed on as `serve` frames lines — or, when the outcome is
unknown, the connection to close. -/
def progress (i : Identity) (now wall : Nat) (st : Option Store) (c : Conn) :
    Conn × Option Store × Bool :=
  match c.post, st with
  | some k, some st =>
    if !c.out.isEmpty || c.phase = .quitting then (c, some st, false)
    else
      let f := st.feed wall k (c.held.length + 1) c.held
      let st1 := f.1.tidy
      match st1.slot k with
      | some s =>
        let freed := (st1.setSlot k (some { s with owner := none })).tidy
        let due := if s.ended then 0 else c.articleDue
        match s.outcome with
        | some .lost => ({ c with held := f.2, articleDue := due }, some freed, true)
        | some o =>
          let c' := { c with
            held := f.2, articleDue := due, out := text i (outcomeReply o), post := none,
            idle := now + inactivity }
          (serve i (Posting.of wall (some freed)) now (f.2.length + 1) c', some freed, false)
        | none => ({ c with held := f.2, articleDue := due }, some st1, false)
      | none => ({ c with held := f.2, post := none }, some st1, false)
  | _, st => (c, st, false)

/-- A POST that waits gets a free slot, and 340, when fewer came before it than slots are free; or
403 once the store has stopped accepting. -/
def claim (i : Identity) (now idx : Nat) (st : Option Store) (c : Conn) : Conn × Option Store :=
  match st with
  | some st =>
    if c.waiting && c.out.isEmpty && c.phase = .open_ then
      let st' := { st with waiters := st.waiters.erase (idx, c.gen) }
      if !st.accepting then
        ({ c with waiting := false, out := text i .unavailable, idle := now + inactivity }, some st')
      else if st.admits (idx, c.gen) then
        match (List.range st.rules.posts).find? st.free with
        | some k =>
          let c' := { c with
            waiting := false, post := some k, out := text i .post, articleDue := now + articleTime }
          (c', some (st'.setSlot k (some { owner := some (idx, c.gen), conn := c.number })))
        | none => (c, some st)
      else (c, some st)
    else (c, some st)
  | none => (c, none)

/-- A connection answered by a read, with nothing untaken: the read's next octets put to send, the
inactivity deadline then started, or stopped while there are none, the article made current with
the first of them when it was named by its number; once all of them are put, the read ended, or for
an OVER or HDR given the next article, an article whose XHDR line is left out among them; a read that failed answered 403 when nothing was given for its
command, or the connection to close. -/
def progressRead (i : Identity) (now : Nat) (st : Option Store) (c : Conn) :
    Conn × Option Store × Bool :=
  match c.read, st with
  | some k, some st =>
    if !c.out.isEmpty || c.phase = .quitting then (c, some st, false)
    else
      match st.readSlot k with
      | some r =>
        if r.bad then
          if r.given = 0 && r.view.all (·.first) then
            ({ c with out := text i .unreadable, read := none, want := none, view := none,
                      idle := now + inactivity },
             some (st.setRead k (some { r with owner := none })).tidy, false)
          else (c, some st, true)
        else
          let piece := (r.out.extract r.given (r.given + CommandSpec.actionData)).toList
          let given := r.given + piece.length
          let ends := r.whole st.rules && given == r.out.size
          let c' := if piece.isEmpty then { c with idle := 0 }
            else { c with out := piece, idle := now + inactivity,
                          current := if r.view.isNone && r.given = 0 && r.number != 0 then r.number
                            else c.current }
          match (if ends then r.view else none).bind fun v => v.rest.head?.map fun x => (x, v) with
          | some ((n, cm), v) =>
            (c', some (st.setRead k (some (r.advance st.rules st.cfg.identity n cm
              { v with rest := v.rest.tail, first := false }))), false)
          | none =>
            if piece.isEmpty then (c', some st, false)
            else
              let r' := { r with given, owner := if ends then none else r.owner }
              (if ends then { c' with read := none, want := none, view := none } else c',
               some (st.setRead k (some r')).tidy, false)
      | none => ({ c with read := none, want := none, view := none }, some st, false)
  | _, st => (c, st, false)

/-- A connection with a reply going out a part at a time and nothing untaken: its next part put to
send, the inactivity deadline started again. -/
def progressList (now wall : Nat) (st : Option Store) (c : Conn) : Conn :=
  match c.listing with
  | some l =>
    if !c.out.isEmpty || c.phase = .quitting then c
    else
      let (part, rest) := l.part (Posting.of wall st) (chunk + 1) []
      { c with out := part, listing := rest, idle := now + inactivity }
  | none => c

/-- An ARTICLE, HEAD or BODY that waits gets a free read, when fewer came before it than reads are
free. -/
def claimRead (idx : Nat) (st : Option Store) (c : Conn) : Conn × Option Store :=
  match st, c.want with
  | some st, some (k, n, id) =>
    if c.read.isNone && c.out.isEmpty && c.phase = .open_ && st.admitsRead (idx, c.gen) then
      match (List.range st.rules.reads).find? st.readFree, st.find id with
      | some j, some cm =>
        let st' := { st with readers := st.readers.erase (idx, c.gen) }
        let r := Read.make st.rules st.cfg.identity (idx, c.gen) k n cm c.view
        ({ c with read := some j }, some (st'.setRead j (some r)))
      | _, _ => (c, some st)
    else (c, some st)
  | st, _ => (c, st)

/-- What a connection that is not closed at a deadline asks of the host once it is served: its
output, with whether to read once it is taken, unless the host has not yet reported it ready
after leaving part of it; or a graceful close once everything is answered and taken after a QUIT, a
502 or the end of input; or, with nothing to send, whether to read, when that has changed. -/
def emit (idx : Nat) (wants : Bool) (c : Conn) : Option Conn × Option Action :=
  if !c.out.isEmpty then
    if c.blocked then (some c, none)
    else (some { c with reading := wants }, some (.send idx c.gen c.out wants))
  else if c.phase = .quitting || (c.phase = .ending && c.held.isEmpty) then
    (none, some (.closeGracefully idx c.gen))
  else if c.phase = .open_ && c.reading != wants then
    (some { c with reading := wants }, some (.send idx c.gen [] wants))
  else (some c, none)

/-- The action for one connection after the batch's events and completions: at most one; and the
store as it leaves it. -/
def act (i : Identity) (now wall idx : Nat) (st : Option Store) (c : Conn) :
    Option Conn × Option Action × Option Store :=
  if c.due now then (none, some (.closeNow idx c.gen), st.map (Store.abandon idx c.gen))
  else
    let g := progress i now wall st c
    if g.2.2 then (none, some (.closeNow idx c.gen), g.2.1)
    else
      let h := progressRead i now g.2.1 g.1
      if h.2.2 then (none, some (.closeNow idx c.gen), h.2.1.map (Store.abandon idx c.gen))
      else
        let l := progressList now wall h.2.1 h.1
        let c1 := if l.out.isEmpty && l.phase != .quitting && l.post.isNone && !l.waiting &&
            l.want.isNone && l.listing.isNone
          then serve i (Posting.of wall h.2.1) now (l.held.length + 1) l else l
        let st1 := if c1.waiting && !h.1.waiting then
            h.2.1.map fun st => { st with waiters := st.waiters ++ [(idx, c.gen)] }
          else if c1.want.isSome && h.1.want.isNone then
            h.2.1.map fun st => { st with readers := st.readers ++ [(idx, c.gen)] }
          else h.2.1
        let k := claim i now idx st1 c1
        let k := claimRead idx k.2 k.1
        let r := emit idx (k.1.wantsWith k.2) k.1
        (r.1.map (Conn.waitLine now), r.2, k.2)

/-- The connections at the indexes `l` acting in turn, the store passed from one to the next. -/
def actFrom (i : Identity) (now wall : Nat) (t : Table) :
    List Nat → Option Store → List (Option Conn × Option Action) × Option Store
  | [], st => ([], st)
  | idx :: rest, st =>
    match t[idx]? with
    | some (some c) =>
      let x := act i now wall idx st c
      let r := actFrom i now wall t rest x.2.2
      ((x.1, x.2.1) :: r.1, r.2)
    | _ =>
      let r := actFrom i now wall t rest st
      ((none, none) :: r.1, r.2)

/-- The store's completions, or a breach for one with no store. -/
def completions (s : Server) (dones : List Done) : Except Breach (Option Store) :=
  match s.store with
  | some st => (some <$> st.completeAll dones).mapError Breach.job
  | none => if dones.isEmpty then pure none else throw (.job .unknownJob)

/-- The slots' jobs, if there is a store. -/
def jobsOf : Option Store → Option Store × List Job
  | some st => (some st.planAll.1, st.planAll.2)
  | none => (none, [])

/-- **A turn**: the batch's events in order, then the completions, then each connection's action,
by index, then the slots' jobs. -/
def turn (i : Identity) (s : Server) (now wall : Nat) (events : List Event) (dones : List Done) :
    Except Breach (Server × List Action × List Job) := do
  if batch < events.length then throw .tooManyEvents
  if now < s.clock || clockLimit ≤ now || wallLimit ≤ wall then throw .badClock
  let s ← events.foldlM (applyEvent i now) s
  let st ← completions s dones
  let r := actFrom i now wall s.table (List.range conns) st
  let j := jobsOf r.2
  return ({ s with table := r.1.map (·.1), clock := now, store := j.1 }, r.1.filterMap (·.2), j.2)

/-- What the host took of each send, in the order of the sends: taken output leaves `out`, output
taken counts as activity but in a POST, and a send not taken whole waits for the host to report
the connection ready. -/
def settleTable (now : Nat) (t : Table) : List Action → List Nat → Except Breach Table
  | [], [] => pure t
  | .send idx gen data _ :: rest, n :: ns => do
    if data.length < n then throw .overTaken
    let t := match t.live idx gen with
      | some c =>
        let idle := if c.read.isSome && c.out.length ≤ n then 0
          else if n = 0 || c.post.isSome || c.waiting then c.idle else now + inactivity
        t.set idx (some (Conn.waitLine now
          { c with out := c.out.drop n, idle := idle, blocked := decide (n < data.length) }))
      | none => t
    settleTable now t rest ns
  | .send .. :: _, [] => throw .overTaken
  | _ :: rest, ns => settleTable now t rest ns
  | [], _ :: _ => throw .overTaken

def settle (s : Server) (actions : List Action) (taken : List Nat) : Except Breach Server := do
  return { s with table := ← settleTable s.clock s.table actions taken }

/-- Whether the connection at `idx` can go on without waiting for the host: nothing of its output is
untaken, and it holds input to answer or to frame, has to close, waits for a slot it gets now or
for its 403, waits for a read it gets now, is answered by a read that has octets to give or
failed, or has a reply going out a part at a time. -/
def Conn.ready (st : Option Store) (idx : Nat) (c : Conn) : Bool :=
  c.out.isEmpty && (c.phase != .open_ || c.listing.isSome ||
    (c.waiting && st.any fun st => !st.accepting || st.admits (idx, c.gen)) ||
    (c.want.isSome && st.any fun st => match c.read with
      | none => st.admitsRead (idx, c.gen)
      | some k => (st.readSlot k).any fun r => r.bad || r.given < r.out.size) ||
    (!c.held.isEmpty && !c.waiting && c.want.isNone && match c.post with
      | none => true
      | some k => st.any fun st => (st.slot k).any Slot.takes))

/-- The earlier of two deadlines, zero standing for none. -/
def soonest (a b : Nat) : Nat := if a = 0 then b else if b = 0 then a else min a b

/-- The earliest of a connection's running deadlines, zero when none runs. -/
def Conn.earliest (c : Conn) : Nat :=
  soonest (soonest (soonest c.first c.idle) c.lineDue) c.articleDue

/-- **When the program needs its next turn**: now if a connection can go on, else the earliest
deadline; zero when there is none. -/
def deadline (s : Server) : Nat :=
  let live := s.table.filterMap id
  if s.table.zipIdx.any (fun (x, idx) => x.any (Conn.ready s.store idx)) then max s.clock 1
  else live.foldl (fun d c => soonest d c.earliest) 0

/-! ## What the session guarantees by construction -/

/-- A store whose articles have article numbers and message-ids, and no more of them than an article
number counts; whose groups' names are no longer than a group's may be; and a wall clock below the
host's limit. -/
def Posting.Fits (p : Posting) : Prop :=
  p.held.length ≤ numberMax ∧ (∀ c ∈ p.held, c.messageId.length ≤ 250 ∧ ∀ x ∈ c.groups, x.number ≤ numberMax) ∧
    (∀ g ∈ p.groups, g.length ≤ groupNameMax) ∧ p.wall < wallLimit

theorem numbered_bounded {p : Posting} (hp : p.Fits) (g : List Byte) :
    ∀ x ∈ numbered p.held g, x.1 ≤ numberMax ∧ x.2.length ≤ 250 := by
  intro x hx
  simp only [numbered, List.mem_filterMap, Option.map_eq_some_iff] at hx
  obtain ⟨c, hc, y, hy, rfl⟩ := hx
  exact ⟨(hp.2.1 c hc).2 y (List.mem_of_find?_eq_some hy), (hp.2.1 c hc).1⟩

/-- A fold that keeps what it has or takes the element in hand ends with what it began with or an
element. -/
theorem foldl_pick {α : Type} (f : Option α → α → Option α) (hf : ∀ b x, f b x = b ∨ f b x = some x) :
    ∀ (l : List α) (b : Option α) (y : α), l.foldl f b = some y → b = some y ∨ y ∈ l
  | [], _, _, h => .inl h
  | x :: rest, b, y, h => by
    rcases foldl_pick f hf rest (f b x) y h with h1 | h1
    · rcases hf b x with h2 | h2
      · exact .inl (h2 ▸ h1)
      · rw [h2] at h1; cases h1; exact .inr (List.mem_cons_self ..)
    · exact .inr (List.mem_cons_of_mem _ h1)

theorem pick_mem {held : List Journal.Commit} {g : List Byte} {n : Nat} {x : Nat × List Byte}
    (h : atNumber held g n = some x ∨ nextAfter held g n = some x ∨ prevBefore held g n = some x) :
    x ∈ numbered held g := by
  rcases h with h | h | h
  · exact List.mem_of_find?_eq_some h
  · rcases foldl_pick _ (fun _ _ => by split <;> simp) _ none x h with h1 | h1
    · cases h1
    · exact h1
  · rcases foldl_pick _ (fun _ _ => by split <;> simp) _ none x h with h1 | h1
    · cases h1
    · exact h1

theorem foldl_min_le (x : Nat) : ∀ l : List Nat, l.foldl min x ≤ x
  | [] => Nat.le_refl _
  | y :: rest => Nat.le_trans (foldl_min_le (min x y) rest) (Nat.min_le_left _ _)

theorem foldl_max_le (m : Nat) : ∀ (l : List Nat) (x : Nat), x ≤ m → (∀ y ∈ l, y ≤ m) → l.foldl max x ≤ m
  | [], _, hx, _ => hx
  | y :: rest, x, hx, hl =>
    foldl_max_le m rest (max x y) (Nat.max_le.mpr ⟨hx, hl y (List.mem_cons_self ..)⟩)
      fun z hz => hl z (List.mem_cons_of_mem _ hz)

theorem summary_selected (held : List Journal.Commit) (g : List Byte) :
    ∃ count low high, summary held g = .selected count low high g := by
  unfold summary
  split
  · exact ⟨_, _, _, rfl⟩
  · exact ⟨_, _, _, rfl⟩

theorem summary_bounded {p : Posting} (hp : p.Fits) (g : List Byte) (hg : g.length ≤ groupNameMax) :
    (summary p.held g).bounded = true := by
  have hb := numbered_bounded hp g
  have hlen : ((numbered p.held g).map (·.1)).length ≤ numberMax :=
    Nat.le_trans (by simp only [List.length_map, numbered]; exact List.length_filterMap_le _ _) hp.1
  unfold summary
  split
  · simp [Reply.bounded, numberMax, hg]
  · rename_i x rest he
    have hall : ∀ y ∈ x :: rest, y ≤ numberMax := by
      intro y hy
      rw [← he] at hy
      obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hy
      exact (hb z hz).1
    have hx := hall x (List.mem_cons_self ..)
    rw [he] at hlen
    simp only [List.length_cons] at hlen
    simp only [Reply.bounded, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨⟨⟨hlen, Nat.le_trans (foldl_min_le x rest) hx⟩,
      foldl_max_le _ rest x hx fun y hy => hall y (List.mem_cons_of_mem _ hy)⟩, hg⟩

theorem foundAs_bounded {p : Posting} (hp : p.Fits) {g : List Byte} (k : Cmd) {x : Nat × List Byte}
    (hx : x ∈ numbered p.held g) : (foundAs k x).bounded = true := by
  obtain ⟨n, id⟩ := x
  obtain ⟨h1, h2⟩ := numbered_bounded hp g _ hx
  by_cases hk : k = .stat <;> simp_all [foundAs, Reply.bounded]

theorem padded_length (k n : Nat) (hk : k ≤ 10) (hn : n < 10 ^ 10) : (padded k n).length ≤ 10 := by
  have := decimal_length n hn
  simp only [padded, List.length_append, List.length_replicate]
  omega

theorem civil_small (z : Nat) (h : z < 2 ^ 30) :
    (ArticleSpec.civilFromDays z).1 < 10 ^ 10 ∧ (ArticleSpec.civilFromDays z).2.1 < 10 ^ 10 ∧
      (ArticleSpec.civilFromDays z).2.2 < 10 ^ 10 := by
  simp only [ArticleSpec.civilFromDays]
  split <;> split <;> omega

/-- DATE's digits, of a wall clock below the host's limit, are at most sixty. -/
theorem dateDigits_length (wall : Nat) (h : wall < wallLimit) : (dateDigits wall).length ≤ 60 := by
  have hz : wall / 1000 / 86400 < 2 ^ 30 := by simp only [wallLimit] at h; omega
  obtain ⟨h1, h2, h3⟩ := civil_small _ hz
  have t1 : wall / 1000 % 86400 / 3600 < 10 ^ 10 := by omega
  have t2 : wall / 1000 % 86400 % 3600 / 60 < 10 ^ 10 := by omega
  have t3 : wall / 1000 % 86400 % 60 < 10 ^ 10 := by omega
  simp only [dateDigits, List.length_append]
  have := padded_length 4 _ (by decide) h1
  have := padded_length 2 _ (by decide) h2
  have := padded_length 2 _ (by decide) h3
  have := padded_length 2 _ (by decide) t1
  have := padded_length 2 _ (by decide) t2
  have := padded_length 2 _ (by decide) t3
  omega

/-- RFC 3977 §7.1.3's example, the epoch, a leap day, and the last wall clock the host may give. -/
theorem date_examples :
    dateDigits 930146184000 = ascii "19990623135624" ∧ dateDigits 999 = ascii "19700101000000" ∧
    dateDigits 951782400000 = ascii "20000229000000" ∧ dateDigits (wallLimit - 1) = ascii "368120220003615" := by
  decide +kernel

/-- A store of two groups, the first holding articles 3 and 5, the second article 1. -/
def listedPosting : Posting :=
  ⟨true, true, [ascii "a.b", ascii "c"],
    [⟨1, ascii "<1@x>", [⟨ascii "a.b", 3⟩], 1, 1, 0⟩, ⟨2, ascii "<2@x>", [⟨ascii "a.b", 5⟩, ⟨ascii "c", 1⟩], 1, 1, 0⟩], 0⟩

/-- A group of articles 1 to 200. -/
def longPosting : Posting :=
  ⟨true, false, [ascii "g"], (List.range 200).map fun k => ⟨k + 1, ascii "<x>", [⟨ascii "g", k + 1⟩], 1, 1, 0⟩, 0⟩

/-- Listings in parts: the numbers in a range, the groups a wildmat matches, and a part that ends as
an action is full, the next with the terminating line. -/
theorem listing_examples :
    (Listing.numbers (ascii "a.b") 1 numberMax).part listedPosting (chunk + 1) [] = (ascii "3\r\n5\r\n.\r\n", none) ∧
    (Listing.numbers (ascii "a.b") 4 5).part listedPosting (chunk + 1) [] = (ascii "5\r\n.\r\n", none) ∧
    (Listing.numbers (ascii "a.b") 1 4).part listedPosting (chunk + 1) [] = (ascii "3\r\n.\r\n", none) ∧
    (Listing.groups none 0).part listedPosting (chunk + 1) [] = (ascii "a.b 5 3 y\r\nc 1 1 y\r\n.\r\n", none) ∧
    (Listing.groups (some (wm "c*,x")) 0).part listedPosting (chunk + 1) [] = (ascii "c 1 1 y\r\n.\r\n", none) ∧
    (Listing.groups (some (wm "x")) 0).part listedPosting (chunk + 1) [] = (ascii ".\r\n", none) ∧
    (Listing.groups none 0).part longPosting (chunk + 1) [] = (ascii "g 200 1 n\r\n.\r\n", none) ∧
    ((Listing.numbers (ascii "g") 1 numberMax).part longPosting (chunk + 1) []).1.length = 512 ∧
    ((Listing.numbers (ascii "g") 1 numberMax).part longPosting (chunk + 1) []).2 =
      some (.numbers (ascii "g") 125 numberMax) ∧
    (Listing.numbers (ascii "g") 125 numberMax).part longPosting (chunk + 1) [] =
      (((List.range 76).map fun k => decimal (k + 125) ++ crlf).flatten ++ ascii ".\r\n", none) := by
  decide +kernel

/-- The articles an OVER or HDR names are ones a store may hold, with article numbers. -/
theorem viewOf_bounded (p : Posting) (hp : p.Fits) (c : Conn) (lg : Bool) (f : Option (List Byte))
    (s : Sel) (hs : ∀ mid, s = .id mid → mid.length ≤ 250) : (viewOf p c lg f s).bounded = true := by
  cases s with
  | id mid =>
    simp only [viewOf]
    split
    · simp [Reply.bounded, numberMax, hs mid rfl]
    · rfl
  | range lo hi =>
    simp only [viewOf]
    split
    · rfl
    · rename_i g _
      generalize hl : ((numbered p.held g).filter fun x => lo ≤ x.1 && x.1 ≤ hi).mergeSort
        (fun a b => a.1 ≤ b.1) = items
      have hm : ∀ x ∈ items, x ∈ numbered p.held g := fun x hx => by
        rw [← hl] at hx
        exact (List.mem_filter.mp ((List.mergeSort_perm _ _).mem_iff.mp hx)).1
      cases items with
      | nil => simp only; split <;> (try split) <;> rfl
      | cons y rest =>
        simp only [Reply.bounded, List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq]
        intro x hx
        exact numbered_bounded hp g x (hm x hx)
  | current =>
    simp only [viewOf]
    split
    · rfl
    · rename_i g _
      split
      · rfl
      · cases ha : atNumber p.held g c.current with
        | none => rfl
        | some x =>
          obtain ⟨h1, h2⟩ := numbered_bounded hp g x (pick_mem (.inl ha))
          simp [Reply.bounded, h1, h2]

/-- A store's answer keeps a reply's message-id one a store may hold, and its numbers article
numbers. -/
theorem resolve_bounded (p : Posting) (hp : p.Fits) (c : Conn) (r : Reply) (h : r.bounded = true) :
    (resolve p c r).bounded = true := by
  cases r
  case select g =>
    simp only [resolve]
    split
    · exact summary_bounded hp g (by simpa [Reply.bounded] using h)
    · rfl
  case byNumber k n =>
    simp only [resolve]
    split
    · rfl
    · rename_i g _
      cases ha : atNumber p.held g n with
      | none => rfl
      | some x => exact foundAs_bounded hp k (pick_mem (.inl ha))
  case current k =>
    simp only [resolve]
    split
    · rfl
    · rename_i g _
      split
      · rfl
      · cases ha : atNumber p.held g c.current with
        | none => rfl
        | some x => exact foundAs_bounded hp k (pick_mem (.inl ha))
  case move fwd =>
    simp only [resolve]
    split
    · rfl
    · rename_i g _
      split
      · rfl
      · have key : ∀ o : Option (Nat × List Byte), (∀ x, o = some x → x ∈ numbered p.held g) →
            ∀ d : Reply, d.bounded = true → ((o.map fun x => Reply.stat x.1 x.2).getD d).bounded = true := by
          intro o ho d hd
          cases o with
          | none => exact hd
          | some x =>
            obtain ⟨h1, h2⟩ := numbered_bounded hp g x (ho x rfl)
            simp [Reply.bounded, h1, h2]
        apply key
        · intro x hx
          cases fwd
          · exact pick_mem (.inr (.inr (by simpa using hx)))
          · exact pick_mem (.inr (.inl (by simpa using hx)))
        · cases fwd <;> rfl
  case listGroup g lo hi =>
    simp only [resolve]
    split
    · rfl
    · rename_i g' _
      split
      · rename_i hc
        have hg := hp.2.2.1 g' (List.contains_iff_mem.mp hc)
        have hs := summary_bounded hp g' hg
        split
        · rename_i e; rw [e] at hs; simpa [Reply.bounded] using hs
        · exact hs
      · rfl
  case date =>
    simp only [resolve, Reply.bounded, decide_eq_true_eq]
    exact Nat.le_trans (dateDigits_length _ hp.2.2.2) (by decide)
  case over lg s =>
    exact viewOf_bounded p hp c lg none s fun mid e => by subst e; simpa [Reply.bounded] using h
  case hdr lg f s =>
    exact viewOf_bounded p hp c lg (some f) s fun mid e => by subst e; simpa [Reply.bounded] using h
  case overview => simpa only [resolve] using h
  all_goals simp only [resolve] <;> (repeat' split) <;> simp_all [Reply.bounded]

/-! ## A listing's parts -/

/-- What is left of a listing: of numbers, how many from where it is to its end; of groups, how many
the store carries from where it is. -/
def Listing.left (p : Posting) : Listing → Nat
  | .numbers _ from_ upto => upto + 1 - from_
  | .groups _ next => p.groups.length - next

theorem partWith_length (next : Listing → Option (List Byte × Listing)) (most : Nat) :
    ∀ fuel (acc : List Byte) (l : Listing), acc.length ≤ most → (partWith next most fuel acc l).1.length ≤ most := by
  intro fuel
  induction fuel with
  | zero => intro acc l h; exact h
  | succ fuel ih =>
    intro acc l h
    unfold partWith
    split
    · split
      · rename_i hl; exact ih _ _ (by simpa using hl)
      · exact h
    · split
      · rename_i hl
        have : (ascii ".\r\n").length = 3 := by decide
        simp only [List.length_append]; omega
      · exact h

theorem partWith_prefix (next : Listing → Option (List Byte × Listing)) (most : Nat) :
    ∀ fuel (acc : List Byte) (l : Listing), acc <+: (partWith next most fuel acc l).1 := by
  intro fuel
  induction fuel with
  | zero => intro acc l; exact List.prefix_refl _
  | succ fuel ih =>
    intro acc l
    unfold partWith
    split
    · split
      · exact (List.prefix_append _ _).trans (ih _ _)
      · exact List.prefix_refl _
    · split
      · exact List.prefix_append _ _
      · exact List.prefix_refl _

/-- **Each line a listing gives leaves less of it.** -/
theorem next_left (p : Posting) (l l' : Listing) (line : List Byte) (h : l.next p = some (line, l')) :
    l'.left p < l.left p := by
  cases l with
  | numbers g from_ upto =>
    simp only [Listing.next, nextWith] at h
    split at h
    · rename_i n hn
      cases h
      have hm := List.min?_mem hn
      simp only [List.mem_filter, Bool.and_eq_true, decide_eq_true_eq] at hm
      simp only [Listing.left]
      omega
    · cases h
  | groups w next =>
    simp only [Listing.next, nextWith] at h
    split at h
    · rename_i g k hk
      cases h
      have hm := List.mem_zipIdx (List.mem_of_find?_eq_some hk)
      simp only [List.length_drop] at hm
      simp only [Listing.left]
      omega
    · cases h

theorem all_mono {α : Type} {o : Option α} {P Q : α → Bool} (h : o.all P = true)
    (hq : ∀ x, P x = true → Q x = true) : o.all Q = true := by
  cases o with
  | none => rfl
  | some x => simpa using hq x (by simpa using h)

theorem partWith_left (p : Posting) (most : Nat) :
    ∀ fuel (acc : List Byte) (l : Listing),
      (partWith (Listing.next p) most fuel acc l).2.all (·.left p ≤ l.left p) := by
  intro fuel
  induction fuel with
  | zero => intro acc l; simp [partWith]
  | succ fuel ih =>
    intro acc l
    unfold partWith
    split
    · rename_i line l' h
      split
      · have hd := next_left p l l' line h
        exact all_mono (ih _ _) fun x hx => by simp only [decide_eq_true_eq] at hx ⊢; omega
      · simp
    · split <;> simp

/-- A line of a listing, of a store that fits, is not empty and fits one action. -/
theorem next_fits (p : Posting) (hp : p.Fits) (l l' : Listing) (line : List Byte) (h : l.next p = some (line, l')) :
    line ≠ [] ∧ line.length ≤ chunk := by
  cases l with
  | numbers g from_ upto =>
    simp only [Listing.next, nextWith] at h
    split at h
    · rename_i n hn
      cases h
      have hm := List.min?_mem hn
      simp only [List.mem_filter, List.mem_map] at hm
      obtain ⟨⟨x, hx, rfl⟩, _⟩ := hm
      have := decimal_length x.1 (by have := (numbered_bounded hp g x hx).1; simp only [numberMax] at this; omega)
      simp only [crlf, ne_eq, List.append_eq_nil_iff, reduceCtorEq, and_false, not_false_eq_true,
        List.length_append, List.length_cons, List.length_nil, chunk, true_and]
      omega
    · cases h
  | groups w next =>
    simp only [Listing.next, nextWith] at h
    split at h
    · rename_i g k hk
      cases h
      have hm := (List.mem_zipIdx (List.mem_of_find?_eq_some hk)).2.2
      have hg : g ∈ p.groups := by
        rw [hm]; exact List.mem_of_mem_drop (List.getElem_mem _)
      have hl := hp.2.2.1 g hg
      have hs := summary_bounded hp g hl
      unfold activeLine
      split
      · rename_i cnt low high g' e
        rw [e] at hs
        simp only [Reply.bounded, Bool.and_eq_true, decide_eq_true_eq] at hs
        have := decimal_length low (by simp only [numberMax] at hs; omega)
        have := decimal_length high (by simp only [numberMax] at hs; omega)
        have : (ascii (if p.accepting then "y" else "n")).length = 1 := by split <;> decide
        simp only [groupNameMax] at hl
        have hlen : (g ++ SP :: decimal high ++ SP :: decimal low ++ SP ::
            ascii (if p.accepting then "y" else "n") ++ crlf).length =
            g.length + (decimal high).length + (decimal low).length +
              (ascii (if p.accepting then "y" else "n")).length + 5 := by
          simp only [crlf, List.length_append, List.length_cons, List.length_nil]; omega
        exact ⟨List.ne_nil_of_length_pos (by omega), by rw [hlen]; simp only [chunk]; omega⟩
      · rename_i e
        obtain ⟨c, lo, hi, hs'⟩ := summary_selected p.held g
        exact absurd hs' (e c lo hi g)
    · cases h

/-- **A listing's part fits one action, and either ends the listing or leaves less of it**, of a
store that fits; it is never empty. -/
theorem part_progress (p : Posting) (hp : p.Fits) (l : Listing) :
    (l.part p (chunk + 1) []).1.length ≤ chunk ∧ (l.part p (chunk + 1) []).1 ≠ [] ∧
      (l.part p (chunk + 1) []).2.all (·.left p < l.left p) := by
  refine ⟨partWith_length _ _ _ _ _ (Nat.zero_le _), ?_⟩
  simp only [Listing.part, partWith]
  split
  · rename_i line l' h
    obtain ⟨hne, hlen⟩ := next_fits p hp l l' line h
    simp only [List.length_nil, Nat.zero_add, hlen, ↓reduceIte, List.nil_append]
    refine ⟨fun e => hne (List.prefix_nil.mp (e ▸ partWith_prefix _ _ _ _ _)), ?_⟩
    have hd := next_left p l l' line h
    exact all_mono (partWith_left p chunk chunk line l') fun x hx => by
      simp only [decide_eq_true_eq] at hx ⊢; omega
  · have : ([] : List Byte).length + 3 ≤ chunk := by decide
    simp only [this, ↓reduceIte]
    exact ⟨by decide, rfl⟩

/-- **Every reply a connection gets fits one action**, with a store whose articles have article
numbers and message-ids, or without one. -/
theorem reply_fits (i : Identity) (hi : i.ok = true) (p : Posting) (hp : p.Fits) (c : Conn) (l : Line) :
    (text i (resolve p c (replyIn p.offered l))).length ≤ CommandSpec.actionData :=
  text_fits i hi _ (resolve_bounded p hp c _ (replyIn_bounded _ l))

/-- The premise holds without a store, and of a store holding an article. -/
theorem fits_witness : (Posting.of 0 none).Fits ∧
    (⟨true, true, [ascii "local.test"],
      [⟨1, ascii "<a@b>", [⟨ascii "local.test", 1⟩], 19, 24, 0⟩], 1790000000000⟩ : Posting).Fits :=
  ⟨by unfold Posting.Fits Posting.of; decide +kernel, by unfold Posting.Fits; decide +kernel⟩

def Action.idx : Action → Nat
  | .send idx .. | .closeGracefully idx _ | .closeNow idx _ => idx

theorem emit_idx (idx : Nat) (w : Bool) (c : Conn) (a : Action) (h : (emit idx w c).2 = some a) :
    a.idx = idx := by
  revert h
  unfold emit
  split
  · split
    · intro h; cases h
    · intro h; cases h; rfl
  · split
    · intro h; cases h; rfl
    · split
      · intro h; cases h; rfl
      · intro h; cases h

theorem act_idx (i : Identity) (now wall idx : Nat) (st : Option Store) (c : Conn) (a : Action)
    (h : (act i now wall idx st c).2.1 = some a) : a.idx = idx := by
  revert h
  unfold act
  split
  · intro h; cases h; rfl
  · dsimp only
    split
    · intro h; cases h; rfl
    · split
      · intro h; cases h; rfl
      · exact emit_idx idx _ _ a

theorem actFrom_ordered (i : Identity) (now wall : Nat) (t : Table) :
    ∀ (l : List Nat) (st : Option Store), l.Pairwise (· < ·) →
      (((actFrom i now wall t l st).1.filterMap (·.2)).map Action.idx).Pairwise (· < ·) ∧
        ∀ a ∈ (actFrom i now wall t l st).1.filterMap (·.2), a.idx ∈ l
  | [], _, _ => by simp [actFrom]
  | idx :: rest, st, hl => by
    obtain ⟨hlt, hr⟩ := List.pairwise_cons.mp hl
    unfold actFrom
    split
    · rename_i c _
      obtain ⟨ih1, ih2⟩ :=
        actFrom_ordered i now wall t rest (act i now wall idx st c).2.2 hr
      cases ha : (act i now wall idx st c).2.1 with
      | none =>
        simp only [ha, List.filterMap_cons]
        exact ⟨ih1, fun a h => List.mem_cons_of_mem _ (ih2 a h)⟩
      | some a0 =>
        have h0 := act_idx i now wall idx st c a0 ha
        simp only [ha, List.filterMap_cons, List.map_cons, List.pairwise_cons, List.mem_map,
          List.mem_cons, forall_eq_or_imp]
        refine ⟨⟨?_, ih1⟩, by simp [h0], fun a h => .inr (ih2 a h)⟩
        rintro _ ⟨b, hb, rfl⟩
        rw [h0]
        exact hlt _ (ih2 b hb)
    · obtain ⟨ih1, ih2⟩ := actFrom_ordered i now wall t rest st hr
      simp only [List.filterMap_cons]
      exact ⟨ih1, fun a h => List.mem_cons_of_mem _ (ih2 a h)⟩

/-- **At most one action a connection in a turn**, in the order of the indexes. -/
theorem turn_ordered (i : Identity) (s s' : Server) (now wall : Nat) (evs : List Event)
    (ds : List Done) (acts : List Action) (js : List Job)
    (h : turn i s now wall evs ds = .ok (s', acts, js)) :
    (acts.map Action.idx).Pairwise (· < ·) := by
  unfold turn at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  split at h
  · cases h
  · split at h
    · cases h
    · split at h
      · cases h
      · split at h
        · cases h
        · simp only [Except.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨-, rfl, -⟩ := h
          exact (actFrom_ordered i now wall _ _ _ List.pairwise_lt_range).1

theorem isEmpty_false {α : Type} {l : List α} (h : l ≠ []) : l.isEmpty = false := by
  cases l <;> simp_all

theorem progress_busy (i : Identity) (now wall : Nat) (st : Option Store) (c : Conn)
    (h : c.out ≠ [] ∨ c.phase = .quitting) : progress i now wall st c = (c, st, false) := by
  unfold progress
  split
  · rcases h with h | h
    · simp [isEmpty_false h]
    · simp [h]
  · rfl

theorem claim_busy (i : Identity) (now idx : Nat) (st : Option Store) (c : Conn)
    (h : c.out ≠ [] ∨ c.phase = .quitting) : claim i now idx st c = (c, st) := by
  unfold claim
  split
  · rcases h with h | h
    · simp [isEmpty_false h]
    · simp [h]
  · rfl

theorem progressRead_busy (i : Identity) (now : Nat) (st : Option Store) (c : Conn)
    (h : c.out ≠ [] ∨ c.phase = .quitting) : progressRead i now st c = (c, st, false) := by
  unfold progressRead
  split
  · rcases h with h | h
    · simp [isEmpty_false h]
    · simp [h]
  · rfl

theorem claimRead_busy (idx : Nat) (st : Option Store) (c : Conn)
    (h : c.out ≠ [] ∨ c.phase = .quitting) : claimRead idx st c = (c, st) := by
  unfold claimRead
  split
  · rcases h with h | h
    · simp [isEmpty_false h]
    · simp [h]
  · rfl

theorem progressList_busy (now wall : Nat) (st : Option Store) (c : Conn)
    (h : c.out ≠ [] ∨ c.phase = .quitting) : progressList now wall st c = c := by
  unfold progressList
  split
  · rcases h with h | h
    · simp [isEmpty_false h]
    · simp [h]
  · rfl

theorem want_both (c : Conn) : (c.want.isSome && c.want.isNone) = false := by
  cases c.want <;> rfl

/-- **Output untaken is sent again once the host has reported the connection ready, and nothing
else is**: no line is answered before what came before it is taken. -/
theorem act_resends (i : Identity) (now wall idx : Nat) (st : Option Store) (c : Conn)
    (hd : c.due now = false) (h : c.out ≠ []) (hb : c.blocked = false) :
    (act i now wall idx st c).2.1 = some (.send idx c.gen c.out (c.wantsWith st)) := by
  simp [act, hd, progress_busy i now wall st c (.inl h), progressRead_busy i now st c (.inl h),
    progressList_busy now wall st c (.inl h), claim_busy i now idx st c (.inl h),
    claimRead_busy idx st c (.inl h), emit, isEmpty_false h, hb, want_both]

/-- …and nothing is sent to a connection the host has not reported ready. -/
theorem act_blocked (i : Identity) (now wall idx : Nat) (st : Option Store) (c : Conn)
    (hd : c.due now = false) (h : c.out ≠ []) (hb : c.blocked = true) :
    (act i now wall idx st c).2.1 = none := by
  simp [act, hd, progress_busy i now wall st c (.inl h), progressRead_busy i now st c (.inl h),
    progressList_busy now wall st c (.inl h), claim_busy i now idx st c (.inl h),
    claimRead_busy idx st c (.inl h), emit, isEmpty_false h, hb, want_both]

/-- Every reply but `ignore` has bytes. -/
theorem text_ne_nil (i : Identity) : ∀ r, r ≠ .ignore → text i r ≠ []
  | .ignore, h => absurd rfl h
  | .capabilities, _ => fun e =>
    absurd (List.append_eq_nil_iff.mp (List.append_eq_nil_iff.mp e).1).1 (by decide +kernel)
  | .capabilitiesPost, _ | .capabilitiesReader, _ => fun e => by
    simp only [text, List.append_assoc, List.append_eq_nil_iff] at e
    exact absurd e.1 (by decide +kernel)
  | .help, _ | .helpPost, _ => fun e =>
    absurd (List.append_eq_nil_iff.mp (List.append_eq_nil_iff.mp (List.append_eq_nil_iff.mp
      (List.append_eq_nil_iff.mp e).1).1).1).1 (by decide +kernel)
  | .stat _ _, _ => fun e =>
    absurd (List.append_eq_nil_iff.mp (List.append_eq_nil_iff.mp (List.append_eq_nil_iff.mp e).1).1).1
      (by decide +kernel)
  | .selected .., _ | .listed .., _ | .time _, _ => fun e => by
    simp only [text, List.append_assoc, List.append_eq_nil_iff] at e
    exact absurd e.1 (by decide +kernel)
  | .quit, _ | .noGroup, _ | .noSuchId, _ | .unknown, _ | .syntax, _ | .post, _ | .posted, _
  | .failed, _ | .notPermitted, _ | .unavailable, _ | .lookup _ _ _, _ | .unreadable, _
  | .select _, _ | .byNumber _ _, _ | .current _, _ | .move _, _ | .noSuchGroup, _ | .noCurrent, _
  | .noNext, _ | .noPrevious, _ | .noNumber, _ | .listGroup .., _ | .active _, _ | .newsgroups, _
  | .newGroups, _ | .date, _ | .modeReader, _ | .readerPosting, _ | .readerNoPosting, _
  | .over .., _ | .hdr .., _ | .noneOver, _ | .noneHdr, _ | .noRange, _ | .fieldRefused, _
  | .overviewFmt, _ | .headerList, _ => by
    simp only [text]; decide +kernel
  | .overview lg f _ _, _ => by
    cases lg <;> cases f <;> (simp only [text, overviewStatus]; decide +kernel)

/-- `serve` leaves output that is already there as it is. -/
theorem serve_out (i : Identity) (p : Posting) (now : Nat) :
    ∀ fuel (c : Conn), c.out ≠ [] → (serve i p now fuel c).out = c.out := by
  intro fuel
  induction fuel with
  | zero => intro c _; rfl
  | succ fuel ih =>
    intro c h
    unfold serve
    split
    · rfl
    · simp only
      split
      · rfl
      · split
        · exact ih _ h
        · simp [isEmpty_false h]

/-- **One reply at a time**: from nothing to send, `serve` puts at most one reply in `out`. -/
theorem serve_one (i : Identity) (p : Posting) (now : Nat) :
    ∀ fuel (c : Conn), c.out = [] →
      (serve i p now fuel c).out = [] ∨
        ∃ r, r ≠ .ignore ∧ (serve i p now fuel c).out = text i r := by
  intro fuel
  induction fuel with
  | zero => intro c h; exact .inl h
  | succ fuel ih =>
    intro c h
    unfold serve
    split
    · exact .inl h
    · simp only
      split
      · exact .inl h
      · rename_i l _
        split
        · exact ih _ h
        · rename_i hr
          split
          · exact .inl h
          · split
            · exact .inl h
            · split
              · exact ih _ h
              · split
                · exact .inr ⟨_, hr, rfl⟩
                · rw [serve_out]
                  · exact .inr ⟨_, hr, rfl⟩
                  · exact text_ne_nil i _ hr

/-- `serve` leaves the line's deadline to `Conn.waitLine`. -/
theorem serve_lineDue (i : Identity) (p : Posting) (now : Nat) :
    ∀ fuel (c : Conn), (serve i p now fuel c).lineDue = c.lineDue := by
  intro fuel
  induction fuel with
  | zero => intro c; rfl
  | succ fuel ih =>
    intro c
    unfold serve
    split
    · rfl
    · simp only
      split
      · rfl
      · split
        · exact ih _
        · split
          · rfl
          · split
            · rfl
            · split
              · exact ih _
              · split
                · rfl
                · exact ih _

theorem emit_lineDue (idx : Nat) (w : Bool) (c c0 : Conn) (h : (emit idx w c).1 = some c0) :
    c0.lineDue = c.lineDue := by
  unfold emit at h
  repeat (first | split at h | (cases h; rfl) | cases h)

/-- `Conn.waitLine` changes nothing but the line's deadline. -/
theorem waitLine_same (now : Nat) (c : Conn) :
    (c.waitLine now).out = c.out ∧ (c.waitLine now).phase = c.phase ∧
      (c.waitLine now).line = c.line := by
  unfold Conn.waitLine
  split
  · split <;> exact ⟨rfl, rfl, rfl⟩
  · exact ⟨rfl, rfl, rfl⟩

/-- With output untaken, `serve` leaves the phase as it is. -/
theorem serve_phase (i : Identity) (p : Posting) (now : Nat) :
    ∀ fuel (c : Conn), c.out ≠ [] → (serve i p now fuel c).phase = c.phase := by
  intro fuel
  induction fuel with
  | zero => intro c _; rfl
  | succ fuel ih =>
    intro c h
    unfold serve
    split
    · rfl
    · simp only
      split
      · rfl
      · split
        · exact ih _ h
        · simp [isEmpty_false h]

/-- `progress` and `claim` leave a connection's phase, line and its deadline as they were. -/
theorem progress_keeps (i : Identity) (now wall : Nat) (st : Option Store) (c : Conn) :
    (progress i now wall st c).1.phase = c.phase ∧
      (progress i now wall st c).1.lineDue = c.lineDue := by
  unfold progress
  split
  · split
    · exact ⟨rfl, rfl⟩
    · dsimp only
      split
      · split
        · exact ⟨rfl, rfl⟩
        · rename_i o _ _
          have ho : text i (outcomeReply o) ≠ [] :=
            text_ne_nil i _ (by cases o <;> simp [outcomeReply])
          exact ⟨serve_phase _ _ _ _ _ ho, serve_lineDue ..⟩
        · exact ⟨rfl, rfl⟩
      · exact ⟨rfl, rfl⟩
  · exact ⟨rfl, rfl⟩

theorem claim_keeps (i : Identity) (now idx : Nat) (st : Option Store) (c : Conn) :
    (claim i now idx st c).1.phase = c.phase ∧ (claim i now idx st c).1.lineDue = c.lineDue := by
  unfold claim
  split
  · split
    · dsimp only
      split
      · exact ⟨rfl, rfl⟩
      · split
        · split
          · exact ⟨rfl, rfl⟩
          · exact ⟨rfl, rfl⟩
        · exact ⟨rfl, rfl⟩
    · exact ⟨rfl, rfl⟩
  · exact ⟨rfl, rfl⟩

theorem progressRead_keeps (i : Identity) (now : Nat) (st : Option Store) (c : Conn) :
    (progressRead i now st c).1.phase = c.phase ∧ (progressRead i now st c).1.lineDue = c.lineDue := by
  unfold progressRead
  repeat (first | split | exact ⟨rfl, rfl⟩ | dsimp only)

theorem progressList_keeps (now wall : Nat) (st : Option Store) (c : Conn) :
    (progressList now wall st c).phase = c.phase ∧ (progressList now wall st c).lineDue = c.lineDue := by
  unfold progressList
  repeat (first | split | exact ⟨rfl, rfl⟩ | dsimp only)

theorem claimRead_keeps (idx : Nat) (st : Option Store) (c : Conn) :
    (claimRead idx st c).1.phase = c.phase ∧ (claimRead idx st c).1.lineDue = c.lineDue := by
  unfold claimRead
  repeat (first | split | exact ⟨rfl, rfl⟩ | dsimp only)

/-- **Bytes do not move the line's deadline**: a connection still waiting for the rest of a line
after its turn keeps the deadline it had, whatever the turn read. -/
theorem act_keeps_line (i : Identity) (now wall idx : Nat) (st : Option Store) (c c' : Conn)
    (hd : c.due now = false) (hl : c.lineDue ≠ 0) (h : (act i now wall idx st c).1 = some c')
    (ho : c'.out = []) (hp : c'.phase = .open_) (hf : c'.line ≠ .fresh) (hw : c'.want = none)
    (hli : c'.listing = none) : c'.lineDue = c.lineDue := by
  simp only [act, hd, Bool.false_eq_true, ↓reduceIte] at h
  split at h
  · cases h
  · split at h
    · cases h
    simp only [Option.map_eq_some_iff] at h
    obtain ⟨c0, h0, rfl⟩ := h
    have e0 : c0.lineDue = c.lineDue := by
      rw [emit_lineDue idx _ _ c0 h0, (claimRead_keeps ..).2, (claim_keeps ..).2]
      split
      · rw [serve_lineDue, (progressList_keeps ..).2, (progressRead_keeps ..).2, (progress_keeps ..).2]
      · rw [(progressList_keeps ..).2, (progressRead_keeps ..).2, (progress_keeps ..).2]
    obtain ⟨so, sp, sl⟩ := waitLine_same now c0
    have sw : (c0.waitLine now).want = c0.want := by
      unfold Conn.waitLine; split <;> (try split) <;> rfl
    have sli : (c0.waitLine now).listing = c0.listing := by
      unfold Conn.waitLine; split <;> (try split) <;> rfl
    rw [so] at ho
    rw [sp] at hp
    rw [sl] at hf
    rw [sw] at hw
    rw [sli] at hli
    simp [Conn.waitLine, ho, hp, hf, hw, hli, e0, hl]

theorem summary_ne_modeReader (held : List Journal.Commit) (g : List Byte) :
    summary held g ≠ .modeReader := by
  unfold summary; split <;> simp

theorem foundAs_ne_modeReader (k : Cmd) (x : Nat × List Byte) : foundAs k x ≠ .modeReader := by
  obtain ⟨n, id⟩ := x; simp only [foundAs]; split <;> simp

theorem getD_map_ne_modeReader {α : Type} (o : Option α) (f : α → Reply) (d : Reply)
    (hf : ∀ x, f x ≠ .modeReader) (hd : d ≠ .modeReader) : (o.map f).getD d ≠ .modeReader := by
  cases o <;> simp_all

theorem viewOf_ne_modeReader (p : Posting) (c : Conn) (lg : Bool) (f : Option (List Byte)) (s : Sel) :
    viewOf p c lg f s ≠ .modeReader := by
  cases s <;> simp only [viewOf] <;> (repeat' split) <;> simp_all
  all_goals exact getD_map_ne_modeReader _ _ _ (fun _ e => Reply.noConfusion e) (by decide)

/-- MODE READER's 502 is left by `resolve` only without a store. -/
theorem resolve_modeReader {p : Posting} {c : Conn} :
    ∀ r, resolve p c r = .modeReader → p.offered = false := by
  intro r h
  cases r <;> simp only [resolve] at h <;> (repeat' split at h) <;>
    first
      | exact absurd h (summary_ne_modeReader _ _)
      | exact absurd h (getD_map_ne_modeReader _ _ _ (foundAs_ne_modeReader _) (by decide))
      | exact absurd h (getD_map_ne_modeReader _ _ _ (fun _ e => Reply.noConfusion e) (by decide))
      | exact absurd h (viewOf_ne_modeReader _ _ _ _ _)
      | (simp_all; done)

/-- An open connection that answers QUIT, or MODE READER without a store, is left with the 205 or the
502 to send and nothing held; the 502 only without a store. -/
theorem serve_quit (i : Identity) (p : Posting) (now : Nat) :
    ∀ fuel (c : Conn), c.phase = .open_ → (serve i p now fuel c).phase = .quitting →
      ((serve i p now fuel c).out = text i .quit ∨
        (p.offered = false ∧ (serve i p now fuel c).out = text i .modeReader)) ∧
        (serve i p now fuel c).held = [] := by
  intro fuel
  induction fuel with
  | zero => intro c hp h; simp only [serve] at h; rw [hp] at h; cases h
  | succ fuel ih =>
    intro c hp h
    revert h
    unfold serve
    split
    · intro h; rw [hp] at h; cases h
    · simp only
      split
      · intro h; simp only at h; rw [hp] at h; cases h
      · split
        · exact ih _ hp
        · split
          · intro h; rw [hp] at h; cases h
          · split
            · intro h; simp only at h; rw [hp] at h; cases h
            · split
              · exact ih _ hp
              · split
                · rename_i hq
                  intro _
                  rcases hq with hq | hq
                  · exact ⟨.inl (by rw [hq]), rfl⟩
                  · exact ⟨.inr ⟨resolve_modeReader _ hq, by rw [hq]⟩, rfl⟩
                · exact ih _ hp

/-- **After a QUIT, only what is left of its reply and the close**: a connection answering QUIT, or
MODE READER without a store, is closed at a deadline, waits for the host, sends the rest of its output
without asking to read, or is closed gracefully. -/
theorem act_quitting (i : Identity) (now wall idx : Nat) (st : Option Store) (c : Conn)
    (hq : c.phase = .quitting) :
    (act i now wall idx st c).2.1 = some (.closeNow idx c.gen) ∨
      (act i now wall idx st c).2.1 = none ∨
      (act i now wall idx st c).2.1 = some (.send idx c.gen c.out false) ∨
      (act i now wall idx st c).2.1 = some (.closeGracefully idx c.gen) := by
  unfold act
  split
  · exact .inl rfl
  · rw [progress_busy i now wall st c (.inr hq)]
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [progressRead_busy i now st c (.inr hq)]
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [progressList_busy now wall st c (.inr hq)]
    simp only [Bool.false_eq_true, ↓reduceIte, hq, bne_self_eq_false, Bool.and_false,
      Bool.false_and, Bool.and_not_self, want_both]
    rw [claim_busy i now idx st c (.inr hq), claimRead_busy idx st c (.inr hq)]
    unfold emit
    split
    · split
      · exact .inr (.inl rfl)
      · exact .inr (.inr (.inl (by simp [Conn.wantsWith, Conn.wants, hq])))
    · exact .inr (.inr (.inr (by simp [hq])))

/-! ## After a QUIT or a 502, only what is left of it -/

/-- A connection that answered QUIT, or MODE READER without a store, has only what is left of the 205
or the 502 to send. -/
def Conn.QuitRest (i : Identity) (c : Conn) : Prop :=
  c.phase = .quitting → c.out <:+ text i .quit ∨ c.out <:+ text i .modeReader

def Table.QuitRest (i : Identity) (t : Table) : Prop := ∀ c, some c ∈ t → c.QuitRest i

theorem empty_quitRest (i : Identity) : Table.QuitRest i Table.empty := by
  intro c hc
  simp [Table.empty, List.mem_replicate] at hc

theorem quitRest_set {i : Identity} {t : Table} {idx : Nat} {x : Option Conn}
    (h : Table.QuitRest i t) (hx : ∀ c, x = some c → c.QuitRest i) :
    Table.QuitRest i (t.set idx x) := by
  intro c hc
  rcases List.mem_or_eq_of_mem_set hc with h1 | h1
  · exact h c h1
  · exact hx c h1.symm

theorem live_mem {t : Table} {idx gen : Nat} {c : Conn} (h : t.live idx gen = some c) :
    some c ∈ t := by
  unfold Table.live at h
  split at h
  · rename_i c' hc
    split at h
    · cases h
      exact List.mem_of_getElem? hc
    · cases h
  · cases h

theorem applyEvent_quitRest {i : Identity} {now : Nat} {s s' : Server} {e : Event}
    (h : applyEvent i now s e = .ok s') (hs : Table.QuitRest i s.table) :
    Table.QuitRest i s'.table := by
  cases e with
  | opened idx gen mp =>
    unfold applyEvent at h
    cases hc : checkIndex idx with
    | error b => simp [hc, bind, Except.bind] at h
    | ok u =>
      simp only [hc, bind, Except.bind] at h
      split at h
      · cases h
      · split at h
        · cases h
        · cases h
          exact quitRest_set hs fun c hc' => by cases hc'; intro hq; cases hq
  | received idx gen data =>
    unfold applyEvent at h
    cases hc : checkIndex idx with
    | error b => simp [hc, bind, Except.bind] at h
    | ok u =>
      by_cases hlen : chunk < data.length
      · simp [hc, hlen, bind, Except.bind] at h
      · simp only [hc, hlen, bind, Except.bind, if_false, pure, Except.pure] at h
        split at h
        · rename_i c hl
          split at h
          · cases h
            exact quitRest_set hs fun c' hc' => by cases hc'; exact hs c (live_mem hl)
          · cases h
        · cases h; exact hs
  | writable idx gen =>
    unfold applyEvent at h
    cases hc : checkIndex idx with
    | error b => simp [hc, bind, Except.bind] at h
    | ok u =>
      simp only [hc, bind, Except.bind] at h
      split at h
      · rename_i c hl
        cases h
        exact quitRest_set hs fun c' hc' => by cases hc'; exact hs c (live_mem hl)
      · cases h; exact hs
  | inputEnded idx gen =>
    unfold applyEvent at h
    cases hc : checkIndex idx with
    | error b => simp [hc, bind, Except.bind] at h
    | ok u =>
      simp only [hc, bind, Except.bind] at h
      split at h
      · split at h
        · cases h
          exact quitRest_set hs fun c' hc' => by cases hc'; intro hq; cases hq
        · cases h
      · cases h; exact hs
  | closed idx gen =>
    unfold applyEvent at h
    cases hc : checkIndex idx with
    | error b => simp [hc, bind, Except.bind] at h
    | ok u =>
      simp only [hc, bind, Except.bind] at h
      split at h
      · cases h
        exact quitRest_set hs fun c' hc' => by cases hc'
      · cases h; exact hs

theorem events_quitRest {i : Identity} {now : Nat} :
    ∀ (es : List Event) (s s' : Server), es.foldlM (applyEvent i now) s = .ok s' →
      Table.QuitRest i s.table → Table.QuitRest i s'.table
  | [], s, s', h, hs => by
    simp only [List.foldlM, pure, Except.pure, Except.ok.injEq] at h
    exact h ▸ hs
  | e :: es, s, s', h, hs => by
    simp only [List.foldlM, bind, Except.bind] at h
    split at h
    · cases h
    · rename_i s1 h1
      exact events_quitRest es s1 s' h (applyEvent_quitRest h1 hs)

/-- Serving a connection that has not answered QUIT leaves it with the 205 or the 502 to send, if it
answers QUIT or MODE READER without a store now. -/
theorem serve_quitRest (i : Identity) (p : Posting) (now : Nat) :
    ∀ fuel (c : Conn), c.phase ≠ .quitting → (serve i p now fuel c).QuitRest i := by
  intro fuel
  induction fuel with
  | zero => intro c hp hq; exact absurd hq hp
  | succ fuel ih =>
    intro c hp
    unfold serve
    split
    · intro hq; exact absurd hq hp
    · simp only
      split
      · intro hq; exact absurd hq hp
      · split
        · exact ih _ hp
        · split
          · intro hq; exact absurd hq hp
          · split
            · intro hq; exact absurd hq hp
            · split
              · exact ih _ hp
              · split
                · rename_i hq
                  intro _
                  show text i _ <:+ _ ∨ text i _ <:+ _
                  rcases hq with hq | hq
                  · rw [hq]; exact .inl (List.suffix_refl _)
                  · rw [hq]; exact .inr (List.suffix_refl _)
                · exact ih _ hp

theorem waitLine_quitRest {i : Identity} {now : Nat} {c : Conn} (h : c.QuitRest i) :
    (Conn.waitLine now c).QuitRest i := by
  unfold Conn.waitLine
  split
  · split
    · exact h
    · exact h
  · exact h

theorem emit_keeps {idx : Nat} {w : Bool} {c c1 : Conn} (h : (emit idx w c).1 = some c1) :
    c1.phase = c.phase ∧ c1.out = c.out := by
  unfold emit at h
  repeat (first | split at h | (cases h; exact ⟨rfl, rfl⟩) | cases h)

/-- What `progress` and `claim` leave of a connection that answers QUIT, or of one that does
not. -/
theorem progress_quitRest (i : Identity) (now wall : Nat) (st : Option Store) (c : Conn)
    (h : c.QuitRest i) : (progress i now wall st c).1.QuitRest i := by
  by_cases hq : c.phase = .quitting
  · rw [progress_busy i now wall st c (.inr hq)]; exact h
  · intro hq'
    exact absurd ((progress_keeps i now wall st c).1 ▸ hq') hq

theorem claim_quitRest (i : Identity) (now idx : Nat) (st : Option Store) (c : Conn)
    (h : c.QuitRest i) : (claim i now idx st c).1.QuitRest i := by
  by_cases hq : c.phase = .quitting
  · rw [claim_busy i now idx st c (.inr hq)]; exact h
  · intro hq'
    exact absurd ((claim_keeps i now idx st c).1 ▸ hq') hq

theorem progressRead_quitRest (i : Identity) (now : Nat) (st : Option Store) (c : Conn)
    (h : c.QuitRest i) : (progressRead i now st c).1.QuitRest i := by
  by_cases hq : c.phase = .quitting
  · rw [progressRead_busy i now st c (.inr hq)]; exact h
  · intro hq'
    exact absurd ((progressRead_keeps i now st c).1 ▸ hq') hq

theorem progressList_quitRest (i : Identity) (now wall : Nat) (st : Option Store) (c : Conn)
    (h : c.QuitRest i) : (progressList now wall st c).QuitRest i := by
  by_cases hq : c.phase = .quitting
  · rw [progressList_busy now wall st c (.inr hq)]; exact h
  · intro hq'
    exact absurd ((progressList_keeps now wall st c).1 ▸ hq') hq

theorem claimRead_quitRest (i : Identity) (idx : Nat) (st : Option Store) (c : Conn)
    (h : c.QuitRest i) : (claimRead idx st c).1.QuitRest i := by
  by_cases hq : c.phase = .quitting
  · rw [claimRead_busy idx st c (.inr hq)]; exact h
  · intro hq'
    exact absurd ((claimRead_keeps idx st c).1 ▸ hq') hq

theorem act_quitRest {i : Identity} {now wall idx : Nat} {st : Option Store} {c c' : Conn}
    (hc : c.QuitRest i) (h : (act i now wall idx st c).1 = some c') : c'.QuitRest i := by
  unfold act at h
  split at h
  · cases h
  · dsimp only at h
    split at h
    · cases h
    · split at h
      · cases h
      · simp only [Option.map_eq_some_iff] at h
        obtain ⟨c1, h1, rfl⟩ := h
        apply waitLine_quitRest
        have hg := progressList_quitRest i now wall
          (progressRead i now (progress i now wall st c).2.1 (progress i now wall st c).1).2.1 _
          (progressRead_quitRest i now (progress i now wall st c).2.1 _ (progress_quitRest i now wall st c hc))
        obtain ⟨hp, ho⟩ := emit_keeps h1
        intro hq
        rw [ho]
        apply claimRead_quitRest i idx _ _ ?_ (hp ▸ hq)
        apply claim_quitRest i now idx _ _ ?_
        split
        · rename_i hs
          simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at hs
          exact serve_quitRest i _ now _ _ hs.1.1.1.1.2
        · exact hg

theorem actFrom_quitRest {i : Identity} {now wall : Nat} {t : Table} (ht : Table.QuitRest i t) :
    ∀ (l : List Nat) (st : Option Store) (c : Conn),
      some c ∈ (actFrom i now wall t l st).1.map (·.1) → c.QuitRest i
  | [], _, _, h => by simp [actFrom] at h
  | idx :: rest, st, c, h => by
    unfold actFrom at h
    split at h
    · rename_i c0 hc0
      simp only [List.map_cons, List.mem_cons] at h
      rcases h with h | h
      · exact act_quitRest (ht c0 (List.mem_of_getElem? hc0)) h.symm
      · exact actFrom_quitRest ht rest _ c h
    · simp only [List.map_cons, List.mem_cons] at h
      rcases h with h | h
      · cases h
      · exact actFrom_quitRest ht rest _ c h

theorem turn_quitRest {i : Identity} {s s' : Server} {now wall : Nat} {es : List Event}
    {ds : List Done} {actions : List Action} {js : List Job}
    (h : turn i s now wall es ds = .ok (s', actions, js))
    (hs : Table.QuitRest i s.table) : Table.QuitRest i s'.table := by
  unfold turn at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  split at h
  · cases h
  · split at h
    · cases h
    · split at h
      · cases h
      · rename_i s1 hs1
        split at h
        · cases h
        · cases h
          exact fun c hc => actFrom_quitRest (events_quitRest es s s1 hs1 hs) _ _ c hc

theorem settleTable_quitRest {i : Identity} {now : Nat} :
    ∀ (t : Table) (acts : List Action) (taken : List Nat) (t' : Table),
      settleTable now t acts taken = .ok t' → Table.QuitRest i t → Table.QuitRest i t'
  | t, [], [], t', h, ht => by
    simp only [settleTable, pure, Except.pure, Except.ok.injEq] at h
    exact h ▸ ht
  | t, .send idx gen data _ :: rest, n :: ns, t', h, ht => by
    simp only [settleTable, bind, Except.bind] at h
    split at h
    · cases h
    · refine settleTable_quitRest _ rest ns t' h ?_
      split
      · rename_i c hl
        apply quitRest_set ht
        intro c' hc'
        cases hc'
        apply waitLine_quitRest
        intro hq
        exact (ht c (live_mem hl) hq).imp (List.drop_suffix _ _).trans (List.drop_suffix _ _).trans
      · exact ht
  | t, .send .. :: _, [], t', h, _ => by simp [settleTable] at h
  | t, .closeGracefully .. :: rest, ns, t', h, ht => by
    simp only [settleTable] at h
    exact settleTable_quitRest t rest ns t' h ht
  | t, .closeNow .. :: rest, ns, t', h, ht => by
    simp only [settleTable] at h
    exact settleTable_quitRest t rest ns t' h ht
  | t, [], _ :: _, t', h, _ => by simp [settleTable] at h

/-- **After a QUIT or a 502, only what is left of it**: from a table in which every connection that
answered QUIT, or MODE READER without a store, has only the rest of the 205 or the 502 to send, as the
empty table, a turn and what the host took of its sends leave a table of which the same holds;
`act_quitting` says such a connection sends only its output or closes. -/
theorem quit_rest {i : Identity} {s s' s'' : Server} {now wall : Nat} {es : List Event}
    {ds : List Done} {actions : List Action} {js : List Job} {taken : List Nat}
    (hs : Table.QuitRest i s.table) (h : turn i s now wall es ds = .ok (s', actions, js))
    (h' : settle s' actions taken = .ok s'') : Table.QuitRest i s''.table := by
  have h1 := turn_quitRest h hs
  unfold settle at h'
  simp only [bind, Except.bind, pure, Except.pure] at h'
  split at h'
  · cases h'
  · rename_i t ht
    cases h'
    exact settleTable_quitRest _ _ _ _ ht h1

theorem getD_set_le {l : List Nat} {idx gen : Nat} (h : l.getD idx 0 < gen) (k : Nat) :
    l.getD k 0 ≤ (l.set idx gen).getD k 0 := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_set]
  split
  · rename_i hk
    subst hk
    split
    · simp only [Option.getD_some]
      simp only [List.getD_eq_getElem?_getD] at h
      exact Nat.le_of_lt h
    · rename_i hl
      simp [List.getElem?_eq_none (Nat.le_of_not_lt hl)]
  · exact Nat.le_refl _

/-- An event leaves the last generation opened at each index where it was, or above it. -/
theorem applyEvent_gens {i : Identity} {now : Nat} {s s' : Server} {e : Event}
    (h : applyEvent i now s e = .ok s') (k : Nat) : s.gens.getD k 0 ≤ s'.gens.getD k 0 := by
  cases e with
  | opened idx gen mp =>
    unfold applyEvent at h
    cases hc : checkIndex idx with
    | error b => simp [hc, bind, Except.bind] at h
    | ok u =>
      simp only [hc, bind, Except.bind] at h
      split at h
      · cases h
      · split at h
        · cases h
        · rename_i hg
          cases h
          simp only [Bool.or_eq_true, decide_eq_true_eq, not_or, Nat.not_le] at hg
          exact getD_set_le hg.1 k
  | received idx gen data =>
    unfold applyEvent at h
    simp only [bind, Except.bind] at h
    repeat (first | split at h | (cases h; exact Nat.le_refl _) | cases h)
  | writable idx gen =>
    unfold applyEvent at h
    simp only [bind, Except.bind] at h
    repeat (first | split at h | (cases h; exact Nat.le_refl _) | cases h)
  | inputEnded idx gen =>
    unfold applyEvent at h
    simp only [bind, Except.bind] at h
    repeat (first | split at h | (cases h; exact Nat.le_refl _) | cases h)
  | closed idx gen =>
    unfold applyEvent at h
    simp only [bind, Except.bind] at h
    repeat (first | split at h | (cases h; exact Nat.le_refl _) | cases h)

/-- **An index's generations only rise**: an open is taken only at a generation past the last one
opened at its index and not past `genLimit`, and becomes the last; so a pair of an index and a
generation names at most one connection of a run, and what is left of a connection gone, an
event, a send or a read it owned, names none that follows it. -/
theorem applyEvent_opened {i : Identity} {now : Nat} {s s' : Server} {idx gen : Nat} {mp : Bool}
    (h : applyEvent i now s (.opened idx gen mp) = .ok s') :
    s.gens.getD idx 0 < gen ∧ gen ≤ genLimit ∧ s'.gens = s.gens.set idx gen := by
  unfold applyEvent at h
  cases hc : checkIndex idx with
  | error b => simp [hc, bind, Except.bind] at h
  | ok u =>
    simp only [hc, bind, Except.bind] at h
    split at h
    · cases h
    · split at h
      · cases h
      · rename_i hg
        cases h
        simp only [Bool.or_eq_true, decide_eq_true_eq, not_or, Nat.not_le] at hg
        exact ⟨hg.1, Nat.not_lt.mp hg.2, rfl⟩

theorem events_gens {i : Identity} {now : Nat} :
    ∀ (es : List Event) (s s' : Server), es.foldlM (applyEvent i now) s = .ok s' →
      ∀ k, s.gens.getD k 0 ≤ s'.gens.getD k 0
  | [], s, s', h, k => by
    simp only [List.foldlM, pure, Except.pure, Except.ok.injEq] at h
    exact h ▸ Nat.le_refl _
  | e :: es, s, s', h, k => by
    simp only [List.foldlM, bind, Except.bind] at h
    split at h
    · cases h
    · rename_i s1 h1
      exact Nat.le_trans (applyEvent_gens h1 k) (events_gens es s1 s' h k)

/-- A turn, and what the host took of its sends, leave each index's last generation where it was or
above. -/
theorem turn_gens {i : Identity} {s s' : Server} {now wall : Nat} {es : List Event}
    {ds : List Done} {actions : List Action} {js : List Job}
    (h : turn i s now wall es ds = .ok (s', actions, js)) (k : Nat) :
    s.gens.getD k 0 ≤ s'.gens.getD k 0 := by
  unfold turn at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  split at h
  · cases h
  · split at h
    · cases h
    · split at h
      · cases h
      · rename_i s1 hs1
        split at h
        · cases h
        · cases h
          exact events_gens es s s1 hs1 k

theorem settle_gens {s s' : Server} {actions : List Action} {taken : List Nat}
    (h : settle s actions taken = .ok s') : s'.gens = s.gens := by
  unfold settle at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  split at h
  · cases h
  · cases h; rfl

/-- An index opened again at its last generation is a breach. -/
theorem reopened_witness :
    (match applyEvent ⟨[], []⟩ 0 { gens := [1] } (.opened 0 1 false) with
      | .error b => b == .reopened
      | .ok _ => false) = true := by decide

/-- The premise holds of a connection that has just answered QUIT, and of the empty table. -/
theorem quitRest_witness :
    Conn.QuitRest ⟨[], []⟩ { Conn.fresh ⟨[], []⟩ false 1 1 0 with
        phase := .quitting, out := text ⟨[], []⟩ .quit } ∧
      Table.QuitRest ⟨[], []⟩ Table.empty :=
  ⟨fun _ => .inl (List.suffix_refl _), empty_quitRest _⟩

end DN.News.SessionSpec
