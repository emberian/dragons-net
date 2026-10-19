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
connection is closed gracefully once it is taken; after the end of input the connection is closed
the same way once every whole line it sent is answered. A deadline that passes closes the
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
-/

namespace DN.News.SessionSpec

open DN.News.FrameSpec DN.News.Framer DN.News.CommandSpec
open DN.News.PostSpec (Store Slot Job Done Fault Read)

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

inductive Phase
  /-- greeted, no command yet or commands being answered -/
  | open_
  /-- the reply to QUIT is being sent; the connection closes when it is taken -/
  | quitting
  /-- the input has ended; what was received is answered, then the connection closes -/
  | ending
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
  /-- the ARTICLE, HEAD or BODY it waits for a read for or is answered by one, with the message-id -/
  want : Option (Cmd × List Byte) := none
  /-- the read that answers it -/
  read : Option Nat := none
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
  /-- a connection opened at an index still in use -/
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

/-- The table, the host's clock at the last batch, the store if there is one, and how many
connections have opened. -/
structure Server where
  table : Table := Table.empty
  clock : Nat := 0
  store : Option Store := none
  opened : Nat := 0

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
      let c := Conn.fresh i (greets s.store mayPost) (s.opened + 1) gen now
      return { s with table := s.table.set idx (some c), opened := s.opened + 1 }
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
                           read := none }
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

/-- …and no POST or read waits or is answered, and the slot of its POST takes octets. -/
def Conn.wantsWith (st : Option Store) (c : Conn) : Bool :=
  c.wants && !c.waiting && c.want.isNone && match c.post with
    | none => true
    | some k => st.any fun st => (st.slot k).any Slot.takes

/-- The line's deadline runs while the program waits for the rest of a line: everything sent was
taken, the connection takes commands and is not answered by a read, and a line is begun. It starts when the waiting starts,
and nothing but the end of the waiting moves it. -/
def Conn.waitLine (now : Nat) (c : Conn) : Conn :=
  if c.out.isEmpty && c.phase == .open_ && c.line != .fresh && c.want.isNone then
    if c.lineDue == 0 then { c with lineDue := now + lineTime } else c
  else { c with lineDue := 0 }

/-- What a store makes of a reply: whether POST is offered, whether the store accepts, and the
message-ids of the articles it holds. -/
structure Posting where
  offered : Bool
  accepting : Bool
  ids : List (List Byte)

/-- What a store makes of a reply, if there is one. -/
def Posting.of : Option Store → Posting
  | some st => ⟨true, st.accepting, st.articles.map (·.messageId)⟩
  | none => ⟨false, false, []⟩

/-- The reply a connection gets with a store: the capabilities with POST while it may post, the
help with POST, for a well-formed POST 340, 440 or 403, and for a message-id the store does not
hold 430, for one it holds with STAT 223. -/
def resolve (p : Posting) (c : Conn) : Reply → Reply
  | .capabilities => if c.greeted && p.accepting then .capabilitiesPost else .capabilities
  | .help => if p.offered then .helpPost else .help
  | .post => if !c.greeted then .notPermitted else if !p.accepting then .unavailable else .post
  | .lookup k id => if !p.ids.contains id then .noSuchId else if k = .stat then .stat id else .lookup k id
  | r => r

/-- Answer the first held line that gets a reply, putting it in `out`, and frame on past the lines
that get none and into an unfinished last line, stopping before the next line that gets a reply: a
connection holds input only while such a line waits. A connection with output untaken, or an
ARTICLE, HEAD or BODY to be answered by a read, answers nothing; a POST that may have a slot waits
for one. Each round frames at least one byte, so `fuel`
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
          if !c.out.isEmpty || c.want.isSome then c
          else if r = .post then { c1 with waiting := true, first := 0, idle := 0 }
          else if let .lookup k id := r then
            serve i p now fuel { c1 with want := some (k, id), first := 0, idle := 0 }
          else
            let c2 := { c1 with out := text i r, first := 0, idle := now + inactivity }
            if r = .quit then { c2 with phase := .quitting, held := [] } else serve i p now fuel c2

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
          (serve i (Posting.of (some freed)) now (f.2.length + 1) c', some freed, false)
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
inactivity deadline then started, or stopped while there are none; once all of them are put, the
read ended; a read that failed answered 403 when it gave nothing, or the connection to close. -/
def progressRead (i : Identity) (now : Nat) (st : Option Store) (c : Conn) :
    Conn × Option Store × Bool :=
  match c.read, st with
  | some k, some st =>
    if !c.out.isEmpty || c.phase = .quitting then (c, some st, false)
    else
      match st.readSlot k with
      | some r =>
        if r.bad then
          if r.given = 0 then
            ({ c with out := text i .unreadable, read := none, want := none, idle := now + inactivity },
             some (st.setRead k (some { r with owner := none })).tidy, false)
          else (c, some st, true)
        else
          let piece := (r.out.extract r.given (r.given + CommandSpec.actionData)).toList
          if piece.isEmpty then ({ c with idle := 0 }, some st, false)
          else
            let given := r.given + piece.length
            let ends := r.whole st.rules && given == r.out.size
            let c' := { c with out := piece, idle := now + inactivity }
            let r' := { r with given, owner := if ends then none else r.owner }
            (if ends then { c' with read := none, want := none } else c',
             some (st.setRead k (some r')).tidy, false)
      | none => ({ c with read := none, want := none }, some st, false)
  | _, st => (c, st, false)

/-- An ARTICLE, HEAD or BODY that waits gets a free read, when fewer came before it than reads are
free. -/
def claimRead (idx : Nat) (st : Option Store) (c : Conn) : Conn × Option Store :=
  match st, c.want with
  | some st, some (k, id) =>
    if c.read.isNone && c.out.isEmpty && c.phase = .open_ && st.admitsRead (idx, c.gen) then
      match (List.range st.rules.reads).find? st.readFree, st.find id with
      | some j, some cm =>
        let st' := { st with readers := st.readers.erase (idx, c.gen) }
        let r : Read := { owner := some (idx, c.gen), cmd := k, commit := cm }
        ({ c with read := some j }, some (st'.setRead j (some (r.refresh st.rules st.cfg.identity))))
      | _, _ => (c, some st)
    else (c, some st)
  | st, _ => (c, st)

/-- What a connection that is not closed at a deadline asks of the host once it is served: its
output, with whether to read once it is taken, unless the host has not yet reported it ready
after leaving part of it; or a graceful close once everything is answered and taken after a QUIT
or the end of input; or, with nothing to send, whether to read, when that has changed. -/
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
        let c1 := if h.1.out.isEmpty && h.1.phase != .quitting && h.1.post.isNone && !h.1.waiting &&
            h.1.want.isNone
          then serve i (Posting.of h.2.1) now (h.1.held.length + 1) h.1 else h.1
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
for its 403, waits for a read it gets now, or is answered by a read that has octets to give or
failed. -/
def Conn.ready (st : Option Store) (idx : Nat) (c : Conn) : Bool :=
  c.out.isEmpty && (c.phase != .open_ ||
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

/-- A store's answer keeps a reply's message-id one a store may hold. -/
theorem resolve_idOk (p : Posting) (c : Conn) (r : Reply) (h : r.idOk = true) :
    (resolve p c r).idOk = true := by
  cases r <;> simp only [resolve] <;> (repeat' split) <;> simp_all [Reply.idOk]

/-- **Every reply a connection gets fits one action**, with a store or without. -/
theorem reply_fits (i : Identity) (hi : i.ok = true) (p : Posting) (c : Conn) (l : Line) :
    (text i (resolve p c (replyIn p.offered l))).length ≤ CommandSpec.actionData :=
  text_fits i hi _ (resolve_idOk p c _ (replyIn_idOk _ l))

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

theorem want_both (c : Conn) : (c.want.isSome && c.want.isNone) = false := by
  cases c.want <;> rfl

/-- **Output untaken is sent again once the host has reported the connection ready, and nothing
else is**: no line is answered before what came before it is taken. -/
theorem act_resends (i : Identity) (now wall idx : Nat) (st : Option Store) (c : Conn)
    (hd : c.due now = false) (h : c.out ≠ []) (hb : c.blocked = false) :
    (act i now wall idx st c).2.1 = some (.send idx c.gen c.out (c.wantsWith st)) := by
  simp [act, hd, progress_busy i now wall st c (.inl h), progressRead_busy i now st c (.inl h),
    claim_busy i now idx st c (.inl h), claimRead_busy idx st c (.inl h), emit, isEmpty_false h, hb,
    want_both]

/-- …and nothing is sent to a connection the host has not reported ready. -/
theorem act_blocked (i : Identity) (now wall idx : Nat) (st : Option Store) (c : Conn)
    (hd : c.due now = false) (h : c.out ≠ []) (hb : c.blocked = true) :
    (act i now wall idx st c).2.1 = none := by
  simp [act, hd, progress_busy i now wall st c (.inl h), progressRead_busy i now st c (.inl h),
    claim_busy i now idx st c (.inl h), claimRead_busy idx st c (.inl h), emit, isEmpty_false h, hb,
    want_both]

/-- Every reply but `ignore` has bytes. -/
theorem text_ne_nil (i : Identity) : ∀ r, r ≠ .ignore → text i r ≠ []
  | .ignore, h => absurd rfl h
  | .capabilities, _ => fun e =>
    absurd (List.append_eq_nil_iff.mp (List.append_eq_nil_iff.mp e).1).1 (by decide +kernel)
  | .capabilitiesPost, _ => fun e =>
    absurd (List.append_eq_nil_iff.mp (List.append_eq_nil_iff.mp (List.append_eq_nil_iff.mp
      e).1).1).1 (by decide +kernel)
  | .help, _ | .helpPost, _ => fun e =>
    absurd (List.append_eq_nil_iff.mp (List.append_eq_nil_iff.mp (List.append_eq_nil_iff.mp
      (List.append_eq_nil_iff.mp e).1).1).1).1 (by decide +kernel)
  | .stat _, _ => fun e => absurd (List.append_eq_nil_iff.mp (List.append_eq_nil_iff.mp e).1).1
    (by decide +kernel)
  | .quit, _ | .noGroup, _ | .noSuchId, _ | .unknown, _ | .syntax, _ | .post, _ | .posted, _
  | .failed, _ | .notPermitted, _ | .unavailable, _ | .lookup _ _, _ | .unreadable, _ => by
    simp only [text]; decide +kernel

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

theorem claimRead_keeps (idx : Nat) (st : Option Store) (c : Conn) :
    (claimRead idx st c).1.phase = c.phase ∧ (claimRead idx st c).1.lineDue = c.lineDue := by
  unfold claimRead
  repeat (first | split | exact ⟨rfl, rfl⟩ | dsimp only)

/-- **Bytes do not move the line's deadline**: a connection still waiting for the rest of a line
after its turn keeps the deadline it had, whatever the turn read. -/
theorem act_keeps_line (i : Identity) (now wall idx : Nat) (st : Option Store) (c c' : Conn)
    (hd : c.due now = false) (hl : c.lineDue ≠ 0) (h : (act i now wall idx st c).1 = some c')
    (ho : c'.out = []) (hp : c'.phase = .open_) (hf : c'.line ≠ .fresh) (hw : c'.want = none) :
    c'.lineDue = c.lineDue := by
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
      · rw [serve_lineDue, (progressRead_keeps ..).2, (progress_keeps ..).2]
      · rw [(progressRead_keeps ..).2, (progress_keeps ..).2]
    obtain ⟨so, sp, sl⟩ := waitLine_same now c0
    have sw : (c0.waitLine now).want = c0.want := by
      unfold Conn.waitLine; split <;> (try split) <;> rfl
    rw [so] at ho
    rw [sp] at hp
    rw [sl] at hf
    rw [sw] at hw
    simp [Conn.waitLine, ho, hp, hf, hw, e0, hl]

/-- An open connection that answers QUIT is left with the 205 to send and nothing held. -/
theorem serve_quit (i : Identity) (p : Posting) (now : Nat) :
    ∀ fuel (c : Conn), c.phase = .open_ → (serve i p now fuel c).phase = .quitting →
      (serve i p now fuel c).out = text i .quit ∧ (serve i p now fuel c).held = [] := by
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
                  exact ⟨by rw [hq], rfl⟩
                · exact ih _ hp

/-- **After a QUIT, only what is left of its reply and the close**: a connection answering QUIT
is closed at a deadline, waits for the host, sends the rest of its output without asking to
read, or is closed gracefully. -/
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
    simp only [Bool.false_eq_true, ↓reduceIte, hq, bne_self_eq_false, Bool.and_false,
      Bool.false_and, Bool.and_not_self, want_both]
    rw [claim_busy i now idx st c (.inr hq), claimRead_busy idx st c (.inr hq)]
    unfold emit
    split
    · split
      · exact .inr (.inl rfl)
      · exact .inr (.inr (.inl (by simp [Conn.wantsWith, Conn.wants, hq])))
    · exact .inr (.inr (.inr (by simp [hq])))

/-! ## After a QUIT, only what is left of the 205 -/

/-- A connection that answered QUIT has only what is left of the 205 to send. -/
def Conn.QuitRest (i : Identity) (c : Conn) : Prop := c.phase = .quitting → c.out <:+ text i .quit

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

/-- Serving a connection that has not answered QUIT leaves it with the 205 to send, if it answers
QUIT now. -/
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
                  show text i _ <:+ _
                  rw [hq]
                  exact List.suffix_refl _
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
        have hg := progressRead_quitRest i now (progress i now wall st c).2.1 _
          (progress_quitRest i now wall st c hc)
        obtain ⟨hp, ho⟩ := emit_keeps h1
        intro hq
        rw [ho]
        apply claimRead_quitRest i idx _ _ ?_ (hp ▸ hq)
        apply claim_quitRest i now idx _ _ ?_
        split
        · rename_i hs
          simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at hs
          exact serve_quitRest i _ now _ _ hs.1.1.1.2
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
        exact (List.drop_suffix _ _).trans (ht c (live_mem hl) hq)
      · exact ht
  | t, .send .. :: _, [], t', h, _ => by simp [settleTable] at h
  | t, .closeGracefully .. :: rest, ns, t', h, ht => by
    simp only [settleTable] at h
    exact settleTable_quitRest t rest ns t' h ht
  | t, .closeNow .. :: rest, ns, t', h, ht => by
    simp only [settleTable] at h
    exact settleTable_quitRest t rest ns t' h ht
  | t, [], _ :: _, t', h, _ => by simp [settleTable] at h

/-- **After a QUIT, only what is left of the 205**: from a table in which every connection that
answered QUIT has only the rest of the 205 to send, as the empty table, a turn and what the host
took of its sends leave a table of which the same holds; `act_quitting` says such a connection
sends only its output or closes. -/
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

/-- The premise holds of a connection that has just answered QUIT, and of the empty table. -/
theorem quitRest_witness :
    Conn.QuitRest ⟨[], []⟩ { Conn.fresh ⟨[], []⟩ false 1 1 0 with
        phase := .quitting, out := text ⟨[], []⟩ .quit } ∧
      Table.QuitRest ⟨[], []⟩ Table.empty :=
  ⟨fun _ => List.suffix_refl _, empty_quitRest _⟩

end DN.News.SessionSpec
