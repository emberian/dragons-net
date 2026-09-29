-- SPDX-License-Identifier: AGPL-3.0-or-later
import DN.News.CommandSpec
import DN.News.Framer

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
-/

namespace DN.News.SessionSpec

open DN.News.FrameSpec DN.News.Framer DN.News.CommandSpec

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
/-- The host's clock stays below this, so deadlines never overflow a signed word. -/
def clockLimit : Nat := 2 ^ 62

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
  deriving DecidableEq, Repr

def Conn.fresh (i : Identity) (gen now : Nat) : Conn :=
  { gen, phase := .open_, line := .fresh, held := [], out := greeting i, reading := false,
    blocked := false, first := now + firstCommand, idle := now + inactivity, lineDue := 0 }

inductive Event
  | opened (idx gen : Nat)
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
  /-- a clock earlier than the last batch's, or not below `clockLimit` -/
  | badClock
  deriving DecidableEq, Repr

def Breach.code : Breach → Nat
  | .tooManyEvents => 1 | .tooLong => 2 | .noSuchIndex => 3 | .unasked => 4 | .overTaken => 5
  | .reopened => 6 | .badClock => 7

abbrev Table := List (Option Conn)

def Table.empty : Table := List.replicate conns none

/-- The table, and the host's clock at the last batch. -/
structure Server where
  table : Table := Table.empty
  clock : Nat := 0

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

/-- One event. An event for a connection the table does not hold, or of an older generation, is
left alone. -/
def applyEvent (i : Identity) (now : Nat) (t : Table) : Event → Except Breach Table
  | .opened idx gen => do
    checkIndex idx
    match t[idx]? with
    | some (some _) => throw .reopened
    | _ => return t.set idx (some (Conn.fresh i gen now))
  | .received idx gen data => do
    checkIndex idx
    if chunk < data.length then throw .tooLong
    match t.live idx gen with
    | some c => if c.asked then return t.set idx (some { c with held := data }) else throw .unasked
    | none => return t
  | .writable idx gen => do
    checkIndex idx
    match t.live idx gen with
    | some c => return t.set idx (some { c with blocked := false })
    | none => return t
  | .inputEnded idx gen => do
    checkIndex idx
    match t.live idx gen with
    | some c =>
      if c.asked then return t.set idx (some { c with phase := .ending, lineDue := 0 })
      else throw .unasked
    | none => return t
  | .closed idx gen => do
    checkIndex idx
    match t.live idx gen with
    | some _ => return t.set idx none
    | none => return t

/-- Whether a deadline has passed. -/
def Conn.due (c : Conn) (now : Nat) : Bool :=
  (c.first != 0 && c.first ≤ now) || c.idle ≤ now || (c.lineDue != 0 && c.lineDue ≤ now)

/-- Whether the host should read from the connection: it takes commands and holds none. -/
def Conn.wants (c : Conn) : Bool := c.phase == .open_ && c.held.isEmpty

/-- The line's deadline runs while the program waits for the rest of a line: everything sent was
taken, the connection takes commands, and a line is begun. It starts when the waiting starts,
and nothing but the end of the waiting moves it. -/
def Conn.waitLine (now : Nat) (c : Conn) : Conn :=
  if c.out.isEmpty && c.phase == .open_ && c.line != .fresh then
    if c.lineDue == 0 then { c with lineDue := now + lineTime } else c
  else { c with lineDue := 0 }

/-- Answer the first held line that gets a reply, putting it in `out`, and frame on past the lines
that get none and into an unfinished last line, stopping before the next line that gets a reply: a
connection holds input only while such a line waits. A connection with output untaken answers
nothing. Each round frames at least one byte, so `fuel` of one more than the held bytes is enough;
a line left unanswered was framed from the start of a line, so the framer's state is left as it
was. -/
def serve (i : Identity) (now : Nat) : Nat → Conn → Conn
  | 0, c => c
  | fuel + 1, c =>
    if c.held.isEmpty then c
    else
      let (k, line', v) := frameOnce lineLimit c.line c.held
      let c1 := { c with line := line', held := c.held.drop k }
      match v with
      | none => c1
      | some l =>
        match reply l with
        | .ignore => serve i now fuel c1
        | r =>
          if !c.out.isEmpty then c
          else
            let c2 := { c1 with out := text i r, first := 0, idle := now + inactivity }
            if r = .quit then { c2 with phase := .quitting, held := [] } else serve i now fuel c2

/-- What a connection that is not closed at a deadline asks of the host once it is served: its
output, with whether to read once it is taken, unless the host has not yet reported it ready
after leaving part of it; or a graceful close once everything is answered and taken after a QUIT
or the end of input. Whether to read changes only with something to send: input arrives only
when the connection asked for it, and is answered or framed in the same turn. -/
def emit (idx : Nat) (c : Conn) : Option Conn × Option Action :=
  if !c.out.isEmpty then
    if c.blocked then (some c, none)
    else (some { c with reading := c.wants }, some (.send idx c.gen c.out c.wants))
  else if c.phase = .quitting || (c.phase = .ending && c.held.isEmpty) then
    (none, some (.closeGracefully idx c.gen))
  else (some c, none)

/-- The action for one connection after the batch's events: at most one. -/
def act (i : Identity) (now idx : Nat) (c : Conn) : Option Conn × Option Action :=
  if c.due now then (none, some (.closeNow idx c.gen))
  else
    let r := emit idx
      (if c.out.isEmpty && c.phase != .quitting then serve i now (c.held.length + 1) c else c)
    (r.1.map (Conn.waitLine now), r.2)

/-- **A turn**: the batch's events in order, then each connection's action, by index. -/
def turn (i : Identity) (s : Server) (now : Nat) (events : List Event) :
    Except Breach (Server × List Action) := do
  if batch < events.length then throw .tooManyEvents
  if now < s.clock || clockLimit ≤ now then throw .badClock
  let t ← events.foldlM (applyEvent i now) s.table
  let results := (List.range conns).map fun idx =>
    match t[idx]? with
    | some (some c) => act i now idx c
    | _ => (none, none)
  return ({ table := results.map (·.1), clock := now }, results.filterMap (·.2))

/-- What the host took of each send, in the order of the sends: taken output leaves `out`, output
taken counts as activity, and a send not taken whole waits for the host to report the connection
ready. -/
def settleTable (now : Nat) (t : Table) : List Action → List Nat → Except Breach Table
  | [], [] => pure t
  | .send idx gen data _ :: rest, n :: ns => do
    if data.length < n then throw .overTaken
    let t := match t.live idx gen with
      | some c =>
        let idle := if n = 0 then c.idle else now + inactivity
        t.set idx (some (Conn.waitLine now
          { c with out := c.out.drop n, idle := idle, blocked := decide (n < data.length) }))
      | none => t
    settleTable now t rest ns
  | .send .. :: _, [] => throw .overTaken
  | _ :: rest, ns => settleTable now t rest ns
  | [], _ :: _ => throw .overTaken

def settle (s : Server) (actions : List Action) (taken : List Nat) : Except Breach Server := do
  return { s with table := ← settleTable s.clock s.table actions taken }

/-- Whether a connection can go on without waiting for the host: nothing of its output is
untaken, and it holds input to answer or has to close. -/
def Conn.ready (c : Conn) : Bool :=
  c.out.isEmpty && (!c.held.isEmpty || c.phase != .open_)

/-- The earliest of a connection's running deadlines. -/
def Conn.earliest (c : Conn) : Nat :=
  let d := if c.first != 0 then min c.first c.idle else c.idle
  if c.lineDue != 0 then min d c.lineDue else d

/-- **When the program needs its next turn**: now if a connection can go on, else the earliest
deadline; zero when there is none. -/
def deadline (s : Server) : Nat :=
  let live := s.table.filterMap id
  if live.any Conn.ready then max s.clock 1
  else live.foldl (fun d c => if d = 0 then c.earliest else min d c.earliest) 0

/-! ## What the session guarantees by construction -/

def Action.idx : Action → Nat
  | .send idx .. | .closeGracefully idx _ | .closeNow idx _ => idx

theorem emit_idx (idx : Nat) (c : Conn) (a : Action) (h : (emit idx c).2 = some a) :
    a.idx = idx := by
  revert h
  unfold emit
  split
  · split
    · intro h; cases h
    · intro h; cases h; rfl
  · split
    · intro h; cases h; rfl
    · intro h; cases h

theorem act_idx (i : Identity) (now idx : Nat) (c : Conn) (a : Action)
    (h : (act i now idx c).2 = some a) : a.idx = idx := by
  revert h
  unfold act
  split
  · intro h; cases h; rfl
  · exact emit_idx idx _ a

/-- **At most one action a connection in a turn**, in the order of the indexes. -/
theorem turn_ordered (i : Identity) (s s' : Server) (now : Nat) (evs : List Event)
    (acts : List Action) (h : turn i s now evs = .ok (s', acts)) :
    (acts.map Action.idx).Pairwise (· < ·) := by
  unfold turn at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  split at h
  · cases h
  · split at h
    · cases h
    · split at h
      · cases h
      · rename_i t1 _
        simp only [Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨-, rfl⟩ := h
        let g : Nat → Option Action := fun idx =>
          match t1[idx]? with
          | some (some c) => (act i now idx c).2
          | _ => none
        have hg : ∀ idx, ∀ a ∈ g idx, a.idx = idx := by
          intro idx a ha
          simp only [g, Option.mem_def] at ha
          split at ha
          · exact act_idx i now idx _ a ha
          · cases ha
        have e : ((List.range conns).map fun idx =>
            match t1[idx]? with
            | some (some c) => act i now idx c
            | _ => (none, none)).filterMap (·.2) = (List.range conns).filterMap g := by
          rw [List.filterMap_map]
          congr 1
          funext idx
          simp only [Function.comp_def, g]
          split <;> rfl
        rw [e, List.map_filterMap]
        have e2 : (List.range conns).filterMap (fun idx => (g idx).map Action.idx) =
            (List.range conns).filter (fun idx => (g idx).isSome) := by
          rw [← List.filterMap_eq_filter]
          congr 1
          funext idx
          cases hgi : g idx with
          | none => simp [Option.guard, hgi]
          | some a => simp [Option.guard, hg idx a hgi, hgi]
        rw [e2]
        exact (List.pairwise_lt_range).sublist List.filter_sublist

theorem isEmpty_false {α : Type} {l : List α} (h : l ≠ []) : l.isEmpty = false := by
  cases l <;> simp_all

/-- **Output untaken is sent again once the host has reported the connection ready, and nothing
else is**: no line is answered before what came before it is taken. -/
theorem act_resends (i : Identity) (now idx : Nat) (c : Conn) (hd : c.due now = false)
    (h : c.out ≠ []) (hb : c.blocked = false) :
    (act i now idx c).2 = some (.send idx c.gen c.out c.wants) := by
  simp [act, emit, hd, isEmpty_false h, hb]

/-- …and nothing is sent to a connection the host has not reported ready. -/
theorem act_blocked (i : Identity) (now idx : Nat) (c : Conn) (hd : c.due now = false)
    (h : c.out ≠ []) (hb : c.blocked = true) : (act i now idx c).2 = none := by
  simp [act, emit, hd, isEmpty_false h, hb]

/-- Every reply but `ignore` has bytes. -/
theorem text_ne_nil (i : Identity) : ∀ r, r ≠ .ignore → text i r ≠ []
  | .ignore, h => absurd rfl h
  | .capabilities, _ => fun e =>
    absurd (List.append_eq_nil_iff.mp (List.append_eq_nil_iff.mp e).1).1 (by decide +kernel)
  | .help, _ => fun e =>
    absurd (List.append_eq_nil_iff.mp (List.append_eq_nil_iff.mp (List.append_eq_nil_iff.mp
      (List.append_eq_nil_iff.mp e).1).1).1).1 (by decide +kernel)
  | .quit, _ | .noGroup, _ | .noSuchId, _ | .unknown, _ | .syntax, _ => by
    simp only [text]; decide +kernel

/-- `serve` leaves output that is already there as it is. -/
theorem serve_out (i : Identity) (now : Nat) :
    ∀ fuel (c : Conn), c.out ≠ [] → (serve i now fuel c).out = c.out := by
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
theorem serve_one (i : Identity) (now : Nat) :
    ∀ fuel (c : Conn), c.out = [] →
      (serve i now fuel c).out = [] ∨ ∃ r, r ≠ .ignore ∧ (serve i now fuel c).out = text i r := by
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
          simp only [h, List.isEmpty_nil, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
          split
          · exact .inr ⟨reply l, hr, rfl⟩
          · rw [serve_out]
            · exact .inr ⟨reply l, hr, rfl⟩
            · exact text_ne_nil i _ hr

/-- `serve` leaves the line's deadline to `Conn.waitLine`. -/
theorem serve_lineDue (i : Identity) (now : Nat) :
    ∀ fuel (c : Conn), (serve i now fuel c).lineDue = c.lineDue := by
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
            · exact ih _

theorem emit_lineDue (idx : Nat) (c c0 : Conn) (h : (emit idx c).1 = some c0) :
    c0.lineDue = c.lineDue := by
  unfold emit at h
  by_cases h1 : c.out.isEmpty <;> by_cases h2 : c.blocked <;>
    by_cases h3 : (c.phase = .quitting || (c.phase = .ending && c.held.isEmpty)) <;>
    simp only [h1, h2, h3] at h <;> simp at h <;> (try subst h) <;> rfl

/-- `Conn.waitLine` changes nothing but the line's deadline. -/
theorem waitLine_same (now : Nat) (c : Conn) :
    (c.waitLine now).out = c.out ∧ (c.waitLine now).phase = c.phase ∧
      (c.waitLine now).line = c.line := by
  unfold Conn.waitLine
  split
  · split <;> exact ⟨rfl, rfl, rfl⟩
  · exact ⟨rfl, rfl, rfl⟩

/-- **Bytes do not move the line's deadline**: a connection still waiting for the rest of a line
after its turn keeps the deadline it had, whatever the turn read. -/
theorem act_keeps_line (i : Identity) (now idx : Nat) (c c' : Conn) (hd : c.due now = false)
    (hl : c.lineDue ≠ 0) (h : (act i now idx c).1 = some c') (ho : c'.out = [])
    (hp : c'.phase = .open_) (hf : c'.line ≠ .fresh) : c'.lineDue = c.lineDue := by
  simp only [act, hd, Bool.false_eq_true, ↓reduceIte, Option.map_eq_some_iff] at h
  obtain ⟨c0, h0, rfl⟩ := h
  have e0 : c0.lineDue = c.lineDue := by
    rw [emit_lineDue idx _ c0 h0]
    split
    · exact serve_lineDue i now _ c
    · rfl
  obtain ⟨so, sp, sl⟩ := waitLine_same now c0
  rw [so] at ho
  rw [sp] at hp
  rw [sl] at hf
  simp [Conn.waitLine, ho, hp, hf, e0, hl]

/-- An open connection that answers QUIT is left with the 205 to send and nothing held. -/
theorem serve_quit (i : Identity) (now : Nat) :
    ∀ fuel (c : Conn), c.phase = .open_ → (serve i now fuel c).phase = .quitting →
      (serve i now fuel c).out = text i .quit ∧ (serve i now fuel c).held = [] := by
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
        · rename_i hr
          split
          · intro h; rw [hp] at h; cases h
          · split
            · rename_i hq
              intro _
              exact ⟨by rw [hq], rfl⟩
            · exact ih _ hp

/-- **After a QUIT, only what is left of its reply and the close**: a connection answering QUIT
is closed at a deadline, waits for the host, sends the rest of its output without asking to
read, or is closed gracefully. -/
theorem act_quitting (i : Identity) (now idx : Nat) (c : Conn) (hq : c.phase = .quitting) :
    (act i now idx c).2 = some (.closeNow idx c.gen) ∨ (act i now idx c).2 = none ∨
      (act i now idx c).2 = some (.send idx c.gen c.out false) ∨
      (act i now idx c).2 = some (.closeGracefully idx c.gen) := by
  unfold act
  split
  · exact .inl rfl
  · simp only [hq, bne_self_eq_false, Bool.and_false, Bool.false_eq_true, ↓reduceIte]
    unfold emit
    split
    · split
      · exact .inr (.inl rfl)
      · exact .inr (.inr (.inl (by simp [Conn.wants, hq])))
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

theorem applyEvent_quitRest {i : Identity} {now : Nat} {t t' : Table} {e : Event}
    (h : applyEvent i now t e = .ok t') (ht : Table.QuitRest i t) : Table.QuitRest i t' := by
  cases e with
  | opened idx gen =>
    unfold applyEvent at h
    cases hc : checkIndex idx with
    | error b => simp [hc, bind, Except.bind] at h
    | ok u =>
      simp only [hc, bind, Except.bind] at h
      split at h
      · cases h
      · cases h
        exact quitRest_set ht fun c hc' => by cases hc'; intro hq; cases hq
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
            exact quitRest_set ht fun c' hc' => by cases hc'; exact ht c (live_mem hl)
          · cases h
        · cases h; exact ht
  | writable idx gen =>
    unfold applyEvent at h
    cases hc : checkIndex idx with
    | error b => simp [hc, bind, Except.bind] at h
    | ok u =>
      simp only [hc, bind, Except.bind] at h
      split at h
      · rename_i c hl
        cases h
        exact quitRest_set ht fun c' hc' => by cases hc'; exact ht c (live_mem hl)
      · cases h; exact ht
  | inputEnded idx gen =>
    unfold applyEvent at h
    cases hc : checkIndex idx with
    | error b => simp [hc, bind, Except.bind] at h
    | ok u =>
      simp only [hc, bind, Except.bind] at h
      split at h
      · split at h
        · cases h
          exact quitRest_set ht fun c' hc' => by cases hc'; intro hq; cases hq
        · cases h
      · cases h; exact ht
  | closed idx gen =>
    unfold applyEvent at h
    cases hc : checkIndex idx with
    | error b => simp [hc, bind, Except.bind] at h
    | ok u =>
      simp only [hc, bind, Except.bind] at h
      split at h
      · cases h
        exact quitRest_set ht fun c' hc' => by cases hc'
      · cases h; exact ht

theorem events_quitRest {i : Identity} {now : Nat} :
    ∀ (es : List Event) (t t' : Table), es.foldlM (applyEvent i now) t = .ok t' →
      Table.QuitRest i t → Table.QuitRest i t'
  | [], t, t', h, ht => by
    simp only [List.foldlM, pure, Except.pure, Except.ok.injEq] at h
    exact h ▸ ht
  | e :: es, t, t', h, ht => by
    simp only [List.foldlM, bind, Except.bind] at h
    split at h
    · cases h
    · rename_i t1 h1
      exact events_quitRest es t1 t' h (applyEvent_quitRest h1 ht)

/-- Serving a connection that has not answered QUIT leaves it with the 205 to send, if it answers
QUIT now. -/
theorem serve_quitRest (i : Identity) (now : Nat) :
    ∀ fuel (c : Conn), c.phase ≠ .quitting → (serve i now fuel c).QuitRest i := by
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

theorem emit_keeps {idx : Nat} {c c1 : Conn} (h : (emit idx c).1 = some c1) :
    c1.phase = c.phase ∧ c1.out = c.out := by
  unfold emit at h
  by_cases ho : c.out.isEmpty = true
  · by_cases hq : (c.phase = .quitting || (c.phase = .ending && c.held.isEmpty)) = true
    · simp [ho, hq] at h
    · simp [ho, hq] at h
      subst h
      exact ⟨rfl, rfl⟩
  · by_cases hb : c.blocked = true
    · simp [ho, hb] at h
      subst h
      exact ⟨rfl, rfl⟩
    · simp [ho, hb] at h
      subst h
      exact ⟨rfl, rfl⟩

theorem act_quitRest {i : Identity} {now idx : Nat} {c c' : Conn} (hc : c.QuitRest i)
    (h : (act i now idx c).1 = some c') : c'.QuitRest i := by
  unfold act at h
  split at h
  · cases h
  · simp only [Option.map_eq_some_iff] at h
    obtain ⟨c1, h1, rfl⟩ := h
    apply waitLine_quitRest
    have h0 : (if c.out.isEmpty && c.phase != .quitting then serve i now (c.held.length + 1) c
        else c).QuitRest i := by
      split
      · rename_i hs
        simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at hs
        exact serve_quitRest i now _ c hs.2
      · exact hc
    obtain ⟨hp, ho⟩ := emit_keeps h1
    intro hq
    rw [ho]
    exact h0 (hp ▸ hq)

theorem turn_quitRest {i : Identity} {s s' : Server} {now : Nat} {es : List Event}
    {actions : List Action} (h : turn i s now es = .ok (s', actions))
    (hs : Table.QuitRest i s.table) : Table.QuitRest i s'.table := by
  unfold turn at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  split at h
  · cases h
  · split at h
    · cases h
    · split at h
      · cases h
      · rename_i t ht
        cases h
        have htq := events_quitRest es s.table t ht hs
        intro c hc
        simp only [List.map_map, List.mem_map, List.mem_range, Function.comp] at hc
        obtain ⟨k, _, hk⟩ := hc
        split at hk
        · rename_i c0 hc0
          exact act_quitRest (htq c0 (List.mem_of_getElem? hc0)) hk
        · cases hk

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
theorem quit_rest {i : Identity} {s s' s'' : Server} {now : Nat} {es : List Event}
    {actions : List Action} {taken : List Nat} (hs : Table.QuitRest i s.table)
    (h : turn i s now es = .ok (s', actions)) (h' : settle s' actions taken = .ok s'') :
    Table.QuitRest i s''.table := by
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
    Conn.QuitRest ⟨[], []⟩ { Conn.fresh ⟨[], []⟩ 1 0 with
        phase := .quitting, out := text ⟨[], []⟩ .quit } ∧
      Table.QuitRest ⟨[], []⟩ Table.empty :=
  ⟨fun _ => List.suffix_refl _, empty_quitRest _⟩

end DN.News.SessionSpec
