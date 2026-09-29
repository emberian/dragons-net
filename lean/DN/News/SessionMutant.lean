-- SPDX-License-Identifier: AGPL-3.0-or-later
import DN.News.SessionSpec

/-!
# DN.News.SessionMutant

The session of `DN.News.SessionSpec` with one of its rules broken, for the lane that holds the
session against an independent reference to show that it sees each (`scripts/session_check.py`).
With no rule broken it is the specification (`turnM_none`, `settleM_none`, `deadlineM_none`).
-/

namespace DN.News.SessionMutant

open DN.News.FrameSpec DN.News.Framer DN.News.CommandSpec DN.News.SessionSpec

inductive Mutant
  | none
  /-- bytes received start the line's deadline again -/
  | lineRenewed
  /-- no deadline for the rest of a line -/
  | noLineDeadline
  /-- the line's deadline runs while output is untaken -/
  | lineWhileBusy
  /-- output taken does not count as activity -/
  | idleNotRenewed
  /-- a send of which nothing was taken counts as activity -/
  | zeroTakeCounts
  /-- a line that gets no reply counts as a command -/
  | blankCounts
  /-- the first command does not clear its deadline -/
  | firstNotCleared
  /-- reading stops for good once a command is answered -/
  | readNotResumed
  /-- no greeting -/
  | noGreeting
  /-- events of an older generation are applied -/
  | staleApplied
  /-- the end of input is not acted on -/
  | endIgnored
  /-- untaken output is sent again without waiting for the host -/
  | resendAnytime
  /-- the next turn earlier than the earliest deadline -/
  | wakeEarly
  /-- a line answered while output is untaken -/
  | answerWhileBusy
  /-- lines after a QUIT answered -/
  | quitTail
  deriving DecidableEq, Repr

def names : List (String × Mutant) :=
  [("line-renewed", .lineRenewed), ("no-line-deadline", .noLineDeadline),
   ("line-while-busy", .lineWhileBusy), ("idle-not-renewed", .idleNotRenewed),
   ("zero-take-counts", .zeroTakeCounts), ("blank-counts", .blankCounts),
   ("first-not-cleared", .firstNotCleared),
   ("read-not-resumed", .readNotResumed), ("no-greeting", .noGreeting),
   ("stale-applied", .staleApplied), ("end-ignored", .endIgnored),
   ("resend-anytime", .resendAnytime), ("wake-early", .wakeEarly),
   ("answer-while-busy", .answerWhileBusy), ("quit-tail", .quitTail)]

def freshM (m : Mutant) (i : Identity) (gen now : Nat) : Conn :=
  { Conn.fresh i gen now with out := if m = .noGreeting then [] else greeting i }

def liveM (m : Mutant) (t : Table) (idx gen : Nat) : Option Conn :=
  match t[idx]? with
  | some (some c) => if c.gen = gen || m = .staleApplied then some c else none
  | _ => none

def applyEventM (m : Mutant) (i : Identity) (now : Nat) (t : Table) : Event → Except Breach Table
  | .opened idx gen => do
    checkIndex idx
    match t[idx]? with
    | some (some _) => throw .reopened
    | _ => return t.set idx (some (freshM m i gen now))
  | .received idx gen data => do
    checkIndex idx
    if chunk < data.length then throw .tooLong
    match liveM m t idx gen with
    | some c =>
      if c.asked then
        let due := if m = .lineRenewed then 0 else c.lineDue
        return t.set idx (some { c with held := data, lineDue := due })
      else throw .unasked
    | none => return t
  | .writable idx gen => do
    checkIndex idx
    match liveM m t idx gen with
    | some c => return t.set idx (some { c with blocked := false })
    | none => return t
  | .inputEnded idx gen => do
    checkIndex idx
    match liveM m t idx gen with
    | some c =>
      if c.asked then
        return if m = .endIgnored then t
          else t.set idx (some { c with phase := .ending, lineDue := 0 })
      else throw .unasked
    | none => return t
  | .closed idx gen => do
    checkIndex idx
    match liveM m t idx gen with
    | some _ => return t.set idx none
    | none => return t

def wantsM (m : Mutant) (c : Conn) : Bool := c.wants && !(m = .readNotResumed && c.first == 0)

def waitLineM (m : Mutant) (now : Nat) (c : Conn) : Conn :=
  if (c.out.isEmpty || m = .lineWhileBusy) && c.phase == .open_ && c.line != .fresh &&
      m != .noLineDeadline then
    if c.lineDue == 0 then { c with lineDue := now + lineTime } else c
  else { c with lineDue := 0 }

def serveM (m : Mutant) (i : Identity) (now : Nat) : Nat → Conn → Conn
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
        | .ignore =>
          serveM m i now fuel
            (if m = .blankCounts then { c1 with first := 0, idle := now + inactivity } else c1)
        | r =>
          if !c.out.isEmpty && m != .answerWhileBusy then c
          else
            let first := if m = .firstNotCleared then c1.first else 0
            let c2 := { c1 with out := text i r, first := first, idle := now + inactivity }
            if r = .quit && m != .quitTail then { c2 with phase := .quitting, held := [] }
            else serveM m i now fuel c2

def emitM (m : Mutant) (idx : Nat) (c : Conn) : Option Conn × Option Action :=
  if !c.out.isEmpty then
    if c.blocked && m != .resendAnytime then (some c, none)
    else (some { c with reading := wantsM m c }, some (.send idx c.gen c.out (wantsM m c)))
  else if c.phase = .quitting || (c.phase = .ending && c.held.isEmpty) then
    (none, some (.closeGracefully idx c.gen))
  else (some c, none)

def actM (m : Mutant) (i : Identity) (now idx : Nat) (c : Conn) : Option Conn × Option Action :=
  if c.due now then (none, some (.closeNow idx c.gen))
  else
    let r := emitM m idx
      (if (c.out.isEmpty || m = .answerWhileBusy) && c.phase != .quitting then
        serveM m i now (c.held.length + 1) c else c)
    (r.1.map (waitLineM m now), r.2)

def turnM (m : Mutant) (i : Identity) (s : Server) (now : Nat) (events : List Event) :
    Except Breach (Server × List Action) := do
  if batch < events.length then throw .tooManyEvents
  if now < s.clock || clockLimit ≤ now then throw .badClock
  let t ← events.foldlM (applyEventM m i now) s.table
  let results := (List.range conns).map fun idx =>
    match t[idx]? with
    | some (some c) => actM m i now idx c
    | _ => (none, none)
  return ({ table := results.map (·.1), clock := now }, results.filterMap (·.2))

def settleTableM (m : Mutant) (now : Nat) (t : Table) :
    List Action → List Nat → Except Breach Table
  | [], [] => pure t
  | .send idx gen data _ :: rest, n :: ns => do
    if data.length < n then throw .overTaken
    let t := match liveM m t idx gen with
      | some c =>
        let idle := if m = .zeroTakeCounts then now + inactivity
          else if n = 0 || m = .idleNotRenewed then c.idle else now + inactivity
        t.set idx (some (waitLineM m now
          { c with out := c.out.drop n, idle := idle, blocked := decide (n < data.length) }))
      | none => t
    settleTableM m now t rest ns
  | .send .. :: _, [] => throw .overTaken
  | _ :: rest, ns => settleTableM m now t rest ns
  | [], _ :: _ => throw .overTaken

def settleM (m : Mutant) (s : Server) (actions : List Action) (taken : List Nat) :
    Except Breach Server := do
  return { s with table := ← settleTableM m s.clock s.table actions taken }

def deadlineM (m : Mutant) (s : Server) : Nat :=
  let d := deadline s
  if m = .wakeEarly && s.clock + 1 < d then d - 1 else d

/-! ## With no rule broken, the specification -/

theorem freshM_none : freshM .none = Conn.fresh := by
  funext i gen now
  rfl

theorem liveM_none : liveM .none = Table.live := by
  funext t idx gen
  cases h : t[idx]? with
  | none => simp [liveM, Table.live, h]
  | some o => cases o <;> simp [liveM, Table.live, h]

theorem waitLineM_none : waitLineM .none = Conn.waitLine := by
  funext now c
  simp [waitLineM, Conn.waitLine]

theorem wantsM_none : wantsM .none = Conn.wants := by
  funext c
  simp [wantsM]

theorem serveM_none (i : Identity) (now : Nat) : serveM .none i now = serve i now := by
  funext fuel c
  induction fuel generalizing c with
  | zero => rfl
  | succ fuel ih =>
    have h1 : (Mutant.none != Mutant.answerWhileBusy) = true := rfl
    have h2 : (Mutant.none != Mutant.quitTail) = true := rfl
    simp only [serveM, serve, ih, reduceCtorEq, if_false, h1, h2, Bool.and_true,
      decide_eq_true_eq]
    rfl

theorem emitM_none : emitM .none = emit := by
  funext idx c
  simp [emitM, emit, wantsM_none]

theorem applyEventM_none : applyEventM .none = applyEvent := by
  funext i now t e
  cases e <;> simp only [applyEventM, applyEvent, liveM_none, freshM_none, reduceCtorEq,
    if_false] <;> rfl

theorem actM_none : actM .none = act := by
  funext i now idx c
  simp [actM, act, emitM_none, serveM_none, waitLineM_none]

theorem turnM_none : turnM .none = turn := by
  funext i s now evs
  simp only [turnM, turn, applyEventM_none, actM_none]
  rfl

theorem settleTableM_none (now : Nat) : settleTableM .none now = settleTable now := by
  funext t acts ns
  induction acts generalizing t ns with
  | nil => cases ns <;> rfl
  | cons a rest ih =>
    cases a <;> cases ns <;>
      simp only [settleTableM, settleTable, ih, liveM_none, waitLineM_none, reduceCtorEq,
        ↓reduceIte, decide_false, Bool.or_false, decide_eq_true_eq] <;> rfl

theorem settleM_none : settleM .none = settle := by
  funext s acts ns
  simp [settleM, settle, settleTableM_none]

theorem deadlineM_none : deadlineM .none = deadline := by
  funext s
  simp [deadlineM]

end DN.News.SessionMutant
