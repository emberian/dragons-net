-- SPDX-License-Identifier: AGPL-3.0-or-later
import DN.News.SessionSpec

/-!
# DN.News.SessionMutant

The session of `DN.News.SessionSpec` with one of its rules broken, for the lane that holds the
session against an independent reference to show that it sees each (`scripts/session_check.py`).
A rule of the store's side is broken by its field of `DN.News.PostSpec.Rules` (`rulesOf`). With no
rule broken it is the specification (`turnM_none`, `settleM_none`, `deadlineM_none`).
-/

namespace DN.News.SessionMutant

open DN.News.FrameSpec DN.News.Framer DN.News.CommandSpec DN.News.SessionSpec
open DN.News.PostSpec (Store Slot Job Done Rules)

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
  /-- an article's octets start its deadline again -/
  | articleRenewed
  /-- no deadline for an article -/
  | noArticleDeadline
  /-- the deadlines run while a POST waits for a slot -/
  | waitDeadlines
  /-- a connection that may not post greeted with 200 -/
  | greetAll
  /-- a POST answered 340 once the store has stopped accepting -/
  | postAfterStop
  /-- a POST of a connection greeted with 201 answered 340 -/
  | postUnpermitted
  /-- POST listed among the capabilities once the store has stopped accepting -/
  | capabilitiesStale
  /-- the host never told to read, or not, with nothing to send -/
  | noReadControl
  /-- a fifth POST at once -/
  | fifthPost
  /-- an article one octet longer -/
  | articleLonger
  /-- no dot put before a line of the file that starts with one -/
  | unstuffed
  /-- a Message-ID another slot has reserved taken -/
  | reservedTaken
  /-- the file closed without a sync -/
  | noFileSync
  /-- the directory not synced after the rename -/
  | noDirSync
  /-- the journal not synced after the append -/
  | noJournalSync
  /-- two syncs of the directory in flight -/
  | dirSyncsOverlap
  /-- two appends of the journal in flight -/
  | appendsOverlap
  /-- an article's number not above the group's highest -/
  | numbersNotAbove
  /-- a failed sync does not stop the store accepting -/
  | syncFailureIgnored
  /-- a failed append of the journal answered 441 -/
  | unknownAnswered
  /-- a refused article's names left -/
  | namesLeft
  /-- a block that ends before the empty line not refused -/
  | unseparated
  /-- one article more than the store holds -/
  | capacityOver
  /-- a refused article's Message-ID still reserved -/
  | refusedReserves
  /-- the articles in flight not refused once the store stops -/
  | stopSparesFlight
  /-- a commit whose sync completes after the store stopped answered 240 -/
  | commitAfterStop
  /-- a POST that waits not answered 403 once the store stops -/
  | waitThroughStop
  /-- a free slot given to the waiting POST of the lowest index, not the first that came -/
  | lowestFirst
  deriving DecidableEq, Repr

def names : List (String × Mutant) :=
  [("line-renewed", .lineRenewed), ("no-line-deadline", .noLineDeadline),
   ("line-while-busy", .lineWhileBusy), ("idle-not-renewed", .idleNotRenewed),
   ("zero-take-counts", .zeroTakeCounts), ("blank-counts", .blankCounts),
   ("first-not-cleared", .firstNotCleared),
   ("read-not-resumed", .readNotResumed), ("no-greeting", .noGreeting),
   ("stale-applied", .staleApplied), ("end-ignored", .endIgnored),
   ("resend-anytime", .resendAnytime), ("wake-early", .wakeEarly),
   ("answer-while-busy", .answerWhileBusy), ("quit-tail", .quitTail),
   ("article-renewed", .articleRenewed), ("no-article-deadline", .noArticleDeadline),
   ("wait-deadlines", .waitDeadlines), ("greet-all", .greetAll),
   ("post-after-stop", .postAfterStop), ("post-unpermitted", .postUnpermitted),
   ("capabilities-stale", .capabilitiesStale), ("no-read-control", .noReadControl),
   ("fifth-post", .fifthPost), ("article-longer", .articleLonger), ("unstuffed", .unstuffed),
   ("reserved-taken", .reservedTaken),
   ("no-file-sync", .noFileSync), ("no-dir-sync", .noDirSync),
   ("no-journal-sync", .noJournalSync), ("dir-syncs-overlap", .dirSyncsOverlap),
   ("appends-overlap", .appendsOverlap), ("numbers-not-above", .numbersNotAbove),
   ("sync-failure-ignored", .syncFailureIgnored), ("unknown-answered", .unknownAnswered),
   ("names-left", .namesLeft), ("unseparated", .unseparated), ("capacity-over", .capacityOver),
   ("refused-reserves", .refusedReserves), ("stop-spares-flight", .stopSparesFlight),
   ("commit-after-stop", .commitAfterStop), ("wait-through-stop", .waitThroughStop),
   ("lowest-first", .lowestFirst)]

/-- The store's rules with the mutant's broken. -/
def rulesOf : Mutant → Rules
  | .fifthPost => { posts := 5 }
  | .articleLonger => { articleMax := 1000001 }
  | .unstuffed => { stuffs := false }
  | .reservedTaken => { reserves := false }
  | .noFileSync => { syncsFile := false }
  | .noDirSync => { syncsDir := false }
  | .noJournalSync => { syncsJournal := false }
  | .dirSyncsOverlap => { oneDirSync := false }
  | .appendsOverlap => { oneAppend := false }
  | .numbersNotAbove => { numbersAbove := false }
  | .syncFailureIgnored => { stops := false }
  | .unknownAnswered => { unknown := false }
  | .namesLeft => { cleans := false }
  | .unseparated => { separates := false }
  | .capacityOver => { capacity := Recovery.capacity + 1 }
  | .refusedReserves => { releases := false }
  | .stopSparesFlight => { refusesInFlight := false }
  | .commitAfterStop => { distrusts := false }
  | _ => {}

def freshM (m : Mutant) (i : Identity) (greeted : Bool) (number gen now : Nat) : Conn :=
  { Conn.fresh i greeted number gen now with
    out := if m = .noGreeting then [] else (Conn.fresh i greeted number gen now).out }

def liveM (m : Mutant) (t : Table) (idx gen : Nat) : Option Conn :=
  match t[idx]? with
  | some (some c) => if c.gen = gen || m = .staleApplied then some c else none
  | _ => none

def applyEventM (m : Mutant) (i : Identity) (now : Nat) (s : Server) :
    Event → Except Breach Server
  | .opened idx gen mayPost => do
    checkIndex idx
    match s.table[idx]? with
    | some (some _) => throw .reopened
    | _ =>
      let c := freshM m i (greets s.store (mayPost || m = .greetAll)) (s.opened + 1) gen now
      return { s with table := s.table.set idx (some c), opened := s.opened + 1 }
  | .received idx gen data => do
    checkIndex idx
    if chunk < data.length then throw .tooLong
    match liveM m s.table idx gen with
    | some c =>
      if c.asked then
        let due := if m = .lineRenewed then 0 else c.lineDue
        return { s with table := s.table.set idx (some { c with held := data, lineDue := due }) }
      else throw .unasked
    | none => return s
  | .writable idx gen => do
    checkIndex idx
    match liveM m s.table idx gen with
    | some c => return { s with table := s.table.set idx (some { c with blocked := false }) }
    | none => return s
  | .inputEnded idx gen => do
    checkIndex idx
    match liveM m s.table idx gen with
    | some c =>
      if c.asked then
        if m = .endIgnored then return s
        else
          let c' := { c with phase := .ending, lineDue := 0, post := none, articleDue := 0 }
          return { s with
            table := s.table.set idx (some c'),
            store := s.store.map (Store.abandon idx gen) }
      else throw .unasked
    | none => return s
  | .closed idx gen => do
    checkIndex idx
    match liveM m s.table idx gen with
    | some _ =>
      return { s with table := s.table.set idx none, store := s.store.map (Store.abandon idx gen) }
    | none => return s

def wantsWithM (m : Mutant) (st : Option Store) (c : Conn) : Bool :=
  c.wantsWith st && !(m = .readNotResumed && c.first == 0)

def waitLineM (m : Mutant) (now : Nat) (c : Conn) : Conn :=
  if (c.out.isEmpty || m = .lineWhileBusy) && c.phase == .open_ && c.line != .fresh &&
      m != .noLineDeadline then
    if c.lineDue == 0 then { c with lineDue := now + lineTime } else c
  else { c with lineDue := 0 }

def resolveM (m : Mutant) (p : Posting) (c : Conn) : Reply → Reply
  | .capabilities =>
    if c.greeted && (p.accepting || m = .capabilitiesStale) then .capabilitiesPost
    else .capabilities
  | .help => if p.offered then .helpPost else .help
  | .post =>
    if !c.greeted && !(m = .postUnpermitted && p.offered) then .notPermitted
    else if !p.accepting && m != .postAfterStop then .unavailable else .post
  | r => r

def serveM (m : Mutant) (i : Identity) (p : Posting) (now : Nat) : Nat → Conn → Conn
  | 0, c => c
  | fuel + 1, c =>
    if c.held.isEmpty then c
    else
      let (k, line', v) := frameOnce lineLimit c.line c.held
      let c1 := { c with line := line', held := c.held.drop k }
      match v with
      | none => c1
      | some l =>
        match resolveM m p c (replyIn p.offered l) with
        | .ignore =>
          serveM m i p now fuel
            (if m = .blankCounts then { c1 with first := 0, idle := now + inactivity } else c1)
        | r =>
          if !c.out.isEmpty && m != .answerWhileBusy then c
          else if r = .post then
            if m = .waitDeadlines then { c1 with waiting := true }
            else { c1 with waiting := true, first := 0, idle := 0 }
          else
            let first := if m = .firstNotCleared then c1.first else 0
            let c2 := { c1 with out := text i r, first := first, idle := now + inactivity }
            if r = .quit && m != .quitTail then { c2 with phase := .quitting, held := [] }
            else serveM m i p now fuel c2

/-- `progress`, an article's octets taken renewing its deadline with `articleRenewed`. -/
def progressM (m : Mutant) (i : Identity) (now wall : Nat) (st : Option Store) (c : Conn) :
    Conn × Option Store × Bool :=
  let g := progress i now wall st c
  if m = .articleRenewed && g.1.held.length < c.held.length && g.1.articleDue != 0 then
    ({ g.1 with articleDue := now + articleTime }, g.2)
  else g

/-- `claim`, with the store taken as accepting by `postAfterStop`; a waiting POST kept waiting
once the store stops by `waitThroughStop`; the connection first among those waiting by
`lowestFirst`; and no deadline given the article by `noArticleDeadline`. -/
def claimM (m : Mutant) (i : Identity) (now idx : Nat) (st : Option Store) (c : Conn) :
    Conn × Option Store :=
  let first (st : Store) := { st with waiters := (idx, c.gen) :: st.waiters.erase (idx, c.gen) }
  let k := if m = .postAfterStop then
      let k := claim i now idx (st.map ({ · with accepting := true })) c
      (k.1, k.2.map ({ · with accepting := st.any (·.accepting) }))
    else if m = .waitThroughStop && c.waiting && st.any (!·.accepting) then (c, st)
    else if m = .lowestFirst then claim i now idx (st.map first) c
    else claim i now idx st c
  if m = .noArticleDeadline && c.post.isNone && k.1.post.isSome then
    ({ k.1 with articleDue := 0 }, k.2)
  else k

def emitM (m : Mutant) (idx : Nat) (wants : Bool) (c : Conn) : Option Conn × Option Action :=
  if !c.out.isEmpty then
    if c.blocked && m != .resendAnytime then (some c, none)
    else (some { c with reading := wants }, some (.send idx c.gen c.out wants))
  else if c.phase = .quitting || (c.phase = .ending && c.held.isEmpty) then
    (none, some (.closeGracefully idx c.gen))
  else if c.phase = .open_ && c.reading != wants && m != .noReadControl then
    (some { c with reading := wants }, some (.send idx c.gen [] wants))
  else (some c, none)

def actM (m : Mutant) (i : Identity) (now wall idx : Nat) (st : Option Store) (c : Conn) :
    Option Conn × Option Action × Option Store :=
  if c.due now then (none, some (.closeNow idx c.gen), st.map (Store.abandon idx c.gen))
  else
    let g := progressM m i now wall st c
    if g.2.2 then (none, some (.closeNow idx c.gen), g.2.1)
    else
      let p : Posting := ⟨g.2.1.isSome, g.2.1.any (·.accepting)⟩
      let c1 := if (g.1.out.isEmpty || m = .answerWhileBusy) && g.1.phase != .quitting &&
          g.1.post.isNone && !g.1.waiting
        then serveM m i p now (g.1.held.length + 1) g.1 else g.1
      let st1 := if c1.waiting && !g.1.waiting then
          g.2.1.map fun st => { st with waiters := st.waiters ++ [(idx, c.gen)] }
        else g.2.1
      let k := claimM m i now idx st1 c1
      let r := emitM m idx (wantsWithM m k.2 k.1) k.1
      (r.1.map (waitLineM m now), r.2, k.2)

def actFromM (m : Mutant) (i : Identity) (now wall : Nat) (t : Table) :
    List Nat → Option Store → List (Option Conn × Option Action) × Option Store
  | [], st => ([], st)
  | idx :: rest, st =>
    match t[idx]? with
    | some (some c) =>
      let x := actM m i now wall idx st c
      let r := actFromM m i now wall t rest x.2.2
      ((x.1, x.2.1) :: r.1, r.2)
    | _ =>
      let r := actFromM m i now wall t rest st
      ((none, none) :: r.1, r.2)

def turnM (m : Mutant) (i : Identity) (s : Server) (now wall : Nat) (events : List Event)
    (dones : List Done) : Except Breach (Server × List Action × List Job) := do
  if batch < events.length then throw .tooManyEvents
  if now < s.clock || clockLimit ≤ now || wallLimit ≤ wall then throw .badClock
  let s ← events.foldlM (applyEventM m i now) s
  let st ← completions s dones
  let r := actFromM m i now wall s.table (List.range conns) st
  let j := jobsOf r.2
  return ({ s with table := r.1.map (·.1), clock := now, store := j.1 }, r.1.filterMap (·.2), j.2)

def settleTableM (m : Mutant) (now : Nat) (t : Table) :
    List Action → List Nat → Except Breach Table
  | [], [] => pure t
  | .send idx gen data _ :: rest, n :: ns => do
    if data.length < n then throw .overTaken
    let t := match liveM m t idx gen with
      | some c =>
        let idle := if m = .zeroTakeCounts then now + inactivity
          else if n = 0 || c.post.isSome || c.waiting || m = .idleNotRenewed then c.idle
          else now + inactivity
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

theorem rulesOf_none : rulesOf .none = {} := rfl

theorem freshM_none : freshM .none = Conn.fresh := by
  funext i g number gen now
  rfl

theorem liveM_none : liveM .none = Table.live := by
  funext t idx gen
  cases h : t[idx]? with
  | none => simp [liveM, Table.live, h]
  | some o => cases o <;> simp [liveM, Table.live, h]

theorem waitLineM_none : waitLineM .none = Conn.waitLine := by
  funext now c
  simp [waitLineM, Conn.waitLine]

theorem wantsWithM_none : wantsWithM .none = Conn.wantsWith := by
  funext st c
  simp [wantsWithM]

theorem resolveM_none : resolveM .none = resolve := by
  funext p c r
  cases r <;> simp [resolveM, resolve]

theorem serveM_none (i : Identity) (p : Posting) (now : Nat) :
    serveM .none i p now = serve i p now := by
  funext fuel c
  induction fuel generalizing c with
  | zero => rfl
  | succ fuel ih =>
    have h1 : (Mutant.none != Mutant.answerWhileBusy) = true := rfl
    have h2 : (Mutant.none != Mutant.quitTail) = true := rfl
    simp only [serveM, serve, ih, resolveM_none, reduceCtorEq, if_false, h1, h2, Bool.and_true,
      decide_eq_true_eq]
    rfl

theorem progressM_none : progressM .none = progress := by
  funext i now wall st c
  simp [progressM]

theorem claimM_none : claimM .none = claim := by
  funext i now idx st c
  simp [claimM]

theorem emitM_none : emitM .none = emit := by
  funext idx w c
  simp [emitM, emit]

theorem applyEventM_none : applyEventM .none = applyEvent := by
  funext i now s e
  cases e <;> simp only [applyEventM, applyEvent, liveM_none, freshM_none, reduceCtorEq,
    if_false, Bool.or_false, decide_false] <;> rfl

theorem actM_none : actM .none = act := by
  funext i now wall idx st c
  simp [actM, act, emitM_none, serveM_none, waitLineM_none, progressM_none, claimM_none,
    wantsWithM_none]

theorem actFromM_none (i : Identity) (now wall : Nat) (t : Table) :
    actFromM .none i now wall t = actFrom i now wall t := by
  funext l st
  induction l generalizing st with
  | nil => rfl
  | cons idx rest ih =>
    simp only [actFromM, actFrom, ih, actM_none]
    rfl

theorem turnM_none : turnM .none = turn := by
  funext i s now wall evs ds
  simp only [turnM, turn, applyEventM_none, actFromM_none]

theorem settleTableM_none (now : Nat) : settleTableM .none now = settleTable now := by
  funext t acts ns
  induction acts generalizing t ns with
  | nil => cases ns <;> rfl
  | cons a rest ih =>
    cases a <;> cases ns <;>
      simp only [settleTableM, settleTable, ih, liveM_none, waitLineM_none, reduceCtorEq,
        ↓reduceIte, decide_false, Bool.or_false] <;> rfl

theorem settleM_none : settleM .none = settle := by
  funext s acts ns
  simp [settleM, settle, settleTableM_none]

theorem deadlineM_none : deadlineM .none = deadline := by
  funext s
  simp [deadlineM]

end DN.News.SessionMutant
