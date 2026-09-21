-- SPDX-License-Identifier: AGPL-3.0-or-later

/-!
# DN.Dataplane.Io.Wake

Source provenance is in docs/provenance.json; assurance boundaries are in
docs/assurance.md.

Two races live here. The first is the Dekker handshake between a producer
posting a wakeup and a reactor deciding to sleep (`wake_no_lost`). The second is
the drain itself: a reactor that reads its queue before clearing the wakeup flag
leaves a window where the producer skips the doorbell and the message is never
looked at (`clear_then_read_no_lost`, `read_then_clear_loses`). Both are proven
over every program-order-respecting interleaving of the two threads, under
sequentially consistent ordering; reordering inside a thread is outside the
model.
-/

namespace DN.Dataplane.Io.Wake

/-- The shared wakeup cell of a completion reactor. `pending` is the producer's
Dekker flag (also the coalescing flag), `mightBlock` the reactor's, and
`syscalls` counts doorbell writes (the `eventfd`/`kevent` syscall we are trying
to avoid). -/
structure Cq where
  pending    : Bool
  mightBlock : Bool
  syscalls   : Nat
deriving DecidableEq, Repr

/-- Producer side: post a cross-thread wakeup.

`owner` is the value an atomic `swap(pending, true)` returns negated — it is
`true` exactly when *this* call performed the false→true transition, i.e. it is
the coalescing leader. The doorbell (`syscalls + 1`) fires only when this call
owns the transition **and** the reactor announced it might block. -/
def notify (c : Cq) : Cq :=
  let owner := !c.pending
  { pending    := true
    mightBlock := c.mightBlock
    syscalls   := if owner && c.mightBlock then c.syscalls + 1 else c.syscalls }

/-- Reactor side: after waking / draining, clear the pending flag. -/
def drain (c : Cq) : Cq := { c with pending := false }

/-! ## Coalescing and the busy reactor (sequential facts) -/

/-- **`wake_idempotent`** — a second wakeup racing the first coalesces into it:
`notify` is idempotent, so no second doorbell is issued. This is the coalescing
guarantee (at most one doorbell per batch of concurrent wakeups). -/
theorem wake_idempotent (c : Cq) : notify (notify c) = notify c := by
  rcases c with ⟨p, mb, s⟩
  cases p <;> cases mb <;> rfl

/-- Corollary in the currency that matters: the coalesced second wakeup adds no
syscall. -/
theorem wake_coalesce_no_extra_syscall (c : Cq) :
    (notify (notify c)).syscalls = (notify c).syscalls := by
  rw [wake_idempotent]

/-- **`wake_busy_zero_syscall`** — a wakeup posted to a *busy* reactor (one that
has not announced it might block: `mightBlock = false`) issues no syscall. -/
theorem wake_busy_zero_syscall (c : Cq) (h : c.mightBlock = false) :
    (notify c).syscalls = c.syscalls := by
  simp [notify, h]

/-! ## The Dekker no-lost-wakeup theorem (all interleavings)

We model the concurrent execution as an interleaving of the four load-bearing
atomic memory operations under sequentially-consistent ordering (the total
modification order production obtains from `SeqCst`). The *demonic* freedom —
which thread's operation the hardware schedules next — is exactly the set of
program-order-respecting interleavings, which we quantify over with an
interleaving relation. -/

/-- The four atomic memory operations of the protocol.
* `PW` — producer writes `pending := true`  (`swap`, records `owner`);
* `PR` — producer reads `mightBlock`;
* `RW` — reactor writes `mightBlock := true`;
* `RR` — reactor reads `pending`. -/
inductive Ev | PW | PR | RW | RR
deriving DecidableEq, Repr

/-- The observable state threaded through an execution: the two flags, plus what
each side *observed* (`owner` = producer's swap result; `prSawMB` = producer's
read of `mightBlock`; `rrSawPending` = reactor's read of `pending`). -/
structure Sim where
  pending      : Bool
  mightBlock   : Bool
  owner        : Bool
  prSawMB      : Bool
  rrSawPending : Bool
deriving Repr

/-- Both flags down, nothing observed. -/
def Sim.init : Sim := ⟨false, false, false, false, false⟩

/-- Sequentially-consistent single-step of one atomic operation. -/
def step (s : Sim) : Ev → Sim
  | .PW => { s with owner := !s.pending, pending := true }
  | .PR => { s with prSawMB := s.mightBlock }
  | .RW => { s with mightBlock := true }
  | .RR => { s with rrSawPending := s.pending }

/-- Run a whole schedule from the initial state. -/
def runSchedule (sch : List Ev) : Sim := sch.foldl step Sim.init

/-- The wakeup is *delivered* on a run iff the producer fired the doorbell
(it owned the transition and saw the reactor about to block) **or** the reactor
cancelled its block (it saw the pending flag). -/
def delivered (s : Sim) : Bool :=
  (s.owner && s.prSawMB) || s.rrSawPending

/-- Program-order-respecting interleaving of two per-thread operation sequences:
`IL prod react sched` holds when `sched` merges `prod` and `react` keeping each
thread's operations in order. This is the exact set of SC schedules the hardware
may pick. -/
inductive IL : List Ev → List Ev → List Ev → Prop
  | nil : IL [] [] []
  | left  {a as bs cs} : IL as bs cs → IL (a :: as) bs (a :: cs)
  | right {b as bs cs} : IL as bs cs → IL as (b :: bs) (b :: cs)

/-- **`wake_no_lost`** — the headline. For *every* interleaving of the producer
program `[PW, PR]` and the reactor program `[RW, RR]` (announce-then-check, the
Dekker order), the wakeup is delivered. No wakeup posted concurrently with the
reactor's decision to sleep is ever lost. -/
theorem wake_no_lost {s : List Ev}
    (h : IL [Ev.PW, Ev.PR] [Ev.RW, Ev.RR] s) :
    delivered (runSchedule s) = true := by
  cases h with
  | left h => cases h with
    | left h => cases h with
      | right h => cases h with
        | right h => cases h with
          | nil => decide
    | right h => cases h with
      | left h => cases h with
        | right h => cases h with
          | nil => decide
      | right h => cases h with
        | left h => cases h with
          | nil => decide
  | right h => cases h with
    | left h => cases h with
      | left h => cases h with
        | right h => cases h with
          | nil => decide
      | right h => cases h with
        | left h => cases h with
          | nil => decide
    | right h => cases h with
      | left h => cases h with
        | left h => cases h with
          | nil => decide

/-! ## Non-vacuity: witnesses and contract-tight mutants -/

/-- The hypothesis of `wake_no_lost` is inhabited — there really are such
interleavings (this exhibits the producer-then-reactor race). -/
theorem no_lost_inhabited :
    IL [Ev.PW, Ev.PR] [Ev.RW, Ev.RR] [Ev.PW, Ev.RW, Ev.PR, Ev.RR] :=
  IL.left (IL.right (IL.left (IL.right IL.nil)))

/-- Mutant: a reactor that **checks pending before announcing might_block**
(program `[RR, RW]` — the wrong order) admits a valid interleaving on which the
wakeup is *lost* (`delivered = false`). This is precisely why the Dekker order
(announce, *then* check) is load-bearing: swap the two reactor operations and
`wake_no_lost` becomes false. -/
theorem dekker_order_necessary :
    IL [Ev.PW, Ev.PR] [Ev.RR, Ev.RW] [Ev.RR, Ev.PW, Ev.PR, Ev.RW]
      ∧ delivered (runSchedule [Ev.RR, Ev.PW, Ev.PR, Ev.RW]) = false :=
  ⟨IL.right (IL.left (IL.left (IL.right IL.nil))), by decide⟩

/-- A doorbell that fires unconditionally (dropping both guards). -/
def notifyBroken (c : Cq) : Cq := { c with pending := true, syscalls := c.syscalls + 1 }

/-- Mutant: without the coalescing guard, `notify` is **not** idempotent — a
second wakeup issues a second doorbell. This shows the `owner` guard in `notify`
is what buys coalescing. -/
theorem coalescing_guard_necessary :
    ∃ c : Cq, (notifyBroken (notifyBroken c)).syscalls ≠ (notifyBroken c).syscalls :=
  ⟨⟨false, false, 0⟩, by decide⟩

/-- Mutant: without the `mightBlock` guard, a wakeup to a *busy* reactor incurs a
syscall — the very cost `wake_busy_zero_syscall` eliminates. -/
theorem busy_guard_necessary :
    ∃ c : Cq, c.mightBlock = false ∧ (notifyBroken c).syscalls ≠ c.syscalls :=
  ⟨⟨false, false, 0⟩, by decide, by decide⟩

/-! ## Executable sanity checks (the theorems, exercised on real inputs) -/

-- Busy reactor: two wakeups, reactor never announced a block → zero syscalls.
private def busyRun : Nat :=
  let c : Cq := ⟨false, false, 0⟩
  (notify (notify c)).syscalls
def regression_231 : Bool := decide (busyRun == 0
  )

-- Reactor about to block: first wakeup rings once, second coalesces → one syscall.
private def blockingRun : Nat :=
  let c : Cq := ⟨false, true, 0⟩          -- reactor announced mightBlock
  (notify (notify c)).syscalls
def regression_237 : Bool := decide (blockingRun == 1
  )

-- Every interleaving of the correct (Dekker) protocol delivers the wakeup.
def regression_240 : Bool := decide (delivered (runSchedule [Ev.PW, Ev.PR, Ev.RW, Ev.RR]) == true
  )
def regression_241 : Bool := decide (delivered (runSchedule [Ev.PW, Ev.RW, Ev.PR, Ev.RR]) == true
  )
def regression_242 : Bool := decide (delivered (runSchedule [Ev.PW, Ev.RW, Ev.RR, Ev.PR]) == true
  )
def regression_243 : Bool := decide (delivered (runSchedule [Ev.RW, Ev.PW, Ev.PR, Ev.RR]) == true
  )
def regression_244 : Bool := decide (delivered (runSchedule [Ev.RW, Ev.PW, Ev.RR, Ev.PR]) == true
  )
def regression_245 : Bool := decide (delivered (runSchedule [Ev.RW, Ev.RR, Ev.PW, Ev.PR]) == true
  )

-- The wrong (check-before-announce) reactor order loses this one.
def regression_248 : Bool := decide (delivered (runSchedule [Ev.RR, Ev.PW, Ev.PR, Ev.RW]) == false
  )

/-! ## The second race: the queue and the flag

The flags above answer "may the reactor sleep?". They do not answer "did the
reactor see the message?", because the model has no queue and never clears
`pending`. The real loss lives in the clearing: a reactor that reads its queue
*before* clearing the flag leaves a window in which a producer sees the flag
still raised, skips the doorbell, and enqueues a message nobody will look at.
The events below add the queue and split the drain into its two writes, so both
orders are expressible and one of them is refuted. -/

/-- The operations of one round once the message queue is part of the state.
`Enq` publishes a message; `PW` is the producer's `swap` on the wakeup flag; `PR`
its read of `mightBlock`; `RC` the reactor clearing the flag; `RD` its read of
the queue; `RW` its announcement that it might block; `RR` its last look at the
flag. -/
inductive QEv | Enq | PW | PR | RC | RD | RW | RR
deriving DecidableEq, Repr

/-- What a run of one round observes: how many messages were published and how
many the reactor took, the two flags, and what each side saw. -/
structure QSim where
  /-- Messages the producer has published. -/
  queue        : Nat
  /-- Messages the reactor has taken. -/
  seen         : Nat
  /-- The wakeup flag. -/
  pending      : Bool
  /-- The reactor's announcement that it may block. -/
  mightBlock   : Bool
  /-- The producer's `swap` result: it performed the false→true transition. -/
  owner        : Bool
  /-- What the producer read from `mightBlock`. -/
  prSawMB      : Bool
  /-- What the reactor read from `pending`. -/
  rrSawPending : Bool
deriving Repr

def QSim.init : QSim := ⟨0, 0, false, false, false, false, false⟩

/-- One atomic operation, sequentially consistent. -/
def qstep (s : QSim) : QEv → QSim
  | .Enq => { s with queue := s.queue + 1 }
  | .PW => { s with owner := !s.pending, pending := true }
  | .PR => { s with prSawMB := s.mightBlock }
  | .RC => { s with pending := false }
  | .RD => { s with seen := s.queue }
  | .RW => { s with mightBlock := true }
  | .RR => { s with rrSawPending := s.pending }

/-- Run a whole schedule from the empty state. -/
def qrun (sch : List QEv) : QSim := sch.foldl qstep QSim.init

/-- The message is not dropped silently: either the reactor already took
everything published, or it will not go to sleep without looking again — the
producer rang the doorbell, or the reactor saw the flag on its last read. It
does **not** say the reactor has read the message: in most schedules the second
disjunct is what holds. -/
def noLost (s : QSim) : Bool :=
  (s.seen == s.queue) || ((s.owner && s.prSawMB) || s.rrSawPending)

/-- Program-order-respecting interleaving, as for `IL` above. -/
inductive QIL : List QEv → List QEv → List QEv → Prop
  | nil : QIL [] [] []
  | left  {a as bs cs} : QIL as bs cs → QIL (a :: as) bs (a :: cs)
  | right {b as bs cs} : QIL as bs cs → QIL as (b :: bs) (b :: cs)

/-- Merges of `a :: as` with the reactor's remaining events, recursing on the
latter. Split out so that both recursions are structural and the enumeration
reduces in the kernel. -/
def mergesAux (f : List QEv → List (List QEv)) (a : QEv) (as : List QEv) :
    List QEv → List (List QEv)
  | [] => [a :: as]
  | b :: bs => (f (b :: bs)).map (a :: ·) ++ (mergesAux f a as bs).map (b :: ·)

/-- Every program-order-respecting merge of two schedules. -/
def merges : List QEv → List QEv → List (List QEv)
  | [], bs => [bs]
  | a :: as, bs => mergesAux (merges as) a as bs

theorem merges_nil_right (as : List QEv) : merges as [] = [as] := by
  cases as <;> rfl

theorem merges_cons_cons (a b : QEv) (as bs : List QEv) :
    merges (a :: as) (b :: bs)
      = (merges as (b :: bs)).map (a :: ·) ++ (merges (a :: as) bs).map (b :: ·) := rfl

theorem mem_merges_of_QIL : ∀ {as bs sch}, QIL as bs sch → sch ∈ merges as bs := by
  intro as bs sch h
  induction h with
  | nil => simp [merges]
  | @left a as bs cs _ ih =>
      cases bs with
      | nil =>
          rw [merges_nil_right] at ih ⊢
          simp at ih
          simp [ih]
      | cons b bs =>
          rw [merges_cons_cons]
          exact List.mem_append_left _ (List.mem_map_of_mem ih)
  | @right b as bs cs _ ih =>
      cases as with
      | nil =>
          simp [merges] at ih ⊢
          simp [ih]
      | cons a as =>
          rw [merges_cons_cons]
          exact List.mem_append_right _ (List.mem_map_of_mem ih)

/-- All 35 schedules of the correct round satisfy `noLost`. -/
theorem merges_all_no_lost :
    (merges [.Enq, .PW, .PR] [.RC, .RD, .RW, .RR]).all (fun sch => noLost (qrun sch))
      = true := by decide

/-- Clear the flag, then read the queue: on every schedule of one producer round
against one reactor round, the message is not dropped silently. -/
theorem clear_then_read_no_lost {sch : List QEv}
    (h : QIL [.Enq, .PW, .PR] [.RC, .RD, .RW, .RR] sch) : noLost (qrun sch) = true :=
  List.all_eq_true.mp merges_all_no_lost sch (mem_merges_of_QIL h)

/-- Read the queue, then clear the flag: two of the 35 schedules drop the
message — the reactor never took it and will sleep without looking again. -/
theorem read_then_clear_loses :
    QIL [.Enq, .PW, .PR] [.RD, .RC, .RW, .RR] [.RD, .Enq, .PW, .PR, .RC, .RW, .RR] ∧
      noLost (qrun [.RD, .Enq, .PW, .PR, .RC, .RW, .RR]) = false :=
  ⟨.right (.left (.left (.left (.right (.right (.right .nil)))))), by decide⟩

-- Every schedule of the correct order keeps the message; the wrong order has a
-- schedule that drops it.
def regression_249 : Bool := decide ((merges [QEv.Enq, QEv.PW, QEv.PR]
    [QEv.RC, QEv.RD, QEv.RW, QEv.RR]).length == 35
  )
def regression_250 : Bool := decide ((merges [QEv.Enq, QEv.PW, QEv.PR]
    [QEv.RC, QEv.RD, QEv.RW, QEv.RR]).all (fun sch => noLost (qrun sch)) == true
  )
def regression_251 : Bool := decide (noLost (qrun [QEv.RD, QEv.Enq, QEv.PW, QEv.PR,
    QEv.RC, QEv.RW, QEv.RR]) == false
  )

end DN.Dataplane.Io.Wake
