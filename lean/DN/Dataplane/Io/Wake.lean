-- SPDX-License-Identifier: AGPL-3.0-or-later

/-!
# DN.Dataplane.Io.Wake

Source provenance is in docs/provenance.json; assurance boundaries are in
docs/assurance.md.
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

end DN.Dataplane.Io.Wake
