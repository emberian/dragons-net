-- SPDX-License-Identifier: AGPL-3.0-or-later

/-!
# DN.Dataplane.Flow.Shed

Source provenance is in docs/provenance.json; assurance boundaries are in
docs/assurance.md.
-/

namespace DN.Dataplane.Flow

universe u
variable {α : Type u}

/-- The explicit fate of a settled unit. Every way out of the backlog is
one of these — the "declared policy" per edge. -/
inductive Fate where
  /-- Consumed by the handler: fully processed. -/
  | delivered
  /-- Dropped by the declared backlog policy (oldest-drop on overflow, or
  recycle at close). -/
  | shed
  /-- Irrecoverably lost at the buffer-exhaustion edge; the socket was
  closed in the same step. -/
  | killed
  deriving Repr, DecidableEq, Inhabited

/-- Per-socket shed state, over an abstract unit type `α`.

`backlog` and `closed` are the operational state; `settled`, `admitted`,
and `refused` are ghost ledgers for the accounting identity. -/
structure ShedQueue (α : Type u) where
  /-- Backlog capacity (units). -/
  cap : Nat
  /-- FIFO backlog of admitted, not-yet-consumed units. -/
  backlog : List α
  /-- Ghost: every unit that left the backlog, in order, with its fate. -/
  settled : List (α × Fate)
  /-- Ghost: every unit the machine admitted, in order. -/
  admitted : List α
  /-- Ghost: units refused at admission — offered to a closed socket;
  never admitted, never owing a fate. -/
  refused : List α
  /-- The socket has been closed. -/
  closed : Bool

/-- A fresh socket with capacity `cap`. -/
def ShedQueue.init (cap : Nat) : ShedQueue α := ⟨cap, [], [], [], [], false⟩

/-- Result code: the declared policy outcome of each event. -/
inductive ShedResult where
  /-- Unit admitted into the backlog, under cap. -/
  | admitted
  /-- Unit admitted; the backlog was full, so the *oldest* entry was shed
  by policy (recorded). -/
  | admittedDropOldest
  /-- Unit refused at admission: socket closed. -/
  | refused
  /-- The oldest backlogged unit was consumed by the handler. -/
  | consumed
  /-- Nothing to consume. -/
  | idle
  /-- Bufferless completion: unit killed, socket closed. -/
  | killedClosed
  /-- Close acknowledged. -/
  | closedOk
  deriving Repr, DecidableEq, Inhabited

/-- Events driving one socket's shed edges. -/
inductive ShedEv (α : Type u) where
  /-- A completion carrying unit `u` *with* a pool buffer arrives. -/
  | admit (u : α)
  /-- The handler consumes the oldest backlogged unit. -/
  | consume
  /-- A completion carrying unit `u` but *no* buffer arrives: the pool was
  exhausted and the data is lost. -/
  | bufferlessKill (u : α)
  /-- The socket is closed; backlogged buffers are recycled (shed). -/
  | close

/-- One step of the shed machine. -/
def ShedQueue.step (s : ShedQueue α) : ShedEv α → ShedQueue α × ShedResult
  | .admit u =>
    if s.closed then
      ({ s with refused := s.refused ++ [u] }, .refused)
    else if s.backlog.length < s.cap then
      ({ s with backlog := s.backlog ++ [u],
                admitted := s.admitted ++ [u] }, .admitted)
    else
      match s.backlog with
      | [] =>
        -- cap = 0: the unit is admitted and immediately shed — explicitly.
        ({ s with settled := s.settled ++ [(u, .shed)],
                  admitted := s.admitted ++ [u] }, .admittedDropOldest)
      | v :: rest =>
        ({ s with backlog := rest ++ [u],
                  settled := s.settled ++ [(v, .shed)],
                  admitted := s.admitted ++ [u] }, .admittedDropOldest)
  | .consume =>
    match s.backlog with
    | [] => (s, .idle)
    | v :: rest =>
      ({ s with backlog := rest,
                settled := s.settled ++ [(v, .delivered)] }, .consumed)
  | .bufferlessKill u =>
    if s.closed then
      ({ s with refused := s.refused ++ [u] }, .refused)
    else
      ({ s with backlog := [],
                settled := s.settled ++ s.backlog.map (fun v => (v, .shed))
                             ++ [(u, .killed)],
                admitted := s.admitted ++ [u],
                closed := true }, .killedClosed)
  | .close =>
    if s.closed then (s, .closedOk)
    else
      ({ s with backlog := [],
                settled := s.settled ++ s.backlog.map (fun v => (v, .shed)),
                closed := true }, .closedOk)

/-- **The stream policy.** Dropping the oldest unit is sound only when units are
independent messages. On a byte stream it is not: the reader would see the tail
of one write spliced onto the head of a later one, and a command parser would
read the splice as a command. When the units are stream segments, a full backlog
therefore leaves only two sound moves — stop taking data, or end the connection —
and this step takes the second, the same transition a bufferless completion
makes. -/
def ShedQueue.streamStep (s : ShedQueue α) : ShedEv α → ShedQueue α × ShedResult
  | .admit u =>
      if s.closed || s.backlog.length < s.cap then s.step (.admit u)
      else s.step (.bufferlessKill u)
  | e => s.step e

/-- **A stream never sheds silently**: when the backlog is full, admitting one
more unit closes the socket instead of dropping data from the middle. -/
theorem ShedQueue.stream_overflow_closes (s : ShedQueue α) (u : α)
    (hopen : s.closed = false) (hfull : ¬ s.backlog.length < s.cap) :
    (s.streamStep (.admit u)).1.closed = true ∧
      (s.streamStep (.admit u)).2 = .killedClosed := by
  simp [streamStep, step, hopen, hfull]

/-- And below the cap the stream policy admits exactly as the datagram one does,
so the difference shows up only at the overflow edge. -/
theorem ShedQueue.stream_under_cap (s : ShedQueue α) (u : α)
    (hroom : s.backlog.length < s.cap) :
    s.streamStep (.admit u) = s.step (.admit u) := by
  simp [streamStep, hroom]

/-- Run a trace of events. -/
def ShedQueue.run (s : ShedQueue α) : List (ShedEv α) → ShedQueue α
  | [] => s
  | e :: es => ((s.step e).1).run es

/-- The machine invariant.

1. **The no-silent-shed identity**: the settled ledger's units, followed
   by the backlog, are exactly the admitted units in order.
2. The backlog respects the cap.
3. A closed socket holds no backlog. -/
def ShedQueue.Inv (s : ShedQueue α) : Prop :=
  s.settled.map Prod.fst ++ s.backlog = s.admitted ∧
  s.backlog.length ≤ s.cap ∧
  (s.closed = true → s.backlog = [])

theorem ShedQueue.init_inv (cap : Nat) :
    (ShedQueue.init cap : ShedQueue α).Inv := by
  simp [Inv, init]

/-- Tagging a list and projecting the tags away is the identity. -/
private theorem map_fst_tag (l : List α) (f : Fate) :
    l.map (Prod.fst ∘ fun v => (v, f)) = l := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    calc (x :: xs).map (Prod.fst ∘ fun v => (v, f))
        = x :: xs.map (Prod.fst ∘ fun v => (v, f)) := rfl
      _ = x :: xs := by rw [ih]

/-- **Preservation**: every edge — admission, oldest-drop, consumption,
bufferless kill, close — preserves the accounting identity, the cap bound,
and the closed-empty condition. -/
theorem ShedQueue.step_inv (s : ShedQueue α) (e : ShedEv α) (h : s.Inv) :
    (s.step e).1.Inv := by
  obtain ⟨hacct, hcap, hclosed⟩ := h
  cases e with
  | admit u =>
    cases hc : s.closed with
    | true =>
      simp only [step, hc, if_pos]
      exact ⟨hacct, hcap, fun _ => hclosed hc⟩
    | false =>
      by_cases hlen : s.backlog.length < s.cap
      · refine ⟨?_, ?_, ?_⟩
        · simp [step, hc, hlen, ← hacct]
        · simp only [step, hc, Bool.false_eq_true, if_false, hlen, if_pos]
          simp
          omega
        · simp [step, hc, hlen]
      · cases hb : s.backlog with
        | nil =>
          have hcap0 : s.cap = 0 := by rw [hb] at hlen; simp at hlen; omega
          refine ⟨?_, ?_, ?_⟩
          · simp [step, hc, hb, hcap0, ← hacct]
          · simp [step, hc, hb, hcap0]
          · simp [step, hc, hb, hcap0]
        | cons v rest =>
          have hlen' : ¬ (rest.length + 1 < s.cap) := by
            rw [hb] at hlen; simpa using hlen
          have hcap' : rest.length + 1 ≤ s.cap := by
            rw [hb] at hcap; simpa using hcap
          refine ⟨?_, ?_, ?_⟩
          · simp [step, hc, hlen', hb, ← hacct]
          · simp [step, hc, hlen', hb]
            omega
          · simp [step, hc, hlen', hb]
  | consume =>
    cases hb : s.backlog with
    | nil => simp only [step, hb]; exact ⟨hacct, hcap, hclosed⟩
    | cons v rest =>
      have hne : s.closed = false := by
        cases hcc : s.closed with
        | false => rfl
        | true => rw [hclosed hcc] at hb; cases hb
      constructor
      · simp only [step, hb, List.map_append, List.map_cons, List.map_nil,
          List.append_assoc]
        rw [← hacct, hb]
        simp
      · refine ⟨?_, ?_⟩
        · simp only [step, hb]
          rw [hb] at hcap
          simp at hcap ⊢
          omega
        · intro hcc
          simp only [step, hb] at hcc ⊢
          rw [hne] at hcc
          cases hcc
  | bufferlessKill u =>
    cases hc : s.closed with
    | true =>
      simp only [step, hc, if_pos]
      exact ⟨hacct, hcap, fun _ => hclosed hc⟩
    | false =>
      refine ⟨?_, by simp [step, hc], by simp [step, hc]⟩
      simp [step, hc, map_fst_tag, ← hacct]
  | close =>
    cases hc : s.closed with
    | true => simp only [step, hc, if_pos]; exact ⟨hacct, hcap, hclosed⟩
    | false =>
      refine ⟨?_, by simp [step, hc], by simp [step, hc]⟩
      simp [step, hc, map_fst_tag, ← hacct]

/-- The invariant holds along every trace from every invariant state. -/
theorem ShedQueue.run_inv (s : ShedQueue α) (es : List (ShedEv α))
    (h : s.Inv) : (s.run es).Inv := by
  induction es generalizing s with
  | nil => exact h
  | cons e es ih => exact ih _ (s.step_inv e h)

/-- The invariant holds along every trace from a fresh socket. -/
theorem ShedQueue.run_init_inv (cap : Nat) (es : List (ShedEv α)) :
    ((ShedQueue.init cap : ShedQueue α).run es).Inv :=
  run_inv _ es (init_inv cap)

/-- **No silent shed** (membership form): every admitted unit is either
still backlogged or has an explicitly recorded fate — delivered, shed, or
killed. There is no fourth way out. -/
theorem ShedQueue.no_silent_shed (s : ShedQueue α) (h : s.Inv) (u : α)
    (hu : u ∈ s.admitted) :
    u ∈ s.backlog ∨ ∃ f, (u, f) ∈ s.settled := by
  rw [← h.1] at hu
  rcases List.mem_append.mp hu with hs | hb
  · rcases List.mem_map.mp hs with ⟨⟨v, f⟩, hmem, hfst⟩
    exact Or.inr ⟨f, by cases hfst; exact hmem⟩
  · exact Or.inl hb

/-- **No invention**: everything in the ledger or the backlog was admitted. -/
theorem ShedQueue.settled_admitted (s : ShedQueue α) (h : s.Inv) (u : α)
    (f : Fate) (hu : (u, f) ∈ s.settled) : u ∈ s.admitted := by
  rw [← h.1]
  exact List.mem_append.mpr (Or.inl (List.mem_map.mpr ⟨(u, f), hu, rfl⟩))

/-- **Order**: the settled ledger is a prefix of the admission sequence —
units settle in the order they were admitted. -/
theorem ShedQueue.settled_prefix (s : ShedQueue α) (h : s.Inv) :
    ∃ rest, s.settled.map Prod.fst ++ rest = s.admitted :=
  ⟨s.backlog, h.1⟩

/-- **The cap is respected**: the backlog bound is one conjunct of the invariant,
so it holds wherever the invariant does — in every reachable state, by
`run_init_inv`. -/
theorem ShedQueue.backlog_bounded (s : ShedQueue α) (h : s.Inv) :
    s.backlog.length ≤ s.cap :=
  h.2.1

/-- The same for any trace from a fresh queue: no event sequence can push the
backlog past the capacity it was created with. -/
theorem ShedQueue.backlog_bounded_run (cap : Nat) (es : List (ShedEv α)) :
    ((ShedQueue.init cap : ShedQueue α).run es).backlog.length
      ≤ ((ShedQueue.init cap : ShedQueue α).run es).cap :=
  backlog_bounded _ (run_init_inv cap es)

/-- **Oldest-drop is exact.** When the backlog is full, admitting `u` sheds
precisely the *oldest* entry (the front), records it, and keeps FIFO order
for the rest: the backlog becomes `rest ++ [u]`. -/
theorem ShedQueue.oldest_drop_exact (s : ShedQueue α) (u v : α)
    (rest : List α) (hb : s.backlog = v :: rest) (hc : s.closed = false)
    (hfull : ¬ s.backlog.length < s.cap) :
    (s.step (.admit u)).1.backlog = rest ++ [u] ∧
    (s.step (.admit u)).1.settled = s.settled ++ [(v, .shed)] ∧
    (s.step (.admit u)).2 = .admittedDropOldest := by
  have hfull' : ¬ (rest.length + 1 < s.cap) := by
    rw [hb] at hfull; simpa using hfull
  simp [step, hc, hfull', hb]

/-- **Consumption is FIFO**: consuming takes exactly the oldest entry and
records it delivered. -/
theorem ShedQueue.consume_fifo (s : ShedQueue α) (v : α) (rest : List α)
    (hb : s.backlog = v :: rest) :
    (s.step .consume).1.backlog = rest ∧
    (s.step .consume).1.settled = s.settled ++ [(v, .delivered)] := by
  simp [step, hb]

/-- **Refusal is not admission**: a unit offered to a closed socket is
recorded refused and the admission ledger is untouched — the accounting
identity owes it nothing. -/
theorem ShedQueue.closed_refuses (s : ShedQueue α) (u : α)
    (hc : s.closed = true) :
    (s.step (.admit u)).1.admitted = s.admitted ∧
    (s.step (.admit u)).1.refused = s.refused ++ [u] ∧
    (s.step (.admit u)).2 = .refused := by
  simp [step, hc]

/-- **The bufferless kill is loud.** Pool exhaustion under data loses the
unit — but the loss is recorded (`killed`), the backlog is explicitly
recycled (`shed`), and the socket closes in the same step. Nothing about
the edge is silent. -/
theorem ShedQueue.bufferless_kill_closes (s : ShedQueue α) (u : α)
    (hc : s.closed = false) :
    (s.step (.bufferlessKill u)).1.closed = true ∧
    (s.step (.bufferlessKill u)).1.backlog = [] ∧
    (u, Fate.killed) ∈ (s.step (.bufferlessKill u)).1.settled := by
  simp [step, hc]

/-- Run a trace under the stream policy. -/
def ShedQueue.runStream (s : ShedQueue α) : List (ShedEv α) → ShedQueue α
  | [] => s
  | e :: es => ((s.streamStep e).1).runStream es

-- Three units into a queue with room for two. The datagram policy sheds the
-- oldest and keeps serving; the stream policy ends the connection instead, so
-- no reader ever sees the splice. Both runs are over the same trace.
private def overflowTrace : List (ShedEv Nat) := [.admit 1, .admit 2, .admit 3]

def regression_452 : Bool := decide (((ShedQueue.init 2 : ShedQueue Nat).run
    overflowTrace).closed == false
  && ((ShedQueue.init 2 : ShedQueue Nat).run overflowTrace).backlog == [2, 3]
  )
def regression_453 : Bool := decide (((ShedQueue.init 2 : ShedQueue Nat).runStream
    overflowTrace).closed == true
  && ((ShedQueue.init 2 : ShedQueue Nat).runStream overflowTrace).backlog == []
  )

-- Under the cap the two policies agree.
def regression_454 : Bool := decide (((ShedQueue.init 4 : ShedQueue Nat).runStream
    overflowTrace).backlog == [1, 2, 3]
  )

/-- Witness: the queue invariant is satisfiable at a concrete capacity. -/
theorem ShedQueue.Inv_witness : (ShedQueue.init 4 : ShedQueue Nat).Inv :=
  ShedQueue.init_inv 4

end DN.Dataplane.Flow
