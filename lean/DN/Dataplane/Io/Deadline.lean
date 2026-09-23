-- SPDX-License-Identifier: AGPL-3.0-or-later
import DN.Dataplane.Io.Reactor

/-!
# DN.Dataplane.Io.Deadline — the unified deadline min-heap with lazy deletion, verified

A completion reactor must wake *exactly* when the nearest of many pending
deadlines expires: connection idle timeouts, request body deadlines, handshake
and keepalive windows all funnel into a single queue that arms **one** kernel
timer for the earliest deadline and re-arms as deadlines come and go. The
running engine would use a `BinaryHeap` keyed by deadline plus a hash map of the
live keys. What follows is a model of that structure: the theorems below are
about this model, and no refinement theorem connects it to a running queue.

## The model

A `DQ K` (deadline queue over correlator/connection keys `K`) holds three parts:

* `heap` — the min-heap, modeled by its *ordered projection*: the exact sequence
  a real binary min-heap yields on repeated pop, i.e. entries in nondecreasing
  deadline order. `Sorted` names that invariant, and `insertSorted` preserves it
  (`insertSorted_sorted`). This file does not carry `Sorted` as a field of `DQ`
  or track it along a run, so every theorem below that needs it takes it as a
  hypothesis.
* `live` — the authoritative map from key to its **current** deadline. A heap
  entry `⟨d, k⟩` is *live* iff `live` still maps `k` to that exact `d`
  (`Live`); otherwise it is a **tombstone** (the key was removed, or its
  deadline was updated and this entry is the stale copy).
* `armed` — the single deadline the kernel timer is currently set for (`Option`:
  at most one armed timer, ever).

**Lazy deletion** is the point: `remove k` drops `k` from `live` and *leaves the
heap untouched* — no O(n) heap surgery. The stale entry is skipped when it
surfaces on pop. `insert`/`update` push a new entry and re-point `live`; the
superseded entry becomes a tombstone the same way.

## What is proven (0 sorries)

* `heap_min_correct` — **peek returns the earliest deadline**: the first live
  entry in the ordered heap has a deadline ≤ every live entry's, and is itself
  live. The queue's notion of "nearest" is the true minimum over live deadlines.
* `heap_lazy_delete` — **a cancelled timer is skipped on pop, not eagerly
  removed**: after `remove k` the heap is byte-for-byte unchanged, yet `k` is
  never emitted by a drain — its entry is passed over as a tombstone.
* `heap_arm_one` — **only the nearest deadline arms the kernel timer**: the
  deadline `arm` selects is a live deadline and is ≤ every live deadline. That a
  queue carries at most one armed timer is structural, not a theorem: `armed` is
  an `Option`.
* `heap_pop_ordered` — **deadlines fire in order**: the sequence a drain emits is
  itself sorted by deadline (nondecreasing) — no timer fires before an earlier
  one.
* `insertKeepingSmall_bounded` / `removeKeepingSmall_bounded` /
  `runKeepingSmall_bounded` — **the tombstones stay bounded**: re-arming a key to
  the deadline it already holds pushes nothing, and sweeping when the tombstones
  outnumber the live entries keeps the heap within twice its live content — at
  every state of every trace, so a client that resets its idle timer on every
  command cannot grow the heap with the command rate.

## Composition with the reactor

The keys have to carry a generation: the reactor's correlators
(`DN.Dataplane.Io.Key`), or connection handles that do. A bare file descriptor is
not a safe key, because the kernel reuses it and a deadline set for a closed
connection would fire on its successor. The armed deadline is the timeout a
reactor loop blocks on, and a fired key drives a `complete` (idle-close,
body-timeout) on the slab. The lazy-tombstone discipline mirrors the slab's
generation tags — a superseded deadline is skipped exactly as a recycled
correlator is rejected in `DN.Dataplane.Io.Slab`. This is a candidate
specification for such a queue, not a description of a running one.
-/

namespace DN.Dataplane.Io

/-- A heap entry: a deadline (in kernel ticks) paired with the key it belongs to.
A running engine would order these by `deadline` in its own heap. -/
structure Entry (K : Type) where
  /-- Absolute deadline in monotonic ticks. -/
  deadline : Nat
  /-- The correlator / connection key this deadline governs. -/
  key : K
deriving Repr, DecidableEq

/-- The deadline queue: the ordered heap projection, the authoritative live map,
and the single armed deadline. -/
structure DQ (K : Type) where
  /-- The min-heap as its ordered pop-sequence (nondecreasing deadline). -/
  heap : List (Entry K)
  /-- Authoritative key → current deadline map (association list). -/
  live : List (K × Nat)
  /-- The one deadline the kernel timer is armed for, if any. -/
  armed : Option Nat

/-! ## The live map (association list) -/

variable {K : Type} [DecidableEq K]

/-- Look up a key's current deadline in the live map (first match wins). -/
def lookupD (l : List (K × Nat)) (k : K) : Option Nat :=
  match l with
  | [] => none
  | (k', d) :: t => if k' = k then some d else lookupD t k

/-- Drop every binding for `k` from the live map. -/
def removeKey (k : K) : List (K × Nat) → List (K × Nat)
  | [] => []
  | (k', d) :: t => if k' = k then removeKey k t else (k', d) :: removeKey k t

/-- Set `k`'s deadline to `d` (drop any prior binding, then prepend). -/
def upsert (l : List (K × Nat)) (k : K) (d : Nat) : List (K × Nat) :=
  (k, d) :: removeKey k l

/-- **A heap entry is live** iff the live map still points its key at exactly its
deadline. Any other case (key removed, or deadline updated so this is a stale
copy) is a tombstone. -/
def Live (live : List (K × Nat)) (e : Entry K) : Prop :=
  lookupD live e.key = some e.deadline

/-- Decidable form of `Live`, used as the `find?`/drain predicate. -/
def isLive (live : List (K × Nat)) (e : Entry K) : Bool :=
  decide (lookupD live e.key = some e.deadline)

theorem isLive_iff (live : List (K × Nat)) (e : Entry K) :
    isLive live e = true ↔ Live live e := by
  simp [isLive, Live]

/-! ### Live-map lemmas -/

/-- After `removeKey k`, the key `k` is absent. -/
theorem lookupD_removeKey_self (l : List (K × Nat)) (k : K) :
    lookupD (removeKey k l) k = none := by
  induction l with
  | nil => rfl
  | cons p t ih =>
    obtain ⟨k', d⟩ := p
    unfold removeKey
    by_cases h : k' = k
    · simp [h, ih]
    · simp only [h, if_false]
      unfold lookupD
      simp [h, ih]

/-- Removing *some other* key preserves an already-absent key. -/
theorem lookupD_removeKey_none {l : List (K × Nat)} {k k' : K}
    (h : lookupD l k = none) : lookupD (removeKey k' l) k = none := by
  induction l with
  | nil => rfl
  | cons p t ih =>
    obtain ⟨a, d⟩ := p
    unfold lookupD at h
    by_cases ha : a = k
    · rw [if_pos ha] at h; exact absurd h (by simp)
    · rw [if_neg ha] at h
      unfold removeKey
      by_cases ha' : a = k'
      · rw [if_pos ha']; exact ih h
      · rw [if_neg ha']; unfold lookupD; rw [if_neg ha]; exact ih h

/-- `upsert` reads back the value just written. -/
theorem lookupD_upsert_self (l : List (K × Nat)) (k : K) (d : Nat) :
    lookupD (upsert l k d) k = some d := by
  unfold upsert lookupD; simp

/-! ## The pop sequence: drain expired, skipping tombstones -/

/-- **The pop sequence.** Walk the ordered heap front-to-back: stop at the first
entry whose deadline is still in the future (`now < deadline`); otherwise, if the
entry is live, emit it and remove its key from the live map (so a later duplicate
entry for the same key becomes a tombstone); if it is a tombstone, drop it and
continue. This is the exact key sequence `drain_expired` returns. -/
def fired : List (Entry K) → List (K × Nat) → Nat → List (Entry K)
  | [], _, _ => []
  | e :: rest, live, now =>
    if now < e.deadline then []
    else if isLive live e then e :: fired rest (removeKey e.key live) now
    else fired rest live now

/-- The full stateful drain: the fired entries, the surviving heap (future +
un-popped), and the compacted live map. `drainExpired.1 = fired` (`fired_eq`). -/
def drainExpired : List (Entry K) → List (K × Nat) → Nat → List (Entry K) × List (Entry K) × List (K × Nat)
  | [], live, _ => ([], [], live)
  | e :: rest, live, now =>
    if now < e.deadline then ([], e :: rest, live)
    else if isLive live e then
      let r := drainExpired rest (removeKey e.key live) now
      (e :: r.1, r.2.1, r.2.2)
    else drainExpired rest live now

/-- The stateful drain's fired projection is exactly `fired`. -/
theorem fired_eq (heap : List (Entry K)) (live : List (K × Nat)) (now : Nat) :
    (drainExpired heap live now).1 = fired heap live now := by
  induction heap generalizing live with
  | nil => rfl
  | cons e rest ih =>
    unfold drainExpired fired
    by_cases h1 : now < e.deadline
    · simp [h1]
    · by_cases h2 : isLive live e
      · simp [h1, h2, ih]
      · simp [h1, h2, ih]

/-! ## Peek / nearest / arm -/

/-- The first live entry in the ordered heap — a real min-heap's `peek` after it
skips tombstones off the top. -/
def firstLive (dq : DQ K) : Option (Entry K) :=
  dq.heap.find? (fun e => isLive dq.live e)

/-- The nearest live deadline: the deadline of the first live entry. -/
def nearest (dq : DQ K) : Option Nat :=
  (firstLive dq).map (·.deadline)

/-- **Arm** the kernel timer for the nearest live deadline (and only that one). -/
def arm (dq : DQ K) : DQ K :=
  { dq with armed := nearest dq }

/-! ## Insert / update / remove -/

/-- Insert `e` into the ordered heap, keeping nondecreasing deadline order. -/
def insertSorted (e : Entry K) : List (Entry K) → List (Entry K)
  | [] => [e]
  | h :: t => if e.deadline ≤ h.deadline then e :: h :: t else h :: insertSorted e t

/-- **Insert / update** a deadline: push a heap entry and re-point the live map,
then re-arm. `update` (sliding an idle window) is the same operation — the prior
entry for `k`, if any, is left in the heap as a tombstone. -/
def insert (dq : DQ K) (k : K) (d : Nat) : DQ K :=
  arm { dq with heap := insertSorted ⟨d, k⟩ dq.heap, live := upsert dq.live k d }

/-- **Remove** (lazy deletion): drop `k` from the live map only. The heap entry
stays, to be skipped when it surfaces on pop. -/
def remove (dq : DQ K) (k : K) : DQ K :=
  { dq with live := removeKey k dq.live }

/-! ## The sorted invariant -/

/-- The heap is ordered by nondecreasing deadline — a real min-heap's pop order. -/
def Sorted (h : List (Entry K)) : Prop :=
  h.Pairwise (fun a b => a.deadline ≤ b.deadline)

omit [DecidableEq K] in
/-- Membership in `insertSorted` is membership in the list plus the new entry. -/
theorem mem_insertSorted {x e : Entry K} {l : List (Entry K)} :
    x ∈ insertSorted e l ↔ x = e ∨ x ∈ l := by
  induction l with
  | nil => simp [insertSorted]
  | cons h t ih =>
    unfold insertSorted
    by_cases hc : e.deadline ≤ h.deadline
    · rw [if_pos hc]; exact List.mem_cons
    · rw [if_neg hc]
      simp only [List.mem_cons, ih]
      exact or_left_comm

omit [DecidableEq K] in
/-- **`insert` preserves the sorted invariant**: a sorted heap stays sorted. The
peek/arm/pop theorems take sortedness as a hypothesis, and this is what
discharges it for a heap built by insertion. -/
theorem insertSorted_sorted (e : Entry K) (l : List (Entry K)) (h : Sorted l) :
    Sorted (insertSorted e l) := by
  induction l with
  | nil => exact List.pairwise_singleton _ e
  | cons a t ih =>
    obtain ⟨ha, ht⟩ := List.pairwise_cons.mp h
    unfold insertSorted
    by_cases hc : e.deadline ≤ a.deadline
    · rw [if_pos hc]
      refine List.pairwise_cons.mpr ⟨?_, h⟩
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact hc
      · exact Nat.le_trans hc (ha x hx)
    · rw [if_neg hc]
      have hae : a.deadline ≤ e.deadline := Nat.le_of_not_le hc
      refine List.pairwise_cons.mpr ⟨?_, ih ht⟩
      intro x hx
      rcases mem_insertSorted.mp hx with rfl | hx
      · exact hae
      · exact ha x hx

omit [DecidableEq K] in
/-- Empty heaps are sorted. -/
theorem sorted_nil : Sorted ([] : List (Entry K)) := List.Pairwise.nil

/-! ## Compaction: keeping the tombstones bounded

Lazy deletion never rewrites the heap, so every `remove` and every slid deadline
leaves a tombstone behind. A client that resets an idle timer on each command —
which RFC 3977 §3.1 asks a server to do — therefore grows the heap with the
command rate, not with the number of connections. Compaction is the sweep that
drops the tombstones. Sweeping when they outnumber the live entries keeps the
heap within twice its live content, which is what the bounds below state; the
cost of the sweeps themselves is not part of this model. -/

/-- How many live entries the heap carries (the rest are tombstones). -/
def liveCount (dq : DQ K) : Nat := dq.heap.countP (fun e => isLive dq.live e)

/-- **Compaction**: drop every tombstone from the heap, keeping the live entries
in their order. The live map and the armed deadline are untouched. -/
def compact (dq : DQ K) : DQ K :=
  { dq with heap := dq.heap.filter (fun e => isLive dq.live e) }

/-- After compaction the heap is exactly its live entries. -/
theorem compact_length (dq : DQ K) : (compact dq).heap.length = liveCount dq := by
  simp [compact, liveCount, List.countP_eq_length_filter]

/-- Compaction keeps every live entry and drops exactly the tombstones. -/
theorem mem_compact {dq : DQ K} {e : Entry K} :
    e ∈ (compact dq).heap ↔ e ∈ dq.heap ∧ isLive dq.live e = true :=
  List.mem_filter

/-- Compaction loses no live entry: the live count is unchanged. -/
theorem compact_liveCount (dq : DQ K) : liveCount (compact dq) = liveCount dq := by
  simp [compact, liveCount, List.countP_eq_length_filter, List.filter_filter]

/-- Compaction keeps the heap ordered, so every peek/arm/pop theorem applies to
the compacted queue. -/
theorem compact_sorted {dq : DQ K} (hs : Sorted dq.heap) : Sorted (compact dq).heap :=
  List.Pairwise.sublist List.filter_sublist hs

/-- Compaction does not change which entry surfaces first: `find?` skips exactly
the entries the filter removes. So the armed deadline survives a sweep. -/
theorem compact_firstLive (dq : DQ K) : firstLive (compact dq) = firstLive dq := by
  show (dq.heap.filter (fun e => isLive dq.live e)).find? (fun e => isLive dq.live e)
      = dq.heap.find? (fun e => isLive dq.live e)
  induction dq.heap with
  | nil => rfl
  | cons e rest ih =>
      by_cases h : isLive dq.live e = true
      · simp [h, List.find?_cons_of_pos]
      · simp [h, List.find?_cons_of_neg, ih]

/-- The heap is within twice its live content: the tombstones do not outnumber
the entries that still matter. -/
def Bounded (dq : DQ K) : Prop := dq.heap.length ≤ 2 * liveCount dq

/-- An empty queue is bounded. -/
theorem init_bounded : Bounded (⟨[], [], none⟩ : DQ K) := by
  simp [Bounded, liveCount]

/-- **Insert with compaction.** Re-arming a key to the deadline it already has
changes nothing, so it pushes no entry; otherwise push and sweep if the
tombstones have come to outnumber the live entries. -/
def insertKeepingSmall (dq : DQ K) (k : K) (d : Nat) : DQ K :=
  if lookupD dq.live k = some d then dq
  else
    let dq' := insert dq k d
    if 2 * liveCount dq' < dq'.heap.length then arm (compact dq') else dq'

/-- **Remove with compaction.** The removal itself stays lazy; the sweep runs
only when the tombstones have outgrown the live entries. -/
def removeKeepingSmall (dq : DQ K) (k : K) : DQ K :=
  let dq' := remove dq k
  if 2 * liveCount dq' < dq'.heap.length then arm (compact dq') else dq'

/-- **The bound is preserved by an insert.** Re-arming to the same deadline
leaves the queue alone, and any other insert either stays under the bound or is
swept back under it. -/
theorem insertKeepingSmall_bounded {dq : DQ K} (hb : Bounded dq) (k : K) (d : Nat) :
    Bounded (insertKeepingSmall dq k d) := by
  unfold insertKeepingSmall
  by_cases hsame : lookupD dq.live k = some d
  · rw [if_pos hsame]; exact hb
  · rw [if_neg hsame]
    by_cases h : 2 * liveCount (insert dq k d) < (insert dq k d).heap.length
    · rw [if_pos h]
      show (compact (insert dq k d)).heap.length ≤ 2 * liveCount (compact (insert dq k d))
      rw [compact_length, compact_liveCount]
      omega
    · rw [if_neg h]
      show (insert dq k d).heap.length ≤ 2 * liveCount (insert dq k d)
      omega

/-- The bound is preserved by a removal. -/
theorem removeKeepingSmall_bounded (dq : DQ K) (k : K) :
    Bounded (removeKeepingSmall dq k) := by
  unfold removeKeepingSmall
  by_cases h : 2 * liveCount (remove dq k) < (remove dq k).heap.length
  · rw [if_pos h]
    show (compact (remove dq k)).heap.length ≤ 2 * liveCount (compact (remove dq k))
    rw [compact_length, compact_liveCount]
    omega
  · rw [if_neg h]
    show (remove dq k).heap.length ≤ 2 * liveCount (remove dq k)
    omega

/-- Sweeping does not change which deadline is armed. -/
theorem compact_nearest (dq : DQ K) : nearest (compact dq) = nearest dq := by
  simp [nearest, compact_firstLive]

/-- **The drain as an operation.** What is due leaves, what survives stays, and
the timer is re-armed for the nearest deadline that is left — the step a fired
kernel timer drives. The entries it emits are `fired dq.heap dq.live now`, which
the theorems below characterise; the sweep is the one the other operations use,
because a drain can leave the heap with more tombstones than live entries. -/
def drained (dq : DQ K) (now : Nat) : DQ K :=
  { heap := (drainExpired dq.heap dq.live now).2.1,
    live := (drainExpired dq.heap dq.live now).2.2,
    armed := dq.armed }

/-- The drain as one step under the sweeping policy: drain, sweep if the
tombstones have outgrown the live entries, and re-arm for what is left. -/
def fireKeepingSmall (dq : DQ K) (now : Nat) : DQ K :=
  arm (if 2 * liveCount (drained dq now) < (drained dq now).heap.length
       then compact (drained dq now) else drained dq now)

/-- What happens to the queue: arm a key for a deadline, cancel it, or let the
armed timer fire. -/
inductive DQOp (K : Type) where
  /-- Arm (or re-arm) `k` for deadline `d`. -/
  | set (k : K) (d : Nat)
  /-- Cancel `k`. -/
  | cancel (k : K)
  /-- The timer fires at `now`: everything due is drained. -/
  | fire (now : Nat)

/-- One operation under the sweeping policy. -/
def stepKeepingSmall (dq : DQ K) : DQOp K → DQ K
  | .set k d => insertKeepingSmall dq k d
  | .cancel k => removeKeepingSmall dq k
  | .fire now => fireKeepingSmall dq now

/-- A trace of operations under the sweeping policy. -/
def runKeepingSmall (dq : DQ K) : List (DQOp K) → DQ K
  | [] => dq
  | op :: rest => runKeepingSmall (stepKeepingSmall dq op) rest

/-- **The bound is preserved by a drain.** A drain removes keys from the live map
and leaves the future entries in the heap, so it can leave more tombstones than
live entries behind; the same sweep puts it back under the bound. -/
theorem fireKeepingSmall_bounded (dq : DQ K) (now : Nat) :
    Bounded (fireKeepingSmall dq now) := by
  unfold fireKeepingSmall
  by_cases h : 2 * liveCount (drained dq now) < (drained dq now).heap.length
  · rw [if_pos h]
    show (compact (drained dq now)).heap.length ≤ 2 * liveCount (compact (drained dq now))
    rw [compact_length, compact_liveCount]
    omega
  · rw [if_neg h]
    show (drained dq now).heap.length ≤ 2 * liveCount (drained dq now)
    omega

/-- **The bound holds along a whole trace.** Starting from an empty queue, every
state a sequence of arms, cancels and drains can reach keeps the heap within
twice its live content — however long the trace and however often one key is
re-armed. -/
theorem runKeepingSmall_bounded (ops : List (DQOp K)) :
    Bounded (runKeepingSmall (⟨[], [], none⟩ : DQ K) ops) := by
  have general : ∀ (l : List (DQOp K)) (dq : DQ K),
      Bounded dq → Bounded (runKeepingSmall dq l) := by
    intro l
    induction l with
    | nil => intro dq h; exact h
    | cons op rest ih =>
        intro dq h
        refine ih (stepKeepingSmall dq op) ?_
        cases op with
        | set k d => exact insertKeepingSmall_bounded h k d
        | cancel k => exact removeKeepingSmall_bounded dq k
        | fire now => exact fireKeepingSmall_bounded dq now
  exact general ops _ init_bounded

/-! ## Headline theorem 1 — peek returns the earliest deadline -/

/-- The core minimum lemma: in a sorted heap, the first live entry found has the
smallest deadline among all live entries. -/
theorem find_is_min (heap : List (Entry K)) (live : List (K × Nat)) (e : Entry K)
    (hs : Sorted heap) (hf : heap.find? (fun x => isLive live x) = some e) :
    ∀ e' ∈ heap, Live live e' → e.deadline ≤ e'.deadline := by
  induction heap with
  | nil => simp at hf
  | cons h t ih =>
    obtain ⟨hhead, htail⟩ := List.pairwise_cons.mp hs
    cases hb : isLive live h with
    | true =>
      rw [List.find?_cons_of_pos hb] at hf
      injection hf with he
      intro e' he' _
      rw [← he]
      rcases List.mem_cons.mp he' with rfl | he'
      · exact Nat.le_refl _
      · exact hhead e' he'
    | false =>
      rw [List.find?_cons_of_neg (by rw [hb]; simp)] at hf
      intro e' he' hlive'
      rcases List.mem_cons.mp he' with rfl | he'
      · have h1 := (isLive_iff live e').mpr hlive'
        rw [hb] at h1; exact absurd h1 (by simp)
      · exact ih htail hf e' he' hlive'

/-- **`heap_min_correct` — peek returns the earliest deadline.** In a sorted
queue, the first live entry (`firstLive`, a real min-heap's post-tombstone-skip
peek) is itself live *and* has a deadline ≤ every live entry's. The queue's
"nearest" is the true minimum over live deadlines — no earlier deadline is ever
missed. -/
theorem heap_min_correct (dq : DQ K) (hs : Sorted dq.heap) (e : Entry K)
    (hf : firstLive dq = some e) :
    Live dq.live e ∧ ∀ e' ∈ dq.heap, Live dq.live e' → e.deadline ≤ e'.deadline := by
  refine ⟨?_, find_is_min dq.heap dq.live e hs hf⟩
  have := List.find?_some hf
  exact (isLive_iff dq.live e).mp this

/-! ## Headline theorem 2 — lazy deletion: a cancelled key is skipped on pop -/

/-- A key absent from the live map is never emitted by a drain: its entries are
all tombstones and are passed over. -/
theorem fired_absent (heap : List (Entry K)) (live : List (K × Nat)) (now : Nat)
    (k : K) (h : lookupD live k = none) :
    k ∉ (fired heap live now).map (·.key) := by
  induction heap generalizing live with
  | nil => simp [fired]
  | cons e rest ih =>
    unfold fired
    by_cases h1 : now < e.deadline
    · simp [h1]
    · rw [if_neg h1]
      by_cases h2 : isLive live e
      · rw [if_pos h2]
        have hek : e.key ≠ k := by
          intro heq
          have : lookupD live e.key = some e.deadline := (isLive_iff live e).mp h2
          rw [heq, h] at this; exact absurd this (by simp)
        simp only [List.map_cons, List.mem_cons, not_or]
        refine ⟨fun hc => hek hc.symm, ?_⟩
        exact ih (removeKey e.key live) (lookupD_removeKey_none h)
      · rw [if_neg h2]; exact ih live h

/-- **`heap_lazy_delete` — a cancelled timer is skipped on pop, not eagerly
removed.** After `remove dq k`, (1) the heap is *byte-for-byte unchanged* (lazy
deletion touches only the live map, no O(n) heap surgery), and (2) `k` is never
emitted by a drain at any `now` — its stale entry is passed over as a tombstone.
The two together are the exact meaning of lazy deletion. -/
theorem heap_lazy_delete (dq : DQ K) (k : K) (now : Nat) :
    (remove dq k).heap = dq.heap ∧
      k ∉ (fired (remove dq k).heap (remove dq k).live now).map (·.key) := by
  refine ⟨rfl, ?_⟩
  apply fired_absent
  exact lookupD_removeKey_self dq.live k

/-! ## Headline theorem 3 — only the nearest deadline arms the kernel timer -/

/-- **`heap_arm_one` — the armed deadline is the earliest live one.** From a
sorted heap, the deadline `arm` records (when it records one) is a *live*
deadline realized by an actual heap entry, and it is ≤ every live entry's
deadline. That no second timer can be recorded is structural — `armed` is an
`Option` — and nothing here says the kernel installed the timer. -/
theorem heap_arm_one (dq : DQ K) (hs : Sorted dq.heap) (d : Nat)
    (h : (arm dq).armed = some d) :
    (∃ e ∈ dq.heap, Live dq.live e ∧ e.deadline = d) ∧
      (∀ e' ∈ dq.heap, Live dq.live e' → d ≤ e'.deadline) := by
  have hn : nearest dq = some d := h
  unfold nearest at hn
  rw [Option.map_eq_some_iff] at hn
  obtain ⟨e, hfe, hde⟩ := hn
  obtain ⟨hlive, hmin⟩ := heap_min_correct dq hs e hfe
  refine ⟨⟨e, List.mem_of_find?_eq_some hfe, hlive, hde⟩, ?_⟩
  intro e' he' hlive'
  rw [← hde]; exact hmin e' he' hlive'

/-! ## Headline theorem 4 — deadlines fire in order -/

/-- Every fired entry comes from the heap (the drain never invents an entry). -/
theorem fired_subset (heap : List (Entry K)) (live : List (K × Nat)) (now : Nat)
    (x : Entry K) (hx : x ∈ fired heap live now) : x ∈ heap := by
  induction heap generalizing live with
  | nil => simp [fired] at hx
  | cons e rest ih =>
    unfold fired at hx
    by_cases h1 : now < e.deadline
    · rw [if_pos h1] at hx; simp at hx
    · rw [if_neg h1] at hx
      by_cases h2 : isLive live e
      · rw [if_pos h2] at hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (ih (removeKey e.key live) hx)
      · rw [if_neg h2] at hx
        exact List.mem_cons_of_mem _ (ih live hx)

/-- **`heap_pop_ordered` — deadlines fire in order.** From a sorted heap, the
sequence a drain emits is itself sorted by nondecreasing deadline: no timer fires
before one with an earlier deadline. Sortedness comes in as a hypothesis;
`insertSorted_sorted` is what supplies it for a heap built by insertion. -/
theorem heap_pop_ordered (heap : List (Entry K)) (live : List (K × Nat)) (now : Nat)
    (hs : Sorted heap) : Sorted (fired heap live now) := by
  induction heap generalizing live with
  | nil => exact sorted_nil
  | cons e rest ih =>
    obtain ⟨hhead, htail⟩ := List.pairwise_cons.mp hs
    unfold fired
    by_cases h1 : now < e.deadline
    · rw [if_pos h1]; exact sorted_nil
    · rw [if_neg h1]
      by_cases h2 : isLive live e
      · rw [if_pos h2]
        refine List.pairwise_cons.mpr ⟨?_, ih (removeKey e.key live) htail⟩
        intro x hx
        exact hhead x (fired_subset rest (removeKey e.key live) now x hx)
      · rw [if_neg h2]; exact ih live htail

/-! ## The invariant and the firing semantics

A second model of this queue used to live beside this one, with the live map and
the armed deadline but no heap. Two models of one component mean two sets of
claims and nothing connecting them, so what the other one proved is proven here,
over the representation that also carries the heap and its tombstones. Key
uniqueness, which that model had to assume, is not needed: `lookupD` reads the
first binding and `upsert` writes to the front, so a key's current deadline is
whatever the map answers.
-/

/-- Removing another key leaves a key's binding alone. -/
theorem lookupD_removeKey_other {l : List (K × Nat)} {k k' : K} (h : k' ≠ k) :
    lookupD (removeKey k' l) k = lookupD l k := by
  induction l with
  | nil => rfl
  | cons p t ih =>
    obtain ⟨a, d⟩ := p
    by_cases ha : a = k'
    · subst ha; simp [removeKey, lookupD, h, ih]
    · simp [removeKey, lookupD, ha, ih]

/-- Writing another key leaves a key's binding alone. -/
theorem lookupD_upsert_other {l : List (K × Nat)} {k k' : K} {d : Nat} (h : k' ≠ k) :
    lookupD (upsert l k' d) k = lookupD l k := by
  simp [upsert, lookupD, h, lookupD_removeKey_other h]

/-- **Every live deadline is in the heap.** Lazy deletion leaves tombstones
behind; it never does the opposite, so a deadline the live map records always has
its own entry to surface on pop. This is what makes `nearest` a lower bound on
the live deadlines rather than on the entries that happen to remain. -/
def Covered (dq : DQ K) : Prop :=
  ∀ k d, lookupD dq.live k = some d → (⟨d, k⟩ : Entry K) ∈ dq.heap

/-- **The queue invariant.** The heap is ordered, every live deadline has an
entry, and the armed deadline is at or before every live one. The last part is
one-sided on purpose: a lazy removal leaves the timer armed for a deadline that
is no longer live (a tombstone's timer, which fires into a no-op), so `armed` may
be *earlier* than every live deadline — never later. -/
structure Inv (dq : DQ K) : Prop where
  /-- The heap is in nondecreasing deadline order. -/
  sorted : Sorted dq.heap
  /-- Every live deadline has its entry in the heap. -/
  covered : Covered dq
  /-- The armed deadline is at or before every live deadline. -/
  armed : ∀ k d, lookupD dq.live k = some d → ∃ t, dq.armed = some t ∧ t ≤ d

/-- The empty queue satisfies the invariant. -/
theorem init_inv : Inv (⟨[], [], none⟩ : DQ K) where
  sorted := sorted_nil
  covered := by intro k d h; exact absurd h (by simp [lookupD])
  armed := by intro k d h; exact absurd h (by simp [lookupD])

/-- A covered live key gives the heap a live entry, so `firstLive` finds one. -/
theorem firstLive_isSome {dq : DQ K} (hc : Covered dq) {k : K} {d : Nat}
    (h : lookupD dq.live k = some d) : ∃ e, firstLive dq = some e := by
  have hmem : (⟨d, k⟩ : Entry K) ∈ dq.heap := hc k d h
  have hlive : isLive dq.live (⟨d, k⟩ : Entry K) = true := by
    simp [isLive, h]
  cases hf : firstLive dq with
  | none =>
    have := List.find?_eq_none.mp hf (⟨d, k⟩ : Entry K) hmem
    exact absurd hlive (by simpa using this)
  | some e => exact ⟨e, rfl⟩

/-- **The armed deadline of an armed queue is the nearest live one.** In a queue
that satisfies the invariant, `nearest` is a lower bound on every live deadline —
the minimum is taken over what the live map says, not over the entries left in
the heap. -/
theorem nearest_le_live {dq : DQ K} (hs : Sorted dq.heap) (hc : Covered dq)
    {k : K} {d : Nat} (h : lookupD dq.live k = some d) :
    ∃ t, nearest dq = some t ∧ t ≤ d := by
  obtain ⟨e, he⟩ := firstLive_isSome hc h
  obtain ⟨_, hmin⟩ := heap_min_correct dq hs e he
  refine ⟨e.deadline, ?_, hmin (⟨d, k⟩ : Entry K) (hc k d h) h⟩
  unfold nearest
  rw [he]
  rfl

/-- **Arming restores the invariant**: a queue whose heap is ordered and whose
live deadlines are covered satisfies all of it once the timer is armed for the
nearest one. -/
theorem arm_inv {dq : DQ K} (hs : Sorted dq.heap) (hc : Covered dq) : Inv (arm dq) where
  sorted := hs
  covered := hc
  armed _ _ h := nearest_le_live hs hc h

/-- Compaction keeps every live deadline covered: it drops tombstones only. -/
theorem compact_covered {dq : DQ K} (hc : Covered dq) : Covered (compact dq) := by
  intro k d h
  have hlive : lookupD dq.live k = some d := h
  exact mem_compact.mpr ⟨hc k d h, by simp [isLive, hlive]⟩

/-- A removal keeps every remaining live deadline covered. -/
theorem remove_covered {dq : DQ K} (hc : Covered dq) (k : K) : Covered (remove dq k) := by
  intro k' d h
  by_cases hk : k = k'
  · subst hk
    rw [show (remove dq k).live = removeKey k dq.live from rfl,
      lookupD_removeKey_self] at h
    exact absurd h (by simp)
  · rw [show (remove dq k).live = removeKey k dq.live from rfl,
      lookupD_removeKey_other hk] at h
    exact hc k' d h

/-- An insert keeps every live deadline covered: the new one gets its own entry,
and the others keep theirs. -/
theorem insert_covered {dq : DQ K} (hc : Covered dq) (k : K) (d : Nat) :
    Covered (insert dq k d) := by
  intro k' d' h
  by_cases hk : k = k'
  · subst hk
    rw [show (insert dq k d).live = upsert dq.live k d from rfl,
      lookupD_upsert_self] at h
    injection h with h
    subst h
    exact mem_insertSorted.mpr (Or.inl rfl)
  · rw [show (insert dq k d).live = upsert dq.live k d from rfl,
      lookupD_upsert_other hk] at h
    exact mem_insertSorted.mpr (Or.inr (hc k' d' h))

/-- What a drain leaves of the heap is a suffix of it: the walk stops at the
first entry that is not due and never reorders anything. -/
theorem drain_suffix (heap : List (Entry K)) (live : List (K × Nat)) (now : Nat) :
    (drainExpired heap live now).2.1 <:+ heap := by
  induction heap generalizing live with
  | nil => exact List.suffix_rfl
  | cons e rest ih =>
    unfold drainExpired
    by_cases h1 : now < e.deadline
    · rw [if_pos h1]; exact List.suffix_rfl
    · rw [if_neg h1]
      by_cases h2 : isLive live e
      · rw [if_pos h2]
        exact (ih (removeKey e.key live)).trans (List.suffix_cons e rest)
      · rw [if_neg h2]
        exact (ih live).trans (List.suffix_cons e rest)

/-- A drain leaves every deadline it did not fire covered: it drops a key from
the live map only when it emits that key's entry, and it drops an entry from the
heap only when it emitted it or found it a tombstone. -/
theorem drain_covered {heap : List (Entry K)} {live : List (K × Nat)} {now : Nat}
    (hc : ∀ k d, lookupD live k = some d → (⟨d, k⟩ : Entry K) ∈ heap) :
    ∀ k d, lookupD (drainExpired heap live now).2.2 k = some d →
      (⟨d, k⟩ : Entry K) ∈ (drainExpired heap live now).2.1 := by
  induction heap generalizing live with
  | nil =>
    intro k d h
    exact absurd (hc k d h) (by simp)
  | cons e rest ih =>
    intro k d h
    unfold drainExpired at h ⊢
    by_cases h1 : now < e.deadline
    · rw [if_pos h1] at h ⊢
      exact hc k d h
    · rw [if_neg h1] at h ⊢
      by_cases h2 : isLive live e
      · rw [if_pos h2] at h ⊢
        refine ih (live := removeKey e.key live) ?_ k d h
        intro k' d' h'
        have hne : e.key ≠ k' := by
          intro hk
          rw [hk, lookupD_removeKey_self] at h'
          exact absurd h' (by simp)
        have hold : lookupD live k' = some d' := by
          rw [← lookupD_removeKey_other hne]; exact h'
        rcases List.mem_cons.mp (hc k' d' hold) with heq | hmem
        · exact absurd (congrArg Entry.key heq.symm) hne
        · exact hmem
      · rw [if_neg h2] at h ⊢
        refine ih (live := live) ?_ k d h
        intro k' d' h'
        rcases List.mem_cons.mp (hc k' d' h') with heq | hmem
        · exact absurd (by rw [← heq]; simpa [isLive, Live] using h' : isLive live e = true) (by simp [h2])
        · exact hmem

/-- **Every operation preserves the invariant**, sweeping or not. -/
theorem stepKeepingSmall_inv {dq : DQ K} (h : Inv dq) (op : DQOp K) :
    Inv (stepKeepingSmall dq op) := by
  cases op with
  | set k d =>
    show Inv (insertKeepingSmall dq k d)
    unfold insertKeepingSmall
    by_cases hsame : lookupD dq.live k = some d
    · rw [if_pos hsame]; exact h
    · rw [if_neg hsame]
      have hs' : Sorted (insert dq k d).heap := insertSorted_sorted _ _ h.sorted
      have hc' : Covered (insert dq k d) := insert_covered h.covered k d
      by_cases hsweep : 2 * liveCount (insert dq k d) < (insert dq k d).heap.length
      · rw [if_pos hsweep]
        exact arm_inv (compact_sorted hs') (compact_covered hc')
      · rw [if_neg hsweep]
        exact { sorted := hs', covered := hc', armed := fun k' d' h' => nearest_le_live hs' hc' h' }
  | fire now =>
    show Inv (fireKeepingSmall dq now)
    unfold fireKeepingSmall
    have hs' : Sorted (drained dq now).heap :=
      List.Pairwise.sublist (drain_suffix dq.heap dq.live now).sublist h.sorted
    have hc' : Covered (drained dq now) := drain_covered h.covered
    by_cases hsweep : 2 * liveCount (drained dq now) < (drained dq now).heap.length
    · rw [if_pos hsweep]
      exact arm_inv (compact_sorted hs') (compact_covered hc')
    · rw [if_neg hsweep]
      exact arm_inv hs' hc'
  | cancel k =>
    show Inv (removeKeepingSmall dq k)
    unfold removeKeepingSmall
    have hs' : Sorted (remove dq k).heap := h.sorted
    have hc' : Covered (remove dq k) := remove_covered h.covered k
    by_cases hsweep : 2 * liveCount (remove dq k) < (remove dq k).heap.length
    · rw [if_pos hsweep]
      exact arm_inv (compact_sorted hs') (compact_covered hc')
    · rw [if_neg hsweep]
      refine { sorted := hs', covered := hc', armed := ?_ }
      intro k' d hk'
      by_cases hk : k = k'
      · subst hk
        rw [show (remove dq k).live = removeKey k dq.live from rfl,
          lookupD_removeKey_self] at hk'
        exact absurd hk' (by simp)
      · rw [show (remove dq k).live = removeKey k dq.live from rfl,
          lookupD_removeKey_other hk] at hk'
        exact h.armed k' d hk'

/-- The invariant holds along a whole trace. -/
theorem runKeepingSmall_inv {dq : DQ K} (h : Inv dq) (ops : List (DQOp K)) :
    Inv (runKeepingSmall dq ops) := by
  induction ops generalizing dq with
  | nil => exact h
  | cons op rest ih => exact ih (stepKeepingSmall_inv h op)

/-- The invariant holds in every state reachable from the empty queue. -/
theorem runKeepingSmall_init_inv (ops : List (DQOp K)) :
    Inv (runKeepingSmall (⟨[], [], none⟩ : DQ K) ops) :=
  runKeepingSmall_inv init_inv ops

/-! ### What a fire does -/

/-- Everything a drain emits was due: the walk stops at the first entry whose
deadline is still in the future. -/
theorem fired_due (heap : List (Entry K)) (live : List (K × Nat)) (now : Nat) :
    ∀ e ∈ fired heap live now, e.deadline ≤ now := by
  induction heap generalizing live with
  | nil => intro e he; simp [fired] at he
  | cons x rest ih =>
    intro e he
    unfold fired at he
    by_cases h1 : now < x.deadline
    · rw [if_pos h1] at he; simp at he
    · rw [if_neg h1] at he
      by_cases h2 : isLive live x
      · rw [if_pos h2] at he
        rcases List.mem_cons.mp he with rfl | he
        · omega
        · exact ih _ e he
      · rw [if_neg h2] at he
        exact ih _ e he

/-- A key still bound to a future deadline is not emitted, whatever the clock
input claims and however many tombstones it carries. The other model needed key
uniqueness as a side condition here; reading the live map answers that. -/
theorem no_early_expiry {dq : DQ K} {k : K} {d now : Nat}
    (h : lookupD dq.live k = some d) (hfut : now < d) :
    ∀ e ∈ fired dq.heap dq.live now, e.key ≠ k := by
  have general : ∀ (heap : List (Entry K)) (live : List (K × Nat)),
      lookupD live k = some d → ∀ e ∈ fired heap live now, e.key ≠ k := by
    intro heap
    induction heap with
    | nil => intro live _ e he; simp [fired] at he
    | cons x rest ih =>
      intro live hlive e he
      unfold fired at he
      by_cases h1 : now < x.deadline
      · rw [if_pos h1] at he; simp at he
      · rw [if_neg h1] at he
        by_cases h2 : isLive live x
        · rw [if_pos h2] at he
          rcases List.mem_cons.mp he with rfl | he
          · intro hkey
            have : lookupD live e.key = some e.deadline := by
              simpa [isLive, Live] using h2
            rw [hkey, hlive] at this
            injection this with this
            omega
          · refine ih (removeKey x.key live) ?_ e he
            by_cases hx : x.key = k
            · exfalso
              have hxl : lookupD live x.key = some x.deadline := by
                simpa [isLive, Live] using h2
              rw [hx, hlive] at hxl
              injection hxl with hxl
              omega
            · rw [lookupD_removeKey_other hx]; exact hlive
        · rw [if_neg h2] at he
          exact ih live hlive e he
  exact general dq.heap dq.live h

/-- A live entry whose deadline is due is emitted: the walk reaches it, because
every earlier entry in the ordered heap is due as well, and it is still live when
it does, because a drain removes only the keys it has emitted. -/
theorem fired_of_due {heap : List (Entry K)} {live : List (K × Nat)} {k : K} {d now : Nat}
    (hs : Sorted heap) (hmem : (⟨d, k⟩ : Entry K) ∈ heap)
    (hlive : lookupD live k = some d) (hdue : d ≤ now) :
    ∃ e ∈ fired heap live now, e.key = k := by
  induction heap generalizing live with
  | nil => exact absurd hmem (by simp)
  | cons x rest ih =>
    obtain ⟨hhead, htail⟩ := List.pairwise_cons.mp hs
    unfold fired
    by_cases h1 : now < x.deadline
    · exfalso
      rcases List.mem_cons.mp hmem with rfl | hrest
      · simp at h1; omega
      · have hxd : x.deadline ≤ d := by simpa using hhead _ hrest
        omega
    · rw [if_neg h1]
      by_cases hlx : isLive live x = true
      · rw [if_pos hlx]
        by_cases hk : x.key = k
        · exact ⟨x, List.mem_cons_self .., hk⟩
        · have hrest : (⟨d, k⟩ : Entry K) ∈ rest := by
            rcases List.mem_cons.mp hmem with rfl | hr
            · exact absurd rfl hk
            · exact hr
          obtain ⟨e, he, hek⟩ :=
            ih htail hrest (by rw [lookupD_removeKey_other hk]; exact hlive)
          exact ⟨e, List.mem_cons_of_mem _ he, hek⟩
      · rw [if_neg hlx]
        have hrest : (⟨d, k⟩ : Entry K) ∈ rest := by
          rcases List.mem_cons.mp hmem with rfl | hr
          · exact absurd (by simp [isLive, hlive] : isLive live (⟨d, k⟩ : Entry K) = true) hlx
          · exact hr
        exact ih htail hrest hlive

/-- **Nothing is lost by a fire**: a live key whose deadline is due fires, and one
still in the future keeps the deadline it had. -/
theorem fire_partitions {dq : DQ K} {k : K} {d : Nat} (hs : Sorted dq.heap)
    (hc : Covered dq) (now : Nat) (h : lookupD dq.live k = some d) :
    (d ≤ now ∧ ∃ e ∈ fired dq.heap dq.live now, e.key = k) ∨
    (now < d ∧ lookupD (drainExpired dq.heap dq.live now).2.2 k = some d) := by
  by_cases hfut : now < d
  · refine Or.inr ⟨hfut, ?_⟩
    have general : ∀ (heap : List (Entry K)) (live : List (K × Nat)),
        lookupD live k = some d → lookupD (drainExpired heap live now).2.2 k = some d := by
      intro heap
      induction heap with
      | nil => intro live hlive; simpa [drainExpired] using hlive
      | cons x rest ih =>
        intro live hlive
        unfold drainExpired
        by_cases h1 : now < x.deadline
        · rw [if_pos h1]; exact hlive
        · rw [if_neg h1]
          by_cases h2 : isLive live x
          · rw [if_pos h2]
            refine ih (removeKey x.key live) ?_
            by_cases hx : x.key = k
            · exfalso
              have hxl : lookupD live x.key = some x.deadline := by
                simpa [isLive, Live] using h2
              rw [hx, hlive] at hxl
              injection hxl with hxl
              omega
            · rw [lookupD_removeKey_other hx]; exact hlive
          · rw [if_neg h2]; exact ih live hlive
    exact general dq.heap dq.live h
  · exact Or.inl ⟨by omega, fired_of_due hs (hc k d h) h (by omega)⟩

/-- **A spurious fire is a no-op**: when nothing is due, the drain emits nothing
and the live map is untouched. This is what makes lazy deletion sound — the timer
left armed for a removed key fires into an empty drain. -/
theorem spurious_fire {dq : DQ K} {now : Nat}
    (hfresh : ∀ k d, lookupD dq.live k = some d → now < d) :
    fired dq.heap dq.live now = [] ∧ (drainExpired dq.heap dq.live now).2.2 = dq.live := by
  have general : ∀ (heap : List (Entry K)) (live : List (K × Nat)),
      (∀ k d, lookupD live k = some d → now < d) →
      fired heap live now = [] ∧ (drainExpired heap live now).2.2 = live := by
    intro heap
    induction heap with
    | nil => intro live _; exact ⟨rfl, rfl⟩
    | cons x rest ih =>
      intro live hf
      unfold fired drainExpired
      by_cases h1 : now < x.deadline
      · rw [if_pos h1, if_pos h1]; exact ⟨rfl, rfl⟩
      · rw [if_neg h1, if_neg h1]
        have h2 : isLive live x = false := by
          cases hb : isLive live x with
          | false => rfl
          | true =>
            exfalso
            have hlive : lookupD live x.key = some x.deadline := by
              simpa [isLive, Live] using hb
            have := hf x.key x.deadline hlive
            omega
        have hne : ¬ (isLive live x = true) := by simp [h2]
        rw [if_neg hne, if_neg hne]
        exact ih live hf
  exact general dq.heap dq.live hfresh

/-! ## Non-vacuity: a concrete queue, evaluated

Real numbers, not schematic hypotheses. Three connection keys with staggered
deadlines; the queue is manifestly sorted; peek picks the minimum, a drain fires
in order, and a removed key is skipped. -/

/-- Sample: keys `10, 20, 30` with deadlines `3, 5, 8` (already sorted). -/
private def sampleDQ : DQ Nat :=
  { heap := [⟨3, 10⟩, ⟨5, 20⟩, ⟨8, 30⟩]
  , live := [(10, 3), (20, 5), (30, 8)]
  , armed := none }

/-- The sample heap is sorted (decidable check, not `native_decide`). -/
theorem sampleDQ_sorted : Sorted sampleDQ.heap := by unfold Sorted; decide

-- Peek returns the earliest deadline (key 10 at deadline 3).
def regression_428 : Bool := decide (firstLive sampleDQ == some ⟨3, 10⟩
  )
def regression_429 : Bool := decide (nearest sampleDQ == some 3
  )

-- Arm installs exactly the nearest deadline.
def regression_432 : Bool := decide ((arm sampleDQ).armed == some 3
  )

-- A full drain at now = 6 fires keys 10 then 20, in deadline order; 30 survives.
def regression_435 : Bool := decide ((fired sampleDQ.heap sampleDQ.live 6).map (·.key) == [10, 20]
  )

-- Lazy delete: remove key 20, heap is unchanged, and 20 is skipped on drain.
def regression_438 : Bool := decide ((remove sampleDQ 20).heap == sampleDQ.heap
  )
def regression_439 : Bool := decide ((fired (remove sampleDQ 20).heap (remove sampleDQ 20).live 6).map (·.key) == [10]
  )

-- Update (slide) key 10's deadline out to 9: the old entry becomes a tombstone,
-- so a drain at now = 6 no longer fires 10 (only 20).
def regression_443 : Bool := decide (((insert sampleDQ 10 9).heap).length == 4   -- old entry retained (tombstone)
  )
def regression_444 : Bool := decide ((fired (insert sampleDQ 10 9).heap (insert sampleDQ 10 9).live 6).map (·.key) == [20]
  )

-- Sliding one key's deadline again and again is what an idle timer does on a
-- client that keeps sending commands. With lazy deletion alone the heap grows by
-- one tombstone per slide; with compaction it stays within twice the live set.
private def slideLazy : Nat → DQ Nat
  | 0 => insert ⟨[], [], none⟩ 1 100
  | n + 1 => insert (slideLazy n) 1 (101 + n)

private def slideCompacting : Nat → DQ Nat
  | 0 => insertKeepingSmall ⟨[], [], none⟩ 1 100
  | n + 1 => insertKeepingSmall (slideCompacting n) 1 (101 + n)

private def resetSameDeadline : Nat → DQ Nat
  | 0 => insertKeepingSmall ⟨[], [], none⟩ 1 100
  | n + 1 => insertKeepingSmall (resetSameDeadline n) 1 100

def regression_445 : Bool := decide ((slideLazy 15).heap.length == 16
  )
-- The sweep keeps the heap small AND keeps the deadline that must still fire:
-- a sweep that emptied the heap would pass the length test and lose the timer.
def regression_446 : Bool := decide ((slideCompacting 15).heap.length <= 2
  && (slideCompacting 15).live.length == 1
  && nearest (slideCompacting 15) == some 115
  )
-- Re-arming to the deadline a key already has pushes nothing, so a client that
-- keeps resetting its timer inside one tick does not grow the heap either.
def regression_447 : Bool := decide ((resetSameDeadline 29).heap.length == 1
  && nearest (resetSameDeadline 29) == some 100
  )

-- A mixed trace of arms, re-arms and cancels: the heap stays within twice the
-- live set at the end, and the live keys are the ones the trace left armed.
private def mixedTrace : List (DQOp Nat) :=
  [.set 1 10, .set 2 20, .set 1 30, .cancel 2, .set 3 40, .set 1 50, .set 3 60, .cancel 1]

def regression_448 : Bool := decide (
  (runKeepingSmall (⟨[], [], none⟩ : DQ Nat) mixedTrace).heap.length
    <= 2 * liveCount (runKeepingSmall (⟨[], [], none⟩ : DQ Nat) mixedTrace)
  && (runKeepingSmall (⟨[], [], none⟩ : DQ Nat) mixedTrace).live.length == 1
  && nearest (runKeepingSmall (⟨[], [], none⟩ : DQ Nat) mixedTrace) == some 60
  )

/-! ### Mutant witnesses (the contract bites)

A queue that armed the *second* entry rather than the nearest would report `5`,
not `3` — `heap_arm_one` rejects it. A drain that eagerly removed on `remove`
would drop the heap entry; `heap_lazy_delete`'s first conjunct (`heap` unchanged)
forbids that. These evaluate to the non-mutant answers, witnessing the theorems
constrain real behavior. -/

/-- The nearest is strictly below the runner-up: arming anything but the head is
observably wrong. -/
theorem sample_nearest_lt_second : nearest sampleDQ = some 3 ∧ (3 : Nat) < 5 := by
  refine ⟨rfl, by decide⟩

/-- Lazy (not eager) deletion is observable: after `remove`, the heap still has
all three entries — an eager implementation would have two. -/
theorem sample_remove_keeps_heap_len : (remove sampleDQ 20).heap.length = 3 := rfl

/-! ## Composition with the reactor correlators

The deadline keys are the reactor's own correlators. Instantiating `K :=
DN.Dataplane.Io.Key` (the generation-tagged slab key, which is `DecidableEq`) shows the
deadline queue composes directly with `DN.Dataplane.Io.Reactor`: a fired key is the
correlator whose slab slot the reactor will `complete` (idle-close / body
timeout), and the armed deadline is the timeout the reactor's wait loop blocks
on. -/

/-- A deadline queue keyed by reactor correlators — the composition instance. -/
private def reactorDQ : DQ Key :=
  { heap := [⟨100, ⟨1, 0⟩⟩, ⟨200, ⟨2, 0⟩⟩]
  , live := [(⟨1, 0⟩, 100), (⟨2, 0⟩, 200)]
  , armed := none }

theorem reactorDQ_sorted : Sorted reactorDQ.heap := by unfold Sorted; decide

-- The nearest correlator deadline arms; its key is a live slab correlator.
def regression_481 : Bool := decide (nearest reactorDQ == some 100
  )
def regression_482 : Bool := decide ((fired reactorDQ.heap reactorDQ.live 150).map (·.key) == [(⟨1, 0⟩ : Key)]
  )

/-! ### Non-vacuity of the invariant and the firing semantics

The trace below moves the queue: two keys are armed, one slides to a later
deadline, and a fire at an instant between them expires exactly the due key. -/

/-- A trace of three arms, the last one sliding key 1 from 10 to 30. -/
def armedDQ : DQ Nat :=
  runKeepingSmall (⟨[], [], none⟩ : DQ Nat) [.set 1 10, .set 2 20, .set 1 30]

-- Sliding a key leaves one binding for it, not two.
def regression_459 : Bool := decide (armedDQ.live.length == 2
  )

-- The slid deadline is what the queue answers for that key.
def regression_484 : Bool := decide (lookupD armedDQ.live 1 == some 30
  )

-- The timer is armed for the nearest live deadline, which is now key 2's.
def regression_485 : Bool := decide (armedDQ.armed == some 20
  )

/-- The same trace without the slide, where a fire at 15 is due for one key. -/
private def twoArmed : DQ Nat :=
  runKeepingSmall (⟨[], [], none⟩ : DQ Nat) [.set 1 10, .set 2 20]

-- A fire between the two deadlines expires exactly the due key.
def regression_460 : Bool := decide ((fired twoArmed.heap twoArmed.live 15).map (·.key) == [1]
  )

-- ... and the key that is still in the future keeps its deadline.
def regression_486 : Bool := decide (
    lookupD (drainExpired twoArmed.heap twoArmed.live 15).2.2 2 == some 20
  )

-- A fire before both deadlines is a no-op on the live map.
def regression_487 : Bool := decide (
    (fired twoArmed.heap twoArmed.live 5).isEmpty
      && (drainExpired twoArmed.heap twoArmed.live 5).2.2 == twoArmed.live
  )

-- A drain is a step: what is due leaves, what is not keeps its deadline, and the
-- timer is re-armed for what is left.
def regression_489 : Bool :=
  let q := runKeepingSmall (⟨[], [], none⟩ : DQ Nat) [.set 1 10, .set 2 20, .fire 15]
  (lookupD q.live 1 == none) && (lookupD q.live 2 == some 20) && (q.armed == some 20)

-- A drain that fires nothing leaves the queue alone but re-arms it.
def regression_490 : Bool :=
  let q := runKeepingSmall (⟨[], [], none⟩ : DQ Nat) [.set 1 10, .set 2 20, .fire 5]
  (lookupD q.live 1 == some 10) && (q.armed == some 10) && (q.heap.length == 2)

-- A drain sweeps the tombstones it leaves behind: three arms of one key and a
-- fire leave a heap no larger than twice what is live.
def regression_491 : Bool :=
  let q := runKeepingSmall (⟨[], [], none⟩ : DQ Nat)
    [.set 1 10, .set 1 20, .set 1 30, .set 2 40, .fire 5]
  q.heap.length <= 2 * liveCount q

/-- The invariant holds in a state the operations really reach. -/
theorem armedDQ_inv : Inv armedDQ := runKeepingSmall_init_inv _

/-- Witness: the coverage premise is satisfiable — that queue covers its live
deadlines. -/
theorem Covered_witness : Covered armedDQ := armedDQ_inv.covered

/-- Witness: the liveness premise is satisfiable — key 2 still holds deadline 20
in that queue, so the tombstone tests are not vacuous. -/
theorem Live_witness : Live armedDQ.live ⟨20, 2⟩ := by
  show lookupD armedDQ.live 2 = some 20
  decide


end DN.Dataplane.Io
