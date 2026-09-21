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

/-- What a caller does to the queue: arm a key for a deadline, or cancel it. -/
inductive DQOp (K : Type) where
  /-- Arm (or re-arm) `k` for deadline `d`. -/
  | set (k : K) (d : Nat)
  /-- Cancel `k`. -/
  | cancel (k : K)

/-- One operation under the sweeping policy. -/
def stepKeepingSmall (dq : DQ K) : DQOp K → DQ K
  | .set k d => insertKeepingSmall dq k d
  | .cancel k => removeKeepingSmall dq k

/-- A trace of operations under the sweeping policy. -/
def runKeepingSmall (dq : DQ K) : List (DQOp K) → DQ K
  | [] => dq
  | op :: rest => runKeepingSmall (stepKeepingSmall dq op) rest

/-- **The bound holds along a whole trace.** Starting from an empty queue, every
state a sequence of arms and cancels can reach keeps the heap within twice its
live content — however long the trace and however often one key is re-armed. -/
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

end DN.Dataplane.Io
