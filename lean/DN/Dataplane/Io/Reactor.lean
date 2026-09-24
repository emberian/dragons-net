-- SPDX-License-Identifier: AGPL-3.0-or-later
import DN.Dataplane.Io.Slab

/-!
# DN.Dataplane.Io.Reactor — the completion-queue reactor as a transition system, with proofs

This file models the one-shot core of a completion reactor: the client *submits*
an operation, the environment later supplies a completion carrying the chosen
correlator, and the reactor maps a live correlator back to that operation. It
does not model cancellation, close/EOF cleanup, multishot continuation, kernel
queue behavior, or their races. Correspondence to a running OS adapter remains
a separate obligation.

## The model

`RState` is the reactor state: a `Slab` of in-flight operations (keyed by the
generation-tagged correlator of `DN.Dataplane.Io.Slab`) and a `done` list — the emitted
completions, newest first. The transitions are ordinary functions (the reactor
is deterministic given the kernel's completion events; the *demonic* freedom —
which one-shot completions arrive, in which order, with stale correlators — is
represented by the sequence of calls to these transitions):

* `submit op` — register `op` in the slab, returning a fresh correlator key;
* `complete k res` — look the key up; on a **live** slot remove it and emit one
  completion, on a **stale** slot (recycled: generation mismatch) emit nothing;
* `inline op res` — the fast path: an op that completed immediately (e.g. a
  non-blocking send that succeeded) never enters the slab; its completion is
  emitted directly under the reserved wakeup-sentinel key;
* `wake` — the reactor wakeup; it touches no completion state.

## What is proven (0 sorries)

* `submit_live` — a submitted op is live under the correlator `submit` returns;
* `complete_emits_one` — completing a live key emits **exactly one** completion,
  carrying that op and result (no lost completion);
* `completion_needs_live_slot` — a completion is emitted **only** for a live
  (non-stale) slot;
* `no_double_completion` — a second completion on the same key emits nothing:
  each submitted op that completes yields **exactly one** completion;
* `submit_complete_exactly_one` — the headline conservation over a submit/
  complete trace: the pair emits one completion `⟨k, op, res⟩` and re-delivery
  of `k` emits none;
* `inline_eq_deferred` — **inline ≡ deferred**: an op done inline delivers the
  same `(op, result)` completion as register-then-complete (the fast path is
  observationally the slow path).

## Relation to the buffer-lease model

Within this one-shot abstraction, the slab lifecycle has a lease-like shape:
`submit` = acquire, `complete` = recycle.
`no_double_completion` is `Slab.slab_no_double_remove` lifted to the reactor,
which is itself the slab-level reading of `DN.Dataplane.Ring.recycle_at_most_once` — the
at-most-once half of the ring discipline. There is currently no product model
coupling operation termination to buffer ownership, and no cancellation or
multishot transition here.

## Native correspondence boundary

The correlator lookup, stale-key rejection, and single completion push are
candidate specifications for corresponding Rust paths. No refinement theorem
currently connects this model to a running reactor. In particular, native
cancellation, multishot completion, operation ownership, and the inline
sentinel representation require a larger model before this file can support
whole-reactor safety claims.
-/

namespace DN.Dataplane.Io

variable {α ρ : Type}

/-- An emitted completion: the correlator it was delivered under, the operation
it finishes, and the kernel result. -/
structure Completion (α ρ : Type) where
  /-- The correlator the completion referenced. -/
  key : Key
  /-- The operation this completion finishes. -/
  op : α
  /-- The kernel result carried by the completion. -/
  result : ρ
deriving Repr, DecidableEq

/-- The reactor state: in-flight operations in the slab, and the log of emitted
completions (newest first). -/
structure RState (α ρ : Type) where
  /-- In-flight operations, keyed by generation-tagged correlator. -/
  slab : Slab α
  /-- Emitted completions, newest first. -/
  done : List (Completion α ρ)

/-- The reserved wakeup-sentinel correlator (index 0). `Slab.allocAt` never
allocates index 0, `Slab.Reserved` is preserved by insert and remove, and
`slab_index0_reserved` turns that into `get = none`, so this correlator cannot
denote a live slot. Reserving it is this application's convention: the kernel
treats a completion's user data as opaque bytes and reserves nothing. -/
def sentinelKey : Key := ⟨0, 0⟩

/-- **Submit**: register an operation, returning its fresh correlator and the new
state. -/
def RState.submit (st : RState α ρ) (op : α) : Key × RState α ρ :=
  let (k, sl) := st.slab.insert op
  (k, { st with slab := sl })

/-- **Complete**: deliver a kernel completion for correlator `k` with result
`res`. On a live slot the op is removed and one completion is emitted; on a stale
slot (recycled) nothing is emitted — the completion is rejected. -/
def RState.complete (st : RState α ρ) (k : Key) (res : ρ) : RState α ρ :=
  match st.slab.remove k with
  | some (op, sl) => { slab := sl, done := ⟨k, op, res⟩ :: st.done }
  | none => st

/-- **Inline**: the fast path — an op that completed immediately, never entering
the slab. Its completion is emitted directly under the wakeup-sentinel key. -/
def RState.inline (st : RState α ρ) (op : α) (res : ρ) : RState α ρ :=
  { st with done := ⟨sentinelKey, op, res⟩ :: st.done }

/-- **Wake**: the reactor wakeup; it touches no completion state. -/
def RState.wake (st : RState α ρ) : RState α ρ := st

/-! ## Safety theorems -/

/-- A submitted op is live under the correlator `submit` hands back. -/
theorem submit_live (st : RState α ρ) (op : α) :
    (st.submit op).2.slab.get (st.submit op).1 = some op := by
  unfold RState.submit
  simpa using slab_insert_get st.slab op

/-- **No lost completion**: completing a live key emits exactly one completion,
carrying that op and result. -/
theorem complete_emits_one (st : RState α ρ) (k : Key) (res : ρ) (op : α) (sl : Slab α)
    (h : st.slab.remove k = some (op, sl)) :
    st.complete k res = { slab := sl, done := ⟨k, op, res⟩ :: st.done } := by
  unfold RState.complete
  rw [h]

/-- On a live key, the completion list grows by exactly one. -/
theorem complete_live_len (st : RState α ρ) (k : Key) (res : ρ) (op : α) (sl : Slab α)
    (h : st.slab.remove k = some (op, sl)) :
    (st.complete k res).done.length = st.done.length + 1 := by
  rw [complete_emits_one st k res op sl h]
  simp

/-- **A completion is emitted only for a live slot.** If `complete` changed the
completion log, the correlator named a live (non-stale) slot. -/
theorem completion_needs_live_slot (st : RState α ρ) (k : Key) (res : ρ)
    (h : (st.complete k res).done ≠ st.done) : (st.slab.get k).isSome := by
  unfold RState.complete at h
  cases hr : st.slab.remove k with
  | none => rw [hr] at h; exact absurd rfl h
  | some p =>
      obtain ⟨op, sl⟩ := p
      rw [Slab.get_of_remove st.slab k op sl hr]
      rfl

/-- **No double completion.** Once a live key is completed, a second completion
on the same key emits nothing — its slot was recycled (generation bumped). Each
op that completes yields exactly one completion. -/
theorem no_double_completion (st : RState α ρ) (k : Key) (res res' : ρ)
    (h : (st.slab.get k).isSome) :
    ((st.complete k res).complete k res').done = (st.complete k res).done := by
  obtain ⟨op, hget⟩ := Option.isSome_iff_exists.mp h
  obtain ⟨sl, hrm⟩ := Slab.remove_of_get st.slab k op hget
  have hst1 : st.complete k res = { slab := sl, done := ⟨k, op, res⟩ :: st.done } :=
    complete_emits_one st k res op sl hrm
  have hnone : sl.remove k = none := slab_no_double_remove st.slab k op sl hrm
  rw [hst1]
  unfold RState.complete
  simp only []
  rw [hnone]

/-- **Conservation over a submit/complete trace** (the headline). Submitting an
op and then completing its correlator emits exactly one completion — `⟨k, op,
res⟩` — and re-delivering the same correlator emits nothing. Each submitted op
that completes yields exactly one completion. -/
theorem submit_complete_exactly_one (st : RState α ρ) (op : α) (res res' : ρ) :
    let k := (st.submit op).1
    let s1 := (st.submit op).2
    (s1.complete k res).done = ⟨k, op, res⟩ :: st.done ∧
      ((s1.complete k res).complete k res').done = (s1.complete k res).done := by
  intro k s1
  have hlive : s1.slab.get k = some op := submit_live st op
  obtain ⟨sl, hrm⟩ := Slab.remove_of_get s1.slab k op hlive
  refine ⟨?_, ?_⟩
  · rw [complete_emits_one s1 k res op sl hrm]
    show (⟨k, op, res⟩ :: s1.done) = ⟨k, op, res⟩ :: st.done
    rfl
  · exact no_double_completion s1 k res res' (by rw [hlive]; rfl)

/-- **Inline ≡ deferred.** An operation done inline (the fast path) delivers the
same `(op, result)` completion as registering it and then completing its
correlator. The correlators differ — inline uses the wakeup sentinel, deferred
uses the fresh slab key — but the delivered `(op, result)` is identical, so the
fast path is observationally the slow path. -/
theorem inline_eq_deferred (st : RState α ρ) (op : α) (res : ρ) :
    let k := (st.submit op).1
    let s1 := (st.submit op).2
    ((s1.complete k res).done.head?.map (fun c => (c.op, c.result)))
      = ((st.inline op res).done.head?.map (fun c => (c.op, c.result))) := by
  intro k s1
  have hlive : s1.slab.get k = some op := submit_live st op
  obtain ⟨sl, hrm⟩ := Slab.remove_of_get s1.slab k op hlive
  rw [complete_emits_one s1 k res op sl hrm]
  unfold RState.inline
  simp

/-! ## Non-vacuity: concrete reactor traces -/

/-- A reactor over `Nat` ops and `Nat` results, starting empty. -/
private def r0 : RState Nat Nat := { slab := Slab.empty Nat 8, done := [] }

-- A submitted op is live under its returned correlator.
def regression_203 : Bool := decide ((r0.submit 100).2.slab.get (r0.submit 100).1 == some 100
  )

-- Submit → complete emits exactly one completion carrying (op, result).
private def submitThenComplete : List (Completion Nat Nat) :=
  let (k, s1) := r0.submit 100
  (s1.complete k 7).done

def regression_210 : Bool := decide (submitThenComplete.length == 1
  )
def regression_211 : Bool := decide ((submitThenComplete.head?.map (fun c => (c.op, c.result))) == some (100, 7)
  )

-- No double completion: re-delivering the same correlator emits nothing.
private def doubleComplete : Nat :=
  let (k, s1) := r0.submit 100
  let s2 := s1.complete k 7
  (s2.complete k 9).done.length

def regression_219 : Bool := decide (doubleComplete == 1
  )

-- Inline ≡ deferred: both deliver the same (op, result) at the head.
private def inlineVsDeferred : Bool :=
  let (k, s1) := r0.submit 100
  let deferred := (s1.complete k 7).done.head?.map (fun c => (c.op, c.result))
  let inline := (r0.inline 100 7).done.head?.map (fun c => (c.op, c.result))
  deferred == inline && deferred == some (100, 7)

def regression_228 : Bool := decide (inlineVsDeferred == true
  )

-- A correlator whose slot has been reused is rejected. The second component
-- records that the reuse really happened: without it the test would pass on a
-- slab that never recycles the index.
private def staleAfterReuse : Nat × Bool :=
  let (kA, s1) := r0.submit 100
  let s2 := s1.complete kA 7         -- kA's slot is free again here
  let (kB, s3) := s2.submit 200      -- same index, newer generation
  ((s3.complete kA 9).done.length, kB.idx == kA.idx)

def regression_236 : Bool := decide (staleAfterReuse == (1, true)
  )

end DN.Dataplane.Io
