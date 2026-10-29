-- SPDX-License-Identifier: AGPL-3.0-or-later

/-!
# DN.Dataplane.Io.Lifecycle — when an operation's lease may be released

An operation handed to the kernel or to a worker holds a lease: a buffer, a slot, a file the
operation may still touch. The lease may go back only once every completion the operation owes has
come, and a request to cancel it is not one: the cancellation's own answer says only whether the
operation was found, and its completion still comes (io_uring's `-ECANCELED`), or came already
(`-ENOENT`), or may come with its result (`-EALREADY`). A multishot operation owes completions until
one without `IORING_CQE_F_MORE`; a zero-copy send owes its data completion and, when that completion
carries `IORING_CQE_F_MORE`, its notification too, in either order; one without it owes none.

`step` is that discipline for one operation: an event, the operation after it, and whether its
lease is released by it. What is proven:

* `run_releases_le_one` — a lease is released at most once, whatever the events;
* `step_release_ended` — it is released only by the event that ends the operation;
* `cancel_never_releases` — neither a cancellation nor its answer releases it;
* `sendZc_release` — a zero-copy send's lease goes back only once its data completion came and,
  if that completion said more, its notification;
* `once_released` — one completion, however many cancellations and answers come before it,
  releases its lease once; `multishot_released` — completions that say more, then the final one,
  do: nothing leaks.

`cancelling` records that a cancellation was asked; nothing waits on it, as nothing may.

Concrete traces witness the cases the reactor meets, and two broken disciplines, one releasing at
the cancellation's answer and one at a zero-copy send's data, release a lease the operation may
still write into (`releaseOnAnswer_early`, `releaseOnData_early`).

The server's host runs its file jobs on workers (`native/jobs.c`): a job is an operation of one
completion, a job not yet begun at a stop is dropped (cancelled before it ran), and one running is
waited for (cancellation found it running). Multishot and zero-copy are io_uring's, which the host
does not use yet.
-/

namespace DN.Dataplane.Io.Lifecycle

/-- What an operation owes: one completion, completions until a final one, or a zero-copy send's
data completion and notification. -/
inductive Kind
  | once
  | multishot
  | sendZc
  deriving DecidableEq, Repr

/-- How the kernel answers a cancellation: it cancelled the operation, did not find it, or found
it running. -/
inductive Answer
  | canceled
  | notFound
  | already
  deriving DecidableEq, Repr

/-- An event of one operation: a completion (`more` for a multishot one that goes on, or a
zero-copy send's data completion a notification follows), a zero-copy send's notification, a
cancellation submitted, its answer. -/
inductive Event
  | done (more : Bool)
  | notif
  | cancel
  | answer (a : Answer)
  deriving DecidableEq, Repr

/-- An operation: its kind, whether a cancellation was asked, whether its last data completion came,
whether no notification is owed any more (one came, or a zero-copy send's data completion said
none follows), and whether it has ended. -/
structure Op where
  kind : Kind
  cancelling : Bool := false
  data : Bool := false
  notified : Bool := false
  ended : Bool := false
  deriving DecidableEq, Repr

/-- Every completion the operation owes has come. -/
def Op.owesNothing (o : Op) : Bool :=
  match o.kind with
  | .sendZc => o.data && o.notified
  | _ => o.data

/-- The operation ended if it owes nothing more, and whether that releases its lease now. -/
def finish (o : Op) : Op × Bool := ({ o with ended := o.owesNothing }, o.owesNothing)

/-- The operation after an event, and whether the event releases its lease: only the one that
ends it, by the last completion it owes. -/
def step (o : Op) : Event → Op × Bool
  | .done more =>
    if o.ended then (o, false)
    else if o.kind == .multishot && more then finish o
    else if o.kind == .sendZc && !more then finish { o with data := true, notified := true }
    else finish { o with data := true }
  | .notif => if o.ended || o.kind != .sendZc then (o, false) else finish { o with notified := true }
  | .cancel => ({ o with cancelling := true }, false)
  | .answer _ => (o, false)

/-- The events in order: the operation after them, and how many released its lease. -/
def run (o : Op) : List Event → Op × Nat
  | [] => (o, 0)
  | e :: es => ((run (step o e).1 es).1, (run (step o e).1 es).2 + if (step o e).2 then 1 else 0)

/-- Every operation and event, as a finite case split: an operation is a kind and four flags. -/
theorem step_cases {P : Op → Event → Prop}
    (h : ∀ k c d n en more a, P ⟨k, c, d, n, en⟩ (.done more) ∧ P ⟨k, c, d, n, en⟩ .notif ∧
      P ⟨k, c, d, n, en⟩ .cancel ∧ P ⟨k, c, d, n, en⟩ (.answer a)) (o : Op) (e : Event) : P o e := by
  obtain ⟨k, c, d, n, en⟩ := o
  cases e with
  | done more => exact (h k c d n en more .canceled).1
  | notif => exact (h k c d n en false .canceled).2.1
  | cancel => exact (h k c d n en false .canceled).2.2.1
  | answer a => exact (h k c d n en false a).2.2.2

theorem step_kind (o : Op) (e : Event) : (step o e).1.kind = o.kind :=
  step_cases (P := fun o e => (step o e).1.kind = o.kind) (by
    intro k c d n en more a
    cases k <;> cases c <;> cases d <;> cases n <;> cases en <;> cases more <;> cases a <;> decide) o e

/-- **Released only by the end**: an event that releases the lease ends an operation that had not
ended, every completion it owes having come. -/
theorem step_release_ended {o : Op} {e : Event} (h : (step o e).2 = true) :
    o.ended = false ∧ (step o e).1.ended = true ∧ (step o e).1.owesNothing = true :=
  step_cases (P := fun o e => (step o e).2 = true →
      o.ended = false ∧ (step o e).1.ended = true ∧ (step o e).1.owesNothing = true) (by
    intro k c d n en more a
    cases k <;> cases c <;> cases d <;> cases n <;> cases en <;> cases more <;> cases a <;> decide) o e h

/-- Once ended, an operation stays ended and nothing releases its lease again. -/
theorem run_ended : ∀ {o : Op}, o.ended = true → ∀ es, (run o es).2 = 0 ∧ (run o es).1.ended = true
  | _, _, [] => ⟨rfl, by assumption⟩
  | o, h, e :: es => by
    have hs : (step o e).2 = false ∧ (step o e).1.ended = true :=
      step_cases (P := fun o e => o.ended = true → (step o e).2 = false ∧ (step o e).1.ended = true) (by
        intro k c d n en more a
        cases k <;> cases c <;> cases d <;> cases n <;> cases en <;> cases more <;> cases a <;> decide) o e h
    have := run_ended hs.2 es
    simp only [run, hs.1, this.1, this.2]
    simp

/-- **A lease is released at most once**, whatever the events. -/
theorem run_releases_le_one : ∀ (o : Op) (es : List Event), o.ended = false → (run o es).2 ≤ 1
  | _, [], _ => Nat.zero_le _
  | o, e :: es, h => by
    simp only [run]
    cases hr : (step o e).2 with
    | true =>
      have := (run_ended (step_release_ended hr).2.1 es).1
      simp [this]
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
      by_cases he : (step o e).1.ended = true
      · simp [(run_ended he es).1]
      · exact run_releases_le_one _ es (by simpa using he)

/-- **Cancelling is not releasing**: neither the request nor its answer gives the lease back. -/
theorem cancel_never_releases (o : Op) (a : Answer) :
    (step o .cancel).2 = false ∧ (step o (.answer a)).2 = false := ⟨rfl, rfl⟩

/-- **A zero-copy send's lease** goes back only once its data completion came and either its
notification came or that completion said none follows. -/
theorem sendZc_release {o : Op} {e : Event} (hk : o.kind = .sendZc) (h : (step o e).2 = true) :
    (step o e).1.data = true ∧ (step o e).1.notified = true := by
  have := (step_release_ended h).2.2
  simpa [Op.owesNothing, step_kind, hk] using this

/-- A cancellation or its answer, which change nothing a completion depends on. -/
def Event.asks : Event → Bool
  | .cancel | .answer _ => true
  | _ => false

theorem asks_keep {o : Op} {e : Event} (h : e.asks = true) :
    (step o e).2 = false ∧ (step o e).1.kind = o.kind ∧ (step o e).1.data = o.data ∧
      (step o e).1.notified = o.notified ∧ (step o e).1.ended = o.ended := by
  cases e <;> simp_all [Event.asks, step]

/-- **No leak, one completion**: an operation of one completion, however many cancellations and
answers come before it, is released once, by it. -/
theorem once_released : ∀ (o : Op) (es : List Event), o.kind = .once → o.ended = false →
    o.data = false → (∀ e ∈ es, e.asks = true) → (run o (es ++ [.done false])).2 = 1
  | o, [], hk, he, hd, _ => by simp [run, step, finish, Op.owesNothing, hk, he]
  | o, e :: es, hk, he, hd, ha => by
    have hs := asks_keep (o := o) (ha e (List.mem_cons_self ..))
    have := once_released (step o e).1 es (hs.2.1.trans hk) (hs.2.2.2.2.trans he) (hs.2.2.1.trans hd)
      (fun e' h' => ha e' (List.mem_cons_of_mem _ h'))
    simp only [List.cons_append, run, hs.1, this]
    rfl

/-- **No leak, multishot**: completions that say more, then the final one, release the lease once. -/
theorem multishot_released : ∀ (o : Op) (n : Nat), o.kind = .multishot → o.ended = false → o.data = false →
    (run o (List.replicate n (.done true) ++ [.done false])).2 = 1
  | o, 0, hk, he, hd => by simp [run, step, finish, Op.owesNothing, hk, he]
  | o, n + 1, hk, he, hd => by
    have hs : step o (.done true) = ({ o with ended := false }, false) := by
      simp [step, finish, Op.owesNothing, hk, he, hd]
    have := multishot_released { o with ended := false } n hk rfl hd
    simp only [List.replicate_succ, List.cons_append, run, hs, this]
    rfl

/-! ## The cases a reactor meets -/

/-- How many times the lease of a new operation of `kind` is released by `es`. -/
def released (kind : Kind) (es : List Event) : Nat := (run { kind } es).2

-- The completion first, the cancellation finding nothing: released by the completion alone.
example : released .once [.done false, .cancel, .answer .notFound] = 1 := by decide
example : (run { kind := .once } [.done false]).2 = 1 := by decide
-- The cancellation first: nothing released until the cancelled completion comes.
example : released .once [.cancel, .answer .canceled] = 0 := by decide
example : released .once [.cancel, .answer .canceled, .done false] = 1 := by decide
-- Found running: its completion still comes, and only it releases.
example : released .once [.cancel, .answer .already, .done false] = 1 := by decide
-- Multishot: MORE, MORE, then the final completion.
example : released .multishot [.done true, .done true] = 0 := by decide
example : released .multishot [.done true, .done true, .done false] = 1 := by decide
-- A zero-copy send: its data completion says a notification follows, which comes after it or
-- before; one that failed says none follows.
example : released .sendZc [.done true] = 0 := by decide
example : released .sendZc [.done true, .notif] = 1 := by decide
example : released .sendZc [.notif, .done true] = 1 := by decide
example : released .sendZc [.done false] = 1 := by decide
-- A late completion after the end releases nothing more.
example : released .once [.done false, .done false] = 1 := by decide

/-! ## Two broken disciplines -/

/-- Broken: the lease goes back once the cancellation is answered. -/
def stepReleaseOnAnswer (o : Op) : Event → Op × Bool
  | .answer _ => if o.cancelling && !o.ended then ({ o with ended := true }, true) else (o, false)
  | e => step o e

/-- Broken: a zero-copy send's lease goes back at its data completion, notification or none. -/
def stepReleaseOnData (o : Op) : Event → Op × Bool
  | .done more => if o.kind == .sendZc && !o.ended then ({ o with data := true, ended := true }, true)
    else step o (.done more)
  | e => step o e

/-- The first broken discipline releases the lease of an operation the kernel may still complete
into it: the answer said `canceled`, and the cancelled completion has not come. -/
theorem releaseOnAnswer_early :
    let o1 := (stepReleaseOnAnswer { kind := .once } .cancel).1
    (stepReleaseOnAnswer o1 (.answer .canceled)).2 = true ∧
      (stepReleaseOnAnswer o1 (.answer .canceled)).1.data = false := by decide

/-- The second releases a zero-copy send's buffer before the kernel's notification that it is done
with it. -/
theorem releaseOnData_early :
    (stepReleaseOnData { kind := .sendZc } (.done true)).2 = true ∧
      (stepReleaseOnData { kind := .sendZc } (.done true)).1.notified = false := by decide

end DN.Dataplane.Io.Lifecycle
