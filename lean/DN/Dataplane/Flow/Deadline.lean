-- SPDX-License-Identifier: AGPL-3.0-or-later
import DN.Dataplane.Flow.Token

/-!
# DN.Dataplane.Flow.Deadline

Source provenance is in docs/provenance.json; assurance boundaries are in
docs/assurance.md.
-/

namespace DN.Dataplane.Flow

universe u
variable {κ : Type u}

/-- The nearest deadline in a list, if any. -/
def nearest? (l : List (κ × Nat)) : Option Nat :=
  l.foldr
    (fun e acc =>
      match acc with
      | none => some e.2
      | some t => some (min e.2 t))
    none

/-- `nearest?` unfolds on cons. -/
theorem nearest?_cons (e : κ × Nat) (l : List (κ × Nat)) :
    nearest? (e :: l) =
      match nearest? l with
      | none => some e.2
      | some t => some (min e.2 t) := rfl

/-- `nearest?` is a lower bound on every member. -/
theorem nearest?_le {l : List (κ × Nat)} {k : κ} {d : Nat}
    (h : (k, d) ∈ l) : ∃ t, nearest? l = some t ∧ t ≤ d := by
  induction l with
  | nil => cases h
  | cons e rest ih =>
    rcases List.mem_cons.mp h with he | hrest
    · subst he
      cases hn : nearest? rest with
      | none => exact ⟨d, by rw [nearest?_cons, hn], Nat.le_refl d⟩
      | some t => exact ⟨min d t, by rw [nearest?_cons, hn], by omega⟩
    · rcases ih hrest with ⟨t, ht, hle⟩
      exact ⟨min e.2 t, by rw [nearest?_cons, ht], by omega⟩

/-- The keyed deadline queue. `live` is the authoritative key → deadline
map (keys unique: `Inv.unique`); `armed` records the deadline that the model
requests for its single timer. This file does not model the syscall, an arm
failure, or eventual timer delivery. `armed` may be *earlier* than every live
deadline (a lazy-deletion tombstone's timer) — never later. -/
structure DeadlineQueue (κ : Type u) where
  live : List (κ × Nat)
  armed : Option Nat

/-- An empty queue: no deadlines, no armed timer. -/
def DeadlineQueue.init : DeadlineQueue κ := ⟨[], none⟩

/-- Events driving the queue. Time enters only as the `fire` input. -/
inductive DeadlineEv (κ : Type u) where
  /-- Set (insert or slide) key `k`'s deadline to `d`, updating the modeled
  requested arm if `d` is now the nearest. -/
  | set (k : κ) (d : Nat)
  /-- Remove key `k`. Lazy: the modeled arm is *not* touched. If the host later
  supplies that fire event, it finds a tombstone and the model chooses a new
  requested arm. -/
  | remove (k : κ)
  /-- The armed timer fires at instant `now` (the explicit time input). -/
  | fire (now : Nat)

/-- One step. Returns the successor state and the keys expired by this
event (nonempty only for `fire`). -/
def DeadlineQueue.step [DecidableEq κ] (s : DeadlineQueue κ) :
    DeadlineEv κ → DeadlineQueue κ × List κ
  | .set k d =>
    ({ live := (k, d) :: s.live.filter (fun e => e.1 ≠ k),
       armed := some (match s.armed with
                      | none => d
                      | some t => min t d) }, [])
  | .remove k =>
    ({ live := s.live.filter (fun e => e.1 ≠ k), armed := s.armed }, [])
  | .fire now =>
    let rest := s.live.filter (fun e => ¬ e.2 ≤ now)
    ({ live := rest, armed := nearest? rest },
     (s.live.filter (fun e => e.2 ≤ now)).map Prod.fst)

/-- **The queue invariant.** `armed`: every live deadline has an `armed` value at
or before it (in particular, live nonempty → the model records a requested arm).
`unique`: a key carries at most one deadline, which the "unique keys by
construction" comment above asserted but nothing proved. Neither is a
syscall-success or timer-progress property. -/
structure DeadlineQueue.Inv (s : DeadlineQueue κ) : Prop where
  /-- The requested arm is at or before every live deadline. -/
  armed : ∀ k d, (k, d) ∈ s.live → ∃ t, s.armed = some t ∧ t ≤ d
  /-- A key appears with at most one deadline. -/
  unique : ∀ k d d', (k, d) ∈ s.live → (k, d') ∈ s.live → d = d'

theorem DeadlineQueue.init_inv : (DeadlineQueue.init : DeadlineQueue κ).Inv where
  armed _ _ h := absurd h (List.not_mem_nil)
  unique _ _ _ h _ := absurd h (List.not_mem_nil)

/-- **Preservation**: set, lazy remove, and fire all preserve both halves of the
invariant — the requested-arm ordering and the uniqueness of keys. -/
theorem DeadlineQueue.step_inv [DecidableEq κ] (s : DeadlineQueue κ)
    (e : DeadlineEv κ) (h : s.Inv) : (s.step e).1.Inv := by
  cases e with
  | set k d =>
    refine ⟨?_, ?_⟩
    · intro k' d' hmem
      simp only [step, List.mem_cons] at hmem
      rcases hmem with heq | hmem
      · cases heq
        cases ha : s.armed with
        | none => exact ⟨d, by simp [step, ha], Nat.le_refl d⟩
        | some t => exact ⟨min t d, by simp [step, ha], by omega⟩
      · rcases h.armed k' d' ((List.mem_filter.mp hmem).1) with ⟨t, hat, hle⟩
        exact ⟨min t d, by simp [step, hat], by omega⟩
    · intro k' d₁ d₂ h₁ h₂
      simp only [step, List.mem_cons, Prod.mk.injEq, List.mem_filter,
        decide_eq_true_eq] at h₁ h₂
      rcases h₁ with ⟨hk₁, hd₁⟩ | ⟨hm₁, hne₁⟩
      · rcases h₂ with ⟨_, hd₂⟩ | ⟨_, hne₂⟩
        · rw [hd₁, hd₂]
        · exact absurd hk₁ hne₂
      · rcases h₂ with ⟨hk₂, _⟩ | ⟨hm₂, _⟩
        · exact absurd hk₂ hne₁
        · exact h.unique k' d₁ d₂ hm₁ hm₂
  | remove k =>
    refine ⟨?_, ?_⟩
    · intro k' d' hmem
      simp only [step] at hmem ⊢
      exact h.armed k' d' ((List.mem_filter.mp hmem).1)
    · intro k' d₁ d₂ h₁ h₂
      simp only [step] at h₁ h₂
      exact h.unique k' d₁ d₂ (List.mem_filter.mp h₁).1 (List.mem_filter.mp h₂).1
  | fire now =>
    refine ⟨?_, ?_⟩
    · intro k' d' hmem
      simp only [step] at hmem ⊢
      exact nearest?_le hmem
    · intro k' d₁ d₂ h₁ h₂
      simp only [step] at h₁ h₂
      exact h.unique k' d₁ d₂ (List.mem_filter.mp h₁).1 (List.mem_filter.mp h₂).1

/-- Run a trace of events. -/
def DeadlineQueue.run [DecidableEq κ] (s : DeadlineQueue κ) :
    List (DeadlineEv κ) → DeadlineQueue κ
  | [] => s
  | e :: es => ((s.step e).1).run es

theorem DeadlineQueue.run_inv [DecidableEq κ] (s : DeadlineQueue κ)
    (es : List (DeadlineEv κ)) (h : s.Inv) : (s.run es).Inv := by
  induction es generalizing s with
  | nil => exact h
  | cons e es ih => exact ih _ (s.step_inv e h)

theorem DeadlineQueue.run_init_inv [DecidableEq κ]
    (es : List (DeadlineEv κ)) :
    ((DeadlineQueue.init : DeadlineQueue κ).run es).Inv :=
  run_inv _ es init_inv

/-- **Expiry is exact**: `fire now` expires a key iff it was live with a
deadline at or before `now`. -/
theorem DeadlineQueue.fire_expires_iff [DecidableEq κ]
    (s : DeadlineQueue κ) (now : Nat) (k : κ) :
    k ∈ (s.step (.fire now)).2 ↔ ∃ d, (k, d) ∈ s.live ∧ d ≤ now := by
  simp only [step, List.mem_map, List.mem_filter]
  constructor
  · rintro ⟨⟨k', d⟩, ⟨hmem, hle⟩, rfl⟩
    exact ⟨d, hmem, by simpa using hle⟩
  · rintro ⟨d, hmem, hle⟩
    exact ⟨(k, d), ⟨hmem, by simpa using hle⟩, rfl⟩

/-- **No early expiry**: an entry still in the future never expires —
regardless of what the (adversarial) clock input does. -/
theorem DeadlineQueue.no_early_expiry [DecidableEq κ]
    (s : DeadlineQueue κ) (now : Nat) (k : κ) (d : Nat)
    (huniq : ∀ k d d', (k, d) ∈ s.live → (k, d') ∈ s.live → d = d')
    (hmem : (k, d) ∈ s.live) (hfut : now < d) : k ∉ (s.step (.fire now)).2 := by
  intro hexp
  rcases (fire_expires_iff s now k).mp hexp with ⟨d', hmem', hle⟩
  have := huniq k d' d hmem' hmem
  omega

/-- The same for any trace from the empty queue. The key-uniqueness side
condition used to be the caller's obligation; it is now part of the invariant
every reachable state carries. -/
theorem DeadlineQueue.no_early_expiry_run [DecidableEq κ] (es : List (DeadlineEv κ))
    (now : Nat) (k : κ) (d : Nat)
    (hmem : (k, d) ∈ ((DeadlineQueue.init : DeadlineQueue κ).run es).live)
    (hfut : now < d) :
    k ∉ (((DeadlineQueue.init : DeadlineQueue κ).run es).step (.fire now)).2 :=
  no_early_expiry _ now k d (run_init_inv es).unique hmem hfut

/-- **No lost deadline**: after a fire, every previously live entry either
expired (deadline ≤ now) or is still live with its deadline intact. -/
theorem DeadlineQueue.fire_partitions [DecidableEq κ]
    (s : DeadlineQueue κ) (now : Nat) (k : κ) (d : Nat)
    (hmem : (k, d) ∈ s.live) :
    (d ≤ now ∧ k ∈ (s.step (.fire now)).2) ∨
    (now < d ∧ (k, d) ∈ (s.step (.fire now)).1.live) := by
  by_cases hle : d ≤ now
  · exact Or.inl ⟨hle, (fire_expires_iff s now k).mpr ⟨d, hmem, hle⟩⟩
  · refine Or.inr ⟨by omega, ?_⟩
    simp only [step, List.mem_filter]
    exact ⟨hmem, by simp; omega⟩

/-- **A sufficiently early arm is requested**: unpacking the invariant, whenever
a deadline is live the model's `armed` field is at or before it. What carries the
weight is that every event preserves the invariant (`step_inv`); this theorem
establishes neither that a kernel timer was installed nor that the host will
supply its `fire` event. -/
theorem DeadlineQueue.wake_scheduled (s : DeadlineQueue κ) (h : s.Inv)
    (k : κ) (d : Nat) (hmem : (k, d) ∈ s.live) :
    ∃ t, s.armed = some t ∧ t ≤ d :=
  h.armed k d hmem

/-- The same for any trace from the empty queue: no invariant has to be supplied
by the caller, because `run_init_inv` establishes it. -/
theorem DeadlineQueue.wake_scheduled_run [DecidableEq κ] (es : List (DeadlineEv κ))
    (k : κ) (d : Nat)
    (hmem : (k, d) ∈ ((DeadlineQueue.init : DeadlineQueue κ).run es).live) :
    ∃ t, ((DeadlineQueue.init : DeadlineQueue κ).run es).armed = some t ∧ t ≤ d :=
  (run_init_inv es).armed k d hmem

/-- **Spurious fires are harmless**: if nothing has expired, `fire` leaves
the live set untouched and expires nothing. (This is what makes lazy
deletion sound: a stale timer for a removed key fires into a no-op.) -/
theorem DeadlineQueue.spurious_fire [DecidableEq κ] (s : DeadlineQueue κ)
    (now : Nat) (hfresh : ∀ k d, (k, d) ∈ s.live → now < d) :
    (s.step (.fire now)).1.live = s.live ∧ (s.step (.fire now)).2 = [] := by
  constructor
  · simp only [step]
    apply List.filter_eq_self.mpr
    intro e he
    have := hfresh e.1 e.2 he
    simp
    omega
  · simp only [step, List.map_eq_nil_iff]
    apply List.filter_eq_nil_iff.mpr
    intro e he
    have := hfresh e.1 e.2 he
    simp
    omega

/-!
## The token seam — timer-vs-fd disjointness, by reuse

Timer completions and fd-bound completions share one 64-bit token word.
The disjointness of the two namespaces is the Token partition theorem's
business; here we instantiate it rather than re-prove it.
-/

/-- **A timer completion is unambiguous.** Any well-formed token whose
encoding equals a well-formed timer token's encoding *is* that timer
token. Immediate from `Token.encode_inj` — the bit-63 namespace does the
work. -/
theorem timer_token_unambiguous {t : Token} {job : Nat}
    (ht : t.Wf) (hj : (Token.timer job).Wf)
    (h : t.encode = (Token.timer job).encode) : t = .timer job :=
  Token.encode_inj ht hj h

/-- A timer token never collides with a pending-operation slab key: a timer
firing can never dispatch as (and complete) a socket operation. -/
theorem timer_never_slab (job index gen : Nat)
    (hj : (Token.timer job).Wf) (hs : (Token.slab index gen).Wf) :
    (Token.timer job).encode ≠ (Token.slab index gen).encode := by
  intro h
  cases Token.encode_inj hj hs h

/-- A timer token never collides with a multishot-recv tag: a timer firing
can never dispatch as inbound socket data. -/
theorem timer_never_recv (job fd : Nat)
    (hj : (Token.timer job).Wf) (hr : (Token.recvMulti fd).Wf) :
    (Token.timer job).encode ≠ (Token.recvMulti fd).encode := by
  intro h
  cases Token.encode_inj hj hr h

/-- **The deadline queue's distinguished timeout token is unambiguous** in
the timeout-token sub-space: any well-formed timeout token encoding to it
*is* it. The queue's `on_timeout` dispatch (matched exactly, before the
sweep test) can therefore never steal another timer's completion. -/
theorem deadline_token_unambiguous {t : TimeoutToken} (ht : t.Wf)
    (h : t.encode = TimeoutToken.deadlineMain.encode) : t = .deadlineMain :=
  TimeoutToken.encode_inj ht trivial h

-- A trace that sets two keys, slides one and fires: the queue moves, so the
-- trace forms above are not statements about an idle model.
def regression_459 : Bool := decide (((DeadlineQueue.init : DeadlineQueue Nat).run
    [.set 1 10, .set 2 20, .set 1 30]).live.length == 2
  )
def regression_460 : Bool := decide ((((DeadlineQueue.init : DeadlineQueue Nat).run
    [.set 1 10, .set 2 20]).step (.fire 15)).2 == [1]
  )

end DN.Dataplane.Flow
