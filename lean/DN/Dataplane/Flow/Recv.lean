-- SPDX-License-Identifier: AGPL-3.0-or-later
/-
# DN.Dataplane.Flow.Recv

Retained compiler/dataplane development and regression examples.
Source provenance is in docs/provenance.json; assurance boundaries are in
docs/assurance.md. HTTP examples are compiler workloads, not dn server features.
-/


namespace DN.Dataplane.Flow

/-- Per-socket receive arming. -/
inductive RecvArming where
  /-- Delivery active: accumulated bytes flow to the handler. -/
  | armed
  /-- Delivery suppressed: bytes park in the kernel buffer, the TCP window
  closes, the peer slows. -/
  | parked
  deriving Repr, DecidableEq, Inhabited

/-- Per-socket receive state, over an abstract byte type `α`.

`arming` and `kernelBuf` are the operational state; `delivered` and
`arrived` are ghost ledgers for the conservation theorem. -/
structure RecvConn (α : Type u) where
  /-- Is delivery armed or parked? -/
  arming : RecvArming
  /-- Abstract content of the kernel TCP receive buffer. -/
  kernelBuf : List α
  /-- Ghost: bytes handed to the handler, in delivery order. -/
  delivered : List α
  /-- Ghost: every byte the network deposited, in arrival order. -/
  arrived : List α

/-- A fresh socket: armed, everything empty. -/
def RecvConn.init : RecvConn α := ⟨.armed, [], [], []⟩

/-- Events driving one socket's receive path. -/
inductive RecvEv (α : Type u) where
  /-- The network deposits `data` into the kernel buffer. Never gated:
  the kernel accepts regardless of arming (the window, not the arming
  bit, is what eventually stops the peer). -/
  | arrive (data : List α)
  /-- The kernel delivers up to `n` buffered bytes to the handler —
  only when armed. On a parked socket this is a no-op: the enforcement. -/
  | deliver (n : Nat)
  /-- Park the socket (cancel receive): suppress delivery. -/
  | park
  /-- Resume the socket: re-arm delivery. -/
  | resume

/-- One step of the receive machine. -/
def RecvConn.step (s : RecvConn α) : RecvEv α → RecvConn α
  | .arrive data =>
    { s with kernelBuf := s.kernelBuf ++ data, arrived := s.arrived ++ data }
  | .deliver n =>
    match s.arming with
    | .parked => s
    | .armed =>
      { s with delivered := s.delivered ++ s.kernelBuf.take n,
               kernelBuf := s.kernelBuf.drop n }
  | .park => { s with arming := .parked }
  | .resume => { s with arming := .armed }

/-- Run a trace of events. -/
def RecvConn.run (s : RecvConn α) : List (RecvEv α) → RecvConn α
  | [] => s
  | e :: es => (s.step e).run es

/-- The machine invariant: **conservation** — delivered bytes followed by
kernel-held bytes are exactly the arrivals, in order. -/
def RecvConn.Inv (s : RecvConn α) : Prop :=
  s.delivered ++ s.kernelBuf = s.arrived

theorem RecvConn.init_inv : (RecvConn.init : RecvConn α).Inv := rfl

/-- **Preservation**: every event — arrival, delivery, park, resume —
preserves conservation. In particular parking loses nothing and arrival
while parked loses nothing. -/
theorem RecvConn.step_inv (s : RecvConn α) (e : RecvEv α) (h : s.Inv) :
    (s.step e).Inv := by
  have h' : s.delivered ++ s.kernelBuf = s.arrived := h
  cases e with
  | arrive data => simp [step, Inv, ← h']
  | deliver n =>
    cases ha : s.arming with
    | parked => simpa [step, ha] using h
    | armed => simp [step, ha, Inv, List.take_append_drop, ← h']
  | park => simpa [step, Inv] using h
  | resume => simpa [step, Inv] using h

/-- The invariant holds along every trace from every invariant state. -/
theorem RecvConn.run_inv (s : RecvConn α) (es : List (RecvEv α)) (h : s.Inv) :
    (s.run es).Inv := by
  induction es generalizing s with
  | nil => exact h
  | cons e es ih => exact ih _ (s.step_inv e h)

/-- The invariant holds along every trace from a fresh socket. -/
theorem RecvConn.run_init_inv (es : List (RecvEv α)) :
    ((RecvConn.init : RecvConn α).run es).Inv :=
  run_inv _ es init_inv

/-- **The enforcement.** Delivery against a parked socket is a strict
no-op: nothing reaches the handler, nothing leaves the kernel buffer. -/
theorem RecvConn.parked_deliver_noop (s : RecvConn α)
    (hp : s.arming = .parked) (n : Nat) :
    s.step (.deliver n) = s := by
  simp [step, hp]

/-- **Parking loses zero bytes.** Bytes arriving on a parked socket land in
the kernel buffer verbatim — appended in order, nothing delivered, nothing
dropped. (The buffer growth is what closes the TCP window.) -/
theorem RecvConn.parked_arrive_accumulates (s : RecvConn α)
    (data : List α) :
    (s.step (.arrive data)).kernelBuf = s.kernelBuf ++ data ∧
    (s.step (.arrive data)).delivered = s.delivered := by
  simp [step]

/-- **Delivery order.** The delivered stream is always a prefix of the
arrival stream: no reorder, no invention, across any park/resume pattern. -/
theorem RecvConn.delivered_prefix (s : RecvConn α) (h : s.Inv) :
    ∃ rest, s.delivered ++ rest = s.arrived :=
  ⟨s.kernelBuf, h⟩

/-- **Resume drains exactly the parked bytes.** After a resume, a delivery
of at least the buffered length hands the handler precisely the bytes that
accumulated while parked, in arrival order, and empties the kernel buffer. -/
theorem RecvConn.resume_drain (s : RecvConn α) (n : Nat)
    (hn : s.kernelBuf.length ≤ n) :
    ((s.step .resume).step (.deliver n)).delivered
        = s.delivered ++ s.kernelBuf ∧
    ((s.step .resume).step (.deliver n)).kernelBuf = [] := by
  simp [step, List.take_of_length_le hn, List.drop_of_length_le hn]

/-- Parking is idempotent, and so is resuming. -/
theorem RecvConn.park_idem (s : RecvConn α) :
    (s.step .park).step .park = s.step .park := rfl

theorem RecvConn.resume_idem (s : RecvConn α) :
    (s.step .resume).step .resume = s.step .resume := rfl

end DN.Dataplane.Flow
