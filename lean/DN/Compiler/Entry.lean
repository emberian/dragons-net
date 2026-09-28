-- SPDX-License-Identifier: AGPL-3.0-or-later
import DN.Compiler.Semantics

/-!
# DN.Compiler.Entry

How a run starts and when it fails, as CakeML's semantics of Pancake says (`ed31510`,
`pancake/semantics/panSemScript.sml`). A run is the call `Call NONE start []` (`semantics_def`);
for a `start` with no parameters, the `Call` clause says: with no clock left the call times out;
otherwise the body runs with one tick less and no locals, a body that ends without a result or
with `Break` or `Continue` is an `Error`, and any other result is passed on with the locals
emptied. The run fails if, for some clock, the call ends in anything but a timeout, an external
call that ends the run, or a return. Running off the end of `main` is therefore a failure.
-/

namespace DN.Compiler.Entry

open DN.Compiler

variable {σ : Type}

/-- `evaluate (Call NONE start [], s)` when `start` is found in the code with no parameters and
`body` is its body. -/
def enter (oracle : Oracle σ) (body : PancakeProg) (s : PancakeState σ) :
    Option Result × PancakeState σ :=
  if s.clock = 0 then (some .timeout, emptyLocals s)
  else
    let r := clampClock (s.clock - 1)
      (PancakeSem oracle body { decClock s with locals := fun _ => none })
    match r.1 with
    | none | some .break_ | some .continue_ => (some .error, r.2)
    | some res => (some res, emptyLocals r.2)

/-- The results that end a run without failing it. -/
def ends : Option Result → Bool
  | some .timeout | some (.finalFFI _) | some (.return_ _) => true
  | _ => false

/-- `semantics s start = Fail`: for some clock, the run ends in something else. -/
def Fails (oracle : Oracle σ) (body : PancakeProg) (s : PancakeState σ) : Prop :=
  ∃ k, ends (enter oracle body { s with clock := k }).1 = false

/-- A body whose every run, whatever the clock, ends as a run may end does not fail. -/
theorem not_fails_of_ends {oracle : Oracle σ} {body : PancakeProg} {s : PancakeState σ}
    (h : ∀ k, ends (enter oracle body { s with clock := k }).1 = true) : ¬ Fails oracle body s := by
  rintro ⟨k, hk⟩
  rw [h k] at hk
  exact Bool.noConfusion hk

/-- A body that ends in a result every time it runs, with no clock or other condition, ends the
call the same way: the call adds only the timeout at clock zero. -/
theorem enter_ends {oracle : Oracle σ} {body : PancakeProg} {s : PancakeState σ}
    (h : ∀ t : PancakeState σ, ends (PancakeSem oracle body t).1 = true) :
    ends (enter oracle body s).1 = true := by
  unfold enter
  split
  · rfl
  · have hb := h { decClock s with locals := fun _ => none }
    simp only [clampClock]
    revert hb
    cases (PancakeSem oracle body { decClock s with locals := fun _ => none }).1 with
    | none => intro hb; exact absurd hb (by decide)
    | some res => cases res <;> first | intro hb; exact absurd hb (by decide) | intro _; rfl

/-! ## Examples

A body that runs off its end fails; one that returns does not; a loop that never ends runs out of
clock, which is not a failure; and with no clock at all, the call times out before the body runs. -/

/-- A state with no memory, for the examples. -/
def bare : PancakeState Unit :=
  { locals := fun _ => none, memory := fun _ => 0, memaddrs := fun _ => false, be := false,
    clock := 1, ffi := (), baseAddr := 0 }

theorem skip_fails : Fails (Oracle.idle (σ := Unit)) .skip bare :=
  ⟨1, by simp [ends, enter, bare, decClock, clampClock, PancakeSem]⟩

theorem return_does_not_fail (s : PancakeState σ) (o : Oracle σ) :
    ¬ Fails o (.ret (.const 0)) s :=
  not_fails_of_ends fun _ => enter_ends fun _ => by simp [ends, PancakeSem, eval]

def regression_815 : Bool := ends (enter (Oracle.idle (σ := Unit)) .skip bare).1 == false
def regression_816 : Bool :=
  (enter (Oracle.idle (σ := Unit)) .skip { bare with clock := 0 }).1 == some .timeout
def regression_817 : Bool :=
  (enter (Oracle.idle (σ := Unit)) (.while_ (.const 1) .skip) { bare with clock := 5 }).1 ==
    some .timeout

end DN.Compiler.Entry
