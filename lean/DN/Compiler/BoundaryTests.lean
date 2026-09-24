-- SPDX-License-Identifier: AGPL-3.0-or-later
import DN.Compiler.Kernels

namespace DN.Compiler.BoundaryTests
open Syntax Lower

private def oracle : Oracle Unit := ⟨fun _ _ _ _ => .final .failed⟩
private def state (alen off len : Nat) : PancakeState Unit :=
  { locals := fun x => match x with
      | "ctrl" => some 0 | "buf" => some 4096 | "len" => some (BitVec.ofNat 64 len)
      | "out" => some 16 | _ => none,
    memory := fun p => if p == 0 then BitVec.ofNat 64 alen else BitVec.ofNat 64 off,
    memaddrs := fun p => p == 0 || p == 8 || p == 16,
    be := false, clock := 2, ffi := (), baseAddr := 0 }

def regionResult (alen off len : Nat) : Option Result := do
  let p ← lower (emitExportFun regionC0)
  (PancakeSem oracle p (state alen off len)).1

-- wrapping_offset_is_rejected
def regression_9001 : Bool := decide (
    regionResult 4096 (2^64-1) 1 = some (.return_ 4294967295) )
-- sign_bit_length_is_rejected
def regression_9002 : Bool := decide (
    regionResult 4096 0 (2^63) = some (.return_ 4294967295) )
-- sign_bit_arena_is_rejected
def regression_9003 : Bool := decide (
    regionResult (2^63) 0 0 = some (.return_ 4294967295) )
-- empty_view_needs_no_buffer_access
def regression_9004 : Bool := decide (
    regionResult 4096 4096 0 = some (.return_ 0) )

/-- The subtraction-form guard establishes the intended natural-number range
without ever needing to form an overflowing word sum. Signed-word agreement
is exercised separately on boundaries in the native lane. -/
theorem range_from_subtraction (alen off len : Nat)
    (ho : off ≤ alen) (hl : len ≤ alen - off) : off + len ≤ alen := by omega

end DN.Compiler.BoundaryTests
