-- SPDX-License-Identifier: AGPL-3.0-or-later
import DN.Compiler.Lower

/-!
# DN.Compiler.LowerBridge

What `lower` makes of a list of byte stores: the address model, the store-list
model, and the bridge lemma that the lowered program is that model.
-/

namespace DN.Compiler.LowerBridge

open DN.Compiler.Syntax (PExpr PStmt PFun POp atOff v n eAdd)
open DN.Compiler
open DN.Compiler.Lower (lowerExp lowerStmt1 lowerStmtsFold lower)

/-- `st8 dst+i, b;` for each `(i, b)`: a byte string written at consecutive offsets. -/
def storesInto (dst : String) (bs : List Nat) : List PStmt :=
  ((List.range bs.length).zip bs).map (fun p => PStmt.storeb (atOff (v dst) p.1) (n p.2))

/-! ## 1. The address model — what `lower` makes of `atOff (v dst) k`

`storesInto` addresses byte `k` as `atOff (v dst) k`, which is `v dst` at offset
`0` (the `+0` is dropped by `atOff`) and `eAdd (v dst) (n k)` otherwise. `lower`
sends the former to `.var dst` and the latter to `.op .add (.var dst) (.const k)`.
`addrModel` is that image, and `lowerExp_atOff` proves `lower` computes it. -/

/-- The `lower`-image of the `k`-th store address `atOff (v dst) k`. -/
def addrModel (dst : String) (k : Nat) : PancakeExp :=
  if k == 0 then .var dst
  else .op .add (.var dst) (.const (BitVec.ofNat 64 k))

/-- `lower` sends the emitted store address to `addrModel`, for every offset. The
`k = 0` case uses `atOff`'s `+0` drop; the `k = k'+1` case lowers the `.binop .add`
to `.op .add`. -/
theorem lowerExp_atOff (dst : String) (k : Nat) :
    lowerExp (atOff (v dst) k) = some (addrModel dst k) := by
  cases k with
  | zero =>
    simp [atOff, addrModel, v, lowerExp]
  | succ k' =>
    simp [atOff, addrModel, eAdd, v, n, lowerExp]

/-- `lower` sends the emitted byte value `n b` to `.const (b : word)`. -/
theorem lowerExp_n (b : Nat) :
    lowerExp (n b) = some (.const (BitVec.ofNat 64 b)) := by
  simp only [n, lowerExp]

/-! ## 2. The store-list model and the bridge lemma

`storesIntoL` is `storesInto`'s body isolated over an arbitrary index/byte list
`ps` (so `storesInto dst bs = storesIntoL dst ((range |bs|).zip bs)`, definitional).
`storesModel` is the model program `lower` produces from it: a right-nested `Seq`
of `.storeByte` nodes matching `lowerStmtsFold`'s own shape (singleton without a
trailing `Skip`). The bridge is proved by induction on `ps`. -/

/-- The emitted store list over an explicit `(offset, byte)` list. Definitionally
`storesInto dst bs = storesIntoL dst ((List.range bs.length).zip bs)`. -/
def storesIntoL (dst : String) (ps : List (Nat × Nat)) : List PStmt :=
  ps.map (fun p => PStmt.storeb (atOff (v dst) p.1) (n p.2))

/-- The `lower`-image of `storesIntoL`: `.storeByte (addrModel dst off) (const b)`
per entry, right-nested, matching `lowerStmtsFold` (a lone entry lowers to a bare
`.storeByte`, no trailing `.skip`). -/
def storesModel (dst : String) : List (Nat × Nat) → PancakeProg
  | []      => .skip
  | [p]     => .storeByte (addrModel dst p.1) (.const (BitVec.ofNat 64 p.2))
  | p :: ps => .seq (.storeByte (addrModel dst p.1) (.const (BitVec.ofNat 64 p.2)))
                    (storesModel dst ps)

/-- Lowering a single emitted store. -/
theorem lowerStmt1_storeb_off (dst : String) (p : Nat × Nat) :
    lowerStmt1 (PStmt.storeb (atOff (v dst) p.1) (n p.2))
      = some (.storeByte (addrModel dst p.1) (.const (BitVec.ofNat 64 p.2))) := by
  rw [lowerStmt1]
  rw [lowerExp_atOff, lowerExp_n]

/-- **THE BRIDGE (generic).** `lower`'s statement folder run on the exact `PStmt`
list `storesInto` emits equals the explicit `.storeByte` model program, for ALL
index/byte lists. Induction on `ps`; the cons step splits on whether the tail is
empty (matching `lowerStmtsFold`'s singleton special case). Every emitted element
is a `.storeb` — never a `.dec` — so the `dec`-scoping branch of `lowerStmtsFold`
never fires. -/
theorem storesIntoL_lowers (dst : String) :
    ∀ ps : List (Nat × Nat),
      lowerStmtsFold (storesIntoL dst ps) = some (storesModel dst ps)
  | [] => rfl
  | [p] => by
      show lowerStmtsFold [PStmt.storeb (atOff (v dst) p.1) (n p.2)]
          = some (storesModel dst [p])
      rw [lowerStmtsFold]
      exact lowerStmt1_storeb_off dst p
  | p :: q :: ps => by
      have ih := storesIntoL_lowers dst (q :: ps)
      have h1 := lowerStmt1_storeb_off dst p
      show (match lowerStmt1 (PStmt.storeb (atOff (v dst) p.1) (n p.2)),
                  lowerStmtsFold (storesIntoL dst (q :: ps)) with
            | some s', some r' => some (PancakeProg.seq s' r')
            | _, _             => none)
          = some (storesModel dst (p :: q :: ps))
      rw [h1, ih]
      rfl

/-- **THE BRIDGE, on the real emitter.** `storesInto dst bs` is definitionally
`storesIntoL dst ((range |bs|).zip bs)`, so the emitted per-byte `st8` head lowers
to a named model `.storeByte` program for EVERY byte list `bs`. -/
theorem storesInto_lowers (dst : String) (bs : List Nat) :
    lowerStmtsFold (storesInto dst bs)
      = some (storesModel dst ((List.range bs.length).zip bs)) := by
  show lowerStmtsFold (storesIntoL dst ((List.range bs.length).zip bs))
      = some (storesModel dst ((List.range bs.length).zip bs))
  exact storesIntoL_lowers dst _

/-! ## 3. Non-vacuity — the bridge lands a REAL, non-trivial program

The emitted head is not empty and not a stub: for a non-empty byte list the model
is a genuine `.storeByte` chain, and its store count equals the byte count. -/

/-- Count the `.storeByte` nodes of a model program (the emitted head is all
byte stores; word stores are not counted). -/
def storeByteCount : PancakeProg → Nat
  | .storeByte _ _ => 1
  | .seq c1 c2     => storeByteCount c1 + storeByteCount c2
  | _              => 0

/-- The model is exactly `|ps|` byte stores — one per emitted `st8`, no stub. -/
theorem storeByteCount_storesModel (dst : String) :
    ∀ ps : List (Nat × Nat), storeByteCount (storesModel dst ps) = ps.length
  | []          => rfl
  | [_]         => rfl
  | _ :: q :: ps => by
      show 1 + storeByteCount (storesModel dst (q :: ps)) = _
      rw [storeByteCount_storesModel dst (q :: ps)]
      simp [List.length_cons]
      omega

/-- On the real emitter: the lowered head has exactly `|bs|` byte stores. -/
theorem storesInto_storeByteCount (dst : String) (bs : List Nat) :
    storeByteCount (storesModel dst ((List.range bs.length).zip bs)) = bs.length := by
  rw [storeByteCount_storesModel]
  rw [List.length_zip, List.length_range, Nat.min_self]

end DN.Compiler.LowerBridge
