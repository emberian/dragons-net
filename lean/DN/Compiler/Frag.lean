-- SPDX-License-Identifier: AGPL-3.0-or-later
import DN.Compiler.Block
import DN.Compiler.Preservation

/-!
# DN.Compiler.Frag

A function's body proven a fragment at a time. `Frag o xs P P'` says the statements `xs`, with any
statements after them, lower and run from `P` to `P'` before those, the locals they declare given back at
the end of their scope; fragments compose (`frag_append`), and a fragment closed on its own lowers and runs as
its statements alone (`frag_close`, by `fold_of_K`). Declarations, calls and single statements are fragments
(`frag_dec`, `frag_call`, `frag_one`, `frag_oneR`). An expression reading no memory evaluates alike in states
agreeing on what it reads (`eval_noLoad`).
-/

namespace DN.Compiler.Frag

open DN.Compiler DN.Compiler.Wp DN.Compiler.WpRet DN.Compiler.Preservation

variable {σ : Type}

/-- An expression that reads no memory. -/
def NoLoad : PancakeExp → Prop
  | .loadByte _ | .loadWord _ => False
  | .op _ l r | .mul l r | .cmp _ l r | .shiftR l r | .shiftL l r => NoLoad l ∧ NoLoad r
  | .const _ | .var _ | .base => True

/-- **An expression reading no memory nor the locals `hide`** evaluates alike in states that agree on
the other locals and the base. -/
theorem eval_noLoad {hide : String → Prop} {s t : PancakeState σ}
    (hl : ∀ x, ¬ hide x → t.locals x = s.locals x) (hb : t.baseAddr = s.baseAddr) :
    ∀ e, NoLoad e → ExpAvoids hide e → eval t e = eval s e
  | .const _, _, _ => rfl
  | .var x, _, h => hl x h
  | .base, _, _ => by simp [eval, hb]
  | .op _ l r, ⟨nl, nr⟩, ⟨al, ar⟩ => by
    simp only [eval, eval_noLoad hl hb l nl al, eval_noLoad hl hb r nr ar]
  | .mul l r, ⟨nl, nr⟩, ⟨al, ar⟩ => by
    simp only [eval, eval_noLoad hl hb l nl al, eval_noLoad hl hb r nr ar]
  | .cmp c l r, ⟨nl, nr⟩, ⟨al, ar⟩ => by
    cases c <;> simp only [eval, eval_noLoad hl hb l nl al, eval_noLoad hl hb r nr ar]
  | .shiftR l r, ⟨nl, nr⟩, ⟨al, ar⟩ => by
    simp only [eval, eval_noLoad hl hb l nl al, eval_noLoad hl hb r nr ar]
  | .shiftL l r, ⟨nl, nr⟩, ⟨al, ar⟩ => by
    simp only [eval, eval_noLoad hl hb l nl al, eval_noLoad hl hb r nr ar]
  | .loadByte _, h, _ => h.elim
  | .loadWord _, h, _ => h.elim

/-- The locals a block declares at its top, a call's result among them. -/
def declared : List Syntax.PStmt → List String
  | [] => []
  | .dec x _ :: rest | .call x _ _ :: rest => x :: declared rest
  | _ :: rest => declared rest

theorem declared_append : ∀ (xs ys : List Syntax.PStmt), declared (xs ++ ys) = declared xs ++ declared ys
  | [], _ => rfl
  | x :: xs, ys => by cases x <;> simp [declared, declared_append xs ys]

theorem lowerK_append : ∀ (xs ys : List Syntax.PStmt) (k : PancakeProg),
    Block.lowerK (xs ++ ys) k = (Block.lowerK ys k).bind (Block.lowerK xs)
  | [], ys, k => by cases h : Block.lowerK ys k <;> simp [Block.lowerK, h]
  | x :: xs, ys, k => by
    have ih := lowerK_append xs ys k
    cases h : Block.lowerK ys k with
    | none => rw [h] at ih; cases x <;> simp [Block.lowerK, ih]
    | some c => rw [h] at ih; cases x <;> simp [Block.lowerK, ih]

/-- Statements from `P` to `P'` ahead of whatever follows: the locals they declare given back at
the end of their scope. -/
def Frag (o : Oracle σ) (xs : List Syntax.PStmt) (P P' : Assn σ) : Prop :=
  ∀ (k : PancakeProg) (R : Ret) (Q : Assn σ), (∀ u y v, Q u → y ∈ declared xs → Q (restore u y v)) →
    SafeR o P' k R Q → ∃ c, Block.lowerK xs k = some c ∧ SafeR o P c R Q

theorem frag_append {o : Oracle σ} {xs ys : List Syntax.PStmt} {P M P' : Assn σ} (h1 : Frag o xs P M)
    (h2 : Frag o ys M P') : Frag o (xs ++ ys) P P' := by
  intro k R Q hQ hk
  obtain ⟨c2, h2c, h2s⟩ := h2 k R Q (fun u y v hq hy => hQ u y v hq (by
    rw [declared_append]; exact List.mem_append_right _ hy)) hk
  obtain ⟨c1, h1c, h1s⟩ := h1 c2 R Q (fun u y v hq hy => hQ u y v hq (by
    rw [declared_append]; exact List.mem_append_left _ hy)) h2s
  exact ⟨c1, by rw [lowerK_append, h2c]; exact h1c, h1s⟩

theorem frag_conseq {o : Oracle σ} {xs : List Syntax.PStmt} {P P0 P0' P' : Assn σ} (h : Frag o xs P0 P0')
    (hp : ∀ s, P s → P0 s) (hq : ∀ s, P0' s → P' s) : Frag o xs P P' := by
  intro k R Q hQ hk
  obtain ⟨c, hc, hs⟩ := h k R Q hQ (conseq hk hq (fun _ _ h => h) (fun _ h => h))
  exact ⟨c, hc, conseq hs hp (fun _ _ h => h) (fun _ h => h)⟩

theorem lowerK_cons {x : Syntax.PStmt} {a : PancakeProg} (hx : Lower.lowerStmt1 x = some a) (hd : x.isDec = false)
    {rest : List Syntax.PStmt} {k r : PancakeProg} (hr : Block.lowerK rest k = some r) :
    Block.lowerK (x :: rest) k = some (.seq a r) := by
  cases x <;> simp_all [Block.lowerK, Syntax.PStmt.isDec]

theorem lowerK_dec {x : String} {e : Syntax.PExpr} {E : PancakeExp} (he : Lower.lowerExp e = some E)
    {rest : List Syntax.PStmt} {k r : PancakeProg} (hr : Block.lowerK rest k = some r) :
    Block.lowerK (.dec x e :: rest) k = some (.dec x E r) := by
  simp [Block.lowerK, he, hr]

theorem lowerK_one {x : Syntax.PStmt} {a : PancakeProg} (hx : Lower.lowerStmt1 x = some a) (hd : x.isDec = false)
    (k : PancakeProg) : Block.lowerK [x] k = some (.seq a k) :=
  lowerK_cons hx hd rfl

/-- A statement that declares nothing and never returns, shown from `P` to `P'`. -/
theorem frag_one {o : Oracle σ} {x : Syntax.PStmt} {a : PancakeProg} {P P' : Assn σ}
    (hx : Lower.lowerStmt1 x = some a) (hd : x.isDec = false) (hr : noRet a = true) (hP' : Safe.ClockFree P')
    (h : Safe.Safe o P a P') : Frag o [x] P P' := by
  intro k R Q _ hk
  exact ⟨.seq a k, lowerK_one hx hd k, seq (ofSafe R hr h) hk hP'⟩

theorem dec_congr (o : Oracle σ) (x : String) (e : PancakeExp) {q q' : PancakeProg}
    (h : ∀ s, PancakeSem o q s = PancakeSem o q' s) (s : PancakeState σ) :
    PancakeSem o (.dec x e q) s = PancakeSem o (.dec x e q') s := by
  rw [PancakeSem.eq_2, PancakeSem.eq_2]
  simp only [h]

theorem decCall_congr (o : Oracle σ) (rt f : String) (args : List PancakeExp) {q q' : PancakeProg}
    (h : ∀ s, PancakeSem o q s = PancakeSem o q' s) (s : PancakeState σ) :
    PancakeSem o (.decCall rt f args q) s = PancakeSem o (.decCall rt f args q') s := by
  rw [PancakeSem.eq_11, PancakeSem.eq_11]
  simp only [h]

theorem lowerK_cons_inv {x : Syntax.PStmt} (hd : x.isDec = false) {rest : List Syntax.PStmt} {k c : PancakeProg}
    (h : Block.lowerK (x :: rest) k = some c) :
    ∃ a r, Lower.lowerStmt1 x = some a ∧ Block.lowerK rest k = some r ∧ c = .seq a r := by
  cases ha : Lower.lowerStmt1 x with
  | none => cases x <;> simp_all [Block.lowerK, Syntax.PStmt.isDec]
  | some a =>
    cases hr : Block.lowerK rest k with
    | none => cases x <;> simp_all [Block.lowerK, Syntax.PStmt.isDec]
    | some r => exact ⟨a, r, rfl, rfl, by cases x <;> simp_all [Block.lowerK, Syntax.PStmt.isDec]⟩

theorem lowerK_dec_inv {n : String} {v : Syntax.PExpr} {rest : List Syntax.PStmt} {k c : PancakeProg}
    (h : Block.lowerK (.dec n v :: rest) k = some c) :
    ∃ v' r, Lower.lowerExp v = some v' ∧ Block.lowerK rest k = some r ∧ c = .dec n v' r := by
  cases hv : Lower.lowerExp v with
  | none => simp [Block.lowerK, hv] at h
  | some v' =>
    cases hr : Block.lowerK rest k with
    | none => simp [Block.lowerK, hv, hr] at h
    | some r => exact ⟨v', r, rfl, rfl, by simp [Block.lowerK, hv, hr] at h; exact h.symm⟩

theorem lowerK_call_inv {rt f : String} {as : List Syntax.PExpr} {rest : List Syntax.PStmt} {k c : PancakeProg}
    (h : Block.lowerK (.call rt f as :: rest) k = some c) :
    ∃ a r, Lower.lowerArgs as = some a ∧ Block.lowerK rest k = some r ∧ c = .decCall rt f a r := by
  cases ha : Lower.lowerArgs as with
  | none => simp [Block.lowerK, ha] at h
  | some a =>
    cases hr : Block.lowerK rest k with
    | none => simp [Block.lowerK, ha, hr] at h
    | some r => exact ⟨a, r, rfl, rfl, by simp [Block.lowerK, ha, hr] at h; exact h.symm⟩

theorem fold_cons_K (o : Oracle σ) {x : Syntax.PStmt} (hd : x.isDec = false) {rest : List Syntax.PStmt}
    {c' : PancakeProg} (h : Block.lowerK (x :: rest) .skip = some c')
    (ih : ∀ {r : PancakeProg}, Block.lowerK rest .skip = some r →
      ∃ c, Lower.lowerStmtsFold rest = some c ∧ ∀ s, PancakeSem o c s = PancakeSem o r s) :
    ∃ c, Lower.lowerStmtsFold (x :: rest) = some c ∧ ∀ s, PancakeSem o c s = PancakeSem o c' s := by
  obtain ⟨a, r, ha, hr, rfl⟩ := lowerK_cons_inv hd h
  cases rest with
  | nil =>
    simp only [Block.lowerK, Option.some.injEq] at hr
    subst hr
    refine ⟨a, ha, fun s => ?_⟩
    rw [Components.seq_run]
    rcases hp : PancakeSem o a s with ⟨_ | r, t⟩ <;> simp [PancakeSem.eq_1]
  | cons y ys =>
    obtain ⟨c0, hc0, hs⟩ := ih hr
    exact ⟨_, Block.fold_cons ha hd (by simp) hc0, fun s => Block.seq_congr o a hs s⟩

/-- **A block lowered on its own runs as it does with nothing after it.** -/
theorem fold_of_K (o : Oracle σ) : ∀ (xs : List Syntax.PStmt) {c' : PancakeProg}, Block.lowerK xs .skip = some c' →
    ∃ c, Lower.lowerStmtsFold xs = some c ∧ ∀ s, PancakeSem o c s = PancakeSem o c' s
  | [], c', h => by
    simp only [Block.lowerK, Option.some.injEq] at h
    exact ⟨.skip, rfl, fun s => by rw [h]⟩
  | .dec n v :: rest, c', h => by
    obtain ⟨v', r, hv, hr, rfl⟩ := lowerK_dec_inv h
    cases rest with
    | nil =>
      simp only [Block.lowerK, Option.some.injEq] at hr
      subst hr
      exact ⟨_, by simp [Lower.lowerStmtsFold, Lower.lowerStmt1, hv], fun _ => rfl⟩
    | cons y ys =>
      obtain ⟨c0, hc0, hs⟩ := fold_of_K o (y :: ys) hr
      exact ⟨_, Block.fold_dec hv (by simp) hc0, dec_congr o n v' hs⟩
  | .call rt f as :: rest, c', h => by
    obtain ⟨a, r, ha, hr, rfl⟩ := lowerK_call_inv h
    cases rest with
    | nil =>
      simp only [Block.lowerK, Option.some.injEq] at hr
      subst hr
      exact ⟨_, by simp [Lower.lowerStmtsFold, Lower.lowerStmt1, ha], fun _ => rfl⟩
    | cons y ys =>
      obtain ⟨c0, hc0, hs⟩ := fold_of_K o (y :: ys) hr
      exact ⟨_, by rw [Preservation.fold_call (by simp), ha, hc0], decCall_congr o rt f a hs⟩
  | .assign _ _ :: rest, _, h | .store _ _ :: rest, _, h | .storeb _ _ :: rest, _, h | .ffi _ _ :: rest, _, h
  | .ret _ :: rest, _, h | .ite _ _ _ :: rest, _, h | .while _ _ :: rest, _, h =>
    fold_cons_K o rfl h (fun hr => fold_of_K o rest hr)

/-- **A fragment closed**: as it lowers on its own, from `P` to `P'`, the locals it declares given back. -/
theorem frag_close {o : Oracle σ} {xs : List Syntax.PStmt} {P P' : Assn σ} (h : Frag o xs P P')
    (hQ : ∀ u y v, P' u → y ∈ declared xs → P' (restore u y v)) (R : Ret) :
    ∃ c, Lower.lowerStmtsFold xs = some c ∧ SafeR o P c R P' := by
  obtain ⟨c', hc', hs'⟩ := h .skip R P' hQ (WpRet.skip o P' R)
  obtain ⟨c, hc, he⟩ := fold_of_K o xs hc'
  exact ⟨c, hc, fun s hs => by rw [he]; exact hs' s hs⟩

/-- A statement that declares nothing, shown for every return. -/
theorem frag_oneR {o : Oracle σ} {x : Syntax.PStmt} {a : PancakeProg} {P P' : Assn σ}
    (hx : Lower.lowerStmt1 x = some a) (hd : x.isDec = false) (hP' : Safe.ClockFree P')
    (h : ∀ R, SafeR o P a R P') : Frag o [x] P P' := by
  intro k R Q _ hk
  exact ⟨.seq a k, lowerK_one hx hd k, seq (h R) hk hP'⟩

/-- A declaration, its value from `P`. -/
theorem frag_dec (o : Oracle σ) {x : String} {e : Syntax.PExpr} {E : PancakeExp} (he : Lower.lowerExp e = some E)
    {P P' : Assn σ} (h : ∀ s, P s → ∃ v, eval s E = some v ∧ P' { s with locals := setLocal s.locals x v }) :
    Frag o [.dec x e] P P' := by
  intro k R Q hQ hk
  exact ⟨.dec x E k, by simp [Block.lowerK, he], dec h hk (fun _ t _ hq => hQ t x _ hq (by simp [declared]))⟩

/-- A call, its callee shown from the caller's state. -/
theorem frag_call (o : Oracle σ) {rt f : String} {as : List Syntax.PExpr} {args : List PancakeExp}
    (has : Lower.lowerArgs as = some args) {P P' : Assn σ} {body : PancakeProg}
    {Pc : PancakeState σ → Assn σ} {Rc : PancakeState σ → Ret}
    (hbody : ∀ s, P s → SafeR o (Pc s) body (Rc s) (fun _ => False))
    (hcall : ∀ s, P s → ∃ vs lc, evalArgs s args = some vs ∧ lookupCode s.code f vs = some (body, lc) ∧
      Pc s { decClock s with locals := lc })
    (hret : ∀ s t v, P s → Rc s v t.memory → Safe.Same s t → P' { t with locals := setLocal s.locals rt v }) :
    Frag o [.call rt f as] P P' := by
  intro k R Q hQ hk
  exact ⟨.decCall rt f args k, by simp [Block.lowerK, has], Block.decCallR_dep hbody hcall hret hk
    (fun s t _ hq => hQ t rt _ hq (by simp [declared]))⟩

/-! ## The premises can hold -/

theorem noLoad_witness : NoLoad (.const 0) := trivial

theorem frag_witness : Frag (σ := Unit) Oracle.idle [] (fun _ => True) (fun _ => True) :=
  fun k _ _ _ h => ⟨k, rfl, h⟩

end DN.Compiler.Frag
