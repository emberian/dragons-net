-- SPDX-License-Identifier: AGPL-3.0-or-later
import DN.Compiler.Components
import DN.Compiler.WpRet

/-!
# DN.Compiler.Block

A function's body, assembled from parts proved on their own. A fragment followed by more runs as itself then the rest
when its top declares and calls nothing (`fold_append`). Declarations scope over the rest (`fold_dec`, `fold_decs`); a
call takes what the callee gives back (`decCallR`, `decCallM`).
-/

namespace DN.Compiler.Block

open DN.Compiler DN.Compiler.Syntax DN.Compiler.Components DN.Compiler.WpRet DN.Compiler.Safe
  DN.Compiler.Entry

variable {σ : Type}

/-- A statement that is not a declaration, in front of more statements, lowers into a sequence. -/
theorem fold_cons {x : PStmt} {a b : PancakeProg} (hx : Lower.lowerStmt1 x = some a)
    (hnd : x.isDec = false) {rest : List PStmt} (hne : rest ≠ [])
    (hrest : Lower.lowerStmtsFold rest = some b) : Lower.lowerStmtsFold (x :: rest) = some (.seq a b) := by
  cases rest with
  | nil => exact absurd rfl hne
  | cons y ys =>
    cases x with
    | dec nm e => simp [PStmt.isDec] at hnd
    | call r f as => simp [PStmt.isDec] at hnd
    | _ => simp [Lower.lowerStmtsFold, hx, hrest]

/-- What follows a statement matters only by how it runs. -/
theorem seq_congr (o : Oracle σ) (p : PancakeProg) {q q' : PancakeProg}
    (h : ∀ s, PancakeSem o q s = PancakeSem o q' s) (s : PancakeState σ) :
    PancakeSem o (.seq p q) s = PancakeSem o (.seq p q') s := by
  rw [seq_run, seq_run]
  cases (PancakeSem o p s).1 with
  | none => exact h _
  | some r => rfl

/-- **A block then more runs as the block, then the rest**, if its top declares and calls nothing. -/
theorem fold_append (o : Oracle σ) :
    ∀ (xs ys : List PStmt), xs ≠ [] → ys ≠ [] → (∀ x ∈ xs, x.isDec = false) →
      ∀ {a b : PancakeProg}, Lower.lowerStmtsFold xs = some a → Lower.lowerStmtsFold ys = some b →
        ∃ c, Lower.lowerStmtsFold (xs ++ ys) = some c ∧
          ∀ s, PancakeSem o c s = PancakeSem o (.seq a b) s
  | [], _, h, _, _, _, _, _, _ => absurd rfl h
  | [x], ys, _, hy, hnd, a, b, ha, hb => by
    have hx : Lower.lowerStmt1 x = some a := by
      cases x <;> simpa [Lower.lowerStmtsFold] using ha
    exact ⟨_, fold_cons hx (hnd x (by simp)) hy hb, fun _ => rfl⟩
  | x :: x' :: xs, ys, _, hy, hnd, a, b, ha, hb => by
    have hx0 := hnd x (by simp)
    cases hl1 : Lower.lowerStmt1 x with
    | none =>
      cases x <;> simp_all [Lower.lowerStmtsFold, PStmt.isDec]
    | some a1 =>
      cases hl2 : Lower.lowerStmtsFold (x' :: xs) with
      | none =>
        cases x <;> simp_all [Lower.lowerStmtsFold, PStmt.isDec]
      | some a2 =>
        have hfa : Lower.lowerStmtsFold (x :: x' :: xs) = some (.seq a1 a2) :=
          fold_cons hl1 hx0 (by simp) hl2
        rw [hfa] at ha
        cases ha
        obtain ⟨c', hc', hrun⟩ := fold_append o (x' :: xs) ys (by simp) hy
          (fun z hz => hnd z (List.mem_cons_of_mem _ hz)) hl2 hb
        refine ⟨.seq a1 c', fold_cons hl1 hx0 (by simp) hc', fun s => ?_⟩
        rw [seq_congr o a1 hrun, seq_assoc]

/-- A declaration in front of more statements lowers into a declaration over them. -/
theorem fold_dec {x : String} {e : PExpr} {e' : PancakeExp} (he : Lower.lowerExp e = some e')
    {rest : List PStmt} (hne : rest ≠ []) {r : PancakeProg} (hr : Lower.lowerStmtsFold rest = some r) :
    Lower.lowerStmtsFold (.dec x e :: rest) = some (.dec x e' r) := by
  cases rest with
  | nil => exact absurd rfl hne
  | cons y ys => simp [Lower.lowerStmtsFold, he, hr]

/-- Locals declared from zero in front of more statements lower into `WpRet.zeros`. -/
theorem fold_zeros (xs : List String) {rest : List PStmt} (hne : rest ≠ []) {r : PancakeProg}
    (hr : Lower.lowerStmtsFold rest = some r) :
    Lower.lowerStmtsFold (xs.map (fun x => PStmt.dec x (n 0)) ++ rest) = some (WpRet.zeros xs r) := by
  induction xs with
  | nil => exact hr
  | cons x xs ih => exact fold_dec rfl (by simp [hne]) ih

/-- Declarations ahead of a program, each with its value. -/
def decs : List (String × PancakeExp) → PancakeProg → PancakeProg
  | [], c => c
  | (x, e) :: ds, c => .dec x e (decs ds c)

/-- Declarations' values as they lower, if each does. -/
def lowerDecs : List (String × PExpr) → Option (List (String × PancakeExp))
  | [] => some []
  | (x, e) :: ds =>
    match Lower.lowerExp e, lowerDecs ds with
    | some e', some ds' => some ((x, e') :: ds')
    | _, _ => none

/-- Declarations in front of more statements lower into `decs`, each value as it lowers. -/
theorem fold_decs :
    ∀ (ds : List (String × PExpr)) {ds' : List (String × PancakeExp)}, lowerDecs ds = some ds' →
      ∀ {rest : List PStmt}, rest ≠ [] → ∀ {r : PancakeProg}, Lower.lowerStmtsFold rest = some r →
        Lower.lowerStmtsFold (ds.map (fun d => PStmt.dec d.1 d.2) ++ rest) = some (decs ds' r)
  | [], _, h, _, _, _, hr => by simp only [lowerDecs, Option.some.injEq] at h; subst h; exact hr
  | (x, e) :: ds, ds', h, rest, hne, r, hr => by
    simp only [lowerDecs] at h
    cases he : Lower.lowerExp e with
    | none => rw [he] at h; cases h
    | some e' =>
      cases hd : lowerDecs ds with
      | none => rw [he, hd] at h; cases h
      | some ds'' =>
        rw [he, hd] at h
        cases h
        exact fold_dec he (by simp [hne]) (fold_decs ds hd hne hr)

/-- The callee found for a call: its body, its parameters bound to the arguments. -/
theorem lookupCode_of {code : String → Option (List String × PancakeProg)} {f : String}
    {ps : List String} {body : PancakeProg} (hf : code f = some (ps, body)) (hnd : ps.Nodup)
    {vs : List Value} (hl : ps.length = vs.length) :
    lookupCode code f vs = some (body, fun k => (ps.zip vs).lookup k) := by
  simp [lookupCode, hf, hnd, hl]

/-- **A call takes what the callee is shown to give back.** A callee that never finishes normally, giving back as `Rc`,
hands value and memory to the caller's rest. That rest runs with the caller's locals and `rt` bound, memory, clock and
world as the callee left. -/
theorem decCallR {o : Oracle σ} {P Q P' Q' Pc : PancakeState σ → Prop} {R Rc : Ret}
    {rt f : String} {args : List PancakeExp} {cont body : PancakeProg}
    (hbody : SafeR o Pc body Rc (fun _ => False))
    (hcall : ∀ s, P s → ∃ vs lc, evalArgs s args = some vs ∧
      lookupCode s.code f vs = some (body, lc) ∧ Pc { decClock s with locals := lc })
    (hret : ∀ s t v, P s → Rc v t.memory → Same s t →
      P' { t with locals := setLocal s.locals rt v })
    (hcont : SafeR o P' cont R Q')
    (hpost : ∀ s t, P s → Q' t → Q { t with locals := resVar t.locals rt (s.locals rt) }) :
    SafeR o P (.decCall rt f args cont) R Q := by
  intro s hs
  obtain ⟨vs, lc, hv, hl, hpc⟩ := hcall s hs
  rw [PancakeSem.eq_11]
  simp only [hv, hl]
  by_cases h0 : s.clock = 0
  · simp only [h0, if_true]; rfl
  · simp only [h0, if_false]
    have k := hbody _ hpc
    have hsame := sem_same o _ body { decClock s with locals := lc } (Nat.le_refl _)
    have hcl := clamp_run o body { decClock s with locals := lc }
    rw [show s.clock - 1 = ({ decClock s with locals := lc } : PancakeState σ).clock from rfl, hcl]
    revert k hsame
    cases PancakeSem o body { decClock s with locals := lc } with
    | mk r t =>
      intro k hsame
      cases r with
      | none => exact k.elim
      | some res =>
        cases res with
        | return_ v =>
          have hs' : Same s t := ⟨hsame.1, hsame.2.1, hsame.2.2.1, hsame.2.2.2⟩
          have k2 := hcont _ (hret s t v hs k hs')
          simp only
          revert k2
          cases PancakeSem o cont { t with locals := setLocal s.locals rt v } with
          | mk r2 t2 => cases r2 with
            | none => exact hpost s t2 hs
            | some res2 => cases res2 <;> exact id
        | _ => first | (exfalso; simp [OkR, ends] at k; done) | (simp [callEnded, OkR, ends])

/-- …a callee whose return is stated against its entry memory, as a frame is: the caller's memory
at the call. -/
theorem decCallM {o : Oracle σ} {P Q P' Q' : PancakeState σ → Prop}
    {Pc : PancakeState σ → Prop} {R : Ret} {Rc : (Word → Word) → Ret}
    {rt f : String} {args : List PancakeExp} {cont body : PancakeProg}
    (hbody : ∀ m0, SafeR o (fun s => Pc s ∧ s.memory = m0) body (Rc m0) (fun _ => False))
    (hcall : ∀ s, P s → ∃ vs lc, evalArgs s args = some vs ∧
      lookupCode s.code f vs = some (body, lc) ∧ Pc { decClock s with locals := lc })
    (hret : ∀ s t v, P s → Rc s.memory v t.memory → Same s t →
      P' { t with locals := setLocal s.locals rt v })
    (hcont : SafeR o P' cont R Q')
    (hpost : ∀ s t, P s → Q' t → Q { t with locals := resVar t.locals rt (s.locals rt) }) :
    SafeR o P (.decCall rt f args cont) R Q := fun s hs =>
  decCallR (P := fun u => P u ∧ u.memory = s.memory) (hbody s.memory)
    (fun u ⟨hu, hm⟩ => by
      obtain ⟨vs, lc, h1, h2, h3⟩ := hcall u hu
      exact ⟨vs, lc, h1, h2, h3, hm⟩)
    (fun u t v ⟨hu, hm⟩ hr hs' => hret u t v hu (hm ▸ hr) hs') hcont
    (fun u t ⟨hu, _⟩ hq => hpost u t hu hq) s ⟨hs, rfl⟩

/-- …and a callee whose premise and result depend on the caller's state at the call. -/
theorem decCallR_dep {o : Oracle σ} {P Q P' Q' : PancakeState σ → Prop} {R : Ret}
    {Pc : PancakeState σ → PancakeState σ → Prop} {Rc : PancakeState σ → Ret}
    {rt f : String} {args : List PancakeExp} {cont body : PancakeProg}
    (hbody : ∀ s, P s → SafeR o (Pc s) body (Rc s) (fun _ => False))
    (hcall : ∀ s, P s → ∃ vs lc, evalArgs s args = some vs ∧
      lookupCode s.code f vs = some (body, lc) ∧ Pc s { decClock s with locals := lc })
    (hret : ∀ s t v, P s → Rc s v t.memory → Same s t →
      P' { t with locals := setLocal s.locals rt v })
    (hcont : SafeR o P' cont R Q')
    (hpost : ∀ s t, P s → Q' t → Q { t with locals := resVar t.locals rt (s.locals rt) }) :
    SafeR o P (.decCall rt f args cont) R Q := by
  intro s0 hs0
  exact decCallR (P := fun s => s = s0) (hbody s0 hs0)
    (fun s hs => by subst hs; exact hcall s hs0)
    (fun s t v hs hr hst => by subst hs; exact hret s t v hs0 hr hst) hcont
    (fun s t hs hq => by subst hs; exact hpost s t hs0 hq) s0 rfl

/-- **Declarations ahead of a program that never finishes normally** are bound for it, the rest as `P` has it. This
holds when each value evaluates under `P` and setting their locals keeps `P`. -/
theorem decs_run {o : Oracle σ} {R : Ret} :
    ∀ (ds : List (String × PancakeExp)) {c : PancakeProg} {P : PancakeState σ → Prop},
      (∀ d ∈ ds, ∀ s, P s → ∃ w, eval s d.2 = some w) →
      (∀ s y w, P s → y ∈ ds.map (·.1) → P { s with locals := setLocal s.locals y w }) →
      SafeR o (fun s => P s ∧ Bound (ds.map (·.1)) s) c R (fun _ => False) →
      SafeR o P (decs ds c) R (fun _ => False)
  | [], _, _, _, _, hc =>
    conseq hc (fun s hs => ⟨hs, fun _ h => by cases h⟩) (fun _ _ h => h) (fun _ h => h)
  | (x, e) :: ds, c, P, hv, hP, hc => by
    refine dec (P' := fun s => P s ∧ ∃ w, s.locals x = some w) (Q' := fun _ => False)
      (fun s hs => ?_) ?_ (fun _ _ _ h => h.elim)
    · obtain ⟨w, hw⟩ := hv (x, e) (by simp) s hs
      exact ⟨w, hw, hP s x w hs (by simp), w, by simp [setLocal]⟩
    refine decs_run ds (P := fun s => P s ∧ ∃ w, s.locals x = some w)
      (fun d hd s hs => hv d (List.mem_cons_of_mem _ hd) s hs.1) (fun s y w ⟨hs, hx⟩ hy => ?_)
      (conseq hc (fun s ⟨⟨hs, hx⟩, hb⟩ => ⟨hs, fun y hy => ?_⟩) (fun _ _ h => h) (fun _ h => h))
    · refine ⟨hP s y w hs (List.mem_cons_of_mem _ hy), ?_⟩
      by_cases hxy : x = y
      · exact ⟨w, by simp [setLocal, hxy]⟩
      · obtain ⟨u, hu⟩ := hx
        exact ⟨u, by simp [setLocal, hxy, hu]⟩
    · rcases List.mem_cons.mp hy with rfl | hy
      · exact hx
      · exact hb y hy

/-- A block lowered with `k` as what follows it: declarations and calls scope over `k`. -/
def lowerK : List PStmt → PancakeProg → Option PancakeProg
  | [], k => some k
  | .dec n v :: rest, k =>
    match Lower.lowerExp v, lowerK rest k with
    | some v', some r => some (.dec n v' r)
    | _, _ => none
  | .call r f as :: rest, k =>
    match Lower.lowerArgs as, lowerK rest k with
    | some a, some c => some (.decCall r f a c)
    | _, _ => none
  | s :: rest, k =>
    match Lower.lowerStmt1 s, lowerK rest k with
    | some s', some r => some (.seq s' r)
    | _, _ => none

/-- **A block followed by more lowers as the block with the rest's lowering after it**, whatever
stands at its top. -/
theorem fold_split : ∀ (xs ys : List PStmt) {k : PancakeProg}, ys ≠ [] →
    Lower.lowerStmtsFold ys = some k → Lower.lowerStmtsFold (xs ++ ys) = lowerK xs k
  | [], ys, k, _, h => by simpa [lowerK] using h
  | x :: xs, ys, k, hne, h => by
    have ih := fold_split xs ys hne h
    obtain ⟨z, zs, hz⟩ : ∃ z zs, xs ++ ys = z :: zs := by
      cases hxy : xs ++ ys with
      | nil => simp_all
      | cons z zs => exact ⟨z, zs, rfl⟩
    rw [List.cons_append, hz]
    rw [hz] at ih
    cases x <;> simp only [Lower.lowerStmtsFold, lowerK, ih] <;> (repeat' split) <;> simp_all

end DN.Compiler.Block
