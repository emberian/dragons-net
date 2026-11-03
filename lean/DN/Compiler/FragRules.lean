-- SPDX-License-Identifier: AGPL-3.0-or-later
import DN.Compiler.Frag

/-!
# DN.Compiler.FragRules

More fragments: branches (`frag_ite`, `frag_skip`), assignments, constant declarations (`decs_frag`) and a counting loop
(`frag_count`). A block proven of its lowering (`frag_fold`) and declarations scoping over what follows (`decs_seq`,
`frag_decs`). Fragments shown state by state or under a pure fact (`frag_each`, `frag_pure`).
-/

namespace DN.Compiler.Frag

open DN.Compiler DN.Compiler.Wp DN.Compiler.WpRet DN.Compiler.Preservation DN.Compiler.Bytes

variable {σ : Type}

/-- A state as `t` but for its clock. -/
structure Like (t u : PancakeState σ) : Prop where
  locals : u.locals = t.locals
  memory : u.memory = t.memory
  memaddrs : u.memaddrs = t.memaddrs
  be : u.be = t.be
  ffi : u.ffi = t.ffi
  base : u.baseAddr = t.baseAddr
  code : u.code = t.code

theorem like_clock (t : PancakeState σ) : Safe.ClockFree (Like t) := fun _ _ h => { h with }

theorem like_refl (t : PancakeState σ) : Like t t := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem like_eq {t u : PancakeState σ} (h : Like t u) : u = { t with clock := u.clock } := by
  cases u; cases t
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  simp only at h1 h2 h3 h4 h5 h6 h7
  subst h1 h2 h3 h4 h5 h6 h7
  rfl

theorem like_eval {t u : PancakeState σ} (h : Like t u) (e : PancakeExp) : eval u e = eval t e := by
  rw [like_eq h, Safe.eval_clock]

/-- `s` with the local `x` set. -/
def setL (s : PancakeState σ) (x : String) (v : Value) : PancakeState σ := { s with locals := setLocal s.locals x v }

/-- A block that lowers before whatever follows. -/
def LowKK (xs : List Syntax.PStmt) : Prop := ∀ k, ∃ c, Block.lowerK xs k = some c

theorem lowKK_append {xs ys : List Syntax.PStmt} (h1 : LowKK xs) (h2 : LowKK ys) : LowKK (xs ++ ys) := fun k => by
  obtain ⟨c2, h2⟩ := h2 k
  obtain ⟨c1, h1⟩ := h1 c2
  exact ⟨c1, by rw [lowerK_append, h2, Option.bind_some, h1]⟩

theorem lowKK_flatten : ∀ (ps : List (List Syntax.PStmt)), (∀ p ∈ ps, LowKK p) → LowKK ps.flatten
  | [], _ => fun k => ⟨k, rfl⟩
  | p :: ps, h => lowKK_append (h p (by simp)) (lowKK_flatten ps fun q hq => h q (by simp [hq]))

theorem lowKK_one {x : Syntax.PStmt} (hd : x.isDec = false) {a : PancakeProg} (h : Lower.lowerStmt1 x = some a) :
    LowKK [x] := fun k => ⟨_, lowerK_one h hd k⟩

theorem lowKK_dec {x : String} {e : Syntax.PExpr} {E : PancakeExp} (h : Lower.lowerExp e = some E) :
    LowKK [.dec x e] := fun _ => ⟨_, lowerK_dec h rfl⟩

theorem lowKK_call {r f : String} {as : List Syntax.PExpr} {a : List PancakeExp} (h : Lower.lowerArgs as = some a) :
    LowKK [.call r f as] := fun k => ⟨.decCall r f a k, by simp [Block.lowerK, h]⟩

/-- A fragment shown from each state on its own. -/
theorem frag_each (o : Oracle σ) {xs : List Syntax.PStmt} (hlow : LowKK xs) {P P' : Assn σ}
    (h : ∀ s, P s → Frag o xs (Like s) P') : Frag o xs P P' := by
  intro k R Q hQ hk
  obtain ⟨c, hc⟩ := hlow k
  refine ⟨c, hc, fun s hs => ?_⟩
  obtain ⟨c', hc', hs'⟩ := h s hs k R Q hQ hk
  rw [hc] at hc'; cases hc'
  exact hs' s (like_refl s)

theorem lowKK_fold {xs : List Syntax.PStmt} (h : LowKK xs) : ∃ c, Lower.lowerStmtsFold xs = some c := by
  obtain ⟨c', hc'⟩ := h .skip
  obtain ⟨c, hc, -⟩ := fold_of_K (σ := Unit) Oracle.idle xs hc'
  exact ⟨c, hc⟩

theorem lowKK_ite {c : Syntax.PExpr} {C : PancakeExp} (hc : Lower.lowerExp c = some C) {t e : List Syntax.PStmt}
    (ht : LowKK t) (he : LowKK e) : LowKK [.ite c t e] := by
  obtain ⟨T, hT⟩ := lowKK_fold ht
  obtain ⟨E, hE⟩ := lowKK_fold he
  exact lowKK_one rfl (a := .cond C T E) (by simp [Lower.lowerStmt1, hc, hT, hE])

/-- A block that lowers before one continuation lowers before any. -/
theorem lowK_any : ∀ (xs : List Syntax.PStmt) {k c : PancakeProg}, Block.lowerK xs k = some c → LowKK xs
  | [], _, _, _ => fun k' => ⟨k', rfl⟩
  | x :: rest, k, c, h => by
    cases hx : x.isDec with
    | false =>
      obtain ⟨a, r, ha, hr, -⟩ := lowerK_cons_inv hx h
      exact lowKK_append (xs := [x]) (lowKK_one hx ha) (lowK_any rest hr)
    | true =>
      cases x with
      | dec n v =>
        obtain ⟨v', r, hv, hr, -⟩ := lowerK_dec_inv h
        exact lowKK_append (xs := [_]) (lowKK_dec hv) (lowK_any rest hr)
      | call rt f as =>
        obtain ⟨a, r, ha, hr, -⟩ := lowerK_call_inv h
        exact lowKK_append (xs := [_]) (lowKK_call ha) (lowK_any rest hr)
      | _ => simp [Syntax.PStmt.isDec] at hx

/-- A fragment shown under a fact its states all give. -/
theorem frag_pure {o : Oracle σ} {xs : List Syntax.PStmt} {P P' : Assn σ} (Q : Prop) (hQ : ∀ s, P s → Q)
    (hl : LowKK xs) (h : Q → Frag o xs P P') : Frag o xs P P' := by
  by_cases q : Q
  · exact h q
  · intro k R Qa _ _
    obtain ⟨c, hc⟩ := hl k
    exact ⟨c, hc, fun s hs => absurd (hQ s hs) q⟩

theorem frag_unsat {o : Oracle σ} {xs : List Syntax.PStmt} {P P' : Assn σ} (hl : LowKK xs) (h : ∀ s, P s → False) :
    Frag o xs P P' :=
  frag_pure False h hl False.elim

theorem lowKK_decs (xs : List String) : LowKK (xs.map fun x => .dec x (Syntax.n 0)) := by
  induction xs with
  | nil => exact fun k => ⟨k, rfl⟩
  | cons x xs ih => exact lowKK_append (xs := [_]) (lowKK_dec rfl) ih

/-- **A branch**: each arm a fragment closed on its own, from where the test sends it. -/
theorem frag_ite (o : Oracle σ) {c : Syntax.PExpr} {C : PancakeExp} (hc : Lower.lowerExp c = some C)
    {t e : List Syntax.PStmt} {P P' : Assn σ} (hP' : Safe.ClockFree P') (hdef : ∀ s, P s → ∃ w, eval s C = some w)
    (ht : Frag o t (fun s => P s ∧ eval s C ≠ some 0) P') (htc : ∀ u y v, P' u → y ∈ declared t → P' (restore u y v))
    (he : Frag o e (fun s => P s ∧ eval s C = some 0) P') (hec : ∀ u y v, P' u → y ∈ declared e → P' (restore u y v)) :
    Frag o [.ite c t e] P P' := by
  obtain ⟨T, hT, -⟩ := frag_close ht htc (fun _ _ => False)
  obtain ⟨E, hE, -⟩ := frag_close he hec (fun _ _ => False)
  refine frag_oneR (a := .cond C T E) (by simp [Lower.lowerStmt1, hc, hT, hE]) rfl hP' fun R => ?_
  obtain ⟨T', hT', hTs⟩ := frag_close ht htc R
  obtain ⟨E', hE', hEs⟩ := frag_close he hec R
  rw [hT] at hT'; cases hT'
  rw [hE] at hE'; cases hE'
  exact WpRet.cond hdef hTs hEs

theorem frag_nil (o : Oracle σ) {P P' : Assn σ} (h : ∀ s, P s → P' s) : Frag o [] P P' :=
  fun k _ _ _ hk => ⟨k, rfl, conseq hk h (fun _ _ h => h) (fun _ h => h)⟩

/-- **A branch not taken**: its test zero from every state the premise holds in. -/
theorem frag_skip (o : Oracle σ) {c : Syntax.PExpr} {C : PancakeExp} (hc : Lower.lowerExp c = some C)
    {t : List Syntax.PStmt} (hlt : LowKK t) {P : Assn σ} (hP : Safe.ClockFree P) (h0 : ∀ s, P s → eval s C = some 0)
    (htc : ∀ u y v, P u → y ∈ declared t → P (restore u y v)) : Frag o [.ite c t []] P P :=
  frag_ite o hc hP (fun s h => ⟨_, h0 s h⟩) (frag_unsat hlt fun s ⟨h, hne⟩ => hne (h0 s h)) htc
    (frag_nil o fun s h => h.1) (fun _ _ _ _ h => by simp [declared] at h)

/-- An assignment, from one state. -/
theorem assign_frag (o : Oracle σ) {s : PancakeState σ} {x : String} {e : Syntax.PExpr} {E : PancakeExp}
    (he : Lower.lowerExp e = some E) {v : Value} (hv : eval s E = some v) (hx : ∃ old, s.locals x = some old) :
    Frag o [.assign x e] (Like s) (Like (setL s x v)) := by
  obtain ⟨old, hold⟩ := hx
  exact frag_one (a := .assign x E) (by simp [Lower.lowerStmt1, he]) rfl rfl (like_clock _)
    (Safe.assign fun u h => ⟨v, old, by rw [like_eval h]; exact hv, by rw [h.locals]; exact hold,
      ⟨by simp [setL, h.locals], h.memory, h.memaddrs, h.be, h.ffi, h.base, h.code⟩⟩)

/-- The names `ns` declared zero, every other local and the rest of `s0` as they were. -/
structure Zeros (s0 : PancakeState σ) (ns : List String) (s : PancakeState σ) : Prop where
  zero : ∀ y ∈ ns, s.locals y = some 0
  frame : ∀ y, y ∉ ns → s.locals y = s0.locals y
  memory : s.memory = s0.memory
  memaddrs : s.memaddrs = s0.memaddrs
  be : s.be = s0.be
  ffi : s.ffi = s0.ffi
  base : s.baseAddr = s0.baseAddr
  code : s.code = s0.code

theorem decs_frag (o : Oracle σ) (s0 : PancakeState σ) : ∀ (xs pre : List String),
    Frag o (xs.map fun x => .dec x (Syntax.n 0)) (Zeros s0 pre) (Zeros s0 (pre ++ xs))
  | [], pre => frag_nil o fun s h => by simpa using h
  | x :: xs, pre => by
    have h1 : Frag o [.dec x (Syntax.n 0)] (Zeros s0 pre) (Zeros s0 (pre ++ [x])) :=
      frag_dec o rfl fun s h => ⟨0, rfl, fun y hy => by
          rcases List.mem_append.mp hy with hy | hy
          · by_cases e : y = x
            · simp [setLocal, e]
            · simp [setLocal, e, h.zero y hy]
          · simp at hy; simp [setLocal, hy],
        fun y hy => by
          have : y ≠ x := fun e => hy (by simp [e])
          simp only [setLocal, if_neg this]
          exact h.frame y fun e => hy (List.mem_append_left _ e),
        h.memory, h.memaddrs, h.be, h.ffi, h.base, h.code⟩
    have h2 := decs_frag o s0 xs (pre ++ [x])
    rw [List.append_assoc, List.singleton_append] at h2
    exact frag_append (xs := [_]) h1 h2

/-- From `s0`, the names `ds` declared, each holding its constant, the rest as at `s0`. -/
structure Consts (s0 : PancakeState σ) (ds : List (String × Nat)) (s : PancakeState σ) : Prop where
  val : ∀ p ∈ ds, s.locals p.1 = some (BitVec.ofNat 64 p.2)
  frame : ∀ y, y ∉ ds.map Prod.fst → s.locals y = s0.locals y
  memory : s.memory = s0.memory
  memaddrs : s.memaddrs = s0.memaddrs
  be : s.be = s0.be
  ffi : s.ffi = s0.ffi
  base : s.baseAddr = s0.baseAddr
  code : s.code = s0.code

/-- **Declarations of constants**, their names distinct. -/
theorem decsC_frag (o : Oracle σ) (s0 : PancakeState σ) : ∀ (ds pre : List (String × Nat)),
    (pre ++ ds).Pairwise (fun a b => a.1 ≠ b.1) →
    Frag o (ds.map fun p => .dec p.1 (Syntax.n p.2)) (Consts s0 pre) (Consts s0 (pre ++ ds))
  | [], pre, _ => frag_nil o fun s h => by simpa using h
  | d :: ds, pre, hd => by
    have hn : ∀ p ∈ pre, p.1 ≠ d.1 := fun p hp => (List.pairwise_append.mp hd).2.2 p hp d (by simp)
    have h1 : Frag o [.dec d.1 (Syntax.n d.2)] (Consts s0 pre) (Consts s0 (pre ++ [d])) :=
      frag_dec o rfl fun s h => ⟨_, rfl, fun p hp => by
          rcases List.mem_append.mp hp with hp | hp
          · simp only [setLocal, if_neg (hn p hp)]; exact h.val p hp
          · simp at hp; subst hp; simp [setLocal],
        fun y hy => by
          have : y ≠ d.1 := fun e => hy (by simp [e])
          simp only [setLocal, if_neg this]
          exact h.frame y fun e => hy (by simp only [List.map_append, List.mem_append]; exact Or.inl e),
        h.memory, h.memaddrs, h.be, h.ffi, h.base, h.code⟩
    have h2 := decsC_frag o s0 ds (pre ++ [d]) (by simpa using hd)
    rw [List.append_assoc, List.singleton_append] at h2
    exact frag_append (xs := [_]) h1 h2

/-- Declarations of constants lower before anything. -/
theorem lowKK_decsC (ds : List (String × Nat)) : LowKK (ds.map fun p => .dec p.1 (Syntax.n p.2)) := by
  induction ds with
  | nil => exact fun k => ⟨k, rfl⟩
  | cons d ds ih => exact lowKK_append (xs := [_]) (lowKK_dec rfl) ih

/-- A block whose top declares and calls nothing, lowered with `k` after it, runs as its lowering, then `k`. -/
theorem lowerK_fold (o : Oracle σ) : ∀ (xs : List Syntax.PStmt), xs ≠ [] → (∀ x ∈ xs, x.isDec = false) →
    ∀ {a : PancakeProg}, Lower.lowerStmtsFold xs = some a → ∀ k, ∃ c, Block.lowerK xs k = some c ∧
      ∀ s, PancakeSem o c s = PancakeSem o (.seq a k) s
  | [], h, _, _, _, _ => absurd rfl h
  | [x], _, hnd, a, ha, k => by
    have hx : Lower.lowerStmt1 x = some a := by cases x <;> simpa [Lower.lowerStmtsFold] using ha
    exact ⟨_, lowerK_one hx (hnd x (by simp)) k, fun _ => rfl⟩
  | x :: y :: ys, _, hnd, a, ha, k => by
    have hx0 := hnd x (by simp)
    obtain ⟨ax, hax⟩ : ∃ ax, Lower.lowerStmt1 x = some ax := by
      cases h : Lower.lowerStmt1 x with
      | some ax => exact ⟨ax, rfl⟩
      | none => cases x <;> simp_all [Lower.lowerStmtsFold, Syntax.PStmt.isDec]
    obtain ⟨b, hb⟩ : ∃ b, Lower.lowerStmtsFold (y :: ys) = some b := by
      cases h : Lower.lowerStmtsFold (y :: ys) with
      | some b => exact ⟨b, rfl⟩
      | none => cases x <;> simp_all [Lower.lowerStmtsFold, Syntax.PStmt.isDec]
    rw [Block.fold_cons hax hx0 (by simp) hb] at ha; cases ha
    obtain ⟨c, hc, hs⟩ := lowerK_fold o (y :: ys) (by simp) (fun z hz => hnd z (by simp [hz])) hb k
    exact ⟨.seq ax c, by rw [lowerK_cons hax hx0 hc], fun s => by
      rw [Components.seq_assoc]; exact Block.seq_congr o ax hs s⟩

/-- **A block proven as its lowering**, no declaration or call at its top. -/
theorem frag_fold (o : Oracle σ) {xs : List Syntax.PStmt} (hne : xs ≠ []) (hnd : ∀ x ∈ xs, x.isDec = false)
    {a : PancakeProg} (ha : Lower.lowerStmtsFold xs = some a) {P P' : Assn σ} (hP' : Safe.ClockFree P')
    (h : ∀ R, SafeR o P a R P') : Frag o xs P P' := by
  intro k R Q _ hk
  obtain ⟨c, hc, hs⟩ := lowerK_fold o xs hne hnd ha k
  refine ⟨c, hc, fun s hp => ?_⟩
  have := WpRet.seq (h R) hk hP' s hp
  rw [hs]; exact this

/-- A check proven of its lowering, from each state on its own. -/
theorem frag_pinned (o : Oracle σ) {xs : List Syntax.PStmt} (hne : xs ≠ []) (hnd : ∀ x ∈ xs, x.isDec = false)
    {c : PancakeProg} (hc : Lower.lowerStmtsFold xs = some c) (hnr : noRet c = true) {P : Assn σ}
    {Post : PancakeState σ → Assn σ} (hcl : ∀ s, Safe.ClockFree (Post s))
    (hP : ∀ s, P s → Safe.Safe o (fun u => u = s) c (Post s)) :
    Frag o xs P (fun u => ∃ s, P s ∧ Post s u) :=
  frag_fold o hne hnd hc (fun _ _ ⟨s, hs, h⟩ => ⟨s, hs, hcl s _ _ h⟩) fun R s hs =>
    WpRet.conseq (WpRet.ofSafe R hnr (hP s hs)) (fun _u (hu : _u = s) => hu) (fun _ _ h => h)
      (fun _ h => ⟨s, hs, h⟩) s rfl

/-- **The declarations' scope may take in what follows**: a block under `ds` reaching `P'`, then `k` from `P'` to `Q`.
They run as the declarations over both, when `P'` and `Q` ignore the declared locals. -/
theorem decs_seq (o : Oracle σ) {R : Ret} {F k : PancakeProg} :
    ∀ (ds : List (String × PancakeExp)) (s : PancakeState σ) (P' Q : PancakeState σ → Prop),
      (∀ u y w, y ∈ ds.map (·.1) → P' u → P' (restore u y w)) →
      (∀ u y w, y ∈ ds.map (·.1) → Q u → Q (restore u y w)) →
      (∀ t, P' t → OkR R Q (PancakeSem o k t)) →
      OkR R P' (PancakeSem o (Block.decs ds F) s) → OkR R Q (PancakeSem o (Block.decs ds (.seq F k)) s)
  | [], s, P', Q, _, _, hk, h => by
    simp only [Block.decs] at h ⊢
    rw [Components.seq_run]
    rcases hF : PancakeSem o F s with ⟨_ | r, t⟩
    · rw [hF] at h; exact hk t h
    · rw [hF] at h; exact okR_post (by simp) rfl h
  | (x, E) :: ds, s, P', Q, hP, hQ, hk, h => by
    simp only [Block.decs] at h ⊢
    rw [PancakeSem] at h ⊢
    cases hv : eval s E with
    | none => simp only [hv] at h ⊢; exact okR_post (by simp) rfl h
    | some val =>
      simp only [hv] at h ⊢
      let P'' : PancakeState σ → Prop := fun u => P' (restore u x (s.locals x))
      let Q'' : PancakeState σ → Prop := fun u => Q (restore u x (s.locals x))
      have ih := decs_seq o (F := F) (k := k) ds { s with locals := setLocal s.locals x val } P'' Q''
        (fun u y w hy hu => by
          show P' (restore (restore u y w) x (s.locals x))
          by_cases e : y = x
          · subst e
            rw [restore_same]; exact hu
          · rw [restore_comm _ e]; exact hP _ y w (by simp [hy]) hu)
        (fun u y w hy hu => by
          show Q (restore (restore u y w) x (s.locals x))
          by_cases e : y = x
          · subst e
            rw [restore_same]; exact hu
          · rw [restore_comm _ e]; exact hQ _ y w (by simp [hy]) hu)
        (fun t ht => by
          have h1 : P' t := by
            have := hP _ x (t.locals x) (by simp) ht
            rwa [restore_restore] at this
          have h2 := hk t h1
          rcases hr : PancakeSem o k t with ⟨_ | r, t2⟩
          · rw [hr] at h2; exact hQ t2 x _ (by simp) h2
          · rw [hr] at h2; exact okR_post (by simp) rfl h2)
      have h' : OkR R P'' (PancakeSem o (Block.decs ds F) { s with locals := setLocal s.locals x val }) := by
        revert h
        rcases PancakeSem o (Block.decs ds F) { s with locals := setLocal s.locals x val } with ⟨_ | r, t⟩
        · exact id
        · exact okR_post (by simp) rfl
      have := ih h'
      revert this
      rcases PancakeSem o (Block.decs ds (.seq F k)) { s with locals := setLocal s.locals x val } with ⟨_ | r, t⟩
      · exact id
      · exact okR_post (by simp) rfl

/-- Declarations lowered before a block: `decs` over its lowering. -/
theorem lowerK_decs : ∀ (ds : List (String × Syntax.PExpr)) {Es : List (String × PancakeExp)},
    Block.lowerDecs ds = some Es → ∀ {body : List Syntax.PStmt} {k c : PancakeProg}, Block.lowerK body k = some c →
      Block.lowerK (ds.map (fun d => .dec d.1 d.2) ++ body) k = some (Block.decs Es c)
  | [], Es, h, _, _, _, hc => by simp [Block.lowerDecs] at h; subst h; simpa [Block.decs] using hc
  | (x, e) :: ds, Es, h, body, k, c, hc => by
    simp only [Block.lowerDecs] at h
    split at h
    · rename_i E Es' hE hEs
      cases h
      simp only [List.map_cons, List.cons_append]
      exact lowerK_dec hE (lowerK_decs ds hEs hc)
    · cases h

/-- Declarations over blocks that run alike run alike. -/
theorem decs_congr (o : Oracle σ) : ∀ (Es : List (String × PancakeExp)) {q q' : PancakeProg},
    (∀ s, PancakeSem o q s = PancakeSem o q' s) → ∀ (s : PancakeState σ),
      PancakeSem o (Block.decs Es q) s = PancakeSem o (Block.decs Es q') s
  | [], _, _, h, s => h s
  | (x, E) :: Es, _, _, h, s => dec_congr o x E (decs_congr o Es h) s

/-- Lowered declarations keep their names. -/
theorem lowerDecs_names : ∀ (ds : List (String × Syntax.PExpr)) {Es : List (String × PancakeExp)},
    Block.lowerDecs ds = some Es → Es.map (·.1) = ds.map (·.1)
  | [], Es, h => by simp [Block.lowerDecs] at h; subst h; rfl
  | (x, e) :: ds, Es, h => by
    simp only [Block.lowerDecs] at h
    split at h
    · rename_i E Es' _ hEs
      cases h
      simp [lowerDecs_names ds hEs]
    · cases h

/-- Declarations' names are declared. -/
theorem declared_decs : ∀ (ds : List (String × Syntax.PExpr)), ∀ y ∈ ds.map (·.1),
    y ∈ declared (ds.map (fun d => Syntax.PStmt.dec d.1 d.2))
  | [], _, h => by simp at h
  | d :: ds, y, h => by
    simp only [List.map_cons, List.mem_cons] at h
    simp only [List.map_cons, declared]
    rcases h with rfl | h
    · simp
    · exact List.mem_cons_of_mem _ (declared_decs ds y h)

/-- **Declarations ahead of a block**, scoping over what follows: proven of their lowering together. -/
theorem frag_decs (o : Oracle σ) (ds : List (String × Syntax.PExpr)) {Es : List (String × PancakeExp)}
    (hE : Block.lowerDecs ds = some Es) {body : List Syntax.PStmt} (hne : body ≠ [])
    (hnd : ∀ y ∈ body, y.isDec = false) {B : PancakeProg} (hB : Lower.lowerStmtsFold body = some B)
    {P P' : Assn σ} (hcl : ∀ u y w, y ∈ ds.map (·.1) → P' u → P' (restore u y w))
    (h : ∀ R, SafeR o P (Block.decs Es B) R P') :
    Frag o (ds.map (fun d => .dec d.1 d.2) ++ body) P P' := by
  intro k R Q hQ hk
  obtain ⟨c, hc, hs⟩ := lowerK_fold o body hne hnd hB k
  have hEs := lowerDecs_names ds hE
  refine ⟨Block.decs Es c, lowerK_decs ds hE hc, fun s hp => ?_⟩
  rw [decs_congr o Es hs s]
  exact decs_seq o Es s P' Q (fun u y w hy hu => hcl u y w (hEs ▸ hy) hu)
    (fun u y w hy hu => hQ u y w hu (by
      rw [declared_append]; exact List.mem_append_left _ (declared_decs ds y (hEs ▸ hy))))
    (fun t ht => hk t ht) (h R s hp)

/-- **A loop counting up**: the body takes the invariant at `i` to `i + 1` while `g i` holds. If the loop ends normally,
it ends where the test fails. -/
theorem frag_count (o : Oracle σ) {c : Syntax.PExpr} {C : PancakeExp} (hc : Lower.lowerExp c = some C)
    {body : List Syntax.PStmt} (hlow : LowKK body) {I : Nat → Assn σ} (hI : ∀ i, Safe.ClockFree (I i))
    (hr : ∀ i u y v, I i u → y ∈ declared body → I i (restore u y v)) {g : Nat → Bool}
    (hcond : ∀ i u, I i u → eval u C = some (if g i then 1 else 0))
    (hbody : ∀ i, g i = true → Frag o body (I i) (I (i + 1))) (i0 : Nat) :
    Frag o [.while c body] (I i0) (fun u => ∃ i, I i u ∧ g i = false) := by
  obtain ⟨BODY, hBl⟩ := lowKK_fold hlow
  have hz : ∀ i u, I i u → eval u C = some 0 → g i = false := fun i u h e => by
    rw [hcond i u h] at e; cases hg : g i <;> simp_all
  refine frag_oneR (a := .while_ C BODY) (by simp [Lower.lowerStmt1, hc, hBl]) rfl
    (fun _ _ ⟨i, h, hg⟩ => ⟨i, hI i _ _ h, hg⟩) fun R => ?_
  refine conseq (WpRet.while_ (I := fun u => ∃ i, I i u) (fun s ⟨i, h⟩ => ⟨_, hcond i s h⟩) ?_
    (fun _ _ ⟨i, h⟩ => ⟨i, hI i _ _ h⟩)) (fun s h => ⟨i0, h⟩) (fun _ _ h => h)
    fun s ⟨⟨i, h⟩, e⟩ => ⟨i, h, hz i s h e⟩
  intro s ⟨⟨i, h⟩, hne⟩
  have hg : g i = true := by
    cases e : g i
    · exact absurd (by rw [hcond i s h, e]; rfl) hne
    · rfl
  obtain ⟨c', hc', hs⟩ := frag_close (hbody i hg) (hr (i + 1)) R
  rw [hBl] at hc'; cases hc'
  exact conseq hs (fun _ h => h) (fun _ _ h => h) (fun u hu => ⟨i + 1, hu⟩) s h

/-- Let the test, true of `j`, be true of every `i ≤ j`. Where a count up to `n` stops, it stands as at `n`. -/
theorem count_exit {p : Nat → Bool} (hmono : ∀ i j, i ≤ j → p j = true → p i = true) {i n : Nat} (hi : i ≤ n)
    (hz : (p i && decide (i < n)) = false) : p i = p n := by
  cases hp : p i
  · cases e : p n
    · rfl
    · rw [hmono i n hi e] at hp; exact absurd hp (by decide)
  · rw [hp, Bool.true_and, decide_eq_false_iff_not] at hz
    have : i = n := by omega
    subst this; exact hp.symm

/-! ### The premises can hold -/

theorem like_witness : Like (bareState ()) (bareState ()) := like_refl _

theorem consts_witness : Consts (bareState ()) [] (bareState ()) :=
  ⟨fun _ h => absurd h (by simp), fun _ _ => rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem zeros_witness : Zeros (bareState ()) [] (bareState ()) :=
  ⟨fun _ h => by simp at h, fun _ _ => rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- An assignment, from what the premise gives. -/
theorem set_frag (o : Oracle σ) {x : String} {e : Syntax.PExpr} {E : PancakeExp} (he : Lower.lowerExp e = some E)
    {P P' : Assn σ} (hP' : Safe.ClockFree P')
    (h : ∀ s, P s → ∃ v, eval s E = some v ∧ (∃ old, s.locals x = some old) ∧ P' (setL s x v)) :
    Frag o [.assign x e] P P' :=
  frag_one (a := .assign x E) (by simp [Lower.lowerStmt1, he]) rfl rfl hP'
    (Safe.assign fun s hs => by
      obtain ⟨v, hv, ⟨old, hold⟩, hp⟩ := h s hs
      exact ⟨v, old, hv, hold, hp⟩)

/-- A store of an octet. -/
theorem storeb_frag (o : Oracle σ) {d e : Syntax.PExpr} {D E : PancakeExp} (hd : Lower.lowerExp d = some D)
    (he : Lower.lowerExp e = some E) {P P' : Assn σ} (hP' : Safe.ClockFree P')
    (h : ∀ s, P s → ∃ addr val, eval s D = some addr ∧ eval s E = some val ∧ s.memaddrs (byteAlign addr) = true ∧
      P' { s with memory := putByte s.memory s.be addr (val.setWidth 8) }) :
    Frag o [.storeb d e] P P' :=
  frag_one (a := .storeByte D E) (by simp [Lower.lowerStmt1, hd, he]) rfl rfl hP'
    (Safe.storeByte fun s hs => by
      obtain ⟨addr, val, ha, hv, hdm, hp⟩ := h s hs
      exact ⟨addr, val, _, ha, hv, memStore_eq _ _ _ _ _ hdm, hp⟩)

/-- A store of a word. -/
theorem store_frag (o : Oracle σ) {d e : Syntax.PExpr} {D E : PancakeExp} (hd : Lower.lowerExp d = some D)
    (he : Lower.lowerExp e = some E) {P P' : Assn σ} (hP' : Safe.ClockFree P')
    (h : ∀ s, P s → ∃ addr val, eval s D = some addr ∧ eval s E = some val ∧ s.memaddrs addr = true ∧
      P' { s with memory := fun k => if k = addr then val else s.memory k }) :
    Frag o [.store d e] P P' :=
  frag_one (a := .store D E) (by simp [Lower.lowerStmt1, hd, he]) rfl rfl hP'
    (Safe.store fun s hs => by
      obtain ⟨addr, val, ha, hv, hdm, hp⟩ := h s hs
      exact ⟨addr, val, _, ha, hv, by simp [memStoreWord, hdm], hp⟩)

/-- A fragment from a premise with a witness, shown for each witness. -/
theorem frag_exists {α : Type} {o : Oracle σ} {xs : List Syntax.PStmt} (hl : LowKK xs) {P : α → Assn σ}
    {Q : Assn σ} (h : ∀ a, Frag o xs (P a) Q) : Frag o xs (fun u => ∃ a, P a u) Q := by
  intro k R Q' hQ hk
  obtain ⟨c, hc⟩ := hl k
  refine ⟨c, hc, fun s ⟨a, hs⟩ => ?_⟩
  obtain ⟨c', hc', hs'⟩ := h a k R Q' hQ hk
  rw [hc] at hc'; cases hc'
  exact hs' s hs

/-- A block that declares nothing gives back no local. -/
theorem noDecl {P' : Assn σ} (xs : List Syntax.PStmt) (h : declared xs = []) :
    ∀ u y v, P' u → y ∈ declared xs → P' (restore u y v) := fun _ _ _ _ hy => by rw [h] at hy; cases hy

/-- A loop lowers before anything when its body does. -/
theorem lowKK_while {c : Syntax.PExpr} {C : PancakeExp} (hc : Lower.lowerExp c = some C) {body : List Syntax.PStmt}
    (hb : LowKK body) : LowKK [.while c body] := by
  obtain ⟨B, hB⟩ := lowKK_fold hb
  exact lowKK_one rfl (a := .while_ C B) (by rw [Lower.lowerStmt1, hc, hB])

/-- **A loop** with an invariant: it holds after the loop, the condition false. -/
theorem frag_while (o : Oracle σ) {c : Syntax.PExpr} {C : PancakeExp} (hc : Lower.lowerExp c = some C)
    {body : List Syntax.PStmt} (hlow : LowKK body) {I : Assn σ} (hI : Safe.ClockFree I)
    (hr : ∀ u y v, I u → y ∈ declared body → I (restore u y v)) (hdef : ∀ u, I u → ∃ w, eval u C = some w)
    (hbody : Frag o body (fun u => I u ∧ eval u C ≠ some 0) I) :
    Frag o [.while c body] I (fun u => I u ∧ eval u C = some 0) := by
  obtain ⟨BODY, hBl⟩ := lowKK_fold hlow
  refine frag_oneR (a := .while_ C BODY) (by simp [Lower.lowerStmt1, hc, hBl]) rfl
    (fun s k ⟨h, e⟩ => ⟨hI _ _ h, by rw [Safe.eval_clock]; exact e⟩) fun R => ?_
  refine conseq (WpRet.while_ (I := I) hdef ?_ hI) (fun s h => h) (fun _ _ h => h) fun s h => h
  intro s hs
  obtain ⟨c', hc', hsafe⟩ := frag_close hbody hr R
  rw [hBl] at hc'; cases hc'
  exact hsafe s hs

theorem lowKK_nil : LowKK [] := fun k => ⟨k, rfl⟩

theorem lowKK_ret {e : Syntax.PExpr} {E : PancakeExp} (he : Lower.lowerExp e = some E) : LowKK [.ret e] :=
  lowKK_one rfl (a := .ret E) (by simp [Lower.lowerStmt1, he])

/-- A local set twice holds the second value. -/
theorem setL_setL (s : PancakeState σ) (x : String) (v w : Value) : setL (setL s x v) x w = setL s x w := by
  simp only [setL]; congr 1; funext y; simp [setLocal]; split <;> rfl

end DN.Compiler.Frag
