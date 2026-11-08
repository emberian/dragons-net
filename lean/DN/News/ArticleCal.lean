-- SPDX-License-Identifier: AGPL-3.0-or-later
import DN.News.ArticleScan
import DN.News.Calendar

/-!
# DN.News.ArticleCal

The article program's arithmetic of the calendar, proven to compute what `DN.News.ArticleSpec` does, if it returns.
`artDiv` divides by long division (`artDiv_ok`). `artCivilOf` and `artCivil` go between days since 1970 and days of
the calendar (`civilFromDays`, `daysFromCivil`).
-/

namespace DN.News.ArticleCal

open DN.Compiler DN.Compiler.Wp DN.Compiler.WpRet DN.Compiler.Frag DN.News.AbnfProg
open DN.News.AbnfSets DN.News.FunRun DN.News.AbnfLeaves DN.News.ArticleRun DN.News.ArticleScan
open DN.News.ScanRun (at_ at_add vals_lookup without Fresh)
open DN.News.FramerCode (bw ev_var bw_ne0 bw_eq0)
open DN.News.AbnfComment (ev_inc)
open DN.News.Calendar (civilWord cal_doe)
open DN.News.ArticleProg (guardL guardS)

variable {σ : Type}

/-! ## Division -/

theorem twoPow_ofNat (j : Nat) : BitVec.twoPow 64 j = BitVec.ofNat 64 (2 ^ j) := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_twoPow]

/-- The word of `artDiv`'s `j`, the bit `J - 1`: -1 once `J` is 0. -/
def jw (J : Nat) : Word := if J = 0 then BitVec.ofNat 64 (2 ^ 64 - 1) else BitVec.ofNat 64 (J - 1)

theorem jw_pos {J : Nat} (h : 1 ≤ J) : jw J = BitVec.ofNat 64 (J - 1) := if_neg (by omega)

theorem jw_dec {J : Nat} (h1 : 1 ≤ J) (h2 : J ≤ 62) : jw J - BitVec.ofNat 64 1 = jw (J - 1) := by
  rw [jw_pos h1]
  unfold jw
  split
  · rename_i h; rw [h]; decide
  · rw [BitVec.ofNat_sub_ofNat_of_le _ _ (by omega) (by omega)]

theorem jw_lt0 {u : PancakeState σ} {J : Nat} (hJ : J ≤ 62) (h : u.locals "j" = some (jw J)) :
    eval u (.cmp .less (.var "j") (.const (BitVec.ofNat 64 0))) = some (bw (decide (J = 0))) := by
  by_cases h0 : J = 0
  · subst h0; simp only [eval, h, jw, if_true]; decide
  · rw [jw_pos (by omega)] at h
    rw [FramerCode.eval_lt (by omega) (by decide) (ev_var h) rfl]
    simp [h0]

theorem jw_ge0 {u : PancakeState σ} {J : Nat} (hJ : J ≤ 62) (h : u.locals "j" = some (jw J)) :
    eval u (FramerCode.leE (.const (BitVec.ofNat 64 0)) (.var "j")) = some (bw (decide (1 ≤ J))) := by
  by_cases h0 : J = 0
  · subst h0; simp only [FramerCode.leE, eval, h, jw, if_true]; decide
  · rw [jw_pos (by omega)] at h
    rw [FramerCode.eval_le (by decide) (by omega) rfl (ev_var h), decide_eq_true (Nat.zero_le _),
      decide_eq_true (show 1 ≤ J by omega)]

/-- The bit `k` of `X`, as `artDiv` tests it against the power of two. -/
theorem divBit_eval {u : PancakeState σ} {X k : Nat} (hk : k < 64)
    (hx : u.locals "x" = some (BitVec.ofNat 64 X)) (hp : u.locals "pw" = some (BitVec.twoPow 64 k)) :
    eval u (.cmp .equal (.cmp .equal (.op .and_ (.var "x") (.var "pw")) (.const (BitVec.ofNat 64 0)))
      (.const (BitVec.ofNat 64 0))) = some (BitVec.ofNat 64 (X / 2 ^ k % 2)) := by
  simp only [eval, hx, hp, BitVec.and_twoPow, BitVec.getLsbD_ofNat]
  have hm : X / 2 ^ k % 2 = 0 ∨ X / 2 ^ k % 2 = 1 := by omega
  rcases hm with hm | hm
  · have : X.testBit k = false := by rw [Nat.testBit_eq_decide_div_mod_eq, hm]; rfl
    simp [this, hm]
  · have : X.testBit k = true := by rw [Nat.testBit_eq_decide_div_mod_eq, hm]; rfl
    have hne : BitVec.twoPow 64 k ≠ 0 := by
      intro e
      have h : 2 ^ k % 2 ^ 64 = 0 := by have := congrArg BitVec.toNat e; rw [BitVec.toNat_twoPow] at this; exact this
      rw [Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by decide) (by omega))] at h
      have := Nat.two_pow_pos k; omega
    simpa [this, hm, show k < 64 by omega] using hne

/-- A step of long division: the next bit taken down. -/
theorem div_step (r D b : Nat) (hD : 1 ≤ D) (hb : b ≤ 1) :
    (2 * r + b) % D = (if D ≤ 2 * (r % D) + b then 2 * (r % D) + b - D else 2 * (r % D) + b) ∧
      (2 * r + b) / D = 2 * (r / D) + (if D ≤ 2 * (r % D) + b then 1 else 0) := by
  have hr := Nat.div_add_mod r D
  have hlt := Nat.mod_lt r (show 0 < D by omega)
  generalize r / D = k at hr
  generalize r % D = m at hr hlt
  subst hr
  have e : 2 * (D * k + m) + b = D * (2 * k) + (2 * m + b) := by rw [Nat.mul_left_comm D 2 k]; omega
  rw [e]
  split
  · rename_i h
    have e2 : D * (2 * k) + (2 * m + b) = D * (2 * k + 1) + (2 * m + b - D) := by
      rw [Nat.mul_add, Nat.mul_one]; omega
    rw [e2, Nat.mul_add_mod, Nat.mul_add_div (by omega), Nat.mod_eq_of_lt (by omega), Nat.div_eq_of_lt (by omega)]
    omega
  · rename_i h
    rw [Nat.mul_add_mod, Nat.mul_add_div (by omega), Nat.mod_eq_of_lt (by omega), Nat.div_eq_of_lt (by omega)]
    omega

theorem shr_step (X J : Nat) (hJ : 1 ≤ J) : X / 2 ^ (J - 1) = 2 * (X / 2 ^ J) + X / 2 ^ (J - 1) % 2 := by
  have h1 : X / 2 ^ J = X / 2 ^ (J - 1) / 2 := by
    rw [Nat.div_div_eq_div_mul, ← Nat.pow_succ, Nat.succ_eq_add_one, Nat.sub_add_cancel hJ]
  rw [h1]; omega

/-- `artDiv`'s locals in its loops: the flag, the bit's place, the remainder and the quotient so far. -/
def divL (X D : Nat) (A : Word) (g J q rm : Nat) : List (String × Value) :=
  [("go", BitVec.ofNat 64 g), ("j", jw J), ("rm", BitVec.ofNat 64 rm), ("q", BitVec.ofNat 64 q), ("a", A),
   ("x", BitVec.ofNat 64 X), ("d", BitVec.ofNat 64 D)]

/-- The locals read off another list. -/
theorem runF_divL {s0 u : PancakeState σ} {l : List (String × Value)} {F : (Word → Word) → Prop}
    (h : RunF s0 l F u) {X D : Nat} {A : Word} {g J q rm : Nat}
    (h1 : l.lookup "go" = some (BitVec.ofNat 64 g) := by rfl) (h2 : l.lookup "j" = some (jw J) := by rfl)
    (h3 : l.lookup "rm" = some (BitVec.ofNat 64 rm) := by rfl) (h4 : l.lookup "q" = some (BitVec.ofNat 64 q) := by rfl)
    (h5 : l.lookup "a" = some A := by rfl) (h6 : l.lookup "x" = some (BitVec.ofNat 64 X) := by rfl)
    (h7 : l.lookup "d" = some (BitVec.ofNat 64 D) := by rfl) : RunF s0 (divL X D A g J q rm) F u :=
  ⟨⟨fun p hp => by
    simp only [divL, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first | exact vals_lookup h.1.vals h1 | exact vals_lookup h.1.vals h2 | exact vals_lookup h.1.vals h3 |
      exact vals_lookup h.1.vals h4 | exact vals_lookup h.1.vals h5 | exact vals_lookup h.1.vals h6 |
      exact vals_lookup h.1.vals h7,
    h.1.memaddrs, h.1.base, h.1.code, h.1.be⟩, h.2⟩

/-- `artDiv`'s first loop body: down to the highest bit set. -/
def divBody1 : List Syntax.PStmt :=
  [kept "j" 63,
   .ite (Syntax.eLe (pow (Syntax.v "j")) (Syntax.v "x")) [.assign "go" (Syntax.n 0)]
     [.assign "j" (Syntax.eSub (Syntax.v "j") (Syntax.n 1)),
      ArticleProg.ifs (Syntax.eLt (Syntax.v "j") (Syntax.n 0)) [.assign "go" (Syntax.n 0)]]]

/-- `artDiv`'s second loop body: a bit taken down. -/
def divBody2 : List Syntax.PStmt :=
  [kept "j" 63, .dec "pw" (pow (Syntax.v "j")),
   .assign "rm" (Syntax.eAdd (Syntax.eAdd (Syntax.v "rm") (Syntax.v "rm"))
     (ne (Syntax.eAnd (Syntax.v "x") (Syntax.v "pw")) (Syntax.n 0))),
   ArticleProg.ifs (Syntax.eLe (Syntax.v "d") (Syntax.v "rm"))
     [.assign "rm" (Syntax.eSub (Syntax.v "rm") (Syntax.v "d")),
      .assign "q" (Syntax.eAdd (Syntax.v "q") (Syntax.v "pw"))],
   .assign "j" (Syntax.eSub (Syntax.v "j") (Syntax.n 1))]

theorem artDiv_body : guardL ArticleProg.artDiv.body =
    [areaAt ArticleProg.ofs,
     ArticleProg.ifs (or2 (or2 (Syntax.eLt (Syntax.v "x") (Syntax.n 0))
          (Syntax.eLt (Syntax.n (2 ^ 62 - 1)) (Syntax.v "x")))
          (or2 (Syntax.eLt (Syntax.v "d") (Syntax.n 1)) (Syntax.eLt (Syntax.n (2 ^ 62)) (Syntax.v "d"))))
       [.store (Syntax.atOff (Syntax.v "a") aBroken) (Syntax.n 1), .ret (Syntax.n 0)],
     .dec "q" (Syntax.n 0), .dec "rm" (Syntax.n 0), .dec "j" (Syntax.n 61), .dec "go" (Syntax.n 1),
     .while (Syntax.v "go") divBody1, .while (Syntax.eLe (Syntax.n 0) (Syntax.v "j")) divBody2,
     .ret (Syntax.v "q")] := rfl

section div
variable (o : Oracle σ) {A : Word} {s1 : PancakeState σ} {X D : Nat} {m0 : Word → Word}

/-- **`artDiv`'s first loop finds the highest bit set**: past it, `X` is below `2 ^ J`. -/
theorem div_loop1 (hA : Area ArticleProg.ofs A s1) (hP : Pows m0 A) (hX : X < 2 ^ 62) :
    Frag o [.while (Syntax.v "go") divBody1] (RunF s1 (divL X D A 1 62 0 0) (· = m0))
      (fun u => ∃ J, RunF s1 (divL X D A 0 J 0 0) (· = m0) u ∧ J ≤ 62 ∧ X < 2 ^ J) := by
  let I : Assn σ := fun u => ∃ t : Nat × Nat, RunF s1 (divL X D A t.1 t.2 0 0) (· = m0) u ∧ t.2 ≤ 62 ∧
    X < 2 ^ t.2 ∧ (t.1 = 1 ∧ 1 ≤ t.2 ∨ t.1 = 0)
  have hIc : Safe.ClockFree I := fun u k ⟨t, h, hv⟩ => ⟨t, runF_clock _ _ _ u k h, hv⟩
  have hlow : LowKK divBody1 := lowK_any _ (k := .skip) rfl
  refine frag_conseq (frag_while o rfl hlow hIc (fun _ _ _ _ hy => by cases hy)
    (fun u ⟨t, h, _⟩ => ⟨_, ev_var (vals_lookup h.1.vals rfl)⟩) ?_)
    (fun u h => ⟨(1, 62), h, Nat.le_refl _, hX, .inl ⟨rfl, by decide⟩⟩) ?_
  · refine frag_conseq (P0 := fun u => ∃ t : Nat × Nat, (fun t u => RunF s1 (divL X D A t.1 t.2 0 0) (· = m0) u ∧
      t.2 ≤ 62 ∧ X < 2 ^ t.2 ∧ t.1 = 1 ∧ 1 ≤ t.2) t u) (frag_exists hlow fun t => ?_)
      (fun u ⟨⟨t, h, h1, h2, h3⟩, h0⟩ => ⟨t, h, h1, h2, by
        rcases h3 with h3 | h3
        · exact h3
        · rw [ev_var (vals_lookup h.1.vals rfl), h3] at h0; exact absurd rfl h0⟩) fun _ h => h
    refine frag_pure (t.2 ≤ 62 ∧ X < 2 ^ t.2 ∧ t.1 = 1 ∧ 1 ≤ t.2) (fun u h => h.2) hlow fun ⟨h1, h2, h3, h4⟩ => ?_
    obtain ⟨g, J⟩ := t
    simp only at h1 h2 h3 h4; subst h3
    refine frag_conseq (P0 := RunF s1 (divL X D A 1 J 0 0) (· = m0)) ?_ (fun u h => h.1) fun _ h => h
    have hj : ∀ u, RunF s1 (divL X D A 1 J 0 0) (· = m0) u → u.locals "j" = some (BitVec.ofNat 64 (J - 1)) :=
      fun u h => by rw [← jw_pos h4]; exact vals_lookup h.1.vals rfl
    refine frag_append (xs := [_]) (kept_frag o (by decide) (runF_clock _ _ _) fun u h => ⟨J - 1, hj u h, by omega⟩) ?_
    have hp63 : 2 ^ (J - 1) < 2 ^ 63 := Nat.pow_lt_pow_right (by decide) (by omega)
    have hX63 : X < 2 ^ 63 := by omega
    have hpw : ∀ u, RunF s1 (divL X D A 1 J 0 0) (· = m0) u →
        eval u (FramerCode.leE (.loadWord (.op .add (.op .add (.var "a") (.const (BitVec.ofNat 64 aPow)))
          (.mul (.var "j") (.const (BitVec.ofNat 64 8))))) (.var "x")) = some (bw (decide (2 ^ (J - 1) ≤ X))) := by
      intro u h
      have e1 := powAt_eval hA h.1.memaddrs (by rw [h.2]; exact hP) (vals_lookup h.1.vals rfl)
        (show J - 1 < 64 by omega) (ev_var (hj u h))
      rw [twoPow_ofNat] at e1
      exact FramerCode.eval_le hp63 hX63 e1 (ev_var (vals_lookup h.1.vals rfl))
    by_cases hb : 2 ^ (J - 1) ≤ X
    · refine DN.News.ScanRun.frag_if o rfl (lowK_any _ (k := .skip) rfl) (lowK_any _ (k := .skip) rfl) rfl rfl hIc
        (b := true) (fun u h => (hpw u h).trans (by rw [bw_t hb])) (fun _ => ?_) fun h => absurd h (by decide)
      exact frag_conseq (runF_set o rfl rfl (v := BitVec.ofNat 64 0) fun _ _ => rfl) (fun _ h => h)
        fun u h => ⟨(0, J), runF_divL h, h1, h2, .inr rfl⟩
    · refine DN.News.ScanRun.frag_if o rfl (lowK_any _ (k := .skip) rfl) (lowK_any _ (k := .skip) rfl) rfl rfl hIc
        (b := false) (fun u h => (hpw u h).trans (by rw [bw_f hb])) (fun h => absurd h (by decide)) fun _ => ?_
      refine frag_append (xs := [_]) (set_to o (l := divL X D A 1 J 0 0) (l' := divL X D A 1 (J - 1) 0 0) rfl rfl
        (v := jw (J - 1)) (fun u h => by
          simp only [eval, vals_lookup h.1.vals (show (divL X D A 1 J 0 0).lookup "j" = some (jw J) from rfl)]
          rw [jw_dec h4 h1])
        fun u h => runF_divL h) ?_
      have hX' : X < 2 ^ (J - 1) := by omega
      have hlt : ∀ u, RunF s1 (divL X D A 1 (J - 1) 0 0) (· = m0) u →
          eval u (.cmp .less (.var "j") (.const (BitVec.ofNat 64 0))) = some (bw (decide (J - 1 = 0))) :=
        fun u h => jw_lt0 (by omega) (vals_lookup h.1.vals rfl)
      by_cases hz : J - 1 = 0
      · refine frag_ifT o rfl (lowK_any _ (k := .skip) rfl) lowKK_nil rfl rfl hIc
          (fun u h => (hlt u h).trans (by rw [bw_t hz])) ?_
        exact frag_conseq (runF_set o rfl rfl (v := BitVec.ofNat 64 0) fun _ _ => rfl) (fun _ h => h)
          fun u h => ⟨(0, J - 1), runF_divL h, by omega, hX', .inr rfl⟩
      · exact frag_ifF o rfl (lowK_any _ (k := .skip) rfl) lowKK_nil rfl rfl hIc
          (fun u h => (hlt u h).trans (by rw [bw_f hz])) (frag_nil o fun u h => ⟨(1, J - 1), h, by omega, hX',
            .inl ⟨rfl, by omega⟩⟩)
  · intro u ⟨⟨t, h, h1, h2, h3⟩, h0⟩
    rcases h3 with ⟨e, _⟩ | e
    · rw [ev_var (vals_lookup h.1.vals rfl), e] at h0; exact absurd (Option.some.inj h0) (by decide)
    · obtain ⟨g, J⟩ := t
      simp only at e h1 h2 h; subst e
      exact ⟨J, h, h1, h2⟩

theorem ev_dbl {u : PancakeState σ} {R B : Nat} {E : PancakeExp} (hr : u.locals "rm" = some (BitVec.ofNat 64 R))
    (hE : eval u E = some (BitVec.ofNat 64 B)) :
    eval u (.op .add (.op .add (.var "rm") (.var "rm")) E) = some (BitVec.ofNat 64 (R + R + B)) := by
  simp only [eval, hr, hE]; rw [← BitVec.ofNat_add, ← BitVec.ofNat_add]

/-- **`artDiv`'s second loop takes the bits down**: past bit 0, the quotient and the remainder of `X` by `D`. -/
theorem div_loop2 (hA : Area ArticleProg.ofs A s1) (hP : Pows m0 A) (hD1 : 1 ≤ D)
    (hD2 : D ≤ 2 ^ 62) {J0 : Nat} (hJ0 : J0 ≤ 62) (hXJ : X < 2 ^ J0) :
    Frag o [.while (Syntax.eLe (Syntax.n 0) (Syntax.v "j")) divBody2] (RunF s1 (divL X D A 0 J0 0 0) (· = m0))
      (RunF s1 (divL X D A 0 0 (X / D) (X % D)) (· = m0)) := by
  let I : Assn σ := fun u => ∃ J, RunF s1 (divL X D A 0 J (X / 2 ^ J / D * 2 ^ J) (X / 2 ^ J % D)) (· = m0) u ∧ J ≤ 62
  have hIc : Safe.ClockFree I := fun u k ⟨J, h, hv⟩ => ⟨J, runF_clock _ _ _ u k h, hv⟩
  have hlow : LowKK divBody2 := lowK_any _ (k := .skip) rfl
  refine frag_conseq (frag_while o rfl hlow hIc
    (fun u z v ⟨J, h, hv⟩ hz => by
      change z ∈ ["pw"] at hz
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hz; subst hz
      exact ⟨J, runF_restore h rfl v, hv⟩) (fun u ⟨J, h, hJ⟩ => ⟨_, jw_ge0 hJ (vals_lookup h.1.vals rfl)⟩) ?_)
    (fun u h => ⟨J0, by rw [Nat.div_eq_of_lt hXJ, Nat.zero_div, Nat.zero_mul, Nat.zero_mod]; exact h, hJ0⟩) ?_
  · refine frag_conseq (P0 := fun u => ∃ J, (fun J u => RunF s1 (divL X D A 0 J (X / 2 ^ J / D * 2 ^ J)
      (X / 2 ^ J % D)) (· = m0) u ∧ J ≤ 62 ∧ 1 ≤ J) J u) (frag_exists hlow fun J => ?_)
      (fun u ⟨⟨J, h, hJ⟩, h0⟩ => ⟨J, h, hJ, by
        have e : eval u (.cmp .notLess (.var "j") (.const (BitVec.ofNat 64 0))) = _ :=
          jw_ge0 hJ (vals_lookup h.1.vals rfl)
        rw [e] at h0; exact of_decide_eq_true (bw_ne0 h0)⟩) fun _ h => h
    refine frag_pure (J ≤ 62 ∧ 1 ≤ J) (fun u h => h.2) hlow fun ⟨hJ, h1⟩ => ?_
    generalize hr : X / 2 ^ J = r
    generalize hb : X / 2 ^ (J - 1) % 2 = bit
    have hbit : bit ≤ 1 := by omega
    have hsh : X / 2 ^ (J - 1) = 2 * r + bit := by rw [← hr, ← hb]; exact shr_step X J h1
    have hrm : r % D < D := Nat.mod_lt _ (by omega)
    have hq : r / D * 2 ^ J ≤ X := by
      rw [← hr]; exact Nat.le_trans (Nat.mul_le_mul_right _ (Nat.div_le_self _ _)) (Nat.div_mul_le_self X _)
    obtain ⟨dm, dd⟩ := div_step r D bit hD1 hbit
    have hpj : 2 ^ J = 2 * 2 ^ (J - 1) := by
      rw [← Nat.pow_succ', Nat.succ_eq_add_one, Nat.sub_add_cancel h1]
    have hp62 : 2 ^ (J - 1) < 2 ^ 62 := Nat.pow_lt_pow_right (by decide) (by omega)
    let L0 := divL X D A 0 J (r / D * 2 ^ J) (r % D)
    refine frag_conseq (P0 := RunF s1 L0 (· = m0)) ?_ (fun u h => by
      show RunF s1 (divL X D A 0 J (r / D * 2 ^ J) (r % D)) _ u; rw [← hr]; exact h.1) fun _ h => h
    have hj : ∀ {l : List (String × Value)} {u}, RunF s1 l (· = m0) u → l.lookup "j" = some (jw J) →
        u.locals "j" = some (BitVec.ofNat 64 (J - 1)) :=
      fun h e => by rw [← jw_pos h1]; exact vals_lookup h.1.vals e
    refine frag_append (xs := [_]) (kept_frag o (by decide) (runF_clock _ _ _) fun u h =>
      ⟨J - 1, hj h rfl, by omega⟩) ?_
    refine frag_append (xs := [_]) (runF_dec o rfl rfl (v := BitVec.twoPow 64 (J - 1)) fun u h =>
      powAt_eval hA h.1.memaddrs (by rw [h.2]; exact hP) (vals_lookup h.1.vals rfl) (by omega)
        (ev_var (hj h rfl))) ?_
    let LP : Nat → Nat → List (String × Value) := fun q rm =>
      ("pw", BitVec.twoPow 64 (J - 1)) :: divL X D A 0 J q rm
    refine frag_append (xs := [_]) (set_to o (l := ("pw", BitVec.twoPow 64 (J - 1)) :: L0)
      (l' := LP (r / D * 2 ^ J) (r % D + r % D + bit)) rfl rfl (v := BitVec.ofNat 64 (r % D + r % D + bit))
      (fun u h => ev_dbl (vals_lookup h.1.vals rfl) (by
        rw [← hb]; exact divBit_eval (by omega) (vals_lookup h.1.vals rfl) (vals_lookup h.1.vals rfl)))
      fun u h => runF_push h rfl (runF_divL h)) ?_
    have hle : ∀ u, RunF s1 (LP (r / D * 2 ^ J) (r % D + r % D + bit)) (· = m0) u →
        eval u (FramerCode.leE (.var "d") (.var "rm")) = some (bw (decide (D ≤ r % D + r % D + bit))) :=
      fun u h => FramerCode.eval_le (by omega) (by omega) (ev_var (vals_lookup h.1.vals rfl))
        (ev_var (vals_lookup h.1.vals rfl))
    have hjd : ∀ q rm, Frag o [.assign "j" (Syntax.eSub (Syntax.v "j") (Syntax.n 1))] (RunF s1 (LP q rm) (· = m0))
        (RunF s1 (divL X D A 0 (J - 1) q rm) (· = m0)) := fun q rm =>
      set_to o (l := LP q rm) rfl rfl (v := jw (J - 1)) (fun u h => by
        simp only [eval, vals_lookup h.1.vals (show (LP q rm).lookup "j" = some (jw J) from rfl)]
        rw [jw_dec h1 hJ]) fun u h => runF_divL h
    by_cases hc : D ≤ r % D + r % D + bit
    · refine frag_append (xs := [_]) (frag_ifT o rfl (lowK_any _ (k := .skip) rfl) lowKK_nil rfl rfl
        (runF_clock _ _ _) (fun u h => (hle u h).trans (by rw [bw_t hc])) (Q := RunF s1
          (LP (r / D * 2 ^ J + 2 ^ (J - 1)) (r % D + r % D + bit - D)) (· = m0)) ?_) ?_
      · refine frag_append (xs := [_]) (set_to o (l := LP (r / D * 2 ^ J) (r % D + r % D + bit))
          (l' := LP (r / D * 2 ^ J) (r % D + r % D + bit - D)) rfl rfl
          (v := BitVec.ofNat 64 (r % D + r % D + bit - D)) (fun u h => DN.News.ArticleRun.ev_sub (y := D)
            (by rw [show D + (r % D + r % D + bit - D) = r % D + r % D + bit by omega]
                exact ev_var (vals_lookup h.1.vals rfl)) (ev_var (vals_lookup h.1.vals rfl)))
          fun u h => runF_push h rfl (runF_divL h)) ?_
        exact set_to o (l := LP (r / D * 2 ^ J) (r % D + r % D + bit - D)) rfl rfl
          (v := BitVec.ofNat 64 (r / D * 2 ^ J + 2 ^ (J - 1))) (fun u h => by
            simp only [eval, vals_lookup h.1.vals (show (LP (r / D * 2 ^ J) (r % D + r % D + bit - D)).lookup "q" =
              some (BitVec.ofNat 64 (r / D * 2 ^ J)) from rfl),
              vals_lookup h.1.vals (show (LP (r / D * 2 ^ J) (r % D + r % D + bit - D)).lookup "pw" =
              some (BitVec.twoPow 64 (J - 1)) from rfl)]
            rw [twoPow_ofNat, ← BitVec.ofNat_add]) fun u h => runF_push h rfl (runF_divL h)
      refine frag_conseq (hjd _ _) (fun _ h => h) fun u h => ⟨J - 1, ?_, by omega⟩
      have e1 : X / 2 ^ (J - 1) / D * 2 ^ (J - 1) = r / D * 2 ^ J + 2 ^ (J - 1) := by
        rw [hsh, dd, if_pos (by omega), hpj]
        generalize r / D = K; generalize 2 ^ (J - 1) = P
        rw [Nat.add_mul, Nat.one_mul, Nat.mul_assoc, Nat.mul_left_comm K 2 P]
      have e2 : X / 2 ^ (J - 1) % D = r % D + r % D + bit - D := by rw [hsh, dm, if_pos (by omega)]; omega
      rw [e1, e2]; exact h
    · refine frag_append (xs := [_]) (frag_ifF o rfl (lowK_any _ (k := .skip) rfl) lowKK_nil rfl rfl
        (runF_clock _ _ _) (fun u h => (hle u h).trans (by rw [bw_f hc])) (frag_nil o fun _ h => h)) ?_
      refine frag_conseq (hjd _ _) (fun _ h => h) fun u h => ⟨J - 1, ?_, by omega⟩
      have e1 : X / 2 ^ (J - 1) / D * 2 ^ (J - 1) = r / D * 2 ^ J := by
        rw [hsh, dd, if_neg (by omega), hpj]
        generalize r / D = K; generalize 2 ^ (J - 1) = P
        rw [Nat.add_zero, Nat.mul_assoc, Nat.mul_left_comm K 2 P]
      have e2 : X / 2 ^ (J - 1) % D = r % D + r % D + bit := by rw [hsh, dm, if_neg (by omega)]; omega
      rw [e1, e2]; exact h
  · intro u ⟨⟨J, h, hJ⟩, h0⟩
    have e : eval u (.cmp .notLess (.var "j") (.const (BitVec.ofNat 64 0))) = _ := jw_ge0 hJ (vals_lookup h.1.vals rfl)
    rw [e] at h0
    have hJ0' : J = 0 := by have := of_decide_eq_false (bw_eq0 h0); omega
    subst hJ0'
    simpa using h

/-- What `artDiv` gives back: `X / D`, changing no word. -/
def DivRet (X D : Nat) (m0 : Word → Word) : Ret := fun v m => v = BitVec.ofNat 64 (X / D) ∧ m = m0

/-- **`artDiv` divides**: of `X` below 2^62 by `D` from 1 to 2^62, if it returns, `X / D`. It reads the powers of two
and changes no word. -/
theorem artDiv_ok (hA : Area ArticleProg.ofs A s1) (hP : Pows s1.memory A) (hX : X < 2 ^ 62) (hD1 : 1 ≤ D)
    (hD2 : D ≤ 2 ^ 62) (hx : s1.locals "x" = some (BitVec.ofNat 64 X)) (hd : s1.locals "d" = some (BitVec.ofNat 64 D)) :
    ∃ body, Lower.lower (gd ArticleProg.artDiv) = some body ∧
      SafeR o (fun s => s = s1) body (DivRet X D s1.memory) fun _ => False := by
  refine body_of ?_
  show FragR o _ (guardL ArticleProg.artDiv.body) _ _
  rw [artDiv_body]
  obtain ⟨EA, hEA⟩ := atOff_lower ArticleProg.ofs
  refine fragR_conseq (P0 := RunF s1 [("x", BitVec.ofNat 64 X), ("d", BitVec.ofNat 64 D)] (· = s1.memory))
    ?_ (entry_two hx hd) fun _ h => h
  refine fragR_append (xs := [_]) (fragR_of (runF_dec o hEA rfl (v := A) fun u h => areaAt_eval hA h.1.base hEA)) ?_
  refine fragR_append (xs := [_]) (fragR_ifF o rfl (lowK_any _ (k := .skip) rfl) lowKK_nil rfl rfl
    (runF_clock _ _ _) (fun u h => (FramerCode.eval_or2 (FramerCode.eval_or2
        (FramerCode.eval_lt (by omega) (by decide) (ev_var (vals_lookup h.1.vals rfl)) rfl)
        (FramerCode.eval_lt (by decide) (by omega) rfl (ev_var (vals_lookup h.1.vals rfl))))
        (FramerCode.eval_or2 (FramerCode.eval_lt (by omega) (by decide) (ev_var (vals_lookup h.1.vals rfl)) rfl)
          (FramerCode.eval_lt (by decide) (by omega) rfl (ev_var (vals_lookup h.1.vals rfl))))).trans (by
      congr 2; simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not]; omega))
    (fragR_of (frag_nil o fun _ h => h))) ?_
  refine fragR_append (xs := [_]) (fragR_of (runF_dec o rfl rfl (v := BitVec.ofNat 64 0) fun _ _ => rfl)) ?_
  refine fragR_append (xs := [_]) (fragR_of (runF_dec o rfl rfl (v := BitVec.ofNat 64 0) fun _ _ => rfl)) ?_
  refine fragR_append (xs := [_]) (fragR_of (runF_dec o rfl rfl (v := BitVec.ofNat 64 61) fun _ _ => rfl)) ?_
  refine fragR_append (xs := [_]) (fragR_of (runF_dec o rfl rfl (v := BitVec.ofNat 64 1) fun _ _ => rfl)) ?_
  refine fragR_append (xs := [_]) (fragR_of (frag_conseq (div_loop1 o hA hP hX) (fun u h => runF_divL h)
    fun _ h => h)) ?_
  have hlow : LowKK [.while (Syntax.eLe (Syntax.n 0) (Syntax.v "j")) divBody2, .ret (Syntax.v "q")] :=
    lowK_any _ (k := .skip) rfl
  refine fragR_exists hlow fun J => ?_
  refine fragR_pure (J ≤ 62 ∧ X < 2 ^ J) (fun u h => h.2) hlow fun ⟨hJ, hXJ⟩ => ?_
  refine fragR_append (xs := [_]) (fragR_of (frag_conseq (div_loop2 o hA hP hD1 hD2 hJ hXJ) (fun u h => h.1)
    fun _ h => h)) ?_
  exact fragR_ret o rfl fun u h => ⟨_, ev_var (vals_lookup h.1.vals rfl), rfl, h.2⟩

end div

/-! ## The day of the calendar -/

theorem mem_artDiv : gd ArticleProg.artDiv ∈
    ArticleProg.functions ArticleSpec.spec (ArticleProg.entries ArticleSpec.spec) .none :=
  List.mem_append_right _ (List.mem_map.2 ⟨ArticleProg.artDiv, by simp, rfl⟩)

/-- **A call of `artDiv`**, the check after it passed: the quotient, the memory as it was. -/
theorem divCall_frag (o : Oracle σ) {R : Ret} {A : Word} {s0 : PancakeState σ} (hA : Area ArticleProg.ofs A s0)
    (hcode : ArtCode s0.code) {rt : String} (hra : rt ≠ "a") {l : List (String × Value)}
    (hla : l.lookup "a" = some A) (hrt : Fresh rt l = true) {m0 : Word → Word} (hP : Pows m0 A)
    (hb : m0 (at_ A aBroken) = 0) {e1 : Syntax.PExpr} {E1 : PancakeExp} (he1 : Lower.lowerExp e1 = some E1)
    {X D : Nat} (hX : X < 2 ^ 62) (hD1 : 1 ≤ D) (hD2 : D ≤ 2 ^ 62)
    (hv1 : ∀ u, RunF s0 l (· = m0) u → eval u E1 = some (BitVec.ofNat 64 X)) :
    FragR o R (guardS (.call rt "artDiv" [e1, Syntax.n D])) (RunF s0 l (· = m0))
      (RunF s0 ((rt, BitVec.ofNat 64 (X / D)) :: l) (· = m0)) := by
  refine fragR_conseq (gcall_frag o hA hcode hra (f := ArticleProg.artDiv) mem_artDiv (by decide)
    (DN.News.AbnfGen.lowerArgs_two (b := Syntax.n D) he1 rfl) hla (vs := [BitVec.ofNat 64 X, BitVec.ofNat 64 D]) rfl
    (fun u h => by simp only [evalArgs, hv1 u h]; rfl) (Rf := DivRet X D)
    (fun s1 hA1 _ _ _ hloc hF => artDiv_ok o hA1 (by rw [hF]; exact hP) hX hD1 hD2 ((hloc "x").trans rfl)
      ((hloc "d").trans rfl)) hrt
    (G := fun v m => m = m0 ∧ v = BitVec.ofNat 64 (X / D)) (fun m m' v hm ⟨e1, e2⟩ => ⟨e2.trans hm, e1⟩)
    fun v m h => by rw [h.1]; exact hb) (fun u h => h) fun u ⟨v, h⟩ => ?_
  obtain ⟨hm, hv⟩ := h.2
  subst hv; exact ⟨h.1, hm⟩

theorem ev_mulc {u : PancakeState σ} {x : String} {X c : Nat} (h : u.locals x = some (BitVec.ofNat 64 X)) :
    eval u (.mul (.var x) (.const (BitVec.ofNat 64 c))) = some (BitVec.ofNat 64 (X * c)) := by
  simp only [eval, h]; rw [← BitVec.ofNat_mul]

theorem ev_cmul {u : PancakeState σ} {x : String} {X c : Nat} (h : u.locals x = some (BitVec.ofNat 64 X)) :
    eval u (.mul (.const (BitVec.ofNat 64 c)) (.var x)) = some (BitVec.ofNat 64 (c * X)) := by
  simp only [eval, h]; rw [← BitVec.ofNat_mul]

theorem ev_subE {u : PancakeState σ} {a b : PancakeExp} {x y : Nat} (ha : eval u a = some (BitVec.ofNat 64 x))
    (hb : eval u b = some (BitVec.ofNat 64 y)) (h : y ≤ x) (hx : x < 2 ^ 64) :
    eval u (.op .sub a b) = some (BitVec.ofNat 64 (x - y)) := by
  simp only [eval, ha, hb]; rw [BitVec.ofNat_sub_ofNat_of_le _ _ (by omega) h]

/-- **A branch that may set `x` anew**: either way `x` then holds `v`, the other locals kept. -/
theorem reassign_frag (o : Oracle σ) {s1 : PancakeState σ} {F : (Word → Word) → Prop} {l : List (String × Value)}
    {x : String} {c : Syntax.PExpr} {C : PancakeExp} (hc : Lower.lowerExp c = some C) {e : Syntax.PExpr}
    {Ee : PancakeExp} (hEe : Lower.lowerExp e = some Ee) {v0 v : Value} (hfr : Fresh x l = true) {b : Bool}
    (hv : ∀ u, RunF s1 ((x, v0) :: l) F u → eval u C = some (bw b))
    (ht : b = true → ∀ u, RunF s1 ((x, v0) :: l) F u → eval u Ee = some v) (he : b = false → v0 = v) :
    Frag o [ArticleProg.ifs c [.assign x e]] (RunF s1 ((x, v0) :: l) F) (RunF s1 ((x, v) :: l) F) := by
  have hlt : LowKK [.assign x e] := lowKK_one rfl (a := .assign x Ee) (by simp [Lower.lowerStmt1, hEe])
  cases b
  · exact frag_ifF o hc hlt lowKK_nil rfl rfl (runF_clock _ _ _) hv (frag_nil o fun u h => by rw [← he rfl]; exact h)
  · refine frag_ifT o hc hlt lowKK_nil rfl rfl (runF_clock _ _ _) hv ?_
    refine frag_conseq (runF_set o hEe (show ((x, v0) :: l).lookup x = some v0 by simp) (ht rfl)) (fun _ h => h)
      fun u h => runF_mono h (fun q hq => ?_) fun _ e => e
    rcases List.mem_cons.1 hq with rfl | hq
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (mem_without (List.mem_cons_of_mem _ hq) (DN.News.ScanRun.fresh_ne hfr q hq))

theorem artCivilOf_body : guardL ArticleProg.artCivilOf.body =
    [areaAt ArticleProg.ofs, .dec "z" (Syntax.eAdd (Syntax.v "days") (Syntax.n 719468)),
     .call "era" "artDiv" [Syntax.v "z", Syntax.n 146097], brk,
     .dec "doe" (Syntax.eSub (Syntax.v "z") (Syntax.eMul (Syntax.v "era") (Syntax.n 146097))),
     .call "a1" "artDiv" [Syntax.v "doe", Syntax.n 1460], brk,
     .call "a2" "artDiv" [Syntax.v "doe", Syntax.n 36524], brk,
     .call "a3" "artDiv" [Syntax.v "doe", Syntax.n 146096], brk,
     .call "yoe" "artDiv" [Syntax.eSub (Syntax.eAdd (Syntax.eSub (Syntax.v "doe") (Syntax.v "a1")) (Syntax.v "a2"))
       (Syntax.v "a3"), Syntax.n 365], brk,
     .call "b1" "artDiv" [Syntax.v "yoe", Syntax.n 4], brk, .call "b2" "artDiv" [Syntax.v "yoe", Syntax.n 100], brk,
     .dec "doy" (Syntax.eSub (Syntax.v "doe") (Syntax.eSub (Syntax.eAdd (Syntax.eMul (Syntax.n 365) (Syntax.v "yoe"))
       (Syntax.v "b1")) (Syntax.v "b2"))),
     .call "mp" "artDiv" [Syntax.eAdd (Syntax.eMul (Syntax.n 5) (Syntax.v "doy")) (Syntax.n 2), Syntax.n 153], brk,
     .call "c1" "artDiv" [Syntax.eAdd (Syntax.eMul (Syntax.n 153) (Syntax.v "mp")) (Syntax.n 2), Syntax.n 5], brk,
     .dec "dy" (Syntax.eAdd (Syntax.eSub (Syntax.v "doy") (Syntax.v "c1")) (Syntax.n 1)),
     .dec "mo" (Syntax.eAdd (Syntax.v "mp") (Syntax.n 3)),
     ArticleProg.ifs (Syntax.eLe (Syntax.n 10) (Syntax.v "mp"))
       [.assign "mo" (Syntax.eSub (Syntax.v "mp") (Syntax.n 9))],
     .dec "yr" (Syntax.eAdd (Syntax.v "yoe") (Syntax.eMul (Syntax.v "era") (Syntax.n 400))),
     ArticleProg.ifs (Syntax.eLe (Syntax.v "mo") (Syntax.n 2)) [inc "yr"],
     .ret (Syntax.eAdd (Syntax.eAdd (Syntax.eMul (Syntax.v "yr") (Syntax.n 512))
       (Syntax.eMul (Syntax.v "mo") (Syntax.n 32)))
       (Syntax.v "dy"))] := rfl

/-- **`artCivilOf` gives the day of the calendar** of a day since 1970 below 2^30, if it returns (`civilFromDays`). It
changes no word. -/
theorem artCivilOf_ok (o : Oracle σ) {A : Word} {s1 : PancakeState σ} (hA : Area ArticleProg.ofs A s1)
    (hcode : ArtCode s1.code) (hP : Pows s1.memory A) (hb : s1.memory (at_ A aBroken) = 0) {z : Nat} (hz : z < 2 ^ 30)
    (hdays : s1.locals "days" = some (BitVec.ofNat 64 z)) :
    ∃ body, Lower.lower (gd ArticleProg.artCivilOf) = some body ∧
      SafeR o (fun s => s = s1) body (fun v m => v = BitVec.ofNat 64 (civilWord z) ∧ m = s1.memory) fun _ => False := by
  -- the values, as `ArticleSpec.civilFromDays` has them
  let zz := z + 719468
  let era := zz / 146097
  let doe := zz - era * 146097
  let a1 := doe / 1460
  let a2 := doe / 36524
  let a3 := doe / 146096
  let yoe := (doe - a1 + a2 - a3) / 365
  let b1 := yoe / 4
  let b2 := yoe / 100
  let doy := doe - (365 * yoe + b1 - b2)
  let mp := (5 * doy + 2) / 153
  let c1 := (153 * mp + 2) / 5
  let dy := doy - c1 + 1
  have g1 : doe < 146097 ∧ era * 146097 ≤ zz ∧ zz < 2 ^ 31 := by
    have : doe = zz - zz / 146097 * 146097 := rfl; have : zz = z + 719468 := rfl; omega
  have g7 : 365 * yoe + b1 - b2 ≤ doe := cal_doe doe g1.1
  have g2 : a1 ≤ doe ∧ a3 ≤ doe - a1 + a2 ∧ yoe < 400 ∧ b2 ≤ 365 * yoe + b1 ∧ c1 ≤ doy ∧ doy ≤ doe := by
    have : a1 = doe / 1460 := rfl; have : a2 = doe / 36524 := rfl; have : a3 = doe / 146096 := rfl
    have : yoe = (doe - a1 + a2 - a3) / 365 := rfl; have : b1 = yoe / 4 := rfl; have : b2 = yoe / 100 := rfl
    have : doy = doe - (365 * yoe + b1 - b2) := rfl; have : mp = (5 * doy + 2) / 153 := rfl
    have : c1 = (153 * mp + 2) / 5 := rfl; omega
  refine body_of ?_
  show FragR o _ (guardL ArticleProg.artCivilOf.body) _ _
  rw [artCivilOf_body]
  obtain ⟨EA, hEA⟩ := atOff_lower ArticleProg.ofs
  refine fragR_conseq (P0 := RunF s1 [("days", BitVec.ofNat 64 z)] (· = s1.memory)) ?_ (entry_one hdays)
    fun _ h => h
  refine fragR_append (xs := [_]) (fragR_of (runF_dec o hEA rfl (v := A) fun u h => areaAt_eval hA h.1.base hEA)) ?_
  refine fragR_append (xs := [_]) (fragR_of (runF_dec o rfl rfl (v := BitVec.ofNat 64 zz) fun u h =>
    ev_inc (vals_lookup h.1.vals rfl))) ?_
  refine fragR_append (xs := [_, _]) (divCall_frag o hA hcode (by decide) rfl rfl hP hb rfl (X := zz) (D := 146097)
    (by omega) (by decide) (by decide) fun u h => ev_var (vals_lookup h.1.vals rfl)) ?_
  refine fragR_append (xs := [_]) (fragR_of (runF_dec o rfl rfl (v := BitVec.ofNat 64 doe) fun u h =>
    ev_subE (ev_var (vals_lookup h.1.vals rfl)) (ev_mulc (vals_lookup h.1.vals rfl)) g1.2.1 (by omega))) ?_
  refine fragR_append (xs := [_, _]) (divCall_frag o hA hcode (by decide) rfl rfl hP hb rfl (X := doe) (D := 1460)
    (by omega) (by decide) (by decide) fun u h => ev_var (vals_lookup h.1.vals rfl)) ?_
  refine fragR_append (xs := [_, _]) (divCall_frag o hA hcode (by decide) rfl rfl hP hb rfl (X := doe) (D := 36524)
    (by omega) (by decide) (by decide) fun u h => ev_var (vals_lookup h.1.vals rfl)) ?_
  refine fragR_append (xs := [_, _]) (divCall_frag o hA hcode (by decide) rfl rfl hP hb rfl (X := doe) (D := 146096)
    (by omega) (by decide) (by decide) fun u h => ev_var (vals_lookup h.1.vals rfl)) ?_
  refine fragR_append (xs := [_, _]) (divCall_frag o hA hcode (by decide) rfl rfl hP hb rfl
    (X := doe - a1 + a2 - a3) (D := 365) (by omega) (by decide) (by decide) fun u h =>
      ev_subE (WpBytes.eval_add (ev_subE (ev_var (vals_lookup h.1.vals rfl)) (ev_var (vals_lookup h.1.vals rfl)) g2.1
        (by omega)) (ev_var (vals_lookup h.1.vals rfl))) (ev_var (vals_lookup h.1.vals rfl)) g2.2.1 (by omega)) ?_
  refine fragR_append (xs := [_, _]) (divCall_frag o hA hcode (by decide) rfl rfl hP hb rfl (X := yoe) (D := 4)
    (by omega) (by decide) (by decide) fun u h => ev_var (vals_lookup h.1.vals rfl)) ?_
  refine fragR_append (xs := [_, _]) (divCall_frag o hA hcode (by decide) rfl rfl hP hb rfl (X := yoe) (D := 100)
    (by omega) (by decide) (by decide) fun u h => ev_var (vals_lookup h.1.vals rfl)) ?_
  refine fragR_append (xs := [_]) (fragR_of (runF_dec o rfl rfl (v := BitVec.ofNat 64 doy) fun u h =>
    ev_subE (ev_var (vals_lookup h.1.vals rfl)) (ev_subE (WpBytes.eval_add (ev_cmul (vals_lookup h.1.vals rfl))
      (ev_var (vals_lookup h.1.vals rfl))) (ev_var (vals_lookup h.1.vals rfl)) g2.2.2.2.1 (by omega)) g7
      (by omega))) ?_
  refine fragR_append (xs := [_, _]) (divCall_frag o hA hcode (by decide) rfl rfl hP hb rfl (X := 5 * doy + 2)
    (D := 153) (by omega) (by decide) (by decide) fun u h =>
      WpBytes.eval_add (ev_cmul (vals_lookup h.1.vals rfl)) rfl) ?_
  refine fragR_append (xs := [_, _]) (divCall_frag o hA hcode (by decide) rfl rfl hP hb rfl (X := 153 * mp + 2)
    (D := 5) (by omega) (by decide) (by decide) fun u h =>
      WpBytes.eval_add (ev_cmul (vals_lookup h.1.vals rfl)) rfl) ?_
  refine fragR_append (xs := [_]) (fragR_of (runF_dec o rfl rfl (v := BitVec.ofNat 64 dy) fun u h =>
    WpBytes.eval_add (ev_subE (ev_var (vals_lookup h.1.vals rfl)) (ev_var (vals_lookup h.1.vals rfl)) g2.2.2.2.2.1
      (by omega)) rfl)) ?_
  refine fragR_append (xs := [_]) (fragR_of (runF_dec o rfl rfl (v := BitVec.ofNat 64 (mp + 3)) fun u h =>
    ev_inc (vals_lookup h.1.vals rfl))) ?_
  let mo := if mp < 10 then mp + 3 else mp - 9
  have hmoB : mo ≤ 12 := by
    have : mp = (5 * doy + 2) / 153 := rfl
    show (if mp < 10 then mp + 3 else mp - 9) ≤ 12; split <;> omega
  refine fragR_append (xs := [_]) (fragR_of (reassign_frag o (x := "mo") (v0 := BitVec.ofNat 64 (mp + 3))
    (v := BitVec.ofNat 64 mo) rfl rfl rfl (b := decide (10 ≤ mp)) (fun u h => FramerCode.eval_le (by decide) (by omega)
      rfl (ev_var (vals_lookup h.1.vals rfl)))
    (fun hb u h => (ev_subE (ev_var (vals_lookup h.1.vals rfl)) rfl (by have := of_decide_eq_true hb; omega)
      (by omega)).trans (by
      show _ = some (BitVec.ofNat 64 (if mp < 10 then mp + 3 else mp - 9))
      rw [if_neg (by simpa using hb)]))
    (fun hb => by
      show BitVec.ofNat 64 (mp + 3) = BitVec.ofNat 64 (if mp < 10 then mp + 3 else mp - 9)
      rw [if_pos (by simpa using hb)]))) ?_
  refine fragR_append (xs := [_]) (fragR_of (runF_dec o rfl rfl (v := BitVec.ofNat 64 (yoe + era * 400)) fun u h =>
    WpBytes.eval_add (ev_var (vals_lookup h.1.vals rfl)) (ev_mulc (vals_lookup h.1.vals rfl)))) ?_
  let yr := if mo ≤ 2 then yoe + era * 400 + 1 else yoe + era * 400
  refine fragR_append (xs := [_]) (fragR_of (reassign_frag o (x := "yr") (v0 := BitVec.ofNat 64 (yoe + era * 400))
    (v := BitVec.ofNat 64 yr) rfl rfl rfl (b := decide (mo ≤ 2)) (fun u h => FramerCode.eval_le (by omega) (by decide)
      (ev_var (vals_lookup h.1.vals rfl)) rfl)
    (fun hb u h => (ev_inc (vals_lookup h.1.vals rfl)).trans (by
      show _ = some (BitVec.ofNat 64 (if mo ≤ 2 then yoe + era * 400 + 1 else yoe + era * 400))
      rw [if_pos (by simpa using hb)]))
    (fun hb => by
      show BitVec.ofNat 64 (yoe + era * 400) = BitVec.ofNat 64 (if mo ≤ 2 then yoe + era * 400 + 1 else yoe + era * 400)
      rw [if_neg (by simpa using hb)]))) ?_
  exact fragR_ret o rfl fun u h => ⟨_, WpBytes.eval_add (WpBytes.eval_add (ev_mulc (vals_lookup h.1.vals rfl))
    (ev_mulc (vals_lookup h.1.vals rfl))) (ev_var (vals_lookup h.1.vals rfl)), rfl, h.2⟩

/-! ## The days of a day of the calendar -/

theorem ofNat_sub_int (N c : Nat) : BitVec.ofNat 64 N - BitVec.ofNat 64 c = BitVec.ofInt 64 ((N : Int) - c) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofInt]
  omega

theorem ev_subC {u : PancakeState σ} {a : PancakeExp} {N c : Nat} (ha : eval u a = some (BitVec.ofNat 64 N)) :
    eval u (.op .sub a (.const (BitVec.ofNat 64 c))) = some (BitVec.ofNat 64 N - BitVec.ofNat 64 c) := by
  simp only [eval, ha]

theorem artCivil_body : guardL ArticleProg.artCivil.body =
    [areaAt ArticleProg.ofs, .dec "y1" (Syntax.v "y"),
     ArticleProg.ifs (Syntax.eLe (Syntax.v "mo") (Syntax.n 2)) [.assign "y1" (Syntax.eSub (Syntax.v "y") (Syntax.n 1))],
     .call "era" "artDiv" [Syntax.v "y1", Syntax.n 400], brk,
     .dec "yoe" (Syntax.eSub (Syntax.v "y1") (Syntax.eMul (Syntax.v "era") (Syntax.n 400))),
     .dec "mp" (Syntax.eAdd (Syntax.v "mo") (Syntax.n 9)),
     ArticleProg.ifs (Syntax.eLt (Syntax.n 2) (Syntax.v "mo"))
       [.assign "mp" (Syntax.eSub (Syntax.v "mo") (Syntax.n 3))],
     .call "q5" "artDiv" [Syntax.eAdd (Syntax.eMul (Syntax.n 153) (Syntax.v "mp")) (Syntax.n 2), Syntax.n 5], brk,
     .call "q4" "artDiv" [Syntax.v "yoe", Syntax.n 4], brk, .call "qc" "artDiv" [Syntax.v "yoe", Syntax.n 100], brk,
     .ret (Syntax.eSub (Syntax.eAdd (Syntax.eAdd (Syntax.eMul (Syntax.v "era") (Syntax.n 146097))
        (Syntax.eMul (Syntax.v "yoe") (Syntax.n 365)))
        (Syntax.eSub (Syntax.eAdd (Syntax.v "q4") (Syntax.eSub (Syntax.eAdd (Syntax.v "q5") (Syntax.v "d"))
          (Syntax.n 1))) (Syntax.v "qc"))) (Syntax.n 719468))] := rfl

/-- **`artCivil` gives the days since 1970 of a day of the calendar** (`daysFromCivil`), if it returns. The year and
the day are from 1 and below 2^40, the month at most 12. It changes no word. -/
theorem artCivil_ok (o : Oracle σ) {A : Word} {s1 : PancakeState σ} (hA : Area ArticleProg.ofs A s1)
    (hcode : ArtCode s1.code) (hP : Pows s1.memory A) (hb : s1.memory (at_ A aBroken) = 0) {Y M Dd : Nat} (hY1 : 1 ≤ Y)
    (hY : Y < 2 ^ 40) (hM : M ≤ 12) (hD1 : 1 ≤ Dd) (hD : Dd < 2 ^ 40) (hy : s1.locals "y" = some (BitVec.ofNat 64 Y))
    (hmo : s1.locals "mo" = some (BitVec.ofNat 64 M)) (hd : s1.locals "d" = some (BitVec.ofNat 64 Dd)) :
    ∃ body, Lower.lower (gd ArticleProg.artCivil) = some body ∧
      SafeR o (fun s => s = s1) body (fun v m => v = BitVec.ofInt 64 (ArticleSpec.daysFromCivil Y M Dd) ∧
        m = s1.memory) fun _ => False := by
  let y1 := if M ≤ 2 then Y - 1 else Y
  let era := y1 / 400
  let yoe := y1 - era * 400
  let mp := if 2 < M then M - 3 else M + 9
  let q5 := (153 * mp + 2) / 5
  have hy1 : y1 < 2 ^ 40 := by show (if M ≤ 2 then Y - 1 else Y) < 2 ^ 40; split <;> omega
  have hera : era * 400 ≤ y1 := Nat.div_mul_le_self _ _
  have hyoe : yoe < 400 := by have : yoe = y1 - y1 / 400 * 400 := rfl; omega
  have hmp : mp ≤ 21 := by show (if 2 < M then M - 3 else M + 9) ≤ 21; split <;> omega
  refine body_of ?_
  show FragR o _ (guardL ArticleProg.artCivil.body) _ _
  rw [artCivil_body]
  obtain ⟨EA, hEA⟩ := atOff_lower ArticleProg.ofs
  refine fragR_conseq (P0 := RunF s1 [("y", BitVec.ofNat 64 Y), ("mo", BitVec.ofNat 64 M), ("d", BitVec.ofNat 64 Dd)]
    (· = s1.memory)) ?_ (entry_run (fun q hq => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl
      · exact hy
      · exact hmo
      · exact hd) rfl) fun _ h => h
  refine fragR_append (xs := [_]) (fragR_of (runF_dec o hEA rfl (v := A) fun u h => areaAt_eval hA h.1.base hEA)) ?_
  refine fragR_append (xs := [_]) (fragR_of (runF_dec o rfl rfl (v := BitVec.ofNat 64 Y) fun u h =>
    ev_var (vals_lookup h.1.vals rfl))) ?_
  refine fragR_append (xs := [_]) (fragR_of (reassign_frag o (x := "y1") (v0 := BitVec.ofNat 64 Y)
    (v := BitVec.ofNat 64 y1) rfl rfl rfl (b := decide (M ≤ 2)) (fun u h => FramerCode.eval_le (by omega) (by decide)
      (ev_var (vals_lookup h.1.vals rfl)) rfl)
    (fun hb u h => (ev_subE (ev_var (vals_lookup h.1.vals rfl)) rfl hY1 (by omega)).trans (by
      show _ = some (BitVec.ofNat 64 (if M ≤ 2 then Y - 1 else Y)); rw [if_pos (by simpa using hb)]))
    (fun hb => by
      show BitVec.ofNat 64 Y = BitVec.ofNat 64 (if M ≤ 2 then Y - 1 else Y); rw [if_neg (by simpa using hb)]))) ?_
  refine fragR_append (xs := [_, _]) (divCall_frag o hA hcode (by decide) rfl rfl hP hb rfl (X := y1) (D := 400)
    (by omega) (by decide) (by decide) fun u h => ev_var (vals_lookup h.1.vals rfl)) ?_
  refine fragR_append (xs := [_]) (fragR_of (runF_dec o rfl rfl (v := BitVec.ofNat 64 yoe) fun u h =>
    ev_subE (ev_var (vals_lookup h.1.vals rfl)) (ev_mulc (vals_lookup h.1.vals rfl)) hera (by omega))) ?_
  refine fragR_append (xs := [_]) (fragR_of (runF_dec o rfl rfl (v := BitVec.ofNat 64 (M + 9)) fun u h =>
    ev_inc (vals_lookup h.1.vals rfl))) ?_
  refine fragR_append (xs := [_]) (fragR_of (reassign_frag o (x := "mp") (v0 := BitVec.ofNat 64 (M + 9))
    (v := BitVec.ofNat 64 mp) rfl rfl rfl (b := decide (2 < M)) (fun u h => FramerCode.eval_lt (by decide) (by omega)
      rfl (ev_var (vals_lookup h.1.vals rfl)))
    (fun hb u h => (ev_subE (ev_var (vals_lookup h.1.vals rfl)) rfl (by have := of_decide_eq_true hb; omega)
      (by omega)).trans (by
        show _ = some (BitVec.ofNat 64 (if 2 < M then M - 3 else M + 9)); rw [if_pos (by simpa using hb)]))
    (fun hb => by
      show BitVec.ofNat 64 (M + 9) = BitVec.ofNat 64 (if 2 < M then M - 3 else M + 9)
      rw [if_neg (by simpa using hb)]))) ?_
  refine fragR_append (xs := [_, _]) (divCall_frag o hA hcode (by decide) rfl rfl hP hb rfl (X := 153 * mp + 2)
    (D := 5) (by omega) (by decide) (by decide) fun u h => WpBytes.eval_add (ev_cmul (vals_lookup h.1.vals rfl)) rfl) ?_
  refine fragR_append (xs := [_, _]) (divCall_frag o hA hcode (by decide) rfl rfl hP hb rfl (X := yoe) (D := 4)
    (by omega) (by decide) (by decide) fun u h => ev_var (vals_lookup h.1.vals rfl)) ?_
  refine fragR_append (xs := [_, _]) (divCall_frag o hA hcode (by decide) rfl rfl hP hb rfl (X := yoe) (D := 100)
    (by omega) (by decide) (by decide) fun u h => ev_var (vals_lookup h.1.vals rfl)) ?_
  refine fragR_ret o rfl fun u h => ⟨BitVec.ofNat 64 (era * 146097 + yoe * 365 + (yoe / 4 + (q5 + Dd - 1) - yoe / 100))
    - BitVec.ofNat 64 719468, ?_, ?_, h.2⟩
  · exact ev_subC (WpBytes.eval_add (WpBytes.eval_add (ev_mulc (vals_lookup h.1.vals rfl))
        (ev_mulc (vals_lookup h.1.vals rfl)))
      (ev_subE (WpBytes.eval_add (ev_var (vals_lookup h.1.vals rfl))
        (ev_subE (WpBytes.eval_add (ev_var (vals_lookup h.1.vals rfl))
        (ev_var (vals_lookup h.1.vals rfl))) rfl (show 1 ≤ q5 + Dd by omega) (by omega)))
        (ev_var (vals_lookup h.1.vals rfl)) (show yoe / 100 ≤ yoe / 4 + (q5 + Dd - 1) by omega) (by omega)))
  · have hN : era * 146097 + yoe * 365 + (yoe / 4 + (q5 + Dd - 1) - yoe / 100) =
        era * 146097 + (yoe * 365 + yoe / 4 - yoe / 100 + (q5 + Dd - 1)) := by omega
    rw [ofNat_sub_int, hN]
    rfl

end DN.News.ArticleCal
