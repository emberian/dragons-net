-- SPDX-License-Identifier: AGPL-3.0-or-later
import DN.News.AbnfLeaves

/-!
# DN.News.AbnfComment

`ruleComment`, proven to do what it is named for (`ruleComment_ok`). If it returns, its slot holds where each comment
opening at another slot's position closes. Those are the ends of the grammar's `comment` matches (`commentAdd_iff`); its
scan is `AbnfMatch.step`'s.
-/

namespace DN.News.AbnfComment

open DN.Compiler DN.Compiler.Wp DN.Compiler.WpRet DN.Compiler.Frag DN.News.AbnfProg DN.News.AbnfLayout
open DN.News.AbnfSets DN.News.FunRun DN.News.AbnfLeaves
open DN.News.ScanRun (at_ at_add at_ne at_inj Vals vals_lookup vals_cons vals_set Fresh without lookup_head
  lookup_without)
open DN.News.FramerCode (bw ev_var)
open DN.News.AbnfMatch (Step step Runs isWsp isCtext isVchar Matches)

variable {σ : Type}

/-! ## The scan, as the model takes it -/

theorem runs_go {input : Array Nat} {y d s y' d' s' e : Nat} (h : step input y d s = .go y' d' s') :
    Runs input y d s e ↔ Runs input y' d' s' e :=
  ⟨fun r => (by
    cases r with
    | done h' => rw [h] at h'; cases h'
    | go h' r' => rw [h] at h'; cases h'; exact r'), fun r => .go h r⟩

theorem runs_fail {input : Array Nat} {y d s e : Nat} (h : step input y d s = .fail) : ¬Runs input y d s e :=
  fun r => by
    cases r with
    | done h' => rw [h] at h'; cases h'
    | go h' _ => rw [h] at h'; cases h'

theorem runs_done {input : Array Nat} {y d s e e' : Nat} (h : step input y d s = .done e') :
    Runs input y d s e ↔ e = e' :=
  ⟨fun r => (by
    cases r with
    | done h' => rw [h] at h'; cases h'; rfl
    | go h' _ => rw [h] at h'; cases h'), fun r => r ▸ .done h⟩

/-- The scan ends inside the input. -/
theorem runs_le {input : Array Nat} {y d s e : Nat} (h : Runs input y d s e) : e ≤ input.size := by
  induction h with
  | done h =>
    obtain ⟨-, h41, -, rfl⟩ := AbnfMatch.step_done h
    exact lt_of_some h41
  | go _ _ ih => exact ih

/-- A step that goes on keeps a comment open, the state one of four, and the input not passed. -/
theorem step_bounds {input : Array Nat} {y d s y' d' s' : Nat} (h : step input y d s = .go y' d' s')
    (hd : 1 ≤ d) (hdy : d ≤ y) (hs : s ≤ 3) : 1 ≤ d' ∧ d' ≤ y' ∧ s' ≤ 3 ∧ y' ≤ input.size := by
  rcases AbnfMatch.step_go h with ⟨-, ⟨b, hb, -⟩, rfl, rfl, rfl⟩ | ⟨-, ⟨b, hb, -⟩, rfl, rfl, rfl⟩ |
      ⟨-, -, ⟨-, hb⟩, rfl, rfl, rfl⟩ | ⟨-, ⟨b, hb, -⟩, rfl, rfl, rfl⟩ | ⟨-, -, ⟨c, hb, -⟩, rfl, rfl, rfl⟩ |
      ⟨-, hb, rfl, rfl, rfl⟩ | ⟨-, hb, h1, rfl, rfl, rfl⟩
  all_goals have := lt_of_some hb
  all_goals first | (refine ⟨by omega, by omega, by split <;> omega, by omega⟩) | omega

/-- What one step leaves in the scan's locals: the model's next ones with `go` 1. `go` is cleared where it fails; `y`
past the comment and `go` 2 where it closes. -/
def Out : Step → Nat → Nat → Nat → Nat → Prop
  | .go y' d' s', y, d, s, g => y = y' ∧ d = d' ∧ s = s' ∧ g = 1
  | .fail, _, _, _, g => g = 0
  | .done e, y, _, _, g => y = e ∧ g = 2

/-! ## The scan's locals -/

/-- The scan's locals before `base`. -/
def SL (y d s g : Nat) (base : List (String × Value)) : List (String × Value) :=
  ("go", BitVec.ofNat 64 g) :: ("sm", BitVec.ofNat 64 s) :: ("dep", BitVec.ofNat 64 d) :: ("y", BitVec.ofNat 64 y) ::
    base

theorem sl_lookup {y d s g : Nat} {base : List (String × Value)} {z : String} (h1 : z ≠ "go") (h2 : z ≠ "sm")
    (h3 : z ≠ "dep") (h4 : z ≠ "y") : (SL y d s g base).lookup z = base.lookup z := by
  rw [SL, ScanRun.lookup_cons_ne h1, ScanRun.lookup_cons_ne h2, ScanRun.lookup_cons_ne h3, ScanRun.lookup_cons_ne h4]

theorem runF_set' (o : Oracle σ) {s0 : PancakeState σ} {l l' : List (String × Value)} {F : (Word → Word) → Prop}
    {x : String} {e : Syntax.PExpr} {E : PancakeExp} (he : Lower.lowerExp e = some E) {w : Value}
    (hl : l.lookup x = some w) {v : Value} (hv : ∀ u, RunF s0 l F u → eval u E = some v)
    (h' : ∀ q ∈ l', q = (x, v) ∨ (q ∈ l ∧ q.1 ≠ x)) : Frag o [.assign x e] (RunF s0 l F) (RunF s0 l' F) :=
  frag_conseq (runF_set o he hl hv) (fun _ h => h) fun _ h => runF_mono h (fun q hq => by
    rcases h' q hq with rfl | ⟨h1, h2⟩
    · exact List.mem_cons_self ..
    · exact List.mem_cons_of_mem _ (mem_without h1 h2)) fun _ e => e

section
variable (o : Oracle σ) {s0 : PancakeState σ} {F : (Word → Word) → Prop} {base : List (String × Value)}
  {y d s g : Nat} {e : Syntax.PExpr} {E : PancakeExp}

theorem sl_go (hb : Fresh "go" base = true) (he : Lower.lowerExp e = some E) {g' : Nat}
    (hv : ∀ u, RunF s0 (SL y d s g base) F u → eval u E = some (BitVec.ofNat 64 g')) :
    Frag o [.assign "go" e] (RunF s0 (SL y d s g base) F) (RunF s0 (SL y d s g' base) F) :=
  runF_set' o he rfl hv fun q hq => by
    simp only [SL, List.mem_cons] at hq
    rcases hq with rfl | rfl | rfl | rfl | hq
    · exact .inl rfl
    · exact .inr ⟨by simp [SL], by simp⟩
    · exact .inr ⟨by simp [SL], by simp⟩
    · exact .inr ⟨by simp [SL], by simp⟩
    · exact .inr ⟨by simp [SL, hq], ScanRun.fresh_ne hb _ hq⟩

theorem sl_sm (hb : Fresh "sm" base = true) (he : Lower.lowerExp e = some E) {s' : Nat}
    (hv : ∀ u, RunF s0 (SL y d s g base) F u → eval u E = some (BitVec.ofNat 64 s')) :
    Frag o [.assign "sm" e] (RunF s0 (SL y d s g base) F) (RunF s0 (SL y d s' g base) F) :=
  runF_set' o he rfl hv fun q hq => by
    simp only [SL, List.mem_cons] at hq
    rcases hq with rfl | rfl | rfl | rfl | hq
    · exact .inr ⟨by simp [SL], by simp⟩
    · exact .inl rfl
    · exact .inr ⟨by simp [SL], by simp⟩
    · exact .inr ⟨by simp [SL], by simp⟩
    · exact .inr ⟨by simp [SL, hq], ScanRun.fresh_ne hb _ hq⟩

theorem sl_dep (hb : Fresh "dep" base = true) (he : Lower.lowerExp e = some E) {d' : Nat}
    (hv : ∀ u, RunF s0 (SL y d s g base) F u → eval u E = some (BitVec.ofNat 64 d')) :
    Frag o [.assign "dep" e] (RunF s0 (SL y d s g base) F) (RunF s0 (SL y d' s g base) F) :=
  runF_set' o he rfl hv fun q hq => by
    simp only [SL, List.mem_cons] at hq
    rcases hq with rfl | rfl | rfl | rfl | hq
    · exact .inr ⟨by simp [SL], by simp⟩
    · exact .inr ⟨by simp [SL], by simp⟩
    · exact .inl rfl
    · exact .inr ⟨by simp [SL], by simp⟩
    · exact .inr ⟨by simp [SL, hq], ScanRun.fresh_ne hb _ hq⟩

theorem sl_y (hb : Fresh "y" base = true) (he : Lower.lowerExp e = some E) {y' : Nat}
    (hv : ∀ u, RunF s0 (SL y d s g base) F u → eval u E = some (BitVec.ofNat 64 y')) :
    Frag o [.assign "y" e] (RunF s0 (SL y d s g base) F) (RunF s0 (SL y' d s g base) F) :=
  runF_set' o he rfl hv fun q hq => by
    simp only [SL, List.mem_cons] at hq
    rcases hq with rfl | rfl | rfl | rfl | hq
    · exact .inr ⟨by simp [SL], by simp⟩
    · exact .inr ⟨by simp [SL], by simp⟩
    · exact .inr ⟨by simp [SL], by simp⟩
    · exact .inl rfl
    · exact .inr ⟨by simp [SL, hq], ScanRun.fresh_ne hb _ hq⟩

end

theorem ev_inc {u : PancakeState σ} {x : String} {X c : Nat} (h : u.locals x = some (BitVec.ofNat 64 X)) :
    eval u (.op .add (.var x) (.const (BitVec.ofNat 64 c))) = some (BitVec.ofNat 64 (X + c)) := by
  simp only [eval, h]; rw [← BitVec.ofNat_add]

/-! ## A byte's class -/

/-- Whether a byte is in ranges `rs`, as `inClass` tests it. -/
def rangesE (rs : List (Nat × Nat)) (b : Syntax.PExpr) : Syntax.PExpr :=
  (rs.map fun (lo, hi) => Syntax.eAnd (Syntax.eLe (Syntax.n lo) b) (Syntax.eLe b (Syntax.n hi))).foldl Syntax.eOr
    (Syntax.n 0)

theorem rules_named : ruleIndex "wsp" = 166 ∧ ruleIndex "ctext" = 38 ∧ ruleIndex "vchar" = 163 := by
  decide +kernel
theorem classes_named : classOf steps (termOf 166) = some [(32, 32), (9, 9)] ∧
    classOf steps (termOf 38) = some [(33, 39), (42, 91), (93, 126)] ∧
    classOf steps (termOf 163) = some [(33, 126)] := by decide +kernel
theorem classOf_wsp : classOf steps (termOf (ruleIndex "wsp")) = some [(32, 32), (9, 9)] := by
  rw [rules_named.1]; exact classes_named.1
theorem classOf_ctext : classOf steps (termOf (ruleIndex "ctext")) = some [(33, 39), (42, 91), (93, 126)] := by
  rw [rules_named.2.1]; exact classes_named.2.1
theorem classOf_vchar : classOf steps (termOf (ruleIndex "vchar")) = some [(33, 126)] := by
  rw [rules_named.2.2]; exact classes_named.2.2

theorem inClass_of {r : String} {rs : List (Nat × Nat)} (h : classOf steps (termOf (ruleIndex r)) = some rs)
    (b : Syntax.PExpr) : inClass r b = rangesE rs b := by
  unfold inClass; rw [h]; rfl
theorem inClass_wsp (b : Syntax.PExpr) : inClass "wsp" b = rangesE [(32, 32), (9, 9)] b := inClass_of classOf_wsp b
theorem inClass_ctext (b : Syntax.PExpr) : inClass "ctext" b = rangesE [(33, 39), (42, 91), (93, 126)] b :=
  inClass_of classOf_ctext b
theorem inClass_vchar (b : Syntax.PExpr) : inClass "vchar" b = rangesE [(33, 126)] b := inClass_of classOf_vchar b

theorem bw_or (p q : Bool) : bw p ||| bw q = bw (p || q) := by cases p <;> cases q <;> decide

theorem ranges_eval {u : PancakeState σ} {b : Syntax.PExpr} {Eb : PancakeExp} (hb0 : Lower.lowerExp b = some Eb)
    {B : Nat} (hB : B < 256) (hb : eval u Eb = some (BitVec.ofNat 64 B)) :
    ∀ (rs : List (Nat × Nat)), (∀ r ∈ rs, r.1 < 256 ∧ r.2 < 256) → ∀ (a : Syntax.PExpr) (Ea : PancakeExp) (p : Bool),
      Lower.lowerExp a = some Ea → eval u Ea = some (bw p) → ∀ E, Lower.lowerExp ((rs.map fun (lo, hi) =>
        Syntax.eAnd (Syntax.eLe (Syntax.n lo) b) (Syntax.eLe b (Syntax.n hi))).foldl Syntax.eOr a) = some E →
      eval u E = some (bw (p || rs.any fun r => decide (r.1 ≤ B) && decide (B ≤ r.2)))
  | [], _, a, Ea, p, ha, hp, E, hE => by
    simp only [List.map_nil, List.foldl_nil] at hE; rw [ha] at hE; cases hE; simpa using hp
  | (lo, hi) :: rs, hrs, a, Ea, p, ha, hp, E, hE => by
    have hr := hrs (lo, hi) (List.mem_cons_self ..)
    have h1 : Lower.lowerExp (Syntax.eOr a (Syntax.eAnd (Syntax.eLe (Syntax.n lo) b) (Syntax.eLe b (Syntax.n hi)))) =
        some (.op .or_ Ea (.op .and_ (FramerCode.leE (.const (BitVec.ofNat 64 lo)) Eb)
          (FramerCode.leE Eb (.const (BitVec.ofNat 64 hi))))) := by
      simp only [Syntax.eOr, Syntax.eAnd, Syntax.eLe, Syntax.n, Lower.lowerExp, ha, hb0]; rfl
    have e1 := FramerCode.eval_le (a := .const (BitVec.ofNat 64 lo)) (x := lo) (y := B) (by omega) (by omega) rfl hb
    have e2 := FramerCode.eval_le (b := .const (BitVec.ofNat 64 hi)) (x := B) (y := hi) (by omega) (by omega) hb rfl
    have h2 := FramerCode.eval_or hp (FramerCode.eval_and e1 e2)
    rw [bw_or] at h2
    rw [ranges_eval hb0 hB hb rs (fun r hr' => hrs r (List.mem_cons_of_mem _ hr')) _ _ _ h1 h2 E hE]
    simp only [List.any_cons, Bool.or_assoc]

theorem wsp_eval {u : PancakeState σ} {b : Syntax.PExpr} {Eb : PancakeExp} (hb0 : Lower.lowerExp b = some Eb)
    {B : Nat} (hB : B < 256) (hb : eval u Eb = some (BitVec.ofNat 64 B)) {E : PancakeExp}
    (hE : Lower.lowerExp (rangesE [(32, 32), (9, 9)] b) = some E) : eval u E = some (bw (isWsp B)) := by
  rw [ranges_eval hb0 hB hb _ (by decide) _ _ false rfl rfl E hE]
  congr 2
  rw [Bool.eq_iff_iff]
  simp only [Bool.false_or, List.any_cons, List.any_nil, Bool.or_false, Bool.or_eq_true, Bool.and_eq_true,
    decide_eq_true_eq, isWsp, beq_iff_eq]
  omega

theorem ctext_eval {u : PancakeState σ} {b : Syntax.PExpr} {Eb : PancakeExp} (hb0 : Lower.lowerExp b = some Eb)
    {B : Nat} (hB : B < 256) (hb : eval u Eb = some (BitVec.ofNat 64 B)) {E : PancakeExp}
    (hE : Lower.lowerExp (rangesE [(33, 39), (42, 91), (93, 126)] b) = some E) : eval u E = some (bw (isCtext B)) := by
  rw [ranges_eval hb0 hB hb _ (by decide) _ _ false rfl rfl E hE]
  congr 2
  simp only [Bool.false_or, List.any_cons, List.any_nil, Bool.or_false, isCtext, Bool.or_assoc]

theorem vchar_eval {u : PancakeState σ} {b : Syntax.PExpr} {Eb : PancakeExp} (hb0 : Lower.lowerExp b = some Eb)
    {B : Nat} (hB : B < 256) (hb : eval u Eb = some (BitVec.ofNat 64 B)) {E : PancakeExp}
    (hE : Lower.lowerExp (rangesE [(33, 126)] b) = some E) : eval u E = some (bw (isVchar B)) := by
  rw [ranges_eval hb0 hB hb _ (by decide) _ _ false rfl rfl E hE]
  congr 2
  simp only [Bool.false_or, List.any_cons, List.any_nil, Bool.or_false, isVchar]

/-- A byte below the slots loads. -/
theorem byte_any {ofs : Nat} {A : Word} {s0 u : PancakeState σ} (hA : Area ofs A s0) (hm : u.memaddrs = s0.memaddrs)
    {E : PancakeExp} {x : Nat} (hx : x < aSets) (hE : eval u E = some (at_ A x)) :
    ∃ B, B < 256 ∧ eval u (.loadByte E) = some (BitVec.ofNat 64 B) := by
  have hd : u.memaddrs (byteAlign (at_ A x)) = true := by
    rw [ScanRun.align_at hA.hA, hm]; exact hA.dom _ (by omega) (by omega)
  refine ⟨(getByte (at_ A x) (u.memory (byteAlign (at_ A x))) u.be).toNat, BitVec.isLt _, ?_⟩
  rw [eval, hE]
  simp only [memLoadByte, hd, if_true]
  congr 1
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]

/-! ## One step of the scan -/

/-- The scan's locals after a step to `st`. -/
def ScanQ (s0 : PancakeState σ) (F : (Word → Word) → Prop) (base : List (String × Value)) (st : Step) : Assn σ :=
  fun u => ∃ y d s g, RunF s0 (SL y d s g base) F u ∧ Out st y d s g

theorem scanQ_clock {s0 : PancakeState σ} {F : (Word → Word) → Prop} {base : List (String × Value)} {st : Step} :
    Safe.ClockFree (ScanQ s0 F base st) := fun u k ⟨y, d, s, g, h, ho⟩ => ⟨y, d, s, g, runF_clock _ _ _ u k h, ho⟩

theorem scanQ_of {o : Oracle σ} {s0 : PancakeState σ} {F : (Word → Word) → Prop} {base : List (String × Value)}
    {xs : List Syntax.PStmt} {P : Assn σ} {y d s g : Nat} {st : Step} (h : Frag o xs P (RunF s0 (SL y d s g base) F))
    (ho : Out st y d s g) : Frag o xs P (ScanQ s0 F base st) :=
  frag_conseq h (fun _ h => h) fun _ h => ⟨y, d, s, g, h, ho⟩

/-- **One byte of the scan** (`scanByte`): the locals go where the model's step goes. -/
theorem scanByte_frag (o : Oracle σ) {ofs : Nat} {A : Word} {s0 : PancakeState σ} (hA : Area ofs A s0)
    {bytes : List (BitVec 8)} (hlen : bytes.length ≤ inputMax) {F : (Word → Word) → Prop}
    (hin : ∀ m, F m → InputAt m s0.memaddrs s0.be A bytes) {base : List (String × Value)}
    (ha : base.lookup "a" = some A) (hnn : base.lookup "nn" = some (BitVec.ofNat 64 bytes.length))
    (hfr : ∀ y ∈ ["go", "sm", "dep", "y"], Fresh y base = true) {Y D Sm B : Nat}
    (hbl : base.lookup "b" = some (BitVec.ofNat 64 B)) (hBs : (inputOf bytes)[Y]? = some B) (hD : 1 ≤ D)
    (hDY : D ≤ Y) (hs : Sm ≤ 3) :
    Frag o [scanByte .none] (RunF s0 (SL Y D Sm 1 base) F) (ScanQ s0 F base (step (inputOf bytes) Y D Sm)) := by
  have hI := inputMax_eq
  have hY : Y < bytes.length := by have := lt_of_some hBs; rwa [inputOf_size] at this
  have hB8 : B < 256 := inputOf_byte hBs
  have f1 := hfr "go" (by simp)
  have f2 := hfr "sm" (by simp)
  have f3 := hfr "dep" (by simp)
  have f4 := hfr "y" (by simp)
  have lk : ∀ {y d s g : Nat} {u : PancakeState σ}, RunF s0 (SL y d s g base) F u →
      u.locals "y" = some (BitVec.ofNat 64 y) ∧ u.locals "dep" = some (BitVec.ofNat 64 d) ∧
      u.locals "sm" = some (BitVec.ofNat 64 s) ∧ u.locals "b" = some (BitVec.ofNat 64 B) ∧ u.locals "a" = some A ∧
      u.locals "nn" = some (BitVec.ofNat 64 bytes.length) := fun h =>
    ⟨vals_lookup h.1.vals rfl, vals_lookup h.1.vals rfl, vals_lookup h.1.vals rfl,
     vals_lookup h.1.vals ((sl_lookup (by decide) (by decide) (by decide) (by decide)).trans hbl),
     vals_lookup h.1.vals ((sl_lookup (by decide) (by decide) (by decide) (by decide)).trans ha),
     vals_lookup h.1.vals ((sl_lookup (by decide) (by decide) (by decide) (by decide)).trans hnn)⟩
  -- the byte after `Y`, past the input a byte of the area
  have nb : ∀ {d s g : Nat} {u : PancakeState σ}, RunF s0 (SL Y d s g base) F u →
      ∃ B1, B1 < 256 ∧ eval u (.loadByte (.op .add (.op .add (.op .add (.var "a")
        (.const (BitVec.ofNat 64 aInput))) (.var "y")) (.const (BitVec.ofNat 64 1)))) = some (BitVec.ofNat 64 B1) ∧
        (Y + 1 < bytes.length → B1 = (bytes[Y + 1]!).toNat) := by
    intro d s g u h
    have hE : eval u (.op .add (.op .add (.op .add (.var "a") (.const (BitVec.ofNat 64 aInput))) (.var "y"))
        (.const (BitVec.ofNat 64 1))) = some (at_ A (aInput + (Y + 1))) := by
      simp only [eval, (lk h).2.2.2.2.1, (lk h).1]
      rw [show aInput + (Y + 1) = aInput + Y + 1 by omega, ← at_add, ← at_add]; rfl
    rcases Nat.lt_or_ge (Y + 1) bytes.length with h1 | h1
    · exact ⟨_, (bytes[Y + 1]!).isLt, inputAt_eval (by rw [h.1.memaddrs, h.1.be]; exact hin _ h.2) h1 hE,
        fun _ => rfl⟩
    · obtain ⟨B1, h8, he⟩ := byte_any hA h.1.memaddrs (x := aInput + (Y + 1))
        (by have := input_le; have := io_le; have := pow_lt; omega) hE
      exact ⟨B1, h8, he, fun h' => absurd h' (by omega)⟩
  have hQ := scanQ_clock (s0 := s0) (F := F) (base := base) (st := step (inputOf bytes) Y D Sm)
  simp only [scanByte, wspAt, inClass_wsp, inClass_ctext, inClass_vchar]
  refine ScanRun.frag_if o rfl (lowK_any _ (k := .skip) rfl) (lowK_any _ (k := .skip) rfl) rfl rfl hQ
    (b := decide (Sm = 2)) (fun u h => FramerCode.eval_eq (by omega) (by decide) (ev_var (lk h).2.2.1) rfl) ?_ ?_
  · -- just past a fold: white space must follow
    intro h2
    have h2 : Sm = 2 := of_decide_eq_true h2
    refine ScanRun.frag_if o rfl (lowK_any _ (k := .skip) rfl) (lowK_any _ (k := .skip) rfl) rfl rfl hQ
      (b := isWsp B) (fun u h => wsp_eval (b := Syntax.v "b") rfl hB8 (ev_var (lk h).2.2.2.1) rfl) ?_ ?_
    · intro hw
      refine scanQ_of (frag_append (xs := [_]) (sl_sm o f2 rfl (s' := 3) fun _ _ => rfl)
        (sl_y o f4 rfl (y' := Y + 1) fun u h => ev_inc (lk h).1)) ?_
      simp [Out, step, hBs, h2, hw]
    · intro hw
      refine scanQ_of (sl_go o f1 rfl (g' := 0) fun _ _ => rfl) ?_
      simp [Out, step, hBs, h2, hw]
  intro h2
  have h2 : Sm ≠ 2 := of_decide_eq_false h2
  refine ScanRun.frag_if o rfl (lowK_any _ (k := .skip) rfl) (lowK_any _ (k := .skip) rfl) rfl rfl hQ
    (b := isWsp B) (fun u h => wsp_eval (b := Syntax.v "b") rfl hB8 (ev_var (lk h).2.2.2.1) rfl) ?_ ?_
  · -- white space
    intro hw
    refine frag_append (xs := [_]) (ScanRun.frag_if o rfl (lowK_any _ (k := .skip) rfl) (lowK_any _ (k := .skip) rfl)
      rfl rfl (runF_clock _ _ _) (Q := RunF s0 (SL Y D (if Sm = 0 then 1 else Sm) 1 base) F) (b := decide (Sm = 0))
      (fun u h => FramerCode.eval_eq (by omega) (by decide) (ev_var (lk h).2.2.1) rfl)
      (fun h0 => by rw [if_pos (of_decide_eq_true h0)]; exact sl_sm o f2 rfl fun _ _ => rfl)
      (fun h0 => frag_nil o fun u h => by rw [if_neg (of_decide_eq_false h0)]; exact h)) ?_
    refine scanQ_of (sl_y o f4 rfl (y' := Y + 1) fun u h => ev_inc (lk h).1) ?_
    simp [Out, step, hBs, h2, hw]
  intro hw
  refine ScanRun.frag_if o rfl (lowK_any _ (k := .skip) rfl) (lowK_any _ (k := .skip) rfl) rfl rfl hQ
    (b := decide (B = 13)) (fun u h => FramerCode.eval_eq (by omega) (by decide) (ev_var (lk h).2.2.2.1) rfl) ?_ ?_
  · -- a fold: CRLF, not twice
    intro h13
    have h13 : B = 13 := of_decide_eq_true h13
    subst h13
    refine ScanRun.frag_if o rfl (lowK_any _ (k := .skip) rfl) (lowK_any _ (k := .skip) rfl) rfl rfl hQ
      (b := decide (Sm = 3) && true)
      (fun u h => FramerCode.eval_and (FramerCode.eval_eq (by omega) (by decide) (ev_var (lk h).2.2.1) rfl) rfl) ?_ ?_
    · intro h3
      have h3 : Sm = 3 := by simpa using h3
      refine scanQ_of (sl_go o f1 rfl (g' := 0) fun _ _ => rfl) ?_
      simp [Out, step, hBs, h3, hw]
    intro h3
    have h3 : Sm ≠ 3 := by simpa using h3
    refine ScanRun.frag_if o rfl (lowK_any _ (k := .skip) rfl) (lowK_any _ (k := .skip) rfl) rfl rfl hQ
      (b := decide (Y + 1 < bytes.length) && decide ((bytes[Y + 1]!).toNat = 10)) (fun u h => by
        obtain ⟨B1, h8, hNB, hb1⟩ := nb h
        refine (FramerCode.eval_and (FramerCode.eval_lt (x := Y + 1) (y := bytes.length) (by omega) (by omega)
          (ev_inc (lk h).1) (ev_var (lk h).2.2.2.2.2)) (FramerCode.eval_eq (x := B1) (y := 10) (by omega)
          (by decide) hNB rfl)).trans ?_
        rcases Nat.lt_or_ge (Y + 1) bytes.length with h1 | h1
        · rw [hb1 h1]
        · simp [Nat.not_lt.2 h1]) ?_ ?_
    · intro hn
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hn
      have hn' : (inputOf bytes)[Y + 1]? = some 10 := by rw [inputOf_lt hn.1, hn.2]
      refine scanQ_of (frag_append (xs := [_]) (sl_sm o f2 rfl (s' := 2) fun _ _ => rfl)
        (sl_y o f4 rfl (y' := Y + 2) fun u h => ev_inc (lk h).1)) ?_
      simp [Out, step, hBs, h2, h3, hw, hn']
    · intro hn
      have hn' : (inputOf bytes)[Y + 1]? ≠ some 10 := by
        rcases Nat.lt_or_ge (Y + 1) bytes.length with h1 | h1
        · rw [inputOf_lt h1]; simpa [h1] using hn
        · rw [inputOf_ge h1]; simp
      refine scanQ_of (sl_go o f1 rfl (g' := 0) fun _ _ => rfl) ?_
      simp [Out, step, hBs, h2, h3, hw, hn']
  intro h13
  have h13 : B ≠ 13 := of_decide_eq_false h13
  refine ScanRun.frag_if o rfl (lowK_any _ (k := .skip) rfl) (lowK_any _ (k := .skip) rfl) rfl rfl hQ
    (b := isCtext B || (decide (B = 92) && false))
    (fun u h => FramerCode.eval_or2 (ctext_eval (b := Syntax.v "b") rfl hB8 (ev_var (lk h).2.2.2.1) rfl)
      (FramerCode.eval_and (FramerCode.eval_eq (by omega) (by decide) (ev_var (lk h).2.2.2.1) rfl) rfl)) ?_ ?_
  · -- text
    intro hc
    have hc : isCtext B = true := by simpa using hc
    refine scanQ_of (frag_append (xs := [_]) (sl_sm o f2 rfl (s' := 0) fun _ _ => rfl)
      (sl_y o f4 rfl (y' := Y + 1) fun u h => ev_inc (lk h).1)) ?_
    simp [Out, step, hBs, h2, hw, h13, hc]
  intro hc
  have hc : isCtext B = false := by simpa using hc
  refine ScanRun.frag_if o rfl (lowK_any _ (k := .skip) rfl) (lowK_any _ (k := .skip) rfl) rfl rfl hQ
    (b := decide (B = 92)) (fun u h => FramerCode.eval_eq (by omega) (by decide) (ev_var (lk h).2.2.2.1) rfl) ?_ ?_
  · -- a quoted pair
    intro h92
    have h92 : B = 92 := of_decide_eq_true h92
    subst h92
    refine ScanRun.frag_if o rfl (lowK_any _ (k := .skip) rfl) (lowK_any _ (k := .skip) rfl) rfl rfl hQ
      (b := decide (Y + 1 < bytes.length) && (isVchar (bytes[Y + 1]!).toNat || isWsp (bytes[Y + 1]!).toNat))
      (fun u h => by
        obtain ⟨B1, h8, hNB, hb1⟩ := nb h
        refine (FramerCode.eval_and (FramerCode.eval_lt (x := Y + 1) (y := bytes.length) (by omega) (by omega)
          (ev_inc (lk h).1) (ev_var (lk h).2.2.2.2.2)) (FramerCode.eval_or2 (vchar_eval (b := nextByte) rfl h8 hNB rfl)
          (wsp_eval (b := nextByte) rfl h8 hNB rfl))).trans ?_
        rcases Nat.lt_or_ge (Y + 1) bytes.length with h1 | h1
        · rw [hb1 h1]
        · simp [Nat.not_lt.2 h1]) ?_ ?_
    · intro hn
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hn
      have hb1 := inputOf_lt hn.1
      generalize (bytes[Y + 1]!).toNat = c at hb1 hn
      refine scanQ_of (frag_append (xs := [_]) (sl_sm o f2 rfl (s' := 0) fun _ _ => rfl)
        (sl_y o f4 rfl (y' := Y + 2) fun u h => ev_inc (lk h).1)) ?_
      simp [Out, step, hBs, h2, hw, h13, hc, hb1, hn.2]
    · intro hn
      refine scanQ_of (sl_go o f1 rfl (g' := 0) fun _ _ => rfl) ?_
      rcases Nat.lt_or_ge (Y + 1) bytes.length with h1 | h1
      · have hb1 := inputOf_lt h1
        simp only [h1, decide_true, Bool.true_and, Bool.or_eq_false_iff] at hn
        generalize (bytes[Y + 1]!).toNat = c at hb1 hn
        simp [Out, step, hBs, h2, hw, h13, hc, hb1, hn.1, hn.2]
      · simp [Out, step, hBs, h2, hw, h13, hc, inputOf_ge h1]
  intro h92
  have h92 : B ≠ 92 := of_decide_eq_false h92
  refine ScanRun.frag_if o rfl (lowK_any _ (k := .skip) rfl) (lowK_any _ (k := .skip) rfl) rfl rfl hQ
    (b := decide (B = 40)) (fun u h => FramerCode.eval_eq (by omega) (by decide) (ev_var (lk h).2.2.2.1) rfl) ?_ ?_
  · -- a comment opens
    intro h40
    have h40 : B = 40 := of_decide_eq_true h40
    subst h40
    refine scanQ_of (frag_append (xs := [_]) (sl_dep o f3 rfl (d' := D + 1) fun u h => ev_inc (lk h).2.1)
      (frag_append (xs := [_]) (sl_sm o f2 rfl (s' := 0) fun _ _ => rfl)
        (sl_y o f4 rfl (y' := Y + 1) fun u h => ev_inc (lk h).1))) ?_
    simp [Out, step, hBs, h2, hw, h13, hc, h92]
  intro h40
  have h40 : B ≠ 40 := of_decide_eq_false h40
  refine ScanRun.frag_if o rfl (lowK_any _ (k := .skip) rfl) (lowK_any _ (k := .skip) rfl) rfl rfl hQ
    (b := decide (B = 41)) (fun u h => FramerCode.eval_eq (by omega) (by decide) (ev_var (lk h).2.2.2.1) rfl) ?_ ?_
  · -- a comment closes, the last one or not
    intro h41
    have h41 : B = 41 := of_decide_eq_true h41
    subst h41
    refine frag_append (xs := [_]) (sl_dep o f3 rfl (d' := D - 1) fun u h => by
      simp only [eval, (lk h).2.1]; rw [ofNat_sub_one hD (by omega)]) ?_
    refine frag_append (xs := [_]) (sl_sm o f2 rfl (s' := 0) fun _ _ => rfl) ?_
    refine frag_append (xs := [_]) (sl_y o f4 rfl (y' := Y + 1) fun u h => ev_inc (lk h).1) ?_
    refine ScanRun.frag_if o rfl (lowK_any _ (k := .skip) rfl) (lowK_any _ (k := .skip) rfl) rfl rfl hQ
      (b := decide (D - 1 = 0)) (fun u h => FramerCode.eval_eq (by omega) (by decide) (ev_var (lk h).2.1) rfl) ?_ ?_
    · intro h1
      have h1 : D = 1 := by have := of_decide_eq_true h1; omega
      refine scanQ_of (sl_go o f1 rfl (g' := 2) fun _ _ => rfl) ?_
      simp [Out, step, hBs, h2, hw, h13, hc, h92, h40, h1]
    · intro h1
      have h1 : D ≠ 1 := by have := of_decide_eq_false h1; omega
      refine scanQ_of (frag_nil o fun _ h => h) ?_
      simp [Out, step, hBs, h2, hw, h13, hc, h92, h40, h1]
  intro h41
  have h41 : B ≠ 41 := of_decide_eq_false h41
  refine scanQ_of (sl_go o f1 rfl (g' := 0) fun _ _ => rfl) ?_
  simp [Out, step, hBs, h2, hw, h13, hc, h92, h40, h41]

theorem sl_fresh {y d s g : Nat} {base : List (String × Value)} {z : String} (h1 : "go" ≠ z) (h2 : "sm" ≠ z)
    (h3 : "dep" ≠ z) (h4 : "y" ≠ z) (h : Fresh z base = true) : Fresh z (SL y d s g base) = true :=
  ScanRun.fresh_cons h1 (ScanRun.fresh_cons h2 (ScanRun.fresh_cons h3 (ScanRun.fresh_cons h4 h)))

theorem lowKK_scanByte : LowKK [scanByte .none] := by
  simp only [scanByte, wspAt, inClass_wsp, inClass_ctext, inClass_vchar]
  exact lowK_any _ (k := .skip) rfl

theorem lowKK_scanStep : LowKK (scanStep .none) :=
  lowKK_ite rfl (lowKK_append (xs := [_]) (lowKK_dec rfl) lowKK_scanByte) (lowK_any _ (k := .skip) rfl)

theorem sl_mem {y d s g : Nat} {base : List (String × Value)} {p q : String × Value} (h : q ∈ SL y d s g base) :
    q ∈ SL y d s g (p :: base) := by
  simp only [SL, List.mem_cons] at h ⊢
  rcases h with h | h | h | h | h
  · exact .inl h
  · exact .inr (.inl h)
  · exact .inr (.inr (.inl h))
  · exact .inr (.inr (.inr (.inl h)))
  · exact .inr (.inr (.inr (.inr (.inr h))))

theorem sl_swap {y d s g : Nat} {base : List (String × Value)} {p q : String × Value} (h : q ∈ SL y d s g (p :: base)) :
    q ∈ p :: SL y d s g base := by
  simp only [SL, List.mem_cons] at h ⊢
  rcases h with h | h | h | h | h | h
  · exact .inr (.inl h)
  · exact .inr (.inr (.inl h))
  · exact .inr (.inr (.inr (.inl h)))
  · exact .inr (.inr (.inr (.inr (.inl h))))
  · exact .inl h
  · exact .inr (.inr (.inr (.inr (.inr h))))

/-- **One step of the scan** (`scanStep`): the byte at `y` read, or the input's end a failure. -/
theorem scanStep_frag (o : Oracle σ) {ofs : Nat} {A : Word} {s0 : PancakeState σ} (hA : Area ofs A s0)
    {bytes : List (BitVec 8)} (hlen : bytes.length ≤ inputMax) {F : (Word → Word) → Prop}
    (hin : ∀ m, F m → InputAt m s0.memaddrs s0.be A bytes) {base : List (String × Value)}
    (ha : base.lookup "a" = some A) (hnn : base.lookup "nn" = some (BitVec.ofNat 64 bytes.length))
    (hfr : ∀ y ∈ ["go", "sm", "dep", "y", "b"], Fresh y base = true) {Y D Sm : Nat} (hD : 1 ≤ D) (hDY : D ≤ Y)
    (hs : Sm ≤ 3) (hY : Y ≤ bytes.length) :
    Frag o (scanStep .none) (RunF s0 (SL Y D Sm 1 base) F) (ScanQ s0 F base (step (inputOf bytes) Y D Sm)) := by
  have hI := inputMax_eq
  have hfb := hfr "b" (by simp)
  have ly : ∀ {u : PancakeState σ}, RunF s0 (SL Y D Sm 1 base) F u → u.locals "y" = some (BitVec.ofNat 64 Y) :=
    fun h => vals_lookup h.1.vals rfl
  have la : ∀ {u : PancakeState σ}, RunF s0 (SL Y D Sm 1 base) F u → u.locals "a" = some A :=
    fun h => vals_lookup h.1.vals ((sl_lookup (by decide) (by decide) (by decide) (by decide)).trans ha)
  have lnn : ∀ {u : PancakeState σ}, RunF s0 (SL Y D Sm 1 base) F u →
      u.locals "nn" = some (BitVec.ofNat 64 bytes.length) :=
    fun h => vals_lookup h.1.vals ((sl_lookup (by decide) (by decide) (by decide) (by decide)).trans hnn)
  have hc : ∀ {u : PancakeState σ}, RunF s0 (SL Y D Sm 1 base) F u →
      eval u (.cmp .less (.var "y") (.var "nn")) = some (bw (decide (Y < bytes.length))) := fun h =>
    FramerCode.eval_lt (by omega) (by omega) (ev_var (ly h)) (ev_var (lnn h))
  have lowT : LowKK [.dec "b" (byte (Syntax.eAdd (Syntax.atOff (Syntax.v "a") aInput) (Syntax.v "y"))),
      scanByte .none] := lowKK_append (xs := [_]) (lowKK_dec rfl) lowKK_scanByte
  unfold scanStep
  refine frag_ite o rfl scanQ_clock (fun u h => ⟨_, hc h⟩) ?_ (fun u z v ⟨y, d, s, g, h, ho⟩ hz => ?_) ?_
    (noDecl _ rfl)
  rotate_left
  · rw [show declared [Syntax.PStmt.dec "b" (byte (Syntax.eAdd (Syntax.atOff (Syntax.v "a") aInput) (Syntax.v "y"))),
      scanByte .none] = ["b"] from rfl, List.mem_singleton] at hz
    subst hz
    exact ⟨y, d, s, g, runF_restore h (sl_fresh (by decide) (by decide) (by decide) (by decide) hfb) v, ho⟩
  · -- the input's end
    by_cases hYn : Y < bytes.length
    · exact frag_unsat (lowK_any _ (k := .skip) rfl) fun u ⟨h, h0⟩ => by
        rw [hc h, decide_eq_true hYn] at h0; cases h0
    have hst : step (inputOf bytes) Y D Sm = .fail := by simp [AbnfMatch.step, inputOf_ge (Nat.not_lt.1 hYn)]
    exact frag_conseq (scanQ_of (sl_go o (hfr "go" (by simp)) rfl (g' := 0) fun _ _ => rfl) (by rw [hst]; rfl))
      (fun u h => h.1) fun _ h => h
  -- the byte at `Y`
  by_cases hYn : ¬Y < bytes.length
  · exact frag_unsat lowT fun u ⟨h, h0⟩ => h0 (by rw [hc h, decide_eq_false hYn]; rfl)
  have hYn : Y < bytes.length := Classical.not_not.1 hYn
  refine frag_conseq (P0 := RunF s0 (SL Y D Sm 1 base) F) (frag_append (xs := [_])
    (runF_dec o rfl (sl_fresh (by decide) (by decide) (by decide) (by decide) hfb)
      (v := BitVec.ofNat 64 (bytes[Y]!).toNat) fun u h => inputAt_eval (by rw [h.1.memaddrs, h.1.be]; exact hin _ h.2)
        hYn (by simp only [eval, la h, ly h]; rw [← at_add]; rfl)) ?_) (fun u h => h.1) fun _ h => h
  refine frag_conseq (scanByte_frag o hA hlen hin (base := ("b", BitVec.ofNat 64 (bytes[Y]!).toNat) :: base)
    ((ScanRun.lookup_cons_ne (by decide) _ _).trans ha) ((ScanRun.lookup_cons_ne (by decide) _ _).trans hnn)
    (fun z hz => ScanRun.fresh_cons (by simp at hz; rcases hz with rfl | rfl | rfl | rfl <;> decide)
      (hfr z (by simp at hz ⊢; rcases hz with rfl | rfl | rfl | rfl <;> simp)))
    (lookup_head _ _ _) (inputOf_lt hYn) hD hDY hs) (fun u h => runF_mono h (fun q hq => sl_swap hq) fun _ e => e)
    fun u ⟨y, d, s, g, h, ho⟩ => ⟨y, d, s, g, runF_mono h (fun q hq => sl_mem hq) fun _ e => e, ho⟩

/-! ## A comment's end -/

/-- What the scan's locals tell of the comment opening at `x`. Going on, its ends are the scan's from them; cleared, it
has none; 2, it closes at `y`. -/
def Inv (input : Array Nat) (x y d s g : Nat) : Prop :=
  (g = 1 ∧ 1 ≤ d ∧ d ≤ y ∧ s ≤ 3 ∧ y ≤ input.size ∧ ∀ e, Runs input (x + 1) 1 0 e ↔ Runs input y d s e) ∨
    (g = 0 ∧ ∀ e, ¬Runs input (x + 1) 1 0 e) ∨ (g = 2 ∧ Runs input (x + 1) 1 0 y)

theorem inv_step {input : Array Nat} {x y d s y' d' s' g' : Nat} (hd : 1 ≤ d) (hdy : d ≤ y) (hs : s ≤ 3)
    (hR : ∀ e, Runs input (x + 1) 1 0 e ↔ Runs input y d s e) (ho : Out (step input y d s) y' d' s' g') :
    Inv input x y' d' s' g' := by
  generalize hst : step input y d s = st at ho
  cases st with
  | go y1 d1 s1 =>
    obtain ⟨rfl, rfl, rfl, rfl⟩ := ho
    obtain ⟨b1, b2, b3, b4⟩ := step_bounds hst hd hdy hs
    exact .inl ⟨rfl, b1, b2, b3, b4, fun e => (hR e).trans (runs_go hst)⟩
  | fail => exact .inr (.inl ⟨ho, fun e h => runs_fail hst ((hR e).1 h)⟩)
  | done e' =>
    obtain ⟨rfl, rfl⟩ := ho
    exact .inr (.inr ⟨rfl, (hR _).2 ((runs_done hst).2 rfl)⟩)

/-- Where the comment that opens at `x` closes, if it does. -/
noncomputable def commentEnd (input : Array Nat) (x : Nat) : Option Nat := by
  classical exact if h : input[x]? = some 40 ∧ ∃ e, Runs input (x + 1) 1 0 e then some h.2.choose else none

theorem commentEnd_iff {input : Array Nat} {x e : Nat} :
    commentEnd input x = some e ↔ input[x]? = some 40 ∧ Runs input (x + 1) 1 0 e := by
  unfold commentEnd
  split
  · rename_i h
    constructor
    · intro he; cases he; exact ⟨h.1, h.2.choose_spec⟩
    · rintro ⟨-, hr⟩; rw [AbnfMatch.runs_det h.2.choose_spec hr]
  · rename_i h
    constructor
    · intro he; cases he
    · rintro ⟨h40, hr⟩; exact absurd ⟨h40, e, hr⟩ h

/-- What `ruleComment` adds at `x`: where the comment that opens at `x` closes. -/
noncomputable def commentAdd (S : Nat → Bool) (bytes : List (BitVec 8)) (x : Nat) : Option Nat :=
  if S x && decide (x < bytes.length) then commentEnd (inputOf bytes) x else none

theorem commentAdd_none {S : Nat → Bool} {bytes : List (BitVec 8)} {x : Nat} (h : S x = false ∨ bytes.length ≤ x) :
    commentAdd S bytes x = none := by
  unfold commentAdd
  rcases h with h | h
  · simp [h]
  · simp [Nat.not_lt.2 h]

theorem commentAdd_small {S : Nat → Bool} {bytes : List (BitVec 8)} {x e : Nat} (h : commentAdd S bytes x = some e) :
    e ≤ bytes.length := by
  unfold commentAdd at h
  split at h
  · have := runs_le (commentEnd_iff.1 h).2; rwa [inputOf_size] at this
  · cases h

/-- **A position of a comment** (`commentBody`): where the comment that opens at `x` closes, added. -/
theorem commentBody_frag (o : Oracle σ) {ofs : Nat} {A : Word} {s0 : PancakeState σ} (hA : Area ofs A s0)
    {kd : Nat} (hkd : kd < slots) {S : Nat → Bool} {bytes : List (BitVec 8)} (hlen : bytes.length ≤ inputMax)
    {m1 : Word → Word} (hr : Reads s0 A bytes m1) {L0 : List (String × Value)}
    (ha : L0.lookup "a" = some A) (hq : L0.lookup "q" = some (at_ A (off kd)))
    (hnn : L0.lookup "nn" = some (BitVec.ofNat 64 bytes.length))
    (hfr : ∀ y ∈ ["go", "sm", "dep", "y", "b", "yw", "yj", "df", "dh", "dl"], Fresh y L0 = true)
    (X : Nat) (lv : List (String × Value)) (hlv : ∀ q ∈ lv, q.1 ∈ loopNames) (hS : S X = true)
    (hX : X < bytes.length) :
    Frag o (commentBody .none)
      (RunF s0 (("x", BitVec.ofNat 64 X) :: lv ++ (winL (commentAdd S bytes) X ++ L0))
        (Built A kd (commentAdd S bytes) X m1))
      (RunF s0 (("x", BitVec.ofNat 64 X) :: lv ++ (winL (commentAdd S bytes) (X + 1) ++ L0))
        (Built A kd (commentAdd S bytes) (X + 1) m1)) := by
  have hI := inputMax_eq
  let add := commentAdd S bytes
  let input := inputOf bytes
  let F := Built A kd add X m1
  let base : List (String × Value) := ("x", BitVec.ofNat 64 X) :: lv ++ (winL add X ++ L0)
  have hnl : ∀ y, y ∉ loopNames → Fresh y lv = true := fun y hy => fresh_loop hlv hy
  have hin : ∀ m, F m → InputAt m s0.memaddrs s0.be A bytes := fun m hb =>
    (reads_built hkd hA.hA hlen hr hb.rest).input
  have lkY : ∀ Y y v, y ≠ "x" → y ∉ loopNames → y ≠ "df" → y ≠ "dh" → y ≠ "dl" → L0.lookup y = some v →
      (("x", BitVec.ofNat 64 X) :: lv ++ (winL add Y ++ L0)).lookup y = some v := by
    intro Y y v h1 h2 h3 h4 h5 h
    rw [List.cons_append, ScanRun.lookup_cons_ne h1, lookup_app_fresh _ (hnl y h2),
      lookup_app_fresh _ (winL_fresh h3 h4 h5), h]
  have frY : ∀ Y y, y ∈ ["go", "sm", "dep", "y", "b", "yw", "yj"] →
      Fresh y (("x", BitVec.ofNat 64 X) :: lv ++ (winL add Y ++ L0)) = true := fun Y y hy => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    have h0 : y ∉ loopNames := by rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [loopNames]
    exact ScanRun.fresh_cons (fun e => h0 (e ▸ by simp [loopNames])) (fresh_app (hnl y h0)
      (fresh_app (winL_fresh (by rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
        (by rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
        (by rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide))
        (hfr y (by rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp))))
  have hx0 : base.lookup "x" = some (BitVec.ofNat 64 X) := by
    show (("x", BitVec.ofNat 64 X) :: lv ++ (winL add X ++ L0)).lookup "x" = _
    rw [List.cons_append, lookup_head]
  have ha' : base.lookup "a" = some A :=
    lkY X "a" A (by decide) (by simp [loopNames]) (by decide) (by decide) (by decide) ha
  have hnn' : base.lookup "nn" = some (BitVec.ofNat 64 bytes.length) :=
    lkY X "nn" _ (by decide) (by simp [loopNames]) (by decide) (by decide) (by decide) hnn
  have hfr' : ∀ y ∈ ["go", "sm", "dep", "y", "b"], Fresh y base = true := fun y hy =>
    frY X y (by simp at hy ⊢; rcases hy with rfl | rfl | rfl | rfl | rfl <;> simp)
  have hc : ∀ u, RunF s0 base F u → eval u (.cmp .equal (.loadByte (.op .add (.op .add (.var "a")
      (.const (BitVec.ofNat 64 aInput))) (.var "x"))) (.const (BitVec.ofNat 64 40))) =
      some (bw (decide ((bytes[X]!).toNat = 40))) := fun u h =>
    FramerCode.eval_eq (by have := (bytes[X]!).isLt; omega) (by decide)
      (inputByte_eval (by rw [h.1.memaddrs, h.1.be]; exact hin _ h.2) (vals_lookup h.1.vals ha') hX
        (vals_lookup h.1.vals hx0)) rfl
  have lgo : ∀ {y d s g : Nat} {u : PancakeState σ}, RunF s0 (SL y d s g base) F u →
      u.locals "go" = some (BitVec.ofNat 64 g) := fun h => vals_lookup h.1.vals rfl
  have hg : ∀ {y d s g c : Nat} {u : PancakeState σ}, RunF s0 (SL y d s g base) F u → Inv input X y d s g → c < 3 →
      eval u (.cmp .equal (.var "go") (.const (BitVec.ofNat 64 c))) = some (bw (decide (g = c))) := fun h hv hc =>
    FramerCode.eval_eq (by rcases hv with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> decide) (by omega) (ev_var (lgo h)) rfl
  have lowF : LowKK [.ite (Syntax.eEq (Syntax.v "go") (Syntax.n 2)) (addBit .none (Syntax.v "y")) []] :=
    lowKK_ite rfl (lowKK_addBit rfl) (lowK_any _ (k := .skip) rfl)
  have rY : ∀ u z v, RunF s0 (("x", BitVec.ofNat 64 X) :: lv ++ (winL add (X + 1) ++ L0)) (Built A kd add (X + 1) m1)
      u → z ∈ ["yw", "yj"] → RunF s0 (("x", BitVec.ofNat 64 X) :: lv ++ (winL add (X + 1) ++ L0))
        (Built A kd add (X + 1) m1) (restore u z v) := fun u z v h hz =>
    runF_restore h (frY (X + 1) z (by simp at hz ⊢; rcases hz with rfl | rfl <;> simp)) v
  unfold commentBody
  refine frag_ite o rfl (runF_clock _ _ _) (fun u h => ⟨_, hc u h⟩) ?_ (fun u z v h hz => ?_) ?_ (noDecl _ rfl)
  rotate_left
  · change z ∈ ["y", "dep", "sm", "go"] at hz
    exact runF_restore h (frY (X + 1) z (by simp at hz ⊢; rcases hz with rfl | rfl | rfl | rfl <;> simp)) v
  · -- no `(` at `X`
    refine frag_nil o fun u ⟨h, h0⟩ => ?_
    have h40 : (bytes[X]!).toNat ≠ 40 := fun e => by
      rw [hc u h, e] at h0; exact absurd h0 (by decide)
    have hadd : add X = none := by
      show commentAdd S bytes X = none
      unfold commentAdd
      rw [if_pos (by simp [hS, hX])]
      exact Option.eq_none_iff_forall_ne_some.2 fun e he => h40 (by
        have := (commentEnd_iff.1 he).1; rw [inputOf_lt hX] at this; exact Option.some.inj this)
    show RunF s0 (("x", BitVec.ofNat 64 X) :: lv ++ (winL add (X + 1) ++ L0)) (Built A kd add (X + 1) m1) u
    rw [winL_skip hadd]
    exact ⟨h.1, built_skip h.2 hadd⟩
  by_cases h40 : ¬(bytes[X]!).toNat = 40
  · exact frag_unsat (lowKK_append (xs := [_, _, _, _]) (lowK_any _ (k := .skip) rfl)
      (lowKK_append (xs := [_]) (lowKK_while rfl lowKK_scanStep) lowF))
      fun u ⟨h, h0⟩ => h0 (by rw [hc u h, decide_eq_false h40]; rfl)
  have h40 : (bytes[X]!).toNat = 40 := Classical.not_not.1 h40
  have hin40 : input[X]? = some 40 := by rw [inputOf_lt hX, h40]
  have hS' : (S X && decide (X < bytes.length)) = true := by simp [hS, hX]
  refine frag_conseq (P0 := RunF s0 base F) ?_ (fun u h => h.1) fun _ h => h
  refine frag_append (xs := [_]) (runF_dec o rfl (frY X "y" (by simp)) (v := BitVec.ofNat 64 (X + 1)) fun u h =>
    ev_inc (vals_lookup h.1.vals hx0)) ?_
  refine frag_append (xs := [_]) (runF_dec o rfl (ScanRun.fresh_cons (by decide) (frY X "dep" (by simp)))
    (v := BitVec.ofNat 64 1) fun _ _ => rfl) ?_
  refine frag_append (xs := [_]) (runF_dec o rfl (ScanRun.fresh_cons (by decide) (ScanRun.fresh_cons (by decide)
    (frY X "sm" (by simp)))) (v := BitVec.ofNat 64 0) fun _ _ => rfl) ?_
  refine frag_append (xs := [_]) (runF_dec o rfl (ScanRun.fresh_cons (by decide) (ScanRun.fresh_cons (by decide)
    (ScanRun.fresh_cons (by decide) (frY X "go" (by simp))))) (v := BitVec.ofNat 64 1) fun _ _ => rfl) ?_
  -- the scan
  let I : Assn σ := fun u => ∃ y d s g, RunF s0 (SL y d s g base) F u ∧ Inv input X y d s g
  have hIc : Safe.ClockFree I := fun u k ⟨y, d, s, g, h, hv⟩ => ⟨y, d, s, g, runF_clock _ _ _ u k h, hv⟩
  refine frag_append (xs := [_]) (frag_conseq (frag_while o (c := Syntax.eEq (Syntax.v "go") (Syntax.n 1)) rfl
    lowKK_scanStep hIc (fun u z v _ hz => by change z ∈ [] at hz; cases hz)
    (fun u ⟨y, d, s, g, h, hv⟩ => ⟨_, hg h hv (by decide)⟩) ?step) (fun u h => ⟨X + 1, 1, 0, 1, h,
      .inl ⟨rfl, Nat.le_refl _, by omega, by omega, by rw [inputOf_size]; omega, fun _ => Iff.rfl⟩⟩) fun _ h => h) ?last
  case step =>
    refine frag_conseq (P0 := fun u => ∃ t : Nat × Nat × Nat,
      (fun t u => RunF s0 (SL t.1 t.2.1 t.2.2 1 base) F u ∧ Inv input X t.1 t.2.1 t.2.2 1) t u)
      (frag_exists lowKK_scanStep fun t => ?_) (fun u ⟨⟨y, d, s, g, h, hv⟩, h0⟩ => ?_) fun _ h => h
    · obtain ⟨y, d, s⟩ := t
      by_cases hv : ¬Inv input X y d s 1
      · exact frag_unsat lowKK_scanStep fun u h => hv h.2
      rcases Classical.not_not.1 hv with ⟨-, hd, hdy, hs, hy, hR⟩ | ⟨h0, -⟩ | ⟨h2, -⟩
      · refine frag_conseq (scanStep_frag o hA hlen hin ha' hnn' hfr' hd hdy hs (by rwa [inputOf_size] at hy))
          (fun u h => h.1) fun u ⟨y', d', s', g', h, ho⟩ => ⟨y', d', s', g', h, inv_step hd hdy hs hR ho⟩
      · cases h0
      · cases h2
    · have g1 : g = 1 := Classical.byContradiction fun hne => h0 (by rw [hg h hv (by decide), decide_eq_false hne]; rfl)
      subst g1
      exact ⟨(y, d, s), h, hv⟩
  case last =>
    refine frag_conseq (P0 := fun u => ∃ t : Nat × Nat × Nat × Nat, (fun t u => RunF s0 (SL t.1 t.2.1 t.2.2.1 t.2.2.2
      base) F u ∧ Inv input X t.1 t.2.1 t.2.2.1 t.2.2.2 ∧ t.2.2.2 ≠ 1) t u) (frag_exists lowF fun t => ?_)
      (fun u ⟨⟨y, d, s, g, h, hv⟩, h0⟩ => ⟨(y, d, s, g), h, hv, fun e => by
        subst e; rw [hg h hv (by decide)] at h0; exact absurd h0 (by decide)⟩) fun _ h => h
    obtain ⟨y, d, s, g⟩ := t
    by_cases hv : ¬(Inv input X y d s g ∧ g ≠ 1)
    · exact frag_unsat lowF fun u h => hv h.2
    obtain ⟨hv, hg1⟩ := Classical.not_not.1 hv
    have hv' := hv
    rcases hv with ⟨rfl, -⟩ | ⟨rfl, hR⟩ | ⟨rfl, hR⟩
    · exact absurd rfl hg1
    · -- the comment does not close: nothing added
      have hadd : add X = none := by
        show commentAdd S bytes X = none
        unfold commentAdd; rw [if_pos hS']
        exact Option.eq_none_iff_forall_ne_some.2 fun e he => hR e (commentEnd_iff.1 he).2
      refine frag_ite o rfl (runF_clock _ _ _) (fun u h => ⟨_, hg h.1 hv' (c := 2) (by decide)⟩)
        (frag_unsat (lowKK_addBit rfl) fun u ⟨h, h0⟩ => h0 (by rw [hg h.1 hv' (c := 2) (by decide)]; rfl))
        (fun u z v h hz => rY u z v h (by change z ∈ ["yw", "yj"] at hz; exact hz))
        (frag_nil o fun u ⟨h, _⟩ => ?_) (noDecl _ rfl)
      show RunF s0 (("x", BitVec.ofNat 64 X) :: lv ++ (winL add (X + 1) ++ L0)) (Built A kd add (X + 1) m1) u
      rw [winL_skip hadd]
      exact ⟨(runF_mono h.1 (fun q hq => List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        (List.mem_cons_of_mem _ hq)))) fun _ e => e).1, built_skip h.1.2 hadd⟩
    · -- the comment closes at `y`
      have hadd : add X = some y := by
        show commentAdd S bytes X = some y
        unfold commentAdd; rw [if_pos hS']
        exact commentEnd_iff.2 ⟨hin40, hR⟩
      refine frag_ite o rfl (runF_clock _ _ _) (fun u h => ⟨_, hg h.1 hv' (c := 2) (by decide)⟩) ?_
        (fun u z v h hz => rY u z v h (by change z ∈ ["yw", "yj"] at hz; exact hz))
        (frag_unsat (lowK_any _ (k := .skip) rfl) fun u ⟨h, h0⟩ => by
          rw [hg h.1 hv' (c := 2) (by decide)] at h0; cases h0) (noDecl _ rfl)
      refine frag_conseq (addAt_frag o hA hkd hlen hr (fun x e he => by have := commentAdd_small he; omega) hadd
        (lv := lv) (L0 := L0) (pre := [("go", BitVec.ofNat 64 2), ("sm", BitVec.ofNat 64 s), ("dep", BitVec.ofNat 64 d),
          ("y", BitVec.ofNat 64 y)]) ha hq
        (fun z hz => hfr z (by simp at hz ⊢; rcases hz with rfl | rfl | rfl | rfl | rfl <;> simp)) hlv
        (fun q hq => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
                        rcases hq with rfl | rfl | rfl | rfl <;> simp) (y := Syntax.v "y") rfl
        (fun u h => ev_var (vals_lookup h.1.vals rfl))) (fun u h => h.1.1)
        fun u h => runF_mono h (fun q hq => List.mem_append_right _ hq) fun _ e => e

/-- **`ruleComment` adds where each comment opening at a position of `S` closes** to slot `kd`, emptied first. Every
word outside it is kept. -/
theorem ruleComment_ok (o : Oracle σ) {ofs : Nat} {A : Word} {s1 : PancakeState σ} (hA : Area ofs A s1)
    {ks kd : Nat} (hks : ks < slots) (hkd : kd < slots) (hne : ks ≠ kd)
    (hs : s1.locals "s" = some (BitVec.ofNat 64 ks)) (hd : s1.locals "d" = some (BitVec.ofNat 64 kd))
    {S Sd : Nat → Bool} (hS : SetAt s1.memory A ks S) (hSd : SetAt s1.memory A kd Sd) {bytes : List (BitVec 8)}
    (hlen : bytes.length ≤ inputMax) (hn : s1.memory (at_ A aLen) = BitVec.ofNat 64 bytes.length)
    (hr : Reads s1 A bytes s1.memory) :
    ∃ body, Lower.lower (ruleComment .none ofs) = some body ∧
      SafeR o (fun s => s = s1) body (LeafRet A kd (below (commentAdd S bytes) (64 * setWords)) s1.memory)
        fun _ => False := by
  have hI := inputMax_eq
  refine body_of ?_
  dsimp only [ruleComment]
  let l0 : List (String × Value) := [("s", BitVec.ofNat 64 ks), ("d", BitVec.ofNat 64 kd)]
  have hentry : ∀ s, s = s1 → RunF s1 l0 (· = s1.memory) s := entry_run (fun q hq => by
    simp only [l0, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact hs
    · exact hd) rfl
  have hfr0 : ∀ y ∈ ["df", "dh", "dl"] ++ loopNames, Fresh y (("nn", BitVec.ofNat 64 bytes.length) ::
      ("q", at_ A (off kd)) :: ("p", at_ A (off ks)) :: ("a", A) :: l0) = true := by
    intro y hy; simp [loopNames] at hy
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  refine fragR_conseq (P0 := RunF s1 l0 (· = s1.memory)) (leaf_frag o hA hks hkd hne hS hSd hlen hn hr (l0 := l0)
    rfl rfl (by intro y hy; simp at hy; rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl) (head := [])
    (frag_nil o fun _ h => h) ⟨rfl, rfl, rfl, rfl⟩ hfr0
    (fun x h => commentAdd_none h) (fun x e he => by have := commentAdd_small he; rw [setWords_eq]; omega)
    (lowKK_ite rfl (lowKK_append (xs := [_, _, _, _]) (lowK_any _ (k := .skip) rfl)
      (lowKK_append (xs := [_]) (lowKK_while rfl lowKK_scanStep)
        (lowKK_ite rfl (lowKK_addBit rfl) (lowK_any _ (k := .skip) rfl)))) (lowK_any _ (k := .skip) rfl))
    (fun y hy => by change y ∈ [] at hy; cases hy)
    fun M0 _ hrM X lv hlv hSX hX => commentBody_frag o hA hkd hlen hrM rfl rfl rfl
      (by intro y hy; simp at hy; rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl)
      X lv hlv hSX hX)
    hentry fun _ h => h

/-- **What `ruleComment` adds is where a comment matches.** -/
theorem commentAdd_iff {S : Nat → Bool} {bytes : List (BitVec 8)} {x e : Nat} :
    commentAdd S bytes x = some e ↔ S x = true ∧ Matches AbnfRules.grammar (inputOf bytes) (.ref commentRule) x e := by
  rw [AbnfMatch.comment_eq, AbnfMatch.comment_runs]
  unfold commentAdd
  constructor
  · intro h
    split at h
    · rename_i hc
      simp only [Bool.and_eq_true] at hc
      exact ⟨hc.1, commentEnd_iff.1 h⟩
    · cases h
  · rintro ⟨hS, h40, hr⟩
    have hx : x < bytes.length := by have := lt_of_some h40; rwa [inputOf_size] at this
    rw [if_pos (by simp [hS, hx])]
    exact commentEnd_iff.2 ⟨h40, hr⟩

/-- **Slot `kd` after `ruleComment`** holds where the comments that open at the positions of `S` close. -/
theorem commentSet_iff {S : Nat → Bool} {bytes : List (BitVec 8)} (hlen : bytes.length ≤ inputMax) (e : Nat) :
    below (commentAdd S bytes) (64 * setWords) e = true ↔
      ∃ x, S x = true ∧ Matches AbnfRules.grammar (inputOf bytes) (.ref commentRule) x e :=
  below_matches (fun _ _ => commentAdd_iff) fun x e h => by
    unfold commentAdd at h
    split at h
    · rename_i hc
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
      rw [setWords_eq]; rw [inputMax_eq] at hlen; omega
    · cases h

/-! ## The premises can hold -/

theorem out_witness : Out .fail 0 0 0 0 := rfl

end DN.News.AbnfComment
