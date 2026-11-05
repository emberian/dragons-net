-- SPDX-License-Identifier: AGPL-3.0-or-later
import DN.News.ArticleDate
import DN.News.ArticleGrammar

/-!
# DN.News.ArticleDateRun

`artDate`'s pieces as the program holds them, the failed flag checked after each call. Its loops are proven to follow
the model of `DN.News.ArticleDate`; `DN.News.ArticleDateOk` joins them.
-/

namespace DN.News.ArticleDateRun

open DN.Compiler DN.Compiler.Wp DN.Compiler.WpRet DN.Compiler.Frag DN.News.AbnfProg
open DN.News.AbnfSets DN.News.FunRun DN.News.AbnfLeaves DN.News.ArticleRun DN.News.ArticleScan DN.News.ArticleCal
open DN.News.ScanRun (at_ at_add vals_lookup without Fresh)
open DN.News.FramerCode (bw ev_var bw_ne0 bw_eq0)
open DN.News.AbnfComment (ev_inc)
open DN.News.ArticleProg (artMax guardL guardS ifs readIn wd tokIn isGap isDig lowerE setW)
open DN.News.ArticleLines (seg seg_succ seg_length)
open DN.News.ArticleSpec (Bytes)
open DN.News.ArticleDate (isComma isComma_toNat)
open Syntax (v n eEq eLt eLe eAnd eAdd eSub eMul)

variable {σ : Type}

/-! ## The body -/

/-- A part of the time ended. -/
def finishS : List Syntax.PStmt :=
  [ifs (eEq (v "cd") (n 0)) [.assign "bad" (n 1)],
   .ite (eEq (v "np") (n 0)) [.assign "hh" (v "cv")]
     [.ite (eEq (v "np") (n 1)) [.assign "mi" (v "cv")] [ifs (eEq (v "np") (n 2)) [.assign "se" (v "cv")]]],
   inc "np", .assign "cv" (n 0), .assign "cd" (n 0)]

/-- The next word, the check of the failed flag after the call, and none if it is empty. -/
def toksS (name : String) (p q : Syntax.PExpr) : List Syntax.PStmt :=
  [.call name "artTok" [p, q], brk, ifs (eEq (wd ArticleProg.xTokLen) (n 0)) [.ret (n 0)]]

/-- The loop's body up to the comment's `(`. -/
def parenBody : List Syntax.PStmt :=
  [.ite (eLt (v "c") (v "e")) (readIn "b" "c" ++ [.ite (eEq (v "b") (n 40)) [.assign "go" (n 0)] [inc "c"]])
    [.assign "go" (n 0)]]

/-- The loop's body over the commas before it. -/
def commaBody : List Syntax.PStmt :=
  readIn "b2" "i" ++ [ifs (eEq (v "b2") (n 44)) [ifs (eEq (v "nc") (n 0)) [.assign "cp" (v "i")], inc "nc"], inc "i"]

/-- The zone's checks of the letters of `GMT`. -/
def gmtS : List Syntax.PStmt :=
  ["g", "m", "t"].zipIdx.map (fun (c, k) =>
    ifs (eEq (v "zl") (n k)) [ifs (ne (lowerE (v "b3")) (n c.toList.head!.toNat)) [.assign "zg" (n 0)]])

/-- The zone's list of statements in the loop's body. -/
def zoneBody : List Syntax.PStmt :=
  [ifs (eEq (v "ph") (n 0)) (finishS ++ [.assign "ph" (n 1)]), ifs (eEq (v "zl") (n 0)) [.assign "z0" (v "b3")]] ++
    gmtS ++
    [ifs (eAnd (eLe (n 1) (v "zl")) (eLe (v "zl") (n 4)))
       [.ite (isDig (v "b3")) [.assign "zv" (eAdd (eMul (v "zv") (n 10)) (eSub (v "b3") (n 48)))]
         [.assign "zd" (n 0)]],
     inc "zl"]

/-- The loop's body over the time and the zone. -/
def tzBody : List Syntax.PStmt :=
  readIn "b3" "j" ++
    [ifs (eEq (isGap (v "b3")) (n 0))
      [.ite (eAnd (eEq (v "ph") (n 0)) (or2 (isDig (v "b3")) (eEq (v "b3") (n 58))))
        [.ite (eEq (v "b3") (n 58)) finishS
          [.assign "cv" (eAdd (eMul (v "cv") (n 10)) (eSub (v "b3") (n 48))),
           ifs (eLt (n 1000) (v "cv")) [.assign "cv" (n 1000)], inc "cd"]] zoneBody],
     inc "j"]

/-- The zone's offset: none for `GMT`, else a sign and four digits of hours and minutes below 60. -/
def zoneS : List Syntax.PStmt :=
  [.ite (eAnd (eEq (v "zl") (n 3)) (v "zg")) []
    [ifs (or2 (ne (v "zl") (n 5)) (eEq (v "zd") (n 0))) [.ret (n 0)],
     .call "zh" "artDiv" [v "zv", n 100], brk, .dec "zm" (eSub (v "zv") (eMul (v "zh") (n 100))),
     ifs (eLe (n 60) (v "zm")) [.ret (n 0)],
     .assign "off" (eAdd (eMul (v "zh") (n 3600)) (eMul (v "zm") (n 60))),
     .ite (eEq (v "z0") (n 43)) []
       [.ite (eEq (v "z0") (n 45)) [.assign "off" (eSub (n 0) (v "off"))] [.ret (n 0)]]]]

/-- The days of the month, its year leap or not. -/
def monthS : List Syntax.PStmt :=
  [.dec "lp" (eAnd (eEq (eAnd (v "y4") (n 3)) (n 0))
     (eAnd (ne (v "y4") (n 100)) (eAnd (ne (v "y4") (n 200)) (ne (v "y4") (n 300))))),
   .dec "dm" (n 31),
   .ite (eEq (v "mo") (n 2)) [.assign "dm" (eAdd (n 28) (v "lp"))]
     [ifs (or2 (or2 (eEq (v "mo") (n 4)) (eEq (v "mo") (n 6))) (or2 (eEq (v "mo") (n 9)) (eEq (v "mo") (n 11))))
       [.assign "dm" (n 30)]]]

/-- The checks of the day, the time, and the day of the week. -/
def checkS : List Syntax.PStmt :=
  [ifs (or2 (or2 (eLt (v "yr") (n 1900)) (or2 (eLt (v "dy") (n 1)) (eLt (v "dm") (v "dy"))))
     (or2 (eLt (n 23) (v "hh")) (or2 (eLt (n 59) (v "mi")) (eLt (n 60) (v "se")))))
     [.ret (n 0)],
   .dec "ye" (v "yr"), ifs (eLe (n ArticleProg.yearBig) (v "yr")) [.assign "ye" (eAdd (n 2000) (v "y4"))],
   .call "days" "artCivil" [v "ye", v "mo", v "dy"], brk,
   ifs (v "hw")
     [ifs (eEq (v "wk") (n 0)) [.ret (n 0)],
      .call "q7" "artDiv" [eAdd (v "days") (n 700004), n 7], brk,
      ifs (ne (eSub (v "wk") (n 1)) (eSub (eAdd (v "days") (n 700004)) (eMul (v "q7") (n 7)))) [.ret (n 0)]],
   ifs (eLe (n ArticleProg.yearBig) (v "yr")) [.ret (n 2)],
   setW ArticleProg.xValue (eSub (eAdd (eMul (v "days") (n 86400))
     (eAdd (eAdd (eMul (v "hh") (n 3600)) (eMul (v "mi") (n 60))) (v "se"))) (v "off")),
   .ret (n 1)]

theorem artDate_body : guardL (ArticleProg.artDate .none).body =
    [areaAt ArticleProg.ofs, .dec "c" (v "s"), .dec "go" (n 1), .while (v "go") parenBody,
     .dec "nc" (n 0), .dec "cp" (n 0), .dec "i" (v "s"), .while (eLt (v "i") (v "c")) commaBody,
     ifs (eLt (n 1) (v "nc")) [.ret (n 0)],
     .dec "wk" (n 0), .dec "hw" (n 0), .dec "ts" (v "s"),
     ifs (eEq (v "nc") (n 1))
       (toksS "t1" (v "s") (v "cp") ++
        [.assign "wk" (tokIn ArticleSpec.dayNames), .assign "hw" (n 1),
         .call "t2" "artTok" [v "t1", v "cp"], brk, ifs (ne (wd ArticleProg.xTokLen) (n 0)) [.ret (n 0)],
         .assign "ts" (eAdd (v "cp") (n 1))])] ++
    toksS "p1" (v "ts") (v "c") ++ [.dec "ds" (wd ArticleProg.xTokS)] ++
    toksS "p2" (v "p1") (v "c") ++ [.dec "mo" (tokIn ArticleSpec.monthNames)] ++
    toksS "p3" (v "p2") (v "c") ++
    [.dec "ys" (wd ArticleProg.xTokS),
     .call "dy" "artNum" [v "ds", v "p1"], brk, ifs (eLt (v "dy") (n 0)) [.ret (n 0)],
     ifs (eEq (v "mo") (n 0)) [.ret (n 0)],
     .call "yr" "artNum" [v "ys", v "p3"], brk, ifs (eLt (v "yr") (n 0)) [.ret (n 0)],
     .dec "y4" (wd ArticleProg.xNumMod),
     ifs (eAnd (n 0) (eLe (n ArticleProg.yearBig) (v "yr"))) [.assign "y4" (n 0)],
     .dec "j" (v "p3"), .dec "ph" (n 0), .dec "np" (n 0), .dec "cv" (n 0), .dec "cd" (n 0),
     .dec "hh" (n 0), .dec "mi" (n 0), .dec "se" (n 0), .dec "bad" (n 0),
     .dec "zl" (n 0), .dec "z0" (n 0), .dec "zd" (n 1), .dec "zv" (n 0), .dec "zg" (n 1),
     .while (eLt (v "j") (v "c")) tzBody,
     ifs (eEq (v "ph") (n 0)) finishS,
     ifs (or2 (v "bad") (or2 (eLt (v "np") (n 2)) (eLt (n 3) (v "np")))) [.ret (n 0)],
     .dec "off" (n 0)] ++ zoneS ++ monthS ++ checkS := by
  show guardL (_ ++ _ ++ _ ++ _ ++ _ ++ _ ++ _ ++ _ ++ _) = _
  simp only [DN.News.ArticleGrammar.guardL_append]
  rfl

/-! ## Up to the comment -/

/-- Not the `(` that starts a comment. -/
def notParen (b : BitVec 8) : Bool := b != ArticleSpec.LPAREN

theorem notParen_toNat (b : BitVec 8) : notParen b = decide (b.toNat ≠ 40) := by
  unfold notParen; rw [bne, ArticleScan.beq_byte]; simp [ArticleSpec.LPAREN]

/-- Where the comment starts from `S`, or `E`. -/
def parenAt (a : Bytes) (S E : Nat) : Nat := S + ((seg a S E).takeWhile notParen).length

def parenL (S E : Nat) (A : Word) (g c : Nat) : List (String × Value) :=
  [("go", BitVec.ofNat 64 g), ("c", BitVec.ofNat 64 c), ("a", A), ("s", BitVec.ofNat 64 S), ("e", BitVec.ofNat 64 E)]

theorem runF_parenL {s0 u : PancakeState σ} {l : List (String × Value)} {F : (Word → Word) → Prop}
    (h : RunF s0 l F u) {S E : Nat} {A : Word} {g c : Nat}
    (h1 : l.lookup "go" = some (BitVec.ofNat 64 g) := by rfl) (h2 : l.lookup "c" = some (BitVec.ofNat 64 c) := by rfl)
    (h3 : l.lookup "a" = some A := by rfl) (h4 : l.lookup "s" = some (BitVec.ofNat 64 S) := by rfl)
    (h5 : l.lookup "e" = some (BitVec.ofNat 64 E) := by rfl) : RunF s0 (parenL S E A g c) F u :=
  ⟨⟨fun q hq => by
    simp only [parenL, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    all_goals first | exact vals_lookup h.1.vals h1 | exact vals_lookup h.1.vals h2 | exact vals_lookup h.1.vals h3 |
      exact vals_lookup h.1.vals h4 | exact vals_lookup h.1.vals h5,
    h.1.memaddrs, h.1.base, h.1.code, h.1.be⟩, h.2⟩

/-- **The first loop finds where the comment starts.** -/
theorem paren_loop (o : Oracle σ) {A : Word} {s1 : PancakeState σ} {a : Bytes} {m0 : Word → Word}
    (hin : InputAt m0 s1.memaddrs s1.be A a) {S E : Nat} (hSE : S ≤ E) (hE : E ≤ a.length) (hEM : E ≤ artMax) :
    Frag o [.while (v "go") parenBody] (RunF s1 (parenL S E A 1 S) (· = m0))
      (RunF s1 (parenL S E A 0 (parenAt a S E)) (· = m0)) := by
  have hM := artMax_eq
  let I : Assn σ := fun u => ∃ t : Nat × Nat, RunF s1 (parenL S E A t.1 t.2) (· = m0) u ∧ S ≤ t.2 ∧ t.2 ≤ E ∧
    (seg a S t.2).all notParen = true ∧ (t.1 = 1 ∨ t.1 = 0 ∧ (t.2 = E ∨ notParen a[t.2]! = false))
  have hIc : Safe.ClockFree I := fun u k ⟨t, h, hv⟩ => ⟨t, runF_clock _ _ _ u k h, hv⟩
  have hlow : LowKK parenBody := lowK_any _ (k := .skip) rfl
  refine frag_conseq (frag_while o rfl hlow hIc (fun _ _ _ _ hy => by cases hy)
    (fun u ⟨t, h, _⟩ => ⟨_, ev_var (vals_lookup h.1.vals rfl)⟩) ?_)
    (fun u h => ⟨(1, S), h, Nat.le_refl _, hSE, by simp [DN.News.ArticleLines.seg_self], .inl rfl⟩) ?_
  · refine frag_conseq (P0 := fun u => ∃ t : Nat × Nat, (fun t u => RunF s1 (parenL S E A t.1 t.2) (· = m0) u ∧
      S ≤ t.2 ∧ t.2 ≤ E ∧ (seg a S t.2).all notParen = true ∧ t.1 = 1) t u) (frag_exists hlow fun t => ?_)
      (fun u ⟨⟨t, h, h1, h2, h3, h4⟩, h0⟩ => ⟨t, h, h1, h2, h3, flag01 (h4.imp_right fun h => h.1) (by
        rw [ev_var (vals_lookup h.1.vals rfl)] at h0; exact fun e => h0 (by rw [e]))⟩) fun _ h => h
    refine frag_pure (S ≤ t.2 ∧ t.2 ≤ E ∧ (seg a S t.2).all notParen = true ∧ t.1 = 1) (fun u h => h.2) hlow
      fun ⟨h1, h2, h3, h4⟩ => ?_
    obtain ⟨g, i⟩ := t
    simp only at h1 h2 h3 h4; subst h4
    refine frag_conseq (P0 := RunF s1 (parenL S E A 1 i) (· = m0)) ?_ (fun u h => h.1) fun _ h => h
    refine DN.News.ArticleRun.frag_ifR o rfl (lowK_any _ (k := .skip) rfl) (lowK_any _ (k := .skip) rfl) hIc
      (fun u y w ⟨t, h, hv⟩ hy => by
        change y ∈ ["b"] at hy
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hy; subst hy
        exact ⟨t, runF_restore h rfl w, hv⟩) (fun _ _ _ _ hy => by cases hy) (b := decide (i < E))
      (fun u h => FramerCode.eval_lt (by omega) (by omega) (ev_var (vals_lookup h.1.vals rfl))
        (ev_var (vals_lookup h.1.vals rfl))) (fun hi => ?_) fun hi => ?_
    · have hi' : i < E := of_decide_eq_true hi
      have hia : i < a.length := by omega
      refine frag_append (xs := [_, _]) (frag_append (xs := [_]) (kept_frag o (by decide) (runF_clock _ _ _)
        fun u h => ⟨i, vals_lookup h.1.vals rfl, by omega⟩) (runF_dec o rfl rfl (v := BitVec.ofNat 64 (a[i]!).toNat)
          fun u h => inByte_eval (input_run hin h) (vals_lookup h.1.vals rfl) hia (vals_lookup h.1.vals rfl))) ?_
      have hbl := (a[i]!).isLt
      refine DN.News.ScanRun.frag_if o rfl (lowK_any _ (k := .skip) rfl) (lowK_any _ (k := .skip) rfl) rfl rfl hIc
        (b := decide ((a[i]!).toNat = 40)) (fun u h => FramerCode.eval_eq (by omega) (by decide)
          (ev_var (vals_lookup h.1.vals rfl)) rfl) (fun hp => ?_) fun hp => ?_
      · exact frag_conseq (runF_set o rfl rfl (v := BitVec.ofNat 64 0) fun _ _ => rfl) (fun _ h => h)
          fun u h => ⟨(0, i), runF_parenL h, h1, h2, h3, .inr ⟨rfl, .inr (by
            rw [notParen_toNat]; simpa using of_decide_eq_true hp)⟩⟩
      · refine frag_conseq (runF_set o rfl rfl (v := BitVec.ofNat 64 (i + 1)) fun u h =>
          ev_inc (vals_lookup h.1.vals rfl)) (fun _ h => h) fun u h => ⟨(1, i + 1), runF_parenL h, by omega, by omega,
            ?_, .inl rfl⟩
        rw [seg_succ a h1 hia, List.all_append, h3, List.all_cons, ← getElem!_pos a i hia, notParen_toNat,
          decide_eq_true (by simpa using hp)]; rfl
    · have hi' : ¬i < E := fun e => by simp [e] at hi
      exact frag_conseq (runF_set o rfl rfl (v := BitVec.ofNat 64 0) fun _ _ => rfl) (fun _ h => h)
        fun u h => ⟨(0, i), runF_parenL h, h1, h2, h3, .inr ⟨rfl, .inl (by omega)⟩⟩
  · intro u ⟨⟨t, h, h1, h2, h3, h4⟩, h0⟩
    rw [ev_var (vals_lookup h.1.vals rfl)] at h0
    rcases h4 with e | ⟨e, hs⟩
    · rw [e] at h0; exact absurd (Option.some.inj h0) (by decide)
    · obtain ⟨g, i⟩ := t
      simp only at e h1 h2 h3 hs h; subst e
      rw [← seg_tw hE h1 h2 h3 hs] at h; exact h

/-! ## The commas before it -/

def commaL (S E : Nat) (A : Word) (c nc cp i : Nat) : List (String × Value) :=
  [("i", BitVec.ofNat 64 i), ("cp", BitVec.ofNat 64 cp), ("nc", BitVec.ofNat 64 nc)] ++ parenL S E A 0 c

theorem runF_commaL {s0 u : PancakeState σ} {l : List (String × Value)} {F : (Word → Word) → Prop}
    (h : RunF s0 l F u) {S E : Nat} {A : Word} {c nc cp i : Nat}
    (h1 : l.lookup "i" = some (BitVec.ofNat 64 i) := by rfl) (h2 : l.lookup "cp" = some (BitVec.ofNat 64 cp) := by rfl)
    (h3 : l.lookup "nc" = some (BitVec.ofNat 64 nc) := by rfl) (h4 : l.lookup "go" = some (BitVec.ofNat 64 0) := by rfl)
    (h5 : l.lookup "c" = some (BitVec.ofNat 64 c) := by rfl) (h6 : l.lookup "a" = some A := by rfl)
    (h7 : l.lookup "s" = some (BitVec.ofNat 64 S) := by rfl) (h8 : l.lookup "e" = some (BitVec.ofNat 64 E) := by rfl) :
    RunF s0 (commaL S E A c nc cp i) F u :=
  ⟨⟨fun q hq => by
    simp only [commaL, parenL, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first | exact vals_lookup h.1.vals h1 | exact vals_lookup h.1.vals h2 | exact vals_lookup h.1.vals h3 |
      exact vals_lookup h.1.vals h4 | exact vals_lookup h.1.vals h5 | exact vals_lookup h.1.vals h6 |
      exact vals_lookup h.1.vals h7 | exact vals_lookup h.1.vals h8,
    h.1.memaddrs, h.1.base, h.1.code, h.1.be⟩, h.2⟩

/-- What the loop over the commas keeps: their count so far, and the first one's place, with none before it. -/
def CommaInv (a : Bytes) (S c nc cp i : Nat) : Prop :=
  S ≤ i ∧ i ≤ c ∧ nc = ((seg a S i).filter isComma).length ∧
    (nc = 0 ∧ cp = 0 ∨ 1 ≤ nc ∧ S ≤ cp ∧ cp < i ∧ isComma a[cp]! = true ∧ (seg a S cp).all (!isComma ·) = true)

/-- **The loop over the commas counts them** and finds the first. -/
theorem comma_loop (o : Oracle σ) {A : Word} {s1 : PancakeState σ} {a : Bytes} {m0 : Word → Word}
    (hin : InputAt m0 s1.memaddrs s1.be A a) {S E c : Nat} (hSc : S ≤ c) (hc : c ≤ E) (hE : E ≤ a.length)
    (hEM : E ≤ artMax) :
    Frag o [.while (eLt (v "i") (v "c")) commaBody] (RunF s1 (commaL S E A c 0 0 S) (· = m0))
      (fun u => ∃ nc cp, RunF s1 (commaL S E A c nc cp c) (· = m0) u ∧ CommaInv a S c nc cp c) := by
  have hM := artMax_eq
  let I : Assn σ := fun u => ∃ t : Nat × Nat × Nat, RunF s1 (commaL S E A c t.1 t.2.1 t.2.2) (· = m0) u ∧
    CommaInv a S c t.1 t.2.1 t.2.2
  have hIc : Safe.ClockFree I := fun u k ⟨t, h, hv⟩ => ⟨t, runF_clock _ _ _ u k h, hv⟩
  have hlow : LowKK commaBody := lowK_any _ (k := .skip) rfl
  have hcond : ∀ u (t : Nat × Nat × Nat), RunF s1 (commaL S E A c t.1 t.2.1 t.2.2) (· = m0) u →
      CommaInv a S c t.1 t.2.1 t.2.2 → eval u (.cmp .less (.var "i") (.var "c")) = some (bw (decide (t.2.2 < c))) :=
    fun u t h hq => FramerCode.eval_lt (by have := hq.2.1; omega) (by omega) (ev_var (vals_lookup h.1.vals rfl))
      (ev_var (vals_lookup h.1.vals rfl))
  refine frag_conseq (frag_while o rfl hlow hIc
    (fun u z w ⟨t, h, hv⟩ hz => by
      change z ∈ ["b2"] at hz
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hz; subst hz
      exact ⟨t, runF_restore h rfl w, hv⟩) (fun u ⟨t, h, hv⟩ => ⟨_, hcond u t h hv⟩) ?_)
    (fun u h => ⟨(0, 0, S), h, Nat.le_refl _, hSc, by simp [DN.News.ArticleLines.seg_self], .inl ⟨rfl, rfl⟩⟩) ?_
  · refine frag_conseq (P0 := fun u => ∃ t : Nat × Nat × Nat, (fun t u => RunF s1 (commaL S E A c t.1 t.2.1 t.2.2)
      (· = m0) u ∧ CommaInv a S c t.1 t.2.1 t.2.2 ∧ t.2.2 < c) t u) (frag_exists hlow fun t => ?_)
      (fun u ⟨⟨t, h, hv⟩, h0⟩ => ⟨t, h, hv, by rw [hcond u t h hv] at h0; exact of_decide_eq_true (bw_ne0 h0)⟩)
      fun _ h => h
    refine frag_pure (CommaInv a S c t.1 t.2.1 t.2.2 ∧ t.2.2 < c) (fun u h => h.2) hlow fun ⟨hq, hi⟩ => ?_
    obtain ⟨nc, cp, i⟩ := t
    simp only at hq hi
    obtain ⟨h1, h2, hnc, hcp⟩ := hq
    have hia : i < a.length := by omega
    have hbl := (a[i]!).isLt
    refine frag_conseq (P0 := RunF s1 (commaL S E A c nc cp i) (· = m0)) ?_ (fun u h => h.1) fun _ h => h
    refine frag_append (xs := [_, _]) (frag_append (xs := [_]) (kept_frag o (by decide) (runF_clock _ _ _)
      fun u h => ⟨i, vals_lookup h.1.vals rfl, by omega⟩) (runF_dec o rfl rfl (v := BitVec.ofNat 64 (a[i]!).toNat)
        fun u h => inByte_eval (input_run hin h) (vals_lookup h.1.vals rfl) hia (vals_lookup h.1.vals rfl))) ?_
    have hseg : seg a S (i + 1) = seg a S i ++ [a[i]!] := by rw [seg_succ a h1 hia, getElem!_pos a i hia]
    have hncB : nc ≤ i := by
      rw [hnc]; exact Nat.le_trans (List.length_filter_le _ _) (by rw [seg_length a h1 (by omega)]; omega)
    let LB : Nat → Nat → List (String × Value) := fun nc' cp' =>
      ("b2", BitVec.ofNat 64 (a[i]!).toNat) :: commaL S E A c nc' cp' i
    have hinc : ∀ nc' cp', CommaInv a S c nc' cp' (i + 1) →
        Frag o [inc "i"] (RunF s1 (LB nc' cp') (· = m0)) I := fun nc' cp' hq' =>
      frag_conseq (runF_set o rfl rfl (v := BitVec.ofNat 64 (i + 1)) fun u h => ev_inc (vals_lookup h.1.vals rfl))
        (fun _ h => h) fun u h => ⟨(nc', cp', i + 1), runF_commaL h, hq'⟩
    by_cases hcm : (a[i]!).toNat = 44
    · have hcm' : isComma a[i]! = true := by rw [isComma_toNat]; simpa using hcm
      have hnc' : nc + 1 = ((seg a S (i + 1)).filter isComma).length := by
        rw [hseg, List.filter_append, List.length_append, ← hnc, List.filter_cons, if_pos hcm']; rfl
      refine frag_append (xs := [_]) (DN.News.ArticleScan.frag_ifT o rfl (lowK_any _ (k := .skip) rfl) lowKK_nil rfl rfl
        (runF_clock _ _ _) (Q := RunF s1 (LB (nc + 1) (if nc = 0 then i else cp)) (· = m0))
        (fun u h => (FramerCode.eval_eq (by omega) (by decide) (ev_var (vals_lookup h.1.vals rfl)) rfl).trans
          (by rw [bw_t hcm])) ?_) (hinc _ _ ?_)
      · by_cases h0 : nc = 0
        · refine frag_append (xs := [_]) (DN.News.ArticleScan.frag_ifT o rfl (lowK_any _ (k := .skip) rfl) lowKK_nil
            rfl rfl (runF_clock _ _ _) (Q := RunF s1 (LB nc i) (· = m0))
            (fun u h => (FramerCode.eval_eq (by omega) (by decide) (ev_var (vals_lookup h.1.vals rfl)) rfl).trans
              (by rw [bw_t h0]))
              (set_to o rfl rfl (v := BitVec.ofNat 64 i) (fun u h => ev_var (vals_lookup h.1.vals rfl))
                fun u h => runF_push h rfl (runF_commaL h))) ?_
          exact set_to o rfl rfl (v := BitVec.ofNat 64 (nc + 1)) (fun u h => ev_inc (vals_lookup h.1.vals rfl))
            fun u h => by rw [if_pos h0]; exact runF_push h rfl (runF_commaL h)
        · refine frag_append (xs := [_]) (DN.News.ArticleScan.frag_ifF o rfl (lowK_any _ (k := .skip) rfl) lowKK_nil
            rfl rfl (runF_clock _ _ _) (Q := RunF s1 (LB nc cp) (· = m0))
            (fun u h => (FramerCode.eval_eq (by omega) (by decide) (ev_var (vals_lookup h.1.vals rfl)) rfl).trans
              (by rw [bw_f h0])) (frag_nil o fun _ h => h)) ?_
          exact set_to o rfl rfl (v := BitVec.ofNat 64 (nc + 1)) (fun u h => ev_inc (vals_lookup h.1.vals rfl))
            fun u h => by rw [if_neg h0]; exact runF_push h rfl (runF_commaL h)
      · refine ⟨by omega, by omega, hnc', .inr ⟨by omega, ?_⟩⟩
        by_cases h0 : nc = 0
        · rw [if_pos h0]
          rcases hcp with ⟨-, -⟩ | ⟨h1', -⟩
          · refine ⟨h1, by omega, hcm', ?_⟩
            have : ((seg a S i).filter isComma) = [] := List.eq_nil_of_length_eq_zero (by omega)
            rw [List.filter_eq_nil_iff] at this
            exact List.all_eq_true.2 fun x hx => by simpa using this x hx
          · omega
        · rw [if_neg h0]
          rcases hcp with ⟨h0', -⟩ | ⟨-, h2', h3', h4', h5'⟩
          · exact absurd h0' h0
          · exact ⟨h2', by omega, h4', h5'⟩
    · have hcm' : isComma a[i]! = false := by rw [isComma_toNat]; simpa using hcm
      refine frag_append (xs := [_]) (DN.News.ArticleScan.frag_ifF o rfl (lowK_any _ (k := .skip) rfl) lowKK_nil rfl rfl
        (runF_clock _ _ _) (Q := RunF s1 (LB nc cp) (· = m0))
        (fun u h => (FramerCode.eval_eq (by omega) (by decide) (ev_var (vals_lookup h.1.vals rfl)) rfl).trans
          (by rw [bw_f hcm])) (frag_nil o fun _ h => h)) (hinc _ _ ?_)
      have hnc2 : nc = ((seg a S (i + 1)).filter isComma).length := by
        rw [hseg, List.filter_append, List.length_append, ← hnc, List.filter_cons, if_neg (by rw [hcm']; decide)]; rfl
      refine ⟨by omega, by omega, hnc2, ?_⟩
      rcases hcp with h0 | ⟨h1', h2', h3', h4', h5'⟩
      · exact .inl h0
      · exact .inr ⟨h1', h2', by omega, h4', h5'⟩
  · intro u ⟨⟨t, h, hq⟩, h0⟩
    rw [hcond u t h hq] at h0
    have hge : c ≤ t.2.2 := by have := of_decide_eq_false (bw_eq0 h0); omega
    have e : t.2.2 = c := by have := hq.2.1; omega
    obtain ⟨nc, cp, i⟩ := t
    simp only at e h hq; subst e
    exact ⟨nc, cp, h, hq⟩

/-! ## A word among names -/

/-- One letter's test of `spells`. -/
def spellG (o : Nat) : Syntax.PExpr → Nat × Nat → Syntax.PExpr :=
  fun acc (c, i) => eAnd acc (eEq (lowerE (byte (Syntax.atOff (v "a") (o + i)))) (n c))

/-- **The letters' tests**, the bytes from `o` known: true when each, read in lower case, is the letter. -/
theorem spells_fold {P : PancakeState σ → Prop} {A : Word} (hA : ∀ u, P u → u.locals "a" = some A) {o : Nat}
    (ho : 0 < o) (tb : Nat → BitVec 8)
    (hb : ∀ i u, i < 8 → P u → memLoadByte u.memory u.memaddrs u.be (at_ A (o + i)) = some (tb i)) :
    ∀ (cs : List Nat) (k0 : Nat) (acc : Syntax.PExpr) (Eacc : PancakeExp) (b0 : Bool),
      Lower.lowerExp acc = some Eacc → (∀ u, P u → eval u Eacc = some (bw b0)) → (∀ c ∈ cs, c < 2 ^ 64) →
      k0 + cs.length ≤ 8 → ∃ E, Lower.lowerExp ((cs.zipIdx k0).foldl (spellG o) acc) = some E ∧ ∀ u, P u →
        eval u E = some (bw (b0 && (cs.zipIdx k0).all fun ci => decide (lowN (tb ci.2).toNat = ci.1)))
  | [], _, _, Eacc, b0, hl, hv, _, _ => ⟨Eacc, hl, fun u h => by simp [hv u h]⟩
  | c :: cs, k0, acc, Eacc, b0, hl, hv, hc, h8 => by
    simp only [List.length_cons] at h8
    have hc0 := hc c List.mem_cons_self
    have hx : (o + k0 == 0) = false := by simp; omega
    obtain ⟨E, hE, hEv⟩ := spells_fold hA ho tb hb cs (k0 + 1) (spellG o acc (c, k0))
      (.op .and_ Eacc (.cmp .equal (.op .add (.loadByte (.op .add (.var "a") (.const (BitVec.ofNat 64 (o + k0)))))
        (.mul (.const (BitVec.ofNat 64 32)) (.op .and_
          (.cmp .notLess (.loadByte (.op .add (.var "a") (.const (BitVec.ofNat 64 (o + k0)))))
            (.const (BitVec.ofNat 64 65)))
          (.cmp .notLess (.const (BitVec.ofNat 64 90))
            (.loadByte (.op .add (.var "a") (.const (BitVec.ofNat 64 (o + k0))))))))) (.const (BitVec.ofNat 64 c))))
      (b0 && decide (lowN (tb k0).toNat = c))
      (by
        show Lower.lowerExp (eAnd acc (eEq (lowerE (byte (Syntax.atOff (v "a") (o + k0)))) (n c))) = _
        rw [atOff_eq hx]; simp [Lower.lowerExp, hl, lowerE, byte, eAnd, eEq, eAdd, eMul, eLe, n, v])
      (fun u h => by
        have hbyte : eval u (.loadByte (.op .add (.var "a") (.const (BitVec.ofNat 64 (o + k0))))) =
            some (BitVec.ofNat 64 (tb k0).toNat) := loadByte_eval (atA_eval (hA u h)) (hb k0 u (by omega) h)
        have hlw : lowN (tb k0).toNat < 2 ^ 64 := by
          have := (tb k0).isLt; unfold lowN; split <;> omega
        rw [FramerCode.eval_and (hv u h) (FramerCode.eval_eq hlw hc0 (lowerEx_eval (tb k0).isLt hbyte) rfl)])
      (fun c' hc' => hc c' (List.mem_cons_of_mem _ hc')) (by omega)
    refine ⟨E, by simpa [List.zipIdx_cons] using hE, fun u h => ?_⟩
    rw [hEv u h]
    simp [List.zipIdx_cons, Bool.and_assoc]

/-- Whether the bytes `tb` spell `s` in lower case. -/
def spellsOK (tb : Nat → BitVec 8) (s : String) : Bool :=
  (ArticleProg.codes (ArticleProg.lowerS s)).zipIdx.all fun ci => decide (lowN (tb ci.2).toNat = ci.1)

/-- One name's term of `tokIn`. -/
def tokF : Syntax.PExpr → String × Nat → Syntax.PExpr :=
  fun acc (s, k) => eAdd acc (eMul (n (k + 1))
    (eAnd (eEq (wd ArticleProg.xTokLen) (n s.length)) (ArticleProg.spells ArticleProg.xTok (ArticleProg.lowerS s))))

theorem tokIn_def (names : List String) : tokIn names = names.zipIdx.foldl tokF (n 0) := rfl

/-- What `tokIn` adds up: each name's place, counted from one, where the word is the name. -/
def tokSum (L : Nat) (tb : Nat → BitVec 8) : List String → Nat → Nat
  | [], _ => 0
  | s :: names, k => (if L = s.length ∧ spellsOK tb s = true then k + 1 else 0) + tokSum L tb names (k + 1)

theorem bw_mul (k : Nat) (b : Bool) : BitVec.ofNat 64 k * bw b = BitVec.ofNat 64 (if b then k else 0) := by
  cases b <;> simp [bw]

/-- **`tokIn`'s value**, the word's length and bytes known. -/
theorem tokIn_fold {P : PancakeState σ → Prop} {A : Word} (hA : ∀ u, P u → u.locals "a" = some A) {L : Nat}
    (hL : L < 2 ^ 64) (hLv : ∀ u, P u → eval u (.loadWord (.op .add (.var "a")
      (.const (BitVec.ofNat 64 ArticleProg.xTokLen)))) = some (BitVec.ofNat 64 L)) (tb : Nat → BitVec 8)
    (hb : ∀ i u, i < 8 → P u → memLoadByte u.memory u.memaddrs u.be (at_ A (ArticleProg.xTok + i)) = some (tb i)) :
    ∀ (names : List String) (k0 : Nat) (acc : Syntax.PExpr) (Eacc : PancakeExp) (A0 : Nat),
      Lower.lowerExp acc = some Eacc → (∀ u, P u → eval u Eacc = some (BitVec.ofNat 64 A0)) →
      (∀ s ∈ names, s.length < 2 ^ 64 ∧ (∀ c ∈ ArticleProg.codes (ArticleProg.lowerS s), c < 2 ^ 64) ∧
        (ArticleProg.codes (ArticleProg.lowerS s)).length ≤ 8) →
      ∃ E, Lower.lowerExp ((names.zipIdx k0).foldl tokF acc) = some E ∧ ∀ u, P u →
        eval u E = some (BitVec.ofNat 64 (A0 + tokSum L tb names k0))
  | [], _, _, Eacc, A0, hl, hv, _ => ⟨Eacc, hl, fun u h => by simp [hv u h, tokSum]⟩
  | s :: names, k0, acc, Eacc, A0, hl, hv, hn => by
    obtain ⟨hs1, hs2, hs3⟩ := hn s List.mem_cons_self
    obtain ⟨Es, hEs, hEsv⟩ := spells_fold hA (by rw [xTok_eq]; decide) tb hb (ArticleProg.codes (ArticleProg.lowerS s))
      0 (n 1) (.const (BitVec.ofNat 64 1)) true rfl (fun _ _ => rfl) hs2 (by omega)
    have hlen : Lower.lowerExp (wd ArticleProg.xTokLen) = some (.loadWord (.op .add (.var "a")
        (.const (BitVec.ofNat 64 ArticleProg.xTokLen)))) := wd_lower 20
    let T : Nat := if L = s.length ∧ spellsOK tb s = true then k0 + 1 else 0
    obtain ⟨E, hE, hEv⟩ := tokIn_fold hA hL hLv tb hb names (k0 + 1) (tokF acc (s, k0))
      (.op .add Eacc (.mul (.const (BitVec.ofNat 64 (k0 + 1))) (.op .and_ (.cmp .equal
        (.loadWord (.op .add (.var "a") (.const (BitVec.ofNat 64 ArticleProg.xTokLen))))
        (.const (BitVec.ofNat 64 s.length))) Es))) (A0 + T)
      (by
        show Lower.lowerExp (eAdd acc (eMul (n (k0 + 1)) (eAnd (eEq (wd ArticleProg.xTokLen) (n s.length))
          (ArticleProg.spells ArticleProg.xTok (ArticleProg.lowerS s))))) = _
        have hEs' : Lower.lowerExp (ArticleProg.spells ArticleProg.xTok (ArticleProg.lowerS s)) = some Es := hEs
        simp only [eAdd, eMul, eAnd, eEq, n, Lower.lowerExp, hl, hlen, hEs'])
      (fun u h => by
        rw [DN.News.AbnfLeaves.ev_add (hv u h) (DN.News.AbnfLeaves.ev_mul rfl (FramerCode.eval_and
          (FramerCode.eval_eq hL hs1 (hLv u h) rfl) (hEsv u h))), bw_mul, ← BitVec.ofNat_add]
        congr 2
        simp only [Bool.true_and, T, spellsOK, Bool.and_eq_true, decide_eq_true_eq]
        split <;> rfl)
      fun s' hs' => hn s' (List.mem_cons_of_mem _ hs')
    refine ⟨E, by simpa [List.zipIdx_cons] using hE, fun u h => ?_⟩
    rw [hEv u h]
    simp only [tokSum, T, Nat.add_assoc]

/-- The place, counted from `k + 1`, of the first name `f` picks, or 0. -/
def firstK (f : String → Bool) : List String → Nat → Nat
  | [], _ => 0
  | s :: names, k => if f s then k + 1 else firstK f names (k + 1)

theorem tokSum_zero {L : Nat} {tb : Nat → BitVec 8} : ∀ (names : List String) (k : Nat),
    (∀ s ∈ names, ¬(L = s.length ∧ spellsOK tb s = true)) → tokSum L tb names k = 0
  | [], _, _ => rfl
  | s :: names, k, h => by
    simp only [tokSum, if_neg (h s List.mem_cons_self), Nat.zero_add]
    exact tokSum_zero names (k + 1) fun s' hs' => h s' (List.mem_cons_of_mem _ hs')

/-- **At most one name spelled**: the sum is the first one's place. -/
theorem tokSum_first {L : Nat} {tb : Nat → BitVec 8} : ∀ (names : List String) (k : Nat),
    names.Pairwise (fun s s' => ¬((L = s.length ∧ spellsOK tb s = true) ∧ (L = s'.length ∧ spellsOK tb s' = true))) →
    tokSum L tb names k = firstK (fun s => decide (L = s.length) && spellsOK tb s) names k
  | [], _, _ => rfl
  | s :: names, k, h => by
    rw [List.pairwise_cons] at h
    simp only [tokSum, firstK, Bool.and_eq_true, decide_eq_true_eq]
    by_cases hs : L = s.length ∧ spellsOK tb s = true
    · rw [if_pos hs, if_pos hs, tokSum_zero names (k + 1) fun s' hs' h' => h.1 s' hs' ⟨hs, h'⟩]
    · rw [if_neg hs, if_neg hs, Nat.zero_add, tokSum_first names (k + 1) h.2]

theorem firstK_congr {f g : String → Bool} : ∀ (names : List String) (k : Nat), (∀ s ∈ names, f s = g s) →
    firstK f names k = firstK g names k
  | [], _, _ => rfl
  | s :: names, k, h => by
    simp only [firstK, h s List.mem_cons_self,
      firstK_congr names (k + 1) fun s' hs' => h s' (List.mem_cons_of_mem _ hs')]

theorem indexOf_firstK (w : Bytes) : ∀ (names : List String) (k : Nat),
    ((ArticleSpec.indexOf w names k).map (· + 1)).getD 0 = firstK (ArticleSpec.named w) names k
  | [], _ => rfl
  | s :: names, k => by
    simp only [ArticleSpec.indexOf, firstK]
    split
    · rfl
    · exact indexOf_firstK w names (k + 1)

theorem spellsOK_iff {tb : Nat → BitVec 8} {s : String} : spellsOK tb s = true ↔
    ∀ i (hi : i < (ArticleProg.codes (ArticleProg.lowerS s)).length),
      lowN (tb i).toNat = (ArticleProg.codes (ArticleProg.lowerS s))[i] := by
  unfold spellsOK
  rw [List.all_eq_true]
  constructor
  · intro h i hi
    have := h ((ArticleProg.codes (ArticleProg.lowerS s))[i], i) (List.mem_zipIdx_iff_getElem?.2 (by simp [hi]))
    simpa using this
  · intro h ci hci
    have e := List.getElem?_eq_some_iff.1 (List.mem_zipIdx_iff_getElem?.1 hci)
    simp only [decide_eq_true_eq]
    rw [h ci.2 (by simpa using e.1)]
    simpa using e.2

/-- Two names both spelled by the same bytes, of one length, are one. -/
theorem spellsOK_same {tb : Nat → BitVec 8} {s s' : String} (h : spellsOK tb s = true) (h' : spellsOK tb s' = true)
    (hl : (ArticleProg.codes (ArticleProg.lowerS s)).length = (ArticleProg.codes (ArticleProg.lowerS s')).length) :
    ArticleProg.codes (ArticleProg.lowerS s) = ArticleProg.codes (ArticleProg.lowerS s') :=
  List.ext_getElem hl fun i h1 h2 => by rw [← spellsOK_iff.1 h i h1, ← spellsOK_iff.1 h' i h2]

theorem named_iff {w : Bytes} {s : String} : ArticleSpec.named w s = true ↔
    w.length = (DN.News.CommandSpec.ascii s).length ∧
      ∀ i (h1 : i < w.length) (h2 : i < (DN.News.CommandSpec.ascii s).length),
      lowN w[i].toNat = lowN (DN.News.CommandSpec.ascii s)[i].toNat := by
  unfold ArticleSpec.named ArticleSpec.sameName
  rw [beq_iff_eq]
  constructor
  · intro h
    have hl := congrArg List.length h
    simp only [List.length_map] at hl
    refine ⟨hl, fun i h1 h2 => ?_⟩
    have := congrArg (fun l => l[i]?) h
    simp only [List.getElem?_map, List.getElem?_eq_getElem h1, List.getElem?_eq_getElem h2, Option.map_some,
      Option.some.injEq] at this
    rw [← lowerB_nat, ← lowerB_nat, this]
  · intro ⟨hl, h⟩
    refine List.ext_getElem (by simp [hl]) fun i h1 h2 => ?_
    simp only [List.getElem_map]
    apply BitVec.eq_of_toNat_eq
    rw [lowerB_nat, lowerB_nat]
    exact h i (by simpa using h1) (by simpa using h2)

/-- **`tokIn` gives the word's place among the days' or the months' names**, counted from one, or 0. -/
theorem tokSum_names {names : List String}
    (hnames : names = ArticleSpec.dayNames ∨ names = ArticleSpec.monthNames) (tok : Bytes) (tb : Nat → BitVec 8)
    (htb : ∀ i, i < 3 → i < tok.length → tb i = tok[i]!) :
    tokSum tok.length tb names 0 = ((ArticleSpec.indexOf tok names 0).map (· + 1)).getD 0 := by
  have hc : ∀ s ∈ names, ArticleProg.codes (ArticleProg.lowerS s) =
      (DN.News.CommandSpec.ascii s).map (fun b => lowN b.toNat) ∧ (DN.News.CommandSpec.ascii s).length = 3 := by
    rcases hnames with rfl | rfl <;> decide +kernel
  have hpw : names.Pairwise (fun s s' => ArticleProg.codes (ArticleProg.lowerS s) ≠
      ArticleProg.codes (ArticleProg.lowerS s')) := by
    rcases hnames with rfl | rfl <;> decide +kernel
  rw [indexOf_firstK, tokSum_first names 0 (hpw.imp_of_mem fun hs hs' hne ⟨⟨_, h1⟩, ⟨_, h2⟩⟩ =>
    hne (spellsOK_same h1 h2 (by rw [(hc _ hs).1, (hc _ hs').1]; simp [(hc _ hs).2, (hc _ hs').2])))]
  refine firstK_congr names 0 fun s hs => ?_
  obtain ⟨hcs, h3⟩ := hc s hs
  have hsl : s.length = 3 := by
    have : (DN.News.CommandSpec.ascii s).length = s.length := by simp [DN.News.CommandSpec.ascii]
    omega
  apply Bool.eq_iff_iff.2
  rw [Bool.and_eq_true, decide_eq_true_eq, named_iff, spellsOK_iff, hcs]
  constructor
  · intro ⟨hl, h⟩
    refine ⟨by omega, fun i h1 h2 => ?_⟩
    have := h i (by simpa using h2)
    rw [List.getElem_map, htb i (by omega) h1, getElem!_pos tok i h1] at this
    exact this
  · intro ⟨hl, h⟩
    refine ⟨by omega, fun i hi => ?_⟩
    have hi' : i < (DN.News.CommandSpec.ascii s).length := by simpa using hi
    rw [List.getElem_map, htb i (by omega) (by omega), getElem!_pos tok i (by omega)]
    exact h i (by omega) hi'

/-! ## The time and the zone in the program -/

open DN.News.ArticleDate (TZ tz0 tzStep tzFinish dig zfOf withZ zFirst zGmt zDig zNum zStep zFirst_zl zGmt_zl
  zNum_zl zStep_zl)

/-- The loop's locals' names but the byte's. -/
def tzNames0 : List String := ["zg", "zv", "zd", "z0", "zl", "bad", "se", "mi", "hh", "cd", "cv", "np", "ph", "j"]

/-- The names of the loop's locals. -/
def tzNames : List String := "b3" :: tzNames0

/-- The loop's locals: its state and its place `J`. -/
def tzL (t : TZ) (J : Nat) : List (String × Value) :=
  [("zg", BitVec.ofNat 64 t.zg), ("zv", BitVec.ofNat 64 t.zv), ("zd", BitVec.ofNat 64 t.zd),
   ("z0", BitVec.ofNat 64 t.z0), ("zl", BitVec.ofNat 64 t.zl), ("bad", BitVec.ofNat 64 t.bad),
   ("se", BitVec.ofNat 64 t.se), ("mi", BitVec.ofNat 64 t.mi), ("hh", BitVec.ofNat 64 t.hh),
   ("cd", BitVec.ofNat 64 t.cd), ("cv", BitVec.ofNat 64 t.cv), ("np", BitVec.ofNat 64 t.np),
   ("ph", BitVec.ofNat 64 t.ph), ("j", BitVec.ofNat 64 J)]

/-- The locals read off another list: the loop's from their names, the others' as they were. -/
theorem runF_tz {s0 u : PancakeState σ} {l : List (String × Value)} {F : (Word → Word) → Prop}
    (h : RunF s0 l F u) {t : TZ} {J : Nat} {P : List (String × Value)}
    (h1 : l.lookup "zg" = some (BitVec.ofNat 64 t.zg) := by rfl)
    (h2 : l.lookup "zv" = some (BitVec.ofNat 64 t.zv) := by rfl)
    (h3 : l.lookup "zd" = some (BitVec.ofNat 64 t.zd) := by rfl)
    (h4 : l.lookup "z0" = some (BitVec.ofNat 64 t.z0) := by rfl)
    (h5 : l.lookup "zl" = some (BitVec.ofNat 64 t.zl) := by rfl)
    (h6 : l.lookup "bad" = some (BitVec.ofNat 64 t.bad) := by rfl)
    (h7 : l.lookup "se" = some (BitVec.ofNat 64 t.se) := by rfl)
    (h8 : l.lookup "mi" = some (BitVec.ofNat 64 t.mi) := by rfl)
    (h9 : l.lookup "hh" = some (BitVec.ofNat 64 t.hh) := by rfl)
    (h10 : l.lookup "cd" = some (BitVec.ofNat 64 t.cd) := by rfl)
    (h11 : l.lookup "cv" = some (BitVec.ofNat 64 t.cv) := by rfl)
    (h12 : l.lookup "np" = some (BitVec.ofNat 64 t.np) := by rfl)
    (h13 : l.lookup "ph" = some (BitVec.ofNat 64 t.ph) := by rfl)
    (h14 : l.lookup "j" = some (BitVec.ofNat 64 J) := by rfl) (hP : ∀ q ∈ P, q ∈ l) :
    RunF s0 (tzL t J ++ P) F u :=
  ⟨⟨fun q hq => by
    rcases List.mem_append.1 hq with hq | hq
    · simp only [tzL, List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals first | exact vals_lookup h.1.vals h1 | exact vals_lookup h.1.vals h2 |
        exact vals_lookup h.1.vals h3 | exact vals_lookup h.1.vals h4 | exact vals_lookup h.1.vals h5 |
        exact vals_lookup h.1.vals h6 | exact vals_lookup h.1.vals h7 | exact vals_lookup h.1.vals h8 |
        exact vals_lookup h.1.vals h9 | exact vals_lookup h.1.vals h10 | exact vals_lookup h.1.vals h11 |
        exact vals_lookup h.1.vals h12 | exact vals_lookup h.1.vals h13 | exact vals_lookup h.1.vals h14
    · exact h.1.vals q (hP q hq),
    h.1.memaddrs, h.1.base, h.1.code, h.1.be⟩, h.2⟩

/-- The others' locals kept as one of the loop's is set. -/
theorem mem_set {ns : List String} {P : List (String × Value)} (hfr : ∀ q ∈ P, q.1 ∉ ns) {x : String} (hx : x ∈ ns)
    (v : Value) (front : List (String × Value)) : ∀ q ∈ P, q ∈ (x, v) :: without x (front ++ P) :=
  fun q hq => List.mem_cons_of_mem _ (mem_without (List.mem_append_right _ hq) fun e => hfr q hq (e ▸ hx))

/-- **A conditional setting of a local**, its condition known. -/
theorem cond_set (o : Oracle σ) {s1 : PancakeState σ} {F : (Word → Word) → Prop} {L L' : List (String × Value)}
    {x : String} {w : Value} (hw : L.lookup x = some w) {c : Syntax.PExpr} {C : PancakeExp}
    (hc : Lower.lowerExp c = some C) {e : Syntax.PExpr} {E : PancakeExp} (he : Lower.lowerExp e = some E) {b : Bool}
    (hv : ∀ u, RunF s1 L F u → eval u C = some (bw b)) {vx : Value} (hE : ∀ u, RunF s1 L F u → eval u E = some vx)
    (hT : b = true → ∀ u, RunF s1 ((x, vx) :: without x L) F u → RunF s1 L' F u)
    (hFl : b = false → ∀ u, RunF s1 L F u → RunF s1 L' F u) :
    Frag o [ifs c [.assign x e]] (RunF s1 L F) (RunF s1 L' F) := by
  have hlt : LowKK [.assign x e] := lowKK_one rfl (a := .assign x E) (by simp [Lower.lowerStmt1, he])
  cases b
  · exact DN.News.ArticleScan.frag_ifF o hc hlt lowKK_nil rfl rfl (runF_clock _ _ _) hv (frag_nil o (hFl rfl))
  · exact DN.News.ArticleScan.frag_ifT o hc hlt lowKK_nil rfl rfl (runF_clock _ _ _) hv (set_to o he hw hE (hT rfl))

section tzplain
variable {s1 : PancakeState σ} {F : (Word → Word) → Prop} {P : List (String × Value)} {J : Nat}

/-- **One of the loop's locals set**, the locals `H` before them and `P` after kept: they read off as those of `t'`. -/
theorem tz_set {H : List (String × Value)} (hH : ∀ q ∈ H, q.1 ∉ tzNames0) (hfr0 : ∀ q ∈ P, q.1 ∉ tzNames0)
    {x : String} (hx : x ∈ tzNames0) {vx : Value} {t t' : TZ} {u : PancakeState σ}
    (h : RunF s1 ((x, vx) :: without x (H ++ (tzL t J ++ P))) F u)
    (h1 : ((x, vx) :: without x (H ++ (tzL t J ++ P))).lookup "zg" = some (BitVec.ofNat 64 t'.zg) := by rfl)
    (h2 : ((x, vx) :: without x (H ++ (tzL t J ++ P))).lookup "zv" = some (BitVec.ofNat 64 t'.zv) := by rfl)
    (h3 : ((x, vx) :: without x (H ++ (tzL t J ++ P))).lookup "zd" = some (BitVec.ofNat 64 t'.zd) := by rfl)
    (h4 : ((x, vx) :: without x (H ++ (tzL t J ++ P))).lookup "z0" = some (BitVec.ofNat 64 t'.z0) := by rfl)
    (h5 : ((x, vx) :: without x (H ++ (tzL t J ++ P))).lookup "zl" = some (BitVec.ofNat 64 t'.zl) := by rfl)
    (h6 : ((x, vx) :: without x (H ++ (tzL t J ++ P))).lookup "bad" = some (BitVec.ofNat 64 t'.bad) := by rfl)
    (h7 : ((x, vx) :: without x (H ++ (tzL t J ++ P))).lookup "se" = some (BitVec.ofNat 64 t'.se) := by rfl)
    (h8 : ((x, vx) :: without x (H ++ (tzL t J ++ P))).lookup "mi" = some (BitVec.ofNat 64 t'.mi) := by rfl)
    (h9 : ((x, vx) :: without x (H ++ (tzL t J ++ P))).lookup "hh" = some (BitVec.ofNat 64 t'.hh) := by rfl)
    (h10 : ((x, vx) :: without x (H ++ (tzL t J ++ P))).lookup "cd" = some (BitVec.ofNat 64 t'.cd) := by rfl)
    (h11 : ((x, vx) :: without x (H ++ (tzL t J ++ P))).lookup "cv" = some (BitVec.ofNat 64 t'.cv) := by rfl)
    (h12 : ((x, vx) :: without x (H ++ (tzL t J ++ P))).lookup "np" = some (BitVec.ofNat 64 t'.np) := by rfl)
    (h13 : ((x, vx) :: without x (H ++ (tzL t J ++ P))).lookup "ph" = some (BitVec.ofNat 64 t'.ph) := by rfl)
    (h14 : ((x, vx) :: without x (H ++ (tzL t J ++ P))).lookup "j" = some (BitVec.ofNat 64 J) := by rfl) :
    RunF s1 (H ++ (tzL t' J ++ P)) F u := by
  have hHP : ∀ q ∈ H ++ P, q ∈ (x, vx) :: without x (H ++ (tzL t J ++ P)) := fun q hq => by
    have hn : q.1 ∉ tzNames0 := by
      rcases List.mem_append.1 hq with hq | hq
      · exact hH q hq
      · exact hfr0 q hq
    refine List.mem_cons_of_mem _ (mem_without ?_ fun e => hn (e ▸ hx))
    rcases List.mem_append.1 hq with hq | hq
    · exact List.mem_append_left _ hq
    · exact List.mem_append_right _ (List.mem_append_right _ hq)
  refine runF_mono (runF_tz h h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 hHP) (fun q hq => ?_) fun _ e => e
  rcases List.mem_append.1 hq with hq | hq
  · exact List.mem_append_right _ (List.mem_append_left _ hq)
  · rcases List.mem_append.1 hq with hq | hq
    · exact List.mem_append_left _ hq
    · exact List.mem_append_right _ (List.mem_append_right _ hq)

theorem nil_fr : ∀ q ∈ ([] : List (String × Value)), q.1 ∉ tzNames0 := fun _ h => nomatch h

/-- **A part of the time ended**, the byte read or not. -/
theorem tz_finish0 (o : Oracle σ) (hfr0 : ∀ q ∈ P, q.1 ∉ tzNames0)
    {t : TZ} (hcd : t.cd < 2 ^ 64) (hnp : t.np < 2 ^ 64) :
    Frag o finishS (RunF s1 (tzL t J ++ P) F) (RunF s1 (tzL (tzFinish t) J ++ P) F) := by
  have ev_eq : ∀ {t' : TZ} (x : String) (X k : Nat), X < 2 ^ 64 → k < 2 ^ 64 → (tzL t' J ++ P).lookup x =
      some (BitVec.ofNat 64 X) → ∀ u, RunF s1 (tzL t' J ++ P) F u →
        eval u (.cmp .equal (.var x) (.const (BitVec.ofNat 64 k))) = some (bw (decide (X = k))) :=
    fun x X k hX hk hl u h => FramerCode.eval_eq hX hk (ev_var (vals_lookup h.1.vals hl)) rfl
  let t1 : TZ := { t with bad := if t.cd = 0 then 1 else t.bad }
  refine frag_append (xs := [_]) (cond_set o (L' := tzL t1 J ++ P) rfl rfl rfl (b := decide (t.cd = 0))
    (ev_eq "cd" t.cd 0 hcd (by decide) rfl) (vx := BitVec.ofNat 64 1) (fun _ _ => rfl)
    (fun hb u h => by
      have e : t.cd = 0 := of_decide_eq_true hb
      have h' := tz_set nil_fr hfr0 (t' := { t with bad := 1 }) (by decide) h
      simp only [t1, if_pos e]; exact h')
    (fun hb u h => by
      have e : ¬t.cd = 0 := of_decide_eq_false hb
      simp only [t1, if_neg e]; exact h)) ?_
  let t2 : TZ := { t1 with
    hh := if t.np = 0 then t.cv else t.hh, mi := if t.np = 1 then t.cv else t.mi
    se := if t.np = 2 then t.cv else t.se }
  have hlow : ∀ (x : String) (y : String), LowKK [Syntax.PStmt.assign x (v y)] := fun x y =>
    lowKK_one rfl (a := .assign x (.var y)) (by simp [Lower.lowerStmt1, Lower.lowerExp, v])
  refine frag_append (xs := [_]) (M := RunF s1 (tzL t2 J ++ P) F) ?_ ?_
  · by_cases h0 : t.np = 0
    · refine DN.News.ArticleScan.frag_ifT o rfl (hlow "hh" "cv") (lowK_any _ (k := .skip) rfl) rfl rfl
        (runF_clock _ _ _) (fun u h => (ev_eq (t' := t1) "np" t.np 0 hnp (by decide) rfl u h).trans
          (by rw [bw_t h0])) ?_
      exact set_to o rfl rfl (v := BitVec.ofNat 64 t.cv) (fun u h => ev_var (vals_lookup h.1.vals rfl)) fun u h => by
        have h' := tz_set nil_fr hfr0 (t' := { t1 with hh := t.cv }) (by decide) h
        simp only [t2, if_pos h0, if_neg (show ¬t.np = 1 by omega), if_neg (show ¬t.np = 2 by omega)]; exact h'
    refine DN.News.ArticleScan.frag_ifF o rfl (hlow "hh" "cv") (lowK_any _ (k := .skip) rfl) rfl rfl
      (runF_clock _ _ _) (fun u h => (ev_eq (t' := t1) "np" t.np 0 hnp (by decide) rfl u h).trans (by rw [bw_f h0])) ?_
    by_cases h1 : t.np = 1
    · refine DN.News.ArticleScan.frag_ifT o rfl (hlow "mi" "cv") (lowK_any _ (k := .skip) rfl) rfl rfl
        (runF_clock _ _ _) (fun u h => (ev_eq (t' := t1) "np" t.np 1 hnp (by decide) rfl u h).trans
          (by rw [bw_t h1])) ?_
      exact set_to o rfl rfl (v := BitVec.ofNat 64 t.cv) (fun u h => ev_var (vals_lookup h.1.vals rfl)) fun u h => by
        have h' := tz_set nil_fr hfr0 (t' := { t1 with mi := t.cv }) (by decide) h
        simp only [t2, if_neg h0, if_pos h1, if_neg (show ¬t.np = 2 by omega)]; exact h'
    refine DN.News.ArticleScan.frag_ifF o rfl (hlow "mi" "cv") (lowK_any _ (k := .skip) rfl) rfl rfl
      (runF_clock _ _ _) (fun u h => (ev_eq (t' := t1) "np" t.np 1 hnp (by decide) rfl u h).trans (by rw [bw_f h1])) ?_
    exact cond_set o rfl rfl rfl (b := decide (t.np = 2)) (ev_eq (t' := t1) "np" t.np 2 hnp (by decide) rfl)
      (vx := BitVec.ofNat 64 t.cv) (fun u h => ev_var (vals_lookup h.1.vals rfl))
      (fun hb u h => by
        have e : t.np = 2 := of_decide_eq_true hb
        have h' := tz_set nil_fr hfr0 (t' := { t1 with se := t.cv }) (by decide) h
        simp only [t2, if_neg h0, if_neg h1, if_pos e]; exact h')
      (fun hb u h => by
        have e : ¬t.np = 2 := of_decide_eq_false hb
        simp only [t2, if_neg h0, if_neg h1, if_neg e]; exact h)
  refine frag_append (xs := [_]) (set_to o rfl rfl (v := BitVec.ofNat 64 (t.np + 1))
    (fun u h => ev_inc (vals_lookup h.1.vals rfl)) fun u h => tz_set nil_fr hfr0 (t' := { t2 with np := t.np + 1 })
      (by decide) h) ?_
  refine frag_append (xs := [_]) (set_to o rfl rfl (v := BitVec.ofNat 64 0) (fun _ _ => rfl)
    fun u h => tz_set nil_fr hfr0 (t' := { t2 with np := t.np + 1, cv := 0 }) (by decide) h) ?_
  exact set_to o rfl rfl (v := BitVec.ofNat 64 0) (fun _ _ => rfl)
    fun u h => tz_set nil_fr hfr0 (t' := tzFinish t) (by decide) h

end tzplain

section tzbody
variable {s1 : PancakeState σ} {F : (Word → Word) → Prop} {P : List (String × Value)} {vb : Value} {J : Nat}

/-- The body's locals: the byte read, the loop's, the others'. -/
abbrev LB (vb : Value) (t : TZ) (J : Nat) (P : List (String × Value)) : List (String × Value) :=
  ("b3", vb) :: (tzL t J ++ P)

theorem b3_fr (vb : Value) : ∀ q ∈ [("b3", vb)], q.1 ∉ tzNames0 := fun q hq => by
  rw [List.mem_singleton.1 hq]; show "b3" ∉ tzNames0; decide

theorem fr0 (hfr : ∀ q ∈ P, q.1 ∉ tzNames) : ∀ q ∈ P, q.1 ∉ tzNames0 :=
  fun q hq e => hfr q hq (List.mem_cons_of_mem _ e)

/-- **A conditional setting of one of the loop's locals**, its condition known. -/
theorem tz_cond (o : Oracle σ) {x : String} (hx : x ∈ tzNames) {c : Syntax.PExpr} {C : PancakeExp}
    (hc : Lower.lowerExp c = some C) {e : Syntax.PExpr} {E : PancakeExp} (he : Lower.lowerExp e = some E)
    {t tT : TZ} {b : Bool} (hv : ∀ u, RunF s1 (LB vb t J P) F u → eval u C = some (bw b)) {vx : Value}
    (hE : ∀ u, RunF s1 (LB vb t J P) F u → eval u E = some vx)
    (hT : b = true → ∀ u, RunF s1 ((x, vx) :: without x (LB vb t J P)) F u → RunF s1 (LB vb tT J P) F u)
    (hFl : b = false → tT = t) :
    Frag o [ifs c [.assign x e]] (RunF s1 (LB vb t J P) F) (RunF s1 (LB vb tT J P) F) := by
  have hlk : ∃ w, (LB vb t J P).lookup x = some w := by
    simp only [tzNames, tzNames0, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact ⟨_, rfl⟩
  obtain ⟨w, hw⟩ := hlk
  exact cond_set o hw hc he hv hE hT fun hb u h => by rw [hFl hb]; exact h

/-- **A part of the time ended.** -/
theorem tz_finish (o : Oracle σ) (hfr : ∀ q ∈ P, q.1 ∉ tzNames) {t : TZ} (hcd : t.cd < 2 ^ 64)
    (hnp : t.np < 2 ^ 64) :
    Frag o finishS (RunF s1 (LB vb t J P) F) (RunF s1 (LB vb (tzFinish t) J P) F) := by
  have perm : ∀ t' : TZ, ∀ q ∈ tzL t' J ++ ("b3", vb) :: P, q ∈ LB vb t' J P := fun t' q hq => by
    rcases List.mem_append.1 hq with h | h
    · exact List.mem_cons_of_mem _ (List.mem_append_left _ h)
    · rcases List.mem_cons.1 h with rfl | h
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (List.mem_append_right _ h)
  have perm' : ∀ t' : TZ, ∀ q ∈ LB vb t' J P, q ∈ tzL t' J ++ ("b3", vb) :: P := fun t' q hq => by
    rcases List.mem_cons.1 hq with rfl | h
    · exact List.mem_append_right _ List.mem_cons_self
    · rcases List.mem_append.1 h with h | h
      · exact List.mem_append_left _ h
      · exact List.mem_append_right _ (List.mem_cons_of_mem _ h)
  have hfr0 : ∀ q ∈ ("b3", vb) :: P, q.1 ∉ tzNames0 := fun q hq => by
    rcases List.mem_cons.1 hq with rfl | h
    · exact b3_fr vb _ List.mem_cons_self
    · exact fr0 hfr q h
  exact frag_conseq (tz_finish0 o hfr0 (J := J) hcd hnp) (fun u h => runF_mono h (perm t) fun _ e => e)
    fun u h => runF_mono h (perm' (tzFinish t)) fun _ e => e

/-- **A digit of the time**: the part's number, at most 1000, and its digits' count. -/
theorem tz_digit (o : Oracle σ) (hfr : ∀ q ∈ P, q.1 ∉ tzNames)
    {t : TZ} {B : Nat} (hvb : vb = BitVec.ofNat 64 B) (hd : dig B) (hcv : t.cv ≤ 1000) :
    Frag o [.assign "cv" (eAdd (eMul (v "cv") (n 10)) (eSub (v "b3") (n 48))),
      ifs (eLt (n 1000) (v "cv")) [.assign "cv" (n 1000)], inc "cd"]
      (RunF s1 (LB vb t J P) F)
      (RunF s1 (LB vb { t with cv := min 1000 (t.cv * 10 + (B - 48)), cd := t.cd + 1 } J P) F) := by
  subst hvb
  have hd' : 48 ≤ B ∧ B ≤ 57 := hd
  let t1 : TZ := { t with cv := t.cv * 10 + (B - 48) }
  refine frag_append (xs := [_]) (set_to o rfl rfl (v := BitVec.ofNat 64 (t.cv * 10 + (B - 48)))
    (fun u h => ArticleScan.ev_madd (vals_lookup h.1.vals rfl) (vals_lookup h.1.vals rfl) hd'.1)
    fun u h => tz_set (b3_fr _) (fr0 hfr) (t' := t1) (by decide) h) ?_
  let t2 : TZ := { t with cv := min 1000 (t.cv * 10 + (B - 48)) }
  refine frag_append (xs := [_]) (tz_cond o (x := "cv") (by decide) rfl rfl (t := t1) (tT := t2)
    (b := decide (1000 < t.cv * 10 + (B - 48)))
    (fun u h => FramerCode.eval_lt (by decide) (by omega) rfl (ev_var (vals_lookup h.1.vals rfl)))
    (vx := BitVec.ofNat 64 1000) (fun _ _ => rfl)
    (fun hb u h => by
      have e : 1000 < t.cv * 10 + (B - 48) := of_decide_eq_true hb
      have h' := tz_set (b3_fr _) (fr0 hfr) (t' := { t with cv := 1000 }) (by decide) h
      show RunF s1 (LB (BitVec.ofNat 64 B) { t with cv := min 1000 (t.cv * 10 + (B - 48)) } J P) F u
      rw [Nat.min_eq_left (by omega)]; exact h')
    (fun hb => by
      have e : ¬1000 < t.cv * 10 + (B - 48) := of_decide_eq_false hb
      show { t with cv := min 1000 (t.cv * 10 + (B - 48)) } = { t with cv := t.cv * 10 + (B - 48) }
      rw [Nat.min_eq_right (by omega)])) ?_
  exact set_to o rfl rfl (v := BitVec.ofNat 64 (t.cd + 1)) (fun u h => ev_inc (vals_lookup h.1.vals rfl))
    fun u h => tz_set (b3_fr _) (fr0 hfr) (by decide) h

theorem gmtS_eq : gmtS =
    [ifs (eEq (v "zl") (n 0)) [ifs (ne (lowerE (v "b3")) (n 103)) [.assign "zg" (n 0)]],
     ifs (eEq (v "zl") (n 1)) [ifs (ne (lowerE (v "b3")) (n 109)) [.assign "zg" (n 0)]],
     ifs (eEq (v "zl") (n 2)) [ifs (ne (lowerE (v "b3")) (n 116)) [.assign "zg" (n 0)]]] := rfl

theorem ofNat_ne_iff {x y : Nat} (hx : x < 2 ^ 64) (hy : y < 2 ^ 64) :
    decide (BitVec.ofNat 64 x ≠ BitVec.ofNat 64 y) = decide (x ≠ y) := by
  apply decide_eq_decide.2
  constructor
  · intro h e; exact h (by rw [e])
  · intro h e; apply h
    have := congrArg BitVec.toNat e
    simpa [Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy] using this

/-- One letter of `GMT` checked: the flag cleared if the zone's byte at `k` is not it. -/
theorem tz_gmt1 (o : Oracle σ) (hfr : ∀ q ∈ P, q.1 ∉ tzNames)
    {t : TZ} {B : Nat} (hvb : vb = BitVec.ofNat 64 B) (hB : B < 256)
    (hzl : t.zl < 2 ^ 63) (k c : Nat) (hk : k < 3) (hc : c < 256) :
    Frag o [ifs (eEq (v "zl") (n k)) [ifs (ne (lowerE (v "b3")) (n c)) [.assign "zg" (n 0)]]]
      (RunF s1 (LB vb t J P) F)
      (RunF s1 (LB vb (if t.zl = k ∧ lowN B ≠ c then { t with zg := 0 } else t) J P) F) := by
  subst hvb
  have hlow : lowN B < 256 := by unfold lowN; split <;> omega
  have hlt : LowKK [ifs (ne (lowerE (v "b3")) (n c)) [.assign "zg" (n 0)]] := lowK_any _ (k := .skip) rfl
  have hz : ∀ {t' : TZ} u, RunF s1 (LB (BitVec.ofNat 64 B) t' J P) F u → t'.zl = t.zl →
      eval u (.cmp .equal (.var "zl") (.const (BitVec.ofNat 64 k))) = some (bw (decide (t.zl = k))) :=
    fun u h e => FramerCode.eval_eq (by omega) (by omega) (by rw [← e]; exact ev_var (vals_lookup h.1.vals rfl)) rfl
  by_cases h1 : t.zl = k
  · refine DN.News.ArticleScan.frag_ifT o rfl hlt lowKK_nil rfl rfl (runF_clock _ _ _)
      (fun u h => (hz u h rfl).trans (by rw [bw_t h1])) ?_
    exact tz_cond o (x := "zg") (by decide) rfl rfl (t := t) (b := decide (lowN B ≠ c))
      (fun u h => by
        rw [DN.News.AbnfLeaves.ne_eval (lowerE_eval hB (vals_lookup h.1.vals rfl)) rfl, ofNat_ne_iff (by omega)
          (by omega)]) (vx := BitVec.ofNat 64 0) (fun _ _ => rfl)
      (fun hb u h => by
        have e : lowN B ≠ c := of_decide_eq_true hb
        rw [if_pos ⟨h1, e⟩]; exact tz_set (b3_fr _) (fr0 hfr) (by decide) h)
      (fun hb => by
        have e : ¬lowN B ≠ c := of_decide_eq_false hb
        rw [if_neg fun h => e h.2])
  · refine DN.News.ArticleScan.frag_ifF o rfl hlt lowKK_nil rfl rfl (runF_clock _ _ _)
      (fun u h => (hz u h rfl).trans (by rw [bw_f h1])) (frag_nil o fun u h => ?_)
    rw [if_neg fun h => h1 h.1]; exact h

theorem zl_ite {c : Prop} [Decidable c] (t t' : TZ) (h : t'.zl = t.zl) : (if c then t' else t).zl = t.zl := by
  split <;> first | exact h | rfl

/-- **The letters of `GMT` checked.** -/
theorem tz_gmt (o : Oracle σ) (hfr : ∀ q ∈ P, q.1 ∉ tzNames)
    {t : TZ} {B : Nat} (hvb : vb = BitVec.ofNat 64 B) (hB : B < 256) (hzl : t.zl < 2 ^ 63) :
    Frag o gmtS (RunF s1 (LB vb t J P) F) (RunF s1 (LB vb (withZ t (zGmt (zfOf t) B)) J P) F) := by
  rw [gmtS_eq]
  let sa : TZ := if t.zl = 0 ∧ lowN B ≠ 103 then { t with zg := 0 } else t
  have hsa : sa.zl = t.zl := zl_ite (c := t.zl = 0 ∧ lowN B ≠ 103) t { t with zg := 0 } rfl
  let sb : TZ := if sa.zl = 1 ∧ lowN B ≠ 109 then { sa with zg := 0 } else sa
  have hsb : sb.zl = t.zl := (zl_ite (c := sa.zl = 1 ∧ lowN B ≠ 109) sa { sa with zg := 0 } rfl).trans hsa
  refine frag_append (xs := [_]) (tz_gmt1 o hfr hvb hB hzl 0 103 (by decide) (by decide)) ?_
  refine frag_append (xs := [_]) (tz_gmt1 o hfr (t := sa) hvb hB (by rw [hsa]; exact hzl) 1 109 (by decide)
    (by decide)) ?_
  refine frag_conseq (tz_gmt1 o hfr (t := sb) hvb hB (by rw [hsb]; exact hzl) 2 116 (by decide) (by decide))
    (fun _ h => h) fun u h => ?_
  have e : (if sb.zl = 2 ∧ lowN B ≠ 116 then { sb with zg := 0 } else sb) = withZ t (zGmt (zfOf t) B) := by
    simp only [sb, sa, withZ, zGmt, zfOf]
    obtain ⟨ph, np, cv, cd, hh, mi, se, bad, zl, z0, zd, zv, zg⟩ := t
    simp only at hzl ⊢
    rcases (by omega : zl = 0 ∨ zl = 1 ∨ zl = 2 ∨ 3 ≤ zl) with z | z | z | z
    · subst z; by_cases l : lowN B = 103 <;> simp [l]
    · subst z; by_cases l : lowN B = 109 <;> simp [l]
    · subst z; by_cases l : lowN B = 116 <;> simp [l]
    · simp [show zl ≠ 0 by omega, show zl ≠ 1 by omega, show zl ≠ 2 by omega]
  rw [e] at h; exact h

/-- **A byte of the zone**, the time ended first if still going on: `tzStep`'s second branch. -/
theorem tz_zone (o : Oracle σ) (hfr : ∀ q ∈ P, q.1 ∉ tzNames)
    {t : TZ} {B : Nat} (hvb : vb = BitVec.ofNat 64 B) (hB : B < 256)
    (hno : ¬(t.ph = 0 ∧ (dig B ∨ B = 58))) (hph : t.ph < 2 ^ 63) (hzl : t.zl < 2 ^ 62) (hcd : t.cd < 2 ^ 64)
    (hnp : t.np < 2 ^ 64) :
    Frag o zoneBody (RunF s1 (LB vb t J P) F) (RunF s1 (LB vb (tzStep t B) J P) F) := by
  let t1 : TZ := if t.ph = 0 then { tzFinish t with ph := 1 } else t
  have hstep : tzStep t B = withZ t1 (zStep (zfOf t1) B) := by unfold tzStep; rw [if_neg hno]
  rw [hstep]
  have h1zl : t1.zl = t.zl := zl_ite (c := t.ph = 0) t { tzFinish t with ph := 1 } rfl
  refine frag_append (xs := [_]) (M := RunF s1 (LB vb t1 J P) F) ?_ ?_
  · by_cases hp : t.ph = 0
    · refine DN.News.ArticleScan.frag_ifT o rfl (lowK_any _ (k := .skip) rfl) lowKK_nil rfl rfl (runF_clock _ _ _)
        (fun u h => (FramerCode.eval_eq (by omega) (by decide) (ev_var (vals_lookup h.1.vals rfl)) rfl).trans
          (by rw [bw_t hp])) ?_
      refine frag_append (tz_finish o hfr hcd hnp) ?_
      exact set_to o rfl rfl (v := BitVec.ofNat 64 1) (fun _ _ => rfl) fun u h => by
        simp only [t1, if_pos hp]; exact tz_set (b3_fr _) (fr0 hfr) (by decide) h
    · refine DN.News.ArticleScan.frag_ifF o rfl (lowK_any _ (k := .skip) rfl) lowKK_nil rfl rfl (runF_clock _ _ _)
        (fun u h => (FramerCode.eval_eq (by omega) (by decide) (ev_var (vals_lookup h.1.vals rfl)) rfl).trans
          (by rw [bw_f hp])) (frag_nil o fun u h => ?_)
      simp only [t1, if_neg hp]; exact h
  let t2 : TZ := withZ t1 (zFirst (zfOf t1) B)
  have h2zl : t2.zl = t.zl := (zFirst_zl _ _).trans h1zl
  refine frag_append (xs := [_]) (tz_cond o (x := "z0") (by decide) rfl rfl (t := t1) (tT := t2)
    (b := decide (t1.zl = 0)) (fun u h => FramerCode.eval_eq (by rw [h1zl]; omega) (by decide)
      (ev_var (vals_lookup h.1.vals rfl)) rfl) (vx := vb) (fun u h => ev_var (vals_lookup h.1.vals rfl))
    (fun hb u h => by
      have e : zFirst (zfOf t1) B = { zfOf t1 with z0 := B } := if_pos (of_decide_eq_true hb)
      simp only [t2, e]; subst hvb; exact tz_set (b3_fr _) (fr0 hfr) (by decide) h)
    (fun hb => by
      have e : zFirst (zfOf t1) B = zfOf t1 := if_neg (of_decide_eq_false hb)
      simp only [t2, e]; rfl)) ?_
  refine frag_append (tz_gmt o hfr (t := t2) hvb hB (by rw [h2zl]; omega)) ?_
  let t3 : TZ := withZ t2 (zGmt (zfOf t2) B)
  have h3zl : t3.zl = t.zl := (zGmt_zl _ _).trans h2zl
  have hdig : ∀ u, RunF s1 (LB vb t3 J P) F u →
      eval u (.op .and_ (FramerCode.leE (.const (BitVec.ofNat 64 48)) (.var "b3"))
        (FramerCode.leE (.var "b3") (.const (BitVec.ofNat 64 57)))) = some (bw (decide (dig B))) := fun u h => by
    subst hvb
    rw [FramerCode.eval_and (FramerCode.eval_le (by decide) (by omega) rfl (ev_var (vals_lookup h.1.vals rfl)))
      (FramerCode.eval_le (by omega) (by decide) (ev_var (vals_lookup h.1.vals rfl)) rfl)]
    unfold dig; simp
  refine frag_append (xs := [_]) (M := RunF s1 (LB vb (withZ t3 (zNum (zfOf t3) B)) J P) F) ?_ ?_
  · have hc : ∀ u, RunF s1 (LB vb t3 J P) F u →
        eval u (.op .and_ (FramerCode.leE (.const (BitVec.ofNat 64 1)) (.var "zl"))
          (FramerCode.leE (.var "zl") (.const (BitVec.ofNat 64 4)))) = some (bw (decide (1 ≤ t3.zl ∧ t3.zl ≤ 4))) :=
      fun u h => by
        rw [FramerCode.eval_and (FramerCode.eval_le (by decide) (by omega) rfl (ev_var (vals_lookup h.1.vals rfl)))
          (FramerCode.eval_le (by omega) (by decide) (ev_var (vals_lookup h.1.vals rfl)) rfl)]
        simp
    by_cases hz : 1 ≤ t3.zl ∧ t3.zl ≤ 4
    · refine DN.News.ArticleScan.frag_ifT o rfl (lowK_any _ (k := .skip) rfl) lowKK_nil rfl rfl (runF_clock _ _ _)
        (fun u h => (hc u h).trans (by rw [bw_t hz])) ?_
      by_cases hd : dig B
      · refine DN.News.ArticleScan.frag_ifT o rfl (lowK_any _ (k := .skip) rfl) (lowK_any _ (k := .skip) rfl) rfl rfl
          (runF_clock _ _ _) (fun u h => (hdig u h).trans (by rw [bw_t hd])) ?_
        have e : zNum (zfOf t3) B = { zfOf t3 with zv := t3.zv * 10 + (B - 48) } := by
          unfold zNum zDig; rw [if_pos (show 1 ≤ (zfOf t3).zl ∧ (zfOf t3).zl ≤ 4 from hz), if_pos hd]; rfl
        exact set_to o rfl rfl (v := BitVec.ofNat 64 (t3.zv * 10 + (B - 48)))
          (fun u h => ArticleScan.ev_madd (vals_lookup h.1.vals rfl) (by subst hvb; exact vals_lookup h.1.vals rfl)
            hd.1) fun u h => by rw [e]; exact tz_set (b3_fr _) (fr0 hfr) (by decide) h
      · refine DN.News.ArticleScan.frag_ifF o rfl (lowK_any _ (k := .skip) rfl) (lowK_any _ (k := .skip) rfl) rfl rfl
          (runF_clock _ _ _) (fun u h => (hdig u h).trans (by rw [bw_f hd])) ?_
        have e : zNum (zfOf t3) B = { zfOf t3 with zd := 0 } := by
          unfold zNum zDig; rw [if_pos (show 1 ≤ (zfOf t3).zl ∧ (zfOf t3).zl ≤ 4 from hz), if_neg hd]
        exact set_to o rfl rfl (v := BitVec.ofNat 64 0) (fun _ _ => rfl) fun u h => by
          rw [e]; exact tz_set (b3_fr _) (fr0 hfr) (by decide) h
    · refine DN.News.ArticleScan.frag_ifF o rfl (lowK_any _ (k := .skip) rfl) lowKK_nil rfl rfl (runF_clock _ _ _)
        (fun u h => (hc u h).trans (by rw [bw_f hz])) (frag_nil o fun u h => ?_)
      have e : zNum (zfOf t3) B = zfOf t3 := if_neg hz
      rw [e]; exact h
  exact set_to o rfl rfl (v := BitVec.ofNat 64 ((zNum (zfOf t3) B).zl + 1))
    (fun u h => ev_inc (vals_lookup h.1.vals rfl)) fun u h => tz_set (b3_fr _) (fr0 hfr) (by decide) h

/-- Bounds the loop's state keeps after `k` bytes. -/
def TB (t : TZ) (k : Nat) : Prop := t.ph ≤ 1 ∧ t.np ≤ k ∧ t.cd ≤ k ∧ t.zl ≤ k ∧ t.cv ≤ 1000

theorem tb_finish {t : TZ} {k : Nat} (h : TB t k) : TB (tzFinish t) (k + 1) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  exact ⟨h1, by simp [tzFinish]; omega, by simp [tzFinish], by simp [tzFinish]; omega, by simp [tzFinish]⟩

theorem tb_witness : TB tz0 0 := ⟨Nat.zero_le _, Nat.zero_le _, Nat.zero_le _, Nat.zero_le _, Nat.zero_le _⟩

theorem tb_step {t : TZ} {k : Nat} (h : TB t k) (b : Nat) : TB (tzStep t b) (k + 1) := by
  have hf := tb_finish h
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  have hz : ∀ t1 : TZ, t1.ph ≤ 1 → t1.np ≤ k + 1 → t1.cd ≤ k + 1 → t1.zl ≤ k → t1.cv ≤ 1000 →
      TB (withZ t1 (zStep (zfOf t1) b)) (k + 1) := fun t1 a1 a2 a3 a4 a5 =>
    ⟨a1, a2, a3, by show (zStep (zfOf t1) b).zl ≤ k + 1; rw [zStep_zl]; exact Nat.succ_le_succ a4, a5⟩
  unfold tzStep
  split
  · split
    · exact hf
    · exact ⟨h1, by dsimp only; omega, by dsimp only; omega, by dsimp only; omega, Nat.min_le_left _ _⟩
  · dsimp only
    split
    · obtain ⟨-, g2, -, -, -⟩ := hf
      exact hz _ (Nat.le_refl _) g2 (Nat.zero_le _) h4 (Nat.zero_le _)
    · exact hz _ h1 (by omega) (by omega) h4 h5

theorem fresh_b3 (hfr : ∀ q ∈ P, q.1 ∉ tzNames) (t : TZ) (J : Nat) : Fresh "b3" (tzL t J ++ P) = true := by
  unfold Fresh
  rw [List.all_append, Bool.and_eq_true]
  refine ⟨rfl, List.all_eq_true.2 fun q hq => ?_⟩
  have := hfr q hq
  simp only [bne_iff_ne, ne_eq]
  intro e; exact this (e ▸ by decide)

/-- **A turn of the loop over the time and the zone**: a gap passed, any other byte a step. -/
theorem tz_body (o : Oracle σ) (hfr : ∀ q ∈ P, q.1 ∉ tzNames)
    {A : Word} {a : Bytes} {M : Word → Word} (hin : InputAt M s1.memaddrs s1.be A a)
    (hla : P.lookup "a" = some A) {t : TZ} {k : Nat} (htb : TB t k) (hk : k ≤ artMax) (hJ : J < a.length)
    (hJM : J < artMax) :
    Frag o tzBody (RunF s1 (tzL t J ++ P) (· = M))
      (RunF s1 (tzL (if ArticleScan.gap a[J]! then t else tzStep t (a[J]!).toNat) (J + 1) ++ P) (· = M)) := by
  have hM := artMax_eq
  obtain ⟨h1, h2, h3, h4, h5⟩ := htb
  have hla2 : ∀ (t' : TZ) (J' : Nat), (tzL t' J' ++ P).lookup "a" = some A :=
    fun t' J' => by simp only [tzL]; exact hla
  generalize hB : (a[J]!).toNat = B
  have hBl : B < 256 := by rw [← hB]; exact (a[J]!).isLt
  have hg : ArticleScan.gap a[J]! = ArticleScan.gap (BitVec.ofNat 8 B) := by
    rw [← hB, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  refine frag_append (xs := [_, _]) (frag_append (xs := [_]) (kept_frag o (by decide) (runF_clock _ _ _)
    fun u h => ⟨J, vals_lookup h.1.vals rfl, by omega⟩) (runF_dec o rfl (fresh_b3 hfr t J) (v := BitVec.ofNat 64 B)
      fun u h => by
        rw [← hB]
        exact inByte_eval (input_run hin h) (vals_lookup h.1.vals (hla2 t J)) hJ (vals_lookup h.1.vals rfl))) ?_
  let t' : TZ := if ArticleScan.gap (BitVec.ofNat 8 B) then t else tzStep t B
  refine frag_append (xs := [_]) (M := RunF s1 (LB (BitVec.ofNat 64 B) t' J P) (· = M)) ?_ ?_
  · have hgv : ∀ u, RunF s1 (LB (BitVec.ofNat 64 B) t J P) (· = M) u →
        eval u (.cmp .equal (.op .or_ (.op .or_ (.cmp .equal (.var "b3") (.const (BitVec.ofNat 64 32)))
          (.cmp .equal (.var "b3") (.const (BitVec.ofNat 64 9)))) (.op .or_ (.cmp .equal (.var "b3")
            (.const (BitVec.ofNat 64 13))) (.cmp .equal (.var "b3") (.const (BitVec.ofNat 64 10)))))
          (.const (BitVec.ofNat 64 0))) = some (bw (!ArticleScan.gap (BitVec.ofNat 8 B))) := fun u h => by
      have hb3 : u.locals "b3" = some (BitVec.ofNat 64 (BitVec.ofNat 8 B).toNat) := by
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hBl]; exact vals_lookup h.1.vals rfl
      have := gap_eval hb3
      rw [FramerCode.eval_eq (x := if ArticleScan.gap (BitVec.ofNat 8 B) then 1 else 0) (y := 0) (by split <;> decide)
        (by decide) (by rw [this]; cases ArticleScan.gap (BitVec.ofNat 8 B) <;> rfl) rfl]
      cases ArticleScan.gap (BitVec.ofNat 8 B) <;> rfl
    by_cases hgp : ArticleScan.gap (BitVec.ofNat 8 B) = true
    · refine DN.News.ArticleScan.frag_ifF o rfl (lowK_any _ (k := .skip) rfl) lowKK_nil rfl rfl (runF_clock _ _ _)
        (fun u h => (hgv u h).trans (by rw [hgp]; rfl)) (frag_nil o fun u h => ?_)
      show RunF s1 (LB (BitVec.ofNat 64 B) (if ArticleScan.gap (BitVec.ofNat 8 B) then t else tzStep t B) J P) _ u
      rw [if_pos hgp]; exact h
    · refine DN.News.ArticleScan.frag_ifT o rfl (lowK_any _ (k := .skip) rfl) lowKK_nil rfl rfl (runF_clock _ _ _)
        (fun u h => (hgv u h).trans (by rw [Bool.eq_false_iff.2 hgp]; rfl)) ?_
      refine frag_conseq (P0' := RunF s1 (LB (BitVec.ofNat 64 B) (tzStep t B) J P) (· = M)) ?_ (fun _ h => h)
        fun u h => by
          show RunF s1 (LB (BitVec.ofNat 64 B) (if ArticleScan.gap (BitVec.ofNat 8 B) then t else tzStep t B) J P) _ u
          rw [if_neg hgp]; exact h
      have hcv : ∀ u, RunF s1 (LB (BitVec.ofNat 64 B) t J P) (· = M) u →
          eval u (.op .and_ (.cmp .equal (.var "ph") (.const (BitVec.ofNat 64 0)))
            (FramerCode.or2E (.op .and_ (FramerCode.leE (.const (BitVec.ofNat 64 48)) (.var "b3"))
              (FramerCode.leE (.var "b3") (.const (BitVec.ofNat 64 57))))
              (.cmp .equal (.var "b3") (.const (BitVec.ofNat 64 58))))) =
            some (bw (decide (t.ph = 0 ∧ (dig B ∨ B = 58)))) := fun u h => by
        rw [FramerCode.eval_and (FramerCode.eval_eq (by omega) (by decide) (ev_var (vals_lookup h.1.vals rfl)) rfl)
          (FramerCode.eval_or2 (FramerCode.eval_and (FramerCode.eval_le (by decide) (by omega) rfl
            (ev_var (vals_lookup h.1.vals rfl))) (FramerCode.eval_le (by omega) (by decide)
              (ev_var (vals_lookup h.1.vals rfl)) rfl))
            (FramerCode.eval_eq (by omega) (by decide) (ev_var (vals_lookup h.1.vals rfl)) rfl))]
        unfold dig; simp [Bool.decide_and, Bool.decide_or]
      by_cases hc : t.ph = 0 ∧ (dig B ∨ B = 58)
      · refine DN.News.ArticleScan.frag_ifT o rfl (lowK_any _ (k := .skip) rfl) (lowK_any _ (k := .skip) rfl) rfl
          rfl (runF_clock _ _ _) (fun u h => (hcv u h).trans (by rw [bw_t hc])) ?_
        by_cases h58 : B = 58
        · have he : tzStep t B = tzFinish t := by unfold tzStep; rw [if_pos hc, if_pos h58]
          rw [he]
          exact DN.News.ArticleScan.frag_ifT o rfl (lowK_any _ (k := .skip) rfl) (lowK_any _ (k := .skip) rfl) rfl
            rfl (runF_clock _ _ _) (fun u h => (FramerCode.eval_eq (by omega) (by decide)
              (ev_var (vals_lookup h.1.vals rfl)) rfl).trans (by rw [bw_t h58]))
            (tz_finish o hfr (by omega) (by omega))
        · have he : tzStep t B = { t with cv := min 1000 (t.cv * 10 + (B - 48)), cd := t.cd + 1 } := by
            unfold tzStep; rw [if_pos hc, if_neg h58]
          rw [he]
          exact DN.News.ArticleScan.frag_ifF o rfl (lowK_any _ (k := .skip) rfl) (lowK_any _ (k := .skip) rfl) rfl
            rfl (runF_clock _ _ _) (fun u h => (FramerCode.eval_eq (by omega) (by decide)
              (ev_var (vals_lookup h.1.vals rfl)) rfl).trans (by rw [bw_f h58]))
            (tz_digit o hfr rfl (hc.2.resolve_right h58) h5)
      · exact DN.News.ArticleScan.frag_ifF o rfl (lowK_any _ (k := .skip) rfl) (lowK_any _ (k := .skip) rfl) rfl
          rfl (runF_clock _ _ _) (fun u h => (hcv u h).trans (by rw [bw_f hc]))
          (tz_zone o hfr rfl hBl hc (by omega) (by omega) (by omega) (by omega))
  rw [hg]
  exact set_to o rfl rfl (v := BitVec.ofNat 64 (J + 1)) (fun u h => ev_inc (vals_lookup h.1.vals rfl))
    fun u h => runF_tz h (hP := fun q hq => mem_set hfr (by decide) _ (("b3", BitVec.ofNat 64 B) :: tzL t' J) q hq)

/-- The loop's state past the bytes `bs`, gaps left out. -/
def tzFold (bs : Bytes) : TZ := (bs.filter (fun b => !ArticleScan.gap b)).foldl (fun t b => tzStep t b.toNat) tz0

theorem tb_mono {t : TZ} {k k' : Nat} (h : TB t k) (hk : k ≤ k') : TB t k' := by
  obtain ⟨a1, a2, a3, a4, a5⟩ := h; exact ⟨a1, by omega, by omega, by omega, a5⟩

theorem tb_fold (bs : Bytes) : TB (tzFold bs) bs.length := by
  unfold tzFold
  have gen : ∀ (l : Bytes) (t : TZ) (k : Nat), TB t k →
      TB (l.foldl (fun t b => tzStep t b.toNat) t) (k + l.length) := by
    intro l; induction l with
    | nil => intro t k h; exact h
    | cons b l ih =>
      intro t k h
      have := ih _ _ (tb_step h b.toNat)
      rw [List.foldl_cons, List.length_cons]
      rwa [show k + (l.length + 1) = k + 1 + l.length by omega]
  exact tb_mono (gen _ tz0 0 tb_witness) (by have := List.length_filter_le (fun b => !ArticleScan.gap b) bs; omega)

/-- **The loop over the time and the zone** folds `tzStep` over the bytes but gaps. -/
theorem tz_loop (o : Oracle σ) (hfr : ∀ q ∈ P, q.1 ∉ tzNames)
    {A : Word} {a : Bytes} {M : Word → Word} (hin : InputAt M s1.memaddrs s1.be A a)
    (hla : P.lookup "a" = some A) {p3 c : Nat} (hlc : P.lookup "c" = some (BitVec.ofNat 64 c)) (hpc : p3 ≤ c)
    (hc : c ≤ a.length) (hcM : c ≤ artMax) :
    Frag o [.while (eLt (v "j") (v "c")) tzBody] (RunF s1 (tzL tz0 p3 ++ P) (· = M))
      (RunF s1 (tzL (tzFold (seg a p3 c)) c ++ P) (· = M)) := by
  have hM := artMax_eq
  have hlc' : ∀ (t : TZ) (J : Nat), (tzL t J ++ P).lookup "c" = some (BitVec.ofNat 64 c) :=
    fun t J => by simp only [tzL]; exact hlc
  let I : Assn σ := fun u => ∃ J, RunF s1 (tzL (tzFold (seg a p3 J)) J ++ P) (· = M) u ∧ p3 ≤ J ∧ J ≤ c
  have hIc : Safe.ClockFree I := fun u k ⟨J, h, hv⟩ => ⟨J, runF_clock _ _ _ u k h, hv⟩
  have hlow : LowKK tzBody := lowK_any _ (k := .skip) rfl
  have hcond : ∀ u J, RunF s1 (tzL (tzFold (seg a p3 J)) J ++ P) (· = M) u → J ≤ c →
      eval u (.cmp .less (.var "j") (.var "c")) = some (bw (decide (J < c))) := fun u J h hJ =>
    FramerCode.eval_lt (by omega) (by omega) (ev_var (vals_lookup h.1.vals rfl))
      (ev_var (vals_lookup h.1.vals (hlc' _ J)))
  refine frag_conseq (frag_while o rfl hlow hIc
    (fun u z w ⟨J, h, hv⟩ hz => by
      change z ∈ ["b3"] at hz
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hz; subst hz
      exact ⟨J, runF_restore h (fresh_b3 hfr _ J) w, hv⟩) (fun u ⟨J, h, hv⟩ => ⟨_, hcond u J h hv.2⟩) ?_)
    (fun u h => ⟨p3, by rw [DN.News.ArticleLines.seg_self]; exact h, Nat.le_refl _, hpc⟩) ?_
  · refine frag_conseq (P0 := fun u => ∃ J, (fun J u => RunF s1 (tzL (tzFold (seg a p3 J)) J ++ P) (· = M) u ∧
      p3 ≤ J ∧ J < c) J u) (frag_exists hlow fun J => ?_)
      (fun u ⟨⟨J, h, h1, h2⟩, h0⟩ => ⟨J, h, h1, by
        rw [hcond u J h h2] at h0; exact of_decide_eq_true (bw_ne0 h0)⟩) fun _ h => h
    refine frag_pure (p3 ≤ J ∧ J < c) (fun u h => h.2) hlow fun ⟨h1, h2⟩ => ?_
    have hJa : J < a.length := by omega
    have htb := tb_fold (seg a p3 J)
    rw [seg_length a h1 (by omega)] at htb
    refine frag_conseq (tz_body o hfr hin hla htb (by omega) hJa (by omega)) (fun u h => h.1) fun u h => ⟨J + 1, ?_,
      by omega, by omega⟩
    have e : tzFold (seg a p3 (J + 1)) =
        (if ArticleScan.gap a[J]! then tzFold (seg a p3 J) else tzStep (tzFold (seg a p3 J)) (a[J]!).toNat) := by
      unfold tzFold
      rw [seg_succ a h1 hJa, ← getElem!_pos a J hJa, List.filter_append, List.foldl_append]
      cases hg : ArticleScan.gap a[J]! <;>
        simp only [List.filter_cons, List.filter_nil, hg, Bool.not_false, Bool.not_true, Bool.false_eq_true, if_true,
          if_false, List.foldl_cons, List.foldl_nil]
    rw [e]; exact h
  · intro u ⟨⟨J, h, h1, h2⟩, h0⟩
    rw [hcond u J h h2] at h0
    have : J = c := by have := of_decide_eq_false (bw_eq0 h0); omega
    subst this; exact h

end tzbody

/-! ## The calls' words -/

/-- The words `artDate` and its callees write: the word's start, length and bytes, the number modulo 400, the value. -/
def scratch (A : Word) (x : Word) : Prop :=
  x = at_ A ArticleProg.xTokS ∨ x = at_ A ArticleProg.xTokLen ∨ x = at_ A ArticleProg.xNumMod ∨
    x = at_ A ArticleProg.xValue ∨ x = at_ A ArticleProg.xTok

/-- Every word but those as in `m0`. -/
def DFrame (A : Word) (m0 m : Word → Word) : Prop := ∀ x, ¬scratch A x → m x = m0 x

theorem dframe_refl (A : Word) (m : Word → Word) : DFrame A m m := fun _ _ => rfl

theorem dframe_trans {A : Word} {m0 m1 m2 : Word → Word} (h1 : DFrame A m0 m1) (h2 : DFrame A m1 m2) :
    DFrame A m0 m2 := fun x hx => (h2 x hx).trans (h1 x hx)

theorem dframe_upd {A : Word} {m0 : Word → Word} {x : Word} (hx : scratch A x) (w : Word) :
    DFrame A m0 (upd m0 x w) := fun _ hy => upd_ne _ fun e => hy (e ▸ hx)

theorem not_scratch_low {A : Word} {y : Nat} (hy : y < aSets) : ¬scratch A (at_ A y) := by
  have hX := X_lt; have hs := sets_le_X; have hT := xTok_eq; have hXv := X_val
  have ne : ∀ z : Nat, aSets ≤ z → z < 2 ^ 64 → at_ A y ≠ at_ A z := fun z h1 h2 =>
    DN.News.ScanRun.at_ne (by omega) h2 (by omega)
  intro h
  rcases h with h | h | h | h | h
  · exact ne _ (w_ge 19) (w_lt64 (by decide)) h
  · exact ne _ (w_ge 20) (w_lt64 (by decide)) h
  · exact ne _ (w_ge 25) (w_lt64 (by decide)) h
  · exact ne _ (w_ge 15) (w_lt64 (by decide)) h
  · exact ne _ (by omega) (by omega) h

theorem dframe_input {A : Word} (hA8 : A.toNat % 8 = 0) {a : Bytes} (hlen : a.length ≤ artMax)
    {m0 m : Word → Word} {dm : Word → Bool} {be : Bool} (hin : InputAt m0 dm be A a) (hf : DFrame A m0 m) :
    InputAt m dm be A a :=
  input_keep hA8 hlen hin fun _ hx => hf _ (not_scratch_low hx)

theorem dframe_low {A : Word} {m0 m : Word → Word} (hf : DFrame A m0 m) {y : Nat} (hy : y < aSets) :
    m (at_ A y) = m0 (at_ A y) := hf _ (not_scratch_low hy)

/-- The bytes put from `xTok`, at most eight, change only its word. -/
theorem putB_tok {A : Word} (hA8 : A.toNat % 8 = 0) (be : Bool) : ∀ (bs : Bytes) (m : Word → Word) (i : Nat),
    i + bs.length ≤ 8 → DFrame A m (putB m be A (ArticleProg.xTok + i) bs)
  | [], _, _, _ => dframe_refl _ _
  | b :: bs, m, i, h => by
    simp only [List.length_cons] at h
    show DFrame A m (putB (DN.Compiler.Bytes.putByte m be (at_ A (ArticleProg.xTok + i)) b) be A
      (ArticleProg.xTok + i + 1) bs)
    have h1 : DFrame A m (DN.Compiler.Bytes.putByte m be (at_ A (ArticleProg.xTok + i)) b) := fun x hx => by
      simp only [DN.Compiler.Bytes.putByte, DN.News.ScanRun.align_at hA8]
      rw [if_neg]
      intro e; apply hx; refine .inr (.inr (.inr (.inr ?_)))
      rw [e, show (ArticleProg.xTok + i) / 8 * 8 = ArticleProg.xTok by rw [xTok_eq]; omega]
    have h2 := putB_tok hA8 be bs (DN.Compiler.Bytes.putByte m be (at_ A (ArticleProg.xTok + i)) b) (i + 1) (by omega)
    rw [show ArticleProg.xTok + i + 1 = ArticleProg.xTok + (i + 1) by omega]
    exact dframe_trans h1 h2

/-- The memory after `artTok` from `P` to `E`: the next word's start, first eight bytes and length. -/
def tokMem (A : Word) (be : Bool) (a : Bytes) (P E : Nat) (m0 : Word → Word) : Word → Word :=
  upd (putB (upd m0 (at_ A ArticleProg.xTokS) (BitVec.ofNat 64 (wordStart a P E))) be A ArticleProg.xTok
    ((seg a (wordStart a P E) (wordEnd a (wordStart a P E) E)).take 8)) (at_ A ArticleProg.xTokLen)
    (BitVec.ofNat 64 (wordEnd a (wordStart a P E) E - wordStart a P E))

theorem tokMem_frame {A : Word} (hA8 : A.toNat % 8 = 0) (be : Bool) (a : Bytes) (P E : Nat) (m0 : Word → Word) :
    DFrame A m0 (tokMem A be a P E m0) := by
  unfold tokMem
  have h1 := putB_tok hA8 be ((seg a (wordStart a P E) (wordEnd a (wordStart a P E) E)).take 8)
    (upd m0 (at_ A ArticleProg.xTokS) (BitVec.ofNat 64 (wordStart a P E))) 0
    (by rw [Nat.zero_add, List.length_take]; exact Nat.min_le_left _ _)
  rw [Nat.add_zero] at h1
  exact dframe_trans (dframe_trans (dframe_upd (A := A) (m0 := m0) (.inl rfl) _) h1)
    (dframe_upd (.inr (.inl rfl)) _)

theorem broken_low : aBroken < aSets := Nat.lt_trans (by rw [aInput_eq]; decide) DN.News.AbnfMain.input_sets

theorem mem_artTok : gd ArticleProg.artTok ∈
    ArticleProg.functions ArticleSpec.spec (ArticleProg.entries ArticleSpec.spec) .none :=
  List.mem_append_right _ (List.mem_map.2 ⟨ArticleProg.artTok, by simp, rfl⟩)

/-- **A call of `artTok`**, the check after it passed: the word found from `P` ends at `we`; the memory `tokMem`. -/
theorem tokCall_frag (o : Oracle σ) {R : Ret} {A : Word} {s0 : PancakeState σ} (hA : Area ArticleProg.ofs A s0)
    (hD : ArtDom A s0.memaddrs) (hcode : ArtCode s0.code) {a : Bytes} (hlen : a.length ≤ artMax) {rt : String}
    (hra : rt ≠ "a") {l : List (String × Value)} (hla : l.lookup "a" = some A) (hrt : Fresh rt l = true)
    {m0 : Word → Word} (hin : InputAt m0 s0.memaddrs s0.be A a) (hb : m0 (at_ A aBroken) = 0) {x y : String}
    {P E ws we : Nat} (hPE : P ≤ E) (hE : E ≤ a.length) (hws : wordStart a P E = ws) (hwe : wordEnd a ws E = we)
    (hx : l.lookup x = some (BitVec.ofNat 64 P)) (hy : l.lookup y = some (BitVec.ofNat 64 E)) :
    FragR o R (guardS (.call rt "artTok" [v x, v y])) (RunF s0 l (· = m0))
      (RunF s0 ((rt, BitVec.ofNat 64 we) :: l) (· = tokMem A s0.be a P E m0)) := by
  subst hws; subst hwe
  refine fragR_conseq (gcall_frag o hA hcode hra (f := ArticleProg.artTok) mem_artTok (by decide)
    (args := [.var x, .var y]) rfl hla (vs := [BitVec.ofNat 64 P, BitVec.ofNat 64 E]) rfl
    (fun u h => by simp only [evalArgs, ev_var (vals_lookup h.1.vals hx), ev_var (vals_lookup h.1.vals hy)])
    (Rf := TokRet A s0.be a P E)
    (fun s1 hA1 _ hm hbe hloc hF => by
      have := artTok_ok o hA1 (by rw [hm]; exact hD) hlen (by rw [hF, hm, hbe]; exact hin) hPE hE
        ((hloc "p").trans rfl) ((hloc "e").trans rfl)
      rw [hbe] at this; exact this) hrt
    (G := fun v m => m = tokMem A s0.be a P E m0 ∧ v = BitVec.ofNat 64 (wordEnd a (wordStart a P E) E))
    (fun m m' v hm ⟨e1, e2⟩ => ⟨by rw [e2, hm]; rfl, e1⟩)
    fun v m h => by rw [h.1, dframe_low (tokMem_frame hA.hA _ _ _ _ _) broken_low]; exact hb) (fun u h => h)
    fun u ⟨v, h⟩ => ?_
  obtain ⟨hm, hv⟩ := h.2
  subst hv; exact ⟨h.1, hm⟩

/-! ## Witnesses: each premise can hold -/

theorem commaInv_witness : CommaInv [] 0 0 0 0 0 := ⟨Nat.le_refl _, Nat.le_refl _, rfl, .inl ⟨rfl, rfl⟩⟩

theorem dframe_witness : DFrame 0 (fun _ => 0) (fun _ => 0) := dframe_refl _ _

theorem scratch_witness : scratch 0 (at_ 0 ArticleProg.xValue) := .inr (.inr (.inr (.inl rfl)))

end DN.News.ArticleDateRun
