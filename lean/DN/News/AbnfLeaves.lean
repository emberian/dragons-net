-- SPDX-License-Identifier: AGPL-3.0-or-later
import DN.News.AbnfSets
import DN.News.AbnfMatch

/-!
# DN.News.AbnfLeaves

The grammar program's leaves, proven to do what they are named for (`leafClass_ok`, `leafText_ok`). If they return,
their slot holds the positions past a class byte or a string from another slot's. These are the ends of their term's
matches (`classAdd_iff`, `textAdd_iff`).
-/

namespace DN.News.AbnfLeaves

open DN.Compiler DN.Compiler.Wp DN.Compiler.WpRet DN.Compiler.Frag DN.News.AbnfProg DN.News.AbnfLayout
open DN.News.AbnfSets DN.News.FunRun
open DN.News.ScanRun (at_ at_add at_ne at_inj Vals vals_lookup vals_cons vals_set Fresh without lookup_head
  lookup_without)
open DN.News.FramerCode (bw ev_var bw_and)
open DN.News.AbnfMatch (bitStep fold_bits foldB Matches)

variable {σ : Type}

/-! ## A set's words and bytes -/

/-- Word `w` of the set `S`: its bits those of `S` from `64 * w`. -/
def wordOf (S : Nat → Bool) (w : Nat) : Word :=
  BitVec.ofNat 64 ((List.range 64).foldl (bitStep fun j => S (64 * w + j)) 0)

theorem wordOf_bit (S : Nat → Bool) (w : Nat) {j : Nat} (hj : j < 64) : (wordOf S w).getLsbD j = S (64 * w + j) := by
  rw [wordOf, BitVec.getLsbD_ofNat, (fold_bits _ 64).2 j]; simp [hj]

/-- A slot's word is its set's. -/
theorem slot_wordOf {m : Word → Word} {A : Word} {k : Nat} {S : Nat → Bool} (h : SetAt m A k S) {w : Nat}
    (hw : w < setWords) : m (slotW A k (2 + w)) = wordOf S w :=
  BitVec.eq_of_getLsbD_eq fun j hj => by rw [h.bits w hw j hj, wordOf_bit S w hj]

/-- The masks of a word's eight bytes. -/
def Masks (m : Word → Word) (A : Word) : Prop :=
  ∀ b, b < 8 → m (at_ A (aMask + 8 * b)) = BitVec.ofNat 64 (255 * 2 ^ (8 * b))

theorem mask_bit {b j : Nat} (hj : j < 64) :
    (BitVec.ofNat 64 (255 * 2 ^ (8 * b))).getLsbD j = decide (8 * b ≤ j ∧ j < 8 * b + 8) := by
  rw [BitVec.getLsbD_ofNat, Nat.testBit_mul_two_pow, show (255 : Nat) = 2 ^ 8 - 1 from rfl,
    Nat.testBit_two_pow_sub_one]
  by_cases h : 8 * b ≤ j <;> simp [h, hj] <;> omega

/-- A byte of a word that its mask finds empty holds no bit. -/
theorem byte_empty {W : Word} {b : Nat} (h : W &&& BitVec.ofNat 64 (255 * 2 ^ (8 * b)) = 0) {j : Nat}
    (h1 : 8 * b ≤ j) (h2 : j < 8 * b + 8) (hj : j < 64) : W.getLsbD j = false := by
  have := congrArg (fun x => x.getLsbD j) h
  simp only [BitVec.getLsbD_and, mask_bit hj] at this
  simpa [h1, h2] using this

/-- A word not zero, as `ne` tells it. -/
theorem ne0_eval {u : PancakeState σ} {E : PancakeExp} {W : Word} (hE : eval u E = some W) :
    eval u (.cmp .equal (.cmp .equal E (.const (BitVec.ofNat 64 0))) (.const (BitVec.ofNat 64 0))) =
      some (bw (decide (W ≠ 0))) := by
  simp only [eval, hE]
  by_cases h : W = 0 <;> simp [h, bw]

/-! ## Each position of a set -/

/-- The names `eachPos` declares. -/
def loopNames : List String := ["lo", "hi", "w", "wd", "m", "j", "x"]

/-- What `eachPos` reads, and how a position not taken leaves `L` and `F`. These are the locals and memory after
positions below `X`. -/
structure Each (A : Word) (ks nn : Nat) (S : Nat → Bool) (L : Nat → List (String × Value))
    (F : Nat → (Word → Word) → Prop) : Prop where
  p : ∀ X, (L X).lookup "p" = some (at_ A (off ks))
  len : ∀ X, (L X).lookup "nn" = some (BitVec.ofNat 64 nn)
  a : ∀ X, (L X).lookup "a" = some A
  fresh : ∀ X, ∀ y ∈ loopNames, Fresh y (L X) = true
  mem : ∀ X m, F X m → SetAt m A ks S ∧ Masks m A ∧ Pows m A
  skip : ∀ X, (S X = false ∨ nn ≤ X) → L (X + 1) = L X ∧ ∀ m, F X m → F (X + 1) m

theorem Each.skipN {A : Word} {ks nn : Nat} {S : Nat → Bool} {L : Nat → List (String × Value)}
    {F : Nat → (Word → Word) → Prop} (h : Each A ks nn S L F) :
    ∀ k X, (∀ Y, X ≤ Y → Y < X + k → S Y = false ∨ nn ≤ Y) → L (X + k) = L X ∧ ∀ m, F X m → F (X + k) m
  | 0, X, _ => ⟨rfl, fun _ h => h⟩
  | k + 1, X, hy => by
    obtain ⟨e1, f1⟩ := h.skipN k X fun Y h1 h2 => hy Y h1 (by omega)
    obtain ⟨e2, f2⟩ := h.skip (X + k) (hy (X + k) (by omega) (by omega))
    exact ⟨by rw [← Nat.add_assoc, e2, e1], fun m hm => f2 m (f1 m hm)⟩

/-! ### Lists of locals -/

theorem fresh_app {y : String} {l1 l2 : List (String × Value)} (h1 : Fresh y l1 = true) (h2 : Fresh y l2 = true) :
    Fresh y (l1 ++ l2) = true := by
  simp only [Fresh, List.all_append, Bool.and_eq_true] at h1 h2 ⊢; exact ⟨h1, h2⟩

theorem lookup_app_fresh {y : String} : ∀ {l1 : List (String × Value)} (l2 : List (String × Value)),
    Fresh y l1 = true → (l1 ++ l2).lookup y = l2.lookup y
  | [], _, _ => rfl
  | (a, b) :: l1, l2, h => by
    have h1 := ScanRun.fresh_ne h (a, b) (List.mem_cons_self ..)
    have h2 : Fresh y l1 = true := by simp only [Fresh, List.all_cons, Bool.and_eq_true] at h ⊢; exact h.2
    rw [List.cons_append, ScanRun.lookup_cons_ne (Ne.symm h1), lookup_app_fresh l2 h2]

theorem lookup_app_some {y : String} {v : Value} {l1 : List (String × Value)} (l2 : List (String × Value))
    (h : l1.lookup y = some v) : (l1 ++ l2).lookup y = some v := by
  rw [List.lookup_append, h]; rfl

/-- A name no loop declares is fresh in the loops' locals. -/
theorem fresh_loop {lv : List (String × Value)} (hlv : ∀ q ∈ lv, q.1 ∈ loopNames) {y : String}
    (hy : y ∉ loopNames) : Fresh y lv = true :=
  List.all_eq_true.2 fun q hq => by
    have := hlv q hq
    simp only [bne_iff_ne, ne_eq]; exact fun e => hy (e ▸ this)

/-! ### The bits of a byte -/

theorem m8_eval {u : PancakeState σ} {M : Nat} (hm : u.locals "m" = some (BitVec.ofNat 64 M)) :
    eval u (.op .add (.mul (.var "m") (.const (BitVec.ofNat 64 8))) (.const (BitVec.ofNat 64 8))) =
      some (BitVec.ofNat 64 (8 * M + 8)) := by
  simp only [eval, hm]
  rw [← BitVec.ofNat_mul, ← BitVec.ofNat_add, Nat.mul_comm]

/-- The loops' bodies lower before anything when the body at each position does. -/
theorem lowKK_bitsBody {body : List Syntax.PStmt} (h : LowKK body) :
    LowKK [.ite (ne (Syntax.eAnd (Syntax.v "wd") (pow (Syntax.v "j"))) (Syntax.n 0)) (posAt body) [], inc "j"] :=
  lowKK_append (xs := [_]) (lowKK_ite rfl (lowKK_append (xs := [_]) (lowKK_dec rfl)
    (lowKK_ite rfl h (lowK_any _ (k := .skip) rfl))) (lowK_any _ (k := .skip) rfl)) (lowK_any _ (k := .skip) rfl)

theorem lowKK_bytesBody {body : List Syntax.PStmt} (h : LowKK body) :
    LowKK [.ite (ne (Syntax.eAnd (Syntax.v "wd") (mask (Syntax.v "m"))) (Syntax.n 0))
      [.dec "j" (Syntax.eMul (Syntax.v "m") (Syntax.n 8)), bitsLoop body] [], inc "m"] :=
  lowKK_append (xs := [_]) (lowKK_ite rfl (lowKK_append (xs := [_]) (lowKK_dec rfl)
    (lowKK_while rfl (lowKK_bitsBody h))) (lowK_any _ (k := .skip) rfl)) (lowK_any _ (k := .skip) rfl)

theorem lowKK_wordsBody {body : List Syntax.PStmt} (h : LowKK body) :
    LowKK [.dec "wd" (.loadw 1 (bitWord "p" (Syntax.v "w"))),
      .ite (ne (Syntax.v "wd") (Syntax.n 0)) [.dec "m" (Syntax.n 0), bytesLoop body] [], inc "w"] :=
  lowKK_append (xs := [_]) (lowKK_dec rfl) (lowKK_append (xs := [_]) (lowKK_ite rfl (lowKK_append (xs := [_])
    (lowKK_dec rfl) (lowKK_while rfl (lowKK_bytesBody h))) (lowK_any _ (k := .skip) rfl)) (lowK_any _ (k := .skip) rfl))

theorem lowKK_eachPos {body : List Syntax.PStmt} (h : LowKK body) : LowKK (eachPos body) :=
  lowKK_append (lowK_any _ (k := .skip) rfl) (lowKK_append (xs := [_]) (lowKK_dec rfl)
    (lowKK_while rfl (lowKK_wordsBody h)))

/-- **The bits of a byte** (`bitsLoop body`): bits `8 * M` to `8 * M + 8` of word `W` of the set. Each set bit is a
position, taken by `body` below `nn`. -/
theorem bitsLoop_frag (o : Oracle σ) {ofs : Nat} {A : Word} {s0 : PancakeState σ} (hA : Area ofs A s0)
    {ks nn : Nat} {S : Nat → Bool} {L : Nat → List (String × Value)} {F : Nat → (Word → Word) → Prop}
    (he : Each A ks nn S L F) (hnn : nn ≤ inputMax) {body : List Syntax.PStmt} (hlow : LowKK body)
    (hdecl : ∀ X, ∀ y ∈ declared body, y ∉ loopNames ∧ Fresh y (L X) = true)
    (hbody : ∀ X (lv : List (String × Value)), (∀ q ∈ lv, q.1 ∈ loopNames) → S X = true → X < nn →
      Frag o body (RunF s0 (("x", BitVec.ofNat 64 X) :: lv ++ L X) (F X))
        (RunF s0 (("x", BitVec.ofNat 64 X) :: lv ++ L (X + 1)) (F (X + 1))))
    {W M : Nat} (hW : W < setWords) (hM : M < 8) {lv : List (String × Value)} (hlv : ∀ q ∈ lv, q.1 ∈ loopNames)
    (hwd : lv.lookup "wd" = some (wordOf S W)) (hw : lv.lookup "w" = some (BitVec.ofNat 64 W))
    (hm : lv.lookup "m" = some (BitVec.ofNat 64 M)) (hj : Fresh "j" lv = true) (hx : Fresh "x" lv = true) :
    Frag o [bitsLoop body]
      (RunF s0 (("j", BitVec.ofNat 64 (8 * M)) :: lv ++ L (64 * W + 8 * M)) (F (64 * W + 8 * M)))
      (RunF s0 (("j", BitVec.ofNat 64 (8 * M + 8)) :: lv ++ L (64 * W + 8 * M + 8)) (F (64 * W + 8 * M + 8))) := by
  rw [setWords_eq] at hW
  have hI := inputMax_eq
  let lj (J : Nat) : List (String × Value) := ("j", BitVec.ofNat 64 J) :: lv ++ L (64 * W + J)
  let I (J : Nat) : Assn σ := fun u => RunF s0 (lj J) (F (64 * W + J)) u ∧ J ≤ 8 * M + 8
  have hIc : ∀ J, Safe.ClockFree (I J) := fun J s k h => ⟨runF_clock _ _ _ s k h.1, h.2⟩
  -- lookups in a list of the loop
  have lkL : ∀ (pre : List (String × Value)), (∀ q ∈ pre, q.1 ∈ loopNames) → ∀ X y, y ∉ loopNames →
      (pre ++ L X).lookup y = (L X).lookup y := fun pre hp X y hy => lookup_app_fresh _ (fresh_loop hp hy)
  have hjlv' : ∀ J, ∀ q ∈ ("j", BitVec.ofNat 64 J) :: lv, q.1 ∈ loopNames := fun J q hq => by
    simp only [List.mem_cons] at hq; rcases hq with rfl | hq
    · simp [loopNames]
    · exact hlv q hq
  -- the list of the loop at `J`, with `x` on it
  have look : ∀ J u, RunF s0 (lj J) (F (64 * W + J)) u →
      u.locals "j" = some (BitVec.ofNat 64 J) ∧ u.locals "m" = some (BitVec.ofNat 64 M) ∧
      u.locals "wd" = some (wordOf S W) ∧ u.locals "w" = some (BitVec.ofNat 64 W) ∧
      u.locals "a" = some A ∧ u.locals "nn" = some (BitVec.ofNat 64 nn) := fun J u h => by
    dsimp only [lj] at h
    refine ⟨vals_lookup h.1.vals (lookup_head _ _ _), ?_, ?_, ?_, ?_, ?_⟩
    · exact vals_lookup h.1.vals (by
        rw [List.cons_append, ScanRun.lookup_cons_ne (by decide)]; exact lookup_app_some _ hm)
    · exact vals_lookup h.1.vals (by
        rw [List.cons_append, ScanRun.lookup_cons_ne (by decide)]; exact lookup_app_some _ hwd)
    · exact vals_lookup h.1.vals (by
        rw [List.cons_append, ScanRun.lookup_cons_ne (by decide)]; exact lookup_app_some _ hw)
    · exact vals_lookup h.1.vals (by
        rw [lkL _ (hjlv' J) _ _ (by simp [loopNames])]; exact he.a _)
    · exact vals_lookup h.1.vals (by
        rw [lkL _ (hjlv' J) _ _ (by simp [loopNames])]; exact he.len _)
  refine frag_conseq (frag_count o rfl
    (lowKK_bitsBody hlow)
    hIc (fun J => noDecl (P' := I J) _ rfl) (g := fun J => decide (J < 8 * M + 8))
    (fun J u h => by
      obtain ⟨hj', hm', -⟩ := look J u h.1
      exact FramerCode.eval_lt (by omega) (by omega) (ev_var hj') (m8_eval hm'))
    (fun J hg => ?_) (8 * M)) (fun u h => ⟨h, by omega⟩) fun u ⟨J, h, hg⟩ => ?_
  rotate_left
  · have : J = 8 * M + 8 := by have := h.2; simp at hg; omega
    subst this
    have h1 := h.1
    dsimp only [lj] at h1
    rw [show 64 * W + (8 * M + 8) = 64 * W + 8 * M + 8 by omega] at h1
    exact h1
  have hJ : J < 8 * M + 8 := of_decide_eq_true hg
  let X := 64 * W + J
  have hX : X < 64 * 1026 := by omega
  -- the bit's test
  have hbit : ∀ u, I J u → eval u (.cmp .equal (.cmp .equal (.op .and_ (.var "wd") (.loadWord (.op .add
      (.op .add (.var "a") (.const (BitVec.ofNat 64 aPow))) (.mul (.var "j") (.const (BitVec.ofNat 64 8))))))
      (.const (BitVec.ofNat 64 0))) (.const (BitVec.ofNat 64 0))) = some (bw (S X)) := fun u h => by
    obtain ⟨hj', -, hwd', -, ha', -⟩ := look J u h.1
    have hp := pow_eval rfl hA h.1.1.memaddrs (he.mem _ _ (h.1.2)).2.2 ha' (by omega) hj'
    have hne : BitVec.twoPow 64 J ≠ 0 := fun e => by
      have := congrArg (fun x => x.getLsbD J) e
      simp only [BitVec.getLsbD_twoPow] at this; simp at this; omega
    rw [ne0_eval (ev_and (ev_var hwd') hp), BitVec.and_twoPow, ← wordOf_bit S W (show J < 64 by omega)]
    cases (wordOf S W).getLsbD J <;> simp [bw] <;> simpa using hne
  let Mid : Assn σ := RunF s0 (("j", BitVec.ofNat 64 J) :: lv ++ L (X + 1)) (F (X + 1))
  have hx' : ∀ Y, Fresh "x" (("j", BitVec.ofNat 64 J) :: lv ++ L Y) = true := fun Y =>
    ScanRun.fresh_cons (by decide) (fresh_app hx (he.fresh Y "x" (by simp [loopNames])))
  refine frag_append (xs := [_]) (M := Mid) (frag_ite o rfl (runF_clock _ _ _) (fun u h => ⟨_, hbit u h⟩) ?_
    (fun u y v h hy => by
      simp [declared, posAt] at hy
      subst hy; exact runF_restore h (hx' _) v) ?_ (noDecl _ rfl)) ?_
  · -- a set bit: position `X`, taken when below `nn`
    have hlowP : LowKK (posAt body) :=
      lowKK_append (xs := [_]) (lowKK_dec rfl) (lowKK_ite rfl hlow (lowK_any _ (k := .skip) rfl))
    by_cases hS0 : S X = false
    · exact frag_unsat hlowP fun u ⟨h, hne⟩ => hne (by rw [hbit u h, hS0]; rfl)
    have hS : S X = true := by simpa using hS0
    refine frag_conseq (P0 := RunF s0 (lj J) (F X))
      (P0' := RunF s0 (("x", BitVec.ofNat 64 X) :: ("j", BitVec.ofNat 64 J) :: lv ++ L (X + 1)) (F (X + 1))) ?_
      (fun u h => h.1.1) fun u h =>
      runF_mono h (fun q hq => List.mem_cons_of_mem _ hq) fun _ e => e
    refine frag_append (xs := [_]) (runF_dec o rfl (hx' _) (v := BitVec.ofNat 64 X) fun u h => ?_) ?_
    · obtain ⟨hj', -, -, hw', -, -⟩ := look J u h
      simp only [eval, hw', hj']
      rw [← BitVec.ofNat_mul, ← BitVec.ofNat_add, Nat.mul_comm]
    have hfrX : ∀ Y, ∀ y ∈ declared body,
        Fresh y (("x", BitVec.ofNat 64 X) :: ("j", BitVec.ofNat 64 J) :: lv ++ L Y) = true := fun Y y hy => by
      obtain ⟨hn, hf⟩ := hdecl Y y hy
      exact ScanRun.fresh_cons (fun e => hn (e ▸ by simp [loopNames]))
        (ScanRun.fresh_cons (fun e => hn (e ▸ by simp [loopNames])) (fresh_app (fresh_loop hlv hn) hf))
    have hev : ∀ u, RunF s0 (("x", BitVec.ofNat 64 X) :: lj J) (F X) u →
        eval u (.cmp .less (.var "x") (.var "nn")) = some (bw (decide (X < nn))) := fun u h => by
      obtain ⟨-, -, -, -, -, hn'⟩ := look J u (runF_mono h (fun q hq => List.mem_cons_of_mem _ hq) fun _ e => e)
      exact FramerCode.eval_lt (by omega) (by omega) (ev_var (vals_lookup h.1.vals (lookup_head _ _ _))) (ev_var hn')
    by_cases hlt : X < nn
    · refine frag_ite o rfl (runF_clock _ _ _) (fun u h => ⟨_, hev u h⟩)
        (frag_conseq (hbody X (("j", BitVec.ofNat 64 J) :: lv) (hjlv' J) hS hlt) (fun u h => h.1) fun _ h => h)
        (fun u y v h hy => runF_restore h (hfrX _ y hy) v)
        (frag_unsat (lowK_any _ (k := .skip) rfl) fun u ⟨h, h0⟩ => by rw [hev u h] at h0; simp [bw, hlt] at h0)
        (noDecl _ rfl)
    · obtain ⟨eL, eF⟩ := he.skip X (.inr (by omega))
      refine frag_ite o rfl (runF_clock _ _ _) (fun u h => ⟨_, hev u h⟩)
        (frag_unsat hlow fun u ⟨h, h0⟩ => h0 (by rw [hev u h]; simp [bw, hlt]))
        (fun u y v h hy => runF_restore h (hfrX _ y hy) v)
        (frag_nil o fun u ⟨h, _⟩ => ⟨by rw [eL]; exact h.1, eF _ h.2⟩) (noDecl _ rfl)
  · -- a bit not set: nothing
    refine frag_nil o fun u ⟨h, h0⟩ => ?_
    rw [hbit u h] at h0
    have hS : S X = false := by cases hs : S X <;> simp [hs, bw] at h0 ⊢
    obtain ⟨eL, eF⟩ := he.skip X (.inl hS)
    exact ⟨by rw [eL]; exact h.1.1, eF _ h.1.2⟩
  · -- the next bit
    refine frag_conseq (runF_set o rfl (lookup_head _ _ _) (v := BitVec.ofNat 64 (J + 1)) fun u h => ?_)
      (fun u h => h) fun u h => ⟨?_, by omega⟩
    · simp only [eval, vals_lookup h.1.vals (lookup_head _ _ _), BitVec.ofNat_add]
    · dsimp only [lj]
      rw [show 64 * W + (J + 1) = X + 1 by omega]
      refine runF_mono h (fun q hq => ?_) fun _ e => e
      simp only [List.cons_append, List.mem_cons] at hq
      rcases hq with rfl | hq
      · exact List.mem_cons_self ..
      · refine List.mem_cons_of_mem _ (mem_without (List.mem_cons_of_mem _ hq) ?_)
        rcases List.mem_append.1 hq with hq | hq
        · exact ScanRun.fresh_ne hj q hq
        · exact ScanRun.fresh_ne (he.fresh _ "j" (by simp [loopNames])) q hq

theorem aMask_eq : aMask = 66408 := rfl

/-- The mask of byte `b`, read from the table, `b` in `x`. -/
theorem mask_eval {E : PancakeExp} {x : String} (he : Lower.lowerExp (mask (Syntax.v x)) = some E) {ofs : Nat}
    {A : Word} {s0 u : PancakeState σ} (hA : Area ofs A s0) (hm : u.memaddrs = s0.memaddrs) (hM : Masks u.memory A)
    (ha : u.locals "a" = some A) {b : Nat} (hb : b < 8) (hx : u.locals x = some (BitVec.ofNat 64 b)) :
    eval u E = some (BitVec.ofNat 64 (255 * 2 ^ (8 * b))) := by
  cases he
  have hl : aMask + 8 * 8 ≤ aSets := aClass_le
  have e : eval u (.op .add (.op .add (.var "a") (.const (BitVec.ofNat 64 aMask))) (.mul (.var x)
      (.const (BitVec.ofNat 64 8)))) = some (at_ A (aMask + 8 * b)) := by
    simp only [eval, ha, hx]
    rw [← BitVec.ofNat_mul]
    show some (at_ A aMask + BitVec.ofNat 64 (b * 8)) = some (at_ A (aMask + 8 * b))
    rw [at_add]
    exact congrArg (fun y => some (at_ A y)) (by omega)
  rw [load_eval hA hm (y := aMask + 8 * b) (by omega) (by rw [aMask_eq]; omega) e, hM b hb]

/-! ### The bytes of a word -/

/-- **The bytes of a word** (`bytesLoop body`): the eight bytes of word `W` of the set. Those holding a bit are read bit
by bit, the rest skipped. -/
theorem bytesLoop_frag (o : Oracle σ) {ofs : Nat} {A : Word} {s0 : PancakeState σ} (hA : Area ofs A s0)
    {ks nn : Nat} {S : Nat → Bool} {L : Nat → List (String × Value)} {F : Nat → (Word → Word) → Prop}
    (he : Each A ks nn S L F) (hnn : nn ≤ inputMax) {body : List Syntax.PStmt} (hlow : LowKK body)
    (hdecl : ∀ X, ∀ y ∈ declared body, y ∉ loopNames ∧ Fresh y (L X) = true)
    (hbody : ∀ X (lv : List (String × Value)), (∀ q ∈ lv, q.1 ∈ loopNames) → S X = true → X < nn →
      Frag o body (RunF s0 (("x", BitVec.ofNat 64 X) :: lv ++ L X) (F X))
        (RunF s0 (("x", BitVec.ofNat 64 X) :: lv ++ L (X + 1)) (F (X + 1))))
    {W : Nat} (hW : W < setWords) {lv : List (String × Value)} (hlv : ∀ q ∈ lv, q.1 ∈ loopNames)
    (hwd : lv.lookup "wd" = some (wordOf S W)) (hw : lv.lookup "w" = some (BitVec.ofNat 64 W))
    (hm : Fresh "m" lv = true) (hj : Fresh "j" lv = true) (hx : Fresh "x" lv = true) :
    Frag o [bytesLoop body]
      (RunF s0 (("m", BitVec.ofNat 64 0) :: lv ++ L (64 * W)) (F (64 * W)))
      (RunF s0 (("m", BitVec.ofNat 64 8) :: lv ++ L (64 * W + 64)) (F (64 * W + 64))) := by
  let lm (M : Nat) : List (String × Value) := ("m", BitVec.ofNat 64 M) :: lv ++ L (64 * W + 8 * M)
  let I (M : Nat) : Assn σ := fun u => RunF s0 (lm M) (F (64 * W + 8 * M)) u ∧ M ≤ 8
  have hIc : ∀ M, Safe.ClockFree (I M) := fun M s k h => ⟨runF_clock _ _ _ s k h.1, h.2⟩
  have hmlv : ∀ M, ∀ q ∈ ("m", BitVec.ofNat 64 M) :: lv, q.1 ∈ loopNames := fun M q hq => by
    simp only [List.mem_cons] at hq; rcases hq with rfl | hq
    · simp [loopNames]
    · exact hlv q hq
  have look : ∀ M u, RunF s0 (lm M) (F (64 * W + 8 * M)) u →
      u.locals "m" = some (BitVec.ofNat 64 M) ∧ u.locals "wd" = some (wordOf S W) ∧ u.locals "a" = some A := by
    intro M u h
    dsimp only [lm] at h
    refine ⟨vals_lookup h.1.vals (lookup_head _ _ _), ?_, ?_⟩
    · exact vals_lookup h.1.vals (by
        rw [List.cons_append, ScanRun.lookup_cons_ne (by decide)]; exact lookup_app_some _ hwd)
    · exact vals_lookup h.1.vals (by rw [lookup_app_fresh _ (fresh_loop (hmlv M) (by simp [loopNames]))]; exact he.a _)
  refine frag_conseq (frag_count o rfl
    (lowKK_bytesBody hlow)
    hIc (fun M => noDecl (P' := I M) _ rfl) (g := fun M => decide (M < 8))
    (fun M u h => FramerCode.eval_lt (by omega) (by decide) (ev_var (look M u h.1).1) rfl) (fun M hg => ?_) 0)
    (fun u h => ⟨h, by omega⟩) fun u ⟨M, h, hg⟩ => ?_
  rotate_left
  · have : M = 8 := by have := h.2; simp at hg; omega
    subst this
    exact h.1
  have hM : M < 8 := of_decide_eq_true hg
  let X := 64 * W + 8 * M
  have hbyte : ∀ u, I M u → eval u (.cmp .equal (.cmp .equal (.op .and_ (.var "wd") (.loadWord (.op .add
      (.op .add (.var "a") (.const (BitVec.ofNat 64 aMask))) (.mul (.var "m") (.const (BitVec.ofNat 64 8))))))
      (.const (BitVec.ofNat 64 0))) (.const (BitVec.ofNat 64 0))) =
        some (bw (decide (wordOf S W &&& BitVec.ofNat 64 (255 * 2 ^ (8 * M)) ≠ 0))) := fun u h => by
    obtain ⟨hm', hwd', ha'⟩ := look M u h.1
    exact ne0_eval (ev_and (ev_var hwd') (mask_eval rfl hA h.1.1.memaddrs (he.mem _ _ h.1.2).2.1 ha' hM hm'))
  let Mid : Assn σ := RunF s0 (("m", BitVec.ofNat 64 M) :: lv ++ L (X + 8)) (F (X + 8))
  have hjm : ∀ Y, Fresh "j" (("m", BitVec.ofNat 64 M) :: lv ++ L Y) = true := fun Y =>
    ScanRun.fresh_cons (by decide) (fresh_app hj (he.fresh Y "j" (by simp [loopNames])))
  refine frag_append (xs := [_]) (M := Mid) (frag_ite o rfl (runF_clock _ _ _) (fun u h => ⟨_, hbyte u h⟩) ?_
    (fun u y v h hy => by
      simp [declared, bitsLoop] at hy
      subst hy; exact runF_restore h (hjm _) v) ?_ (noDecl _ rfl)) ?_
  · -- a byte holding a bit: its bits
    refine frag_conseq (P0 := RunF s0 (lm M) (F X)) (P0' := RunF s0 (("j", BitVec.ofNat 64 (8 * M + 8)) ::
      ("m", BitVec.ofNat 64 M) :: lv ++ L (64 * W + 8 * M + 8)) (F (64 * W + 8 * M + 8))) ?_ (fun u h => h.1.1)
      fun u h => runF_mono h (fun q hq => List.mem_cons_of_mem _ hq) fun _ e => e
    refine frag_append (xs := [_]) (runF_dec o rfl (hjm _) (v := BitVec.ofNat 64 (8 * M)) fun u h => ?_) ?_
    · simp only [eval, (look M u h).1]
      rw [← BitVec.ofNat_mul, Nat.mul_comm]
    exact bitsLoop_frag o hA he hnn hlow hdecl hbody hW hM (hmlv M)
      (by rw [ScanRun.lookup_cons_ne (by decide)]; exact hwd) (by rw [ScanRun.lookup_cons_ne (by decide)]; exact hw)
      (lookup_head _ _ _) (ScanRun.fresh_cons (by decide) hj) (ScanRun.fresh_cons (by decide) hx)
  · -- an empty byte: nothing
    refine frag_nil o fun u ⟨h, h0⟩ => ?_
    rw [hbyte u h] at h0
    have hz : wordOf S W &&& BitVec.ofNat 64 (255 * 2 ^ (8 * M)) = 0 := by
      by_cases e : wordOf S W &&& BitVec.ofNat 64 (255 * 2 ^ (8 * M)) = 0
      · exact e
      · rw [decide_eq_true e] at h0; exact absurd h0 (by decide)
    obtain ⟨eL, eF⟩ := he.skipN 8 X fun Y h1 h2 => .inl (by
      rw [show Y = 64 * W + (Y - 64 * W) by omega, ← wordOf_bit S W (by omega)]
      exact byte_empty hz (by omega) (by omega) (by omega))
    exact ⟨by rw [eL]; exact h.1.1, eF _ h.1.2⟩
  · -- the next byte
    refine frag_conseq (runF_set o rfl (lookup_head _ _ _) (v := BitVec.ofNat 64 (M + 1)) fun u h => ?_)
      (fun u h => h) fun u h => ⟨?_, by omega⟩
    · simp only [eval, vals_lookup h.1.vals (lookup_head _ _ _), BitVec.ofNat_add]
    · dsimp only [lm]
      rw [show 64 * W + 8 * (M + 1) = X + 8 by omega]
      refine runF_mono h (fun q hq => ?_) fun _ e => e
      simp only [List.cons_append, List.mem_cons] at hq
      rcases hq with rfl | hq
      · exact List.mem_cons_self ..
      · refine List.mem_cons_of_mem _ (mem_without (List.mem_cons_of_mem _ hq) ?_)
        rcases List.mem_append.1 hq with hq | hq
        · exact ScanRun.fresh_ne hm q hq
        · exact ScanRun.fresh_ne (he.fresh _ "m" (by simp [loopNames])) q hq

/-! ### The words of a set -/

/-- **The words of a set** (`wordsLoop body`): words `W` to `hi` of the set. Those holding a bit are read byte by byte,
the rest skipped. -/
theorem wordsLoop_frag (o : Oracle σ) {ofs : Nat} {A : Word} {s0 : PancakeState σ} (hA : Area ofs A s0)
    {ks nn : Nat} (hks : ks < slots) {S : Nat → Bool} {L : Nat → List (String × Value)}
    {F : Nat → (Word → Word) → Prop} (he : Each A ks nn S L F) (hnn : nn ≤ inputMax) {body : List Syntax.PStmt}
    (hlow : LowKK body) (hdecl : ∀ X, ∀ y ∈ declared body, y ∉ loopNames ∧ Fresh y (L X) = true)
    (hbody : ∀ X (lv : List (String × Value)), (∀ q ∈ lv, q.1 ∈ loopNames) → S X = true → X < nn →
      Frag o body (RunF s0 (("x", BitVec.ofNat 64 X) :: lv ++ L X) (F X))
        (RunF s0 (("x", BitVec.ofNat 64 X) :: lv ++ L (X + 1)) (F (X + 1))))
    {lo hi : Nat} (hlo : lo < setWords) (hhi : hi < setWords) {lv : List (String × Value)}
    (hlv : ∀ q ∈ lv, q.1 ∈ loopNames)
    (hh : lv.lookup "hi" = some (BitVec.ofNat 64 hi)) (hw : Fresh "w" lv = true) (hwd : Fresh "wd" lv = true)
    (hm : Fresh "m" lv = true) (hj : Fresh "j" lv = true) (hx : Fresh "x" lv = true) :
    Frag o [wordsLoop body]
      (RunF s0 (("w", BitVec.ofNat 64 lo) :: lv ++ L (64 * lo)) (F (64 * lo)))
      (fun u => ∃ W, hi < W ∧ RunF s0 (("w", BitVec.ofNat 64 W) :: lv ++ L (64 * W)) (F (64 * W)) u) := by
  rw [setWords_eq] at hlo hhi
  let lw (W : Nat) : List (String × Value) := ("w", BitVec.ofNat 64 W) :: lv ++ L (64 * W)
  let I (W : Nat) : Assn σ := fun u => RunF s0 (lw W) (F (64 * W)) u ∧ W ≤ max lo (hi + 1)
  have hIc : ∀ W, Safe.ClockFree (I W) := fun W s k h => ⟨runF_clock _ _ _ s k h.1, h.2⟩
  have hwlv : ∀ W, ∀ q ∈ ("w", BitVec.ofNat 64 W) :: lv, q.1 ∈ loopNames := fun W q hq => by
    simp only [List.mem_cons] at hq; rcases hq with rfl | hq
    · simp [loopNames]
    · exact hlv q hq
  have hwwlv : ∀ W (WD : Word), ∀ q ∈ ("wd", WD) :: ("w", BitVec.ofNat 64 W) :: lv, q.1 ∈ loopNames :=
    fun W WD q hq => by
      simp only [List.mem_cons] at hq; rcases hq with rfl | hq
      · simp [loopNames]
      · exact hwlv W q (List.mem_cons.2 hq)
  have look : ∀ W u, RunF s0 (lw W) (F (64 * W)) u → u.locals "w" = some (BitVec.ofNat 64 W) ∧
      u.locals "hi" = some (BitVec.ofNat 64 hi) ∧ u.locals "p" = some (at_ A (off ks)) := by
    intro W u h
    dsimp only [lw] at h
    refine ⟨vals_lookup h.1.vals (lookup_head _ _ _), ?_, ?_⟩
    · exact vals_lookup h.1.vals (by
        rw [List.cons_append, ScanRun.lookup_cons_ne (by decide)]; exact lookup_app_some _ hh)
    · exact vals_lookup h.1.vals (by rw [lookup_app_fresh _ (fresh_loop (hwlv W) (by simp [loopNames]))]; exact he.p _)
  have hwdF : ∀ W Y, Fresh "wd" (("w", BitVec.ofNat 64 W) :: lv ++ L Y) = true := fun W Y =>
    ScanRun.fresh_cons (by decide) (fresh_app hwd (he.fresh Y "wd" (by simp [loopNames])))
  refine frag_conseq (frag_count o rfl
    (lowKK_wordsBody hlow)
    hIc (fun W u y v h hy => by
      obtain rfl : y = "wd" := by simpa [declared, declared_append, inc] using hy
      exact ⟨runF_restore h.1 (hwdF W _) v, h.2⟩) (g := fun W => decide (W ≤ hi))
    (fun W u h => FramerCode.eval_le (by omega) (by omega) (ev_var (look W u h.1).1) (ev_var (look W u h.1).2.1))
    (fun W hg => ?_) lo) (fun u h => ⟨h, by omega⟩) fun u ⟨W, h, hg⟩ => ?_
  rotate_left
  · exact ⟨W, by simpa using hg, h.1⟩
  have hW : W ≤ hi := of_decide_eq_true hg
  refine frag_conseq (P0 := RunF s0 (lw W) (F (64 * W))) (P0' := RunF s0 (lw (W + 1)) (F (64 * (W + 1)))) ?_
    (fun u h => h.1) fun u h => ⟨h, by omega⟩
  let WD := wordOf S W
  let lwd : List (String × Value) := ("wd", WD) :: lw W
  -- the word read
  refine frag_append (xs := [_]) (runF_dec o rfl (hwdF W _) (v := WD) fun u h => ?_) ?_
  · obtain ⟨hw', -, hp'⟩ := look W u h
    rw [slotLoad_eval hA h.1.memaddrs hks (bitIdx (by rw [setWords_eq]; omega)) (bit_eval rfl hp' hw'),
      slot_wordOf (he.mem _ _ h.2).1 (by rw [setWords_eq]; omega)]
  have hcond : ∀ u, RunF s0 lwd (F (64 * W)) u →
      eval u (.cmp .equal (.cmp .equal (.var "wd") (.const (BitVec.ofNat 64 0))) (.const (BitVec.ofNat 64 0))) =
        some (bw (decide (WD ≠ 0))) := fun u h => ne0_eval (ev_var (vals_lookup h.1.vals (lookup_head _ _ _)))
  let Mid : Assn σ := RunF s0 (("wd", WD) :: ("w", BitVec.ofNat 64 W) :: lv ++ L (64 * W + 64)) (F (64 * W + 64))
  have hmF : ∀ Y, Fresh "m" (("wd", WD) :: ("w", BitVec.ofNat 64 W) :: lv ++ L Y) = true := fun Y =>
    ScanRun.fresh_cons (by decide) (ScanRun.fresh_cons (by decide)
      (fresh_app hm (he.fresh Y "m" (by simp [loopNames]))))
  refine frag_append (xs := [_]) (M := Mid) (frag_ite o rfl (runF_clock _ _ _)
    (fun u h => ⟨_, hcond u h⟩) ?_ (fun u y v h hy => by
      obtain rfl : y = "m" := by simpa [declared, bytesLoop] using hy
      exact runF_restore h (hmF _) v) ?_ (noDecl _ rfl)) ?_
  · -- a word holding a bit: its bytes
    refine frag_conseq (P0 := RunF s0 lwd (F (64 * W)))
      (P0' := RunF s0 (("m", BitVec.ofNat 64 8) :: ("wd", WD) :: ("w", BitVec.ofNat 64 W) :: lv ++ L (64 * W + 64))
        (F (64 * W + 64))) ?_ (fun u h => h.1)
      fun u h => runF_mono h (fun q hq => List.mem_cons_of_mem _ hq) fun _ e => e
    refine frag_append (xs := [_]) (runF_dec o rfl (hmF _) (v := BitVec.ofNat 64 0) fun u h => rfl) ?_
    exact bytesLoop_frag o hA he hnn hlow hdecl hbody (by rw [setWords_eq]; omega) (hwwlv W WD) (lookup_head _ _ _)
      (by rw [ScanRun.lookup_cons_ne (by decide), lookup_head])
      (ScanRun.fresh_cons (by decide) (ScanRun.fresh_cons (by decide) hm))
      (ScanRun.fresh_cons (by decide) (ScanRun.fresh_cons (by decide) hj))
      (ScanRun.fresh_cons (by decide) (ScanRun.fresh_cons (by decide) hx))
  · -- an empty word: nothing
    refine frag_nil o fun u ⟨h, h0⟩ => ?_
    rw [hcond u h] at h0
    have hz : WD = 0 := by
      by_cases e : WD = 0
      · exact e
      · rw [decide_eq_true e] at h0; exact absurd h0 (by decide)
    obtain ⟨eL, eF⟩ := he.skipN 64 (64 * W) fun Y h1 h2 => .inl (by
      rw [show Y = 64 * W + (Y - 64 * W) by omega, ← wordOf_bit S W (by omega)]
      show WD.getLsbD _ = false
      rw [hz]; simp)
    exact ⟨by rw [eL]; exact h.1, eF _ h.2⟩
  · -- the next word
    refine frag_conseq (runF_set o rfl (by
        simp only [List.cons_append]; rw [ScanRun.lookup_cons_ne (by decide), lookup_head])
      (v := BitVec.ofNat 64 (W + 1)) fun u h => ?_) (fun u h => h) fun u h => ?_
    · have hw : (("wd", WD) :: ("w", BitVec.ofNat 64 W) :: lv ++ L (64 * W + 64)).lookup "w" =
          some (BitVec.ofNat 64 W) := by
        simp only [List.cons_append]; rw [ScanRun.lookup_cons_ne (by decide), lookup_head]
      simp only [eval, vals_lookup h.1.vals hw, BitVec.ofNat_add]
    · dsimp only [lw]
      rw [show 64 * (W + 1) = 64 * W + 64 by omega]
      refine runF_mono h (fun q hq => ?_) fun _ e => e
      simp only [List.cons_append, List.mem_cons] at hq
      rcases hq with rfl | hq
      · exact List.mem_cons_self ..
      · refine List.mem_cons_of_mem _ (mem_without (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hq)) ?_)
        rcases List.mem_append.1 hq with hq | hq
        · exact ScanRun.fresh_ne hw q hq
        · exact ScanRun.fresh_ne (he.fresh _ "w" (by simp [loopNames])) q hq

/-! ### Each position -/

/-- **Each position of a set** (`eachPos body`): those in slot `ks` below `nn`, lowest first, each taken by `body`. At
the end the set holds none past the `X` reached. -/
theorem eachPos_frag (o : Oracle σ) {ofs : Nat} {A : Word} {s0 : PancakeState σ} (hA : Area ofs A s0)
    {ks nn : Nat} (hks : ks < slots) {S : Nat → Bool} {L : Nat → List (String × Value)}
    {F : Nat → (Word → Word) → Prop} (he : Each A ks nn S L F) (hnn : nn ≤ inputMax) {body : List Syntax.PStmt}
    (hlow : LowKK body) (hdecl : ∀ X, ∀ y ∈ declared body, y ∉ loopNames ∧ Fresh y (L X) = true)
    (hbody : ∀ X (lv : List (String × Value)), (∀ q ∈ lv, q.1 ∈ loopNames) → S X = true → X < nn →
      Frag o body (RunF s0 (("x", BitVec.ofNat 64 X) :: lv ++ L X) (F X))
        (RunF s0 (("x", BitVec.ofNat 64 X) :: lv ++ L (X + 1)) (F (X + 1))))
    {M0 : Word → Word} (hF0 : F 0 M0) :
    Frag o (eachPos body) (RunF s0 (L 0) (· = M0))
      (fun u => ∃ X, (∀ Y, X ≤ Y → S Y = false) ∧ RunF s0 (L X) (F X) u) := by
  have hS := (he.mem 0 M0 hF0).1
  have l1 := hS.lo
  have h1 := hS.hi
  generalize hlo : (M0 (slotW A ks 0)).toNat = lov at l1
  generalize hhi : (M0 (slotW A ks 1)).toNat = hiv at h1
  have fr : ∀ X y, y ∈ loopNames → Fresh y (L X) = true := fun X y hy => he.fresh X y hy
  refine frag_append (readWin_frag o hA hks (by decide) (by decide) (he.p 0) (fr 0 "lo" (by simp [loopNames]))
    (fr 0 "hi" (by simp [loopNames])) hS) ?_
  rw [hlo, hhi]
  let lv : List (String × Value) := [("hi", BitVec.ofNat 64 hiv), ("lo", BitVec.ofNat 64 lov)]
  have hlv : ∀ q ∈ lv, q.1 ∈ loopNames := fun q hq => by
    simp only [lv, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl <;> simp [loopNames]
  -- the positions below the window are none of the set
  obtain ⟨eL, eF⟩ := he.skipN (64 * lov) 0 fun Y _ h2 => .inl (by
    cases e : S Y
    · rfl
    · have := (hS.win Y e).1; rw [hlo] at this; omega)
  rw [Nat.zero_add] at eL eF
  refine frag_append (xs := [_]) (runF_dec o rfl (v := BitVec.ofNat 64 lov) (ScanRun.fresh_cons (by decide)
    (ScanRun.fresh_cons (by decide) (fr 0 "w" (by simp [loopNames])))) fun u h =>
      ev_var (vals_lookup h.1.vals (by rw [ScanRun.lookup_cons_ne (by decide), lookup_head]))) ?_
  refine frag_conseq (wordsLoop_frag o hA hks he hnn hlow hdecl hbody (lo := lov) (hi := hiv) l1 h1 hlv
    (lookup_head _ _ _) (by simp [lv, Fresh]) (by simp [lv, Fresh]) (by simp [lv, Fresh]) (by simp [lv, Fresh])
    (by simp [lv, Fresh])) (fun u h => ⟨?_, by rw [show u.memory = M0 from h.2]; exact eF _ hF0⟩)
    fun u ⟨W, hW, h⟩ => ⟨64 * W, fun Y hY => ?_, ?_⟩
  · rw [eL]; exact h.1
  · cases e : S Y
    · rfl
    · have := (hS.win Y e).2; rw [hhi] at this; omega
  · exact runF_mono h (fun q hq => List.mem_cons_of_mem _ (List.mem_append_right _ hq)) fun _ e => e

/-! ## A position added -/

theorem mem_of_lookup : ∀ {l : List (String × Value)} {x : String} {v : Value}, l.lookup x = some v → (x, v) ∈ l
  | [], _, _, h => nomatch h
  | (a, b) :: l, x, v, h => by
    by_cases e : x = a
    · subst e; rw [lookup_head] at h; cases h; exact List.mem_cons_self ..
    · rw [ScanRun.lookup_cons_ne e] at h; exact List.mem_cons_of_mem _ (mem_of_lookup h)

/-- A local listed again at the front, as it is. -/
theorem runF_front {s0 u : PancakeState σ} {l : List (String × Value)} {F : (Word → Word) → Prop}
    (h : RunF s0 l F u) {x : String} {v : Value} (hl : l.lookup x = some v) :
    RunF s0 ((x, v) :: without x l) F u :=
  ⟨⟨fun q hq => by
    simp only [List.mem_cons] at hq
    rcases hq with rfl | hq
    · exact vals_lookup h.1.vals hl
    · exact h.1.vals q (List.mem_filter.1 hq).1, h.1.memaddrs, h.1.base, h.1.code, h.1.be⟩, h.2⟩

/-- The window's ends grown to take word `w`: the first word gives both. -/
def grow (dl dh : Nat) (df : Bool) (w : Nat) : Nat × Nat := if df then (w, w) else (min dl w, max dh w)

/-- **The window grown** (`addWin`): its ends in `dl` and `dh` take word `yw`, and `df` is cleared. -/
theorem addWin_frag (o : Oracle σ) {s0 : PancakeState σ} {l : List (String × Value)} {F : (Word → Word) → Prop}
    {dl dh w : Nat} {df : Bool} (hb1 : dl < 2 ^ 62) (hb2 : dh < 2 ^ 62) (hb3 : w < 2 ^ 62)
    (hdl : l.lookup "dl" = some (BitVec.ofNat 64 dl)) (hdh : l.lookup "dh" = some (BitVec.ofNat 64 dh))
    (hdf : l.lookup "df" = some (bw df)) (hw : l.lookup "yw" = some (BitVec.ofNat 64 w)) :
    Frag o (addWin .none) (RunF s0 l F)
      (RunF s0 (("df", bw false) :: ("dh", BitVec.ofNat 64 (grow dl dh df w).2) ::
        ("dl", BitVec.ofNat 64 (grow dl dh df w).1) :: without "dl" (without "dh" (without "df" l))) F) := by
  have hFc := runF_clock (σ := σ) s0
  have lw : ∀ (l' : List (String × Value)), (∀ q ∈ l, q.1 ≠ "dl" → q.1 ≠ "dh" → q.1 ≠ "df" → q ∈ l') →
      ∀ q ∈ without "dl" (without "dh" (without "df" l)), q ∈ l' := fun l' hl' q hq => by
    simp only [without, List.mem_filter, bne_iff_ne, ne_eq] at hq
    exact hl' q hq.1.1.1 hq.2 hq.1.2 hq.1.1.2
  show Frag o [.ite (Syntax.v "df") _ _] _ _
  refine ScanRun.frag_if o rfl (lowK_any _ (k := .skip) rfl) (lowK_any _ (k := .skip) rfl) rfl rfl (hFc _ _)
    (b := df) (fun u h => ev_var (vals_lookup h.1.vals hdf)) (fun e => ?_) fun e => ?_
  · subst e
    refine frag_append (xs := [_]) (runF_set o rfl hdl (v := BitVec.ofNat 64 w) fun u h =>
      ev_var (vals_lookup h.1.vals hw)) ?_
    have l1 : (("dl", BitVec.ofNat 64 w) :: without "dl" l).lookup "dh" = some (BitVec.ofNat 64 dh) := by
      rw [ScanRun.lookup_cons_ne (by decide), lookup_without (by decide)]; exact hdh
    have l2 : (("dl", BitVec.ofNat 64 w) :: without "dl" l).lookup "yw" = some (BitVec.ofNat 64 w) := by
      rw [ScanRun.lookup_cons_ne (by decide), lookup_without (by decide)]; exact hw
    have l3 : (("dh", BitVec.ofNat 64 w) :: without "dh" (("dl", BitVec.ofNat 64 w) :: without "dl" l)).lookup "df" =
        some (bw true) := by
      rw [ScanRun.lookup_cons_ne (by decide), lookup_without (by decide), ScanRun.lookup_cons_ne (by decide),
        lookup_without (by decide)]; exact hdf
    refine frag_append (xs := [_]) (runF_set o rfl l1 (v := BitVec.ofNat 64 w) fun u h =>
      ev_var (vals_lookup h.1.vals l2)) ?_
    refine frag_conseq (runF_set o rfl l3 (v := bw false) fun u h => rfl)
      (fun u h => h) fun u h => runF_mono h (fun q hq => ?_) fun _ e => e
    simp only [grow, if_true, List.mem_cons] at hq
    rcases hq with rfl | rfl | rfl | hq
    · exact List.mem_cons_self ..
    · exact List.mem_cons_of_mem _ (mem_without (List.mem_cons_self ..) (by simp))
    · exact List.mem_cons_of_mem _ (mem_without (List.mem_cons_of_mem _ (mem_without (List.mem_cons_self ..)
        (by simp))) (by simp))
    · refine lw _ (fun q hq h1 h2 h3 => ?_) q hq
      exact List.mem_cons_of_mem _ (mem_without (List.mem_cons_of_mem _ (mem_without (List.mem_cons_of_mem _
        (mem_without hq h1)) h2)) h3)
  · subst e
    -- the start, then the end
    refine frag_append (xs := [_]) (M := RunF s0 (("dl", BitVec.ofNat 64 (min dl w)) :: without "dl" l) F)
      (ScanRun.frag_if o rfl (lowK_any _ (k := .skip) rfl) (lowK_any _ (k := .skip) rfl) rfl rfl (hFc _ _)
        (b := decide (w < dl)) (fun u h => FramerCode.eval_lt (by omega) (by omega)
          (ev_var (vals_lookup h.1.vals hw)) (ev_var (vals_lookup h.1.vals hdl))) (fun e => ?_) fun e => ?_) ?_
    · refine frag_conseq (runF_set o rfl hdl (v := BitVec.ofNat 64 w) fun u h => ev_var (vals_lookup h.1.vals hw))
        (fun u h => h) fun u h => ?_
      rwa [Nat.min_eq_right (by simp at e; omega)]
    · refine frag_nil o fun u h => ?_
      rw [Nat.min_eq_left (by simp at e; omega)]
      exact runF_front h hdl
    refine frag_conseq (ScanRun.frag_if o rfl (lowK_any _ (k := .skip) rfl) (lowK_any _ (k := .skip) rfl) rfl rfl
      (hFc _ _) (P := RunF s0 (("dl", BitVec.ofNat 64 (min dl w)) :: without "dl" l) F)
      (Q := RunF s0 (("dh", BitVec.ofNat 64 (max dh w)) :: without "dh" (("dl", BitVec.ofNat 64 (min dl w)) ::
        without "dl" l)) F) (b := decide (dh < w))
      (fun u h => FramerCode.eval_lt (by omega) (by omega)
        (ev_var (vals_lookup h.1.vals (by
          rw [ScanRun.lookup_cons_ne (by decide), lookup_without (by decide)]; exact hdh)))
        (ev_var (vals_lookup h.1.vals (by
          rw [ScanRun.lookup_cons_ne (by decide), lookup_without (by decide)]; exact hw))))
      (fun e => ?_) fun e => ?_) (fun u h => h) fun u h => runF_mono h (fun q hq => ?_) fun _ e => e
    · refine frag_conseq (runF_set o rfl (by
        rw [ScanRun.lookup_cons_ne (by decide), lookup_without (by decide)]; exact hdh) (v := BitVec.ofNat 64 w)
        fun u h => ev_var (vals_lookup h.1.vals (by
          rw [ScanRun.lookup_cons_ne (by decide), lookup_without (by decide)]; exact hw)))
        (fun u h => h) fun u h => ?_
      rwa [Nat.max_eq_right (by simp at e; omega)]
    · refine frag_nil o fun u h => ?_
      rw [Nat.max_eq_left (by simp at e; omega)]
      exact runF_front h (by rw [ScanRun.lookup_cons_ne (by decide), lookup_without (by decide)]; exact hdh)
    simp only [grow, Bool.false_eq_true, if_false, List.mem_cons] at hq
    rcases hq with rfl | rfl | rfl | hq
    · exact List.mem_cons_of_mem _ (mem_without (List.mem_cons_of_mem _ (mem_without (mem_of_lookup hdf)
        (by simp))) (by simp))
    · exact List.mem_cons_self ..
    · exact List.mem_cons_of_mem _ (mem_without (List.mem_cons_self ..) (by simp))
    · refine lw _ (fun q hq h1 h2 _ => ?_) q hq
      exact List.mem_cons_of_mem _ (mem_without (List.mem_cons_of_mem _ (mem_without hq h1)) h2)

/-- **A position added** (`addBit`): its bit set in slot `kd`, the window's ends grown to its word. -/
theorem addBit_frag (o : Oracle σ) {ofs : Nat} {A : Word} {s0 : PancakeState σ} (hA : Area ofs A s0) {kd : Nat}
    (hkd : kd < slots) {l : List (String × Value)} (ha : l.lookup "a" = some A)
    (hq : l.lookup "q" = some (at_ A (off kd))) {y : Syntax.PExpr} {Ey : PancakeExp} (hy0 : Lower.lowerExp y = some Ey)
    {Y : Nat} (hY : Y < 64 * setWords) (hy : ∀ u, RunF s0 l (fun _ => True) u → eval u Ey = some (BitVec.ofNat 64 Y))
    (hw : Fresh "yw" l = true) (hj : Fresh "yj" l = true) {dl dh : Nat} {df : Bool} (hb1 : dl < setWords)
    (hb2 : dh < setWords) (hdl : l.lookup "dl" = some (BitVec.ofNat 64 dl))
    (hdh : l.lookup "dh" = some (BitVec.ofNat 64 dh)) (hdf : l.lookup "df" = some (bw df)) {m0 : Word → Word}
    (hP : Pows m0 A) :
    Frag o (addBit .none y) (RunF s0 l (· = m0))
      (RunF s0 (("df", bw false) :: ("dh", BitVec.ofNat 64 (grow dl dh df (Y / 64)).2) ::
        ("dl", BitVec.ofNat 64 (grow dl dh df (Y / 64)).1) :: without "dl" (without "dh" (without "df" l)))
        (· = upd m0 (slotW A kd (2 + Y / 64)) (m0 (slotW A kd (2 + Y / 64)) ||| BitVec.twoPow 64 (Y % 64)))) := by
  rw [setWords_eq] at hb1 hb2 hY
  let l2 : List (String × Value) := ("yj", BitVec.ofNat 64 (Y % 64)) :: ("yw", BitVec.ofNat 64 (Y / 64)) :: l
  have c2 : ∀ x, x ≠ "yj" → x ≠ "yw" → l2.lookup x = l.lookup x := fun x h1 h2 => by
    rw [ScanRun.lookup_cons_ne h1, ScanRun.lookup_cons_ne h2]
  refine frag_append (frag_append (posParts_frag o hy0 (by rw [setWords_eq]; omega) (fun u h => hy u ⟨h.1, trivial⟩)
    hw hj) (setBit_frag o hA hkd (by rw [c2 _ (by decide) (by decide)]; exact ha)
      (by rw [c2 _ (by decide) (by decide)]; exact hq) (by rw [setWords_eq]; omega)
      (by rw [ScanRun.lookup_cons_ne (by decide), lookup_head]) (lookup_head _ _ _) hP)) ?_
  refine frag_conseq (addWin_frag o (l := l2) (dl := dl) (dh := dh) (w := Y / 64) (df := df) (by omega) (by omega)
    (by omega)
    (by rw [c2 _ (by decide) (by decide)]; exact hdl) (by rw [c2 _ (by decide) (by decide)]; exact hdh)
    (by rw [c2 _ (by decide) (by decide)]; exact hdf) (by rw [ScanRun.lookup_cons_ne (by decide), lookup_head]))
    (fun u h => h) fun u h => runF_mono h (fun q hq' => ?_) fun _ e => e
  simp only [List.mem_cons] at hq'
  rcases hq' with rfl | rfl | rfl | hq'
  · exact List.mem_cons_self ..
  · exact List.mem_cons_of_mem _ (List.mem_cons_self ..)
  · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
  · refine List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ ?_))
    simp only [without, List.mem_filter] at hq' ⊢
    exact ⟨⟨⟨List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hq'.1.1.1), hq'.1.1.2⟩, hq'.1.2⟩, hq'.2⟩

/-! ## A set built from another's positions -/

/-- The positions added at the positions below `X`, `add x` the end added at `x`, if any. -/
def below (add : Nat → Option Nat) (X e : Nat) : Bool := (List.range X).any fun x => add x == some e

theorem below_succ (add : Nat → Option Nat) (X e : Nat) :
    below add (X + 1) e = (below add X e || add X == some e) := by
  simp [below, List.range_succ, List.any_append]

/-- The window's ends, and whether it is empty, after the positions below `X`. -/
def winS (add : Nat → Option Nat) : Nat → Nat × Nat × Bool
  | 0 => (1, 0, true)
  | X + 1 => match add X with
    | none => winS add X
    | some e => ((grow (winS add X).1 (winS add X).2.1 (winS add X).2.2 (e / 64)).1,
        (grow (winS add X).1 (winS add X).2.1 (winS add X).2.2 (e / 64)).2, false)

/-- What the window says of the positions added: none while it is empty. Otherwise its ends bound their words, and one
is added. -/
def WinOk (add : Nat → Option Nat) (X : Nat) : Prop :=
  ((winS add X).2.2 = true → ∀ e, below add X e = false) ∧
  ((winS add X).2.2 = false → (winS add X).1 ≤ (winS add X).2.1 ∧ (∃ e, below add X e = true) ∧
    ∀ e, below add X e = true → (winS add X).1 ≤ e / 64 ∧ e / 64 ≤ (winS add X).2.1)

theorem winOk (add : Nat → Option Nat) : ∀ X, WinOk add X
  | 0 => ⟨fun _ _ => by simp [below], fun h => by simp [winS] at h⟩
  | X + 1 => by
    obtain ⟨h1, h2⟩ := winOk add X
    cases ha : add X with
    | none =>
      have hb : ∀ e, below add (X + 1) e = below add X e := fun e => by rw [below_succ, ha]; simp
      have hw : winS add (X + 1) = winS add X := by simp only [winS, ha]
      refine ⟨fun h e => by rw [hb]; exact h1 (hw ▸ h) e, fun h => ?_⟩
      rw [hw] at h ⊢
      obtain ⟨a, ⟨e, he⟩, c⟩ := h2 h
      exact ⟨a, ⟨e, by rw [hb]; exact he⟩, fun e' he' => c e' (by rw [← hb]; exact he')⟩
    | some e =>
      have hb : ∀ e', below add (X + 1) e' = (below add X e' || e == e') := fun e' => by
        rw [below_succ, ha]; simp
      have hw : winS add (X + 1) = ((grow (winS add X).1 (winS add X).2.1 (winS add X).2.2 (e / 64)).1,
          (grow (winS add X).1 (winS add X).2.1 (winS add X).2.2 (e / 64)).2, false) := by simp only [winS, ha]
      refine ⟨(fun h => by rw [hw] at h; simp at h), fun _ => ?_⟩
      rw [hw]
      simp only [grow]
      cases hd : (winS add X).2.2
      · obtain ⟨a, -, c⟩ := h2 hd
        simp only [Bool.false_eq_true, if_false]
        refine ⟨by omega, ⟨e, by rw [hb]; simp⟩, fun e' he' => ?_⟩
        rw [hb] at he'
        simp only [Bool.or_eq_true, beq_iff_eq] at he'
        rcases he' with he' | rfl
        · have := c e' he'; omega
        · omega
      · simp only [if_true]
        refine ⟨Nat.le_refl _, ⟨e, by rw [hb]; simp⟩, fun e' he' => ?_⟩
        rw [hb, h1 hd e'] at he'
        simp only [Bool.false_or, beq_iff_eq] at he'
        subst he'; omega

/-- An empty window is `[1, 0]`. -/
theorem winS_empty (add : Nat → Option Nat) : ∀ X, (winS add X).2.2 = true → (winS add X).1 = 1 ∧ (winS add X).2.1 = 0
  | 0, _ => ⟨rfl, rfl⟩
  | X + 1, h => by
    cases ha : add X with
    | none => simp only [winS, ha] at h ⊢; exact winS_empty add X h
    | some e => simp only [winS, ha] at h; cases h

/-- The window's ends stay below a bound on the words added. -/
theorem winS_lt (add : Nat → Option Nat) {B : Nat} (hB : 2 ≤ B) (h : ∀ x e, add x = some e → e / 64 < B) :
    ∀ X, (winS add X).1 < B ∧ (winS add X).2.1 < B
  | 0 => ⟨by simp [winS]; omega, by simp [winS]; omega⟩
  | X + 1 => by
    obtain ⟨h1, h2⟩ := winS_lt add hB h X
    cases ha : add X with
    | none => simp only [winS, ha]; exact ⟨h1, h2⟩
    | some e =>
      have := h X e ha
      simp only [winS, ha, grow]
      split <;> constructor <;> simp <;> omega

/-- Slot `kd` holds the positions added below `X` as bits, every other word as in `m1`. -/
structure Built (A : Word) (kd : Nat) (add : Nat → Option Nat) (X : Nat) (m1 m : Word → Word) : Prop where
  bits : ∀ w, w < setWords → ∀ j, j < 64 → (m (slotW A kd (2 + w))).getLsbD j = below add X (64 * w + j)
  rest : ∀ a, (∀ w, w < setWords → a ≠ slotW A kd (2 + w)) → m a = m1 a

theorem built_zero {A : Word} {kd : Nat} {add : Nat → Option Nat} {m1 : Word → Word}
    (h : ∀ w, w < setWords → ∀ j, j < 64 → (m1 (slotW A kd (2 + w))).getLsbD j = false) : Built A kd add 0 m1 m1 :=
  ⟨fun w hw j hj => by rw [h w hw j hj]; simp [below], fun _ _ => rfl⟩

theorem built_skip {A : Word} {kd : Nat} {add : Nat → Option Nat} {X : Nat} {m1 m : Word → Word}
    (h : Built A kd add X m1 m) (ha : add X = none) : Built A kd add (X + 1) m1 m :=
  ⟨fun w hw j hj => by rw [h.bits w hw j hj, below_succ, ha]; simp, h.rest⟩

/-- A position added: its bit set in its word. -/
theorem built_add {A : Word} {kd : Nat} (hkd : kd < slots) {add : Nat → Option Nat} {X e : Nat} {m1 m : Word → Word}
    (h : Built A kd add X m1 m) (ha : add X = some e) (he : e < 64 * setWords) :
    Built A kd add (X + 1) m1
      (upd m (slotW A kd (2 + e / 64)) (m (slotW A kd (2 + e / 64)) ||| BitVec.twoPow 64 (e % 64))) := by
  rw [setWords_eq] at he
  refine ⟨fun w hw j hj => ?_, fun a ha' => ?_⟩
  · rw [below_succ, ha]
    by_cases ew : w = e / 64
    · subst ew
      rw [upd_eq, getLsbD_or_twoPow _ (by omega), h.bits _ hw j hj]
      congr 1
      rw [Bool.eq_iff_iff]; simp only [beq_iff_eq, Option.some.injEq]
      constructor <;> intro x <;> omega
    · rw [upd_ne _ (slotW_ne hkd (bitIdx hw) (bitIdx (by rw [setWords_eq]; omega)) (by omega)), h.bits w hw j hj]
      have : ¬(e = 64 * w + j) := fun x => ew (by omega)
      simp [this]
  · rw [upd_ne _ (ha' _ (by rw [setWords_eq]; omega))]; exact h.rest a ha'

/-- **The set built, its window stored** (the leaves' end): the slot holds the positions added. -/
theorem built_setAt {A : Word} {kd : Nat} (hkd : kd < slots) {add : Nat → Option Nat} {X : Nat} {m1 m : Word → Word}
    (h : Built A kd add X m1 m) (hsm : ∀ x e, add x = some e → e < 64 * setWords) :
    SetAt (upd (upd m (slotW A kd 0) (BitVec.ofNat 64 (winS add X).1)) (slotW A kd 1)
      (BitVec.ofNat 64 (winS add X).2.1)) A kd (below add X) := by
  have hl := winS_lt add (B := setWords) (by rw [setWords_eq]; decide)
    (fun x e he => by have := hsm x e he; rw [setWords_eq] at this ⊢; omega) X
  have hw := winOk add X
  have h01 : slotW A kd 0 ≠ slotW A kd 1 := slotW_ne hkd (by decide) (by decide) (by decide)
  have e0 : (upd (upd m (slotW A kd 0) (BitVec.ofNat 64 (winS add X).1)) (slotW A kd 1)
      (BitVec.ofNat 64 (winS add X).2.1) (slotW A kd 0)).toNat = (winS add X).1 := by
    rw [upd_ne _ h01, upd_eq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by rw [setWords_eq] at hl; omega)]
  have e1 : (upd (upd m (slotW A kd 0) (BitVec.ofNat 64 (winS add X).1)) (slotW A kd 1)
      (BitVec.ofNat 64 (winS add X).2.1) (slotW A kd 1)).toNat = (winS add X).2.1 := by
    rw [upd_eq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by rw [setWords_eq] at hl; omega)]
  have small : ∀ e, below add X e = true → e < 64 * setWords := fun e he => by
    simp only [below, List.any_eq_true, beq_iff_eq] at he
    obtain ⟨x, -, hx⟩ := he
    exact hsm x e hx
  refine ⟨by rw [e0]; exact hl.1, by rw [e1]; exact hl.2, fun w hw j hj => ?_, small, fun x hx => ?_, fun hle => ?_⟩
  · rw [upd_ne _ (slotW_bit_ne hkd hw).2, upd_ne _ (slotW_bit_ne hkd hw).1]; exact h.bits w hw j hj
  · rw [e0, e1]
    cases hd : (winS add X).2.2
    · exact (hw.2 hd).2.2 x hx
    · rw [hw.1 hd x] at hx; cases hx
  · rw [e0, e1] at hle
    cases hd : (winS add X).2.2
    · exact (hw.2 hd).2.1
    · -- an empty window is `[1, 0]`
      exfalso
      have := winS_empty add X hd
      omega

/-! ## The input and the tables -/

/-- The input's bytes from `aInput`, as a load reads them. -/
def InputAt (m : Word → Word) (dm : Word → Bool) (be : Bool) (A : Word) (bytes : List (BitVec 8)) : Prop :=
  ∀ x, x < bytes.length → memLoadByte m dm be (at_ A (aInput + x)) = some bytes[x]!

/-- A word of class `k`. -/
def classWord (k i : Nat) : Nat := (classes[k]?.getD [])[i]?.getD 0

/-- The classes' words from `aClass`, four to a class. -/
def ClassesAt (m : Word → Word) (A : Word) : Prop :=
  ∀ k, k < classes.length → ∀ i, i < 4 → m (at_ A (aClass + 32 * k + 8 * i)) = BitVec.ofNat 64 (classWord k i)

theorem aClass_eq : aClass = 66472 := rfl

/-- A byte of the input, its address worked out to `aInput + y` past the area. -/
theorem inputAt_eval {u : PancakeState σ} {A : Word} {bytes : List (BitVec 8)}
    (hin : InputAt u.memory u.memaddrs u.be A bytes) {E : PancakeExp} {Y : Nat} (hY : Y < bytes.length)
    (hE : eval u E = some (at_ A (aInput + Y))) :
    eval u (.loadByte E) = some (BitVec.ofNat 64 (bytes[Y]!).toNat) := by
  rw [eval, hE]
  simp only [hin Y hY]
  congr 1
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]

/-- The input's byte at `x`, its address `a + aInput + x`. -/
theorem inputByte_eval {u : PancakeState σ} {A : Word} {bytes : List (BitVec 8)}
    (hin : InputAt u.memory u.memaddrs u.be A bytes) (ha : u.locals "a" = some A) {X : Nat} (hX : X < bytes.length)
    (hx : u.locals "x" = some (BitVec.ofNat 64 X)) :
    eval u (.loadByte (.op .add (.op .add (.var "a") (.const (BitVec.ofNat 64 aInput))) (.var "x"))) =
      some (BitVec.ofNat 64 (bytes[X]!).toNat) :=
  inputAt_eval hin hX (by simp only [eval, ha, hx]; rw [← at_add]; rfl)

/-- A byte's word in its class, the number of the thresholds 64, 128 and 192 it reaches. -/
theorem bw3 {B : Nat} (hB : B < 256) :
    bw (decide (64 ≤ B)) + bw (decide (128 ≤ B)) + bw (decide (192 ≤ B)) = BitVec.ofNat 64 (B / 64) := by
  by_cases h1 : 64 ≤ B <;> by_cases h2 : 128 ≤ B <;> by_cases h3 : 192 ≤ B <;> simp [bw, h1, h2, h3] <;>
    first | omega | (congr 1; omega)

/-- Word `i` of class `k`, its address `t + 8 * i`. -/
theorem classWord_eval {ofs : Nat} {A : Word} {s0 u : PancakeState σ} (hA : Area ofs A s0)
    (hm : u.memaddrs = s0.memaddrs) (hC : ClassesAt u.memory A) {k i : Nat} (hk : k < classes.length) (hi : i < 4)
    (ht : u.locals "t" = some (at_ A (aClass + 32 * k))) (hb : u.locals "bw" = some (BitVec.ofNat 64 i)) :
    eval u (.loadWord (.op .add (.var "t") (.mul (.var "bw") (.const (BitVec.ofNat 64 8))))) =
      some (BitVec.ofNat 64 (classWord k i)) := by
  have hl := classes_end
  have e : eval u (.op .add (.var "t") (.mul (.var "bw") (.const (BitVec.ofNat 64 8)))) =
      some (at_ A (aClass + 32 * k + 8 * i)) := by
    simp only [eval, ht, hb]
    rw [← BitVec.ofNat_mul, at_add]
    exact congrArg (fun y => some (at_ A y)) (by omega)
  rw [load_eval hA hm (y := aClass + 32 * k + 8 * i) (by omega) (by rw [aClass_eq]; omega) e, hC k hk i hi]

/-! ## What the leaves read -/

/-- Words below the slots are no slot's bits. -/
theorem below_bits {A : Word} {k x : Nat} (hk : k < slots) (hx : x < aSets) :
    ∀ w, w < setWords → at_ A x ≠ slotW A k (2 + w) :=
  fun w hw e => notInSlot hk hx ⟨2 + w, bitIdx hw, e⟩

/-- String `k` and whether its letters match in either case. -/
@[irreducible] def textAt (k : Nat) : List Nat × Bool := texts[k]?.getD ([], false)

theorem textAt_short {k : Nat} (hk : k < texts.length) : (textAt k).1.length ≤ textMax := by
  unfold textAt; exact texts_short k hk

theorem textAt_byte {k i : Nat} (hk : k < texts.length) (hi : i < (textAt k).1.length) : (textAt k).1[i]! < 256 := by
  have := texts_bytes k hk
  unfold textAt at hi ⊢
  refine this _ ?_
  rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]
  exact List.getElem_mem hi

/-- Where string `k`'s bytes start among the strings' bytes. -/
def textOff (k : Nat) : Nat := ((texts.take k).map (·.1.length)).sum

theorem take_sum_le (T : List (List Nat × Bool)) {k : Nat} (hk : k < T.length) :
    ((T.take k).map (·.1.length)).sum + (T[k]?.getD ([], false)).1.length ≤ (T.map (·.1.length)).sum := by
  have h1 : (T.map (·.1.length)).sum = ((T.map (·.1.length)).take (k + 1)).sum +
      ((T.map (·.1.length)).drop (k + 1)).sum := by rw [← List.sum_append, List.take_append_drop]
  have h2 : ((T.map (·.1.length)).take (k + 1)).sum = ((T.map (·.1.length)).take k).sum +
      (T[k]?.getD ([], false)).1.length := by
    rw [List.take_add_one, List.sum_append, List.getElem?_map, List.getElem?_eq_getElem hk]
    simp
  rw [List.map_take]; omega

theorem textOff_le {k : Nat} (hk : k < texts.length) : textOff k + (textAt k).1.length ≤ textBytes := by
  unfold textAt; exact take_sum_le texts hk

/-- The strings' table from `aTexts`, three words each: where the bytes start, how many, and the case. The bytes lie
from `aTextBytes`. -/
def TextsAt (m : Word → Word) (dm : Word → Bool) (be : Bool) (A : Word) : Prop :=
  ∀ k, k < texts.length → m (at_ A (aTexts + 24 * k)) = BitVec.ofNat 64 (textOff k) ∧
    m (at_ A (aTexts + 24 * k + 8)) = BitVec.ofNat 64 (textAt k).1.length ∧
    m (at_ A (aTexts + 24 * k + 16)) = bw (textAt k).2 ∧
    ∀ i, i < (textAt k).1.length →
      memLoadByte m dm be (at_ A (aTextBytes + textOff k + i)) = some (BitVec.ofNat 8 ((textAt k).1[i]!))

/-- What the leaves read: the input, the powers of two, the masks, the classes and the strings. -/
structure Reads (s0 : PancakeState σ) (A : Word) (bytes : List (BitVec 8)) (m : Word → Word) : Prop where
  input : InputAt m s0.memaddrs s0.be A bytes
  pows : Pows m A
  masks : Masks m A
  classes : ClassesAt m A
  texts : TextsAt m s0.memaddrs s0.be A

/-- **What the leaves read is kept** where the words below the slots are. -/
theorem reads_keep {s0 : PancakeState σ} {A : Word} {bytes : List (BitVec 8)} (hA8 : A.toNat % 8 = 0)
    (hlen : bytes.length ≤ inputMax) {m1 m : Word → Word} (h : Reads s0 A bytes m1)
    (keep : ∀ x, x < aSets → m (at_ A x) = m1 (at_ A x)) : Reads s0 A bytes m := by
  have hp := pow_lt
  have hio := io_le
  have hin := input_le
  refine ⟨fun x hx => ?_, fun j hj => ?_, fun b hb => ?_, fun k hk i hi => ?_, fun k hk => ?_⟩
  · have := h.input x hx
    unfold memLoadByte at this ⊢
    rw [ScanRun.align_at hA8] at this ⊢
    rw [keep ((aInput + x) / 8 * 8) (by omega)]; exact this
  · rw [keep (aPow + 8 * j) (by omega)]; exact h.pows j hj
  · rw [keep (aMask + 8 * b) (by have := aClass_le; have : aClass = aMask + 8 * 8 := rfl; omega)]; exact h.masks b hb
  · have := classes_end
    rw [keep (aClass + 32 * k + 8 * i) (by omega)]; exact h.classes k hk i hi
  · have hte := texts_end
    have htb := textBytes_le
    have hof := textOff_le hk
    obtain ⟨t0, t1, t2, t3⟩ := h.texts k hk
    refine ⟨by rw [keep _ (by omega)]; exact t0, by rw [keep _ (by omega)]; exact t1,
      by rw [keep _ (by omega)]; exact t2,
      fun i hi => ?_⟩
    have := t3 i hi
    unfold memLoadByte at this ⊢
    rw [ScanRun.align_at hA8] at this ⊢
    rw [keep ((aTextBytes + textOff k + i) / 8 * 8) (by omega)]; exact this

/-- What the leaves read is kept while slot `kd` is built. -/
theorem reads_built {s0 : PancakeState σ} {A : Word} {bytes : List (BitVec 8)} {kd : Nat} (hkd : kd < slots)
    (hA8 : A.toNat % 8 = 0) (hlen : bytes.length ≤ inputMax) {m1 m : Word → Word} (h : Reads s0 A bytes m1)
    (hm : ∀ a, (∀ w, w < setWords → a ≠ slotW A kd (2 + w)) → m a = m1 a) : Reads s0 A bytes m :=
  reads_keep hA8 hlen h fun _ hx => hm _ (below_bits hkd hx)

/-! ## A byte of a class -/

/-- A byte in class `k`: bit `b % 64` of its word `b / 64`. -/
def classBit (k b : Nat) : Bool := (classWord k (b / 64)).testBit (b % 64)

/-- What a leaf adds at `x`: `f x`, where `x` is a position of `S` below `nn` that `P` takes. -/
def leafAdd (S : Nat → Bool) (nn : Nat) (P : Nat → Bool) (f : Nat → Nat) (x : Nat) : Option Nat :=
  if S x && decide (x < nn) && P x then some (f x) else none

/-- The window's locals after the positions below `X`. -/
def winL (add : Nat → Option Nat) (X : Nat) : List (String × Value) :=
  [("df", bw (winS add X).2.2), ("dh", BitVec.ofNat 64 (winS add X).2.1), ("dl", BitVec.ofNat 64 (winS add X).1)]

theorem winL_skip {add : Nat → Option Nat} {X : Nat} (h : add X = none) : winL add (X + 1) = winL add X := by
  simp [winL, winS, h]

/-- The test of a byte's bit in a class word. -/
theorem class_test (W : Nat) {i : Nat} (hi : i < 64) :
    bw (decide (BitVec.ofNat 64 W &&& BitVec.twoPow 64 i ≠ 0)) = bw (W.testBit i) := by
  rw [BitVec.and_twoPow, BitVec.getLsbD_ofNat]
  have hne : BitVec.twoPow 64 i ≠ 0 := fun e => by
    have := congrArg (fun x => x.getLsbD i) e
    simp only [BitVec.getLsbD_twoPow] at this; simp at this; omega
  have hne' : ¬BitVec.twoPow 64 i = 0#64 := hne
  cases W.testBit i <;> simp [hi, hne']

theorem mem_withoutW {q : String × Value} {l : List (String × Value)} (hq : q ∈ l) (h1 : q.1 ≠ "dl")
    (h2 : q.1 ≠ "dh") (h3 : q.1 ≠ "df") : q ∈ without "dl" (without "dh" (without "df" l)) :=
  mem_without (mem_without (mem_without hq h3) h2) h1

theorem winL_fresh {add : Nat → Option Nat} {Y : Nat} {y : String} (h3 : y ≠ "df") (h4 : y ≠ "dh") (h5 : y ≠ "dl") :
    Fresh y (winL add Y) = true := by
  simp only [winL, Fresh, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true, bne_iff_ne, ne_eq]
  exact ⟨fun e => h3 e.symm, fun e => h4 e.symm, fun e => h5 e.symm⟩

/-- What `leafClass` adds at `x`: `x + 1`, its byte in class `k`. -/
def classAdd (S : Nat → Bool) (bytes : List (BitVec 8)) (k : Nat) : Nat → Option Nat :=
  leafAdd S bytes.length (fun x => classBit k (bytes[x]!).toNat) (· + 1)

theorem classAdd_small {S : Nat → Bool} {bytes : List (BitVec 8)} {k : Nat} (hlen : bytes.length ≤ inputMax) :
    ∀ x e, classAdd S bytes k x = some e → e ≤ inputMax := fun x e h => by
  simp only [classAdd, leafAdd] at h
  split at h
  · rename_i hc; cases h; simp only [Bool.and_eq_true, decide_eq_true_eq] at hc; omega
  · cases h

/-- **A position added** at the end of a leaf's body: its bit set in slot `kd`, the window grown. The window's locals
are those after `X`. -/
theorem addAt_frag (o : Oracle σ) {ofs : Nat} {A : Word} {s0 : PancakeState σ} (hA : Area ofs A s0) {kd : Nat}
    (hkd : kd < slots) {bytes : List (BitVec 8)} (hlen : bytes.length ≤ inputMax) {m1 : Word → Word}
    (hr : Reads s0 A bytes m1) {add : Nat → Option Nat} (hsm : ∀ x e, add x = some e → e ≤ inputMax)
    {X Y : Nat} (hadd : add X = some Y) {L0 lv pre : List (String × Value)}
    (ha : L0.lookup "a" = some A) (hq : L0.lookup "q" = some (at_ A (off kd)))
    (hfr : ∀ y ∈ ["yw", "yj", "df", "dh", "dl"], Fresh y L0 = true) (hlv : ∀ q ∈ lv, q.1 ∈ loopNames)
    (hpre : ∀ q ∈ pre, q.1 ≠ "yw" ∧ q.1 ≠ "yj" ∧ q.1 ≠ "df" ∧ q.1 ≠ "dh" ∧ q.1 ≠ "dl" ∧ q.1 ≠ "a" ∧ q.1 ≠ "q")
    {y : Syntax.PExpr} {Ey : PancakeExp} (hy0 : Lower.lowerExp y = some Ey)
    (hy : ∀ u, RunF s0 (pre ++ (("x", BitVec.ofNat 64 X) :: lv ++ (winL add X ++ L0))) (fun _ => True) u →
      eval u Ey = some (BitVec.ofNat 64 Y)) :
    Frag o (addBit .none y)
      (RunF s0 (pre ++ (("x", BitVec.ofNat 64 X) :: lv ++ (winL add X ++ L0))) (Built A kd add X m1))
      (RunF s0 (pre ++ (("x", BitVec.ofNat 64 X) :: lv ++ (winL add (X + 1) ++ L0))) (Built A kd add (X + 1) m1)) := by
  have hI := inputMax_eq
  have hY : Y ≤ inputMax := hsm X Y hadd
  have hwl := winS_lt add (B := setWords) (by rw [setWords_eq]; decide)
    (fun x e he => by have := hsm x e he; rw [setWords_eq]; omega) X
  rw [setWords_eq] at hwl
  have hws : winS add (X + 1) = ((grow (winS add X).1 (winS add X).2.1 (winS add X).2.2 (Y / 64)).1,
      (grow (winS add X).1 (winS add X).2.1 (winS add X).2.2 (Y / 64)).2, false) := by simp only [winS, hadd]
  -- the list and its lookups
  let lst : List (String × Value) := pre ++ (("x", BitVec.ofNat 64 X) :: lv ++ (winL add X ++ L0))
  have hnl : ∀ y, y ∉ loopNames → Fresh y lv = true := fun y hy => fresh_loop hlv hy
  have lkpre : ∀ y, (∀ q ∈ pre, q.1 ≠ y) → y ≠ "x" → y ∉ loopNames →
      lst.lookup y = (winL add X ++ L0).lookup y := fun y h1 h2 h3 => by
    show (pre ++ _).lookup y = _
    rw [lookup_app_fresh _ (List.all_eq_true.2 fun q hq => by simpa using h1 q hq), List.cons_append,
      ScanRun.lookup_cons_ne h2, lookup_app_fresh _ (hnl y h3)]
  have nw : ∀ y, y ∈ ["a", "q", "df", "dh", "dl"] → (∀ q ∈ pre, q.1 ≠ y) ∧ y ≠ "x" ∧ y ∉ loopNames := by
    intro y hy
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    refine ⟨fun q hq => ?_, by rcases hy with rfl | rfl | rfl | rfl | rfl <;> decide,
      by rcases hy with rfl | rfl | rfl | rfl | rfl <;> simp [loopNames]⟩
    have := hpre q hq
    rcases hy with rfl | rfl | rfl | rfl | rfl <;> simp_all
  have lkL : ∀ y v, y ∈ ["a", "q"] → L0.lookup y = some v → lst.lookup y = some v := fun y v hy h => by
    obtain ⟨n1, n2, n3⟩ := nw y (by simp at hy; rcases hy with rfl | rfl <;> simp)
    rw [lkpre y n1 n2 n3, lookup_app_fresh _ (winL_fresh (by simp at hy; rcases hy with rfl | rfl <;> decide)
      (by simp at hy; rcases hy with rfl | rfl <;> decide) (by simp at hy; rcases hy with rfl | rfl <;> decide)), h]
  have lkw : ∀ y v, y ∈ ["df", "dh", "dl"] → (winL add X).lookup y = some v → lst.lookup y = some v :=
    fun y v hy h => by
      obtain ⟨n1, n2, n3⟩ := nw y (by simp at hy; rcases hy with rfl | rfl | rfl <;> simp)
      rw [lkpre y n1 n2 n3]; exact lookup_app_some _ h
  have fy : ∀ y, y ∈ ["yw", "yj"] → Fresh y lst = true := fun y hy => by
    have h0 : y ∉ loopNames := by simp at hy; rcases hy with rfl | rfl <;> simp [loopNames]
    refine fresh_app (List.all_eq_true.2 fun q hq => ?_) (ScanRun.fresh_cons (fun e => h0 (e ▸ by simp [loopNames]))
      (fresh_app (hnl y h0) (fresh_app (winL_fresh (by simp at hy; rcases hy with rfl | rfl <;> decide)
        (by simp at hy; rcases hy with rfl | rfl <;> decide) (by simp at hy; rcases hy with rfl | rfl <;> decide))
        (hfr y (by simp at hy; rcases hy with rfl | rfl <;> simp)))))
    have := hpre q hq
    simp at hy; rcases hy with rfl | rfl <;> simp [this.1, this.2.1]
  have hlowA : LowKK (addBit .none y) := lowKK_append (lowKK_append (xs := [_, _, _])
    (lowKK_append (xs := [_]) (lowKK_dec (by simp only [Lower.lowerExp, hy0]; rfl)) (lowKK_append (xs := [_])
      (lowK_any _ (k := .skip) rfl) (lowKK_dec (by simp only [Syntax.eAnd, Lower.lowerExp, hy0]; rfl))))
    (lowK_any _ (k := .skip) rfl)) (lowK_any _ (k := .skip) rfl)
  refine frag_conseq (P0 := fun u => ∃ M, (fun M u => RunF s0 lst (· = M) u ∧ Built A kd add X m1 M) M u)
    (frag_exists hlowA fun M => ?_) (fun u h => ⟨u.memory, ⟨h.1, rfl⟩, h.2⟩) fun _ h => h
  by_cases hM : ¬Built A kd add X m1 M
  · exact frag_unsat hlowA fun u h => hM h.2
  have hM : Built A kd add X m1 M := Classical.not_not.1 hM
  have hrM := reads_built hkd hA.hA hlen hr hM.rest
  have wdl : (winL add X).lookup "dl" = some (BitVec.ofNat 64 (winS add X).1) := by
    simp only [winL]; rw [ScanRun.lookup_cons_ne (by decide), ScanRun.lookup_cons_ne (by decide), lookup_head]
  have wdh : (winL add X).lookup "dh" = some (BitVec.ofNat 64 (winS add X).2.1) := by
    simp only [winL]; rw [ScanRun.lookup_cons_ne (by decide), lookup_head]
  have wdf : (winL add X).lookup "df" = some (bw (winS add X).2.2) := by simp only [winL]; rw [lookup_head]
  refine frag_conseq (addBit_frag o hA hkd (l := lst) (lkL "a" A (by simp) ha) (lkL "q" _ (by simp) hq) hy0
    (Y := Y) (by rw [setWords_eq]; omega) (fun u h => hy u h) (fy "yw" (by simp)) (fy "yj" (by simp))
    (by rw [setWords_eq]; exact hwl.1) (by rw [setWords_eq]; exact hwl.2) (lkw "dl" _ (by simp) wdl)
    (lkw "dh" _ (by simp) wdh) (lkw "df" _ (by simp) wdf) hrM.pows) (fun u h => h.1) fun u h => ?_
  refine ⟨(runF_mono h (fun q hq => ?_) (fun _ _ => trivial)).1, by rw [h.2]; exact built_add hkd hM hadd (by
    rw [setWords_eq]; omega)⟩
  have t3 : ∀ q', q' ∈ lst → q'.1 ≠ "dl" → q'.1 ≠ "dh" → q'.1 ≠ "df" → q' ∈ ("df", bw false) ::
      ("dh", BitVec.ofNat 64 (grow (winS add X).1 (winS add X).2.1 (winS add X).2.2 (Y / 64)).2) ::
      ("dl", BitVec.ofNat 64 (grow (winS add X).1 (winS add X).2.1 (winS add X).2.2 (Y / 64)).1) ::
      without "dl" (without "dh" (without "df" lst)) := fun q' h' a1 a2 a3 =>
    List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (mem_withoutW h' a1 a2 a3)))
  rcases List.mem_append.1 hq with hq | hq
  · have := hpre q hq
    exact t3 q (List.mem_append_left _ hq) this.2.2.2.2.1 this.2.2.2.1 this.2.2.1
  rw [List.cons_append] at hq
  rcases List.mem_cons.1 hq with rfl | hq
  · exact t3 _ (List.mem_append_right _ (List.mem_cons_self ..)) (by simp) (by simp) (by simp)
  rcases List.mem_append.1 hq with hq | hq
  · have hn := hlv q hq
    exact t3 q (List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_append_left _ hq)))
      (fun e => by rw [e] at hn; simp [loopNames] at hn) (fun e => by rw [e] at hn; simp [loopNames] at hn)
      (fun e => by rw [e] at hn; simp [loopNames] at hn)
  rcases List.mem_append.1 hq with hq | hq
  · rw [winL, hws] at hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact List.mem_cons_self ..
    · exact List.mem_cons_of_mem _ (List.mem_cons_self ..)
    · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
  · exact t3 q (List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_append_right _
      (List.mem_append_right _ hq)))) (ScanRun.fresh_ne (hfr "dl" (by simp)) q hq)
      (ScanRun.fresh_ne (hfr "dh" (by simp)) q hq) (ScanRun.fresh_ne (hfr "df" (by simp)) q hq)

/-- **A byte of a class** (`classBody`): position `x + 1` added when the byte at `x` is in class `k`. -/
theorem classBody_frag (o : Oracle σ) {ofs : Nat} {A : Word} {s0 : PancakeState σ} (hA : Area ofs A s0)
    {kd k : Nat} (hkd : kd < slots) (hk : k < classes.length) {S : Nat → Bool} {bytes : List (BitVec 8)}
    (hlen : bytes.length ≤ inputMax) {m1 : Word → Word} (hr : Reads s0 A bytes m1)
    {L0 : List (String × Value)} (ha : L0.lookup "a" = some A) (hq : L0.lookup "q" = some (at_ A (off kd)))
    (ht : L0.lookup "t" = some (at_ A (aClass + 32 * k)))
    (hfr : ∀ y ∈ ["b", "bw", "yw", "yj", "df", "dh", "dl"], Fresh y L0 = true)
    (X : Nat) (lv : List (String × Value)) (hlv : ∀ q ∈ lv, q.1 ∈ loopNames) (hS : S X = true)
    (hX : X < bytes.length) :
    Frag o (classBody .none)
      (RunF s0 (("x", BitVec.ofNat 64 X) :: lv ++ (winL (classAdd S bytes k) X ++ L0))
        (Built A kd (classAdd S bytes k) X m1))
      (RunF s0 (("x", BitVec.ofNat 64 X) :: lv ++ (winL (classAdd S bytes k) (X + 1) ++ L0))
        (Built A kd (classAdd S bytes k) (X + 1) m1)) := by
  let add := classAdd S bytes k
  let B := (bytes[X]!).toNat
  have hB : B < 256 := (bytes[X]!).isLt
  -- names
  have nl : ∀ y, y ∉ loopNames → Fresh y lv = true := fun y hy => fresh_loop hlv hy
  have fL : ∀ Y y, y ∈ ["b", "bw", "yw", "yj"] →
      Fresh y (("x", BitVec.ofNat 64 X) :: lv ++ (winL add Y ++ L0)) = true :=
    fun Y y hy => by
      have h1 : y ∉ loopNames := by simp at hy; rcases hy with rfl | rfl | rfl | rfl <;> simp [loopNames]
      have h2 : Fresh y L0 = true := hfr y (by simp at hy; rcases hy with rfl | rfl | rfl | rfl <;> simp)
      have h3 : Fresh y (winL add Y) = true := by
        simp at hy; rcases hy with rfl | rfl | rfl | rfl <;> simp [winL, Fresh]
      exact ScanRun.fresh_cons (fun e => h1 (e ▸ by simp [loopNames])) (fresh_app (nl y h1) (fresh_app h3 h2))
  have lk : ∀ Y y, y ≠ "x" → y ∉ loopNames → y ≠ "df" → y ≠ "dh" → y ≠ "dl" →
      (("x", BitVec.ofNat 64 X) :: lv ++ (winL add Y ++ L0)).lookup y = L0.lookup y := by
    intro Y y h1 h2 h3 h4 h5
    rw [List.cons_append, ScanRun.lookup_cons_ne h1, lookup_app_fresh _ (nl y h2),
      lookup_app_fresh _ (winL_fresh h3 h4 h5)]
  have ns : ∀ y, y ∈ ["a", "q", "t"] → y ≠ "x" ∧ y ∉ loopNames ∧ y ≠ "df" ∧ y ≠ "dh" ∧ y ≠ "dl" := by
    intro y hy; simp at hy; rcases hy with rfl | rfl | rfl <;> simp [loopNames]
  have ha0 := (lk X "a" (ns "a" (by simp)).1 (ns "a" (by simp)).2.1 (ns "a" (by simp)).2.2.1
    (ns "a" (by simp)).2.2.2.1 (ns "a" (by simp)).2.2.2.2).trans ha
  have ht0 := (lk X "t" (ns "t" (by simp)).1 (ns "t" (by simp)).2.1 (ns "t" (by simp)).2.2.1
    (ns "t" (by simp)).2.2.2.1 (ns "t" (by simp)).2.2.2.2).trans ht
  have hx0 : (("x", BitVec.ofNat 64 X) :: lv ++ (winL add X ++ L0)).lookup "x" = some (BitVec.ofNat 64 X) := by
    rw [List.cons_append, lookup_head]
  have hrd : ∀ u, RunF s0 (("x", BitVec.ofNat 64 X) :: lv ++ (winL add X ++ L0)) (Built A kd add X m1) u →
      Reads s0 A bytes u.memory := fun u h => reads_built hkd hA.hA hlen hr h.2.rest
  -- the byte at `x`
  refine frag_append (xs := [_]) (runF_dec o rfl (fL X "b" (by simp)) (v := BitVec.ofNat 64 B) fun u h => by
    have hin := (hrd u h).input
    rw [← h.1.memaddrs, ← h.1.be] at hin
    exact inputByte_eval hin (vals_lookup h.1.vals ha0) hX (vals_lookup h.1.vals hx0)) ?_
  -- its word in the class
  have lb : ∀ (l : List (String × Value)), (("b", BitVec.ofNat 64 B) :: l).lookup "b" = some (BitVec.ofNat 64 B) :=
    fun l => lookup_head _ _ _
  refine frag_append (xs := [_]) (runF_dec o rfl (ScanRun.fresh_cons (by decide) (fL X "bw" (by simp)))
    (v := BitVec.ofNat 64 (B / 64)) fun u h => by
      have hb := ev_var (vals_lookup h.1.vals (lb _))
      have e1 := FramerCode.eval_le (a := .const (BitVec.ofNat 64 64)) (x := 64) (y := B) (by decide) (by omega) rfl hb
      have e2 := FramerCode.eval_le (a := .const (BitVec.ofNat 64 128)) (x := 128) (y := B) (by decide) (by omega)
        rfl hb
      have e3 := FramerCode.eval_le (a := .const (BitVec.ofNat 64 192)) (x := 192) (y := B) (by decide) (by omega)
        rfl hb
      have : eval u (.op .add (.op .add (FramerCode.leE (.const (BitVec.ofNat 64 64)) (.var "b"))
          (FramerCode.leE (.const (BitVec.ofNat 64 128)) (.var "b"))) (FramerCode.leE (.const (BitVec.ofNat 64 192))
          (.var "b"))) = some (bw (decide (64 ≤ B)) + bw (decide (128 ≤ B)) + bw (decide (192 ≤ B))) := by
        simp only [eval, e1, e2, e3]
      rw [bw3 hB] at this
      exact this) ?_
  -- the lists around the test
  have l2 : ∀ Y, ∀ q ∈ ("bw", BitVec.ofNat 64 (B / 64)) :: ("b", BitVec.ofNat 64 B) :: ("x", BitVec.ofNat 64 X) ::
      lv ++ (winL add Y ++ L0), q.1 ≠ "yw" ∧ q.1 ≠ "yj" := fun Y q hq => by
    simp only [List.mem_cons, List.cons_append, List.mem_append] at hq
    rcases hq with rfl | rfl | rfl | hq | hq | hq
    · simp
    · simp
    · simp
    · have := hlv q hq; constructor <;> intro e <;> rw [e] at this <;> simp [loopNames] at this
    · simp only [winL, List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl <;> simp
    · exact ⟨fun e => by have := ScanRun.fresh_ne (hfr "yw" (by simp)) q hq; exact this e,
        fun e => by have := ScanRun.fresh_ne (hfr "yj" (by simp)) q hq; exact this e⟩
  have fr2 : ∀ Y y, (y = "yw" ∨ y = "yj") → Fresh y (("bw", BitVec.ofNat 64 (B / 64)) :: ("b", BitVec.ofNat 64 B) ::
      ("x", BitVec.ofNat 64 X) :: lv ++ (winL add Y ++ L0)) = true := fun Y y hy =>
    List.all_eq_true.2 fun q hq => by
      have := l2 Y q hq
      rcases hy with rfl | rfl <;> simp [this]
  let Mid : Assn σ := RunF s0 (("bw", BitVec.ofNat 64 (B / 64)) :: ("b", BitVec.ofNat 64 B) ::
    ("x", BitVec.ofNat 64 X) :: lv ++ (winL add (X + 1) ++ L0)) (Built A kd add (X + 1) m1)
  refine frag_conseq (P0' := Mid) ?_ (fun u h => h) fun u h =>
    runF_mono h (fun q hq => List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hq)) fun _ e => e
  let l2 : List (String × Value) := ("bw", BitVec.ofNat 64 (B / 64)) :: ("b", BitVec.ofNat 64 B) ::
    ("x", BitVec.ofNat 64 X) :: lv ++ (winL add X ++ L0)
  have c2 : ∀ y, y ≠ "bw" → y ≠ "b" → l2.lookup y = (("x", BitVec.ofNat 64 X) :: lv ++ (winL add X ++ L0)).lookup y :=
    fun y h1 h2 => by
      show (("bw", BitVec.ofNat 64 (B / 64)) :: ("b", BitVec.ofNat 64 B) :: _).lookup y = _
      rw [ScanRun.lookup_cons_ne h1, ScanRun.lookup_cons_ne h2]; rfl
  have hb2 : l2.lookup "b" = some (BitVec.ofNat 64 B) := by
    show (("bw", BitVec.ofNat 64 (B / 64)) :: ("b", BitVec.ofNat 64 B) :: _).lookup "b" = _
    rw [ScanRun.lookup_cons_ne (by decide), lookup_head]
  have hcond : ∀ u, RunF s0 l2 (Built A kd add X m1) u →
      eval u (.cmp .equal (.cmp .equal (.op .and_ (.loadWord (.op .add (.var "t") (.mul (.var "bw")
        (.const (BitVec.ofNat 64 8))))) (.loadWord (.op .add (.op .add (.var "a") (.const (BitVec.ofNat 64 aPow)))
        (.mul (.op .and_ (.var "b") (.const (BitVec.ofNat 64 63))) (.const (BitVec.ofNat 64 8))))))
        (.const (BitVec.ofNat 64 0))) (.const (BitVec.ofNat 64 0))) = some (bw (classBit k B)) := fun u h => by
    have hrd' := reads_built hkd hA.hA hlen hr h.2.rest
    have hand := and63_eval (y := Syntax.v "b") rfl rfl (Y := B) (by omega) (ev_var (vals_lookup h.1.vals hb2))
    rw [ne0_eval (ev_and (classWord_eval hA h.1.memaddrs hrd'.classes hk (i := B / 64) (by omega)
      (vals_lookup h.1.vals ((c2 "t" (by decide) (by decide)).trans ht0)) (vals_lookup h.1.vals (lookup_head _ _ _)))
      (powAt_eval hA h.1.memaddrs hrd'.pows (vals_lookup h.1.vals ((c2 "a" (by decide) (by decide)).trans ha0))
        (by omega) hand)), class_test _ (by omega)]
    rfl
  have hlowA : LowKK (addBit .none (Syntax.eAdd (Syntax.v "x") (Syntax.n 1))) := lowK_any _ (k := .skip) rfl
  have hBx : B = (bytes[X]!).toNat := rfl
  by_cases hc : classBit k B = true
  · have hadd : add X = some (X + 1) := by
      show leafAdd _ _ _ _ X = _
      simp only [leafAdd, hS, decide_eq_true hX, Bool.true_and, ← hBx, hc, if_true]
    refine frag_ite o rfl (runF_clock _ _ _) (fun u h => ⟨_, hcond u h⟩) ?_
      (fun u y v h hy => by
        have hd : declared (addBit .none (Syntax.eAdd (Syntax.v "x") (Syntax.n 1))) = ["yw", "yj"] := rfl
        rw [hd] at hy
        have : y = "yw" ∨ y = "yj" := by simpa using hy
        exact runF_restore h (fr2 (X + 1) y this) v)
      (frag_unsat (lowK_any _ (k := .skip) rfl) fun u ⟨h, h0⟩ => by rw [hcond u h, hc] at h0; cases h0)
      (noDecl _ rfl)
    have hfr5 : ∀ y ∈ ["yw", "yj", "df", "dh", "dl"], Fresh y L0 = true := fun y hy => hfr y (by
      simp at hy; rcases hy with rfl | rfl | rfl | rfl | rfl <;> simp)
    exact frag_conseq (addAt_frag o hA hkd hlen hr (fun x e he => by have := classAdd_small hlen x e he; omega) hadd
      (lv := lv) (L0 := L0) (pre := [("bw", BitVec.ofNat 64 (B / 64)), ("b", BitVec.ofNat 64 B)]) ha hq hfr5 hlv
      (fun q hq => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
        rcases hq with rfl | rfl <;> simp) (y := Syntax.eAdd (Syntax.v "x") (Syntax.n 1)) rfl
      (fun u h => by simp only [eval, vals_lookup h.1.vals ((c2 "x" (by decide) (by decide)).trans hx0),
        BitVec.ofNat_add]))
      (fun u h => h.1) fun u h => h
  · have hc' : classBit k B = false := by simpa using hc
    have hadd : add X = none := by
      show leafAdd _ _ _ _ X = _
      simp only [leafAdd, ← hBx, hc', Bool.and_false, Bool.false_eq_true, if_false]
    refine frag_ite o rfl (runF_clock _ _ _) (fun u h => ⟨_, hcond u h⟩)
      (frag_unsat hlowA fun u ⟨h, h0⟩ => h0 (by rw [hcond u h, hc']; rfl))
      (fun u y v h hy => by
        have hd : declared (addBit .none (Syntax.eAdd (Syntax.v "x") (Syntax.n 1))) = ["yw", "yj"] := rfl
        rw [hd] at hy
        have : y = "yw" ∨ y = "yj" := by simpa using hy
        exact runF_restore h (fr2 (X + 1) y this) v)
      (frag_nil o fun u ⟨h, _⟩ => ?_) (noDecl _ rfl)
    show RunF s0 (("bw", BitVec.ofNat 64 (B / 64)) :: ("b", BitVec.ofNat 64 B) :: ("x", BitVec.ofNat 64 X) :: lv ++
      (winL add (X + 1) ++ L0)) (Built A kd add (X + 1) m1) u
    rw [winL_skip hadd]
    exact ⟨h.1, built_skip h.2 hadd⟩

/-! ## The class leaf -/

theorem prologue_len (ofs : Nat) (ps : List (String × String)) :
    prologue .none ofs ps true = prologue .none ofs ps ++
      [.dec "nn" (word (Syntax.v "a") aLen), kept "nn" inputMax] := by
  simp [prologue]

theorem below_stop {add : Nat → Option Nat} {X : Nat} (h : ∀ Y, X ≤ Y → add Y = none) :
    ∀ k, below add (X + k) = below add X
  | 0 => rfl
  | k + 1 => funext fun e => by
    rw [← Nat.add_assoc, below_succ, h _ (by omega), congrFun (below_stop h k) e]; simp

/-- Past the last position adding one, the set added stays. -/
theorem below_eq {add : Nat → Option Nat} {X B : Nat} (h : ∀ Y, min X B ≤ Y → add Y = none) :
    below add X = below add B := by
  have e1 := below_stop h (X - min X B)
  have e2 := below_stop h (B - min X B)
  rw [show min X B + (X - min X B) = X by omega] at e1
  rw [show min X B + (B - min X B) = B by omega] at e2
  rw [e1, e2]

/-- What a leaf gives back: 0, slot `kd` holding `T`, every word outside it as in `m0`. -/
def LeafRet (A : Word) (kd : Nat) (T : Nat → Bool) (m0 : Word → Word) : Ret := fun v m =>
  v = 0 ∧ SetAt m A kd T ∧ Frame A kd m0 m

/-- **A leaf's run**: the area, slots and input length, slot `kd` emptied, `head` and the window. Then each position of
slot `ks` goes through `body`. The window is stored, and slot `kd` holds what `add` adds. -/
theorem leaf_frag (o : Oracle σ) {ofs : Nat} {A : Word} {s1 : PancakeState σ} (hA : Area ofs A s1)
    {ks kd : Nat} (hks : ks < slots) (hkd : kd < slots) (hne : ks ≠ kd) {S Sd : Nat → Bool}
    (hS : SetAt s1.memory A ks S) (hSd : SetAt s1.memory A kd Sd) {bytes : List (BitVec 8)}
    (hlen : bytes.length ≤ inputMax) (hn : s1.memory (at_ A aLen) = BitVec.ofNat 64 bytes.length)
    (hr : Reads s1 A bytes s1.memory) {l0 : List (String × Value)}
    (hl0s : l0.lookup "s" = some (BitVec.ofNat 64 ks)) (hl0d : l0.lookup "d" = some (BitVec.ofNat 64 kd))
    (f : ∀ y ∈ ["a", "p", "q", "nn", "cl", "ch", "cw"], Fresh y l0 = true) {head body : List Syntax.PStmt}
    {L0 : List (String × Value)}
    (hhead : Frag o head (RunF s1 (("nn", BitVec.ofNat 64 bytes.length) :: ("q", at_ A (off kd)) ::
        ("p", at_ A (off ks)) :: ("a", A) :: l0) fun m => SetAt m A kd (fun _ => false) ∧ Frame A kd s1.memory m)
      (RunF s1 L0 fun m => SetAt m A kd (fun _ => false) ∧ Frame A kd s1.memory m))
    (hL0 : L0.lookup "p" = some (at_ A (off ks)) ∧ L0.lookup "q" = some (at_ A (off kd)) ∧
      L0.lookup "nn" = some (BitVec.ofNat 64 bytes.length) ∧ L0.lookup "a" = some A)
    (hfr : ∀ y ∈ ["df", "dh", "dl"] ++ loopNames, Fresh y L0 = true)
    {add : Nat → Option Nat} (hnone : ∀ x, (S x = false ∨ bytes.length ≤ x) → add x = none)
    (hsm : ∀ x e, add x = some e → e < 64 * setWords) (hlowB : LowKK body)
    (hdecl : ∀ y ∈ declared body, y ∉ loopNames ∧ y ∉ ["df", "dh", "dl"] ∧ Fresh y L0 = true)
    (hbody : ∀ M0, SetAt M0 A kd (fun _ => false) ∧ Frame A kd s1.memory M0 → Reads s1 A bytes M0 →
      ∀ X (lv : List (String × Value)), (∀ q ∈ lv, q.1 ∈ loopNames) → S X = true → X < bytes.length →
      Frag o body (RunF s1 (("x", BitVec.ofNat 64 X) :: lv ++ (winL add X ++ L0)) (Built A kd add X M0))
        (RunF s1 (("x", BitVec.ofNat 64 X) :: lv ++ (winL add (X + 1) ++ L0)) (Built A kd add (X + 1) M0))) :
    FragR o (LeafRet A kd (below add (64 * setWords)) s1.memory)
      (prologue .none ofs [("s", "p"), ("d", "q")] true ++ clearQ ++ head ++ startWin ++ eachPos body ++ epilogue)
      (RunF s1 l0 (· = s1.memory)) fun _ => False := by
  let l1 : List (String × Value) := ("q", at_ A (off kd)) :: ("p", at_ A (off ks)) :: ("a", A) :: l0
  let l2 : List (String × Value) := ("nn", BitVec.ofNat 64 bytes.length) :: l1
  let G : (Word → Word) → Prop := fun m => SetAt m A kd (fun _ => false) ∧ Frame A kd s1.memory m
  have fr2 : ∀ y, y ∈ ["a", "p", "q", "nn", "cl", "ch", "cw"] → y ∉ ["q", "p", "a", "nn"] → Fresh y l2 = true :=
    fun y hy hn => by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hn
      exact ScanRun.fresh_cons (Ne.symm hn.2.2.2) (ScanRun.fresh_cons (Ne.symm hn.1) (ScanRun.fresh_cons
        (Ne.symm hn.2.1) (ScanRun.fresh_cons (Ne.symm hn.2.2.1) (f y hy))))
  -- the start: the area, the slots, the input's length
  have hpro : Frag o (prologue .none ofs [("s", "p"), ("d", "q")] ++
      [.dec "nn" (word (Syntax.v "a") aLen), kept "nn" inputMax]) (RunF s1 l0 (· = s1.memory))
      (RunF s1 l2 (· = s1.memory)) := by
    refine frag_append (start2_frag o hA (x := "s") (p := "p") (y := "d") (q := "q") (by decide) (by decide)
      (by decide) (by decide) hks hkd (l := l0) hl0s hl0d (f "a" (by simp)) (f "p" (by simp))
      (ScanRun.fresh_cons (by decide) (ScanRun.fresh_cons (by decide) (f "q" (by simp))))) ?_
    refine frag_append (xs := [_]) (runF_dec o rfl (l := l1) (ScanRun.fresh_cons (by decide) (ScanRun.fresh_cons
      (by decide) (ScanRun.fresh_cons (by decide) (f "nn" (by simp))))) (v := BitVec.ofNat 64 bytes.length)
      fun u h => ?_)
      (kept_frag o (by decide) (runF_clock _ _ _) fun u h =>
        ⟨bytes.length, vals_lookup h.1.vals (lookup_head _ _ _), hlen⟩)
    have hl8 : aLen < aSets + slots * setSize := by
      have := pow_lt; rw [aPow_eq] at this; simp only [aLen]; omega
    have := load_eval hA h.1.memaddrs (y := aLen) hl8 (by decide)
      (E := .op .add (.var "a") (.const (BitVec.ofNat 64 aLen)))
      (by simp only [eval, vals_lookup h.1.vals (by
        rw [ScanRun.lookup_cons_ne (by decide), ScanRun.lookup_cons_ne (by decide), lookup_head] :
        l1.lookup "a" = some A)]; rfl)
    rw [h.2, hn] at this
    exact this
  have hclear : Frag o clearQ (RunF s1 l2 (· = s1.memory)) (RunF s1 l2 G) :=
    clearQ_frag o hA hkd (l := l2) (by rw [ScanRun.lookup_cons_ne (by decide), lookup_head])
      (fr2 "cl" (by simp) (by decide)) (fr2 "ch" (by simp) (by decide)) (fr2 "cw" (by simp) (by decide)) hSd
  have hwin : Frag o startWin (RunF s1 L0 G) (RunF s1 (winL add 0 ++ L0) G) := by
    refine frag_append (xs := [_]) (runF_dec o rfl (hfr "dl" (by simp)) (v := BitVec.ofNat 64 1) fun u h => rfl) ?_
    refine frag_append (xs := [_]) (runF_dec o rfl (ScanRun.fresh_cons (by decide) (hfr "dh" (by simp)))
      (v := BitVec.ofNat 64 0) fun u h => rfl) ?_
    refine frag_conseq (runF_dec o rfl (ScanRun.fresh_cons (by decide) (ScanRun.fresh_cons (by decide)
      (hfr "df" (by simp)))) (v := BitVec.ofNat 64 1) fun u h => rfl) (fun u h => h)
      fun u h => runF_mono h (fun q hq => ?_) fun _ e => e
    simp only [winL, winS, List.cons_append, List.nil_append, List.mem_cons] at hq
    rcases hq with rfl | rfl | rfl | hq
    · exact List.mem_cons_self ..
    · exact List.mem_cons_of_mem _ (List.mem_cons_self ..)
    · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
    · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hq))
  -- each position of `S`
  have hlowE : LowKK (eachPos body) := lowKK_eachPos hlowB
  have lkL : ∀ X y v, y ≠ "df" → y ≠ "dh" → y ≠ "dl" → L0.lookup y = some v →
      (winL add X ++ L0).lookup y = some v := fun X y v h1 h2 h3 h =>
    (lookup_app_fresh _ (winL_fresh h1 h2 h3)).trans h
  have hM0 : ∀ M0, G M0 → ∀ x, x < aSets → M0 (at_ A x) = s1.memory (at_ A x) := fun M0 hG x hx =>
    hG.2 _ (notInSlot hkd hx)
  have hEach : ∀ M0, G M0 → Each A ks bytes.length S (fun X => winL add X ++ L0)
      (fun X => Built A kd add X M0) := fun M0 hG => by
    have hrM := reads_keep hA.hA hlen hr (hM0 M0 hG)
    refine ⟨fun X => lkL X "p" _ (by decide) (by decide) (by decide) hL0.1,
      fun X => lkL X "nn" _ (by decide) (by decide) (by decide) hL0.2.2.1,
      fun X => lkL X "a" _ (by decide) (by decide) (by decide) hL0.2.2.2, fun X y hy => ?_, fun X m hb => ?_,
      fun X h => ?_⟩
    · have hy' := hy
      simp only [loopNames, List.mem_cons, List.not_mem_nil, or_false] at hy'
      exact fresh_app (winL_fresh (by rcases hy' with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
        (by rcases hy' with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
        (by rcases hy' with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide))
        (hfr y (List.mem_append_right _ hy))
    · have hrm := reads_built hkd hA.hA hlen hrM hb.rest
      refine ⟨setAt_frame hS fun i hi => ?_, hrm.masks, hrm.pows⟩
      rw [hb.rest _ fun w hw e => hne (slotW_inj hks hkd hi (bitIdx hw) e).1]
      exact hG.2 _ fun ⟨i', hi', e⟩ => hne (slotW_inj hks hkd hi hi' e).1
    · have ha : add X = none := hnone X h
      exact ⟨by show winL add (X + 1) ++ L0 = winL add X ++ L0; rw [winL_skip ha], fun m hb => built_skip hb ha⟩
  have heach : Frag o (eachPos body) (RunF s1 (winL add 0 ++ L0) G)
      (fun u => ∃ M0, G M0 ∧ ∃ X, (∀ Y, X ≤ Y → S Y = false) ∧
        RunF s1 (winL add X ++ L0) (Built A kd add X M0) u) := by
    refine frag_conseq (P0 := fun u => ∃ M0, (fun M0 u => RunF s1 (winL add 0 ++ L0) (· = M0) u ∧ G M0) M0 u)
      (frag_exists hlowE fun M0 => ?_) (fun u h => ⟨u.memory, ⟨h.1, rfl⟩, h.2⟩) fun _ h => h
    by_cases hG : ¬G M0
    · exact frag_unsat hlowE fun u h => hG h.2
    have hG : G M0 := Classical.not_not.1 hG
    have hrM := reads_keep hA.hA hlen hr (hM0 M0 hG)
    refine frag_conseq (eachPos_frag o hA hks (hEach M0 hG) hlen hlowB (fun X y hy => ?_)
      (hbody M0 hG hrM) (built_zero fun w hw j hj => hG.1.bits w hw j hj)) (fun u h => h.1) fun u h => ⟨M0, hG, h⟩
    obtain ⟨h1, h2, h3⟩ := hdecl y hy
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at h2
    exact ⟨h1, fresh_app (winL_fresh h2.1 h2.2.1 h2.2.2) h3⟩
  -- the end: the window stored
  let T := below add (64 * setWords)
  let Fin : (Word → Word) → Prop := fun m => SetAt m A kd T ∧ Frame A kd s1.memory m
  have hlowS : LowKK [.store (Syntax.atOff (Syntax.v "q") sLo) (Syntax.v "dl"),
      .store (Syntax.atOff (Syntax.v "q") sHi) (Syntax.v "dh")] := lowK_any _ (k := .skip) rfl
  have hstores : Frag o [.store (Syntax.atOff (Syntax.v "q") sLo) (Syntax.v "dl"),
      .store (Syntax.atOff (Syntax.v "q") sHi) (Syntax.v "dh")]
      (fun u => ∃ M0, G M0 ∧ ∃ X, (∀ Y, X ≤ Y → S Y = false) ∧
        RunF s1 (winL add X ++ L0) (Built A kd add X M0) u) (RunF s1 [] Fin) := by
    refine frag_conseq (P0 := fun u => ∃ p : (Word → Word) × Nat, (fun p u => G p.1 ∧ (∀ Y, p.2 ≤ Y → S Y = false) ∧
        RunF s1 (winL add p.2 ++ L0) (Built A kd add p.2 p.1) u) p u)
      (frag_exists hlowS fun ⟨M0, X⟩ => ?_) (fun u ⟨M0, hG, X, hX, h⟩ => ⟨(M0, X), hG, hX, h⟩) fun _ h => h
    by_cases hc : ¬(G M0 ∧ ∀ Y, X ≤ Y → S Y = false)
    · exact frag_unsat hlowS fun u h => hc ⟨h.1, h.2.1⟩
    obtain ⟨hG, hX⟩ := Classical.not_not.1 hc
    have wq : ∀ Y, (winL add Y ++ L0).lookup "q" = some (at_ A (off kd)) := fun Y =>
      lkL Y "q" _ (by decide) (by decide) (by decide) hL0.2.1
    have wdl : (winL add X ++ L0).lookup "dl" = some (BitVec.ofNat 64 (winS add X).1) := by
      refine lookup_app_some _ ?_
      simp only [winL]; rw [ScanRun.lookup_cons_ne (by decide), ScanRun.lookup_cons_ne (by decide), lookup_head]
    have wdh : (winL add X ++ L0).lookup "dh" = some (BitVec.ofNat 64 (winS add X).2.1) := by
      refine lookup_app_some _ ?_
      simp only [winL]; rw [ScanRun.lookup_cons_ne (by decide), lookup_head]
    have hoff := off_lt hkd 8 (by rw [setSize_eq]; omega)
    have hoff0 := off_lt hkd 0 (by rw [setSize_eq]; omega)
    refine frag_conseq (P0 := RunF s1 (winL add X ++ L0) (Built A kd add X M0))
      (P0' := RunF s1 (winL add X ++ L0) Fin) ?_ (fun u h => h.2.2)
      fun u h => runF_mono h (fun _ h => nomatch h) fun _ e => e
    refine frag_append (xs := [_]) (runF_store o hA rfl rfl (y := off kd) (by omega) (off_mod kd)
      (fun u h => ev_var (vals_lookup h.1.vals (wq X))) (val := fun _ => BitVec.ofNat 64 (winS add X).1)
      (fun u h => ev_var (vals_lookup h.1.vals wdl))
      (G := fun m => ∃ m', Built A kd add X M0 m' ∧ m = upd m' (at_ A (off kd)) (BitVec.ofNat 64 (winS add X).1))
      fun m hm => ⟨m, hm, rfl⟩) ?_
    refine frag_conseq (runF_store o hA rfl rfl (y := off kd + 8) hoff (by have := off_mod kd; omega)
      (fun u h => by simp only [eval, vals_lookup h.1.vals (wq X)]; rw [at_add]; rfl)
      (val := fun _ => BitVec.ofNat 64 (winS add X).2.1) (fun u h => ev_var (vals_lookup h.1.vals wdh))
      (G := Fin) fun m ⟨m', hb, e⟩ => ?_) (fun u h => h) fun u h => h
    subst e
    have hs8 : at_ A (off kd + 8) = slotW A kd 1 := by rw [slotW, Nat.mul_one]
    rw [hs8, ← slotW_zero]
    have hT : below add X = T := below_eq fun Y hY => hnone Y (.inl (by
      by_cases hXY : X ≤ Y
      · exact hX Y hXY
      · cases e : S Y
        · rfl
        · have := hS.small Y e; omega))
    refine ⟨hT ▸ built_setAt hkd hb hsm, fun a ha => ?_⟩
    have h0 : a ≠ slotW A kd 0 := fun e => ha ⟨0, by decide, e⟩
    have h1 : a ≠ slotW A kd 1 := fun e => ha ⟨1, by decide, e⟩
    rw [upd_ne _ h1, upd_ne _ h0, hb.rest a fun w hw e => ha ⟨2 + w, bitIdx hw, e⟩]
    exact hG.2 a ha
  rw [prologue_len]
  refine fragR_append (fragR_append (fragR_append (fragR_append (fragR_append (fragR_of hpro) (fragR_of hclear))
    (fragR_of hhead)) (fragR_of hwin)) (fragR_of heach)) ?_
  show FragR o _ ([_, _] ++ [.ret (Syntax.n 0)]) _ _
  exact fragR_append (fragR_of hstores) (fragR_ret o rfl fun u h => ⟨0, rfl, rfl, h.2.1, h.2.2⟩)

theorem classAdd_none {S : Nat → Bool} {bytes : List (BitVec 8)} {k x : Nat} (h : S x = false ∨ bytes.length ≤ x) :
    classAdd S bytes k x = none := by
  simp only [classAdd, leafAdd]
  rcases h with h | h
  · simp [h]
  · simp [show ¬x < bytes.length by omega]

/-- **`leafClass` adds the positions past those of `S` whose byte is in class `k`** to slot `kd`, emptied first. Every
word outside it is kept. -/
theorem leafClass_ok (o : Oracle σ) {ofs : Nat} {A : Word} {s1 : PancakeState σ} (hA : Area ofs A s1)
    {ks kd k : Nat} (hks : ks < slots) (hkd : kd < slots) (hne : ks ≠ kd) (hk : k < classes.length)
    (hs : s1.locals "s" = some (BitVec.ofNat 64 ks)) (hd : s1.locals "d" = some (BitVec.ofNat 64 kd))
    (hkl : s1.locals "k" = some (BitVec.ofNat 64 k)) {S Sd : Nat → Bool} (hS : SetAt s1.memory A ks S)
    (hSd : SetAt s1.memory A kd Sd) {bytes : List (BitVec 8)} (hlen : bytes.length ≤ inputMax)
    (hn : s1.memory (at_ A aLen) = BitVec.ofNat 64 bytes.length) (hr : Reads s1 A bytes s1.memory) :
    ∃ body, Lower.lower (leafClass .none ofs) = some body ∧
      SafeR o (fun s => s = s1) body (LeafRet A kd (below (classAdd S bytes k) (64 * setWords)) s1.memory)
        fun _ => False := by
  refine body_of ?_
  dsimp only [leafClass]
  let l0 : List (String × Value) := [("s", BitVec.ofNat 64 ks), ("d", BitVec.ofNat 64 kd), ("k", BitVec.ofNat 64 k)]
  let l2 : List (String × Value) := ("nn", BitVec.ofNat 64 bytes.length) :: ("q", at_ A (off kd)) ::
    ("p", at_ A (off ks)) :: ("a", A) :: l0
  let L0 : List (String × Value) := ("t", at_ A (aClass + 32 * k)) :: l2
  let G : (Word → Word) → Prop := fun m => SetAt m A kd (fun _ => false) ∧ Frame A kd s1.memory m
  have hentry : ∀ s, s = s1 → RunF s1 l0 (· = s1.memory) s := entry_run (fun q hq => by
    simp only [l0, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact hs
    · exact hd
    · exact hkl) rfl
  have hhead : Frag o classHead (RunF s1 l2 G) (RunF s1 L0 G) := by
    refine frag_append (xs := [_]) (kept_frag o (by have := classes_le; omega) (runF_clock _ _ _) fun u h =>
      ⟨k, vals_lookup h.1.vals (rfl : l2.lookup "k" = some (BitVec.ofNat 64 k)), by omega⟩) ?_
    refine runF_dec o rfl rfl (v := at_ A (aClass + 32 * k)) fun u h => ?_
    simp only [eval, vals_lookup h.1.vals (rfl : l2.lookup "a" = some A),
      vals_lookup h.1.vals (rfl : l2.lookup "k" = some (BitVec.ofNat 64 k))]
    rw [← BitVec.ofNat_mul]
    show some (at_ A aClass + BitVec.ofNat 64 (k * 32)) = _
    rw [at_add]; exact congrArg (fun y => some (at_ A y)) (by omega)
  have hfr0 : ∀ y ∈ ["b", "bw", "yw", "yj", "df", "dh", "dl"], Fresh y L0 = true := by
    intro y hy; simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  refine fragR_conseq (P0 := RunF s1 l0 (· = s1.memory)) (leaf_frag o hA hks hkd hne hS hSd hlen hn hr (l0 := l0)
    rfl rfl (by intro y hy; simp at hy; rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl) (L0 := L0)
    hhead ⟨rfl, rfl, rfl, rfl⟩ (by intro y hy; simp [loopNames] at hy; rcases hy with rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl <;> rfl) (fun x h => classAdd_none h) (fun x e he => by
        have := classAdd_small hlen x e he; rw [setWords_eq]; rw [inputMax_eq] at this; omega)
    (lowK_any _ (k := .skip) rfl) (fun y hy => by
      rw [show declared (classBody .none) = ["b", "bw"] from rfl] at hy
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
      rcases hy with rfl | rfl <;> exact ⟨by simp [loopNames], by simp, rfl⟩)
    fun M0 _ hrM X lv hlv hSX hX => classBody_frag o hA hkd hk hlen hrM rfl rfl rfl hfr0 X lv hlv hSX hX)
    hentry fun _ h => h

/-! ## A string -/

theorem atOff_texts : Syntax.atOff (Syntax.v "a") aTexts = Syntax.eAdd (Syntax.v "a") (Syntax.n aTexts) := by
  unfold Syntax.atOff; rw [if_neg (by rw [beq_iff_eq]; exact aTexts_ne)]

theorem atOff_textBytes :
    Syntax.atOff (Syntax.v "a") aTextBytes = Syntax.eAdd (Syntax.v "a") (Syntax.n aTextBytes) := by
  unfold Syntax.atOff; rw [if_neg (by rw [beq_iff_eq]; exact aTextBytes_ne)]

/-- A byte of string `k`, its address worked out to `aTextBytes + textOff k + i`. -/
theorem textByte_eval {u : PancakeState σ} {A : Word} (ht : TextsAt u.memory u.memaddrs u.be A) {k i : Nat}
    (hk : k < texts.length) (hi : i < (textAt k).1.length) {E : PancakeExp}
    (hE : eval u E = some (at_ A (aTextBytes + textOff k + i))) :
    eval u (.loadByte E) = some (BitVec.ofNat 64 ((textAt k).1[i]!)) := by
  have hl := (ht k hk).2.2.2 i hi
  have hb : (textAt k).1[i]! < 256 := textAt_byte hk hi
  generalize (textAt k).1[i]! = b at hl hb ⊢
  rw [eval, hE]
  dsimp only
  rw [hl]
  dsimp only
  congr 1
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega

theorem one_and_bw (a : Bool) : BitVec.ofNat 64 1 &&& bw a = bw a := by cases a <;> decide

theorem mul32_bw (a : Bool) : BitVec.ofNat 64 32 * bw a = BitVec.ofNat 64 (32 * if a then 1 else 0) := by
  cases a <;> decide

/-- The program's fold of a byte, `cf` a flag. -/
theorem foldB_word (cf : Bool) (B : Nat) :
    BitVec.ofNat 64 B + BitVec.ofNat 64 32 * (BitVec.ofNat 64 1 &&& (bw cf &&& (bw (decide (65 ≤ B)) &&&
      bw (decide (B ≤ 90))))) = BitVec.ofNat 64 (foldB cf B) := by
  rw [bw_and, bw_and, one_and_bw, mul32_bw, ← BitVec.ofNat_add]; rfl

theorem ev_add {u : PancakeState σ} {a b : PancakeExp} {x y : Word} (ha : eval u a = some x)
    (hb : eval u b = some y) : eval u (.op .add a b) = some (x + y) := by simp only [eval, ha, hb]

theorem ev_mul {u : PancakeState σ} {a b : PancakeExp} {x y : Word} (ha : eval u a = some x)
    (hb : eval u b = some y) : eval u (.mul a b) = some (x * y) := by simp only [eval, ha, hb]

/-- Two words told apart, as `ne` tells them. -/
theorem ne_eval {u : PancakeState σ} {a b : PancakeExp} {x y : Word} (ha : eval u a = some x)
    (hb : eval u b = some y) :
    eval u (.cmp .equal (.cmp .equal a b) (.const (BitVec.ofNat 64 0))) = some (bw (decide (x ≠ y))) := by
  simp only [eval, ha, hb]
  by_cases h : x = y <;> simp [h, bw]

/-- Whether the first `n` bytes of string `k` lie at `x`, as `leafText` compares them. -/
def okTo (bytes : List (BitVec 8)) (k x n : Nat) : Bool :=
  (List.range n).all fun j => foldB (textAt k).2 (bytes[x + j]!).toNat == (textAt k).1[j]!

theorem okTo_succ (bytes : List (BitVec 8)) (k x n : Nat) :
    okTo bytes k x (n + 1) = (okTo bytes k x n && foldB (textAt k).2 (bytes[x + n]!).toNat == (textAt k).1[n]!) := by
  simp [okTo, List.range_succ, List.all_append]

/-- **A string compared** (`textCmp`): `ok` stays set exactly when string `k` lies at `x`. For a caseless string,
letters match in either case. -/
theorem textCmp_frag (o : Oracle σ) {s0 : PancakeState σ} {A : Word} {k : Nat} (hk : k < texts.length)
    {bytes : List (BitVec 8)} {X : Nat} (hX : X + (textAt k).1.length ≤ bytes.length) (hlen : bytes.length ≤ inputMax)
    {base : List (String × Value)} {F : (Word → Word) → Prop}
    (hF : ∀ m, F m → InputAt m s0.memaddrs s0.be A bytes ∧ TextsAt m s0.memaddrs s0.be A)
    (ha : base.lookup "a" = some A) (hx : base.lookup "x" = some (BitVec.ofNat 64 X))
    (hl : base.lookup "len" = some (BitVec.ofNat 64 (textAt k).1.length))
    (hoff : base.lookup "off" = some (BitVec.ofNat 64 (textOff k)))
    (hcf : base.lookup "cf" = some (bw (textAt k).2))
    (hfr : ∀ y ∈ ["i", "ok", "b", "lb"], Fresh y base = true) :
    Frag o [textCmp .none]
      (RunF s0 (("i", BitVec.ofNat 64 0) :: ("ok", bw true) :: base) F)
      (RunF s0 (("i", BitVec.ofNat 64 (textAt k).1.length) :: ("ok", bw (okTo bytes k X (textAt k).1.length)) ::
        base) F) := by
  rw [textCmp, atOff_textBytes]
  have hI := inputMax_eq
  have hsh := textAt_short hk
  have htm : textMax = 63 := rfl
  generalize hn : (textAt k).1.length = len at hX hl hsh ⊢
  let li (i : Nat) : List (String × Value) := ("i", BitVec.ofNat 64 i) :: ("ok", bw (okTo bytes k X i)) :: base
  let I (i : Nat) : Assn σ := fun u => RunF s0 (li i) F u ∧ i ≤ len
  have hIc : ∀ i, Safe.ClockFree (I i) := fun i s c h => ⟨runF_clock _ _ _ s c h.1, h.2⟩
  have lb : ∀ i y, y ≠ "i" → y ≠ "ok" → (li i).lookup y = base.lookup y := fun i y h1 h2 => by
    show (("i", _) :: ("ok", _) :: base).lookup y = _
    rw [ScanRun.lookup_cons_ne h1, ScanRun.lookup_cons_ne h2]
  have fb : ∀ i y, y ∈ ["b", "lb"] → Fresh y (li i) = true := fun i y hy => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    have := hfr y (by rcases hy with rfl | rfl <;> simp)
    rcases hy with rfl | rfl <;> exact ScanRun.fresh_cons (by decide) (ScanRun.fresh_cons (by decide) this)
  refine frag_conseq (frag_count o rfl (lowKK_append (xs := [_]) (lowKK_dec rfl) (lowKK_append (xs := [_])
    (lowKK_dec rfl) (lowKK_append (xs := [_]) (lowKK_ite rfl (lowK_any _ (k := .skip) rfl)
      (lowK_any _ (k := .skip) rfl))
      (lowK_any _ (k := .skip) rfl)))) hIc
    (fun i u y v h hy => by
      have : y = "b" ∨ y = "lb" := by simpa [declared, inc] using hy
      exact ⟨runF_restore h.1 (fb i y (by rcases this with rfl | rfl <;> simp)) v, h.2⟩)
    (g := fun i => decide (i < len))
    (fun i u h => FramerCode.eval_lt (by omega) (by omega) (ev_var (vals_lookup h.1.1.vals (lookup_head _ _ _)))
      (ev_var (vals_lookup h.1.1.vals ((lb i "len" (by decide) (by decide)).trans hl))))
    (fun i hg => ?_) 0) (fun u h => ⟨h, Nat.zero_le _⟩) fun u ⟨i, h, hg⟩ => ?_
  rotate_left
  · have : i = len := by have := h.2; simp at hg; omega
    subst this; exact h.1
  have hi : i < len := of_decide_eq_true hg
  let B := (bytes[X + i]!).toNat
  have hB : B < 256 := (bytes[X + i]!).isLt
  let ls (lbv : Value) : List (String × Value) := ("lb", lbv) :: ("b", BitVec.ofNat 64 B) :: li i
  have lkb : ∀ y, y ≠ "i" → y ≠ "ok" → y ≠ "b" → ((("b", BitVec.ofNat 64 B) :: li i)).lookup y = base.lookup y :=
    fun y h1 h2 h3 => by rw [ScanRun.lookup_cons_ne h3, lb i y h1 h2]
  refine frag_conseq (P0 := RunF s0 (li i) F) ?_ (fun u h => h.1) fun u h => ⟨h, by omega⟩
  -- the input's byte at `x + i`
  refine frag_append (xs := [_]) (runF_dec o rfl (fb i "b" (by simp)) (v := BitVec.ofNat 64 B) fun u h => ?_) ?_
  · have hin := (hF _ h.2).1
    rw [← h.1.memaddrs, ← h.1.be] at hin
    refine inputAt_eval hin (Y := X + i) (by omega) ?_
    simp only [eval, vals_lookup h.1.vals ((lb i "a" (by decide) (by decide)).trans ha),
      vals_lookup h.1.vals ((lb i "x" (by decide) (by decide)).trans hx), vals_lookup h.1.vals (lookup_head _ _ _)]
    show some (at_ A aInput + BitVec.ofNat 64 X + BitVec.ofNat 64 i) = _
    rw [at_add, at_add, Nat.add_assoc]
  -- folded
  have hlbf : Fresh "lb" (("b", BitVec.ofNat 64 B) :: li i) = true :=
    ScanRun.fresh_cons (by decide) (fb i "lb" (by simp))
  refine frag_append (xs := [_]) (runF_dec o rfl hlbf (v := BitVec.ofNat 64 (foldB (textAt k).2 B)) fun u h => ?_) ?_
  · have hb := vals_lookup h.1.vals (lookup_head _ _ _ : (("b", BitVec.ofNat 64 B) :: li i).lookup "b" = _)
    have hc := vals_lookup h.1.vals ((lkb "cf" (by decide) (by decide) (by decide)).trans hcf)
    rw [← foldB_word]
    exact ev_add (ev_var hb) (ev_mul rfl (ev_and rfl (ev_and (ev_var hc)
      (ev_and (FramerCode.eval_le (a := .const (BitVec.ofNat 64 65)) (x := 65) (y := B) (by decide) (by omega) rfl
        (ev_var hb)) (FramerCode.eval_le (b := .const (BitVec.ofNat 64 90)) (x := B) (y := 90) (by omega)
          (by decide) (ev_var hb) rfl)))))
  let F' := foldB (textAt k).2 B
  have hF' : F' < 300 := by show foldB _ B < 300; unfold foldB; split <;> omega
  have hil : i < (textAt k).1.length := by omega
  have hsb : (textAt k).1[i]! < 256 := textAt_byte hk hil
  have lk2 : ∀ y, y ≠ "i" → y ≠ "ok" → y ≠ "b" → y ≠ "lb" → (ls (BitVec.ofNat 64 F')).lookup y = base.lookup y :=
    fun y h1 h2 h3 h4 => by
      show (("lb", _) :: ("b", _) :: li i).lookup y = _
      rw [ScanRun.lookup_cons_ne h4, lkb y h1 h2 h3]
  have hli : (ls (BitVec.ofNat 64 F')).lookup "i" = some (BitVec.ofNat 64 i) := by
    show (("lb", _) :: ("b", _) :: ("i", _) :: _).lookup "i" = _
    rw [ScanRun.lookup_cons_ne (by decide), ScanRun.lookup_cons_ne (by decide), lookup_head]
  have hcond : ∀ u, RunF s0 (ls (BitVec.ofNat 64 F')) F u →
      eval u (.cmp .equal (.cmp .equal (.var "lb") (.loadByte (.op .add (.op .add (.op .add (.var "a")
        (.const (BitVec.ofNat 64 aTextBytes))) (.var "off")) (.var "i")))) (.const (BitVec.ofNat 64 0))) =
        some (bw (decide (BitVec.ofNat 64 F' ≠ BitVec.ofNat 64 ((textAt k).1[i]!)))) := fun u h => by
    have ht := (hF _ h.2).2
    rw [← h.1.memaddrs, ← h.1.be] at ht
    exact ne_eval (ev_var (vals_lookup h.1.vals (lookup_head _ _ _))) (textByte_eval ht hk hil (by
      simp only [eval, vals_lookup h.1.vals ((lk2 "a" (by decide) (by decide) (by decide) (by decide)).trans ha),
        vals_lookup h.1.vals ((lk2 "off" (by decide) (by decide) (by decide) (by decide)).trans hoff),
        vals_lookup h.1.vals hli]
      show some (at_ A aTextBytes + BitVec.ofNat 64 (textOff k) + BitVec.ofNat 64 i) = _
      rw [at_add, at_add]))
  have hsucc := okTo_succ bytes k X i
  generalize hc : (textAt k).1[i]! = c at hcond hsucc hsb
  have hwq : (BitVec.ofNat 64 F' = BitVec.ofNat 64 c) ↔ F' = c := by
    constructor
    · intro e; have := congrArg BitVec.toNat e; simp only [BitVec.toNat_ofNat] at this; omega
    · intro e; rw [e]
  let Mid : Assn σ := RunF s0 (("lb", BitVec.ofNat 64 F') :: ("b", BitVec.ofNat 64 B) :: ("i", BitVec.ofNat 64 i) ::
    ("ok", bw (okTo bytes k X (i + 1))) :: base) F
  refine frag_append (xs := [_]) (M := Mid) ?_ ?_
  · by_cases hm : F' = c
    · have e : okTo bytes k X (i + 1) = okTo bytes k X i := by
        rw [hsucc, show (foldB (textAt k).2 (bytes[X + i]!).toNat == c) = true from beq_iff_eq.2 hm, Bool.and_true]
      refine ScanRun.frag_if o rfl (lowK_any _ (k := .skip) rfl) (lowK_any _ (k := .skip) rfl) rfl rfl
        (runF_clock _ _ _) (b := false) (fun u h => by
          rw [hcond u h, decide_eq_false fun h' => h' (hwq.2 hm)]) (fun e => absurd e (by decide))
        fun _ => frag_nil o fun u h => ?_
      show RunF s0 (("lb", _) :: ("b", _) :: ("i", _) :: ("ok", bw (okTo bytes k X (i + 1))) :: base) F u
      rw [e]; exact h
    · have e : okTo bytes k X (i + 1) = false := by
        rw [hsucc, show (foldB (textAt k).2 (bytes[X + i]!).toNat == c) = false from beq_eq_false_iff_ne.2 hm,
          Bool.and_false]
      refine ScanRun.frag_if o rfl (lowK_any _ (k := .skip) rfl) (lowK_any _ (k := .skip) rfl) rfl rfl
        (runF_clock _ _ _) (b := true) (fun u h => by
          rw [hcond u h, decide_eq_true (show BitVec.ofNat 64 F' ≠ BitVec.ofNat 64 c from fun h' => hm (hwq.1 h'))])
        (fun _ => ?_) fun e => absurd e (by decide)
      refine frag_conseq (runF_set o rfl (by
        show (("lb", _) :: ("b", _) :: ("i", _) :: ("ok", _) :: base).lookup "ok" = _
        rw [ScanRun.lookup_cons_ne (by decide), ScanRun.lookup_cons_ne (by decide), ScanRun.lookup_cons_ne (by decide),
          lookup_head]) (v := BitVec.ofNat 64 0) fun u h => rfl) (fun u h => h)
        fun u h => runF_mono h (fun q hq => ?_) fun _ e => e
      rcases List.mem_cons.1 hq with rfl | hq
      · exact List.mem_cons_of_mem _ (mem_without (List.mem_cons_self ..) (by simp))
      rcases List.mem_cons.1 hq with rfl | hq
      · exact List.mem_cons_of_mem _ (mem_without (List.mem_cons_of_mem _ (List.mem_cons_self ..)) (by simp))
      rcases List.mem_cons.1 hq with rfl | hq
      · exact List.mem_cons_of_mem _ (mem_without (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
          (List.mem_cons_self ..))) (by simp))
      rcases List.mem_cons.1 hq with rfl | hq
      · rw [e]; exact List.mem_cons_self ..
      · exact List.mem_cons_of_mem _ (mem_without (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
          (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hq)))) (ScanRun.fresh_ne (hfr "ok" (by simp)) q hq))
  · -- the next byte
    refine frag_conseq (runF_set o rfl (by
      show (("lb", _) :: ("b", _) :: ("i", _) :: _).lookup "i" = _
      rw [ScanRun.lookup_cons_ne (by decide), ScanRun.lookup_cons_ne (by decide), lookup_head])
      (v := BitVec.ofNat 64 (i + 1)) fun u h => ?_) (fun u h => h) fun u h => runF_mono h (fun q hq => ?_) fun _ e => e
    · simp only [eval, vals_lookup h.1.vals (by
        show (("lb", _) :: ("b", _) :: ("i", BitVec.ofNat 64 i) :: _).lookup "i" = _
        rw [ScanRun.lookup_cons_ne (by decide), ScanRun.lookup_cons_ne (by decide), lookup_head]), BitVec.ofNat_add]
    · rcases List.mem_cons.1 hq with rfl | hq
      · exact List.mem_cons_self ..
      rcases List.mem_cons.1 hq with rfl | hq
      · exact List.mem_cons_of_mem _ (mem_without (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
          (List.mem_cons_of_mem _ (List.mem_cons_self ..)))) (by simp))
      · exact List.mem_cons_of_mem _ (mem_without (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
          (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hq)))) (ScanRun.fresh_ne (hfr "i" (by simp)) q hq))

/-- Whether string `k` lies at `x` in the input. -/
def textHere (bytes : List (BitVec 8)) (k x : Nat) : Bool :=
  decide (x + (textAt k).1.length ≤ bytes.length) && okTo bytes k x (textAt k).1.length

/-- What `leafText` adds at `x`: the position past string `k`, when it lies there. -/
def textAdd (S : Nat → Bool) (bytes : List (BitVec 8)) (k : Nat) : Nat → Option Nat :=
  leafAdd S bytes.length (textHere bytes k) (· + (textAt k).1.length)

theorem textAdd_small {S : Nat → Bool} {bytes : List (BitVec 8)} {k : Nat} :
    ∀ x e, textAdd S bytes k x = some e → e ≤ bytes.length := fun x e h => by
  simp only [textAdd, leafAdd, textHere] at h
  split at h
  · rename_i hc; cases h; simp only [Bool.and_eq_true, decide_eq_true_eq] at hc; omega
  · cases h

theorem textAdd_none {S : Nat → Bool} {bytes : List (BitVec 8)} {k x : Nat} (h : S x = false ∨ bytes.length ≤ x) :
    textAdd S bytes k x = none := by
  simp only [textAdd, leafAdd]
  rcases h with h | h
  · simp [h]
  · simp [show ¬x < bytes.length by omega]

theorem lowKK_addBit {y : Syntax.PExpr} {Ey : PancakeExp} (hy0 : Lower.lowerExp y = some Ey) :
    LowKK (addBit .none y) := lowKK_append (lowKK_append (xs := [_, _, _])
  (lowKK_append (xs := [_]) (lowKK_dec (by simp only [Lower.lowerExp, hy0]; rfl)) (lowKK_append (xs := [_])
    (lowK_any _ (k := .skip) rfl) (lowKK_dec (by simp only [Syntax.eAnd, Lower.lowerExp, hy0]; rfl))))
  (lowK_any _ (k := .skip) rfl)) (lowK_any _ (k := .skip) rfl)

theorem lowKK_textCmp : LowKK [textCmp .none] := by
  rw [textCmp, atOff_textBytes]
  exact lowKK_while rfl (lowKK_append (xs := [_]) (lowKK_dec rfl) (lowKK_append (xs := [_]) (lowKK_dec rfl)
    (lowKK_append (xs := [_]) (lowKK_ite rfl (lowK_any _ (k := .skip) rfl) (lowK_any _ (k := .skip) rfl))
      (lowK_any _ (k := .skip) rfl))))

theorem lowKK_fits : LowKK [.dec "ok" (Syntax.n 1), .dec "i" (Syntax.n 0), textCmp .none,
    .ite (Syntax.v "ok") (addBit .none (Syntax.eAdd (Syntax.v "x") (Syntax.v "len"))) []] :=
  lowKK_append (xs := [_]) (lowKK_dec rfl) (lowKK_append (xs := [_]) (lowKK_dec rfl) (lowKK_append (xs := [_])
    lowKK_textCmp (lowKK_ite rfl (lowKK_addBit rfl) (lowK_any _ (k := .skip) rfl))))

/-- **A string at a position** (`textBody`): the position past string `k` added when it lies at `x`. -/
theorem textBody_frag (o : Oracle σ) {ofs : Nat} {A : Word} {s0 : PancakeState σ} (hA : Area ofs A s0)
    {kd k : Nat} (hkd : kd < slots) (hk : k < texts.length) {S : Nat → Bool} {bytes : List (BitVec 8)}
    (hlen : bytes.length ≤ inputMax) {m1 : Word → Word} (hr : Reads s0 A bytes m1) {L0 : List (String × Value)}
    (ha : L0.lookup "a" = some A) (hq : L0.lookup "q" = some (at_ A (off kd)))
    (hnn : L0.lookup "nn" = some (BitVec.ofNat 64 bytes.length))
    (hl : L0.lookup "len" = some (BitVec.ofNat 64 (textAt k).1.length))
    (hoff : L0.lookup "off" = some (BitVec.ofNat 64 (textOff k))) (hcf : L0.lookup "cf" = some (bw (textAt k).2))
    (hfr : ∀ y ∈ ["ok", "i", "b", "lb", "yw", "yj", "df", "dh", "dl"], Fresh y L0 = true)
    (X : Nat) (lv : List (String × Value)) (hlv : ∀ q ∈ lv, q.1 ∈ loopNames) (hS : S X = true)
    (hX : X < bytes.length) :
    Frag o (textBody .none)
      (RunF s0 (("x", BitVec.ofNat 64 X) :: lv ++ (winL (textAdd S bytes k) X ++ L0))
        (Built A kd (textAdd S bytes k) X m1))
      (RunF s0 (("x", BitVec.ofNat 64 X) :: lv ++ (winL (textAdd S bytes k) (X + 1) ++ L0))
        (Built A kd (textAdd S bytes k) (X + 1) m1)) := by
  have hI := inputMax_eq
  have hsh := textAt_short hk
  have htm : textMax = 63 := rfl
  generalize hn : (textAt k).1.length = len at hl hsh
  let add := textAdd S bytes k
  have hnl : ∀ y, y ∉ loopNames → Fresh y lv = true := fun y hy => fresh_loop hlv hy
  have lk : ∀ Y y v, y ≠ "x" → y ∉ loopNames → y ≠ "df" → y ≠ "dh" → y ≠ "dl" → L0.lookup y = some v →
      (("x", BitVec.ofNat 64 X) :: lv ++ (winL add Y ++ L0)).lookup y = some v := by
    intro Y y v h1 h2 h3 h4 h5 h
    rw [List.cons_append, ScanRun.lookup_cons_ne h1, lookup_app_fresh _ (hnl y h2),
      lookup_app_fresh _ (winL_fresh h3 h4 h5), h]
  have nn' : ∀ y, y ∈ ["a", "q", "nn", "len", "off", "cf"] → y ≠ "x" ∧ y ∉ loopNames ∧ y ≠ "df" ∧ y ≠ "dh" ∧
      y ≠ "dl" := by
    intro y hy; simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [loopNames]
  have lk' : ∀ y v, y ∈ ["a", "q", "nn", "len", "off", "cf"] → L0.lookup y = some v →
      (("x", BitVec.ofNat 64 X) :: lv ++ (winL add X ++ L0)).lookup y = some v := fun y v hy h => by
    obtain ⟨a1, a2, a3, a4, a5⟩ := nn' y hy; exact lk X y v a1 a2 a3 a4 a5 h
  have hx0 : (("x", BitVec.ofNat 64 X) :: lv ++ (winL add X ++ L0)).lookup "x" = some (BitVec.ofNat 64 X) := by
    rw [List.cons_append, lookup_head]
  have frY : ∀ Y y, y ∈ ["ok", "i", "b", "lb"] → Fresh y (("x", BitVec.ofNat 64 X) :: lv ++ (winL add Y ++ L0)) =
      true := fun Y y hy => by
    have h0 : y ∉ loopNames := by simp at hy; rcases hy with rfl | rfl | rfl | rfl <;> simp [loopNames]
    exact ScanRun.fresh_cons (fun e => h0 (e ▸ by simp [loopNames])) (fresh_app (hnl y h0)
      (fresh_app (winL_fresh (by simp at hy; rcases hy with rfl | rfl | rfl | rfl <;> decide)
        (by simp at hy; rcases hy with rfl | rfl | rfl | rfl <;> decide)
        (by simp at hy; rcases hy with rfl | rfl | rfl | rfl <;> decide))
        (hfr y (by simp at hy; rcases hy with rfl | rfl | rfl | rfl <;> simp))))
  have hcond : ∀ u, RunF s0 (("x", BitVec.ofNat 64 X) :: lv ++ (winL add X ++ L0)) (Built A kd add X m1) u →
      eval u (FramerCode.leE (.op .add (.var "x") (.var "len")) (.var "nn")) =
        some (bw (decide (X + len ≤ bytes.length))) := fun u h =>
    FramerCode.eval_le (by omega) (by omega) (by
      simp only [eval, vals_lookup h.1.vals hx0, vals_lookup h.1.vals (lk' "len" _ (by simp) hl)]
      rw [← BitVec.ofNat_add]) (ev_var (vals_lookup h.1.vals (lk' "nn" _ (by simp) hnn)))
  have hdecl : declared [.dec "ok" (Syntax.n 1), .dec "i" (Syntax.n 0), textCmp .none,
      .ite (Syntax.v "ok") (addBit .none (Syntax.eAdd (Syntax.v "x") (Syntax.v "len"))) []] = ["ok", "i"] := rfl
  by_cases hfit : ¬(X + len ≤ bytes.length)
  · have hadd : add X = none := by
      show leafAdd _ _ _ _ X = _
      simp only [leafAdd, textHere, hn, decide_eq_false hfit, Bool.false_and, Bool.and_false, Bool.false_eq_true,
        if_false]
    refine frag_ite o rfl (runF_clock _ _ _) (fun u h => ⟨_, hcond u h⟩)
      (frag_unsat lowKK_fits fun u ⟨h, h0⟩ => h0 (by rw [hcond u h, decide_eq_false hfit]; rfl))
      (fun u y v h hy => by
        rw [hdecl] at hy
        exact runF_restore h (frY _ y (by simp at hy; rcases hy with rfl | rfl <;> simp)) v)
      (frag_nil o fun u ⟨h, _⟩ => ?_) (noDecl _ rfl)
    show RunF s0 (("x", BitVec.ofNat 64 X) :: lv ++ (winL add (X + 1) ++ L0)) (Built A kd add (X + 1) m1) u
    rw [winL_skip hadd]
    exact ⟨h.1, built_skip h.2 hadd⟩
  have hfit : X + len ≤ bytes.length := Classical.not_not.1 hfit
  let Q : Assn σ := RunF s0 (("x", BitVec.ofNat 64 X) :: lv ++ (winL add (X + 1) ++ L0)) (Built A kd add (X + 1) m1)
  refine frag_ite o rfl (runF_clock _ _ _) (fun u h => ⟨_, hcond u h⟩) (P' := Q) ?_
    (fun u y v h hy => by
      rw [hdecl] at hy
      exact runF_restore h (frY _ y (by simp at hy; rcases hy with rfl | rfl <;> simp)) v)
    (frag_unsat (lowK_any _ (k := .skip) rfl) fun u ⟨h, h0⟩ => by rw [hcond u h, decide_eq_true hfit] at h0; cases h0)
    (noDecl _ rfl)
  refine frag_conseq (P0 := RunF s0 (("x", BitVec.ofNat 64 X) :: lv ++ (winL add X ++ L0)) (Built A kd add X m1)) ?_
    (fun u h => h.1) fun u h => h
  let base := ("x", BitVec.ofNat 64 X) :: lv ++ (winL add X ++ L0)
  refine frag_append (xs := [_]) (runF_dec o rfl (frY X "ok" (by simp)) (v := BitVec.ofNat 64 1) fun u h => rfl) ?_
  refine frag_append (xs := [_]) (runF_dec o rfl (ScanRun.fresh_cons (by decide) (frY X "i" (by simp)))
    (v := BitVec.ofNat 64 0) fun u h => rfl) ?_
  have hlen' : base.lookup "len" = some (BitVec.ofNat 64 (textAt k).1.length) := by
    rw [hn]; exact lk' "len" _ (by simp) hl
  refine frag_append (xs := [_]) (textCmp_frag o hk (by rw [hn]; exact hfit) hlen (base := base)
    (F := Built A kd add X m1) (fun m hb => ⟨(reads_built hkd hA.hA hlen hr hb.rest).input,
      (reads_built hkd hA.hA hlen hr hb.rest).texts⟩) (lk' "a" _ (by simp) ha) hx0 hlen'
    (lk' "off" _ (by simp) hoff) (lk' "cf" _ (by simp) hcf)
    (fun y hy => frY X y (by simp at hy; rcases hy with rfl | rfl | rfl | rfl <;> simp))) ?_
  -- the string there, or not
  have hsm : ∀ x e, add x = some e → e ≤ inputMax := fun x e he => by
    have := textAdd_small x e he; omega
  by_cases hok : okTo bytes k X (textAt k).1.length = true
  · have hadd : add X = some (X + (textAt k).1.length) := by
      show leafAdd _ _ _ _ X = _
      simp only [leafAdd, textHere, hS, decide_eq_true hX, decide_eq_true (show X + (textAt k).1.length ≤
        bytes.length by rw [hn]; exact hfit), hok, Bool.and_self, if_true]
    have hokv : ∀ u, RunF s0 (("i", BitVec.ofNat 64 (textAt k).1.length) ::
        ("ok", bw (okTo bytes k X (textAt k).1.length)) :: base) (Built A kd add X m1) u →
        eval u (.var "ok") = some (bw true) := fun u h => by
      rw [← hok]; exact ev_var (vals_lookup h.1.vals (by rw [ScanRun.lookup_cons_ne (by decide), lookup_head]))
    have hfr5 : ∀ y ∈ ["yw", "yj", "df", "dh", "dl"], Fresh y L0 = true := fun y hy => hfr y (by
      simp at hy; rcases hy with rfl | rfl | rfl | rfl | rfl <;> simp)
    refine frag_ite o rfl (runF_clock _ _ _) (fun u h => ⟨_, hokv u h⟩) ?_
      (fun u y v h hy => by
        rw [show declared (addBit .none (Syntax.eAdd (Syntax.v "x") (Syntax.v "len"))) = ["yw", "yj"] from rfl] at hy
        have h0 : y ∉ loopNames := by simp at hy; rcases hy with rfl | rfl <;> simp [loopNames]
        exact runF_restore h (ScanRun.fresh_cons (fun e => h0 (by rw [← e]; simp [loopNames])) (fresh_app (hnl y h0)
          (fresh_app (winL_fresh (by simp at hy; rcases hy with rfl | rfl <;> decide)
            (by simp at hy; rcases hy with rfl | rfl <;> decide) (by simp at hy; rcases hy with rfl | rfl <;> decide))
            (hfr5 y (by simp at hy; rcases hy with rfl | rfl <;> simp))))) v)
      (frag_unsat (lowK_any _ (k := .skip) rfl) fun u ⟨h, h0⟩ => by rw [hokv u h] at h0; cases h0) (noDecl _ rfl)
    refine frag_conseq (addAt_frag o hA hkd hlen hr hsm hadd (lv := lv) (L0 := L0)
      (pre := [("i", BitVec.ofNat 64 (textAt k).1.length), ("ok", bw true)]) ha hq hfr5 hlv
      (fun q hq => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
                      rcases hq with rfl | rfl <;> simp) (y := Syntax.eAdd (Syntax.v "x") (Syntax.v "len")) rfl
      (fun u h => by
        simp only [eval, vals_lookup h.1.vals (by
          show (("i", _) :: ("ok", _) :: base).lookup "x" = _
          rw [ScanRun.lookup_cons_ne (by decide), ScanRun.lookup_cons_ne (by decide)]; exact hx0),
          vals_lookup h.1.vals (by
          show (("i", _) :: ("ok", _) :: base).lookup "len" = _
          rw [ScanRun.lookup_cons_ne (by decide), ScanRun.lookup_cons_ne (by decide)]; exact hlen')]
        rw [← BitVec.ofNat_add]))
      (fun u h => by have h1 := h.1; rw [hok] at h1; exact h1)
      fun u h => runF_mono h (fun q hq => List.mem_append_right _ hq) fun _ e => e
  · have hok' : okTo bytes k X (textAt k).1.length = false := by simpa using hok
    have hadd : add X = none := by
      show leafAdd _ _ _ _ X = _
      simp only [leafAdd, textHere, hok', Bool.and_false, Bool.false_eq_true, if_false]
    refine frag_ite o rfl (runF_clock _ _ _) (fun u h => ⟨_, ev_var (vals_lookup h.1.vals (by
        rw [ScanRun.lookup_cons_ne (by decide), lookup_head]))⟩)
      (frag_unsat (lowKK_addBit rfl) fun u ⟨h, h0⟩ => h0 (by
        rw [ev_var (vals_lookup h.1.vals (by rw [ScanRun.lookup_cons_ne (by decide), lookup_head])), hok']; rfl))
      (fun u y v h hy => by
        rw [show declared (addBit .none (Syntax.eAdd (Syntax.v "x") (Syntax.v "len"))) = ["yw", "yj"] from rfl] at hy
        have h0 : y ∉ loopNames := by simp at hy; rcases hy with rfl | rfl <;> simp [loopNames]
        exact runF_restore h (ScanRun.fresh_cons (fun e => h0 (by rw [← e]; simp [loopNames])) (fresh_app (hnl y h0)
          (fresh_app (winL_fresh (by simp at hy; rcases hy with rfl | rfl <;> decide)
            (by simp at hy; rcases hy with rfl | rfl <;> decide) (by simp at hy; rcases hy with rfl | rfl <;> decide))
            (hfr y (by simp at hy; rcases hy with rfl | rfl <;> simp))))) v)
      (frag_nil o fun u ⟨h, _⟩ => ?_) (noDecl _ rfl)
    show RunF s0 (("x", BitVec.ofNat 64 X) :: lv ++ (winL add (X + 1) ++ L0)) (Built A kd add (X + 1) m1) u
    rw [winL_skip hadd]
    exact ⟨(runF_mono h (fun q hq => List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hq)) fun _ e => e).1,
      built_skip h.2 hadd⟩

/-- **`leafText` adds the positions past string `k` where it lies from those of `S`** to slot `kd`, emptied first. Every
word outside it is kept. -/
theorem leafText_ok (o : Oracle σ) {ofs : Nat} {A : Word} {s1 : PancakeState σ} (hA : Area ofs A s1)
    {ks kd k : Nat} (hks : ks < slots) (hkd : kd < slots) (hne : ks ≠ kd) (hk : k < texts.length)
    (hs : s1.locals "s" = some (BitVec.ofNat 64 ks)) (hd : s1.locals "d" = some (BitVec.ofNat 64 kd))
    (hkl : s1.locals "k" = some (BitVec.ofNat 64 k)) {S Sd : Nat → Bool} (hS : SetAt s1.memory A ks S)
    (hSd : SetAt s1.memory A kd Sd) {bytes : List (BitVec 8)} (hlen : bytes.length ≤ inputMax)
    (hn : s1.memory (at_ A aLen) = BitVec.ofNat 64 bytes.length) (hr : Reads s1 A bytes s1.memory) :
    ∃ body, Lower.lower (leafText .none ofs) = some body ∧
      SafeR o (fun s => s = s1) body (LeafRet A kd (below (textAdd S bytes k) (64 * setWords)) s1.memory)
        fun _ => False := by
  have hI := inputMax_eq
  refine body_of ?_
  dsimp only [leafText]
  let l0 : List (String × Value) := [("s", BitVec.ofNat 64 ks), ("d", BitVec.ofNat 64 kd), ("k", BitVec.ofNat 64 k)]
  let l2 : List (String × Value) := ("nn", BitVec.ofNat 64 bytes.length) :: ("q", at_ A (off kd)) ::
    ("p", at_ A (off ks)) :: ("a", A) :: l0
  let L0 : List (String × Value) := ("cf", bw (textAt k).2) :: ("len", BitVec.ofNat 64 (textAt k).1.length) ::
    ("off", BitVec.ofNat 64 (textOff k)) :: ("t", at_ A (aTexts + 24 * k)) :: l2
  let G : (Word → Word) → Prop := fun m => SetAt m A kd (fun _ => false) ∧ Frame A kd s1.memory m
  have hentry : ∀ s, s = s1 → RunF s1 l0 (· = s1.memory) s := entry_run (fun q hq => by
    simp only [l0, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact hs
    · exact hd
    · exact hkl) rfl
  have hte := texts_end
  have hsh := textAt_short hk
  have hof := textOff_le hk
  have htb := textBytes_le
  have hsl := aSets_le
  obtain ⟨t0, t1, t2, -⟩ := hr.texts k hk
  have keep : ∀ m, G m → ∀ x, x < aSets → m (at_ A x) = s1.memory (at_ A x) := fun m hG x hx =>
    hG.2 _ (notInSlot hkd hx)
  have hload : ∀ (l : List (String × Value)) (c : Nat) (v : Word), c ≤ 16 → c % 8 = 0 →
      s1.memory (at_ A (aTexts + 24 * k + c)) = v → l.lookup "t" = some (at_ A (aTexts + 24 * k)) →
      ∀ u, RunF s1 l G u → eval u (.loadWord (.op .add (.var "t") (.const (BitVec.ofNat 64 c)))) = some v := by
    intro l c v hc hc8 hv hl u h
    rw [load_eval hA h.1.memaddrs (y := aTexts + 24 * k + c) (by omega)
      (by have := aTexts_mod; omega) (by simp only [eval, vals_lookup h.1.vals hl]; rw [at_add]),
      keep _ h.2 _ (by omega), hv]
  have hhead : Frag o textHead (RunF s1 l2 G) (RunF s1 L0 G) := by
    unfold textHead
    rw [atOff_texts]
    refine frag_append (xs := [_]) (kept_frag o (by have := texts_le; omega) (runF_clock _ _ _) fun u h =>
      ⟨k, vals_lookup h.1.vals (rfl : l2.lookup "k" = some (BitVec.ofNat 64 k)), by omega⟩) ?_
    refine frag_append (xs := [_]) (runF_dec o rfl rfl (v := at_ A (aTexts + 24 * k)) fun u h => ?_) ?_
    · simp only [eval, vals_lookup h.1.vals (rfl : l2.lookup "a" = some A),
        vals_lookup h.1.vals (rfl : l2.lookup "k" = some (BitVec.ofNat 64 k))]
      rw [← BitVec.ofNat_mul]
      show some (at_ A aTexts + BitVec.ofNat 64 (k * 24)) = _
      rw [at_add]; exact congrArg (fun y => some (at_ A y)) (by omega)
    refine frag_append (xs := [_]) (runF_dec o rfl rfl (v := BitVec.ofNat 64 (textOff k)) fun u h => ?_) ?_
    · exact (load_eval hA h.1.memaddrs (y := aTexts + 24 * k) (by omega) (by have := aTexts_mod; omega)
        (ev_var (vals_lookup h.1.vals (lookup_head _ _ _)))).trans (by rw [keep _ h.2 _ (by omega), t0])
    refine frag_append (xs := [_]) (kept_frag o (by omega) (runF_clock _ _ _) fun u h =>
      ⟨textOff k, vals_lookup h.1.vals (lookup_head _ _ _), by omega⟩) ?_
    refine frag_append (xs := [_]) (runF_dec o rfl rfl (v := BitVec.ofNat 64 (textAt k).1.length)
      (hload _ 8 _ (by decide) (by decide) t1 (by rw [ScanRun.lookup_cons_ne (by decide), lookup_head]))) ?_
    refine frag_append (xs := [_]) (kept_frag o (by decide) (runF_clock _ _ _) fun u h =>
      ⟨(textAt k).1.length, vals_lookup h.1.vals (lookup_head _ _ _), hsh⟩) ?_
    refine frag_append (xs := [_]) (runF_dec o rfl rfl (v := bw (textAt k).2)
      (hload _ 16 _ (by decide) (by decide) t2 (by
        rw [ScanRun.lookup_cons_ne (by decide), ScanRun.lookup_cons_ne (by decide), lookup_head]))) ?_
    exact kept_frag o (by decide) (runF_clock _ _ _) fun u h =>
      ⟨if (textAt k).2 then 1 else 0, by rw [vals_lookup h.1.vals (lookup_head _ _ _)]; cases (textAt k).2 <;> rfl,
        by split <;> omega⟩
  refine fragR_conseq (P0 := RunF s1 l0 (· = s1.memory)) (leaf_frag o hA hks hkd hne hS hSd hlen hn hr (l0 := l0)
    rfl rfl (by intro y hy; simp at hy; rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl) (L0 := L0)
    hhead ⟨rfl, rfl, rfl, rfl⟩ (by intro y hy; simp [loopNames] at hy; rcases hy with rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl <;> rfl) (fun x h => textAdd_none h) (fun x e he => by
        have := textAdd_small x e he; rw [setWords_eq]; omega)
    (lowKK_ite rfl lowKK_fits (lowK_any _ (k := .skip) rfl)) (fun y hy => by
      rw [show declared (textBody .none) = [] from rfl] at hy; cases hy)
    fun M0 _ hrM X lv hlv hSX hX => textBody_frag o hA hkd hk hlen hrM rfl rfl rfl rfl rfl rfl
      (by intro y hy; simp at hy; rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl)
      X lv hlv hSX hX)
    hentry fun _ h => h

/-! ## The input as the grammar reads it -/

/-- The input as the grammar reads it. -/
def inputOf (bytes : List (BitVec 8)) : Array Nat := (bytes.map BitVec.toNat).toArray

theorem inputOf_lt {bytes : List (BitVec 8)} {y : Nat} (h : y < bytes.length) :
    (inputOf bytes)[y]? = some (bytes[y]!).toNat := by
  simp [inputOf, h]

theorem inputOf_ge {bytes : List (BitVec 8)} {y : Nat} (h : bytes.length ≤ y) : (inputOf bytes)[y]? = none := by
  simp [inputOf, h]

theorem inputOf_size (bytes : List (BitVec 8)) : (inputOf bytes).size = bytes.length := by simp [inputOf]

theorem inputOf_byte {bytes : List (BitVec 8)} {y b : Nat} (h : (inputOf bytes)[y]? = some b) : b < 256 := by
  rcases Nat.lt_or_ge y bytes.length with hy | hy
  · rw [inputOf_lt hy] at h; cases h; exact (bytes[y]!).isLt
  · rw [inputOf_ge hy] at h; cases h

theorem lt_of_some {input : Array Nat} {i b : Nat} (h : input[i]? = some b) : i < input.size :=
  (Array.getElem?_eq_some_iff.1 h).1

/-! ## What the leaves add, as the grammar matches -/

/-- **What `leafClass` adds is where its term matches**, class `k` the bits of the term's class. -/
theorem classAdd_iff {f : Nat} {t : Abnf.Term} {rs : List (Nat × Nat)} (ht : classOf f t = some rs) {k : Nat}
    (hk : classes[k]? = some (bitsOf rs)) {S : Nat → Bool} {bytes : List (BitVec 8)} {x e : Nat} :
    classAdd S bytes k x = some e ↔ S x = true ∧ Matches AbnfRules.grammar (inputOf bytes) t x e := by
  rw [AbnfMatch.class_match ht fun b hb => inputOf_byte hb]
  simp only [classAdd, leafAdd, classBit, classWord, hk, Option.getD_some]
  constructor
  · intro h
    split at h
    · rename_i hc
      cases h
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
      exact ⟨hc.1.1, ⟨_, inputOf_lt hc.1.2, hc.2⟩, rfl⟩
    · cases h
  · rintro ⟨hS, ⟨b, hb, hbit⟩, rfl⟩
    have hx : x < bytes.length := by have := lt_of_some hb; rwa [inputOf_size] at this
    rw [inputOf_lt hx] at hb
    cases hb
    simp only [getElem!_pos bytes x hx] at hbit
    simp [hS, hx, hbit]

theorem textAt_eq {k : Nat} {t : List Nat × Bool} (hk : texts[k]? = some t) : textAt k = t := by
  unfold textAt; rw [hk]; rfl

/-- **What `leafText` adds is where its term matches**, string `k` the term's, folded as it says. -/
theorem textAdd_iff {f : Nat} {t : Abnf.Term} {bs : List Nat} {c : Bool} (ht : textOf f t = some (bs, c)) {k : Nat}
    (hk : texts[k]? = some (bs, c && bs.any fun b => 97 ≤ b && b ≤ 122)) {S : Nat → Bool}
    {bytes : List (BitVec 8)} {x e : Nat} :
    textAdd S bytes k x = some e ↔ S x = true ∧ Matches AbnfRules.grammar (inputOf bytes) t x e := by
  rw [AbnfMatch.text_match ht]
  have hl : 0 < bs.length := by
    have := texts_nonempty k (List.getElem?_eq_some_iff.1 hk).1
    rw [hk] at this
    simpa using this
  simp only [textAdd, leafAdd, textHere, okTo, textAt_eq hk]
  constructor
  · intro h
    split at h
    · rename_i hc
      cases h
      simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range, beq_iff_eq] at hc
      have := hc.2.1
      refine ⟨hc.1.1, fun i hi => ⟨_, inputOf_lt (by omega), ?_⟩, rfl⟩
      rw [hc.2.2 i hi, getElem!_pos bs i hi]
    · cases h
  · rintro ⟨hS, hm, rfl⟩
    have hend : x + bs.length ≤ bytes.length := by
      obtain ⟨b, hb, -⟩ := hm (bs.length - 1) (by omega)
      have := lt_of_some hb; rw [inputOf_size] at this; omega
    split
    · rfl
    rename_i hc
    refine absurd ?_ hc
    simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range, beq_iff_eq]
    refine ⟨⟨hS, by omega⟩, hend, fun i hi => ?_⟩
    obtain ⟨b, hb, hf⟩ := hm i hi
    rw [inputOf_lt (by omega)] at hb
    cases hb
    rw [hf, getElem!_pos bs i hi]

/-- **A leaf's set** is the ends of the matches from the positions of `S`. This holds when what it adds at `x` is the
ends from `x`, and comes from below `B`. -/
theorem below_matches {add : Nat → Option Nat} {B : Nat} {S : Nat → Bool} {M : Nat → Nat → Prop}
    (h : ∀ x e, add x = some e ↔ S x = true ∧ M x e) (hb : ∀ x e, add x = some e → x < B) {e : Nat} :
    below add B e = true ↔ ∃ x, S x = true ∧ M x e := by
  simp only [below, List.any_eq_true, List.mem_range, beq_iff_eq]
  exact ⟨fun ⟨x, _, hx⟩ => ⟨x, (h x e).1 hx⟩, fun ⟨x, hx⟩ => ⟨x, hb x e ((h x e).2 hx), (h x e).2 hx⟩⟩

/-- **Slot `kd` after `leafClass`** holds where the term's matches end from the positions of `S`. -/
theorem classSet_iff {f : Nat} {t : Abnf.Term} {rs : List (Nat × Nat)} (ht : classOf f t = some rs) {k : Nat}
    (hk : classes[k]? = some (bitsOf rs)) {S : Nat → Bool} {bytes : List (BitVec 8)} (hlen : bytes.length ≤ inputMax)
    (e : Nat) : below (classAdd S bytes k) (64 * setWords) e = true ↔
      ∃ x, S x = true ∧ Matches AbnfRules.grammar (inputOf bytes) t x e :=
  below_matches (fun _ _ => classAdd_iff ht hk) fun x e h => by
    simp only [classAdd, leafAdd] at h
    split at h
    · rename_i hc
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
      rw [setWords_eq]; rw [inputMax_eq] at hlen; omega
    · cases h

/-- **Slot `kd` after `leafText`** likewise. -/
theorem textSet_iff {f : Nat} {t : Abnf.Term} {bs : List Nat} {c : Bool} (ht : textOf f t = some (bs, c)) {k : Nat}
    (hk : texts[k]? = some (bs, c && bs.any fun b => 97 ≤ b && b ≤ 122)) {S : Nat → Bool}
    {bytes : List (BitVec 8)} (hlen : bytes.length ≤ inputMax) (e : Nat) :
    below (textAdd S bytes k) (64 * setWords) e = true ↔
      ∃ x, S x = true ∧ Matches AbnfRules.grammar (inputOf bytes) t x e :=
  below_matches (fun _ _ => textAdd_iff ht hk) fun x e h => by
    simp only [textAdd, leafAdd] at h
    split at h
    · rename_i hc
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
      rw [setWords_eq]; rw [inputMax_eq] at hlen; omega
    · cases h

/-! ## Calls -/

theorem reads_of {s0 s1 : PancakeState σ} (hm : s1.memaddrs = s0.memaddrs) (hb : s1.be = s0.be) {A : Word}
    {bytes : List (BitVec 8)} {m : Word → Word} (h : Reads s0 A bytes m) : Reads s1 A bytes m :=
  ⟨by rw [hm, hb]; exact h.input, h.pows, h.masks, h.classes, by rw [hm, hb]; exact h.texts⟩

/-! ## The premises can hold -/

/-- The strings' bytes, one after another. -/
def allTextBytes : List Nat := (texts.map (·.1)).flatten

theorem flatten_at : ∀ (T : List (List Nat × Bool)) (k i : Nat), k < T.length →
    i < (T[k]?.getD ([], false)).1.length →
    (T.map (·.1)).flatten[((T.take k).map (·.1.length)).sum + i]? = some (T[k]?.getD ([], false)).1[i]!
  | [], _, _, hk, _ => absurd hk (by simp)
  | t :: T, 0, i, _, hi => by
    simp only [List.getElem?_cons_zero, Option.getD_some] at hi ⊢
    simp only [List.take_zero, List.map_nil, List.sum_nil, Nat.zero_add, List.map_cons, List.flatten_cons]
    rw [List.getElem?_append_left hi, List.getElem?_eq_getElem hi, getElem!_pos _ i hi]
  | t :: T, k + 1, i, hk, hi => by
    simp only [List.getElem?_cons_succ] at hi ⊢
    simp only [List.take_succ_cons, List.map_cons, List.sum_cons, List.flatten_cons]
    rw [List.getElem?_append_right (by omega), show t.1.length + ((T.take k).map (·.1.length)).sum + i - t.1.length =
      ((T.take k).map (·.1.length)).sum + i by omega]
    exact flatten_at T k i (by simp at hk; omega) hi

theorem allTextBytes_at {k i : Nat} (hk : k < texts.length) (hi : i < (textAt k).1.length) :
    allTextBytes[textOff k + i]? = some (textAt k).1[i]! := by
  unfold allTextBytes textOff
  unfold textAt at hi ⊢
  exact flatten_at texts k i hk hi

/-- The number whose base-256 digits from the lowest are `f x`, …, `f (x + n - 1)`, each taken mod 256. -/
def digits (f : Nat → Nat) (x : Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => f x % 256 + 256 * digits f (x + 1) n

theorem digits_lt (f : Nat → Nat) : ∀ x n, digits f x n < 256 ^ n
  | _, 0 => by simp [digits]
  | x, n + 1 => by
    have := digits_lt f (x + 1) n
    have := Nat.mod_lt (f x) (by decide : 256 > 0)
    rw [digits, Nat.pow_succ]; omega

theorem digits_div (f : Nat → Nat) : ∀ x n i, i < n → digits f x n / 256 ^ i % 256 = f (x + i) % 256
  | _, 0, _, h => absurd h (by omega)
  | x, n + 1, 0, _ => by simp [digits, Nat.add_mul_mod_self_left]
  | x, n + 1, i + 1, h => by
    rw [digits, Nat.pow_succ', ← Nat.div_div_eq_div_mul, Nat.add_mul_div_left _ _ (by decide),
      Nat.div_eq_of_lt (Nat.mod_lt _ (by decide)), Nat.zero_add, digits_div f (x + 1) n i (by omega),
      Nat.add_assoc, Nat.add_comm 1 i]

/-- A byte of a word of digits. -/
theorem getByte_digits (f : Nat → Nat) {z : Nat} (hz : z < 2 ^ 64) :
    getByte (BitVec.ofNat 64 z) (BitVec.ofNat 64 (digits f (z / 8 * 8) 8)) false = BitVec.ofNat 8 (f z) := by
  have hl := digits_lt f (z / 8 * 8) 8
  apply BitVec.eq_of_toNat_eq
  simp only [getByte, byteIndex, Bool.false_eq_true, if_false, BitVec.toNat_setWidth, BitVec.toNat_ushiftRight,
    BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  rw [Nat.mod_eq_of_lt (by omega : z < 2 ^ 64), Nat.mod_eq_of_lt (by omega : digits f (z / 8 * 8) 8 < 2 ^ 64),
    Nat.pow_mul, digits_div f _ 8 (z % 8) (Nat.mod_lt _ (by decide)), show z / 8 * 8 + z % 8 = z by omega]

theorem at0 {x : Nat} (hx : x < 2 ^ 64) : (at_ 0 x).toNat = x := by
  simp [at_, Nat.mod_eq_of_lt hx]

section
variable (P M C T B : Nat) (cw : Nat → Nat → Nat) (toff tlen : Nat → Nat) (tcf : Nat → Bool) (tb : List Nat)

/-- An area at 0: powers of two from `P`, masks from `M`, class words `cw` from `C`. Strings' offsets, lengths and folds
lie from `T`, their bytes `tb` from `B`. -/
def tablesOf (a : Word) : Word :=
  if a.toNat < P then 0
  else if a.toNat < M then BitVec.twoPow 64 ((a.toNat - P) / 8)
  else if a.toNat < C then BitVec.ofNat 64 (255 * 2 ^ (8 * ((a.toNat - M) / 8)))
  else if a.toNat < T then BitVec.ofNat 64 (cw ((a.toNat - C) / 32) ((a.toNat - C) % 32 / 8))
  else if a.toNat < B then
    (if (a.toNat - T) % 24 = 0 then BitVec.ofNat 64 (toff ((a.toNat - T) / 24))
     else if (a.toNat - T) % 24 = 8 then BitVec.ofNat 64 (tlen ((a.toNat - T) / 24))
     else bw (tcf ((a.toNat - T) / 24)))
  else BitVec.ofNat 64 (digits (fun y => tb[y - B]?.getD 0) a.toNat 8)

variable {P M C T B}

theorem tablesOf_pow (hM : P + 8 * 64 ≤ M) (h : M < 2 ^ 64) {j : Nat} (hj : j < 64) :
    tablesOf P M C T B cw toff tlen tcf tb (at_ 0 (P + 8 * j)) = BitVec.twoPow 64 j := by
  unfold tablesOf
  rw [at0 (by omega), if_neg (by omega), if_pos (by omega), show (P + 8 * j - P) / 8 = j by omega]

theorem tablesOf_mask (hM : P ≤ M) (hC : M + 8 * 8 ≤ C) (h : C < 2 ^ 64) {b : Nat} (hb : b < 8) :
    tablesOf P M C T B cw toff tlen tcf tb (at_ 0 (M + 8 * b)) = BitVec.ofNat 64 (255 * 2 ^ (8 * b)) := by
  unfold tablesOf
  rw [at0 (by omega), if_neg (by omega), if_neg (by omega), if_pos (by omega), show (M + 8 * b - M) / 8 = b by omega]

theorem tablesOf_class (hM : P ≤ M) (hC : M ≤ C) {k i : Nat} (hT : C + 32 * k + 32 ≤ T) (h : T < 2 ^ 64)
    (hi : i < 4) : tablesOf P M C T B cw toff tlen tcf tb (at_ 0 (C + 32 * k + 8 * i)) = BitVec.ofNat 64 (cw k i) := by
  unfold tablesOf
  rw [at0 (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos (by omega),
    show (C + 32 * k + 8 * i - C) / 32 = k by omega, show (C + 32 * k + 8 * i - C) % 32 / 8 = i by omega]

theorem tablesOf_head (hM : P ≤ M) (hC : M ≤ C) (hT : C ≤ T) {k : Nat} (hB : T + 24 * k + 24 ≤ B)
    (h : B < 2 ^ 64) :
    tablesOf P M C T B cw toff tlen tcf tb (at_ 0 (T + 24 * k)) = BitVec.ofNat 64 (toff k) ∧
    tablesOf P M C T B cw toff tlen tcf tb (at_ 0 (T + 24 * k + 8)) = BitVec.ofNat 64 (tlen k) ∧
    tablesOf P M C T B cw toff tlen tcf tb (at_ 0 (T + 24 * k + 16)) = bw (tcf k) := by
  unfold tablesOf
  refine ⟨?_, ?_, ?_⟩
  · rw [at0 (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos (by omega),
      if_pos (by omega), show (T + 24 * k - T) / 24 = k by omega]
  · rw [at0 (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos (by omega),
      if_neg (by omega), if_pos (by omega), show (T + 24 * k + 8 - T) / 24 = k by omega]
  · rw [at0 (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos (by omega),
      if_neg (by omega), if_neg (by omega), show (T + 24 * k + 16 - T) / 24 = k by omega]

theorem tablesOf_byte (hM : P ≤ M) (hC : M ≤ C) (hT : C ≤ T) (hTB : T ≤ B) (h8 : B % 8 = 0) {z : Nat} (hz : B ≤ z)
    (h : z < 2 ^ 64) : memLoadByte (tablesOf P M C T B cw toff tlen tcf tb) (fun _ => true) false (at_ 0 z) =
      some (BitVec.ofNat 8 (tb[z - B]?.getD 0)) := by
  unfold memLoadByte
  rw [ScanRun.align_at (by decide), if_pos rfl]
  unfold tablesOf
  rw [at0 (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
    show at_ 0 z = BitVec.ofNat 64 z by simp [at_], getByte_digits _ h]

end

/-- The tables as the leaves read them, in an area at 0. -/
def tablesMem : Word → Word :=
  tablesOf aPow aMask aClass aTexts aTextBytes classWord textOff (fun k => (textAt k).1.length) (fun k => (textAt k).2)
    allTextBytes

theorem lt_of_room {a b c d : Nat} (h1 : a + b + c + 1 ≤ d) (h2 : d ≤ 2 ^ 20) : a < 2 ^ 64 := by omega

theorem pow_mask : aPow ≤ aMask := Nat.le_of_add_right_le mask_after
theorem mask_class : aMask ≤ aClass := Nat.le_of_add_right_le class_after
theorem class_texts : aClass ≤ aTexts := Nat.le_of_add_right_le texts_after
theorem texts_le_bytes : aTexts ≤ aTextBytes := Nat.le_of_add_right_le bytes_after
theorem tables_bound : aTextBytes < 2 ^ 64 := lt_of_room textBytes_le aSets_le

theorem tablesMem_pow {j : Nat} (hj : j < 64) : tablesMem (at_ 0 (aPow + 8 * j)) = BitVec.twoPow 64 j :=
  tablesOf_pow (P := aPow) (M := aMask) (C := aClass) (T := aTexts) (B := aTextBytes) _ _ _ _ _ mask_after
    (Nat.lt_of_le_of_lt (Nat.le_trans mask_class (Nat.le_trans class_texts texts_le_bytes)) tables_bound) hj

theorem tablesMem_mask {b : Nat} (hb : b < 8) :
    tablesMem (at_ 0 (aMask + 8 * b)) = BitVec.ofNat 64 (255 * 2 ^ (8 * b)) :=
  tablesOf_mask (P := aPow) (M := aMask) (C := aClass) (T := aTexts) (B := aTextBytes) _ _ _ _ _ pow_mask class_after
    (Nat.lt_of_le_of_lt (Nat.le_trans class_texts texts_le_bytes) tables_bound) hb

theorem tablesMem_class {k i : Nat} (hk : k < classes.length) (hi : i < 4) :
    tablesMem (at_ 0 (aClass + 32 * k + 8 * i)) = BitVec.ofNat 64 (classWord k i) :=
  tablesOf_class (P := aPow) (M := aMask) (C := aClass) (T := aTexts) (B := aTextBytes) _ _ _ _ _ pow_mask mask_class
    (by have := texts_after; omega) (Nat.lt_of_le_of_lt texts_le_bytes tables_bound) hi

theorem reads_witness : Reads (bareState ()) 0 [] tablesMem := by
  have a4 := bytes_after
  have h2 := aSets_le
  have h3 := textBytes_le
  have h4 := tables_bound
  refine ⟨fun x hx => absurd hx (by simp), fun j hj => tablesMem_pow hj, fun b hb => tablesMem_mask hb,
    fun k hk i hi => tablesMem_class hk hi, fun k hk => ?_⟩
  have hof := textOff_le hk
  obtain ⟨t0, t1, t2⟩ := tablesOf_head (P := aPow) (M := aMask) (C := aClass) (T := aTexts) (B := aTextBytes)
    classWord textOff (fun k => (textAt k).1.length) (fun k => (textAt k).2) allTextBytes (k := k) pow_mask
    mask_class class_texts (by omega) h4
  refine ⟨t0, t1, t2, fun i hi => ?_⟩
  rw [show (bareState ()).memaddrs = fun _ => true from rfl, show (bareState ()).be = false from rfl, tablesMem,
    tablesOf_byte (P := aPow) (M := aMask) (C := aClass) (T := aTexts) (B := aTextBytes) _ _ _ _ _ pow_mask
      mask_class class_texts texts_le_bytes aTextBytes_mod (by omega) (by omega),
    show aTextBytes + textOff k + i - aTextBytes = textOff k + i by omega, allTextBytes_at hk hi, Option.getD_some]

theorem built_witness : Built 0 0 (fun _ => none) 0 emptyMem emptyMem :=
  built_zero fun w hw j hj => setAt_witness.bits w hw j hj

theorem each_witness : Each 0 0 0 (fun _ => false)
    (fun _ => [("p", at_ 0 (off 0)), ("nn", BitVec.ofNat 64 0), ("a", 0)])
    (fun _ m => SetAt m 0 0 (fun _ => false) ∧ Masks m 0 ∧ Pows m 0) :=
  ⟨fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ y hy => by
    simp only [loopNames, List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl, fun _ _ h => h, fun _ _ => ⟨rfl, fun _ h => h⟩⟩

/-- A memory for the leaves' premises together: the input `[b]` and its length, the tables, slots 0 and 1 empty. -/
def leafMem (b : BitVec 8) (a : Word) : Word :=
  if a = at_ 0 aLen then 1
  else if a = slotW 0 0 0 ∨ a = slotW 0 1 0 then 1
  else if a = at_ 0 (aInput / 8 * 8) then
    BitVec.ofNat 64 (digits (fun y => if y = aInput then b.toNat else 0) (aInput / 8 * 8) 8)
  else tablesMem a

theorem allTextBytes_length : allTextBytes.length = textBytes := by
  unfold allTextBytes textBytes
  simp only [List.length_flatten, List.map_map]
  rfl

theorem digits_zero (f : Nat → Nat) : ∀ x n, (∀ i, i < n → f (x + i) = 0) → digits f x n = 0
  | _, 0, _ => rfl
  | x, n + 1, h => by
    have h0 := h 0 (by omega)
    rw [Nat.add_zero] at h0
    rw [digits, h0, digits_zero f (x + 1) n fun i hi => by
      rw [show x + 1 + i = x + (i + 1) by omega]; exact h (i + 1) (by omega)]

theorem tablesMem_high {x : Nat} (hx : aSets ≤ x) (h64 : x < 2 ^ 64) : tablesMem (at_ 0 x) = 0 := by
  have h1 := pow_mask
  have h2 := mask_class
  have h3 := class_texts
  have h4 := texts_le_bytes
  have h5 := textBytes_le
  have hl := allTextBytes_length
  unfold tablesMem tablesOf
  rw [at0 h64, if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
    digits_zero _ _ _ fun i _ => by rw [List.getElem?_eq_none (by omega)]; rfl]
  rfl

theorem aInput_eq : aInput = 168 := rfl

theorem slotW0 {k i : Nat} : slotW 0 k i = at_ 0 (off k + 8 * i) := rfl

theorem off_ge (k : Nat) : aSets ≤ off k := Nat.le_add_right _ _

/-- The first word of slot 0 or 1 is past the tables. -/
theorem slot01 {x : Nat} (hx : x < aSets) {a : Word} (ha : a = slotW 0 0 0 ∨ a = slotW 0 1 0) : at_ 0 x ≠ a := by
  have h2 := slots_two
  have hs := aSets_le
  rcases ha with rfl | rfl
  · exact at_ne (by omega) (by have := off_small (k := 0) (by omega) 0 (by rw [setSize_eq]; decide); omega)
      (by have := off_ge 0; omega)
  · exact at_ne (by omega) (by have := off_small (k := 1) (by omega) 0 (by rw [setSize_eq]; decide); omega)
      (by have := off_ge 1; omega)

/-- The tables lie in a row below the slots. -/
theorem bytes_sets : aTextBytes ≤ aSets :=
  Nat.le_of_add_right_le (Nat.le_of_add_right_le (Nat.le_of_add_right_le textBytes_le))

theorem input_sets : aInput + inputMax ≤ aSets :=
  Nat.le_trans input_le (Nat.le_trans io_le (Nat.le_of_add_right_le pow_lt))

theorem aLen_lt_input : aLen < aInput := by rw [aInput_eq]; decide

theorem pow_in {j : Nat} (hj : j < 64) : aPow ≤ aPow + 8 * j ∧ aPow + 8 * j < aSets :=
  ⟨Nat.le_add_right _ _, Nat.lt_of_lt_of_le (Nat.add_lt_add_left (by omega) _) pow_lt⟩

theorem mask_in {c : Nat} (hc : c < 8) : aPow ≤ aMask + 8 * c ∧ aMask + 8 * c < aSets :=
  ⟨Nat.le_trans pow_mask (Nat.le_add_right _ _), Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le
    (Nat.add_lt_add_left (show 8 * c < 8 * 8 by omega) _) class_after)
    (Nat.le_trans class_texts (Nat.le_trans texts_le_bytes bytes_sets))⟩

theorem class_in {k i : Nat} (hk : k < classes.length) (hi : i < 4) :
    aPow ≤ aClass + 32 * k + 8 * i ∧ aClass + 32 * k + 8 * i < aSets := by
  refine ⟨Nat.le_trans (Nat.le_trans pow_mask mask_class) (Nat.le_trans (Nat.le_add_right _ _) (Nat.le_add_right _ _)),
    Nat.lt_of_lt_of_le ?_ (Nat.le_trans texts_after (Nat.le_trans texts_le_bytes bytes_sets))⟩
  rw [Nat.add_assoc]
  exact Nat.add_lt_add_left (by omega) _

theorem text_in {k r : Nat} (hk : k < texts.length) (hr : r < 24) :
    aPow ≤ aTexts + 24 * k + r ∧ aTexts + 24 * k + r < aSets := by
  refine ⟨Nat.le_trans (Nat.le_trans pow_mask (Nat.le_trans mask_class class_texts))
    (Nat.le_trans (Nat.le_add_right _ _) (Nat.le_add_right _ _)), Nat.lt_of_lt_of_le ?_
    (Nat.le_trans bytes_after bytes_sets)⟩
  rw [Nat.add_assoc]
  exact Nat.add_lt_add_left (by omega) _

theorem text_in0 {k : Nat} (hk : k < texts.length) : aPow ≤ aTexts + 24 * k ∧ aTexts + 24 * k < aSets := by
  simpa using text_in hk (r := 0) (by decide)

theorem byte_in {k i : Nat} (hk : k < texts.length) (hi : i < (textAt k).1.length) :
    aPow ≤ (aTextBytes + textOff k + i) / 8 * 8 ∧ (aTextBytes + textOff k + i) / 8 * 8 < aSets := by
  have h1 : aPow ≤ aTextBytes :=
    Nat.le_trans pow_mask (Nat.le_trans mask_class (Nat.le_trans class_texts texts_le_bytes))
  have h2 := aTextBytes_mod
  have h3 := textOff_le hk
  have h4 := textBytes_le
  generalize aPow = P at h1
  generalize aTextBytes = B at *
  generalize aSets = T at *
  constructor <;> omega

/-- Where the tables are, `leafMem` holds them. -/
theorem leafMem_tab (b : BitVec 8) {x : Nat} (h1 : aPow ≤ x) (h2 : x < aSets) :
    leafMem b (at_ 0 x) = tablesMem (at_ 0 x) := by
  have hs := aSets_le
  have hl := aLen_lt_input
  have hp : aInput < aPow := Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_add_of_pos_right (by
    rw [inputMax_eq]; decide)) input_le) io_le
  unfold leafMem
  rw [if_neg (at_ne (by omega) (by decide) (by have : aLen = 8 := rfl; omega)), if_neg (fun h => slot01 h2 h rfl),
    if_neg (at_ne (by omega) (by omega) (by omega))]

theorem leafMem_empty (b : BitVec 8) {k : Nat} (hk : k = 0 ∨ k = 1) : SetAt (leafMem b) 0 k (fun _ => false) := by
  have h2 := slots_two
  have hkl : k < slots := by omega
  have hin := input_sets
  have hI := inputMax_eq
  have hs := aSets_le
  have hl := aLen_lt_input
  have word : ∀ i, 1 ≤ i → i < setSize / 8 → leafMem b (slotW 0 k i) = 0 := fun i hi1 hi2 => by
    have ho := off_small hkl (8 * i) (by rw [setSize_eq] at hi2 ⊢; omega)
    have hg := off_ge k
    unfold leafMem
    rw [slotW0, if_neg (at_ne (by omega) (by decide) (by have : aLen = 8 := rfl; omega)), if_neg ?_,
      if_neg (at_ne (by omega) (by omega) (by omega)), tablesMem_high (x := off k + 8 * i) (by omega) (by omega)]
    rintro (e | e)
    · exact slotW_ne' hkl (by omega) hi2 (by rw [setSize_eq]; decide) (by omega) (slotW0.trans e)
    · exact slotW_ne' hkl (by omega) hi2 (by rw [setSize_eq]; decide) (by omega) (slotW0.trans e)
  have h0 : leafMem b (slotW 0 k 0) = 1 := by
    have ho := off_small hkl 0 (by rw [setSize_eq]; decide)
    have hg := off_ge k
    unfold leafMem
    rw [slotW0, if_neg (at_ne (by omega) (by decide) (by have : aLen = 8 := rfl; omega)), if_pos]
    rcases hk with rfl | rfl
    · exact .inl rfl
    · exact .inr rfl
  have h1 := word 1 (Nat.le_refl _) (by rw [setSize_eq]; decide)
  refine ⟨by rw [h0]; decide, by rw [h1]; decide, fun w hw j _ => ?_, fun _ h => by simp at h,
    fun _ h => by simp at h, fun h => by rw [h0, h1] at h; simp at h⟩
  rw [setWords_eq] at hw
  rw [word (2 + w) (by omega) (by rw [setSize_eq]; omega)]
  simp

/-- **The leaves' premises hold together**: the area at 0, the input `(` and its length, the tables, two empty
slots. -/
theorem leaf_witness : Reads (bareState ()) 0 [BitVec.ofNat 8 40] (leafMem (BitVec.ofNat 8 40)) ∧
    SetAt (leafMem (BitVec.ofNat 8 40)) 0 0 (fun _ => false) ∧
    SetAt (leafMem (BitVec.ofNat 8 40)) 0 1 (fun _ => false) ∧
    leafMem (BitVec.ofNat 8 40) (at_ 0 aLen) = BitVec.ofNat 64 [BitVec.ofNat 8 40].length := by
  refine ⟨⟨fun x hx => ?_, fun j hj => ?_, fun c hc => ?_, fun k hk i hi => ?_, fun k hk => ?_⟩,
    leafMem_empty _ (.inl rfl), leafMem_empty _ (.inr rfl), by unfold leafMem; rw [if_pos rfl]; rfl⟩
  · have : x = 0 := by simp at hx; omega
    subst this
    have hw : aInput / 8 * 8 < aSets := Nat.lt_of_le_of_lt (Nat.div_mul_le_self _ _)
      (Nat.lt_of_lt_of_le (Nat.lt_add_of_pos_right (by rw [inputMax_eq]; decide)) input_sets)
    show some (getByte (at_ 0 (aInput + 0)) (leafMem _ (byteAlign (at_ 0 (aInput + 0)))) false) = _
    rw [ScanRun.align_at (by decide)]
    simp only [Nat.add_zero]
    unfold leafMem
    rw [if_neg (at_ne (by rw [aInput_eq]; decide) (by decide) (by rw [aInput_eq]; decide)),
      if_neg (fun h => slot01 hw h rfl), if_pos rfl, show at_ 0 aInput = BitVec.ofNat 64 aInput by simp [at_],
      getByte_digits _ (by rw [aInput_eq]; decide)]
    simp
  · rw [leafMem_tab _ (pow_in hj).1 (pow_in hj).2]; exact reads_witness.pows j hj
  · rw [leafMem_tab _ (mask_in hc).1 (mask_in hc).2]; exact reads_witness.masks c hc
  · rw [leafMem_tab _ (class_in hk hi).1 (class_in hk hi).2]; exact reads_witness.classes k hk i hi
  · obtain ⟨t0, t1, t2, t3⟩ := reads_witness.texts k hk
    refine ⟨by rw [leafMem_tab _ (text_in0 hk).1 (text_in0 hk).2]; exact t0,
      by rw [leafMem_tab _ (text_in hk (r := 8) (by decide)).1 (text_in hk (r := 8) (by decide)).2]; exact t1,
      by rw [leafMem_tab _ (text_in hk (r := 16) (by decide)).1 (text_in hk (r := 16) (by decide)).2]; exact t2,
      fun i hi => ?_⟩
    rw [← t3 i hi]
    exact ScanRun.load_eq (by rw [ScanRun.align_at (by decide), leafMem_tab _ (byte_in hk hi).1 (byte_in hk hi).2])

theorem tables_witness : InputAt (leafMem (BitVec.ofNat 8 40)) (fun _ => true) false 0 [BitVec.ofNat 8 40] ∧
    Masks (leafMem (BitVec.ofNat 8 40)) 0 ∧ ClassesAt (leafMem (BitVec.ofNat 8 40)) 0 ∧
    TextsAt (leafMem (BitVec.ofNat 8 40)) (fun _ => true) false 0 :=
  ⟨leaf_witness.1.input, leaf_witness.1.masks, leaf_witness.1.classes, leaf_witness.1.texts⟩

end DN.News.AbnfLeaves
