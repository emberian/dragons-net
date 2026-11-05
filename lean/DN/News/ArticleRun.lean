-- SPDX-License-Identifier: AGPL-3.0-or-later
import DN.News.AbnfMain
import DN.News.ArticleLines
import DN.News.ArticleProg

/-!
# DN.News.ArticleRun

The article program's functions over lines and fields, proven to do what `DN.News.ArticleLines` says of them. Each is
the program's: its body with a check of the failed flag after each call (`gd`).
-/

namespace DN.News.ArticleRun

open DN.Compiler DN.Compiler.Wp DN.Compiler.WpRet DN.Compiler.Frag DN.News.AbnfProg
open DN.News.AbnfSets DN.News.FunRun DN.News.AbnfLeaves
open DN.News.ScanRun (at_ at_add Vals vals_lookup vals_cons vals_set Fresh without lookup_head fresh_cons)
open DN.News.FramerCode (bw ev_var bw_ne0 bw_eq0)
open DN.News.AbnfComment (ev_inc)
open DN.News.ArticleProg (artMax guardL guardS)
open DN.News.ArticleLines
open DN.News.ArticleSpec (Bytes COLON)
open DN.News.CommandSpec (isWS)

variable {σ : Type}

/-- A function as the program holds it: a check of the failed flag after each call. -/
def gd (f : Syntax.PFun) : Syntax.PFun := { f with body := guardL f.body }

/-- **A loop whose body may return**, with an invariant: it holds after the loop, the condition false. -/
theorem fragR_while (o : Oracle σ) {R : Ret} {c : Syntax.PExpr} {C : PancakeExp} (hc : Lower.lowerExp c = some C)
    {body : List Syntax.PStmt} (hlow : LowKK body) {I : Assn σ} (hI : Safe.ClockFree I)
    (hr : ∀ u y v, I u → y ∈ declared body → I (restore u y v)) (hdef : ∀ u, I u → ∃ w, eval u C = some w)
    (hbody : FragR o R body (fun u => I u ∧ eval u C ≠ some 0) I) :
    FragR o R [.while c body] I (fun u => I u ∧ eval u C = some 0) := by
  obtain ⟨BODY, hBl⟩ := lowKK_fold hlow
  intro k Q _ hk
  refine ⟨.seq (.while_ C BODY) k, lowerK_one (by simp [Lower.lowerStmt1, hc, hBl]) rfl k, ?_⟩
  refine seq (WpRet.while_ (I := I) hdef ?_ hI) hk (fun s k' ⟨h, e⟩ => ⟨hI _ _ h, by rw [Safe.eval_clock]; exact e⟩)
  obtain ⟨c', hc', hsafe⟩ := fragR_close hbody hr
  rw [hBl] at hc'; cases hc'
  exact hsafe

/-- A body shown under a fact its states all give. -/
theorem fragR_pure {o : Oracle σ} {R : Ret} {xs : List Syntax.PStmt} {P P' : Assn σ} (Q : Prop) (hQ : ∀ s, P s → Q)
    (hl : LowKK xs) (h : Q → FragR o R xs P P') : FragR o R xs P P' := by
  by_cases q : Q
  · exact h q
  · intro k Qa _ _
    obtain ⟨c, hc⟩ := hl k
    exact ⟨c, hc, fun s hs => absurd (hQ s hs) q⟩

/-- The input read from a state of the body, its memory `m`. -/
theorem input_run {s1 u : PancakeState σ} {l : List (String × Value)} {m : Word → Word} {A : Word} {a : Bytes}
    (hin : InputAt m s1.memaddrs s1.be A a) (h : RunF s1 l (· = m) u) : InputAt u.memory u.memaddrs u.be A a := by
  rw [h.2, h.1.memaddrs, h.1.be]; exact hin

/-- The input's byte at the local `i`, its address `a + aInput + i`. -/
theorem inByte_eval {u : PancakeState σ} {A : Word} {a : Bytes} (hin : InputAt u.memory u.memaddrs u.be A a)
    {i : String} (ha : u.locals "a" = some A) {X : Nat} (hX : X < a.length)
    (hx : u.locals i = some (BitVec.ofNat 64 X)) :
    eval u (.loadByte (.op .add (.op .add (.var "a") (.const (BitVec.ofNat 64 aInput))) (.var i))) =
      some (BitVec.ofNat 64 (a[X]!).toNat) :=
  inputAt_eval hin hX (by simp only [eval, ha, hx]; rw [← at_add]; rfl)

theorem byte_lt (b : BitVec 8) : b.toNat < 2 ^ 64 := by have := b.isLt; omega

/-! ## Where a line ends -/

theorem eolOf_step (a : Bytes) {E LIM : Nat} (h : E + 1 < LIM) :
    eolOf a E LIM = if crlfAt a E then E else eolOf a (E + 1) LIM := by
  simp only [eolOf, show LIM - E = (LIM - (E + 1)) + 1 by omega, eolGo, if_pos h]

theorem eolOf_out (a : Bytes) {E LIM : Nat} (h : ¬E + 1 < LIM) : eolOf a E LIM = LIM := by
  unfold eolOf
  cases LIM - E with
  | zero => rfl
  | succ n => simp only [eolGo, if_neg h]

theorem crlf_bytes {a : Bytes} {E : Nat} (h : E + 1 < a.length) :
    crlfAt a E = (decide ((a[E]!).toNat = 13) && decide ((a[E + 1]!).toNat = 10)) := by
  have h0 : E < a.length := by omega
  simp only [crlfAt, List.getElem?_eq_getElem h0, List.getElem?_eq_getElem h, getElem!_pos a E h0,
    getElem!_pos a (E + 1) h]
  simp only [Option.some_beq_some, DN.News.FrameSpec.CR, DN.News.FrameSpec.LF]
  congr 1
  · by_cases e : a[E] = 13#8
    · simp [e]
    · have : (a[E]).toNat ≠ 13 := fun e' => e (BitVec.eq_of_toNat_eq e')
      simp [e, this]
  · by_cases e : a[E + 1] = 10#8
    · simp [e]
    · have : (a[E + 1]).toNat ≠ 10 := fun e' => e (BitVec.eq_of_toNat_eq e')
      simp [e, this]

theorem artEol_body : (ArticleProg.artEol .none).body =
    [areaAt ArticleProg.ofs, kept "lim" artMax, .dec "e" (Syntax.v "q"), .dec "go" (Syntax.n 1),
     .while (Syntax.v "go")
       [.ite (Syntax.eLt (Syntax.eAdd (Syntax.v "e") (Syntax.n 1)) (Syntax.v "lim"))
         [kept "e" (artMax - 2), .dec "c" (ArticleProg.inByte "e"),
          .dec "f" (Syntax.eAdd (Syntax.v "e") (Syntax.n 1)), .dec "d" (ArticleProg.inByte "f"),
          .ite (Syntax.eAnd (Syntax.eEq (Syntax.v "c") (Syntax.n 13)) (Syntax.eEq (Syntax.v "d") (Syntax.n 10)))
            [.assign "go" (Syntax.n 0)] [inc "e"]]
         [.assign "e" (Syntax.v "lim"), .assign "go" (Syntax.n 0)]],
     .ret (Syntax.v "e")] := rfl

theorem artEol_guard : guardL (ArticleProg.artEol .none).body = (ArticleProg.artEol .none).body := rfl

/-- What `artEol` gives back: where the line from `q` ends, the memory as in `m0`. -/
def EolRet (a : Bytes) (q lim : Nat) (m0 : Word → Word) : Ret :=
  fun v m => m = m0 ∧ v = BitVec.ofNat 64 (eolOf a q lim)

theorem artMax_eq : artMax = 65600 := rfl

/-- **`artEol` finds where a line ends**: the first CRLF from `q` before `lim`, or `lim`. -/
theorem artEol_ok (o : Oracle σ) {A : Word} {s1 : PancakeState σ} (hA : Area ArticleProg.ofs A s1) {a : Bytes}
    (hin : InputAt s1.memory s1.memaddrs s1.be A a) {Q LIM : Nat} (hQ : Q ≤ artMax) (hL : LIM ≤ a.length)
    (hLM : LIM ≤ artMax) (hq : s1.locals "q" = some (BitVec.ofNat 64 Q))
    (hl : s1.locals "lim" = some (BitVec.ofNat 64 LIM)) :
    ∃ body, Lower.lower (gd (ArticleProg.artEol .none)) = some body ∧
      SafeR o (fun s => s = s1) body (EolRet a Q LIM s1.memory) fun _ => False := by
  have hM := artMax_eq
  refine body_of ?_
  show FragR o _ (guardL (ArticleProg.artEol .none).body) _ _
  rw [artEol_guard, artEol_body]
  let L0 : List (String × Value) := [("a", A), ("q", BitVec.ofNat 64 Q), ("lim", BitVec.ofNat 64 LIM)]
  obtain ⟨EA, hEA⟩ := atOff_lower ArticleProg.ofs
  refine fragR_conseq (P0 := RunF s1 [("q", BitVec.ofNat 64 Q), ("lim", BitVec.ofNat 64 LIM)] (· = s1.memory))
    ?_ (entry_two hq hl) fun _ h => h
  refine fragR_append (xs := [_]) (fragR_of (runF_dec o hEA rfl (v := A) fun u h => areaAt_eval hA h.1.base hEA)) ?_
  refine fragR_append (xs := [_]) (fragR_of (kept_frag o (by decide) (runF_clock _ _ _) fun u h =>
    ⟨LIM, vals_lookup h.1.vals rfl, hLM⟩)) ?_
  refine fragR_append (xs := [_]) (fragR_of (runF_dec o rfl rfl (v := BitVec.ofNat 64 Q) fun u h =>
    ev_var (vals_lookup h.1.vals rfl))) ?_
  refine fragR_append (xs := [_]) (fragR_of (runF_dec o rfl rfl (v := BitVec.ofNat 64 1) fun _ _ => rfl)) ?_
  -- the loop
  let I : Assn σ := fun u => ∃ g E, RunF s1 (("go", BitVec.ofNat 64 g) :: ("e", BitVec.ofNat 64 E) :: L0)
    (· = s1.memory) u ∧ E ≤ artMax ∧ ((g = 1 ∧ eolOf a E LIM = eolOf a Q LIM) ∨ (g = 0 ∧ E = eolOf a Q LIM))
  have hIc : Safe.ClockFree I := fun u k ⟨g, E, h, hv⟩ => ⟨g, E, runF_clock _ _ _ u k h, hv⟩
  have hgo : ∀ u, I u → ∃ g, eval u (.var "go") = some (BitVec.ofNat 64 g) ∧ (g = 0 ∨ g = 1) ∧
      (∀ E, RunF s1 (("go", BitVec.ofNat 64 g) :: ("e", BitVec.ofNat 64 E) :: L0) (· = s1.memory) u → True) :=
    fun u ⟨g, E, h, _, hv⟩ => ⟨g, ev_var (vals_lookup h.1.vals rfl), by omega, fun _ _ => trivial⟩
  have hlowB : LowKK [Syntax.PStmt.ite (Syntax.eLt (Syntax.eAdd (Syntax.v "e") (Syntax.n 1)) (Syntax.v "lim"))
      [kept "e" (artMax - 2), .dec "c" (ArticleProg.inByte "e"), .dec "f" (Syntax.eAdd (Syntax.v "e") (Syntax.n 1)),
       .dec "d" (ArticleProg.inByte "f"),
       .ite (Syntax.eAnd (Syntax.eEq (Syntax.v "c") (Syntax.n 13)) (Syntax.eEq (Syntax.v "d") (Syntax.n 10)))
         [.assign "go" (Syntax.n 0)] [inc "e"]]
      [.assign "e" (Syntax.v "lim"), .assign "go" (Syntax.n 0)]] := lowK_any _ (k := .skip) rfl
  refine fragR_append (xs := [_]) (fragR_conseq (fragR_while o rfl hlowB hIc
    (fun u z v _ hz => by change z ∈ [] at hz; cases hz) (fun u hu => by
      obtain ⟨g, hg, _⟩ := hgo u hu; exact ⟨_, hg⟩) ?step)
    (fun u h => ⟨1, Q, h, hQ, .inl ⟨rfl, rfl⟩⟩) fun _ h => h) ?last
  case last =>
    refine fragR_ret o rfl fun u ⟨⟨g, E, h, _, hv⟩, h0⟩ => ⟨_, ev_var (vals_lookup h.1.vals rfl), h.2, ?_⟩
    rcases hv with ⟨rfl, -⟩ | ⟨rfl, hE⟩
    · rw [ev_var (vals_lookup h.1.vals rfl)] at h0; exact absurd h0 (by decide)
    · rw [hE]
  case step =>
    refine fragR_of (frag_conseq (P0 := fun u => ∃ E : Nat, (fun E u => RunF s1 (("go", BitVec.ofNat 64 1) ::
      ("e", BitVec.ofNat 64 E) :: L0) (· = s1.memory) u ∧ E ≤ artMax ∧ eolOf a E LIM = eolOf a Q LIM) E u)
      (frag_exists hlowB fun E => ?body) (fun u ⟨⟨g, E, h, hE, hv⟩, h0⟩ => ?pre) fun _ h => h)
    case pre =>
      rcases hv with ⟨rfl, hv⟩ | ⟨rfl, -⟩
      · exact ⟨E, h, hE, hv⟩
      · rw [ev_var (vals_lookup h.1.vals rfl)] at h0; exact absurd rfl h0
    case body =>
    let LE : List (String × Value) := ("go", BitVec.ofNat 64 1) :: ("e", BitVec.ofNat 64 E) :: L0
    refine frag_pure (E ≤ artMax ∧ eolOf a E LIM = eolOf a Q LIM) (fun u h => h.2) hlowB fun ⟨hE, hEq⟩ => ?_
    refine frag_conseq (P0 := RunF s1 LE (· = s1.memory)) ?_ (fun u h => h.1) fun _ h => h
    have hcond : ∀ u, RunF s1 LE (· = s1.memory) u →
        eval u (.cmp .less (.op .add (.var "e") (.const (BitVec.ofNat 64 1))) (.var "lim")) =
          some (bw (decide (E + 1 < LIM))) := fun u h =>
      FramerCode.eval_lt (by omega) (by omega) (ev_inc (vals_lookup h.1.vals rfl)) (ev_var (vals_lookup h.1.vals rfl))
    have hrI : ∀ u z v, I u → z ∈ declared [kept "e" (artMax - 2), .dec "c" (ArticleProg.inByte "e"),
        .dec "f" (Syntax.eAdd (Syntax.v "e") (Syntax.n 1)), .dec "d" (ArticleProg.inByte "f"),
        .ite (Syntax.eAnd (Syntax.eEq (Syntax.v "c") (Syntax.n 13)) (Syntax.eEq (Syntax.v "d") (Syntax.n 10)))
          [.assign "go" (Syntax.n 0)] [inc "e"]] → I (restore u z v) := fun u z v ⟨g, E', h, hv⟩ hz => by
      change z ∈ ["c", "f", "d"] at hz
      refine ⟨g, E', runF_restore h ?_ v, hv⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
      rcases hz with rfl | rfl | rfl <;> rfl
    have hmem : ∀ (g E' : Nat) (L : List (String × Value)), ("e", BitVec.ofNat 64 E') ∈ L → (∀ q ∈ L0, q ∈ L) →
        ∀ q ∈ ("go", BitVec.ofNat 64 g) :: ("e", BitVec.ofNat 64 E') :: L0, q ∈ ("go", BitVec.ofNat 64 g) :: L :=
      fun g E' L he hL q hq => by
        simp only [List.mem_cons] at hq
        rcases hq with rfl | rfl | hq
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ he
        · exact List.mem_cons_of_mem _ (hL q hq)
    refine frag_ite o rfl hIc (fun u h => ⟨_, hcond u h⟩) ?_ hrI ?_ (noDecl _ rfl)
    · -- a byte pair to read
      refine frag_pure (E + 1 < LIM) (fun u ⟨h, h0⟩ => by
        rw [hcond u h] at h0; exact of_decide_eq_true (bw_ne0 h0)) (lowK_any _ (k := .skip) rfl) fun hlt => ?_
      refine frag_conseq (P0 := RunF s1 LE (· = s1.memory)) ?_ (fun u h => h.1) fun _ h => h
      refine frag_append (xs := [_]) (kept_frag o (by decide) (runF_clock _ _ _) fun u h =>
        ⟨E, vals_lookup h.1.vals rfl, by omega⟩) ?_
      refine frag_append (xs := [_]) (runF_dec o rfl rfl (v := BitVec.ofNat 64 (a[E]!).toNat) fun u h =>
        inByte_eval (input_run hin h) (vals_lookup h.1.vals rfl) (by omega) (vals_lookup h.1.vals rfl)) ?_
      refine frag_append (xs := [_]) (runF_dec o rfl rfl (v := BitVec.ofNat 64 (E + 1)) fun u h =>
        ev_inc (vals_lookup h.1.vals rfl)) ?_
      refine frag_append (xs := [_]) (runF_dec o rfl rfl (v := BitVec.ofNat 64 (a[E + 1]!).toNat) fun u h =>
        inByte_eval (input_run hin h) (vals_lookup h.1.vals rfl) (by omega) (vals_lookup h.1.vals rfl)) ?_
      let LD : List (String × Value) := ("d", BitVec.ofNat 64 (a[E + 1]!).toNat) :: ("f", BitVec.ofNat 64 (E + 1)) ::
        ("c", BitVec.ofNat 64 (a[E]!).toNat) :: LE
      have hpair : ∀ u, RunF s1 LD (· = s1.memory) u →
          eval u (.op .and_ (.cmp .equal (.var "c") (.const (BitVec.ofNat 64 13)))
            (.cmp .equal (.var "d") (.const (BitVec.ofNat 64 10)))) = some (bw (crlfAt a E)) := fun u h => by
        rw [crlf_bytes (by omega)]
        exact FramerCode.eval_and (FramerCode.eval_eq (byte_lt _) (by decide) (ev_var (vals_lookup h.1.vals rfl)) rfl)
          (FramerCode.eval_eq (byte_lt _) (by decide) (ev_var (vals_lookup h.1.vals rfl)) rfl)
      have hL0 : ∀ q ∈ L0, q ∈ without "go" LD := fun q hq => by
        simp only [L0, List.mem_cons, List.not_mem_nil, or_false] at hq
        simp only [LD, LE, L0, without, List.mem_filter, List.mem_cons]
        rcases hq with rfl | rfl | rfl <;> simp
      refine frag_ite o rfl hIc (fun u h => ⟨_, hpair u h⟩) ?_ (noDecl _ rfl) ?_ (noDecl _ rfl)
      · -- the line ends at `E`
        refine frag_pure (crlfAt a E = true) (fun u ⟨h, h0⟩ => by rw [hpair u h] at h0; exact bw_ne0 h0)
          (lowK_any _ (k := .skip) rfl) fun hc => ?_
        refine frag_conseq (runF_set o rfl rfl (v := BitVec.ofNat 64 0) fun _ _ => rfl) (fun u h => h.1) fun u h =>
          ⟨0, E, runF_mono h (hmem 0 E _ (by simp [without, LE, L0]) hL0) fun _ e => e, hE,
            .inr ⟨rfl, by rw [← hEq, eolOf_step a hlt, if_pos hc]⟩⟩
      · -- no CRLF at `E`
        refine frag_pure (crlfAt a E = false) (fun u ⟨h, h0⟩ => by rw [hpair u h] at h0; exact bw_eq0 h0)
          (lowK_any _ (k := .skip) rfl) fun hc => ?_
        have hL0' : ∀ q ∈ L0, q ∈ without "e" LD := fun q hq => by
          simp only [L0, List.mem_cons, List.not_mem_nil, or_false] at hq
          simp only [LD, LE, L0, without, List.mem_filter, List.mem_cons]
          rcases hq with rfl | rfl | rfl <;> simp
        refine frag_conseq (runF_set o rfl rfl (v := BitVec.ofNat 64 (E + 1))
          (fun u h => ev_inc (vals_lookup h.1.vals rfl))) (fun u h => h.1) fun u h =>
          ⟨1, E + 1, runF_mono h (fun q hq => ?_) fun _ e => e, by omega,
            .inl ⟨rfl, by rw [← hEq, eolOf_step a hlt, if_neg (by simp [hc])]⟩⟩
        simp only [List.mem_cons] at hq
        rcases hq with rfl | rfl | hq
        · exact List.mem_cons_of_mem _ (by simp [without, LE, L0])
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (hL0' q hq)
    · -- past the bound: the line ends at `lim`
      refine frag_pure (¬E + 1 < LIM) (fun u ⟨h, h0⟩ => by
        rw [hcond u h] at h0; exact of_decide_eq_false (bw_eq0 h0)) (lowK_any _ (k := .skip) rfl) fun hlt => ?_
      refine frag_conseq (P0 := RunF s1 LE (· = s1.memory)) ?_ (fun u h => h.1) fun _ h => h
      refine frag_append (xs := [_]) (runF_set o rfl rfl (v := BitVec.ofNat 64 LIM) fun u h =>
        ev_var (vals_lookup h.1.vals rfl)) ?_
      refine frag_conseq (runF_set o rfl rfl (v := BitVec.ofNat 64 0) fun _ _ => rfl) (fun u h => h) fun u h =>
        ⟨0, LIM, runF_mono h (fun q hq => ?_) fun _ e => e, hLM, .inr ⟨rfl, by rw [← hEq, eolOf_out a hlt]⟩⟩
      simp only [List.mem_cons] at hq
      rcases hq with rfl | rfl | hq
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (by simp [without, LE, L0])
      · simp only [L0, List.mem_cons, List.not_mem_nil, or_false] at hq
        simp only [LE, L0, without, List.mem_filter, List.mem_cons]
        rcases hq with rfl | rfl | rfl <;> simp

/-! ## Calls -/

/-- The code holds each of the article program's functions as it lowers. -/
def ArtCode (code : String → Option (List String × PancakeProg)) : Prop :=
  ∀ f ∈ ArticleProg.functions ArticleSpec.spec (ArticleProg.entries ArticleSpec.spec) .none, ∀ body,
    Lower.lower f = some body → code f.name = some (f.params.map (·.2), body)

theorem broken_lower : Lower.lowerExp (word (Syntax.v "a") aBroken) =
    some (.loadWord (.op .add (.var "a") (.const (BitVec.ofNat 64 aBroken)))) := rfl

/-- **The check after a call**: with the failed flag clear, nothing returns. -/
theorem guard_frag (o : Oracle σ) {R : Ret} {A : Word} {s0 : PancakeState σ} (hA : Area ArticleProg.ofs A s0)
    {P : Assn σ} (hP : Safe.ClockFree P) (h : ∀ u, P u → u.locals "a" = some A ∧ u.memaddrs = s0.memaddrs ∧
      u.memory (at_ A aBroken) = 0) :
    FragR o R [ArticleProg.ifs (word (Syntax.v "a") aBroken) [.ret (Syntax.n 1)]] P P := by
  have hb : aBroken < aSets + slots * setSize :=
    Nat.lt_of_lt_of_le (Nat.lt_trans (by rw [aInput_eq]; decide) DN.News.AbnfMain.input_sets) (Nat.le_add_right _ _)
  have hev : ∀ u, P u → eval u (.loadWord (.op .add (.var "a") (.const (BitVec.ofNat 64 aBroken)))) = some 0 :=
    fun u hu => by
      obtain ⟨ha, hm, h0⟩ := h u hu
      rw [load_eval hA hm (y := aBroken) hb (by decide) (by simp only [eval, ha]; rfl), h0]
  refine fragR_ite o broken_lower hP (fun u hu => ⟨_, hev u hu⟩) ?_ (fun _ _ _ _ hy => by simp [declared] at hy)
    (fragR_of (frag_nil o fun u h => h.1)) (fun _ _ _ _ hy => by simp [declared] at hy)
  exact fragR_of (frag_unsat (lowKK_ret rfl) fun u ⟨hu, h0⟩ => h0 (hev u hu))

/-! ## White space alone -/

theorem isWS_bytes (b : BitVec 8) : (decide (b.toNat = 32) || decide (b.toNat = 9)) = isWS b := by
  revert b; decide

theorem artAllWS_body : ArticleProg.artAllWS.body =
    [areaAt ArticleProg.ofs, .dec "i" (Syntax.v "s"),
     .while (Syntax.eLt (Syntax.v "i") (Syntax.v "e"))
       [kept "i" (artMax - 1), .dec "b" (ArticleProg.inByte "i"),
        .ite (ArticleProg.isWS (Syntax.v "b")) [inc "i"] [.ret (Syntax.n 0)]],
     .ret (Syntax.n 1)] := rfl

theorem artAllWS_guard : guardL ArticleProg.artAllWS.body = ArticleProg.artAllWS.body := rfl

/-- What `artAllWS` gives back: whether every byte from `s` to `e` is white space, the memory as in `m0`. -/
def AllRet (a : Bytes) (s e : Nat) (m0 : Word → Word) : Ret :=
  fun v m => m = m0 ∧ v = bw ((seg a s e).all isWS)

theorem seg_mem (a : Bytes) {s i e : Nat} (h1 : s ≤ i) (h2 : i < e) (h3 : e ≤ a.length) : a[i]! ∈ seg a s e := by
  have hi : i < a.length := by omega
  have hlen := seg_length a (by omega : s ≤ e) h3
  have : (seg a s e)[i - s]? = some a[i] := by
    simp only [seg, List.getElem?_take, List.getElem?_drop, show s + (i - s) = i by omega,
      List.getElem?_eq_getElem hi]
    rw [if_pos (by omega)]
  rw [getElem!_pos a i hi]
  exact List.mem_of_getElem? this

/-- **`artAllWS` tells whether a run of bytes is white space alone.** -/
theorem artAllWS_ok (o : Oracle σ) {A : Word} {s1 : PancakeState σ} (hA : Area ArticleProg.ofs A s1) {a : Bytes}
    (hin : InputAt s1.memory s1.memaddrs s1.be A a) {S E : Nat} (hS : S ≤ artMax) (hE : E ≤ a.length)
    (hEM : E ≤ artMax) (hs : s1.locals "s" = some (BitVec.ofNat 64 S))
    (he : s1.locals "e" = some (BitVec.ofNat 64 E)) :
    ∃ body, Lower.lower (gd ArticleProg.artAllWS) = some body ∧
      SafeR o (fun s => s = s1) body (AllRet a S E s1.memory) fun _ => False := by
  have hM := artMax_eq
  refine body_of ?_
  show FragR o _ (guardL ArticleProg.artAllWS.body) _ _
  rw [artAllWS_guard, artAllWS_body]
  let L0 : List (String × Value) := [("a", A), ("s", BitVec.ofNat 64 S), ("e", BitVec.ofNat 64 E)]
  obtain ⟨EA, hEA⟩ := atOff_lower ArticleProg.ofs
  refine fragR_conseq (P0 := RunF s1 [("s", BitVec.ofNat 64 S), ("e", BitVec.ofNat 64 E)] (· = s1.memory))
    ?_ (entry_two hs he) fun _ h => h
  refine fragR_append (xs := [_]) (fragR_of (runF_dec o hEA rfl (v := A) fun u h => areaAt_eval hA h.1.base hEA)) ?_
  refine fragR_append (xs := [_]) (fragR_of (runF_dec o rfl rfl (v := BitVec.ofNat 64 S) fun u h =>
    ev_var (vals_lookup h.1.vals rfl))) ?_
  let I : Assn σ := fun u => ∃ i, RunF s1 (("i", BitVec.ofNat 64 i) :: L0) (· = s1.memory) u ∧ S ≤ i ∧
    (i ≤ E ∨ i = S) ∧ i ≤ artMax ∧ (seg a S i).all isWS = true
  have hIc : Safe.ClockFree I := fun u k ⟨i, h, hv⟩ => ⟨i, runF_clock _ _ _ u k h, hv⟩
  have hcond : ∀ u i, RunF s1 (("i", BitVec.ofNat 64 i) :: L0) (· = s1.memory) u → i ≤ artMax →
      eval u (.cmp .less (.var "i") (.var "e")) = some (bw (decide (i < E))) := fun u i h hi =>
    FramerCode.eval_lt (by omega) (by omega) (ev_var (vals_lookup h.1.vals rfl)) (ev_var (vals_lookup h.1.vals rfl))
  have hlowB : LowKK [kept "i" (artMax - 1), .dec "b" (ArticleProg.inByte "i"),
      .ite (ArticleProg.isWS (Syntax.v "b")) [inc "i"] [.ret (Syntax.n 0)]] := lowK_any _ (k := .skip) rfl
  refine fragR_append (xs := [_]) (fragR_conseq (fragR_while o rfl hlowB hIc
    (fun u z v ⟨i, h, hv⟩ hz => by
      change z ∈ ["b"] at hz
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hz; subst hz
      exact ⟨i, runF_restore h rfl v, hv⟩) (fun u ⟨i, h, hv⟩ => ⟨_, hcond u i h hv.2.2.1⟩) ?step)
    (fun u h => ⟨S, h, Nat.le_refl _, .inr rfl, hS, by simp [seg_self]⟩) fun _ h => h) ?last
  case last =>
    refine fragR_ret o rfl fun u ⟨⟨i, h, hSi, hiE, hiM, hall⟩, h0⟩ => ⟨_, rfl, h.2, ?_⟩
    rw [hcond u i h hiM] at h0
    have hge := of_decide_eq_false (bw_eq0 h0)
    have : (seg a S E).all isWS = true := by
      rcases hiE with hiE | hiS
      · rw [show E = i by omega]; exact hall
      · simp [seg, show E - S = 0 by omega]
    rw [this]; rfl
  case step =>
    refine fragR_conseq (P0 := fun u => ∃ i : Nat, (fun i u => RunF s1 (("i", BitVec.ofNat 64 i) :: L0)
      (· = s1.memory) u ∧ S ≤ i ∧ i < E ∧ (seg a S i).all isWS = true) i u)
      (fragR_exists hlowB fun i => ?_)
      (fun u ⟨⟨i, h, hSi, _, hiM, hall⟩, h0⟩ => ⟨i, h, hSi, by
        rw [hcond u i h hiM] at h0; exact of_decide_eq_true (bw_ne0 h0), hall⟩) fun _ h => h
    refine fragR_pure (S ≤ i ∧ i < E ∧ (seg a S i).all isWS = true) (fun u h => h.2) hlowB
      fun ⟨hSi, hiE, hall⟩ => ?_
    refine fragR_conseq (P0 := RunF s1 (("i", BitVec.ofNat 64 i) :: L0) (· = s1.memory)) ?_ (fun u h => h.1)
      fun _ h => h
    refine fragR_append (xs := [_]) (fragR_of (kept_frag o (by decide) (runF_clock _ _ _) fun u h =>
      ⟨i, vals_lookup h.1.vals rfl, by omega⟩)) ?_
    refine fragR_append (xs := [_]) (fragR_of (runF_dec o rfl rfl (v := BitVec.ofNat 64 (a[i]!).toNat) fun u h =>
      inByte_eval (input_run hin h) (vals_lookup h.1.vals rfl) (by omega) (vals_lookup h.1.vals rfl))) ?_
    let LB : List (String × Value) := ("b", BitVec.ofNat 64 (a[i]!).toNat) :: ("i", BitVec.ofNat 64 i) :: L0
    have hws : ∀ u, RunF s1 LB (· = s1.memory) u →
        eval u (.op .or_ (.cmp .equal (.var "b") (.const (BitVec.ofNat 64 32)))
          (.cmp .equal (.var "b") (.const (BitVec.ofNat 64 9)))) = some (bw (isWS a[i]!)) := fun u h => by
      rw [← isWS_bytes, ← DN.News.AbnfComment.bw_or]
      exact FramerCode.eval_or (FramerCode.eval_eq (byte_lt _) (by decide) (ev_var (vals_lookup h.1.vals rfl)) rfl)
        (FramerCode.eval_eq (byte_lt _) (by decide) (ev_var (vals_lookup h.1.vals rfl)) rfl)
    refine fragR_if o rfl (lowK_any _ (k := .skip) rfl) (lowKK_ret rfl) hIc
      (fun u z v h hz => by change z ∈ [] at hz; cases hz) (fun u z v h hz => by change z ∈ [] at hz; cases hz)
      (b := isWS a[i]!) (fun u h => hws u h) (fun hw => ?_) (fun hw => ?_)
    · refine fragR_of (frag_conseq (runF_set o rfl rfl (v := BitVec.ofNat 64 (i + 1)) fun u h =>
        ev_inc (vals_lookup h.1.vals rfl)) (fun u h => h) fun u h => ⟨i + 1, runF_mono h (fun q hq => ?_) fun _ e => e,
          by omega, .inl (by omega), by omega, by
            have hw' : isWS a[i] = true := by rwa [getElem!_pos a i (by omega)] at hw
            rw [seg_succ a hSi (by omega), List.all_append]; simp [hall, hw']⟩)
      simp only [List.mem_cons] at hq
      rcases hq with rfl | hq
      · exact List.mem_cons_self
      · simp only [L0, List.mem_cons, List.not_mem_nil, or_false] at hq
        simp only [L0, without, List.mem_filter, List.mem_cons]
        rcases hq with rfl | rfl | rfl <;> simp
    · refine fragR_ret o rfl fun u h => ⟨_, rfl, h.2, ?_⟩
      have : (seg a S E).all isWS = false := by
        cases hc : (seg a S E).all isWS
        · rfl
        · exact absurd (List.all_eq_true.1 hc _ (seg_mem a hSi hiE hE)) (by rw [hw]; decide)
      rw [this]; rfl

/-! ## The article's words -/

/-- The article's area starts where the grammar's ends: the kernel works out the grammar's once, here. -/
theorem X_eq : ArticleProg.X = aSets + slots * setSize := by decide +kernel

/-- The article's words lie past the grammar's, the whole area below `2 ^ 22`. -/
theorem X_lt : ArticleProg.X < 2 ^ 22 := by decide

theorem X_val : ArticleProg.X = 497936 := rfl
theorem xName_eq : ArticleProg.xName = 505392 := rfl
theorem xFirst_eq : ArticleProg.xFirst = 576408 := rfl

theorem X_mod : ArticleProg.X % 8 = 0 := by decide

theorem sets_le_X : aSets ≤ ArticleProg.X := X_eq ▸ Nat.le_add_right _ _

/-- The article's words up to the tables, each addressable. -/
def ArtDom (A : Word) (dm : Word → Bool) : Prop :=
  ∀ x, aSets ≤ x → x < ArticleProg.xFirst → x % 8 = 0 → dm (at_ A x) = true

/-- The article's scalar words, `w 0` to `w 31`, lie before the tables. -/
theorem w_lt {i : Nat} (hi : i < 32) : ArticleProg.w i < ArticleProg.xFirst := by
  simp only [ArticleProg.w, X_val, xFirst_eq]; omega

theorem w_ge (i : Nat) : aSets ≤ ArticleProg.w i := Nat.le_trans sets_le_X (Nat.le_add_right _ _)

theorem w_mod (i : Nat) : ArticleProg.w i % 8 = 0 := by simp only [ArticleProg.w, X_val]; omega

theorem w_lt64 {i : Nat} (hi : i < 32) : ArticleProg.w i < 2 ^ 64 := by simp only [ArticleProg.w, X_val]; omega

theorem w_ne {i j : Nat} (hi : i < 32) (hj : j < 32) (h : i ≠ j) (A : Word) :
    at_ A (ArticleProg.w i) ≠ at_ A (ArticleProg.w j) :=
  DN.News.ScanRun.at_ne (w_lt64 hi) (w_lt64 hj) (by simp only [ArticleProg.w]; omega)

theorem w_ne0 (i : Nat) : (ArticleProg.w i == 0) = false := by
  simp only [ArticleProg.w, X_val, beq_eq_false_iff_ne]; omega

/-- Word `i`'s address as the program writes it, lowered without working out the offset. -/
theorem atOffW_lower (i : Nat) : Lower.lowerExp (Syntax.atOff (Syntax.v "a") (ArticleProg.w i)) =
    some (.op .add (.var "a") (.const (BitVec.ofNat 64 (ArticleProg.w i)))) := by
  simp only [Syntax.atOff, w_ne0, Bool.false_eq_true, if_false]; rfl

theorem wd_lower (i : Nat) : Lower.lowerExp (word (Syntax.v "a") (ArticleProg.w i)) =
    some (.loadWord (.op .add (.var "a") (.const (BitVec.ofNat 64 (ArticleProg.w i))))) := by
  simp only [word, Syntax.atOff, w_ne0, Bool.false_eq_true, if_false]; rfl

/-- A scalar word of the article's is addressable. -/
theorem artDom_w {A : Word} {dm : Word → Bool} (h : ArtDom A dm) {i : Nat} (hi : i < 32) :
    dm (at_ A (ArticleProg.w i)) = true := h _ (w_ge i) (w_lt hi) (w_mod i)

/-- The failed flag is not one of the article's words. -/
theorem broken_ne_w {i : Nat} (hi : i < 32) (A : Word) : at_ A aBroken ≠ at_ A (ArticleProg.w i) :=
  DN.News.ScanRun.at_ne (by decide) (w_lt64 hi) (fun e => by
    have := w_ge i; have : aBroken < aSets :=
      Nat.lt_trans (by rw [aInput_eq]; decide) DN.News.AbnfMain.input_sets
    omega)

/-- The input's bytes lie below the slots. -/
theorem input_below : aInput + artMax ≤ aSets := by
  have h1 := DN.News.AbnfLayout.input_le; have h2 := DN.News.AbnfLayout.io_le; have h3 := DN.News.AbnfLayout.pow_lt
  rw [inputMax_eq] at h1; rw [artMax_eq]
  generalize aInput = i at *; generalize aIO = io at *; generalize aPow = pw at *; generalize aSets = st at *; omega

/-- **The input is kept** where only words from the slots on changed. -/
theorem input_keep {A : Word} (hA8 : A.toNat % 8 = 0) {a : Bytes} (ha : a.length ≤ artMax) {m1 m : Word → Word}
    {dm : Word → Bool} {be : Bool} (h : InputAt m1 dm be A a) (keep : ∀ x, x < aSets → m (at_ A x) = m1 (at_ A x)) :
    InputAt m dm be A a := by
  intro x hx
  have hb := input_below
  have := h x hx
  unfold memLoadByte at this ⊢
  rw [DN.News.ScanRun.align_at hA8] at this ⊢
  rw [keep ((aInput + x) / 8 * 8) (by omega)]; exact this

/-- A word of the article's stored. -/
theorem runF_storeA (o : Oracle σ) {A : Word} {s0 : PancakeState σ} {l : List (String × Value)}
    {F G : (Word → Word) → Prop} {d e : Syntax.PExpr} {D E : PancakeExp} (hd : Lower.lowerExp d = some D)
    (he : Lower.lowerExp e = some E) {y : Nat} (hy : s0.memaddrs (at_ A y) = true)
    (hD : ∀ u, RunF s0 l F u → eval u D = some (at_ A y)) {val : (Word → Word) → Word}
    (hE : ∀ u, RunF s0 l F u → eval u E = some (val u.memory)) (hG : ∀ m, F m → G (upd m (at_ A y) (val m))) :
    Frag o [.store d e] (RunF s0 l F) (RunF s0 l G) :=
  store_frag o hd he (runF_clock _ _ _) fun u h =>
    ⟨_, _, hD u h, hE u h, by rw [h.1.memaddrs]; exact hy,
      ⟨h.1.vals, h.1.memaddrs, h.1.base, h.1.code, h.1.be⟩, hG _ h.2⟩

/-- A word of the article's read. -/
theorem loadA_eval {A : Word} {s0 u : PancakeState σ} (hm : u.memaddrs = s0.memaddrs) {y : Nat}
    (hy : s0.memaddrs (at_ A y) = true) {E : PancakeExp} (hE : eval u E = some (at_ A y)) :
    eval u (.loadWord E) = some (u.memory (at_ A y)) :=
  WpBytes.eval_load hE (by rw [hm]; exact hy) rfl

theorem atA_eval {u : PancakeState σ} {A : Word} (ha : u.locals "a" = some A) {y : Nat} :
    eval u (.op .add (.var "a") (.const (BitVec.ofNat 64 y))) = some (at_ A y) := by
  simp only [eval, ha]; rfl

theorem ev_sub {u : PancakeState σ} {a b : PancakeExp} {x y : Nat} (ha : eval u a = some (BitVec.ofNat 64 (y + x)))
    (hb : eval u b = some (BitVec.ofNat 64 y)) : eval u (.op .sub a b) = some (BitVec.ofNat 64 x) := by
  simp only [eval, ha, hb]
  congr 1
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
  omega

theorem ev_add2 {u : PancakeState σ} {x : String} {X : Nat} (h : u.locals x = some (BitVec.ofNat 64 X)) :
    eval u (.op .add (.var x) (.const (BitVec.ofNat 64 2))) = some (BitVec.ofNat 64 (X + 2)) := ev_inc h

/-! ## Calls of the article's functions -/

/-- **A call of one of the article's functions**, the check after it passed: the failed flag stays clear. -/
theorem gcall_frag (o : Oracle σ) {R : Ret} {A : Word} {s0 : PancakeState σ} (hA : Area ArticleProg.ofs A s0)
    (hcode : ArtCode s0.code) {rt : String} (hra : rt ≠ "a") {f : Syntax.PFun}
    (hf : gd f ∈ ArticleProg.functions ArticleSpec.spec (ArticleProg.entries ArticleSpec.spec) .none)
    (hnd : (f.params.map (·.2)).Nodup) {as : List Syntax.PExpr} {args : List PancakeExp}
    (has : Lower.lowerArgs as = some args) {l : List (String × Value)} (hla : l.lookup "a" = some A)
    {F : (Word → Word) → Prop} {vs : List Value} (hlen : (f.params.map (·.2)).length = vs.length)
    (hargs : ∀ u, RunF s0 l F u → evalArgs u args = some vs) {Rf : (Word → Word) → Ret}
    (hbody : ∀ s1 : PancakeState σ, Area ArticleProg.ofs A s1 → s1.code = s0.code → s1.memaddrs = s0.memaddrs →
      s1.be = s0.be → (∀ k, s1.locals k = ((f.params.map (·.2)).zip vs).lookup k) → F s1.memory →
      ∃ body, Lower.lower (gd f) = some body ∧ SafeR o (fun s => s = s1) body (Rf s1.memory) fun _ => False)
    (hrt : Fresh rt l = true) {G : Value → (Word → Word) → Prop} (hG : ∀ m m' v, F m → Rf m v m' → G v m')
    (hbr : ∀ v m, G v m → m (at_ A aBroken) = 0) :
    FragR o R (guardS (.call rt f.name as)) (RunF s0 l F) (fun u => ∃ v, RunF s0 ((rt, v) :: l) (G v) u) := by
  refine fragR_append (xs := [_]) (fragR_of (DN.News.AbnfGen.progCall_frag o hA (f := gd f) hnd has
    (fun body hb => hcode _ hf body hb) hlen hargs hbody hrt hG)) ?_
  exact guard_frag o hA (fun u k ⟨v, h⟩ => ⟨v, runF_clock _ _ _ u k h⟩) fun u ⟨v, h⟩ =>
    ⟨vals_lookup h.1.vals (by rw [DN.News.ScanRun.lookup_cons_ne (Ne.symm hra)]; exact hla), h.1.memaddrs,
      hbr v _ h.2⟩

theorem mem_artEol : gd (ArticleProg.artEol .none) ∈
    ArticleProg.functions ArticleSpec.spec (ArticleProg.entries ArticleSpec.spec) .none :=
  List.mem_append_right _ (List.mem_map.2 ⟨_, List.mem_cons_self, rfl⟩)

/-- **A call of `artEol`**: the place where the line ends, the memory as it was. -/
theorem eolCall_frag (o : Oracle σ) {R : Ret} {A : Word} {s0 : PancakeState σ} (hA : Area ArticleProg.ofs A s0)
    (hcode : ArtCode s0.code) {a : Bytes} {rt : String} (hra : rt ≠ "a") {l : List (String × Value)}
    (hla : l.lookup "a" = some A) (hrt : Fresh rt l = true) {F : (Word → Word) → Prop} {e1 e2 : Syntax.PExpr}
    {E1 E2 : PancakeExp} (he1 : Lower.lowerExp e1 = some E1) (he2 : Lower.lowerExp e2 = some E2) {Q LIM : Nat}
    (hQ : Q ≤ artMax) (hL : LIM ≤ a.length) (hLM : LIM ≤ artMax)
    (hv1 : ∀ u, RunF s0 l F u → eval u E1 = some (BitVec.ofNat 64 Q))
    (hv2 : ∀ u, RunF s0 l F u → eval u E2 = some (BitVec.ofNat 64 LIM))
    (hF : ∀ m, F m → InputAt m s0.memaddrs s0.be A a ∧ m (at_ A aBroken) = 0) :
    FragR o R (guardS (.call rt "artEol" [e1, e2])) (RunF s0 l F)
      (RunF s0 ((rt, BitVec.ofNat 64 (eolOf a Q LIM)) :: l) F) := by
  refine fragR_conseq (gcall_frag o hA hcode hra (f := ArticleProg.artEol .none) mem_artEol (by decide)
    (DN.News.AbnfGen.lowerArgs_two he1 he2) hla (vs := [BitVec.ofNat 64 Q, BitVec.ofNat 64 LIM]) rfl
    (fun u h => by simp only [evalArgs, hv1 u h, hv2 u h]) (Rf := EolRet a Q LIM)
    (fun s1 hA1 _ hm hbe hloc hF1 => artEol_ok o hA1 (by rw [hm, hbe]; exact (hF _ hF1).1) hQ hL hLM
      ((hloc "q").trans rfl) ((hloc "lim").trans rfl)) hrt
    (G := fun v m => F m ∧ v = BitVec.ofNat 64 (eolOf a Q LIM)) (fun m m' v hm ⟨e1, e2⟩ => ⟨e1 ▸ hm, e2⟩)
    fun v m h => (hF m h.1).2) (fun u h => h) fun u ⟨v, h⟩ => ?_
  obtain ⟨hm, hv⟩ := h.2
  subst hv; exact ⟨h.1, hm⟩

/-! ## A field's end -/

theorem artField_guarded : guardL ArticleProg.artField.body =
    [areaAt ArticleProg.ofs, .dec "sep" (word (Syntax.v "a") ArticleProg.xSep), kept "sep" artMax,
     .dec "j" (Syntax.v "p"), .dec "go" (Syntax.n 1),
     .while (Syntax.v "go")
       [kept "j" (artMax - 1), .dec "b" (ArticleProg.inByte "j"),
        .ite (Syntax.eEq (Syntax.v "b") (Syntax.n 58)) [.assign "go" (Syntax.n 0)] [inc "j"]],
     ArticleProg.setW ArticleProg.xNl (Syntax.eSub (Syntax.v "j") (Syntax.v "p")),
     .call "e" "artEol" [Syntax.v "j", Syntax.v "sep"],
     ArticleProg.ifs (word (Syntax.v "a") aBroken) [.ret (Syntax.n 1)],
     ArticleProg.setW ArticleProg.xE1 (Syntax.v "e"),
     .dec "q" (Syntax.eAdd (Syntax.v "e") (Syntax.n 2)), .assign "go" (Syntax.n 1),
     .while (Syntax.v "go")
       [.ite (Syntax.eLt (Syntax.v "q") (Syntax.v "sep"))
         [kept "q" (artMax - 1), .dec "c" (ArticleProg.inByte "q"),
          .ite (ArticleProg.isWS (Syntax.v "c"))
            [.call "f" "artEol" [Syntax.v "q", Syntax.v "sep"],
             ArticleProg.ifs (word (Syntax.v "a") aBroken) [.ret (Syntax.n 1)],
             .assign "q" (Syntax.eAdd (Syntax.v "f") (Syntax.n 2))]
            [.assign "go" (Syntax.n 0)]]
         [.assign "go" (Syntax.n 0)]],
     .ret (Syntax.v "q")] := rfl

/-- What `artField` gives back: the field's end `q`. Its name's length `k` goes in `xNl`, its first line's end `e` in
`xE1`. -/
def FieldRet (A : Word) (q k e : Nat) (m0 : Word → Word) : Ret := fun v m =>
  m = upd (upd m0 (at_ A ArticleProg.xNl) (BitVec.ofNat 64 k)) (at_ A ArticleProg.xE1) (BitVec.ofNat 64 e) ∧
    v = BitVec.ofNat 64 q

theorem colon_byte {a : Bytes} {j : Nat} (hj : j < a.length) :
    decide ((a[j]!).toNat = 58) = decide (a[j]? = some COLON) := by
  rw [List.getElem?_eq_getElem hj, getElem!_pos a j hj]
  by_cases h : a[j] = COLON
  · simp [h, COLON]
  · have : (a[j]).toNat ≠ 58 := fun e => h (BitVec.eq_of_toNat_eq (by rw [e]; rfl))
    simp [h, this]

/-- A store to word `i` of the article's keeps the input and the failed flag. -/
theorem keep_w {A : Word} (hA8 : A.toNat % 8 = 0) {a : Bytes} (ha : a.length ≤ artMax) {m : Word → Word}
    {dm : Word → Bool} {be : Bool} (hin : InputAt m dm be A a) (hb : m (at_ A aBroken) = 0) {i : Nat} (hi : i < 32)
    (v : Word) : InputAt (upd m (at_ A (ArticleProg.w i)) v) dm be A a ∧
      upd m (at_ A (ArticleProg.w i)) v (at_ A aBroken) = 0 :=
  ⟨input_keep hA8 ha hin fun x hx => upd_ne _ (DN.News.ScanRun.at_ne (by have := X_lt; have := sets_le_X; omega)
      (w_lt64 hi) (by have := w_ge i; omega)),
    by rw [upd_ne _ (broken_ne_w hi A)]; exact hb⟩

/-- **`artField` finds where the field at `p` ends**: past its last continuation line. It leaves its name's length in
`xNl` and its first line's end in `xE1`. -/
theorem artField_ok (o : Oracle σ) {A : Word} {s1 : PancakeState σ} (hA : Area ArticleProg.ofs A s1)
    (hD : ArtDom A s1.memaddrs) (hcode : ArtCode s1.code) {a : Bytes} (hlen : a.length ≤ artMax)
    (hin : InputAt s1.memory s1.memaddrs s1.be A a) (hb : s1.memory (at_ A aBroken) = 0) {SEP P e : Nat}
    {L : List (Nat × Nat)} (hf : FieldAt a SEP P e L) (hsep : s1.memory (at_ A ArticleProg.xSep) = BitVec.ofNat 64 SEP)
    (hp : s1.locals "p" = some (BitVec.ofNat 64 P)) :
    ∃ body, Lower.lower (gd ArticleProg.artField) = some body ∧
      SafeR o (fun s => s = s1) body (FieldRet A (nextOf a L SEP) (nameLen a P e) e s1.memory) fun _ => False := by
  have hM := artMax_eq
  have hS := lines_sep hf.lines
  have hSL : SEP ≤ a.length := Nat.le_of_lt hS.2.2
  have hm := lines_mem hf.lines (P, e) List.mem_cons_self
  obtain ⟨hk0, hke, hcol, hnoc⟩ := fieldAt_colon hf
  have heol := fieldAt_eol hf
  generalize hK : nameLen a P e = K at hk0 hke hcol hnoc heol ⊢
  refine body_of ?_
  show FragR o _ (guardL ArticleProg.artField.body) _ _
  rw [artField_guarded]
  let L0 : List (String × Value) := [("sep", BitVec.ofNat 64 SEP), ("a", A), ("p", BitVec.ofNat 64 P)]
  obtain ⟨EA, hEA⟩ := atOff_lower ArticleProg.ofs
  refine fragR_conseq (P0 := RunF s1 [("p", BitVec.ofNat 64 P)] (· = s1.memory)) ?_ (entry_one hp) fun _ h => h
  refine fragR_append (xs := [_]) (fragR_of (runF_dec o hEA rfl (v := A) fun u h => areaAt_eval hA h.1.base hEA)) ?_
  refine fragR_append (xs := [_]) (fragR_of (runF_dec o (wd_lower 16) rfl (v := BitVec.ofNat 64 SEP) fun u h => by
    rw [loadA_eval h.1.memaddrs (artDom_w hD (i := 16) (by decide)) (atA_eval (vals_lookup h.1.vals rfl)), h.2]
    exact congrArg some hsep)) ?_
  refine fragR_append (xs := [_]) (fragR_of (kept_frag o (by decide) (runF_clock _ _ _) fun u h =>
    ⟨SEP, vals_lookup h.1.vals rfl, by omega⟩)) ?_
  refine fragR_append (xs := [_]) (fragR_of (runF_dec o rfl rfl (v := BitVec.ofNat 64 P) fun u h =>
    ev_var (vals_lookup h.1.vals rfl))) ?_
  refine fragR_append (xs := [_]) (fragR_of (runF_dec o rfl rfl (v := BitVec.ofNat 64 1) fun _ _ => rfl)) ?_
  -- the name: up to the colon
  let I1 : Assn σ := fun u => ∃ g J, RunF s1 (("go", BitVec.ofNat 64 g) :: ("j", BitVec.ofNat 64 J) :: L0)
    (· = s1.memory) u ∧ P ≤ J ∧ J ≤ P + K ∧ (g = 1 ∨ (g = 0 ∧ J = P + K))
  have hI1 : Safe.ClockFree I1 := fun u k ⟨g, J, h, hv⟩ => ⟨g, J, runF_clock _ _ _ u k h, hv⟩
  have hlow1 : LowKK [kept "j" (artMax - 1), .dec "b" (ArticleProg.inByte "j"),
      .ite (Syntax.eEq (Syntax.v "b") (Syntax.n 58)) [.assign "go" (Syntax.n 0)] [inc "j"]] :=
    lowK_any _ (k := .skip) rfl
  refine fragR_append (xs := [_]) (fragR_of (frag_conseq (frag_while o rfl hlow1 hI1
    (fun u z v ⟨g, J, h, hv⟩ hz => by
      change z ∈ ["b"] at hz
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hz; subst hz
      exact ⟨g, J, runF_restore h rfl v, hv⟩)
    (fun u ⟨g, J, h, _⟩ => ⟨_, ev_var (vals_lookup h.1.vals rfl)⟩) ?colon)
    (fun u h => ⟨1, P, h, Nat.le_refl _, by omega, .inl rfl⟩)
    (fun u ⟨⟨g, J, h, hPJ, hJK, hv⟩, h0⟩ => show RunF s1 (("go", BitVec.ofNat 64 0) ::
        ("j", BitVec.ofNat 64 (P + K)) :: L0) (· = s1.memory) u by
      rcases hv with rfl | ⟨rfl, rfl⟩
      · rw [ev_var (vals_lookup h.1.vals rfl)] at h0; exact absurd h0 (by decide)
      · exact h))) ?rest
  case colon =>
    refine frag_conseq (P0 := fun u => ∃ J : Nat, (fun J u => RunF s1 (("go", BitVec.ofNat 64 1) ::
      ("j", BitVec.ofNat 64 J) :: L0) (· = s1.memory) u ∧ P ≤ J ∧ J ≤ P + K) J u)
      (frag_exists hlow1 fun J => ?body) (fun u ⟨⟨g, J, h, hPJ, hJK, hv⟩, h0⟩ => ⟨J, ?pre, hPJ, hJK⟩) fun _ h => h
    case pre =>
      rcases hv with rfl | ⟨rfl, -⟩
      · exact h
      · rw [ev_var (vals_lookup h.1.vals rfl)] at h0; exact absurd rfl h0
    case body =>
    refine frag_pure (P ≤ J ∧ J ≤ P + K) (fun u h => h.2) hlow1 fun ⟨hPJ, hJK⟩ => ?_
    refine frag_conseq (P0 := RunF s1 (("go", BitVec.ofNat 64 1) :: ("j", BitVec.ofNat 64 J) :: L0)
      (· = s1.memory)) ?_ (fun u h => h.1) fun _ h => h
    have hJ : J < a.length := by omega
    refine frag_append (xs := [_]) (kept_frag o (by decide) (runF_clock _ _ _) fun u h =>
      ⟨J, vals_lookup h.1.vals rfl, by omega⟩) ?_
    refine frag_append (xs := [_]) (runF_dec o rfl rfl (v := BitVec.ofNat 64 (a[J]!).toNat) fun u h =>
      inByte_eval (input_run hin h) (vals_lookup h.1.vals rfl) hJ (vals_lookup h.1.vals rfl)) ?_
    refine DN.News.ScanRun.frag_if o rfl (lowK_any _ (k := .skip) rfl) (lowK_any _ (k := .skip) rfl) rfl rfl hI1
      (b := decide (a[J]? = some COLON)) (fun u h => by
        rw [← colon_byte hJ]
        exact FramerCode.eval_eq (byte_lt _) (by decide) (ev_var (vals_lookup h.1.vals rfl)) rfl) (fun hc => ?_)
      (fun hc => ?_)
    · have hJK' : J = P + K := Classical.byContradiction fun hne => hnoc J hPJ (by omega) (of_decide_eq_true hc)
      refine frag_conseq (runF_set o rfl rfl (v := BitVec.ofNat 64 0) fun _ _ => rfl) (fun u h => h) fun u h =>
        ⟨0, J, runF_mono h (fun q hq => ?_) fun _ e => e, hPJ, hJK, .inr ⟨rfl, hJK'⟩⟩
      simp only [List.mem_cons] at hq
      rcases hq with rfl | rfl | hq
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (by simp [without])
      · simp only [L0, List.mem_cons, List.not_mem_nil, or_false] at hq
        simp only [L0, without, List.mem_filter, List.mem_cons]
        rcases hq with rfl | rfl | rfl <;> simp
    · have hJK' : J ≠ P + K := fun e' => by subst e'; rw [hcol] at hc; exact absurd hc (by decide)
      refine frag_conseq (runF_set o rfl rfl (v := BitVec.ofNat 64 (J + 1)) fun u h =>
        ev_inc (vals_lookup h.1.vals rfl)) (fun u h => h) fun u h =>
        ⟨1, J + 1, runF_mono h (fun q hq => ?_) fun _ e => e, by omega, by omega, .inl rfl⟩
      simp only [List.mem_cons] at hq
      rcases hq with rfl | rfl | hq
      · exact List.mem_cons_of_mem _ (by simp [without])
      · exact List.mem_cons_self
      · simp only [L0, List.mem_cons, List.not_mem_nil, or_false] at hq
        simp only [L0, without, List.mem_filter, List.mem_cons]
        rcases hq with rfl | rfl | rfl <;> simp
  case rest =>
  let m1 := upd s1.memory (at_ A ArticleProg.xNl) (BitVec.ofNat 64 K)
  let m2 := upd m1 (at_ A ArticleProg.xE1) (BitVec.ofNat 64 e)
  have hk1 := keep_w hA.hA hlen hin hb (i := 17) (by decide) (BitVec.ofNat 64 K)
  have hk2 := keep_w hA.hA hlen hk1.1 hk1.2 (i := 18) (by decide) (BitVec.ofNat 64 e)
  -- the name's length stored
  refine fragR_append (xs := [_]) (fragR_of (runF_storeA o (atOffW_lower 17) rfl (y := ArticleProg.w 17)
    (artDom_w hD (by decide)) (fun u h => atA_eval (vals_lookup h.1.vals rfl)) (val := fun _ => BitVec.ofNat 64 K)
    (fun u h => ev_sub (y := P) (ev_var (vals_lookup h.1.vals rfl)) (ev_var (vals_lookup h.1.vals rfl)))
    (G := (· = m1)) fun m hm => by subst hm; rfl)) ?_
  -- the first line's end
  refine fragR_append (xs := [_, _]) (fragR_conseq (eolCall_frag o hA hcode (rt := "e") (by decide)
    (l := ("go", BitVec.ofNat 64 0) :: ("j", BitVec.ofNat 64 (P + K)) :: L0) rfl rfl (F := (· = m1))
    (e1 := Syntax.v "j") (e2 := Syntax.v "sep") rfl rfl (Q := P + K) (LIM := SEP) (by omega) hSL (by omega)
    (fun u h => ev_var (vals_lookup h.1.vals rfl)) (fun u h => ev_var (vals_lookup h.1.vals rfl))
    fun m hm => by rw [hm]; exact hk1) (fun u h => h) fun u h => by rw [heol] at h; exact h) ?_
  refine fragR_append (xs := [_]) (fragR_of (runF_storeA o (atOffW_lower 18) rfl (y := ArticleProg.w 18)
    (artDom_w hD (by decide)) (fun u h => atA_eval (vals_lookup h.1.vals rfl)) (val := fun _ => BitVec.ofNat 64 e)
    (fun u h => ev_var (vals_lookup h.1.vals rfl)) (G := (· = m2)) fun m hm => by subst hm; rfl)) ?_
  refine fragR_append (xs := [_]) (fragR_of (runF_dec o rfl rfl (v := BitVec.ofNat 64 (e + 2)) fun u h =>
    ev_add2 (vals_lookup h.1.vals rfl))) ?_
  let L1 : List (String × Value) := ("e", BitVec.ofNat 64 e) :: ("j", BitVec.ofNat 64 (P + K)) :: L0
  refine fragR_append (xs := [_]) (fragR_of (frag_conseq (runF_set o rfl rfl (v := BitVec.ofNat 64 1) fun _ _ => rfl)
    (fun u h => h) (P' := RunF s1 (("go", BitVec.ofNat 64 1) :: ("q", BitVec.ofNat 64 (e + 2)) :: L1) (· = m2))
    fun u h => runF_mono h (fun q hq => by
      simp only [List.mem_cons] at hq
      rcases hq with rfl | rfl | hq
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (by simp [without])
      · simp only [L1, L0, List.mem_cons, List.not_mem_nil, or_false] at hq
        simp only [L0, without, List.mem_filter, List.mem_cons]
        rcases hq with rfl | rfl | rfl | rfl | rfl <;> simp) fun _ e => e)) ?_
  -- the continuation lines
  let I2 : Assn σ := fun u => ∃ g Q, RunF s1 (("go", BitVec.ofNat 64 g) :: ("q", BitVec.ofNat 64 Q) :: L1)
    (· = m2) u ∧ Q ≤ SEP ∧ ((g = 1 ∧ ∃ L', Lines a Q L' SEP ∧ nextOf a L' SEP = nextOf a L SEP) ∨
      (g = 0 ∧ Q = nextOf a L SEP))
  have hI2 : Safe.ClockFree I2 := fun u k ⟨g, Q, h, hv⟩ => ⟨g, Q, runF_clock _ _ _ u k h, hv⟩
  have hlow2 : LowKK [Syntax.PStmt.ite (Syntax.eLt (Syntax.v "q") (Syntax.v "sep"))
      [kept "q" (artMax - 1), .dec "c" (ArticleProg.inByte "q"),
       .ite (ArticleProg.isWS (Syntax.v "c"))
         [.call "f" "artEol" [Syntax.v "q", Syntax.v "sep"],
          ArticleProg.ifs (word (Syntax.v "a") aBroken) [.ret (Syntax.n 1)],
          .assign "q" (Syntax.eAdd (Syntax.v "f") (Syntax.n 2))]
         [.assign "go" (Syntax.n 0)]]
      [.assign "go" (Syntax.n 0)]] := lowK_any _ (k := .skip) rfl
  have hL := (lines_tail hf.lines).2
  refine fragR_append (xs := [_]) (fragR_conseq (fragR_while o rfl hlow2 hI2
    (fun u z v _ hz => by change z ∈ [] at hz; cases hz)
    (fun u ⟨g, Q, h, _⟩ => ⟨_, ev_var (vals_lookup h.1.vals rfl)⟩) ?cont)
    (fun u h => ⟨1, e + 2, h, by have := lines_sep hL; omega, .inl ⟨rfl, L, hL, rfl⟩⟩) fun _ h => h) ?last
  case last =>
    refine fragR_ret o rfl fun u ⟨⟨g, Q, h, _, hv⟩, h0⟩ => ⟨_, ev_var (vals_lookup h.1.vals rfl), ?_⟩
    rcases hv with ⟨rfl, -⟩ | ⟨rfl, hQ⟩
    · rw [ev_var (vals_lookup h.1.vals rfl)] at h0; exact absurd h0 (by decide)
    · exact ⟨h.2, by rw [hQ]⟩
  case cont =>
    refine fragR_conseq (P0 := fun u => ∃ t : Nat × List (Nat × Nat), (fun t u => RunF s1 (("go", BitVec.ofNat 64 1) ::
      ("q", BitVec.ofNat 64 t.1) :: L1) (· = m2) u ∧ t.1 ≤ SEP ∧ Lines a t.1 t.2 SEP ∧
        nextOf a t.2 SEP = nextOf a L SEP) t u)
      (fragR_exists hlow2 fun t => ?body) (fun u ⟨⟨g, Q, h, hQ, hv⟩, h0⟩ => ?pre) fun _ h => h
    case pre =>
      rcases hv with ⟨rfl, L', hL', hn⟩ | ⟨rfl, -⟩
      · exact ⟨(Q, L'), h, hQ, hL', hn⟩
      · rw [ev_var (vals_lookup h.1.vals rfl)] at h0; exact absurd rfl h0
    case body =>
    obtain ⟨Q, L'⟩ := t
    refine fragR_pure (Q ≤ SEP ∧ Lines a Q L' SEP ∧ nextOf a L' SEP = nextOf a L SEP) (fun u h => h.2) hlow2
      fun ⟨hQ, hL', hn⟩ => ?_
    refine fragR_conseq (P0 := RunF s1 (("go", BitVec.ofNat 64 1) :: ("q", BitVec.ofNat 64 Q) :: L1) (· = m2)) ?_
      (fun u h => h.1) fun _ h => h
    have hrst : ∀ (L2 : List (String × Value)) (g Q' : Nat) (u : PancakeState σ),
        RunF s1 L2 (· = m2) u → (∀ q ∈ ("go", BitVec.ofNat 64 g) :: ("q", BitVec.ofNat 64 Q') :: L1, q ∈ L2) →
        Q' ≤ SEP → ((g = 1 ∧ ∃ L', Lines a Q' L' SEP ∧ nextOf a L' SEP = nextOf a L SEP) ∨
          (g = 0 ∧ Q' = nextOf a L SEP)) → I2 u :=
      fun L2 g Q' u h hm hQ' hv => ⟨g, Q', runF_mono h hm fun _ e => e, hQ', hv⟩
    have hL1 : ∀ (L2 : List (String × Value)), (∀ q ∈ L1, q ∈ L2) → ∀ q ∈ L1, q ∈ L2 := fun _ h => h
    refine fragR_if o rfl (lowK_any _ (k := .skip) rfl) (lowK_any _ (k := .skip) rfl) hI2
      (fun u z v ⟨g, Q', h, hv⟩ hz => by
        change z ∈ ["c"] at hz
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hz; subst hz
        exact ⟨g, Q', runF_restore h rfl v, hv⟩) (fun u z v h hz => by change z ∈ [] at hz; cases hz)
      (b := decide (Q < SEP)) (fun u h => FramerCode.eval_lt (by omega) (by omega)
        (ev_var (vals_lookup h.1.vals rfl)) (ev_var (vals_lookup h.1.vals rfl))) (fun hq => ?_) (fun hq => ?_)
    · have hq := of_decide_eq_true hq
      obtain ⟨e', L'', rfl, heol', he2, hqe, hel, hL''⟩ := lines_cons hL' hq
      refine fragR_append (xs := [_]) (fragR_of (kept_frag o (by decide) (runF_clock _ _ _) fun u h =>
        ⟨Q, vals_lookup h.1.vals rfl, by omega⟩)) ?_
      refine fragR_append (xs := [_]) (fragR_of (runF_dec o rfl rfl (v := BitVec.ofNat 64 (a[Q]!).toNat) fun u h =>
        inByte_eval (input_run hk2.1 h) (vals_lookup h.1.vals rfl) (by omega) (vals_lookup h.1.vals rfl))) ?_
      refine fragR_if o rfl (lowK_any _ (k := .skip) rfl) (lowK_any _ (k := .skip) rfl) hI2
        (fun u z v ⟨g, Q', h, hv⟩ hz => by
          change z ∈ ["f"] at hz
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hz; subst hz
          exact ⟨g, Q', runF_restore h rfl v, hv⟩) (fun u z v h hz => by change z ∈ [] at hz; cases hz)
        (b := isWS a[Q]!) (fun u h => by
          show eval u _ = some (bw (isWS a[Q]!))
          rw [← isWS_bytes, ← DN.News.AbnfComment.bw_or]
          exact FramerCode.eval_or (FramerCode.eval_eq (byte_lt _) (by decide) (ev_var (vals_lookup h.1.vals rfl)) rfl)
            (FramerCode.eval_eq (byte_lt _) (by decide) (ev_var (vals_lookup h.1.vals rfl)) rfl))
        (fun hw => ?_) (fun hw => ?_)
      · -- a continuation: past its line
        have hc : cont a (Q, e') = true := by rw [cont_byte (by omega)]; exact hw
        refine fragR_append (xs := [_, _]) (eolCall_frag o hA hcode (rt := "f") (by decide) rfl rfl (F := (· = m2))
          (e1 := Syntax.v "q") (e2 := Syntax.v "sep") rfl rfl (Q := Q) (LIM := SEP) (by omega) hSL (by omega)
          (fun u h => ev_var (vals_lookup h.1.vals rfl)) (fun u h => ev_var (vals_lookup h.1.vals rfl))
          fun m hm => by rw [hm]; exact hk2) ?_
        rw [heol']
        refine fragR_of (frag_conseq (runF_set o rfl rfl (v := BitVec.ofNat 64 (e' + 2)) fun u h =>
          ev_add2 (vals_lookup h.1.vals rfl)) (fun u h => h) fun u h => hrst _ 1 (e' + 2) u h ?_ he2
            (.inl ⟨rfl, L'', hL'', by rw [← hn, nextOf_cont hc]⟩))
        intro q hq
        simp only [List.mem_cons] at hq
        rcases hq with rfl | rfl | hq
        · exact List.mem_cons_of_mem _ (by simp [without])
        · exact List.mem_cons_self
        · simp only [L1, L0, List.mem_cons, List.not_mem_nil, or_false] at hq
          simp only [L1, L0, without, List.mem_filter, List.mem_cons]
          rcases hq with rfl | rfl | rfl | rfl | rfl <;> simp
      · -- the next field's start
        have hc : cont a (Q, e') = false := by rw [cont_byte (by omega)]; exact hw
        refine fragR_of (frag_conseq (runF_set o rfl rfl (v := BitVec.ofNat 64 0) fun _ _ => rfl) (fun u h => h)
          fun u h => hrst _ 0 Q u h ?_ hQ (.inr ⟨rfl, by rw [← hn, nextOf_stop hc]⟩))
        intro q hq
        simp only [List.mem_cons] at hq
        rcases hq with rfl | rfl | hq
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (by simp [without])
        · simp only [L1, L0, List.mem_cons, List.not_mem_nil, or_false] at hq
          simp only [L1, L0, without, List.mem_filter, List.mem_cons]
          rcases hq with rfl | rfl | rfl | rfl | rfl <;> simp
    · -- the empty line reached
      have hq := of_decide_eq_false hq
      have hnil := lines_at_sep hL' (by omega)
      subst hnil
      refine fragR_of (frag_conseq (runF_set o rfl rfl (v := BitVec.ofNat 64 0) fun _ _ => rfl) (fun u h => h)
        fun u h => hrst _ 0 Q u h ?_ hQ (.inr ⟨rfl, by rw [← hn, nextOf_nil]; omega⟩))
      intro q hq
      simp only [List.mem_cons] at hq
      rcases hq with rfl | rfl | hq
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (by simp [without])
      · simp only [L1, L0, List.mem_cons, List.not_mem_nil, or_false] at hq
        simp only [L1, L0, without, List.mem_filter, List.mem_cons]
        rcases hq with rfl | rfl | rfl | rfl | rfl <;> simp

/-! ## Calls of `artField` and `artAllWS` -/

/-- The memory `artField` leaves: the name's length and the first line's end stored. -/
def fieldMem (A : Word) (k e : Nat) (m0 : Word → Word) : Word → Word :=
  upd (upd m0 (at_ A ArticleProg.xNl) (BitVec.ofNat 64 k)) (at_ A ArticleProg.xE1) (BitVec.ofNat 64 e)

theorem mem_artField : gd ArticleProg.artField ∈
    ArticleProg.functions ArticleSpec.spec (ArticleProg.entries ArticleSpec.spec) .none :=
  List.mem_append_right _ (List.mem_map.2 ⟨ArticleProg.artField, List.mem_of_getElem? (i := 2) rfl, rfl⟩)

theorem mem_artAllWS : gd ArticleProg.artAllWS ∈
    ArticleProg.functions ArticleSpec.spec (ArticleProg.entries ArticleSpec.spec) .none :=
  List.mem_append_right _ (List.mem_map.2 ⟨ArticleProg.artAllWS, List.mem_of_getElem? (i := 3) rfl, rfl⟩)

theorem fieldMem_keep {A : Word} (hA8 : A.toNat % 8 = 0) {a : Bytes} (ha : a.length ≤ artMax) {m : Word → Word}
    {dm : Word → Bool} {be : Bool} (hin : InputAt m dm be A a) (hb : m (at_ A aBroken) = 0) (k e : Nat) :
    InputAt (fieldMem A k e m) dm be A a ∧ fieldMem A k e m (at_ A aBroken) = 0 :=
  have h1 := keep_w hA8 ha hin hb (i := 17) (by decide) (BitVec.ofNat 64 k)
  keep_w hA8 ha h1.1 h1.2 (i := 18) (by decide) (BitVec.ofNat 64 e)

/-- **A call of `artField`** on a field's start. -/
theorem fieldCall_frag (o : Oracle σ) {R : Ret} {A : Word} {s0 : PancakeState σ} (hA : Area ArticleProg.ofs A s0)
    (hD : ArtDom A s0.memaddrs) (hcode : ArtCode s0.code) {a : Bytes} (hlen : a.length ≤ artMax) {rt : String}
    (hra : rt ≠ "a") {l : List (String × Value)} (hla : l.lookup "a" = some A) (hrt : Fresh rt l = true)
    {m0 : Word → Word} {e1 : Syntax.PExpr} {E1 : PancakeExp} (he1 : Lower.lowerExp e1 = some E1) {SEP P e : Nat}
    {L : List (Nat × Nat)} (hf : FieldAt a SEP P e L)
    (hv1 : ∀ u, RunF s0 l (· = m0) u → eval u E1 = some (BitVec.ofNat 64 P))
    (hin : InputAt m0 s0.memaddrs s0.be A a) (hb : m0 (at_ A aBroken) = 0)
    (hsep : m0 (at_ A ArticleProg.xSep) = BitVec.ofNat 64 SEP) :
    FragR o R (guardS (.call rt "artField" [e1])) (RunF s0 l (· = m0))
      (RunF s0 ((rt, BitVec.ofNat 64 (nextOf a L SEP)) :: l) (· = fieldMem A (nameLen a P e) e m0)) := by
  refine fragR_conseq (gcall_frag o hA hcode hra (f := ArticleProg.artField) mem_artField (by decide)
    (args := [E1]) (by simp [Lower.lowerArgs, he1]) hla (vs := [BitVec.ofNat 64 P]) rfl (fun u h => by simp only
        [evalArgs, hv1 u h])
    (Rf := FieldRet A (nextOf a L SEP) (nameLen a P e) e)
    (fun s1 hA1 hc hm hbe hloc hF1 => artField_ok o hA1 (by rw [hm]; exact hD) (by rw [hc]; exact hcode) hlen
      (by rw [hm, hbe, hF1]; exact hin) (by rw [hF1]; exact hb) hf (by rw [hF1]; exact hsep) ((hloc "p").trans rfl))
    hrt (G := fun v m => m = fieldMem A (nameLen a P e) e m0 ∧ v = BitVec.ofNat 64 (nextOf a L SEP))
    (fun m m' v hm ⟨e1, e2⟩ => ⟨by rw [e1, hm]; rfl, e2⟩)
    fun v m h => by rw [h.1]; exact (fieldMem_keep hA.hA hlen hin hb _ _).2) (fun u h => h) fun u ⟨v, h⟩ => ?_
  obtain ⟨hm, hv⟩ := h.2
  subst hv; exact ⟨h.1, hm⟩

/-- **A call of `artAllWS`.** -/
theorem allCall_frag (o : Oracle σ) {R : Ret} {A : Word} {s0 : PancakeState σ} (hA : Area ArticleProg.ofs A s0)
    (hcode : ArtCode s0.code) {a : Bytes} {rt : String} (hra : rt ≠ "a") {l : List (String × Value)}
    (hla : l.lookup "a" = some A) (hrt : Fresh rt l = true) {F : (Word → Word) → Prop} {e1 e2 : Syntax.PExpr}
    {E1 E2 : PancakeExp} (he1 : Lower.lowerExp e1 = some E1) (he2 : Lower.lowerExp e2 = some E2) {S E : Nat}
    (hS : S ≤ artMax) (hE : E ≤ a.length) (hEM : E ≤ artMax)
    (hv1 : ∀ u, RunF s0 l F u → eval u E1 = some (BitVec.ofNat 64 S))
    (hv2 : ∀ u, RunF s0 l F u → eval u E2 = some (BitVec.ofNat 64 E))
    (hF : ∀ m, F m → InputAt m s0.memaddrs s0.be A a ∧ m (at_ A aBroken) = 0) :
    FragR o R (guardS (.call rt "artAllWS" [e1, e2])) (RunF s0 l F)
      (RunF s0 ((rt, bw ((seg a S E).all isWS)) :: l) F) := by
  refine fragR_conseq (gcall_frag o hA hcode hra (f := ArticleProg.artAllWS) mem_artAllWS (by decide)
    (DN.News.AbnfGen.lowerArgs_two he1 he2) hla (vs := [BitVec.ofNat 64 S, BitVec.ofNat 64 E]) rfl
    (fun u h => by simp only [evalArgs, hv1 u h, hv2 u h]) (Rf := AllRet a S E)
    (fun s1 hA1 _ hm hbe hloc hF1 => artAllWS_ok o hA1 (by rw [hm, hbe]; exact (hF _ hF1).1) hS hE hEM
      ((hloc "s").trans rfl) ((hloc "e").trans rfl)) hrt
    (G := fun v m => F m ∧ v = bw ((seg a S E).all isWS)) (fun m m' v hm ⟨e1, e2⟩ => ⟨e1 ▸ hm, e2⟩)
    fun v m h => (hF m h.1).2) (fun u h => h) fun u ⟨v, h⟩ => ?_
  obtain ⟨hm, hv⟩ := h.2
  subst hv; exact ⟨h.1, hm⟩

/-! ## A blank line in a field -/

/-- The check after a call. -/
def brk : Syntax.PStmt := ArticleProg.ifs (word (Syntax.v "a") aBroken) [.ret (Syntax.n 1)]

theorem artBlank_guarded : guardL ArticleProg.artBlank.body =
    [areaAt ArticleProg.ofs, .call "fe" "artField" [Syntax.v "p"], brk,
     .dec "nl" (word (Syntax.v "a") ArticleProg.xNl), .dec "e1" (word (Syntax.v "a") ArticleProg.xE1),
     .call "x" "artAllWS" [Syntax.eAdd (Syntax.eAdd (Syntax.v "p") (Syntax.v "nl")) (Syntax.n 1), Syntax.v "e1"], brk,
     ArticleProg.ifs (Syntax.v "x") [.ret (Syntax.n 1)],
     .dec "q" (Syntax.eAdd (Syntax.v "e1") (Syntax.n 2)),
     .while (Syntax.eLt (Syntax.v "q") (Syntax.v "fe"))
       [.call "f" "artEol" [Syntax.v "q", Syntax.v "fe"], brk,
        .call "y" "artAllWS" [Syntax.v "q", Syntax.v "f"], brk,
        ArticleProg.ifs (Syntax.v "y") [.ret (Syntax.n 1)], .assign "q" (Syntax.eAdd (Syntax.v "f") (Syntax.n 2))],
     .ret (Syntax.n 0)] := rfl

/-- What `artBlank` gives back: whether a line of the field's body is white space alone, `artField`'s words stored. -/
def BlankRet (A : Word) (k e : Nat) (b : Bool) (m0 : Word → Word) : Ret := fun v m => m = fieldMem A k e m0 ∧ v = bw b

theorem ev_add3 {u : PancakeState σ} {x y : String} {X Y : Nat} (hx : u.locals x = some (BitVec.ofNat 64 X))
    (hy : u.locals y = some (BitVec.ofNat 64 Y)) :
    eval u (.op .add (.op .add (.var x) (.var y)) (.const (BitVec.ofNat 64 1))) = some (BitVec.ofNat 64 (X + Y +
        1)) := by
  simp only [eval, hx, hy]; rw [← BitVec.ofNat_add, ← BitVec.ofNat_add]

theorem fieldMem_nl (A : Word) (k e : Nat) (m0 : Word → Word) :
    fieldMem A k e m0 (at_ A ArticleProg.xNl) = BitVec.ofNat 64 k :=
  (upd_ne (BitVec.ofNat 64 e) (w_ne (i := 17) (j := 18) (by decide) (by decide) (by decide) A)).trans (upd_eq _ _ _)

theorem fieldMem_e1 (A : Word) (k e : Nat) (m0 : Word → Word) :
    fieldMem A k e m0 (at_ A ArticleProg.xE1) = BitVec.ofNat 64 e := upd_eq _ _ _

/-- **`artBlank` finds a line of white space alone** in the body of the field at `p` (RFC 5536 §2.2). -/
theorem artBlank_ok (o : Oracle σ) {A : Word} {s1 : PancakeState σ} (hA : Area ArticleProg.ofs A s1)
    (hD : ArtDom A s1.memaddrs) (hcode : ArtCode s1.code) {a : Bytes} (hlen : a.length ≤ artMax)
    (hin : InputAt s1.memory s1.memaddrs s1.be A a) (hb : s1.memory (at_ A aBroken) = 0) {SEP P e : Nat}
    {L : List (Nat × Nat)} (hf : FieldAt a SEP P e L) (hsep : s1.memory (at_ A ArticleProg.xSep) = BitVec.ofNat 64 SEP)
    (hp : s1.locals "p" = some (BitVec.ofNat 64 P)) :
    ∃ body, Lower.lower (gd ArticleProg.artBlank) = some body ∧
      SafeR o (fun s => s = s1) body (BlankRet A (nameLen a P e) e
        ((seg a (P + nameLen a P e + 1) e).all isWS || blankL a L) s1.memory) fun _ => False := by
  have hM := artMax_eq
  have hS := lines_sep hf.lines
  have hSL : SEP ≤ a.length := Nat.le_of_lt hS.2.2
  have hm := lines_mem hf.lines (P, e) List.mem_cons_self
  simp only at hm
  obtain ⟨hk0, hke, -, -⟩ := fieldAt_colon hf
  have hL := (lines_tail hf.lines).2
  have hFE := nextOf_ge hL
  generalize hK : nameLen a P e = K at hk0 hke ⊢
  generalize hFE' : nextOf a L SEP = FE at hFE
  let M := fieldMem A K e s1.memory
  have hkM := fieldMem_keep hA.hA hlen hin hb K e
  refine body_of ?_
  show FragR o _ (guardL ArticleProg.artBlank.body) _ _
  rw [artBlank_guarded]
  obtain ⟨EA, hEA⟩ := atOff_lower ArticleProg.ofs
  refine fragR_conseq (P0 := RunF s1 [("p", BitVec.ofNat 64 P)] (· = s1.memory)) ?_ (entry_one hp) fun _ h => h
  refine fragR_append (xs := [_]) (fragR_of (runF_dec o hEA rfl (v := A) fun u h => areaAt_eval hA h.1.base hEA)) ?_
  refine fragR_append (xs := [_, _]) (fragR_conseq (fieldCall_frag o hA hD hcode hlen (rt := "fe") (by decide)
    (l := [("a", A), ("p", BitVec.ofNat 64 P)]) rfl rfl (m0 := s1.memory) (e1 := Syntax.v "p") rfl hf
    (fun u h => ev_var (vals_lookup h.1.vals rfl)) hin hb hsep) (fun u h => h) fun u h => by
      rw [hK, hFE'] at h; exact h) ?_
  refine fragR_append (xs := [_]) (fragR_of (runF_dec o (wd_lower 17) rfl (v := BitVec.ofNat 64 K) fun u h => by
    rw [loadA_eval h.1.memaddrs (artDom_w hD (i := 17) (by decide)) (atA_eval (vals_lookup h.1.vals rfl)), h.2]
    exact congrArg some (fieldMem_nl A K e _))) ?_
  refine fragR_append (xs := [_]) (fragR_of (runF_dec o (wd_lower 18) rfl (v := BitVec.ofNat 64 e) fun u h => by
    rw [loadA_eval h.1.memaddrs (artDom_w hD (i := 18) (by decide)) (atA_eval (vals_lookup h.1.vals rfl)), h.2]
    exact congrArg some (fieldMem_e1 A K e _))) ?_
  refine fragR_append (xs := [_, _]) (allCall_frag o hA hcode (a := a) (rt := "x") (by decide) rfl rfl (F := (· = M))
    rfl rfl (S := P + K + 1) (E := e) (by omega) (by omega) (by omega)
    (fun u h => ev_add3 (vals_lookup h.1.vals rfl) (vals_lookup h.1.vals rfl))
    (fun u h => ev_var (vals_lookup h.1.vals rfl)) fun m hm => by rw [hm]; exact hkM) ?_
  have hlowR : LowKK [.dec "q" (Syntax.eAdd (Syntax.v "e1") (Syntax.n 2)),
      .while (Syntax.eLt (Syntax.v "q") (Syntax.v "fe"))
       [.call "f" "artEol" [Syntax.v "q", Syntax.v "fe"], brk,
        .call "y" "artAllWS" [Syntax.v "q", Syntax.v "f"], brk,
        ArticleProg.ifs (Syntax.v "y") [.ret (Syntax.n 1)], .assign "q" (Syntax.eAdd (Syntax.v "f") (Syntax.n 2))],
      .ret (Syntax.n 0)] := lowK_any _ (k := .skip) rfl
  cases hb1 : (seg a (P + K + 1) e).all isWS with
  | true =>
    refine fragR_append (xs := [_]) (fragR_if o rfl (lowKK_ret rfl) (lowK_any _ (k := .skip) rfl)
      (Q := fun _ => False) (fun _ _ h => h) (fun _ _ _ h _ => h) (fun _ _ _ h _ => h) (b := true)
      (fun u h => by rw [ev_var (vals_lookup h.1.vals rfl)]; rfl) (fun _ => fragR_ret o rfl fun u h =>
        ⟨_, rfl, h.2, rfl⟩) fun e => absurd e (by decide)) (fragR_of (frag_unsat hlowR fun _ h => h))
  | false =>
    let B : List (String × Value) := ("x", bw false) :: ("e1", BitVec.ofNat 64 e) ::
      ("nl", BitVec.ofNat 64 K) :: ("fe", BitVec.ofNat 64 FE) :: [("a", A), ("p", BitVec.ofNat 64 P)]
    refine fragR_append (xs := [_]) (fragR_if o rfl (lowKK_ret rfl) (lowK_any _ (k := .skip) rfl)
      (Q := RunF s1 B (· = M)) (runF_clock _ _ _) (fun _ _ _ _ hy => by simp [declared] at hy)
      (fun _ _ _ _ hy => by simp [declared] at hy) (b := false)
      (fun u h => by rw [ev_var (vals_lookup h.1.vals rfl)]; rfl) (fun e => absurd e (by decide))
      fun _ => fragR_of (frag_nil o fun u h => h)) ?_
    refine fragR_append (xs := [_]) (fragR_of (runF_dec o rfl rfl (v := BitVec.ofNat 64 (e + 2)) fun u h =>
      ev_add2 (vals_lookup h.1.vals rfl))) ?_
    let I : Assn σ := fun u => ∃ Q L1, RunF s1 (("q", BitVec.ofNat 64 Q) :: B) (· = M) u ∧ Lines a Q L1 SEP ∧
      nextOf a L1 SEP = FE ∧ blankL a L1 = blankL a L
    have hIc : Safe.ClockFree I := fun u k ⟨Q, L1, h, hv⟩ => ⟨Q, L1, runF_clock _ _ _ u k h, hv⟩
    have hcond : ∀ u Q L1, RunF s1 (("q", BitVec.ofNat 64 Q) :: B) (· = M) u → Lines a Q L1 SEP →
        nextOf a L1 SEP = FE → eval u (.cmp .less (.var "q") (.var "fe")) = some (bw (decide (Q < FE))) :=
      fun u Q L1 h hL1 hn => by
        have := (nextOf_ge hL1); rw [hn] at this
        exact FramerCode.eval_lt (by omega) (by omega) (ev_var (vals_lookup h.1.vals rfl))
          (ev_var (vals_lookup h.1.vals rfl))
    have hlowB : LowKK [.call "f" "artEol" [Syntax.v "q", Syntax.v "fe"], brk,
        .call "y" "artAllWS" [Syntax.v "q", Syntax.v "f"], brk,
        ArticleProg.ifs (Syntax.v "y") [.ret (Syntax.n 1)], .assign "q" (Syntax.eAdd (Syntax.v "f") (Syntax.n 2))] :=
      lowK_any _ (k := .skip) rfl
    refine fragR_append (xs := [_]) (fragR_conseq (fragR_while o rfl hlowB hIc
      (fun u z v ⟨Q, L1, h, hv⟩ hz => by
        change z ∈ ["f", "y"] at hz
        refine ⟨Q, L1, runF_restore h ?_ v, hv⟩
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
        rcases hz with rfl | rfl <;> rfl)
      (fun u ⟨Q, L1, h, hL1, hn, _⟩ => ⟨_, hcond u Q L1 h hL1 hn⟩) ?step)
      (fun u h => ⟨e + 2, L, h, hL, hFE', rfl⟩) fun _ h => h) ?last
    case last =>
      refine fragR_ret o rfl fun u ⟨⟨Q, L1, h, hL1, hn, hbl⟩, h0⟩ => ⟨_, rfl, h.2, ?_⟩
      rw [hcond u Q L1 h hL1 hn] at h0
      have hge := of_decide_eq_false (bw_eq0 h0)
      have := (nextOf_ge hL1).1; rw [hn] at this
      rw [← hbl, blankL_stop hL1 (by omega)]; rfl
    case step =>
      refine fragR_conseq (P0 := fun u => ∃ t : Nat × List (Nat × Nat), (fun t u =>
        RunF s1 (("q", BitVec.ofNat 64 t.1) :: B) (· = M) u ∧ Lines a t.1 t.2 SEP ∧ nextOf a t.2 SEP = FE ∧
          blankL a t.2 = blankL a L ∧ t.1 < FE) t u)
        (fragR_exists hlowB fun t => ?_) (fun u ⟨⟨Q, L1, h, hL1, hn, hbl⟩, h0⟩ => ⟨(Q, L1), h, hL1, hn, hbl, by
          rw [hcond u Q L1 h hL1 hn] at h0; exact of_decide_eq_true (bw_ne0 h0)⟩) fun _ h => h
      obtain ⟨Q, L1⟩ := t
      refine fragR_pure (Lines a Q L1 SEP ∧ nextOf a L1 SEP = FE ∧ blankL a L1 = blankL a L ∧ Q < FE)
        (fun u h => h.2) hlowB fun ⟨hL1, hn, hbl, hQ⟩ => ?_
      refine fragR_conseq (P0 := RunF s1 (("q", BitVec.ofNat 64 Q) :: B) (· = M)) ?_ (fun u h => h.1) fun _ h => h
      have hQS : Q < SEP := by have := hFE.2; omega
      obtain ⟨e', L2, rfl, heol', he2, hqe, hel, hL2⟩ := lines_cons hL1 hQS
      have hc : cont a (Q, e') = true := by
        cases hc : cont a (Q, e')
        · rw [nextOf_stop hc] at hn; omega
        · rfl
      rw [nextOf_cont hc] at hn
      have hge2 := (nextOf_ge hL2).1; rw [hn] at hge2
      have heolF : eolOf a Q FE = e' := by
        rw [eolOf_lim a (lim := SEP) (by omega) (by rw [heol']; omega) (by rw [heol']; omega), heol']
      refine fragR_append (xs := [_, _]) (eolCall_frag o hA hcode (a := a) (rt := "f") (by decide) rfl rfl
        (F := (· = M)) (e1 := Syntax.v "q") (e2 := Syntax.v "fe") rfl rfl (Q := Q) (LIM := FE) (by omega) (by omega)
        (by omega) (fun u h => ev_var (vals_lookup h.1.vals rfl)) (fun u h => ev_var (vals_lookup h.1.vals rfl))
        fun m hm => by rw [hm]; exact hkM) ?_
      rw [heolF]
      refine fragR_append (xs := [_, _]) (allCall_frag o hA hcode (a := a) (rt := "y") (by decide) rfl rfl
        (F := (· = M)) rfl rfl (S := Q) (E := e') (by omega) (by omega) (by omega)
        (fun u h => ev_var (vals_lookup h.1.vals rfl)) (fun u h => ev_var (vals_lookup h.1.vals rfl))
        fun m hm => by rw [hm]; exact hkM) ?_
      rw [blankL_cont hc] at hbl
      cases hy : (seg a Q e').all isWS with
      | true =>
        refine fragR_append (xs := [_]) (fragR_if o rfl (lowKK_ret rfl) (lowK_any _ (k := .skip) rfl)
          (Q := fun _ => False) (fun _ _ h => h) (fun _ _ _ h _ => h) (fun _ _ _ h _ => h) (b := true)
          (fun u h => by rw [ev_var (vals_lookup h.1.vals rfl)]; rfl) (fun _ => fragR_ret o rfl fun u h =>
            ⟨_, rfl, h.2, by rw [← hbl, hy]; rfl⟩) fun e => absurd e (by decide))
          (fragR_of (frag_unsat (lowK_any _ (k := .skip) rfl) fun _ h => h))
      | false =>
        refine fragR_append (xs := [_]) (fragR_if o rfl (lowKK_ret rfl) (lowK_any _ (k := .skip) rfl)
          (Q := RunF s1 (("y", bw false) :: ("f", BitVec.ofNat 64 e') :: ("q", BitVec.ofNat 64 Q) :: B) (· = M))
          (runF_clock _ _ _) (fun _ _ _ _ hy => by simp [declared] at hy)
          (fun _ _ _ _ hy => by simp [declared] at hy) (b := false)
          (fun u h => by rw [ev_var (vals_lookup h.1.vals rfl)]; rfl) (fun e => absurd e (by decide))
          fun _ => fragR_of (frag_nil o fun u h => h)) ?_
        refine fragR_of (frag_conseq (runF_set o rfl rfl (v := BitVec.ofNat 64 (e' + 2)) fun u h =>
          ev_add2 (vals_lookup h.1.vals rfl)) (fun u h => h) fun u h => ⟨e' + 2, L2,
            runF_mono h (fun q hq => ?_) fun _ e => e, hL2, hn, by rw [← hbl, hy]; rfl⟩)
        simp only [List.mem_cons] at hq
        rcases hq with rfl | hq
        · exact List.mem_cons_self
        · simp only [B, List.mem_cons, List.not_mem_nil, or_false] at hq
          simp only [B, without, List.mem_filter, List.mem_cons]
          rcases hq with rfl | rfl | rfl | rfl | rfl | rfl <;> simp

/-! ## A refusal's name -/

/-- Octets `bs` stored from offset `x` of the area at `A` on. -/
def putB (m : Word → Word) (be : Bool) (A : Word) (x : Nat) : Bytes → Word → Word
  | [] => m
  | b :: bs => putB (DN.Compiler.Bytes.putByte m be (at_ A x) b) be A (x + 1) bs

theorem putB_snoc (be : Bool) (A : Word) : ∀ (bs : Bytes) (m : Word → Word) (x : Nat) (b : BitVec 8),
    putB m be A x (bs ++ [b]) = DN.Compiler.Bytes.putByte (putB m be A x bs) be (at_ A (x + bs.length)) b
  | [], m, x, b => by simp [putB]
  | c :: bs, m, x, b => by
    simp only [List.cons_append, putB, List.length_cons]
    rw [putB_snoc be A bs _ (x + 1) b, show x + 1 + bs.length = x + (bs.length + 1) by omega]

/-- A word `putB` leaves: one holding none of the octets. -/
theorem putB_other (be : Bool) {A : Word} (hA8 : A.toNat % 8 = 0) : ∀ (bs : Bytes) (m : Word → Word) (x y : Nat),
    y < x / 8 * 8 → x + bs.length < 2 ^ 63 → putB m be A x bs (at_ A y) = m (at_ A y)
  | [], _, _, _, _, _ => rfl
  | b :: bs, m, x, y, hy, hx => by
    simp only [putB, List.length_cons] at hx ⊢
    rw [putB_other be hA8 bs _ (x + 1) y (by omega) (by omega)]
    simp only [DN.Compiler.Bytes.putByte, DN.News.ScanRun.align_at hA8]
    rw [if_neg (DN.News.ScanRun.at_ne (by omega) (by omega) (by omega))]

theorem xName_ne0 : (ArticleProg.xName == 0) = false := by rw [xName_eq]; rfl

theorem xName_lt : ArticleProg.xName + ArticleProg.nameCap ≤ ArticleProg.xFirst := by
  rw [xName_eq, xFirst_eq]; decide

theorem xName_ge : aSets + 8 ≤ ArticleProg.xName := by
  have := sets_le_X; rw [X_val] at this; rw [xName_eq]; omega

theorem xName_mod : ArticleProg.xName % 8 = 0 := by rw [xName_eq]

theorem xFirst_small : ArticleProg.xFirst < 2 ^ 23 := by rw [xFirst_eq]; decide

theorem atOffName_lower : Lower.lowerExp (Syntax.atOff (Syntax.v "a") ArticleProg.xName) =
    some (.op .add (.var "a") (.const (BitVec.ofNat 64 ArticleProg.xName))) := by
  simp only [Syntax.atOff, xName_ne0, Bool.false_eq_true, if_false]; rfl

theorem setWidth_byte (b : BitVec 8) : (BitVec.ofNat 64 b.toNat).setWidth 8 = b := by
  apply BitVec.eq_of_toNat_eq; simp

theorem artNameAt_guarded : guardL ArticleProg.artNameAt.body =
    [areaAt ArticleProg.ofs, .call "fe" "artField" [Syntax.v "p"], brk,
     .dec "nl" (word (Syntax.v "a") ArticleProg.xNl), kept "nl" (ArticleProg.nameCap - 1), .dec "i" (Syntax.n 0),
     .while (Syntax.eLt (Syntax.v "i") (Syntax.v "nl"))
       [.dec "f" (Syntax.eAdd (Syntax.v "p") (Syntax.v "i")), kept "f" (artMax - 1), .dec "b" (ArticleProg.inByte "f"),
        .storeb (Syntax.eAdd (Syntax.atOff (Syntax.v "a") ArticleProg.xName) (Syntax.v "i")) (Syntax.v "b"),
        inc "i"],
     ArticleProg.setW ArticleProg.xNameLen (Syntax.v "nl"), .ret (Syntax.n 0)] := rfl

/-- The memory `artNameAt` leaves: `artField`'s words, the name's octets from `xName` and its length in
`xNameLen`. -/
def nameMem (A : Word) (be : Bool) (name : Bytes) (k e : Nat) (m0 : Word → Word) : Word → Word :=
  upd (putB (fieldMem A k e m0) be A ArticleProg.xName name) (at_ A ArticleProg.xNameLen) (BitVec.ofNat 64 name.length)

def NameRet (A : Word) (be : Bool) (name : Bytes) (k e : Nat) (m0 : Word → Word) : Ret :=
  fun v m => m = nameMem A be name k e m0 ∧ v = 0

theorem ev_addv {u : PancakeState σ} {x y : String} {X Y : Nat} (hx : u.locals x = some (BitVec.ofNat 64 X))
    (hy : u.locals y = some (BitVec.ofNat 64 Y)) :
    eval u (.op .add (.var x) (.var y)) = some (BitVec.ofNat 64 (X + Y)) := by
  simp only [eval, hx, hy]; rw [← BitVec.ofNat_add]

/-- **`artNameAt` writes the name of the field at `p`** as a refusal's. -/
theorem artNameAt_ok (o : Oracle σ) {A : Word} {s1 : PancakeState σ} (hA : Area ArticleProg.ofs A s1)
    (hD : ArtDom A s1.memaddrs) (hcode : ArtCode s1.code) {a : Bytes} (hlen : a.length ≤ artMax)
    (hin : InputAt s1.memory s1.memaddrs s1.be A a) (hb : s1.memory (at_ A aBroken) = 0) {SEP P e : Nat}
    {L : List (Nat × Nat)} (hf : FieldAt a SEP P e L) (hsep : s1.memory (at_ A ArticleProg.xSep) = BitVec.ofNat 64 SEP)
    (hK : nameLen a P e < ArticleProg.nameCap) (hp : s1.locals "p" = some (BitVec.ofNat 64 P)) :
    ∃ body, Lower.lower (gd ArticleProg.artNameAt) = some body ∧
      SafeR o (fun s => s = s1) body (NameRet A s1.be (seg a P (P + nameLen a P e)) (nameLen a P e) e s1.memory)
        fun _ => False := by
  have hM := artMax_eq
  have hS := lines_sep hf.lines
  have hm := lines_mem hf.lines (P, e) List.mem_cons_self
  simp only at hm
  obtain ⟨hk0, hke, -, -⟩ := fieldAt_colon hf
  have hlenK : (seg a P (P + nameLen a P e)).length = nameLen a P e := by
    rw [seg_length a (by omega) (by omega)]; omega
  generalize hKd : nameLen a P e = K at hk0 hke hK hlenK ⊢
  generalize hFE : nextOf a L SEP = FE
  let M := fieldMem A K e s1.memory
  have hkM := fieldMem_keep hA.hA hlen hin hb K e
  have hX := xName_ge; have hX2 := xName_lt; have hX3 := xName_mod; have hX4 := xFirst_small
  have hNC : ArticleProg.nameCap = 1024 := rfl
  -- the memory as the name is copied
  let Mi : Nat → Word → Word := fun i => putB M s1.be A ArticleProg.xName (seg a P (P + i))
  have hMi : ∀ i, i ≤ K → InputAt (Mi i) s1.memaddrs s1.be A a ∧ Mi i (at_ A aBroken) = 0 := fun i hi => by
    have hseg : (seg a P (P + i)).length = i := by rw [seg_length a (by omega) (by omega)]; omega
    have keep : ∀ y, y < aSets → Mi i (at_ A y) = M (at_ A y) := fun y hy =>
      putB_other s1.be hA.hA _ _ _ y (by omega) (by rw [hseg]; omega)
    exact ⟨input_keep hA.hA hlen hkM.1 keep, by rw [keep aBroken (by
      exact Nat.lt_trans (by rw [aInput_eq]; decide) DN.News.AbnfMain.input_sets)]; exact hkM.2⟩
  refine body_of ?_
  show FragR o _ (guardL ArticleProg.artNameAt.body) _ _
  rw [artNameAt_guarded]
  obtain ⟨EA, hEA⟩ := atOff_lower ArticleProg.ofs
  refine fragR_conseq (P0 := RunF s1 [("p", BitVec.ofNat 64 P)] (· = s1.memory)) ?_ (entry_one hp) fun _ h => h
  refine fragR_append (xs := [_]) (fragR_of (runF_dec o hEA rfl (v := A) fun u h => areaAt_eval hA h.1.base hEA)) ?_
  refine fragR_append (xs := [_, _]) (fragR_conseq (fieldCall_frag o hA hD hcode hlen (rt := "fe") (by decide)
    (l := [("a", A), ("p", BitVec.ofNat 64 P)]) rfl rfl (m0 := s1.memory) (e1 := Syntax.v "p") rfl hf
    (fun u h => ev_var (vals_lookup h.1.vals rfl)) hin hb hsep) (fun u h => h) fun u h => by
      rw [hKd, hFE] at h; exact h) ?_
  refine fragR_append (xs := [_]) (fragR_of (runF_dec o (wd_lower 17) rfl (v := BitVec.ofNat 64 K) fun u h => by
    rw [loadA_eval h.1.memaddrs (artDom_w hD (i := 17) (by decide)) (atA_eval (vals_lookup h.1.vals rfl)), h.2]
    exact congrArg some (fieldMem_nl A K e _))) ?_
  refine fragR_append (xs := [_]) (fragR_of (kept_frag o (by decide) (runF_clock _ _ _) fun u h =>
    ⟨K, vals_lookup h.1.vals rfl, by rw [hNC]; omega⟩)) ?_
  refine fragR_append (xs := [_]) (fragR_of (runF_dec o rfl rfl (v := BitVec.ofNat 64 0) fun _ _ => rfl)) ?_
  let B : List (String × Value) := ("nl", BitVec.ofNat 64 K) :: ("fe", BitVec.ofNat 64 FE) ::
    [("a", A), ("p", BitVec.ofNat 64 P)]
  let I : Assn σ := fun u => ∃ i, RunF s1 (("i", BitVec.ofNat 64 i) :: B) (· = Mi i) u ∧ i ≤ K
  have hIc : Safe.ClockFree I := fun u k ⟨i, h, hv⟩ => ⟨i, runF_clock _ _ _ u k h, hv⟩
  have hcond : ∀ u i, RunF s1 (("i", BitVec.ofNat 64 i) :: B) (· = Mi i) u → i ≤ K →
      eval u (.cmp .less (.var "i") (.var "nl")) = some (bw (decide (i < K))) := fun u i h hi =>
    FramerCode.eval_lt (by rw [hNC] at hK; omega) (by rw [hNC] at hK; omega) (ev_var (vals_lookup h.1.vals rfl))
      (ev_var (vals_lookup h.1.vals rfl))
  have hstl : Lower.lowerExp (Syntax.eAdd (Syntax.atOff (Syntax.v "a") ArticleProg.xName) (Syntax.v "i")) =
      some (.op .add (.op .add (.var "a") (.const (BitVec.ofNat 64 ArticleProg.xName))) (.var "i")) := by
    show Lower.lowerExp (.binop .add (Syntax.atOff (Syntax.v "a") ArticleProg.xName) (.var "i")) = _
    rw [Lower.lowerExp, atOffName_lower]; rfl
  have hlowB : LowKK [.dec "f" (Syntax.eAdd (Syntax.v "p") (Syntax.v "i")), kept "f" (artMax - 1),
      .dec "b" (ArticleProg.inByte "f"),
      .storeb (Syntax.eAdd (Syntax.atOff (Syntax.v "a") ArticleProg.xName) (Syntax.v "i")) (Syntax.v "b"),
      inc "i"] :=
    lowKK_append (xs := [_, _, _]) (lowK_any _ (k := .skip) rfl)
      (lowKK_append (xs := [_]) (lowKK_one rfl (a := .storeByte _ (.var "b")) (by
        simp only [Lower.lowerStmt1, hstl]; rfl)) (lowK_any _ (k := .skip) rfl))
  refine fragR_append (xs := [_]) (fragR_of (frag_conseq (frag_while o rfl hlowB hIc
    (fun u z v ⟨i, h, hv⟩ hz => by
      change z ∈ ["f", "b"] at hz
      refine ⟨i, runF_restore h ?_ v, hv⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
      rcases hz with rfl | rfl <;> rfl)
    (fun u ⟨i, h, hi⟩ => ⟨_, hcond u i h hi⟩) ?step)
    (fun u h => ⟨0, by simp only [Mi, Nat.add_zero, seg_self, putB]; exact h, Nat.zero_le _⟩)
    (P' := RunF s1 (("i", BitVec.ofNat 64 K) :: B) (· = Mi K)) fun u ⟨⟨i, h, hi⟩, h0⟩ => by
      rw [hcond u i h hi] at h0
      have : i = K := by have := of_decide_eq_false (bw_eq0 h0); omega
      subst this; exact h)) ?_
  case step =>
    refine frag_conseq (P0 := fun u => ∃ i : Nat, (fun i u => RunF s1 (("i", BitVec.ofNat 64 i) :: B) (· = Mi i) u ∧
      i < K) i u) (frag_exists hlowB fun i => ?_) (fun u ⟨⟨i, h, hi⟩, h0⟩ => ⟨i, h, by
        rw [hcond u i h hi] at h0; exact of_decide_eq_true (bw_ne0 h0)⟩) fun _ h => h
    refine frag_pure (i < K) (fun u h => h.2) hlowB fun hi => ?_
    refine frag_conseq (P0 := RunF s1 (("i", BitVec.ofNat 64 i) :: B) (· = Mi i)) ?_ (fun u h => h.1) fun _ h => h
    refine frag_append (xs := [_]) (runF_dec o rfl rfl (v := BitVec.ofNat 64 (P + i)) fun u h =>
      ev_addv (vals_lookup h.1.vals rfl) (vals_lookup h.1.vals rfl)) ?_
    refine frag_append (xs := [_]) (kept_frag o (by decide) (runF_clock _ _ _) fun u h =>
      ⟨P + i, vals_lookup h.1.vals rfl, by omega⟩) ?_
    refine frag_append (xs := [_]) (runF_dec o rfl rfl (v := BitVec.ofNat 64 (a[P + i]!).toNat) fun u h =>
      inByte_eval (input_run (hMi i (by omega)).1 h) (vals_lookup h.1.vals rfl) (by omega) (vals_lookup h.1.vals rfl)) ?_
    let LB : List (String × Value) := ("b", BitVec.ofNat 64 (a[P + i]!).toNat) :: ("f", BitVec.ofNat 64 (P + i)) ::
      ("i", BitVec.ofNat 64 i) :: B
    refine frag_append (xs := [_]) (storeb_frag o hstl rfl (runF_clock _ _ _) (P' := RunF s1 LB (· = Mi (i + 1)))
      fun u h => ⟨at_ A (ArticleProg.xName + i), _, by
        simp only [eval, vals_lookup h.1.vals (show LB.lookup "a" = some A from rfl),
          vals_lookup h.1.vals (show LB.lookup "i" = some (BitVec.ofNat 64 i) from rfl)]
        rw [← at_add]; rfl, ev_var (vals_lookup h.1.vals rfl), ?_, ?_⟩) ?_
    · rw [DN.News.ScanRun.align_at hA.hA, h.1.memaddrs]
      exact hD _ (by omega) (by omega) (by omega)
    · refine ⟨⟨h.1.vals, h.1.memaddrs, h.1.base, h.1.code, h.1.be⟩, ?_⟩
      show DN.Compiler.Bytes.putByte u.memory u.be (at_ A (ArticleProg.xName + i)) _ = Mi (i + 1)
      rw [h.2, h.1.be, setWidth_byte]
      have hseg : (seg a P (P + i)).length = i := by rw [seg_length a (by omega) (by omega)]; omega
      show _ = putB M s1.be A ArticleProg.xName (seg a P (P + i + 1))
      rw [seg_succ a (by omega) (by omega), getElem!_pos a (P + i) (by omega), putB_snoc, hseg]
    refine frag_conseq (runF_set o rfl rfl (v := BitVec.ofNat 64 (i + 1)) fun u h => ev_inc (vals_lookup h.1.vals rfl))
      (fun u h => h) fun u h => ⟨i + 1, runF_mono h (fun q hq => ?_) fun _ e => e, by omega⟩
    simp only [List.mem_cons] at hq
    rcases hq with rfl | hq
    · exact List.mem_cons_self
    · simp only [B, List.mem_cons, List.not_mem_nil, or_false] at hq
      simp only [LB, B, without, List.mem_filter, List.mem_cons]
      rcases hq with rfl | rfl | rfl | rfl <;> simp
  -- the length, the return
  refine fragR_append (xs := [_]) (fragR_of (runF_storeA o (atOffW_lower 11) rfl (y := ArticleProg.w 11)
    (artDom_w hD (by decide)) (fun u h => atA_eval (vals_lookup h.1.vals rfl)) (val := fun _ => BitVec.ofNat 64 K)
    (fun u h => ev_var (vals_lookup h.1.vals rfl))
    (G := (· = nameMem A s1.be (seg a P (P + K)) K e s1.memory)) fun m hm => by
      subst hm; simp only [nameMem, hlenK]; rfl)) ?_
  exact fragR_ret o rfl fun u h => ⟨_, rfl, h.2, rfl⟩

/-! ## A field's entry -/

/-- An entry's name as its table holds it: in lower case. -/
def lowCodes (s : String) : Bytes := (ArticleProg.codes (ArticleProg.lowerS s)).map (BitVec.ofNat 8)

/-- Whether a name is entry `s`, read without case. -/
def entryIs (s : String) (name : Bytes) : Bool := name.map ArticleSpec.lowerB == lowCodes s

/-- The entry of a name, read without case, or the count of entries. -/
def classOf (es : List String) (name : Bytes) : Nat := (es.findIdx? (entryIs · name)).getD es.length

/-- Where entry `k`'s name lies among the names' bytes. -/
def offOf (es : List String) (k : Nat) : Nat := ((es.take k).map String.length).sum

theorem lowCodes_length (s : String) : (lowCodes s).length = s.length := by
  simp [lowCodes, ArticleProg.codes, ArticleProg.lowerS]

/-- The entries' tables as `artTables` leaves them: each name's place and length, its bytes in lower case. -/
structure TablesAt (A : Word) (dm : Word → Bool) (be : Bool) (m : Word → Word) (es : List String) : Prop where
  off : ∀ k, k < es.length → m (at_ A (ArticleProg.xNameT es + 16 * k)) = BitVec.ofNat 64 (offOf es k)
  len : ∀ k (_hk : k < es.length), m (at_ A (ArticleProg.xNameT es + 16 * k + 8)) = BitVec.ofNat 64 es[k].length
  bytes : ∀ k (_hk : k < es.length) i (_hi : i < es[k].length),
    memLoadByte m dm be (at_ A (ArticleProg.xNameBytes es + offOf es k + i)) = some (lowCodes es[k])[i]!

/-- The tables' words addressable. -/
def TabDom (A : Word) (dm : Word → Bool) (es : List String) : Prop :=
  ∀ x, ArticleProg.xFirst ≤ x → x < ArticleProg.size es → x % 8 = 0 → dm (at_ A x) = true

theorem bw_ofNat (t : Bool) : bw t = BitVec.ofNat 64 (if t then 1 else 0) := by cases t <;> rfl

/-- A byte loaded from memory. -/
theorem loadByte_eval {u : PancakeState σ} {E : PancakeExp} {w : Word} {b : BitVec 8} (hE : eval u E = some w)
    (hm : memLoadByte u.memory u.memaddrs u.be w = some b) :
    eval u (.loadByte E) = some (BitVec.ofNat 64 b.toNat) := by
  rw [eval, hE]
  simp only [hm]
  congr 1
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]

/-- A byte in lower case, as a number. -/
def lowN (b : Nat) : Nat := if 65 ≤ b ∧ b ≤ 90 then b + 32 else b

theorem lowerB_nat (b : BitVec 8) : (ArticleSpec.lowerB b).toNat = lowN b.toNat := by
  unfold ArticleSpec.lowerB lowN
  split
  · rename_i h; rw [BitVec.toNat_add]; simp; omega
  · rfl

theorem lowerEx_eval {u : PancakeState σ} {E : PancakeExp} {B : Nat} (hB : B < 256)
    (hE : eval u E = some (BitVec.ofNat 64 B)) :
    eval u (.op .add E (.mul (.const (BitVec.ofNat 64 32)) (.op .and_
      (.cmp .notLess E (.const (BitVec.ofNat 64 65))) (.cmp .notLess (.const (BitVec.ofNat 64 90)) E)))) =
      some (BitVec.ofNat 64 (lowN B)) := by
  have h1 := FramerCode.eval_le (t := u) (a := .const (BitVec.ofNat 64 65)) (b := E) (x := 65) (y := B)
    (by decide) (by omega) rfl hE
  have h2 := FramerCode.eval_le (t := u) (a := E) (b := .const (BitVec.ofNat 64 90)) (x := B) (y := 90)
    (by omega) (by decide) hE rfl
  simp only [FramerCode.leE] at h1 h2
  rw [DN.News.AbnfLeaves.ev_add hE (DN.News.AbnfLeaves.ev_mul rfl (FramerCode.eval_and h1 h2))]
  unfold lowN
  by_cases h : 65 ≤ B ∧ B ≤ 90
  · rw [if_pos h, decide_eq_true h.1, decide_eq_true h.2]
    apply congrArg some; apply BitVec.eq_of_toNat_eq; simp [bw]
  · rw [if_neg h]
    have : (decide (65 ≤ B) && decide (B ≤ 90)) = false := by
      by_cases h3 : 65 ≤ B
      · simp only [decide_eq_true h3, Bool.true_and, decide_eq_false_iff_not]; omega
      · simp [h3]
    rw [this]
    apply congrArg some; apply BitVec.eq_of_toNat_eq; simp [bw]

theorem lowerE_eval {u : PancakeState σ} {x : String} {B : Nat} (hB : B < 256)
    (hx : u.locals x = some (BitVec.ofNat 64 B)) :
    eval u (.op .add (.var x) (.mul (.const (BitVec.ofNat 64 32)) (.op .and_
      (.cmp .notLess (.var x) (.const (BitVec.ofNat 64 65))) (.cmp .notLess (.const (BitVec.ofNat 64 90)) (.var x))))) =
      some (BitVec.ofNat 64 (lowN B)) := lowerEx_eval hB (ev_var hx)

theorem atOff_eq {p : Syntax.PExpr} {x : Nat} (hx : (x == 0) = false) : Syntax.atOff p x = Syntax.eAdd p (Syntax.n
    x) := by
  simp [Syntax.atOff, hx]

theorem xFirst_le_nameT (es : List String) : ArticleProg.xFirst + 16 ≤ ArticleProg.xNameT es := by
  simp only [ArticleProg.xNameT, ArticleProg.xRuleT, ArticleProg.xFlags]; omega

theorem xFirst_mod : ArticleProg.xFirst % 8 = 0 := by rw [xFirst_eq]

theorem offOf_le (es : List String) {k : Nat} (hk : k < es.length) :
    offOf es k + es[k].length ≤ ArticleProg.nameBytes es := by
  unfold offOf ArticleProg.nameBytes
  conv => rhs; rw [← List.take_append_drop k es]
  rw [List.map_append, List.sum_append, List.drop_eq_getElem_cons hk, List.map_cons, List.sum_cons]
  omega

theorem entryIs_iff {s : String} {a : Bytes} {P NL : Nat} (hs : s.length = NL) (hPN : P + NL ≤ a.length) :
    entryIs s (seg a P (P + NL)) = true ↔ ∀ j, j < NL → lowN (a[P + j]!).toNat = ((lowCodes s)[j]!).toNat := by
  have hl : (seg a P (P + NL)).length = NL := by rw [seg_length a (by omega) hPN]; omega
  have hc := lowCodes_length s
  unfold entryIs
  rw [beq_iff_eq]
  constructor
  · intro h j hj
    have := congrArg (·[j]?) h
    simp only [List.getElem?_map] at this
    rw [seg_get a (by omega), List.getElem?_eq_getElem (show P + j < a.length by omega),
      List.getElem?_eq_getElem (show j < (lowCodes s).length by omega)] at this
    simp only [Option.map_some, Option.some.injEq] at this
    rw [getElem!_pos a (P + j) (by omega), getElem!_pos (lowCodes s) j (by omega), ← this, lowerB_nat]
  · intro h
    apply List.ext_getElem (by simp [hl, hc, hs])
    intro j h1 h2
    simp only [List.getElem_map]
    have hj : j < NL := by simp [hl] at h1; exact h1
    have hg : (seg a P (P + NL))[j] = a[P + j]'(by omega) := by
      have := seg_get a (x := P) (e := P + NL) (i := j) (by omega)
      rw [List.getElem?_eq_getElem (show j < (seg a P (P + NL)).length by rw [hl]; exact hj),
        List.getElem?_eq_getElem (show P + j < a.length by omega)] at this
      exact Option.some.inj this
    rw [hg]
    apply BitVec.eq_of_toNat_eq
    have := h j hj
    rw [getElem!_pos a (P + j) (by omega), getElem!_pos (lowCodes s) j (by omega)] at this
    rw [lowerB_nat, this]

theorem classOf_eq {es : List String} {name : Bytes} {k : Nat} (hk : k < es.length)
    (hpre : ∀ j (hj : j < k), entryIs (es[j]'(Nat.lt_trans hj hk)) name = false) (hm : entryIs es[k] name = true) :
    classOf es name = k := by
  unfold classOf
  rw [List.findIdx?_eq_some_iff_getElem.2 ⟨hk, hm, fun j hj => by rw [hpre j hj]; decide⟩]; rfl

theorem classOf_none {es : List String} {name : Bytes}
    (h : ∀ j (hj : j < es.length), entryIs es[j] name = false) : classOf es name = es.length := by
  unfold classOf
  rw [List.findIdx?_eq_none_iff.2 fun x hx => by
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hx; exact h j hj]; rfl

theorem artClass_body (es : List String) : (ArticleProg.artClass es .none).body =
    [areaAt ArticleProg.ofs, kept "nl" artMax, .dec "k" (Syntax.n 0),
     .while (Syntax.eLt (Syntax.v "k") (Syntax.n (ArticleProg.E es)))
       [.dec "t" (Syntax.eAdd (Syntax.atOff (Syntax.v "a") (ArticleProg.xNameT es))
          (Syntax.eMul (Syntax.v "k") (Syntax.n 16))),
        .dec "off" (.loadw 1 (Syntax.v "t")), kept "off" (ArticleProg.nameBytes es),
        .dec "ln" (.loadw 1 (Syntax.atOff (Syntax.v "t") 8)), kept "ln" 64,
        ArticleProg.ifs (Syntax.eEq (Syntax.v "ln") (Syntax.v "nl"))
          [.dec "i" (Syntax.n 0), .dec "ok" (Syntax.n 1),
           .while (Syntax.eLt (Syntax.v "i") (Syntax.v "ln"))
             [.dec "pi" (Syntax.eAdd (Syntax.v "p") (Syntax.v "i")), kept "pi" (artMax - 1),
              .dec "b" (ArticleProg.inByte "pi"),
              .dec "oi" (Syntax.eAdd (Syntax.v "off") (Syntax.v "i")), kept "oi" (ArticleProg.nameBytes es),
              ArticleProg.ifs (ne (ArticleProg.lowerE (Syntax.v "b"))
                (byte (Syntax.eAdd (Syntax.atOff (Syntax.v "a") (ArticleProg.xNameBytes es)) (Syntax.v "oi"))))
                [.assign "ok" (Syntax.n 0)],
              inc "i"],
           ArticleProg.ifs (Syntax.v "ok") [.ret (Syntax.v "k")]],
        inc "k"],
     .ret (Syntax.n (ArticleProg.E es))] := rfl

theorem artClass_guard (es : List String) :
    guardL (ArticleProg.artClass es .none).body = (ArticleProg.artClass es .none).body := rfl

theorem at_mul (A : Word) (x k c : Nat) :
    A + BitVec.ofNat 64 x + BitVec.ofNat 64 k * BitVec.ofNat 64 c = at_ A (x + c * k) := by
  rw [← BitVec.ofNat_mul, BitVec.add_assoc, ← BitVec.ofNat_add, Nat.mul_comm]; rfl

/-- What `artClass` gives back: the entry of the name of `nl` octets at `p`, read without case. -/
def ClassRet (es : List String) (name : Bytes) (m0 : Word → Word) : Ret :=
  fun v m => m = m0 ∧ v = BitVec.ofNat 64 (classOf es name)

/-- **`artClass` finds the entry of a field's name**, compared without case (RFC 5322 §1.2.2). -/
theorem artClass_ok (o : Oracle σ) {es : List String} {A : Word} {s1 : PancakeState σ}
    (hA : Area ArticleProg.ofs A s1) (hT : TabDom A s1.memaddrs es) (htab : TablesAt A s1.memaddrs s1.be s1.memory es)
    (hes : ∀ s ∈ es, s.length ≤ 64) (hsz : ArticleProg.size es < 2 ^ 40) {a : Bytes}
    (hin : InputAt s1.memory s1.memaddrs s1.be A a) (hlen : a.length ≤ artMax) {P NL : Nat} (hPN : P + NL ≤ a.length)
    (hp : s1.locals "p" = some (BitVec.ofNat 64 P)) (hnl : s1.locals "nl" = some (BitVec.ofNat 64 NL)) :
    ∃ body, Lower.lower (gd (ArticleProg.artClass es .none)) = some body ∧
      SafeR o (fun s => s = s1) body (ClassRet es (seg a P (P + NL)) s1.memory) fun _ => False := by
  have hM := artMax_eq
  have hT0 : (ArticleProg.xNameT es == 0) = false := by
    have := xFirst_le_nameT es; rw [beq_eq_false_iff_ne]; omega
  have hB0 : (ArticleProg.xNameBytes es == 0) = false := by
    have := xFirst_le_nameT es; simp only [ArticleProg.xNameBytes, beq_eq_false_iff_ne]; omega
  have hNB : ArticleProg.nameBytes es < 2 ^ 40 := by
    have : ArticleProg.nameBytes es ≤ ArticleProg.size es := by
      show _ ≤ ArticleProg.xNameBytes es + (ArticleProg.nameBytes es + 7) / 8 * 8; omega
    omega
  have hEE : ArticleProg.E es = es.length := rfl
  refine body_of ?_
  show FragR o _ (guardL (ArticleProg.artClass es .none).body) _ _
  rw [artClass_guard, artClass_body, atOff_eq hT0, atOff_eq hB0]
  let L0 : List (String × Value) := [("a", A), ("p", BitVec.ofNat 64 P), ("nl", BitVec.ofNat 64 NL)]
  obtain ⟨EA, hEA⟩ := atOff_lower ArticleProg.ofs
  refine fragR_conseq (P0 := RunF s1 [("p", BitVec.ofNat 64 P), ("nl", BitVec.ofNat 64 NL)] (· = s1.memory))
    ?_ (entry_two hp hnl) fun _ h => h
  refine fragR_append (xs := [_]) (fragR_of (runF_dec o hEA rfl (v := A) fun u h => areaAt_eval hA h.1.base hEA)) ?_
  refine fragR_append (xs := [_]) (fragR_of (kept_frag o (by decide) (runF_clock _ _ _) fun u h =>
    ⟨NL, vals_lookup h.1.vals rfl, by omega⟩)) ?_
  refine fragR_append (xs := [_]) (fragR_of (runF_dec o rfl rfl (v := BitVec.ofNat 64 0) fun _ _ => rfl)) ?_
  have hnl' : (seg a P (P + NL)).length = NL := by rw [seg_length a (by omega) hPN]; omega
  have hTd : ∀ y, ArticleProg.xFirst ≤ y → y < ArticleProg.size es → y % 8 = 0 → s1.memaddrs (at_ A y) = true := hT
  have hNTmod : ArticleProg.xNameT es % 8 = 0 := by
    have := xFirst_mod; simp only [ArticleProg.xNameT, ArticleProg.xRuleT, ArticleProg.xFlags]; omega
  have hnT := xFirst_le_nameT es
  have hszE : ArticleProg.xNameT es + 16 * es.length ≤ ArticleProg.size es := by
    show _ ≤ ArticleProg.xNameT es + 16 * ArticleProg.E es + _; omega
  let I : Assn σ := fun u => ∃ k, RunF s1 (("k", BitVec.ofNat 64 k) :: L0) (· = s1.memory) u ∧ k ≤ es.length ∧
    ∀ j (hj : j < k) (hjE : j < es.length), entryIs es[j] (seg a P (P + NL)) = false
  have hIc : Safe.ClockFree I := fun u c ⟨k, h, hv⟩ => ⟨k, runF_clock _ _ _ u c h, hv⟩
  have hcondK : ∀ u k, RunF s1 (("k", BitVec.ofNat 64 k) :: L0) (· = s1.memory) u → k ≤ es.length →
      eval u (.cmp .less (.var "k") (.const (BitVec.ofNat 64 (ArticleProg.E es)))) =
        some (bw (decide (k < es.length))) := fun u k h hk =>
    FramerCode.eval_lt (by omega) (by omega) (ev_var (vals_lookup h.1.vals rfl)) rfl
  have hlowO := lowK_any (k := .skip) [.dec "t" (Syntax.eAdd (Syntax.eAdd (Syntax.v "a") (Syntax.n
      (ArticleProg.xNameT es)))
          (Syntax.eMul (Syntax.v "k") (Syntax.n 16))),
        .dec "off" (.loadw 1 (Syntax.v "t")), kept "off" (ArticleProg.nameBytes es),
        .dec "ln" (.loadw 1 (Syntax.atOff (Syntax.v "t") 8)), kept "ln" 64,
        ArticleProg.ifs (Syntax.eEq (Syntax.v "ln") (Syntax.v "nl"))
          [.dec "i" (Syntax.n 0), .dec "ok" (Syntax.n 1),
           .while (Syntax.eLt (Syntax.v "i") (Syntax.v "ln"))
             [.dec "pi" (Syntax.eAdd (Syntax.v "p") (Syntax.v "i")), kept "pi" (artMax - 1),
              .dec "b" (ArticleProg.inByte "pi"),
              .dec "oi" (Syntax.eAdd (Syntax.v "off") (Syntax.v "i")), kept "oi" (ArticleProg.nameBytes es),
              ArticleProg.ifs (ne (ArticleProg.lowerE (Syntax.v "b"))
                (byte (Syntax.eAdd (Syntax.eAdd (Syntax.v "a") (Syntax.n (ArticleProg.xNameBytes es))) (Syntax.v
                    "oi"))))
                [.assign "ok" (Syntax.n 0)],
              inc "i"],
           ArticleProg.ifs (Syntax.v "ok") [.ret (Syntax.v "k")]],
        inc "k"] rfl
  refine fragR_append (xs := [_]) (fragR_conseq (fragR_while o rfl hlowO hIc
    (fun u z v ⟨k, h, hv⟩ hz => by
      change z ∈ ["t", "off", "ln"] at hz
      refine ⟨k, runF_restore h ?_ v, hv⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
      rcases hz with rfl | rfl | rfl <;> rfl)
    (fun u ⟨k, h, hk, _⟩ => ⟨_, hcondK u k h hk⟩) ?step)
    (fun u h => ⟨0, h, Nat.zero_le _, fun j hj => absurd hj (Nat.not_lt_zero _)⟩) fun _ h => h) ?last
  case last =>
    refine fragR_ret o rfl fun u ⟨⟨k, h, hk, hv⟩, h0⟩ => ⟨_, rfl, h.2, ?_⟩
    rw [hcondK u k h hk] at h0
    have hkE : k = es.length := by have := of_decide_eq_false (bw_eq0 h0); omega
    subst hkE
    rw [classOf_none fun j hj => hv j hj hj]; rfl
  case step =>
    refine fragR_conseq (P0 := fun u => ∃ k : Nat, (fun k u => RunF s1 (("k", BitVec.ofNat 64 k) :: L0)
        (· = s1.memory) u ∧ k < es.length ∧
        ∀ j (hj : j < k) (hjE : j < es.length), entryIs es[j] (seg a P (P + NL)) = false) k u)
      (fragR_exists hlowO fun k => ?_) (fun u ⟨⟨k, h, hk, hv⟩, h0⟩ => ⟨k, h, by
        rw [hcondK u k h hk] at h0; exact of_decide_eq_true (bw_ne0 h0), hv⟩) fun _ h => h
    refine fragR_pure (k < es.length ∧ ∀ j (hj : j < k) (hjE : j < es.length),
      entryIs es[j] (seg a P (P + NL)) = false) (fun u h => h.2) hlowO fun ⟨hk, hpre⟩ => ?_
    refine fragR_conseq (P0 := RunF s1 (("k", BitVec.ofNat 64 k) :: L0) (· = s1.memory)) ?_ (fun u h => h.1)
      fun _ h => h
    have hsk := hes _ (List.getElem_mem hk)
    have hoff := offOf_le es hk
    refine fragR_append (xs := [_]) (fragR_of (runF_dec o rfl rfl
      (v := at_ A (ArticleProg.xNameT es + 16 * k)) fun u h => by
        simp only [eval, vals_lookup h.1.vals (show (("k", BitVec.ofNat 64 k) :: L0).lookup "a" = some A from rfl),
          vals_lookup h.1.vals (show (("k", BitVec.ofNat 64 k) :: L0).lookup "k" = some (BitVec.ofNat 64 k) from rfl)]
        rw [at_mul])) ?_
    refine fragR_append (xs := [_]) (fragR_of (runF_dec o rfl rfl (v := BitVec.ofNat 64 (offOf es k)) fun u h => by
      rw [loadA_eval h.1.memaddrs (hTd _ (by omega) (by omega) (by omega)) (ev_var (vals_lookup h.1.vals rfl)), h.2]
      exact congrArg some (htab.off k hk))) ?_
    refine fragR_append (xs := [_]) (fragR_of (kept_frag o (by omega) (runF_clock _ _ _) fun u h =>
      ⟨offOf es k, vals_lookup h.1.vals rfl, by omega⟩)) ?_
    refine fragR_append (xs := [_]) (fragR_of (runF_dec o rfl rfl (v := BitVec.ofNat 64 es[k].length) fun u h => by
      rw [loadA_eval h.1.memaddrs (y := ArticleProg.xNameT es + 16 * k + 8) (hTd _ (by omega) (by omega) (by omega))
        (by simp only [eval, vals_lookup h.1.vals (show (("off", BitVec.ofNat 64 (offOf es k)) ::
          ("t", at_ A (ArticleProg.xNameT es + 16 * k)) :: ("k", BitVec.ofNat 64 k) :: L0).lookup "t" =
            some (at_ A (ArticleProg.xNameT es + 16 * k)) from rfl)]; rw [at_add]), h.2]
      exact congrArg some (htab.len k hk))) ?_
    refine fragR_append (xs := [_]) (fragR_of (kept_frag o (by decide) (runF_clock _ _ _) fun u h =>
      ⟨es[k].length, vals_lookup h.1.vals rfl, hsk⟩)) ?_
    let LK : List (String × Value) := ("ln", BitVec.ofNat 64 es[k].length) :: ("off", BitVec.ofNat 64 (offOf es k)) ::
      ("t", at_ A (ArticleProg.xNameT es + 16 * k)) :: ("k", BitVec.ofNat 64 k) :: L0
    let J : Assn σ := fun u => RunF s1 LK (· = s1.memory) u ∧ entryIs es[k] (seg a P (P + NL)) = false
    have hJc : Safe.ClockFree J := fun u c h => ⟨runF_clock _ _ _ u c h.1, h.2⟩
    refine fragR_append (xs := [_]) (fragR_if o rfl (lowK_any _ (k := .skip) rfl) (lowK_any _ (k := .skip) rfl)
      (Q := J) hJc (fun u z v h hz => by
        change z ∈ ["i", "ok"] at hz
        refine ⟨runF_restore h.1 ?_ v, h.2⟩
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
        rcases hz with rfl | rfl <;> rfl) (fun _ _ _ _ hy => by simp [declared] at hy)
      (b := decide (es[k].length = NL)) (fun u h => FramerCode.eval_eq (by omega) (by omega)
        (ev_var (vals_lookup h.1.vals rfl)) (ev_var (vals_lookup h.1.vals rfl))) (fun hl => ?same)
      (fun hl => ?differ)) ?inck
    case differ =>
      refine fragR_of (frag_nil o fun u h => ⟨h, ?_⟩)
      have hne := of_decide_eq_false hl
      unfold entryIs
      cases hc : (List.map ArticleSpec.lowerB (seg a P (P + NL)) == lowCodes es[k])
      · rfl
      · exfalso
        have := congrArg List.length (beq_iff_eq.1 hc)
        rw [List.length_map, hnl', lowCodes_length] at this
        exact hne this.symm
    case inck =>
      refine fragR_of (frag_pure (entryIs es[k] (seg a P (P + NL)) = false) (fun u h => h.2)
        (lowK_any _ (k := .skip) rfl) fun hek => frag_conseq (runF_set o rfl rfl (v := BitVec.ofNat 64 (k + 1))
          fun u h => ev_inc (vals_lookup h.1.vals rfl)) (fun u h => h.1) fun u h =>
            ⟨k + 1, runF_mono h (fun q hq => ?_) fun _ e => e, by omega, fun j hj hjE => ?_⟩)
      · simp only [List.mem_cons] at hq
        rcases hq with rfl | hq
        · exact List.mem_cons_self
        · simp only [L0, List.mem_cons, List.not_mem_nil, or_false] at hq
          simp only [LK, L0, without, List.mem_filter, List.mem_cons]
          rcases hq with rfl | rfl | rfl <;> simp
      · by_cases hjk : j < k
        · exact hpre j hjk hjE
        · have : j = k := by omega
          subst this; exact hek
    case same =>
      have hlen' := of_decide_eq_true hl
      refine fragR_append (xs := [_]) (fragR_of (runF_dec o rfl rfl (v := BitVec.ofNat 64 0) fun _ _ => rfl)) ?_
      refine fragR_append (xs := [_]) (fragR_of (runF_dec o rfl rfl (v := BitVec.ofNat 64 1) fun _ _ => rfl)) ?_
      let LI : Nat → Nat → List (String × Value) := fun i ok =>
        ("ok", BitVec.ofNat 64 ok) :: ("i", BitVec.ofNat 64 i) :: LK
      let JJ : Assn σ := fun u => ∃ i ok, RunF s1 (LI i ok) (· = s1.memory) u ∧ i ≤ NL ∧ (ok = 0 ∨ ok = 1) ∧
        (ok = 1 ↔ ∀ j, j < i → lowN (a[P + j]!).toNat = ((lowCodes es[k])[j]!).toNat)
      have hJJ : Safe.ClockFree JJ := fun u c ⟨i, ok, h, hv⟩ => ⟨i, ok, runF_clock _ _ _ u c h, hv⟩
      have hcondI : ∀ u i ok, RunF s1 (LI i ok) (· = s1.memory) u → i ≤ NL →
          eval u (.cmp .less (.var "i") (.var "ln")) = some (bw (decide (i < NL))) := fun u i ok h hi =>
        FramerCode.eval_lt (by omega) (by omega) (ev_var (vals_lookup h.1.vals rfl))
          (by rw [ev_var (vals_lookup h.1.vals rfl), hlen'])
      have hlowI := lowK_any (k := .skip)
        [.dec "pi" (Syntax.eAdd (Syntax.v "p") (Syntax.v "i")), kept "pi" (artMax - 1),
         .dec "b" (ArticleProg.inByte "pi"),
         .dec "oi" (Syntax.eAdd (Syntax.v "off") (Syntax.v "i")), kept "oi" (ArticleProg.nameBytes es),
         ArticleProg.ifs (ne (ArticleProg.lowerE (Syntax.v "b"))
           (byte (Syntax.eAdd (Syntax.eAdd (Syntax.v "a") (Syntax.n (ArticleProg.xNameBytes es))) (Syntax.v "oi"))))
           [.assign "ok" (Syntax.n 0)],
         inc "i"] rfl
      let Post : Assn σ := fun u => ∃ ok, RunF s1 (LI NL ok) (· = s1.memory) u ∧ (ok = 0 ∨ ok = 1) ∧
        (ok = 1 ↔ entryIs es[k] (seg a P (P + NL)) = true)
      refine fragR_append (xs := [_]) (fragR_of (frag_conseq (frag_while o rfl hlowI hJJ
        (fun u z v ⟨i, ok, h, hv⟩ hz => by
          change z ∈ ["pi", "b", "oi"] at hz
          refine ⟨i, ok, runF_restore h ?_ v, hv⟩
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
          rcases hz with rfl | rfl | rfl <;> rfl)
        (fun u ⟨i, ok, h, hi, _⟩ => ⟨_, hcondI u i ok h hi⟩) ?istep)
        (fun u h => ⟨0, 1, h, Nat.zero_le _, .inr rfl, by simp⟩) (P' := Post)
        fun u ⟨⟨i, ok, h, hi, hok, hiff⟩, h0⟩ => by
          rw [hcondI u i ok h hi] at h0
          have : i = NL := by have := of_decide_eq_false (bw_eq0 h0); omega
          subst this
          exact ⟨ok, h, hok, hiff.trans (entryIs_iff hlen' hPN).symm⟩)) ?ifok
      case ifok =>
        refine fragR_exists (lowK_any _ (k := .skip) rfl) fun ok => ?_
        refine fragR_pure ((ok = 0 ∨ ok = 1) ∧ (ok = 1 ↔ entryIs es[k] (seg a P (P + NL)) = true))
          (fun u h => h.2) (lowK_any _ (k := .skip) rfl) fun ⟨hok, hiff⟩ => ?_
        refine fragR_conseq (P0 := RunF s1 (LI NL ok) (· = s1.memory)) ?_ (fun u h => h.1) fun _ h => h
        refine fragR_if o rfl (lowKK_ret rfl) (lowK_any _ (k := .skip) rfl) hJc (fun _ _ _ _ hy => by
          simp [declared] at hy) (fun _ _ _ _ hy => by simp [declared] at hy) (b := decide (ok = 1))
          (fun u h => by rw [ev_var (vals_lookup h.1.vals rfl), DN.News.AbnfGen.bw_of hok]; rfl) (fun hb1 => ?_)
          (fun hb1 => ?_)
        · refine fragR_ret o rfl fun u h => ⟨_, ev_var (vals_lookup h.1.vals rfl), h.2, ?_⟩
          rw [classOf_eq hk (fun j hj => hpre j hj _) (hiff.1 (of_decide_eq_true hb1))]
        · refine fragR_of (frag_nil o fun u h => ⟨runF_mono h (fun q hq => ?_) fun _ e => e, ?_⟩)
          · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hq)
          · cases he : entryIs es[k] (seg a P (P + NL))
            · rfl
            · exact absurd (hiff.2 he) (of_decide_eq_false hb1)
      case istep =>
        refine frag_conseq (P0 := fun u => ∃ t : Nat × Nat, (fun t u => RunF s1 (LI t.1 t.2) (· = s1.memory) u ∧
          t.1 < NL ∧ (t.2 = 0 ∨ t.2 = 1) ∧
            (t.2 = 1 ↔ ∀ j, j < t.1 → lowN (a[P + j]!).toNat = ((lowCodes es[k])[j]!).toNat)) t u)
          (frag_exists hlowI fun t => ?_) (fun u ⟨⟨i, ok, h, hi, hok, hiff⟩, h0⟩ => ⟨(i, ok), h, by
            rw [hcondI u i ok h hi] at h0; exact of_decide_eq_true (bw_ne0 h0), hok, hiff⟩) fun _ h => h
        obtain ⟨i, ok⟩ := t
        refine frag_pure (i < NL ∧ (ok = 0 ∨ ok = 1) ∧
          (ok = 1 ↔ ∀ j, j < i → lowN (a[P + j]!).toNat = ((lowCodes es[k])[j]!).toNat)) (fun u h => h.2) hlowI
          fun ⟨hi, hok, hiff⟩ => ?_
        refine frag_conseq (P0 := RunF s1 (LI i ok) (· = s1.memory)) ?_ (fun u h => h.1) fun _ h => h
        have hci : i < es[k].length := by omega
        refine frag_append (xs := [_]) (runF_dec o rfl rfl (v := BitVec.ofNat 64 (P + i)) fun u h =>
          ev_addv (vals_lookup h.1.vals rfl) (vals_lookup h.1.vals rfl)) ?_
        refine frag_append (xs := [_]) (kept_frag o (by decide) (runF_clock _ _ _) fun u h =>
          ⟨P + i, vals_lookup h.1.vals rfl, by omega⟩) ?_
        refine frag_append (xs := [_]) (runF_dec o rfl rfl (v := BitVec.ofNat 64 (a[P + i]!).toNat) fun u h =>
          inByte_eval (input_run hin h) (vals_lookup h.1.vals rfl) (by omega) (vals_lookup h.1.vals rfl)) ?_
        refine frag_append (xs := [_]) (runF_dec o rfl rfl (v := BitVec.ofNat 64 (offOf es k + i)) fun u h =>
          ev_addv (vals_lookup h.1.vals rfl) (vals_lookup h.1.vals rfl)) ?_
        refine frag_append (xs := [_]) (kept_frag o (by omega) (runF_clock _ _ _) fun u h =>
          ⟨offOf es k + i, vals_lookup h.1.vals rfl, by omega⟩) ?_
        let LB : List (String × Value) := ("oi", BitVec.ofNat 64 (offOf es k + i)) ::
          ("b", BitVec.ofNat 64 (a[P + i]!).toNat) :: ("pi", BitVec.ofNat 64 (P + i)) :: LI i ok
        have hBi : (a[P + i]!).toNat < 256 := (a[P + i]!).isLt
        have hCi : ((lowCodes es[k])[i]!).toNat < 256 := ((lowCodes es[k])[i]!).isLt
        have hcmp : ∀ u, RunF s1 LB (· = s1.memory) u →
            eval u (.cmp .equal (.cmp .equal (.op .add (.var "b") (.mul (.const (BitVec.ofNat 64 32))
              (.op .and_ (.cmp .notLess (.var "b") (.const (BitVec.ofNat 64 65)))
                (.cmp .notLess (.const (BitVec.ofNat 64 90)) (.var "b")))))
              (.loadByte (.op .add (.op .add (.var "a") (.const (BitVec.ofNat 64 (ArticleProg.xNameBytes es))))
                (.var "oi")))) (.const (BitVec.ofNat 64 0))) =
              some (bw (!decide (lowN (a[P + i]!).toNat = ((lowCodes es[k])[i]!).toNat))) := fun u h => by
          have hX := lowerE_eval (u := u) (x := "b") hBi (vals_lookup h.1.vals rfl)
          have hY : eval u (.loadByte (.op .add (.op .add (.var "a")
              (.const (BitVec.ofNat 64 (ArticleProg.xNameBytes es)))) (.var "oi"))) =
              some (BitVec.ofNat 64 ((lowCodes es[k])[i]!).toNat) := by
            refine loadByte_eval (w := at_ A (ArticleProg.xNameBytes es + offOf es k + i)) ?_ ?_
            · simp only [eval, vals_lookup h.1.vals (show LB.lookup "a" = some A from rfl),
                vals_lookup h.1.vals (show LB.lookup "oi" = some (BitVec.ofNat 64 (offOf es k + i)) from rfl)]
              show some (at_ A (ArticleProg.xNameBytes es) + BitVec.ofNat 64 (offOf es k + i)) = _
              rw [at_add, Nat.add_assoc]
            · rw [h.2, h.1.memaddrs, h.1.be]; exact htab.bytes k hk i hci
          have h1 := FramerCode.eval_eq (by unfold lowN; split <;> omega) (by omega) hX hY
          rw [bw_ofNat] at h1
          have h2 := FramerCode.eval_eq (t := u) (b := .const (BitVec.ofNat 64 0)) (y := 0)
            (by split <;> omega) (by decide) h1 rfl
          rw [h2]
          cases decide (lowN (a[P + i]!).toNat = ((lowCodes es[k])[i]!).toNat) <;> rfl
        let Mid : Assn σ := fun u => ∃ ok', RunF s1 (LI i ok') (· = s1.memory) u ∧ (ok' = 0 ∨ ok' = 1) ∧
          (ok' = 1 ↔ ∀ j, j < i + 1 → lowN (a[P + j]!).toNat = ((lowCodes es[k])[j]!).toNat)
        have hMid : Safe.ClockFree Mid := fun u c ⟨ok', h, hv⟩ => ⟨ok', runF_clock _ _ _ u c h, hv⟩
        have hmemLI : ∀ (q : String × Value) (ok' : Nat), q ∈ LI i ok' →
            q ∈ ("ok", BitVec.ofNat 64 ok') :: without "ok" LB := fun q ok' hq => by
          simp only [LI, List.mem_cons] at hq
          rcases hq with rfl | rfl | hq
          · exact List.mem_cons_self
          · exact List.mem_cons_of_mem _ (by simp [without, LB, LI])
          · simp only [LK, L0, List.mem_cons, List.not_mem_nil, or_false] at hq
            simp only [LB, LI, LK, L0, without, List.mem_filter, List.mem_cons]
            rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
        refine frag_append (xs := [_]) (DN.News.ScanRun.frag_if o rfl (lowK_any _ (k := .skip) rfl)
          (lowK_any _ (k := .skip) rfl) rfl rfl hMid
          (b := !decide (lowN (a[P + i]!).toNat = ((lowCodes es[k])[i]!).toNat)) hcmp (fun hb => ?_)
          (fun hb => ?_)) ?_
        · refine frag_conseq (runF_set o rfl rfl (v := BitVec.ofNat 64 0) fun _ _ => rfl) (fun u h => h)
            fun u h => ⟨0, runF_mono h (fun q hq => hmemLI q 0 hq) fun _ e => e, .inl rfl, ?_⟩
          simp only [Bool.not_eq_true', decide_eq_false_iff_not] at hb
          exact ⟨fun e => absurd e (by decide), fun hall => absurd (hall i (by omega)) hb⟩
        · refine frag_nil o fun u h => ⟨ok, runF_mono h (fun q hq => ?_) fun _ e => e, hok, ?_⟩
          · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hq))
          · simp only [Bool.not_eq_false', decide_eq_true_eq] at hb
            rw [hiff]
            exact ⟨fun hall j hj => if hji : j < i then hall j hji else by rw [show j = i by omega]; exact hb,
              fun hall j hj => hall j (by omega)⟩
        refine frag_exists (lowK_any _ (k := .skip) rfl) fun ok' => ?_
        refine frag_pure ((ok' = 0 ∨ ok' = 1) ∧
          (ok' = 1 ↔ ∀ j, j < i + 1 → lowN (a[P + j]!).toNat = ((lowCodes es[k])[j]!).toNat)) (fun u h => h.2)
          (lowK_any _ (k := .skip) rfl) fun ⟨hok', hiff'⟩ => ?_
        refine frag_conseq (runF_set o rfl rfl (v := BitVec.ofNat 64 (i + 1)) fun u h =>
          ev_inc (vals_lookup h.1.vals rfl)) (fun u h => h.1) fun u h =>
            ⟨i + 1, ok', runF_mono h (fun q hq => ?_) fun _ e => e, by omega, hok', hiff'⟩
        simp only [LI, List.mem_cons] at hq
        rcases hq with rfl | rfl | hq
        · exact List.mem_cons_of_mem _ List.mem_cons_self
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (by simp only [without, List.mem_filter]; exact ⟨List.mem_cons_of_mem _
            (List.mem_cons_of_mem _ hq), by
              simp only [LK, L0, List.mem_cons, List.not_mem_nil, or_false] at hq
              rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl⟩)

/-! ## The section's shape -/

theorem artStruct_guarded (r : ArticleSpec.Rules) : guardL (ArticleProg.artStruct r).body =
    [areaAt ArticleProg.ofs, .dec "len" (word (Syntax.v "a") ArticleProg.xLen), kept "len" artMax,
     ArticleProg.ifs (Syntax.eEq (Syntax.v "len") (Syntax.n 0)) [.ret (Syntax.n 1)],
     .call "e0" "artEol" [Syntax.n 0, Syntax.v "len"], brk,
     ArticleProg.ifs (Syntax.eEq (Syntax.v "e0") (Syntax.n 0)) [.ret (Syntax.n 1)],
     .dec "s" (Syntax.n 0), .dec "sep" ArticleProg.neg1, .dec "long" (Syntax.n 0), .dec "mal" (Syntax.n 0),
     .dec "go" (Syntax.n 1),
     .while (Syntax.v "go")
       [.call "e" "artEol" [Syntax.v "s", Syntax.v "len"], brk,
        .ite (Syntax.eEq (Syntax.v "e") (Syntax.v "len")) [.assign "go" (Syntax.n 0)]
          [.ite (Syntax.eEq (Syntax.v "e") (Syntax.v "s")) [.assign "sep" (Syntax.v "s"), .assign "go" (Syntax.n 0)]
            [ArticleProg.ifs (Syntax.eLt (Syntax.n r.lineMax) (Syntax.eSub (Syntax.v "e") (Syntax.v "s")))
               [.assign "long" (Syntax.n 1)],
             kept "s" (artMax - 1), .dec "b" (ArticleProg.inByte "s"),
             .ite (ArticleProg.isWS (Syntax.v "b"))
               [ArticleProg.ifs (Syntax.eEq (Syntax.v "s") (Syntax.n 0)) [.assign "mal" (Syntax.n 1)]]
               [.dec "j" (Syntax.v "s"), .dec "g" (Syntax.n 1),
                .while (Syntax.v "g")
                  [.ite (Syntax.eLt (Syntax.v "j") (Syntax.v "e"))
                    [kept "j" (artMax - 1), .dec "c" (ArticleProg.inByte "j"),
                     .ite (Syntax.eEq (Syntax.v "c") (Syntax.n 58)) [.assign "g" (Syntax.n 0)]
                       [.ite (ArticleProg.ftext (Syntax.v "c")) [inc "j"]
                         [.assign "mal" (Syntax.n 1), .assign "g" (Syntax.n 0)]]]
                    [.assign "mal" (Syntax.n 1), .assign "g" (Syntax.n 0)]],
                ArticleProg.ifs (Syntax.eEq (Syntax.v "j") (Syntax.v "s")) [.assign "mal" (Syntax.n 1)]],
             .assign "s" (Syntax.eAdd (Syntax.v "e") (Syntax.n 2))]]],
     ArticleProg.ifs (Syntax.eLt (Syntax.v "sep") (Syntax.n 0)) [.ret (Syntax.n 2)],
     ArticleProg.ifs (Syntax.eLt (Syntax.n r.headerMax) (Syntax.v "sep")) [.ret (Syntax.n 3)],
     ArticleProg.ifs (Syntax.v "long") [.ret (Syntax.n 4)],
     ArticleProg.ifs (Syntax.v "mal") [.ret (Syntax.n 5)],
     ArticleProg.setW ArticleProg.xSep (Syntax.v "sep"), .ret (Syntax.n 0)] := rfl

/-- A flag as a number. -/
def bnat (b : Bool) : Nat := if b then 1 else 0

/-- The memory `artStruct` leaves: the empty line's place in `xSep` if the shape is right. -/
def structMem (r : ArticleSpec.Rules) (A : Word) (a : Bytes) (m0 : Word → Word) : Word → Word :=
  if shapeOf r a = 0 then upd m0 (at_ A ArticleProg.xSep) (BitVec.ofNat 64 ((spans a 0).2.getD 0)) else m0

/-- What `artStruct` gives back: the section's shape. -/
def StructRet (r : ArticleSpec.Rules) (A : Word) (a : Bytes) (m0 : Word → Word) : Ret :=
  fun v m => m = structMem r A a m0 ∧ v = BitVec.ofNat 64 (shapeOf r a)

theorem structMem_ne {r : ArticleSpec.Rules} {A : Word} {a : Bytes} {m0 : Word → Word} (h : shapeOf r a ≠ 0) :
    structMem r A a m0 = m0 := by unfold structMem; rw [if_neg h]

theorem neg_lt (u : PancakeState σ) {x : String} (hx : u.locals x = some (BitVec.ofNat 64 (2 ^ 64 - 1))) :
    eval u (.cmp .less (.var x) (.const (BitVec.ofNat 64 0))) = some (bw true) := by
  simp only [eval, hx]; rfl

/-- The section's lines checked so far: a line past the bound, a malformed line. -/
def longL (r : ArticleSpec.Rules) (L : List (Nat × Nat)) : Bool := L.any fun q => decide (r.lineMax < q.2 - q.1)

theorem shapeOf_none {r : ArticleSpec.Rules} {a : Bytes} (hne : (spans a 0).1 ≠ []) (hp : (spans a 0).2 = none) :
    shapeOf r a = 2 := by
  unfold shapeOf; rw [if_neg hne, hp]

theorem shapeOf_some {r : ArticleSpec.Rules} {a : Bytes} {p : Nat} (hne : (spans a 0).1 ≠ [])
    (hp : (spans a 0).2 = some p) : shapeOf r a = if r.headerMax < p then 3 else if longL r (spans a 0).1 then 4
      else if (spans a 0).1.any (malLine a) then 5 else 0 := by
  unfold shapeOf longL; rw [if_neg hne, hp]

/-- **A branch on a known flag**, arms that declare locals. -/
theorem frag_ifR (o : Oracle σ) {c : Syntax.PExpr} {C : PancakeExp} (hc : Lower.lowerExp c = some C)
    {t e : List Syntax.PStmt} (hlt : LowKK t) (hle : LowKK e) {P Q : Assn σ} (hQ : Safe.ClockFree Q)
    (htc : ∀ u y v, Q u → y ∈ declared t → Q (restore u y v)) (hec : ∀ u y v, Q u → y ∈ declared e → Q (restore u y v))
    {b : Bool} (hv : ∀ u, P u → eval u C = some (bw b)) (ht : b = true → Frag o t P Q) (he : b = false → Frag o e P Q) :
    Frag o [.ite c t e] P Q := by
  refine frag_ite o hc hQ (fun u hu => ⟨_, hv u hu⟩) ?_ htc ?_ hec
  · cases b with
    | true => exact frag_conseq (ht rfl) (fun u h => h.1) fun _ h => h
    | false => exact frag_unsat hlt fun u ⟨hu, hne⟩ => hne (by rw [hv u hu]; rfl)
  · cases b with
    | true => exact frag_unsat hle fun u ⟨hu, h0⟩ => absurd (Option.some.inj ((hv u hu).symm.trans h0)) (by decide)
    | false => exact frag_conseq (he rfl) (fun u h => h.1) fun _ h => h

theorem seg_cons (a : Bytes) {j e : Nat} (hj : j < e) (he : e ≤ a.length) :
    seg a j e = a[j]! :: seg a (j + 1) e := by
  unfold seg
  rw [List.drop_eq_getElem_cons (by omega), show e - j = (e - (j + 1)) + 1 by omega, List.take_succ_cons,
    getElem!_pos a j (by omega)]

theorem nameScan_le : ∀ (l : Bytes) (k : Nat), (nameScan l k).1 ≤ k + l.length
  | [], k => by simp [nameScan]
  | x :: rest, k => by
    simp only [nameScan, List.length_cons]
    split
    · omega
    · split
      · have := nameScan_le rest (k + 1); omega
      · omega

theorem ftext_bytes (b : BitVec 8) :
    (decide (33 ≤ b.toNat) && decide (b.toNat ≤ 57) || decide (59 ≤ b.toNat) && decide (b.toNat ≤ 126)) =
      ArticleSpec.isFtext b := rfl

/-- `artStruct`'s locals in its loop. -/
def stL (g M Lg SP S e0 N : Nat) (A : Word) : List (String × Value) :=
  [("go", BitVec.ofNat 64 g), ("mal", BitVec.ofNat 64 M), ("long", BitVec.ofNat 64 Lg), ("sep", BitVec.ofNat 64 SP),
   ("s", BitVec.ofNat 64 S), ("e0", BitVec.ofNat 64 e0), ("len", BitVec.ofNat 64 N), ("a", A)]

/-- A state's locals read off another list of them, a name at a time. -/
theorem runF_stL {s0 u : PancakeState σ} {l : List (String × Value)} {F : (Word → Word) → Prop}
    (h : RunF s0 l F u) {g M Lg SP S e0 N : Nat} {A : Word} (h1 : l.lookup "go" = some (BitVec.ofNat 64 g))
    (h2 : l.lookup "mal" = some (BitVec.ofNat 64 M)) (h3 : l.lookup "long" = some (BitVec.ofNat 64 Lg))
    (h4 : l.lookup "sep" = some (BitVec.ofNat 64 SP)) (h5 : l.lookup "s" = some (BitVec.ofNat 64 S))
    (h6 : l.lookup "e0" = some (BitVec.ofNat 64 e0)) (h7 : l.lookup "len" = some (BitVec.ofNat 64 N))
    (h8 : l.lookup "a" = some A) : RunF s0 (stL g M Lg SP S e0 N A) F u :=
  ⟨⟨fun q hq => by
    simp only [stL, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first | exact vals_lookup h.1.vals h1 | exact vals_lookup h.1.vals h2 | exact vals_lookup h.1.vals h3 |
      exact vals_lookup h.1.vals h4 | exact vals_lookup h.1.vals h5 | exact vals_lookup h.1.vals h6 |
      exact vals_lookup h.1.vals h7 | exact vals_lookup h.1.vals h8,
    h.1.memaddrs, h.1.base, h.1.code, h.1.be⟩, h.2⟩

/-- A local read off another list, put in front. -/
theorem runF_push {s0 u : PancakeState σ} {l l' : List (String × Value)} {F : (Word → Word) → Prop}
    (h : RunF s0 l F u) {x : String} {v : Value} (hx : l.lookup x = some v) (h' : RunF s0 l' F u) :
    RunF s0 ((x, v) :: l') F u :=
  ⟨⟨fun q hq => by
    rcases List.mem_cons.1 hq with rfl | hq
    · exact vals_lookup h.1.vals hx
    · exact h'.1.vals q hq, h'.1.memaddrs, h'.1.base, h'.1.code, h'.1.be⟩, h'.2⟩

theorem longL_append (r : ArticleSpec.Rules) (pre : List (Nat × Nat)) (q : Nat × Nat) :
    longL r (pre ++ [q]) = (longL r pre || decide (r.lineMax < q.2 - q.1)) := by
  simp [longL, List.any_append]

theorem malL_append (a : Bytes) (pre : List (Nat × Nat)) (q : Nat × Nat) :
    (pre ++ [q]).any (malLine a) = (pre.any (malLine a) || malLine a q) := by
  simp [List.any_append]

/-- **`artStruct` finds the section's shape** and the empty line's place (`shapeOf`). -/
theorem artStruct_ok (o : Oracle σ) {r : ArticleSpec.Rules} (hlm : r.lineMax < 2 ^ 62) (hhm : r.headerMax < 2 ^ 62)
    {A : Word} {s1 : PancakeState σ} (hA : Area ArticleProg.ofs A s1) (hD : ArtDom A s1.memaddrs)
    (hcode : ArtCode s1.code) {a : Bytes} (hlen : a.length ≤ artMax) (hin : InputAt s1.memory s1.memaddrs s1.be A a)
    (hb : s1.memory (at_ A aBroken) = 0) (hlw : s1.memory (at_ A ArticleProg.xLen) = BitVec.ofNat 64 a.length) :
    ∃ body, Lower.lower (gd (ArticleProg.artStruct r)) = some body ∧
      SafeR o (fun s => s = s1) body (StructRet r A a s1.memory) fun _ => False := by
  have hM := artMax_eq
  refine body_of ?_
  show FragR o _ (guardL (ArticleProg.artStruct r).body) _ _
  rw [artStruct_guarded]
  obtain ⟨EA, hEA⟩ := atOff_lower ArticleProg.ofs
  refine fragR_conseq (P0 := RunF s1 [] (· = s1.memory)) ?_ (entry_run (l := []) (fun q hq => nomatch hq) rfl)
    fun _ h => h
  refine fragR_append (xs := [_]) (fragR_of (runF_dec o hEA rfl (v := A) fun u h => areaAt_eval hA h.1.base hEA)) ?_
  refine fragR_append (xs := [_]) (fragR_of (runF_dec o (wd_lower 1) rfl (v := BitVec.ofNat 64 a.length) fun u h => by
    rw [loadA_eval h.1.memaddrs (artDom_w hD (i := 1) (by decide)) (atA_eval (vals_lookup h.1.vals rfl)), h.2]
    exact congrArg some hlw)) ?_
  refine fragR_append (xs := [_]) (fragR_of (kept_frag o (by decide) (runF_clock _ _ _) fun u h =>
    ⟨a.length, vals_lookup h.1.vals rfl, hlen⟩)) ?_
  let B1 : List (String × Value) := [("len", BitVec.ofNat 64 a.length), ("a", A)]
  -- no header: an empty section
  refine fragR_append (xs := [_]) (fragR_if o rfl (lowKK_ret rfl) (lowK_any _ (k := .skip) rfl)
    (Q := fun u => RunF s1 B1 (· = s1.memory) u ∧ a.length ≠ 0) (fun u c h => ⟨runF_clock _ _ _ u c h.1, h.2⟩)
    (fun _ _ _ _ hy => by simp [declared] at hy) (fun _ _ _ _ hy => by simp [declared] at hy)
    (b := decide (a.length = 0)) (fun u h => FramerCode.eval_eq (by omega) (by decide)
      (ev_var (vals_lookup h.1.vals rfl)) rfl) (fun h0 => fragR_ret o rfl fun u h => ⟨_, rfl, ?_, ?_⟩)
    (fun h0 => fragR_of (frag_nil o fun u h => ⟨h, of_decide_eq_false h0⟩))) ?_
  · have h1 : shapeOf r a = 1 := shapeOf_nil ((spans_nil a).2 (.inl (of_decide_eq_true h0)))
    rw [structMem_ne (by omega)]; exact h.2
  · have h1 : shapeOf r a = 1 := shapeOf_nil ((spans_nil a).2 (.inl (of_decide_eq_true h0)))
    rw [h1]
  -- the first line's end
  refine fragR_pure (a.length ≠ 0) (fun u h => h.2) (lowK_any _ (k := .skip) rfl) fun hn0 => ?_
  refine fragR_conseq (P0 := RunF s1 B1 (· = s1.memory)) ?_ (fun u h => h.1) fun _ h => h
  refine fragR_append (xs := [_, _]) (eolCall_frag o hA hcode (a := a) (rt := "e0") (by decide) rfl rfl
    (F := (· = s1.memory)) (e1 := Syntax.n 0) (e2 := Syntax.v "len") rfl rfl (Q := 0) (LIM := a.length) (by omega)
    (Nat.le_refl _) hlen (fun _ _ => rfl) (fun u h => ev_var (vals_lookup h.1.vals rfl))
    fun m hm => by rw [hm]; exact ⟨hin, hb⟩) ?_
  let B0 : List (String × Value) := ("e0", BitVec.ofNat 64 (eolOf a 0 a.length)) :: B1
  have he0 := eolOf_ge a (Nat.zero_le a.length)
  -- no header: the empty line first
  refine fragR_append (xs := [_]) (fragR_if o rfl (lowKK_ret rfl) (lowK_any _ (k := .skip) rfl)
    (Q := fun u => RunF s1 B0 (· = s1.memory) u ∧ eolOf a 0 a.length ≠ 0) (fun u c h => ⟨runF_clock _ _ _ u c h.1, h.2⟩)
    (fun _ _ _ _ hy => by simp [declared] at hy) (fun _ _ _ _ hy => by simp [declared] at hy)
    (b := decide (eolOf a 0 a.length = 0)) (fun u h => FramerCode.eval_eq (by omega) (by decide)
      (ev_var (vals_lookup h.1.vals rfl)) rfl) (fun h0 => fragR_ret o rfl fun u h => ⟨_, rfl, ?_, ?_⟩)
    (fun h0 => fragR_of (frag_nil o fun u h => ⟨h, of_decide_eq_false h0⟩))) ?_
  · have h1 : shapeOf r a = 1 := shapeOf_nil ((spans_nil a).2 (.inr (of_decide_eq_true h0)))
    rw [structMem_ne (by omega)]; exact h.2
  · have h1 : shapeOf r a = 1 := shapeOf_nil ((spans_nil a).2 (.inr (of_decide_eq_true h0)))
    rw [h1]
  refine fragR_pure (eolOf a 0 a.length ≠ 0) (fun u h => h.2) (lowK_any _ (k := .skip) rfl) fun he00 => ?_
  refine fragR_conseq (P0 := RunF s1 B0 (· = s1.memory)) ?_ (fun u h => h.1) fun _ h => h
  have hne : (spans a 0).1 ≠ [] := fun h => by
    rcases (spans_nil a).1 h with h | h
    · exact hn0 h
    · exact he00 h
  refine fragR_append (xs := [_]) (fragR_of (runF_dec o rfl rfl (v := BitVec.ofNat 64 0) fun _ _ => rfl)) ?_
  refine fragR_append (xs := [_]) (fragR_of (runF_dec o rfl rfl (v := BitVec.ofNat 64 (2 ^ 64 - 1))
    fun _ _ => rfl)) ?_
  refine fragR_append (xs := [_]) (fragR_of (runF_dec o rfl rfl (v := BitVec.ofNat 64 0) fun _ _ => rfl)) ?_
  refine fragR_append (xs := [_]) (fragR_of (runF_dec o rfl rfl (v := BitVec.ofNat 64 0) fun _ _ => rfl)) ?_
  refine fragR_append (xs := [_]) (fragR_of (runF_dec o rfl rfl (v := BitVec.ofNat 64 1) fun _ _ => rfl)) ?_
  let LS : Nat → Nat → Nat → Nat → Nat → List (String × Value) := fun g M Lg SP S =>
    stL g M Lg SP S (eolOf a 0 a.length) a.length A
  let Post : Nat → Nat → Nat → Prop := fun M Lg SP =>
    ((spans a 0).2 = none ∧ SP = 2 ^ 64 - 1) ∨ (∃ p, (spans a 0).2 = some p ∧ SP = p ∧ p < a.length ∧
      Lg = bnat (longL r (spans a 0).1) ∧ M = bnat ((spans a 0).1.any (malLine a)))
  let I : Assn σ := fun u => ∃ g M Lg SP S, RunF s1 (LS g M Lg SP S) (· = s1.memory) u ∧ S ≤ a.length ∧
    ((g = 1 ∧ SP = 2 ^ 64 - 1 ∧ ∃ pre, (spans a 0).1 = pre ++ (spans a S).1 ∧ (spans a 0).2 = (spans a S).2 ∧
      Lg = bnat (longL r pre) ∧ M = bnat (pre.any (malLine a))) ∨ (g = 0 ∧ Post M Lg SP))
  have hIc : Safe.ClockFree I := fun u c ⟨g, M, Lg, SP, S, h, hv⟩ => ⟨g, M, Lg, SP, S, runF_clock _ _ _ u c h, hv⟩
  have hlowL := lowK_any (k := .skip) [.call "e" "artEol" [Syntax.v "s", Syntax.v "len"], brk,
        .ite (Syntax.eEq (Syntax.v "e") (Syntax.v "len")) [.assign "go" (Syntax.n 0)]
          [.ite (Syntax.eEq (Syntax.v "e") (Syntax.v "s")) [.assign "sep" (Syntax.v "s"), .assign "go" (Syntax.n 0)]
            [ArticleProg.ifs (Syntax.eLt (Syntax.n r.lineMax) (Syntax.eSub (Syntax.v "e") (Syntax.v "s")))
               [.assign "long" (Syntax.n 1)],
             kept "s" (artMax - 1), .dec "b" (ArticleProg.inByte "s"),
             .ite (ArticleProg.isWS (Syntax.v "b"))
               [ArticleProg.ifs (Syntax.eEq (Syntax.v "s") (Syntax.n 0)) [.assign "mal" (Syntax.n 1)]]
               [.dec "j" (Syntax.v "s"), .dec "g" (Syntax.n 1),
                .while (Syntax.v "g")
                  [.ite (Syntax.eLt (Syntax.v "j") (Syntax.v "e"))
                    [kept "j" (artMax - 1), .dec "c" (ArticleProg.inByte "j"),
                     .ite (Syntax.eEq (Syntax.v "c") (Syntax.n 58)) [.assign "g" (Syntax.n 0)]
                       [.ite (ArticleProg.ftext (Syntax.v "c")) [inc "j"]
                         [.assign "mal" (Syntax.n 1), .assign "g" (Syntax.n 0)]]]
                    [.assign "mal" (Syntax.n 1), .assign "g" (Syntax.n 0)]],
                ArticleProg.ifs (Syntax.eEq (Syntax.v "j") (Syntax.v "s")) [.assign "mal" (Syntax.n 1)]],
             .assign "s" (Syntax.eAdd (Syntax.v "e") (Syntax.n 2))]]] rfl
  refine fragR_append (xs := [_]) (fragR_conseq (fragR_while o rfl hlowL hIc
    (fun u z v ⟨g, M, Lg, SP, S, h, hv⟩ hz => by
      change z ∈ ["e"] at hz
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hz; subst hz
      exact ⟨g, M, Lg, SP, S, runF_restore h rfl v, hv⟩)
    (fun u ⟨g, M, Lg, SP, S, h, _⟩ => ⟨_, ev_var (vals_lookup h.1.vals rfl)⟩) ?step)
    (fun u h => ⟨1, 0, 0, 2 ^ 64 - 1, 0, h, Nat.zero_le _, .inl ⟨rfl, rfl, [], rfl, rfl, rfl, rfl⟩⟩)
    (P' := fun u => ∃ M Lg SP S, RunF s1 (LS 0 M Lg SP S) (· = s1.memory) u ∧ Post M Lg SP)
    fun u ⟨⟨g, M, Lg, SP, S, h, _, hv⟩, h0⟩ => by
      rcases hv with ⟨rfl, -⟩ | ⟨rfl, hp⟩
      · rw [ev_var (vals_lookup h.1.vals rfl)] at h0; exact absurd h0 (by decide)
      · exact ⟨M, Lg, SP, S, h, hp⟩) ?chain
  case chain =>
    have hlowC := lowK_any (k := .skip)
      [ArticleProg.ifs (Syntax.eLt (Syntax.v "sep") (Syntax.n 0)) [.ret (Syntax.n 2)],
       ArticleProg.ifs (Syntax.eLt (Syntax.n r.headerMax) (Syntax.v "sep")) [.ret (Syntax.n 3)],
       ArticleProg.ifs (Syntax.v "long") [.ret (Syntax.n 4)],
       ArticleProg.ifs (Syntax.v "mal") [.ret (Syntax.n 5)],
       ArticleProg.setW ArticleProg.xSep (Syntax.v "sep"), .ret (Syntax.n 0)] rfl
    refine fragR_exists hlowC fun M => fragR_exists hlowC fun Lg => fragR_exists hlowC fun SP =>
      fragR_exists hlowC fun S => ?_
    refine fragR_pure (Post M Lg SP) (fun u h => h.2) hlowC fun hpost => ?_
    refine fragR_conseq (P0 := RunF s1 (LS 0 M Lg SP S) (· = s1.memory)) ?_ (fun u h => h.1) fun _ h => h
    rcases hpost with ⟨hnone, rfl⟩ | ⟨p, hsome, rfl, hpl, rfl, rfl⟩
    · -- no empty line
      refine fragR_append (xs := [_]) (fragR_if o rfl (lowKK_ret rfl) (lowK_any _ (k := .skip) rfl)
        (Q := fun _ => False) (fun _ _ h => h) (fun _ _ _ h _ => h) (fun _ _ _ h _ => h) (b := true)
        (fun u h => neg_lt u (vals_lookup h.1.vals rfl)) (fun _ => fragR_ret o rfl fun u h =>
          ⟨_, rfl, by rw [structMem_ne (by rw [shapeOf_none hne hnone]; decide)]; exact h.2,
            by rw [shapeOf_none hne hnone]⟩)
        fun e => absurd e (by decide)) (fragR_of (frag_unsat (lowK_any _ (k := .skip) rfl) fun _ h => h))
    · have hsh := shapeOf_some (r := r) hne hsome
      have hSP : Safe.ClockFree (RunF s1 (LS 0 (bnat ((spans a 0).1.any (malLine a))) (bnat (longL r (spans a 0).1))
          SP S)
          (· = s1.memory)) := runF_clock _ _ _
      refine fragR_append (xs := [_]) (fragR_if o rfl (lowKK_ret rfl) (lowK_any _ (k := .skip) rfl) hSP
        (fun _ _ _ _ hy => by simp [declared] at hy) (fun _ _ _ _ hy => by simp [declared] at hy) (b := false)
        (fun u h => FramerCode.eval_lt (y := 0) (by omega) (by decide) (ev_var (vals_lookup h.1.vals rfl)) rfl)
        (fun e => absurd e (by decide)) fun _ => fragR_of (frag_nil o fun u h => h)) ?_
      by_cases h3 : r.headerMax < SP
      · refine fragR_append (xs := [_]) (fragR_if o rfl (lowKK_ret rfl) (lowK_any _ (k := .skip) rfl)
          (Q := fun _ => False) (fun _ _ h => h) (fun _ _ _ h _ => h) (fun _ _ _ h _ => h) (b := true)
          (fun u h => by
            have := FramerCode.eval_lt (t := u) (a := .const (BitVec.ofNat 64 r.headerMax)) (b := .var "sep")
              (x := r.headerMax) (y := SP) (by omega) (by omega) rfl (ev_var (vals_lookup h.1.vals rfl))
            rw [decide_eq_true h3] at this; exact this) (fun _ => fragR_ret o rfl fun u h =>
              ⟨_, rfl, by rw [structMem_ne (by rw [hsh, if_pos h3]; decide)]; exact h.2,
                by rw [hsh, if_pos h3]⟩)
          fun e => absurd e (by decide)) (fragR_of (frag_unsat (lowK_any _ (k := .skip) rfl) fun _ h => h))
      refine fragR_append (xs := [_]) (fragR_if o rfl (lowKK_ret rfl) (lowK_any _ (k := .skip) rfl) hSP
        (fun _ _ _ _ hy => by simp [declared] at hy) (fun _ _ _ _ hy => by simp [declared] at hy) (b := false)
        (fun u h => by
          have := FramerCode.eval_lt (t := u) (a := .const (BitVec.ofNat 64 r.headerMax)) (b := .var "sep")
            (x := r.headerMax) (y := SP) (by omega) (by omega) rfl (ev_var (vals_lookup h.1.vals rfl))
          rw [decide_eq_false h3] at this; exact this) (fun e => absurd e (by decide))
        fun _ => fragR_of (frag_nil o fun u h => h)) ?_
      have hfl : ∀ (u : PancakeState σ) (x : String) (b : Bool), u.locals x = some (BitVec.ofNat 64 (bnat b)) →
          eval u (.var x) = some (if b then 1 else 0) := fun u x b hx => by rw [ev_var hx]; cases b <;> rfl
      by_cases h4 : longL r (spans a 0).1 = true
      · refine fragR_append (xs := [_]) (fragR_if o rfl (lowKK_ret rfl) (lowK_any _ (k := .skip) rfl)
          (Q := fun _ => False) (fun _ _ h => h) (fun _ _ _ h _ => h) (fun _ _ _ h _ => h) (b := true)
          (fun u h => h4 ▸ hfl u "long" _ (vals_lookup h.1.vals rfl))
          (fun _ => fragR_ret o rfl fun u h =>
            ⟨_, rfl, by rw [structMem_ne (by rw [hsh, if_neg h3, if_pos h4]; decide)]; exact h.2,
              by rw [hsh, if_neg h3, if_pos h4]⟩)
          fun e => absurd e (by decide)) (fragR_of (frag_unsat (lowK_any _ (k := .skip) rfl) fun _ h => h))
      have h4' : longL r (spans a 0).1 = false := by simpa using h4
      refine fragR_append (xs := [_]) (fragR_if o rfl (lowKK_ret rfl) (lowK_any _ (k := .skip) rfl) hSP
        (fun _ _ _ _ hy => by simp [declared] at hy) (fun _ _ _ _ hy => by simp [declared] at hy) (b := false)
        (fun u h => h4' ▸ hfl u "long" _ (vals_lookup h.1.vals rfl)) (fun e => absurd e (by decide))
        fun _ => fragR_of (frag_nil o fun u h => h)) ?_
      by_cases h5 : (spans a 0).1.any (malLine a) = true
      · refine fragR_append (xs := [_]) (fragR_if o rfl (lowKK_ret rfl) (lowK_any _ (k := .skip) rfl)
          (Q := fun _ => False) (fun _ _ h => h) (fun _ _ _ h _ => h) (fun _ _ _ h _ => h) (b := true)
          (fun u h => h5 ▸ hfl u "mal" _ (vals_lookup h.1.vals rfl))
          (fun _ => fragR_ret o rfl fun u h =>
            ⟨_, rfl, by rw [structMem_ne (by rw [hsh, if_neg h3, h4', if_pos h5]; decide)]; exact h.2,
              by rw [hsh, if_neg h3, h4', if_pos h5]; rfl⟩)
          fun e => absurd e (by decide)) (fragR_of (frag_unsat (lowK_any _ (k := .skip) rfl) fun _ h => h))
      have h5' : (spans a 0).1.any (malLine a) = false := by simpa using h5
      refine fragR_append (xs := [_]) (fragR_if o rfl (lowKK_ret rfl) (lowK_any _ (k := .skip) rfl) hSP
        (fun _ _ _ _ hy => by simp [declared] at hy) (fun _ _ _ _ hy => by simp [declared] at hy) (b := false)
        (fun u h => h5' ▸ hfl u "mal" _ (vals_lookup h.1.vals rfl)) (fun e => absurd e (by decide))
        fun _ => fragR_of (frag_nil o fun u h => h)) ?_
      have h0 : shapeOf r a = 0 := by rw [hsh, if_neg h3, h4', h5']; rfl
      refine fragR_append (xs := [_]) (fragR_of (runF_storeA o (atOffW_lower 16) rfl (y := ArticleProg.w 16)
        (artDom_w hD (by decide)) (fun u h => atA_eval (vals_lookup h.1.vals rfl)) (val := fun _ => BitVec.ofNat 64 SP)
        (fun u h => ev_var (vals_lookup h.1.vals rfl)) (G := (· = structMem r A a s1.memory)) fun m hm => by
          subst hm; unfold structMem; rw [if_pos h0, hsome]; rfl)) ?_
      exact fragR_ret o rfl fun u h => ⟨_, rfl, h.2, by rw [h0]⟩
  case step =>
    refine fragR_conseq (P0 := fun u => ∃ t : Nat × Nat × Nat × List (Nat × Nat), (fun t u =>
      RunF s1 (LS 1 t.1 t.2.1 (2 ^ 64 - 1) t.2.2.1) (· = s1.memory) u ∧ t.2.2.1 ≤ a.length ∧
        (spans a 0).1 = t.2.2.2 ++ (spans a t.2.2.1).1 ∧ (spans a 0).2 = (spans a t.2.2.1).2 ∧
        t.2.1 = bnat (longL r t.2.2.2) ∧ t.1 = bnat (t.2.2.2.any (malLine a))) t u)
      (fragR_exists hlowL fun t => ?body) (fun u ⟨⟨g, M, Lg, SP, S, h, hS, hv⟩, h0⟩ => ?pre) fun _ h => h
    case pre =>
      rcases hv with ⟨rfl, rfl, pre, h1, h2, h3, h4⟩ | ⟨rfl, -⟩
      · exact ⟨(M, Lg, S, pre), h, hS, h1, h2, h3, h4⟩
      · rw [ev_var (vals_lookup h.1.vals rfl)] at h0; exact absurd rfl h0
    case body =>
    obtain ⟨M, Lg, S, pre⟩ := t
    refine fragR_pure (S ≤ a.length ∧ (spans a 0).1 = pre ++ (spans a S).1 ∧ (spans a 0).2 = (spans a S).2 ∧
      Lg = bnat (longL r pre) ∧ M = bnat (pre.any (malLine a))) (fun u h => h.2) hlowL
      fun ⟨hS, hpre1, hpre2, hLg, hMm⟩ => ?_
    subst hLg hMm
    refine fragR_conseq (P0 := RunF s1 (LS 1 (bnat (pre.any (malLine a))) (bnat (longL r pre)) (2 ^ 64 - 1) S)
      (· = s1.memory)) ?_ (fun u h => h.1) fun _ h => h
    have hE := eolOf_ge a hS
    refine fragR_append (xs := [_, _]) (eolCall_frag o hA hcode (a := a) (rt := "e") (by decide) rfl rfl
      (F := (· = s1.memory)) (e1 := Syntax.v "s") (e2 := Syntax.v "len") rfl rfl (Q := S) (LIM := a.length)
      (by omega) (Nat.le_refl _) hlen (fun u h => ev_var (vals_lookup h.1.vals rfl))
      (fun u h => ev_var (vals_lookup h.1.vals rfl)) fun m hm => by rw [hm]; exact ⟨hin, hb⟩) ?_
    generalize hEd : eolOf a S a.length = E at hE
    refine fragR_of (DN.News.ScanRun.frag_if o rfl (lowK_any _ (k := .skip) rfl) (lowK_any _ (k := .skip) rfl)
      rfl rfl hIc (b := decide (E = a.length)) (fun u h => FramerCode.eval_eq (by omega) (by omega)
        (ev_var (vals_lookup h.1.vals rfl)) (ev_var (vals_lookup h.1.vals rfl))) (fun hb1 => ?endIn)
      (fun hb1 => ?lineIn))
    case endIn =>
      have hEN := of_decide_eq_true hb1
      refine frag_conseq (runF_set o rfl rfl (v := BitVec.ofNat 64 0) fun _ _ => rfl) (fun u h => h) fun u h =>
        ⟨0, _, _, 2 ^ 64 - 1, S, runF_stL h rfl rfl rfl rfl rfl rfl rfl rfl, hS,
          .inr ⟨rfl, .inl ⟨by rw [hpre2, spans_end a (by rw [hEd, hEN])], rfl⟩⟩⟩
    case lineIn =>
      have hEN : E < a.length := by have := of_decide_eq_false hb1; omega
      have hf := eolOf_found a (show eolOf a S a.length < a.length by rw [hEd]; exact hEN)
      rw [hEd] at hf
      let m0 := s1.memory
      let LB : Bool → Nat → List (String × Value) := fun Mb Lg' =>
        ("b", BitVec.ofNat 64 (a[S]!).toNat) :: ("e", BitVec.ofNat 64 E) ::
          LS 1 (bnat Mb) Lg' (2 ^ 64 - 1) S
      have hscan : ∀ (Mb : Bool) (Lg3 : Nat), E ≠ S → Frag o
          [.dec "j" (Syntax.v "s"), .dec "g" (Syntax.n 1),
           .while (Syntax.v "g")
             [.ite (Syntax.eLt (Syntax.v "j") (Syntax.v "e"))
               [kept "j" (artMax - 1), .dec "c" (ArticleProg.inByte "j"),
                .ite (Syntax.eEq (Syntax.v "c") (Syntax.n 58)) [.assign "g" (Syntax.n 0)]
                  [.ite (ArticleProg.ftext (Syntax.v "c")) [inc "j"]
                    [.assign "mal" (Syntax.n 1), .assign "g" (Syntax.n 0)]]]
               [.assign "mal" (Syntax.n 1), .assign "g" (Syntax.n 0)]],
           ArticleProg.ifs (Syntax.eEq (Syntax.v "j") (Syntax.v "s")) [.assign "mal" (Syntax.n 1)]]
          (RunF s1 (LB Mb Lg3) (· = m0)) (RunF s1 (LB (Mb || malName a (S, E)) Lg3) (· = m0)) := by
        intro Mb Lg3 hES
        let JL : Nat → Nat → Bool → List (String × Value) := fun g J M2 =>
          ("g", BitVec.ofNat 64 g) :: ("j", BitVec.ofNat 64 J) :: LB M2 Lg3
        let NS := nameScan (seg a S E) 0
        let Jv : Assn σ := fun u => ∃ g J M2, RunF s1 (JL g J M2) (· = m0) u ∧ S ≤ J ∧ J ≤ E ∧
          ((g = 1 ∧ M2 = Mb ∧ NS = nameScan (seg a J E) (J - S)) ∨ (g = 0 ∧ J = S + NS.1 ∧ M2 = (Mb || NS.2)))
        have hJv : Safe.ClockFree Jv := fun u c ⟨g, J, M2, h, hv⟩ => ⟨g, J, M2, runF_clock _ _ _ u c h, hv⟩
        have hNSle : NS.1 ≤ E - S := by
          have := nameScan_le (seg a S E) 0; rw [seg_length a (by omega) (by omega)] at this; simp only [NS]; omega
        have hmn : malName a (S, E) = (NS.2 || NS.1 == 0) := rfl
        refine frag_append (xs := [_]) (runF_dec o rfl rfl (v := BitVec.ofNat 64 S) fun u h =>
          ev_var (vals_lookup h.1.vals rfl)) ?_
        refine frag_append (xs := [_]) (runF_dec o rfl rfl (v := BitVec.ofNat 64 1) fun _ _ => rfl) ?_
        have hlowS := lowK_any (k := .skip) [.ite (Syntax.eLt (Syntax.v "j") (Syntax.v "e"))
               [kept "j" (artMax - 1), .dec "c" (ArticleProg.inByte "j"),
                .ite (Syntax.eEq (Syntax.v "c") (Syntax.n 58)) [.assign "g" (Syntax.n 0)]
                  [.ite (ArticleProg.ftext (Syntax.v "c")) [inc "j"]
                    [.assign "mal" (Syntax.n 1), .assign "g" (Syntax.n 0)]]]
               [.assign "mal" (Syntax.n 1), .assign "g" (Syntax.n 0)]] rfl
        refine frag_append (xs := [_]) (frag_conseq (frag_while o rfl hlowS hJv
          (fun u z v _ hz => by change z ∈ [] at hz; cases hz)
          (fun u ⟨g, J, M2, h, _⟩ => ⟨_, ev_var (vals_lookup h.1.vals rfl)⟩) ?sstep)
          (fun u h => ⟨1, S, Mb, h, Nat.le_refl _, by omega, .inl ⟨rfl, rfl, by simp [NS]⟩⟩)
          (P' := RunF s1 (JL 0 (S + NS.1) (Mb || NS.2)) (· = m0)) fun u ⟨⟨g, J, M2, h, _, _, hv⟩, h0⟩ => by
            rcases hv with ⟨rfl, -⟩ | ⟨rfl, rfl, rfl⟩
            · rw [ev_var (vals_lookup h.1.vals rfl)] at h0; exact absurd h0 (by decide)
            · exact h) ?fin
        case fin =>
          refine DN.News.ScanRun.frag_if o rfl (lowK_any _ (k := .skip) rfl) (lowK_any _ (k := .skip) rfl) rfl rfl
            (runF_clock _ _ _) (b := decide (S + NS.1 = S)) (fun u h => FramerCode.eval_eq (by omega) (by omega)
              (ev_var (vals_lookup h.1.vals rfl)) (ev_var (vals_lookup h.1.vals rfl))) (fun h0 => ?_) (fun h0 => ?_)
          · have hk : NS.1 = 0 := by have := of_decide_eq_true h0; omega
            have : (Mb || malName a (S, E)) = true := by rw [hmn, hk]; simp
            simp only [LB, this]
            exact frag_conseq (runF_set o rfl rfl (v := BitVec.ofNat 64 1) fun _ _ => rfl) (fun u h => h) fun u h =>
              runF_push h rfl (runF_push h rfl (runF_stL h rfl rfl rfl rfl rfl rfl rfl rfl))
          · have hk : NS.1 ≠ 0 := by have := of_decide_eq_false h0; omega
            have : (Mb || malName a (S, E)) = (Mb || NS.2) := by rw [hmn, beq_eq_false_iff_ne.2 hk, Bool.or_false]
            rw [this]
            exact frag_nil o fun u h => runF_mono h (fun q hq => List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hq))
              fun _ e => e
        case sstep =>
          refine frag_conseq (P0 := fun u => ∃ J : Nat, (fun J u => RunF s1 (JL 1 J Mb) (· = m0) u ∧ S ≤ J ∧ J ≤ E ∧
            NS = nameScan (seg a J E) (J - S)) J u) (frag_exists hlowS fun J => ?sbody)
            (fun u ⟨⟨g, J, M2, h, h1, h2, hv⟩, h0⟩ => ?spre) fun _ h => h
          case spre =>
            rcases hv with ⟨rfl, rfl, hv⟩ | ⟨rfl, -⟩
            · exact ⟨J, h, h1, h2, hv⟩
            · rw [ev_var (vals_lookup h.1.vals rfl)] at h0; exact absurd rfl h0
          case sbody =>
          refine frag_pure (S ≤ J ∧ J ≤ E ∧ NS = nameScan (seg a J E) (J - S)) (fun u h => h.2) hlowS
            fun ⟨h1, h2, hv⟩ => ?_
          refine frag_conseq (P0 := RunF s1 (JL 1 J Mb) (· = m0)) ?_ (fun u h => h.1) fun _ h => h
          refine frag_ifR o rfl (lowK_any _ (k := .skip) rfl) (lowK_any _ (k := .skip) rfl) hJv
            (fun u z v ⟨g, J', M2, h, hv⟩ hz => by
              change z ∈ ["c"] at hz
              simp only [List.mem_cons, List.not_mem_nil, or_false] at hz; subst hz
              exact ⟨g, J', M2, runF_restore h rfl v, hv⟩) (fun _ _ _ _ hy => by change _ ∈ [] at hy; cases hy)
            (b := decide (J < E)) (fun u h => FramerCode.eval_lt (by omega) (by omega)
              (ev_var (vals_lookup h.1.vals rfl)) (ev_var (vals_lookup h.1.vals
                  rfl))) (fun hb => ?sinl) (fun hb => ?soutl)
          case soutl =>
            have hJE : J = E := by have := of_decide_eq_false hb; omega
            have hns : NS = (J - S, true) := by rw [hv, hJE, seg_self]; rfl
            refine frag_append (xs := [_]) (runF_set o rfl rfl (v := BitVec.ofNat 64 1) fun _ _ => rfl) ?_
            exact frag_conseq (runF_set o rfl rfl (v := BitVec.ofNat 64 0) fun _ _ => rfl) (fun u h => h) fun u h =>
              ⟨0, J, true, runF_push h rfl (runF_push h rfl (runF_push h rfl (runF_push h rfl
                (runF_stL h rfl rfl rfl rfl rfl rfl rfl rfl)))), h1, h2,
                .inr ⟨rfl, by rw [hns]; simp only; omega, by rw [hns]; simp⟩⟩
          case sinl =>
            have hJE : J < E := of_decide_eq_true hb
            have hsc := seg_cons a hJE (by omega)
            refine frag_append (xs := [_]) (kept_frag o (by decide) (runF_clock _ _ _) fun u h =>
              ⟨J, vals_lookup h.1.vals rfl, by omega⟩) ?_
            refine frag_append (xs := [_]) (runF_dec o rfl rfl (v := BitVec.ofNat 64 (a[J]!).toNat) fun u h =>
              inByte_eval (input_run hin h) (vals_lookup h.1.vals rfl) (by omega) (vals_lookup h.1.vals rfl)) ?_
            have hJl : J < a.length := by omega
            refine DN.News.ScanRun.frag_if o rfl (lowK_any _ (k := .skip) rfl) (lowK_any _ (k := .skip) rfl) rfl rfl
              hJv (b := decide (a[J]? = some COLON)) (fun u h => by
                rw [← colon_byte hJl]
                exact FramerCode.eval_eq (byte_lt _) (by decide) (ev_var (vals_lookup h.1.vals rfl)) rfl)
              (fun hc => ?_) (fun hc => ?_)
            · have hcol : a[J]! = COLON := by
                have := of_decide_eq_true hc
                rw [List.getElem?_eq_getElem hJl, Option.some.injEq] at this
                rw [getElem!_pos a J hJl, this]
              have hns : NS = (J - S, false) := by rw [hv, hsc]; simp [nameScan, hcol]
              exact frag_conseq (runF_set o rfl rfl (v := BitVec.ofNat 64 0) fun _ _ => rfl) (fun u h => h) fun u h =>
                ⟨0, J, Mb, runF_push h rfl (runF_push h rfl (runF_push h rfl (runF_push h rfl
                  (runF_stL h rfl rfl rfl rfl rfl rfl rfl rfl)))), h1, h2,
                  .inr ⟨rfl, by rw [hns]; simp only; omega, by rw [hns]; simp⟩⟩
            · have hcol : a[J]! ≠ COLON := by
                have := of_decide_eq_false hc
                rw [List.getElem?_eq_getElem hJl, Option.some.injEq] at this
                rw [getElem!_pos a J hJl]; exact this
              refine DN.News.ScanRun.frag_if o rfl (lowK_any _ (k := .skip) rfl) (lowK_any _ (k := .skip) rfl) rfl
                rfl hJv (b := ArticleSpec.isFtext a[J]!) (fun u h => by
                  rw [← ftext_bytes, ← DN.News.AbnfComment.bw_or]
                  have hc := ev_var (t := u) (x := "c") (vals_lookup h.1.vals rfl)
                  have hB := byte_lt a[J]!
                  exact FramerCode.eval_or
                    (FramerCode.eval_and (FramerCode.eval_le (by decide) (by omega) rfl hc)
                      (FramerCode.eval_le (by omega) (by decide) hc rfl))
                    (FramerCode.eval_and (FramerCode.eval_le (by decide) (by omega) rfl hc)
                      (FramerCode.eval_le (by omega) (by decide) hc rfl))) (fun hf => ?_) (fun hf => ?_)
              · have hns : NS = nameScan (seg a (J + 1) E) (J + 1 - S) := by
                  rw [hv, hsc]; simp only [nameScan, if_neg hcol, hf, if_true]
                  rw [show J - S + 1 = J + 1 - S by omega]
                exact frag_conseq (runF_set o rfl rfl (v := BitVec.ofNat 64 (J + 1)) fun u h =>
                  ev_inc (vals_lookup h.1.vals rfl)) (fun u h => h) fun u h =>
                  ⟨1, J + 1, Mb, runF_push h rfl (runF_push h rfl (runF_push h rfl (runF_push h rfl
                    (runF_stL h rfl rfl rfl rfl rfl rfl rfl rfl)))), by omega, by omega, .inl ⟨rfl, rfl, hns⟩⟩
              · have hns : NS = (J - S, true) := by
                  rw [hv, hsc]; simp only [nameScan, if_neg hcol, hf, Bool.false_eq_true, if_false]
                refine frag_append (xs := [_]) (runF_set o rfl rfl (v := BitVec.ofNat 64 1) fun _ _ => rfl) ?_
                exact frag_conseq (runF_set o rfl rfl (v := BitVec.ofNat 64 0) fun _ _ => rfl) (fun u h => h)
                  fun u h => ⟨0, J, true, runF_push h rfl (runF_push h rfl (runF_push h rfl (runF_push h rfl
                    (runF_stL h rfl rfl rfl rfl rfl rfl rfl rfl)))), h1, h2,
                    .inr ⟨rfl, by rw [hns]; simp only; omega, by rw [hns]; simp⟩⟩
      refine frag_ifR o rfl (lowK_any _ (k := .skip) rfl) (lowK_any _ (k := .skip) rfl) hIc
        (fun _ _ _ _ hy => by simp [declared] at hy)
        (fun u z v ⟨g, M', Lg', SP', S', h, hv⟩ hz => by
          change z ∈ ["b"] at hz
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hz; subst hz
          exact ⟨g, M', Lg', SP', S', runF_restore h rfl v, hv⟩)
        (b := decide (E = S)) (fun u h => FramerCode.eval_eq (by omega) (by omega)
          (ev_var (vals_lookup h.1.vals rfl)) (ev_var (vals_lookup h.1.vals rfl))) (fun hb2 => ?sepIn)
        (fun hb2 => ?lineC)
      case sepIn =>
        have hES := of_decide_eq_true hb2
        have hsp := spans_sep a hS (by rw [hEd]; exact hEN) (by rw [hEd]; exact hES)
        have hp1 : (spans a 0).1 = pre := by rw [hpre1, hsp, List.append_nil]
        have hp2 : (spans a 0).2 = some S := by rw [hpre2, hsp]
        refine frag_append (xs := [_]) (runF_set o rfl rfl (v := BitVec.ofNat 64 S) fun u h =>
          ev_var (vals_lookup h.1.vals rfl)) ?_
        exact frag_conseq (runF_set o rfl rfl (v := BitVec.ofNat 64 0) fun _ _ => rfl) (fun u h => h) fun u h =>
          ⟨0, _, _, S, S, runF_stL h rfl rfl rfl rfl rfl rfl rfl rfl, hS, .inr ⟨rfl, .inr ⟨S, hp2, rfl, by omega,
            by rw [hp1], by rw [hp1]⟩⟩⟩
      case lineC =>
        have hES : E ≠ S := of_decide_eq_false hb2
        have hsl := spans_line a hS (by rw [hEd]; exact hEN) (by rw [hEd]; exact hES)
        rw [hEd] at hsl
        let LgN := bnat (longL r (pre ++ [(S, E)]))
        refine frag_append (xs := [_]) (DN.News.ScanRun.frag_if o rfl (lowK_any _ (k := .skip) rfl)
          (lowK_any _ (k := .skip) rfl) rfl rfl
          (Q := RunF s1 (("e", BitVec.ofNat 64 E) :: LS 1 (bnat (pre.any (malLine a))) LgN (2 ^ 64 - 1) S) (· = m0))
          (runF_clock _ _ _) (b := decide (r.lineMax < E - S)) (fun u h => FramerCode.eval_lt (by omega) (by omega)
            rfl (ev_sub (y := S) (x := E - S) (by rw [Nat.add_sub_cancel' hE.1]; exact ev_var (vals_lookup h.1.vals
                rfl))
              (ev_var (vals_lookup h.1.vals rfl)))) (fun hb3 => ?_) (fun hb3 => ?_)) ?_
        · have : LgN = 1 := by simp only [LgN, longL_append, hb3, Bool.or_true]; rfl
          rw [this]
          exact frag_conseq (runF_set o rfl rfl (v := BitVec.ofNat 64 1) fun _ _ => rfl) (fun u h => h) fun u h =>
            runF_push h rfl (runF_stL h rfl rfl rfl rfl rfl rfl rfl rfl)
        · have : LgN = bnat (longL r pre) := by simp only [LgN, longL_append, hb3, Bool.or_false]
          rw [this]; exact frag_nil o fun u h => h
        refine frag_append (xs := [_]) (kept_frag o (by decide) (runF_clock _ _ _) fun u h =>
          ⟨S, vals_lookup h.1.vals rfl, by omega⟩) ?_
        refine frag_append (xs := [_]) (runF_dec o rfl rfl (v := BitVec.ofNat 64 (a[S]!).toNat) fun u h =>
          inByte_eval (input_run hin h) (vals_lookup h.1.vals rfl) (by omega) (vals_lookup h.1.vals rfl)) ?_
        have hcont : cont a (S, E) = isWS a[S]! := cont_byte (by omega)
        let MN := (pre ++ [(S, E)]).any (malLine a)
        refine frag_append (xs := [_]) (frag_ifR o rfl (lowK_any _ (k := .skip) rfl) (lowK_any _ (k := .skip) rfl)
          (Q := RunF s1 (LB MN LgN) (· = m0)) (runF_clock _ _ _) (fun _ _ _ _ hy => by change _ ∈ [] at hy; cases hy)
          (fun u z v h hz => by
            change z ∈ ["j", "g"] at hz
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
            rcases hz with rfl | rfl <;> exact runF_restore h rfl v)
          (b := isWS a[S]!) (fun u h => by
            rw [← isWS_bytes, ← DN.News.AbnfComment.bw_or]
            exact FramerCode.eval_or (FramerCode.eval_eq (byte_lt _) (by decide) (ev_var (vals_lookup h.1.vals rfl))
                rfl)
              (FramerCode.eval_eq (byte_lt _) (by decide) (ev_var (vals_lookup h.1.vals rfl)) rfl))
          (fun hw => ?_) (fun hw => ?_)) ?_
        · -- a continuation: malformed if first
          have hml : malLine a (S, E) = decide (S = 0) := by
            simp only [malLine, hcont, hw, if_true]; cases h : decide (S = 0) <;> simp_all
          refine DN.News.ScanRun.frag_if o rfl (lowK_any _ (k := .skip) rfl) (lowK_any _ (k := .skip) rfl) rfl rfl
            (runF_clock _ _ _) (b := decide (S = 0)) (fun u h => FramerCode.eval_eq (by omega) (by decide)
              (ev_var (vals_lookup h.1.vals rfl)) rfl) (fun h0 => ?_) (fun h0 => ?_)
          · have : MN = true := by simp only [MN, malL_append, hml, h0, Bool.or_true]
            simp only [LB, this]
            exact frag_conseq (runF_set o rfl rfl (v := BitVec.ofNat 64 1) fun _ _ => rfl) (fun u h => h) fun u h =>
              runF_push h rfl (runF_push h rfl (runF_stL h rfl rfl rfl rfl rfl rfl rfl rfl))
          · have : MN = pre.any (malLine a) := by simp only [MN, malL_append, hml, h0, Bool.or_false]
            simp only [LB, this]
            exact frag_nil o fun u h => h
        · -- a field's first line: its name
          have hml : malLine a (S, E) = malName a (S, E) := by simp only [malLine, hcont, hw]; rfl
          refine frag_conseq (hscan (pre.any (malLine a)) LgN hES) (fun u h => h) fun u h => ?_
          have : MN = (pre.any (malLine a) || malName a (S, E)) := by simp only [MN, malL_append, hml]
          rw [this]; exact h
        refine frag_conseq (runF_set o rfl rfl (v := BitVec.ofNat 64 (E + 2)) fun u h =>
          ev_add2 (vals_lookup h.1.vals rfl)) (fun u h => h) fun u h =>
          ⟨1, bnat MN, LgN, 2 ^ 64 - 1, E + 2, runF_stL h rfl rfl rfl rfl rfl rfl rfl rfl, by omega,
            .inl ⟨rfl, rfl, pre ++ [(S, E)], by rw [hpre1, hsl, List.append_assoc]; rfl, by rw [hpre2, hsl], rfl, rfl⟩⟩

/-! ## The program's code -/

/-- The article's functions' names: past the grammar's, and none twice. -/
theorem names_nodup :
    ((ArticleProg.functions ArticleSpec.spec (ArticleProg.entries ArticleSpec.spec) .none).map (·.name)).Nodup := by
  unfold ArticleProg.functions
  rw [List.map_append, List.map_map]
  have ha : (List.map ((·.name) ∘ fun f : Syntax.PFun => { f with body := guardL f.body })
      [ArticleProg.artEol .none, ArticleProg.artStruct ArticleSpec.spec, ArticleProg.artField, ArticleProg.artAllWS,
       ArticleProg.artBlank, ArticleProg.artClass (ArticleProg.entries ArticleSpec.spec) .none, ArticleProg.artGrammar,
       ArticleProg.artMsgIds ArticleSpec.spec .none, ArticleProg.artReceived, ArticleProg.artTok, ArticleProg.artNum,
       ArticleProg.artDiv, ArticleProg.artCivil, ArticleProg.artCivilOf, ArticleProg.artDate .none,
       ArticleProg.artNum10, ArticleProg.artCopy (ArticleProg.entries ArticleSpec.spec) .none,
       ArticleProg.artToMsg (ArticleProg.entries ArticleSpec.spec), ArticleProg.artNameAt, ArticleProg.artElem,
       ArticleProg.artKnown, ArticleProg.artGroups, ArticleProg.artDistAll, ArticleProg.artPosted,
       ArticleProg.artFormat, ArticleProg.artAdded ArticleSpec.spec (ArticleProg.entries ArticleSpec.spec) .none,
       ArticleProg.artCheck ArticleSpec.spec (ArticleProg.entries ArticleSpec.spec), ArticleProg.artContext,
       ArticleProg.artTables ArticleSpec.spec (ArticleProg.entries ArticleSpec.spec)]) =
      ["artEol", "artStruct", "artField", "artAllWS", "artBlank", "artClass", "artGrammar", "artMsgIds",
       "artReceived", "artTok", "artNum", "artDiv", "artCivil", "artCivilOf", "artDate", "artNum10", "artCopy",
       "artToMsg", "artNameAt", "artElem", "artKnown", "artGroups", "artDistAll", "artPosted", "artFormat",
       "artAdded", "artCheck", "artContext", "artTables"] := rfl
  rw [ha]
  have hg : ∀ g ∈ (AbnfProg.functions .none ArticleProg.ofs).map (·.name), g.toList.head? ≠ some 'a' := by
    intro g hg
    unfold AbnfProg.functions at hg
    rw [List.map_append, List.map_map] at hg
    rcases List.mem_append.1 hg with hg | hg
    · simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    · obtain ⟨i, -, rfl⟩ := List.mem_map.1 hg
      show (AbnfProg.ruleFun .none ArticleProg.ofs i).name.toList.head? ≠ _
      rw [DN.News.AbnfRun.ruleFun_name]
      by_cases hi : i = AbnfProg.commentRule
      · rw [hi, DN.News.AbnfRun.funName_comment]; decide
      · obtain ⟨rest, e⟩ := DN.News.AbnfMain.tl_rule hi
        rw [e]; simp
  refine List.nodup_append.2 ⟨DN.News.AbnfMain.names_nodup _, by decide, fun g hgm b hb e => ?_⟩
  have := hg g hgm
  rw [e] at this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact this rfl

/-- The code a run of the article program holds: each function by its name, as it lowers. -/
noncomputable def artCode : String → Option (List String × PancakeProg) := fun name =>
  ((ArticleProg.functions ArticleSpec.spec (ArticleProg.entries ArticleSpec.spec) .none).find? (·.name == name)).bind
    fun f => (Lower.lower f).map ((f.params.map (·.2)), ·)

/-- **The program's code holds each of its functions.** -/
theorem artCode_ok : ArtCode artCode := fun f hf body hb => by
  simp only [artCode, DN.News.AbnfMain.find_name names_nodup hf, Option.bind_some, hb, Option.map_some]

/-! ## The premises can hold -/

theorem artDom_witness : ArtDom 0 (fun _ => true) := fun _ _ _ _ => rfl

theorem tabDom_witness : TabDom 0 (fun _ => true) ["a"] := fun _ _ _ _ => rfl

/-- A memory holding the tables of the one entry `a`. -/
def wTables : Word → Word := fun w =>
  if w = 0 + BitVec.ofNat 64 (ArticleProg.xNameT ["a"] + 8) then 1
  else if w = 0 + BitVec.ofNat 64 (ArticleProg.xNameBytes ["a"]) then 97 else 0

theorem tablesAt_witness : TablesAt 0 (fun _ => true) false wTables ["a"] := by
  refine ⟨fun k hk => ?_, fun k hk => ?_, fun k hk i hi => ?_⟩
  · obtain rfl : k = 0 := by simpa using hk
    decide +kernel +revert
  · obtain rfl : k = 0 := by simpa using hk
    decide +kernel +revert
  · obtain rfl : k = 0 := by simpa using hk
    revert i; decide +kernel +revert

end DN.News.ArticleRun
