-- SPDX-License-Identifier: AGPL-3.0-or-later
import DN.News.AbnfRun

/-!
# DN.News.AbnfMain

A round of `main` answers what the grammar says (`round_frag`, `ansOf_answer`). In range: 2 for a start past the longest
input, else whether a match from a start reaches the end. From the one start 0 that is `Abnf.matches?`'s answer
(`ansOf_matches`).
-/

namespace DN.News.AbnfMain

open DN.Compiler DN.Compiler.Wp DN.Compiler.WpRet DN.Compiler.Frag DN.News.AbnfProg DN.News.AbnfLayout
open DN.News.AbnfSets DN.News.FunRun DN.News.AbnfLeaves DN.News.AbnfGen DN.News.AbnfRun
open DN.News.ScanRun (at_ at_add at_ne at_inj at_zero Vals vals_lookup vals_cons vals_set Fresh without lookup_head
  lookup_without fresh_cons)
open DN.News.FramerCode (bw ev_var)
open DN.News.AbnfMatch (Matches)
open DN.News.AbnfComment (ev_inc)

variable {σ : Type}

/-! ## A case -/

/-- A case as the host leaves it: the rule asked, the starts, the input (`Base` gives its length). -/
structure CaseAt (m : Word → Word) (A : Word) (r : Nat) (starts : List Word) : Prop where
  rule : m (at_ A aRule) = BitVec.ofNat 64 r
  count : m (at_ A aStarts) = BitVec.ofNat 64 starts.length
  starts : ∀ k (hk : k < starts.length), m (at_ A (aStartList + 8 * k)) = starts[k]

/-- The answer to a case: 2 when a start lies past the longest input. Else 1 when a match of rule `r` from a start ends
at the input's end, 0 when none does. -/
def Answer (r : Nat) (starts : List Word) (bytes : List (BitVec 8)) (ans : Word) : Prop :=
  ((∃ x ∈ starts, inputMax < x.toNat) → ans = 2) ∧
    ((∀ x ∈ starts, x.toNat ≤ inputMax) →
      (ans = 1 ↔ ∃ x ∈ starts, Matches AbnfRules.grammar (inputOf bytes) (.ref r) x.toNat bytes.length) ∧
        (ans = 0 ∨ ans = 1))

theorem aStartList_eq : aStartList = 40 := rfl

theorem input_pow : aInput ≤ aPow := Nat.le_trans (Nat.le_add_right _ _) (Nat.le_trans input_le io_le)

theorem input_sets : aInput < aSets := Nat.lt_of_le_of_lt input_pow (Nat.lt_of_lt_of_le (by decide) pow_lt)

/-- The header's words lie below the slots. -/
theorem head_low {x : Nat} (hx : x < aInput) : x < aSets := Nat.lt_trans hx input_sets

theorem in_word_ge (x : Nat) : aInput ≤ (aInput + x) / 8 * 8 := by rw [aInput_eq]; omega

/-- **What the leaves read is kept** where only words below the input changed. -/
theorem reads_keep_low {s0 : PancakeState σ} {A : Word} {bytes : List (BitVec 8)} (hA8 : A.toNat % 8 = 0)
    (hlen : bytes.length ≤ inputMax) {m1 m : Word → Word} (h : Reads s0 A bytes m1)
    (keep : ∀ x, aInput ≤ x → x < aSets → m (at_ A x) = m1 (at_ A x)) : Reads s0 A bytes m := by
  have hip := input_pow
  have hpm := pow_mask
  have hmc := mask_class
  have hct := class_texts
  have htb' := texts_le_bytes
  refine ⟨fun x hx => ?_, fun j hj => ?_, fun b hb => ?_, fun k hk i hi => ?_, fun k hk => ?_⟩
  · have := h.input x hx
    unfold memLoadByte at this ⊢
    rw [ScanRun.align_at hA8] at this ⊢
    have hlt : (aInput + x) / 8 * 8 < aSets := by
      have hp := pow_lt; have hio := io_le; have hin := input_le; omega
    rw [keep ((aInput + x) / 8 * 8) (in_word_ge x) hlt]; exact this
  · rw [keep (aPow + 8 * j) (Nat.le_trans hip (Nat.le_add_right _ _)) (by have hp := pow_lt; omega)]
    exact h.pows j hj
  · rw [keep (aMask + 8 * b) (Nat.le_trans hip (Nat.le_trans hpm (Nat.le_add_right _ _)))
      (by have := aClass_le; have : aClass = aMask + 8 * 8 := rfl; omega)]; exact h.masks b hb
  · rw [keep (aClass + 32 * k + 8 * i) (Nat.le_trans hip (Nat.le_trans hpm (Nat.le_trans hmc
      (Nat.le_trans (Nat.le_add_right _ _) (Nat.le_add_right _ _))))) (by have := classes_end; omega)]
    exact h.classes k hk i hi
  · have hte := texts_end
    have htb := textBytes_le
    have hof := textOff_le hk
    have hT : aInput ≤ aTexts := Nat.le_trans hip (Nat.le_trans hpm (Nat.le_trans hmc hct))
    have hB : aInput ≤ aTextBytes := Nat.le_trans hT htb'
    obtain ⟨t0, t1, t2, t3⟩ := h.texts k hk
    refine ⟨by rw [keep _ (Nat.le_trans hT (Nat.le_add_right _ _)) (by omega)]; exact t0,
      by rw [keep _ (Nat.le_trans hT (Nat.le_trans (Nat.le_add_right _ _) (Nat.le_add_right _ _))) (by omega)]
         exact t1,
      by rw [keep _ (Nat.le_trans hT (Nat.le_trans (Nat.le_add_right _ _) (Nat.le_add_right _ _))) (by omega)]
         exact t2, fun i hi => ?_⟩
    have := t3 i hi
    unfold memLoadByte at this ⊢
    rw [ScanRun.align_at hA8] at this ⊢
    have h8 := aTextBytes_mod
    rw [keep ((aTextBytes + textOff k + i) / 8 * 8) (by omega) (by omega)]; exact this

/-- What a round keeps: what calls take, and the case. -/
def RoundMem (s0 : PancakeState σ) (A : Word) (bytes : List (BitVec 8)) (r : Nat) (starts : List Word)
    (m : Word → Word) : Prop :=
  Base s0 A bytes m ∧ CaseAt m A r starts

theorem start_low {k : Nat} {starts : List Word} (hk : k < starts.length) (hks : starts.length ≤ startsMax) :
    aStartList + 8 * k < aInput := by
  have : startsMax = 16 := rfl
  rw [aStartList_eq, aInput_eq]; omega

theorem caseAt_keep {m m' : Word → Word} {A : Word} {r : Nat} {starts : List Word} (hks : starts.length ≤ startsMax)
    (h : CaseAt m A r starts)
    (hk : ∀ x, x < aInput → x ≠ aBroken → x ≠ aAnswer → m' (at_ A x) = m (at_ A x)) :
    CaseAt m' A r starts :=
  ⟨by rw [hk aRule (by rw [aInput_eq]; decide) (by decide) (by decide)]; exact h.rule,
   by rw [hk aStarts (by rw [aInput_eq]; decide) (by decide) (by decide)]; exact h.count,
   fun k hk' => by
     have := start_low hk' hks
     rw [hk _ this (by rw [aStartList_eq]; simp only [aBroken]; omega)
       (by rw [aStartList_eq]; simp only [aAnswer]; omega)]
     exact h.starts k hk'⟩

/-- **A word below the input stored**, the flag's or the answer's: the round's memory kept. -/
theorem roundMem_upd {s0 : PancakeState σ} {A : Word} {bytes : List (BitVec 8)} {r : Nat} {starts : List Word}
    (hA8 : A.toNat % 8 = 0) (hlen : bytes.length ≤ inputMax) (hks : starts.length ≤ startsMax) {m : Word → Word}
    (h : RoundMem s0 A bytes r starts m) {x0 : Nat} (hx : x0 = aBroken ∨ x0 = aAnswer) (v : Word) :
    RoundMem s0 A bytes r starts (upd m (at_ A x0) v) := by
  have hx0 : x0 < aInput := by rcases hx with rfl | rfl <;> rw [aInput_eq] <;> decide
  have hsets := input_sets
  have hne : ∀ x, x < aSets → x ≠ x0 → upd m (at_ A x0) v (at_ A x) = m (at_ A x) := fun x h1 h2 =>
    upd_ne _ (at_ne (by have := aSets_le; omega) (by have := aSets_le; omega) h2)
  refine ⟨⟨fun k hk => ?_, ?_, reads_keep_low hA8 hlen h.1.2.2 fun x h1 h2 => hne x h2 (by omega)⟩,
    caseAt_keep hks h.2 fun x h1 h2 h3 => hne x (by omega) (by rcases hx with rfl | rfl <;> assumption)⟩
  · obtain ⟨S, hS⟩ := h.1.1 k hk
    exact ⟨S, setAt_frame hS fun i hi => upd_ne _ fun e => notInSlot hk (by omega) ⟨i, hi, e.symm⟩⟩
  · rw [hne aLen aLen_low (by rcases hx with rfl | rfl <;> decide)]; exact h.1.2.1

/-- **Slot `kd` and the slots from `free` on changed**: the round's memory kept, each slot still a set. -/
theorem roundMem_kept {s0 : PancakeState σ} {A : Word} {bytes : List (BitVec 8)} {r : Nat} {starts : List Word}
    (hA8 : A.toNat % 8 = 0) (hlen : bytes.length ≤ inputMax) (hks : starts.length ≤ startsMax) {kd free : Nat}
    (hkd : kd < slots) {m m' : Word → Word} (h : RoundMem s0 A bytes r starts m) (hK : Kept A kd free m m')
    (hall : AllSets A m') : RoundMem s0 A bytes r starts m' :=
  ⟨base_keep hA8 hlen hkd h.1 hK hall, caseAt_keep hks h.2 fun _ hx _ _ =>
    kept_low hkd hK (Nat.lt_trans hx input_sets)⟩

/-! ## The starts -/

theorem mem_setAdd {ofs : Nat} : setAdd .none ofs ∈ functions .none ofs := List.mem_append_left _ (.tail _ (.head _))

/-- **A call of `setAdd`.** -/
theorem add_frag (o : Oracle σ) {ofs : Nat} {A : Word} {s0 : PancakeState σ} (hA : Area ofs A s0)
    (hcode : ProgCode s0.code ofs) {rt : String} {l : List (String × Value)} {F : (Word → Word) → Prop}
    (hrt : Fresh rt l = true) {e1 e2 : Syntax.PExpr} {E1 E2 : PancakeExp} (he1 : Lower.lowerExp e1 = some E1)
    (he2 : Lower.lowerExp e2 = some E2) {k : Nat} (hk : k < slots) (hv1 : ∀ u, RunF s0 l F u → eval u E1 = some
        (BitVec.ofNat 64 k))
    {Y : Word} (hv2 : ∀ u, RunF s0 l F u → eval u E2 = some Y) {S : Nat → Bool}
    (hS : ∀ m, F m → SetAt m A k S ∧ Pows m A) :
    Frag o [.call rt "setAdd" [e1, e2]] (RunF s0 l F)
      (fun u => ∃ v, RunF s0 ((rt, v) :: l) (fun m' => ∃ m, F m ∧ AddRet A k S Y m v m') u) :=
  progCall_frag o hA (f := setAdd .none ofs) (args := [E1, E2]) (vs := [BitVec.ofNat 64 k, Y])
    (by show ["d", "y"].Nodup; decide) (lowerArgs_two he1 he2) (progCode_of hcode mem_setAdd) rfl
    (fun u h => by simp only [evalArgs, hv1 u h, hv2 u h]) (R := AddRet A k S Y)
    (fun s1 hA1 _ _ _ hloc hF => setAdd_ok o hA1 hk ((hloc "d").trans rfl) ((hloc "y").trans rfl) (hS _ hF).1
      (hS _ hF).2) hrt fun m m' v hF hr => ⟨m, hF, hr⟩

/-- The positions of the first `k` starts, those up to the longest input. -/
def startSet (starts : List Word) (k : Nat) : Nat → Bool :=
  fun x => (starts.take k).any fun w => w.toNat == x && decide (x ≤ inputMax)

/-- Whether one of the first `k` starts lies past the longest input. -/
def brokenAt (starts : List Word) (k : Nat) : Bool := (starts.take k).any fun w => decide (inputMax < w.toNat)

theorem take_succ_any {starts : List Word} {k : Nat} (hk : k < starts.length) (p : Word → Bool) :
    (starts.take (k + 1)).any p = ((starts.take k).any p || p starts[k]) := by
  rw [List.take_add_one, List.getElem?_eq_getElem hk]
  simp only [Option.toList_some, List.any_append, List.any_cons, List.any_nil, Bool.or_false]

/-- The starts added, the first `k`: slot 0 their positions, the flag whether one lies past the longest input. -/
def StartsAt (s0 : PancakeState σ) (A : Word) (bytes : List (BitVec 8)) (r : Nat) (starts : List Word) (k : Nat)
    (m : Word → Word) : Prop :=
  RoundMem s0 A bytes r starts m ∧ SetAt m A 0 (startSet starts k) ∧ m (at_ A aBroken) = bw (brokenAt starts k)

theorem startsMax_eq : startsMax = 16 := rfl

theorem load_at {ofs : Nat} {A : Word} {s0 u : PancakeState σ} (hA : Area ofs A s0) (hm : u.memaddrs = s0.memaddrs)
    (ha : u.locals "a" = some A) {y : Nat} (hy : y < aInput) (hy8 : y % 8 = 0) :
    eval u (.loadWord (.op .add (.var "a") (.const (BitVec.ofNat 64 y)))) = some (u.memory (at_ A y)) :=
  load_eval hA hm (Nat.lt_of_lt_of_le (Nat.lt_trans hy input_sets) (Nat.le_add_right _ _)) hy8
    (by simp only [eval, ha]; rfl)

/-- **A start added**: slot 0 its position if within the longest input, the flag set if not. -/
theorem add_step {s0 : PancakeState σ} {A : Word} {bytes : List (BitVec 8)} {r : Nat} {starts : List Word}
    (hA8 : A.toNat % 8 = 0) (hlen : bytes.length ≤ inputMax) (hks : starts.length ≤ startsMax) {k : Nat}
    (hk : k < starts.length) {m m' : Word → Word} (h : StartsAt s0 A bytes r starts k m) {v : Value}
    (hr : AddRet A 0 (startSet starts k) starts[k] m v m') : StartsAt s0 A bytes r starts (k + 1) m' := by
  have h0 : 0 < slots := by have := slots_two; omega
  have hsb : ∀ x, startSet starts (k + 1) x = (startSet starts k x || (starts[k].toNat == x && decide (x ≤
      inputMax))) :=
    fun x => take_succ_any hk _
  have hbb : brokenAt starts (k + 1) = (brokenAt starts k || decide (inputMax < starts[k].toNat)) := take_succ_any hk _
  rcases hr with ⟨hY, -, hS', hfr⟩ | ⟨hY, -, rfl⟩
  · refine ⟨roundMem_kept hA8 hlen hks h0 h.1 (kept_frame (free := 0) (.inl rfl) hfr) (allSets_frame h.1.1.1 h0 hS'
      hfr),
      ?_, ?_⟩
    · have e : (fun x => startSet starts k x || x == starts[k].toNat) = startSet starts (k + 1) := funext fun x => by
        rw [hsb]
        by_cases hx : x = starts[k].toNat
        · subst hx; simp [hY]
        · rw [beq_false_of_ne hx, beq_false_of_ne (Ne.symm hx)]; simp
      rw [← e]; exact hS'
    · rw [hfr _ (notInSlot h0 (head_low (by rw [aInput_eq]; decide))), h.2.2, hbb]
      simp [Nat.not_lt.2 hY]
  · refine ⟨roundMem_upd hA8 hlen hks h.1 (.inl rfl) 1, ?_, ?_⟩
    · have e : startSet starts k = startSet starts (k + 1) := funext fun x => by
        rw [hsb]
        by_cases hx : x = starts[k].toNat
        · subst hx; simp [Nat.not_le.2 hY]
        · rw [beq_false_of_ne (Ne.symm hx)]; simp
      rw [← e]
      exact setAt_frame h.2.1 fun i hi => upd_ne _ fun e' =>
        notInSlot h0 (head_low (by rw [aInput_eq]; decide)) ⟨i, hi, e'.symm⟩
    · rw [upd_eq, hbb]; simp [hY]; rfl

/-- **The starts added to slot 0**, emptied first, and the flag set where one lies past the longest input. -/
theorem starts_frag (o : Oracle σ) {ofs : Nat} {A : Word} {s0 : PancakeState σ} (hA : Area ofs A s0)
    (hcode : ProgCode s0.code ofs) {bytes : List (BitVec 8)} (hlen : bytes.length ≤ inputMax) {r : Nat}
    {starts : List Word} (hks : starts.length ≤ startsMax) {l : List (String × Value)} (hla : ("a", A) ∈ l)
    (hz : Fresh "z" l = true) (hk : Fresh "k" l = true) (hkl : Fresh "ks" l = true) (hu : Fresh "u" l = true)
    {F : (Word → Word) → Prop} (hF : ∀ m, F m → RoundMem s0 A bytes r starts m ∧ m (at_ A aBroken) = 0) :
    Frag o [.call "z" "setClear" [Syntax.n 0], .dec "k" (Syntax.n 0), .dec "ks" (word (Syntax.v "a") aStarts),
      startsLoop] (RunF s0 l F) (fun w => ∃ vz, RunF s0 (("ks", BitVec.ofNat 64 starts.length) ::
        ("k", BitVec.ofNat 64 starts.length) :: ("z", vz) :: l) (StartsAt s0 A bytes r starts starts.length) w) := by
  have h0 : 0 < slots := by have := slots_two; omega
  have hlowL : LowKK [startsLoop] := lowKK_while rfl (lowKK_append (xs := [_])
    (lowKK_call (a := [.const _, .loadWord _]) rfl) (lowK_any _ (k := .skip) rfl))
  have hlowR : LowKK [.dec "k" (Syntax.n 0), .dec "ks" (word (Syntax.v "a") aStarts), startsLoop] :=
    lowKK_append (xs := [_]) (lowKK_dec rfl) (lowKK_append (xs := [_]) (lowKK_dec rfl) hlowL)
  refine frag_append (xs := [_]) (clear_frag o hA hcode (rt := "z") hz (lower_n 0) h0 (fun _ _ => rfl)
    fun m hm => (hF m hm).1.1.1) (frag_exists hlowR fun vz => ?_)
  have hk1 : Fresh "k" (("z", vz) :: l) = true := fresh_cons (by decide) hk
  have hks1 : Fresh "ks" (("k", BitVec.ofNat 64 0) :: ("z", vz) :: l) = true :=
    fresh_cons (by decide) (fresh_cons (by decide) hkl)
  refine frag_append (xs := [_]) (runF_dec o rfl hk1 (v := BitVec.ofNat 64 0) fun _ _ => rfl)
    (frag_append (xs := [_]) (runF_dec o rfl hks1 (v := BitVec.ofNat 64 starts.length) fun w h => ?_) ?_)
  · obtain ⟨m, hm, -, -, hfr⟩ := h.2
    rw [load_at hA h.1.memaddrs (h.1.vals _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hla)))
      (by rw [aInput_eq]; decide) (by decide)]
    rw [hfr _ (notInSlot h0 (head_low (by rw [aInput_eq]; decide)))]
    exact congrArg some (hF m hm).1.2.count
  let LL : Nat → List (String × Value) := fun k =>
    ("ks", BitVec.ofNat 64 starts.length) :: ("k", BitVec.ofNat 64 k) :: ("z", vz) :: l
  let I : Assn σ := fun w => ∃ k, k ≤ starts.length ∧ RunF s0 (LL k) (StartsAt s0 A bytes r starts k) w
  have hI : Safe.ClockFree I := fun w c ⟨k, hk, h⟩ => ⟨k, hk, runF_clock _ _ _ w c h⟩
  have hlen16 : starts.length ≤ 16 := hks
  have hU : ∀ k, Fresh "u" (LL k) = true := fun k =>
    fresh_cons (by decide) (fresh_cons (by decide) (fresh_cons (by decide) hu))
  have hev : ∀ k w (G : (Word → Word) → Prop), k ≤ starts.length → RunF s0 (LL k) G w →
      eval w (.op .and_ (.cmp .less (.var "k") (.var "ks")) (.cmp .less (.var "k")
        (.const (BitVec.ofNat 64 startsMax)))) = some (bw (decide (k < starts.length) && decide (k < startsMax))) :=
    fun k w G hk h => FramerCode.eval_and (FramerCode.eval_lt (by omega) (by omega)
      (vals_mem h (by simp [LL])) (vals_mem h (by simp [LL]))) (FramerCode.eval_lt
          (by omega) (by rw [startsMax_eq]; omega)
        (vals_mem h (by simp [LL])) rfl)
  have hlowB : LowKK [.call "u" "setAdd" [Syntax.n 0, .loadw 1 (Syntax.eAdd (Syntax.atOff (Syntax.v "a") aStartList)
      (Syntax.eMul (Syntax.v "k") (Syntax.n 8)))], inc "k"] :=
    lowKK_append (xs := [_]) (lowKK_call (a := [.const _, .loadWord _]) rfl) (lowK_any _ (k := .skip) rfl)
  refine frag_conseq (frag_while o (C := .op .and_ (.cmp .less (.var "k") (.var "ks")) (.cmp .less (.var "k")
      (.const (BitVec.ofNat 64 startsMax)))) rfl hlowB hI (fun w y v ⟨k, hk, h⟩ hy => ?_)
    (fun w ⟨k, hk, h⟩ => ⟨_, hev k w _ hk h⟩) ?_) (fun w h => ?_) fun w ⟨⟨k, hk, h⟩, h0⟩ => ?_
  · simp only [inc, declared, List.mem_cons, List.not_mem_nil, or_false] at hy
    subst hy; exact ⟨k, hk, runF_restore h (hU k) v⟩
  · -- a start added
    refine frag_conseq (P0 := fun w =>
      ∃ k, (k ≤ starts.length ∧ RunF s0 (LL k) (StartsAt s0 A bytes r starts k) w) ∧
      eval w (.op .and_ (.cmp .less (.var "k") (.var "ks")) (.cmp .less (.var "k")
        (.const (BitVec.ofNat 64 startsMax)))) ≠ some 0) (frag_exists hlowB fun k => ?_)
      (fun w ⟨⟨k, hk, h⟩, hne⟩ => ⟨k, ⟨hk, h⟩, hne⟩) fun _ h => h
    refine frag_pure (k < starts.length) (fun w ⟨⟨hk, h⟩, hne⟩ => by
        rw [hev k w _ hk h] at hne
        have := FramerCode.bw_ne0 hne
        simp only [Bool.and_eq_true, decide_eq_true_eq] at this; exact this.1) hlowB fun hkl => ?_
    refine frag_conseq (P0 := RunF s0 (LL k) (StartsAt s0 A bytes r starts k)) ?_ (fun w h => h.1.2) fun _ h => h
    have h0 : 0 < slots := by have := slots_two; omega
    have hy : aStartList + 8 * k < aInput := start_low hkl hks
    refine frag_append (xs := [_]) (add_frag o hA hcode (rt := "u") (hU k) (lower_n 0) rfl h0 (fun _ _ => rfl)
      (Y := starts[k]) (fun w h => ?_) (S := startSet starts k) fun m hm => ⟨hm.2.1, hm.1.1.2.2.pows⟩)
      (frag_exists (lowK_any _ (k := .skip) rfl) fun vu => ?_)
    · have ha : w.locals "a" = some A :=
        h.1.vals _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hla)))
      have hkv : w.locals "k" = some (BitVec.ofNat 64 k) := h.1.vals ("k", BitVec.ofNat 64 k) (by simp [LL])
      rw [load_eval hA h.1.memaddrs (y := aStartList + 8 * k) (Nat.lt_of_lt_of_le (head_low hy) (Nat.le_add_right _ _))
        (by rw [aStartList_eq]; omega) (by
          simp only [eval, ha, hkv]
          rw [← BitVec.ofNat_mul]
          show some (at_ A aStartList + BitVec.ofNat 64 (k * 8)) = _
          rw [at_add]
          exact congrArg (fun y => some (at_ A y)) (by omega))]
      exact congrArg some (h.2.1.2.starts k hkl)
    · have hk2 : Fresh "k" [("u", vu), ("ks", BitVec.ofNat 64 starts.length)] = true :=
        fresh_cons (by decide) (fresh_cons (by decide) rfl)
      refine frag_conseq (runF_swap o (pre := [_, _]) hk2 (fresh_cons (by decide) hk) rfl (v := BitVec.ofNat 64 (k + 1))
        fun w h => ev_inc (vals_mem h (by simp))) (fun _ h => h) fun w h => ⟨k + 1, hkl, runF_mono h
          (fun q hq => List.mem_cons_of_mem _ hq) fun m' ⟨m, hm, hr⟩ =>
            add_step hA.hA hlen hks hkl hm hr⟩
  · -- the loop's start
    refine ⟨0, Nat.zero_le _, runF_mono h (fun _ hq => hq) fun m' ⟨m, hm, _, hS0, hfr⟩ => ?_⟩
    have h0 : 0 < slots := by have := slots_two; omega
    refine ⟨roundMem_kept hA.hA hlen hks h0 (hF m hm).1 (kept_frame (free := 0) (.inl rfl) hfr)
      (allSets_frame (hF m hm).1.1.1 h0 hS0 hfr), ?_, ?_⟩
    · have : startSet starts 0 = fun _ => false := funext fun x => by simp [startSet]
      rw [this]; exact hS0
    · rw [hfr _ (notInSlot h0 (head_low (by rw [aInput_eq]; decide))), (hF m hm).2]; rfl
  · -- the loop's end: every start added
    rw [hev k w _ hk h] at h0
    have := FramerCode.bw_eq0 h0
    simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not, Nat.not_lt] at this
    have hk' : k = starts.length := by
      rcases this with h' | h'
      · omega
      · rw [startsMax_eq] at h'; omega
    subst hk'
    exact ⟨vz, h⟩

/-! ## The rule asked -/

theorem rootCall_decl (i : Nat) : declared [rootCall i] = ["c"] := by
  unfold rootCall
  split
  · rfl
  · split
    · rename_i l _; cases l <;> rfl
    · rfl

theorem lowKK_rootCall (i : Nat) : LowKK [rootCall i] := by
  unfold rootCall
  split
  · exact lowKK_call (lowerArgs_two rfl rfl)
  · split
    · rename_i l _; cases l <;> exact lowKK_call (lowerArgs_three rfl rfl _)
    · exact lowKK_call (a := [.const _]) rfl

theorem pick_eval {w : PancakeState σ} {R i : Nat} (hR : R < 2 ^ 64) (hi : i < 2 ^ 64)
    (h : eval w (.var "r") = some (BitVec.ofNat 64 R)) :
    eval w (.cmp .equal (.var "r") (.const (BitVec.ofNat 64 i))) = some (bw (decide (R = i))) :=
  FramerCode.eval_eq hR hi h rfl

section picks
variable (o : Oracle σ) {R : Nat}

/-- The branches of other rules than `R` pass. -/
theorem picks_skip (hR : R < 2 ^ 64) {X : Assn σ} (hX : Safe.ClockFree X)
    (hXr : ∀ w, X w → eval w (.var "r") = some
    (BitVec.ofNat 64 R))
    (hXc : ∀ w y v, X w → y = "c" → X (restore w y v)) :
    ∀ L : List Nat, R ∉ L → (∀ i ∈ L, i < 2 ^ 64) → Frag o (L.map pick) X X
  | [], _, _ => frag_nil o fun _ h => h
  | i :: L, hn, hb =>
    frag_append (xs := [_]) (frag_skip o rfl (lowKK_rootCall i) hX (fun w h => by
        rw [pick_eval hR (hb i (List.mem_cons_self ..)) (hXr w h)]
        rw [decide_eq_false (fun e => hn (by rw [e]; exact List.mem_cons_self ..))]; rfl)
      fun w y v h hy => hXc w y v h (by rw [rootCall_decl] at hy; simpa using hy))
      (picks_skip hR hX hXr hXc L (fun h => hn (List.mem_cons_of_mem _ h)) fun j hj => hb j (List.mem_cons_of_mem _ hj))

/-- **The branches**: the one of rule `R` calls it, the others pass. -/
theorem picks_frag (hR : R < 2 ^ 64) {P Q : Assn σ} (hP : Safe.ClockFree P) (hQ : Safe.ClockFree Q)
    (hPr : ∀ w, P w → eval w (.var "r") = some (BitVec.ofNat 64 R))
    (hQr : ∀ w, Q w → eval w (.var "r") = some (BitVec.ofNat 64 R))
    (hPc : ∀ w y v, P w → y = "c" → P (restore w y v)) (hQc : ∀ w y v, Q w → y = "c" → Q (restore w y v))
    (hcall : Frag o [rootCall R] P Q) :
    ∀ L : List Nat, L.Nodup → R ∈ L → (∀ i ∈ L, i < 2 ^ 64) → Frag o (L.map pick) P Q
  | [], _, hm, _ => nomatch hm
  | i :: L, hnd, hm, hb => by
    have hi := hb i (List.mem_cons_self ..)
    by_cases e : i = R
    · subst e
      refine frag_append (xs := [_]) (frag_ite o rfl hQ (fun w h => ⟨_, pick_eval hR hi (hPr w h)⟩)
        (frag_conseq hcall (fun _ h => h.1) fun _ h => h) (fun w y v h hy => hQc w y v h (by
          rw [rootCall_decl] at hy; simpa using hy))
        (frag_unsat lowKK_nil fun w ⟨h, h0⟩ => by rw [pick_eval hR hi (hPr w h)] at h0; simp [bw] at h0)
        (noDecl _ rfl)) (picks_skip o hR hQ hQr hQc L (List.nodup_cons.1 hnd).1 fun j hj => hb j (List.mem_cons_of_mem
            _ hj))
    · refine frag_append (xs := [_]) (frag_skip o rfl (lowKK_rootCall i) hP (fun w h => by
          rw [pick_eval hR hi (hPr w h), decide_eq_false (Ne.symm e)]; rfl)
        fun w y v h hy => hPc w y v h (by rw [rootCall_decl] at hy; simpa using hy)) ?_
      exact picks_frag hR hP hQ hPr hQr hPc hQc hcall L (List.nodup_cons.1 hnd).2
        ((List.mem_cons.1 hm).resolve_left (Ne.symm e)) fun j hj => hb j (List.mem_cons_of_mem _ hj)

end picks

/-- After the rule's call: slot 1 the ends of its matches from the starts. -/
def Picked (s0 : PancakeState σ) (A : Word) (bytes : List (BitVec 8)) (r : Nat) (starts : List Word)
    (m : Word → Word) : Prop :=
  RoundMem s0 A bytes r starts m ∧ Holds A m 1 (Ends bytes (.ref r) (startSet starts starts.length)) ∧
    m (at_ A aBroken) = bw (brokenAt starts starts.length)

theorem leaf_rule {r : Nat} (hr : r < AbnfRules.grammar.size) (hf : hasFun r = false) {l : Leaf}
    (hl : leafOf (termOf r) = some l) : l ∈ allLeaves := by
  unfold allLeaves
  refine List.mem_flatMap.2 ⟨r, List.mem_range.2 hr, ?_⟩
  rw [if_neg (by simp [hf]), hl]; exact List.mem_singleton_self _

theorem ends_ref {bytes : List (BitVec 8)} {r : Nat} (hr : r < AbnfRules.grammar.size) {S : Nat → Bool} (e : Nat) :
    Ends bytes (termOf r) S e ↔ Ends bytes (.ref r) S e :=
  ⟨fun ⟨x, hx, hm⟩ => ⟨x, hx, (AbnfMatch.ref_iff' (term_at hr)).2 hm⟩,
   fun ⟨x, hx, hm⟩ => ⟨x, hx, (AbnfMatch.ref_iff' (term_at hr)).1 hm⟩⟩

/-- **The rule asked, called** from slot 0 into slot 1: its function, or its leaf. -/
theorem rootCall_frag (o : Oracle σ) {ofs : Nat} {A : Word} {s0 : PancakeState σ} (hA : Area ofs A s0)
    (hcode : ProgCode s0.code ofs) {bytes : List (BitVec 8)} (hlen : bytes.length ≤ inputMax) {r : Nat}
    (hr : r < AbnfRules.grammar.size) {starts : List Word} (hks : starts.length ≤ startsMax)
    {l : List (String × Value)} (hc : Fresh "c" l = true) :
    Frag o [rootCall r] (RunF s0 l (StartsAt s0 A bytes r starts starts.length))
      (RunF s0 l (Picked s0 A bytes r starts)) := by
  have h0 : 0 < slots := by have := slots_two; omega
  have h1 : 1 < slots := by have := slots_two; omega
  have hb : aBroken < aSets := head_low (by rw [aInput_eq]; decide)
  unfold rootCall
  by_cases hf : hasFun r = true
  · rw [if_pos hf]
    have hi := order_has hr hf
    obtain ⟨-, hroots, -, -⟩ := order_all hi
    have hroots' : 2 ≤ frameOf r := hroots
    refine frag_conseq (ruleCall_frag o hA (rt := "c") hc (bodies_ok o hcode r hi) (e1 := Syntax.n 0)
      (e2 := Syntax.n 1) rfl rfl (by omega) (by omega) (by decide) (fun _ _ => rfl) (fun _ _ => rfl) hlen
      fun m hm => ⟨hm.2.1, hm.1.1⟩) (fun _ h => h) fun w ⟨v, h⟩ =>
        runF_mono h (fun q hq => List.mem_cons_of_mem _ hq)
        fun m' ⟨m, hm, _, hH, hall, hK⟩ => ⟨roundMem_kept hA.hA hlen hks h1 hm.1 hK hall, hH, by
          rw [kept_low h1 hK hb]; exact hm.2.2⟩
  · rw [if_neg hf]
    have hf' : hasFun r = false := by simpa using hf
    obtain ⟨lf, hl⟩ : ∃ lf, leafOf (termOf r) = some lf := by
      unfold hasFun at hf'; simp only [Bool.or_eq_false_iff, beq_eq_false_iff_ne, Option.isNone_eq_false_iff,
        Option.isSome_iff_exists] at hf'
      exact hf'.2
    rw [hl]
    have hlf := leaf_rule hr hf' hl
    have post : ∀ T : Nat → Bool,
        (∀ e, T e = true ↔ Ends bytes (termOf r) (startSet starts starts.length) e) →
        ∀ w : PancakeState σ, (∃ v, RunF s0 (("c", v) :: l) (fun m' => ∃ m,
          StartsAt s0 A bytes r starts starts.length m ∧ LeafRet A 1 T m v m') w) →
        RunF s0 l (Picked s0 A bytes r starts) w := fun T hT w ⟨v, h⟩ =>
      runF_mono h (fun q hq => List.mem_cons_of_mem _ hq) fun m' ⟨m, hm, _, hS1, hfr⟩ =>
        ⟨roundMem_kept hA.hA hlen hks h1 hm.1 (kept_frame (free := 0) (.inl rfl) hfr)
          (allSets_frame hm.1.1.1 h1 hS1 hfr), by
            unfold Holds; rw [← setOf_eq fun e => (hT e).trans (ends_ref hr e)]; exact hS1,
          by rw [hfr _ (notInSlot h1 hb)]; exact hm.2.2⟩
    rcases leafOf_some hl with ⟨rs, hrs, rfl⟩ | ⟨bs, c, hbs, rfl⟩
    · have hidx := class_idx hlf
      exact frag_conseq (class_frag o hA hcode hc rfl rfl h0 h1 (by decide) (List.getElem?_eq_some_iff.1 hidx).1
        (fun _ _ => rfl) (fun _ _ => rfl) hlen fun m hm => ⟨hm.2.1, hm.1.1⟩) (fun _ h => h)
        (post _ fun e => classSet_iff hrs hidx hlen e)
    · have hidx := text_idx hlf
      exact frag_conseq (text_frag o hA hcode hc rfl rfl h0 h1 (by decide) (List.getElem?_eq_some_iff.1 hidx).1
        (fun _ _ => rfl) (fun _ _ => rfl) hlen fun m hm => ⟨hm.2.1, hm.1.1⟩) (fun _ h => h)
        (post _ fun e => textSet_iff hbs hidx hlen e)

/-! ## The answer -/

theorem mem_setHas {ofs : Nat} : setHas .none ofs ∈ functions .none ofs := List.mem_append_left _
  (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))))))

/-- **A call of `setHas`.** -/
theorem has_frag (o : Oracle σ) {ofs : Nat} {A : Word} {s0 : PancakeState σ} (hA : Area ofs A s0)
    (hcode : ProgCode s0.code ofs) {rt : String} {l : List (String × Value)} {F : (Word → Word) → Prop}
    (hrt : Fresh rt l = true) {e1 e2 : Syntax.PExpr} {E1 E2 : PancakeExp} (he1 : Lower.lowerExp e1 = some E1)
    (he2 : Lower.lowerExp e2 = some E2) {k Y : Nat} (hk : k < slots) (hY : Y ≤ inputMax)
    (hv1 : ∀ u, RunF s0 l F u → eval u E1 = some (BitVec.ofNat 64 k))
    (hv2 : ∀ u, RunF s0 l F u → eval u E2 = some (BitVec.ofNat 64 Y)) {S : Nat → Bool}
    (hS : ∀ m, F m → SetAt m A k S ∧ Pows m A) :
    Frag o [.call rt "setHas" [e1, e2]] (RunF s0 l F)
      (fun u => ∃ v, RunF s0 ((rt, v) :: l) (fun m' => ∃ m, F m ∧ HasRet S Y m v m') u) :=
  progCall_frag o hA (f := setHas .none ofs) (args := [E1, E2]) (vs := [BitVec.ofNat 64 k, BitVec.ofNat 64 Y])
    (by show ["s", "y"].Nodup; decide) (lowerArgs_two he1 he2) (progCode_of hcode mem_setHas) rfl
    (fun u h => by simp only [evalArgs, hv1 u h, hv2 u h]) (R := HasRet S Y)
    (fun s1 hA1 _ _ _ hloc hF => setHas_ok o hA1 hk hY ((hloc "s").trans rfl) ((hloc "y").trans rfl) (hS _ hF).1
      (hS _ hF).2) hrt fun m m' v hF hr => ⟨m, hF, hr⟩

/-- The answer the round gives a case. -/
noncomputable def ansOf (r : Nat) (starts : List Word) (bytes : List (BitVec 8)) : Word :=
  if brokenAt starts starts.length then 2
  else bw (setOf (Ends bytes (.ref r) (startSet starts starts.length)) bytes.length)

theorem startSet_all {starts : List Word} (h : ∀ x ∈ starts, x.toNat ≤ inputMax) (y : Nat) :
    startSet starts starts.length y = true ↔ ∃ x ∈ starts, x.toNat = y := by
  simp only [startSet, List.take_length, List.any_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]
  exact ⟨fun ⟨x, hx, he, _⟩ => ⟨x, hx, he⟩, fun ⟨x, hx, he⟩ => ⟨x, hx, he, he ▸ h x hx⟩⟩

/-- **The round's answer is the case's.** -/
theorem ansOf_answer (r : Nat) (starts : List Word) (bytes : List (BitVec 8)) :
    Answer r starts bytes (ansOf r starts bytes) := by
  constructor
  · rintro ⟨x, hx, hb⟩
    have : brokenAt starts starts.length = true := by
      simp only [brokenAt, List.take_length, List.any_eq_true, decide_eq_true_eq]; exact ⟨x, hx, hb⟩
    simp [ansOf, this]
  · intro hall
    have : brokenAt starts starts.length = false := by
      simp only [brokenAt, List.take_length, List.any_eq_false, decide_eq_true_eq, Nat.not_lt]; exact hall
    simp only [ansOf, this, Bool.false_eq_true, if_false]
    have e : setOf (Ends bytes (.ref r) (startSet starts starts.length)) bytes.length = true ↔
        ∃ x ∈ starts, Matches AbnfRules.grammar (inputOf bytes) (.ref r) x.toNat bytes.length := by
      rw [setOf_iff]
      constructor
      · rintro ⟨y, hy, hm⟩
        obtain ⟨x, hx, rfl⟩ := (startSet_all hall y).1 hy
        exact ⟨x, hx, hm⟩
      · rintro ⟨x, hx, hm⟩
        exact ⟨x.toNat, (startSet_all hall _).2 ⟨x, hx, rfl⟩, hm⟩
    cases hb : setOf (Ends bytes (.ref r) (startSet starts starts.length)) bytes.length
    · rw [hb] at e
      exact ⟨Iff.intro (fun h => absurd h (by decide)) (fun h => absurd (e.2 h) (by simp)), .inl rfl⟩
    · rw [hb] at e
      exact ⟨⟨fun _ => e.1 rfl, fun _ => rfl⟩, .inr rfl⟩

theorem size_lt : AbnfRules.grammar.size < 2 ^ 32 := by decide +kernel

/-- **A case**, its header read and in range: the answer in `ans`. -/
theorem case_frag (o : Oracle σ) {ofs : Nat} {A : Word} {s0 : PancakeState σ} (hA : Area ofs A s0)
    (hcode : ProgCode s0.code ofs) {bytes : List (BitVec 8)} (hlen : bytes.length ≤ inputMax) {r : Nat}
    (hr : r < AbnfRules.grammar.size) {starts : List Word} (hks : starts.length ≤ startsMax)
    {l : List (String × Value)} (hla : ("a", A) ∈ l)
    (hfr : ∀ y ∈ ["z", "k", "ks", "u", "c", "h", "ans", "nn", "r"], Fresh y l = true)
    {F : (Word → Word) → Prop} (hF : ∀ m, F m → RoundMem s0 A bytes r starts m ∧ m (at_ A aBroken) = 0) :
    Frag o (caseBody AbnfRules.grammar.size) (RunF s0 (("ans", BitVec.ofNat 64 2) :: ("nn", BitVec.ofNat 64
        bytes.length) ::
        ("r", BitVec.ofNat 64 r) :: l) F)
      (RunF s0 (("ans", ansOf r starts bytes) :: ("nn", BitVec.ofNat 64 bytes.length) :: ("r", BitVec.ofNat 64 r) :: l)
        (RoundMem s0 A bytes r starts)) := by
  have hI := inputMax_eq
  have hsz := size_lt
  have h1 : 1 < slots := by have := slots_two; omega
  let Lr : List (String × Value) := ("ans", BitVec.ofNat 64 2) :: ("nn", BitVec.ofNat 64 bytes.length) ::
    ("r", BitVec.ofNat 64 r) :: l
  have hfL : ∀ y ∈ ["z", "k", "ks", "u", "c", "h"], Fresh y Lr = true := fun y hy => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact fresh_cons (by decide) (fresh_cons (by decide) (fresh_cons (by decide) (hfr _ (by simp))))
  have hlowP : LowKK ((List.range AbnfRules.grammar.size).map pick) := by
    induction (List.range AbnfRules.grammar.size) with
    | nil => exact lowKK_nil
    | cons i L ih => exact lowKK_append (xs := [_]) (lowKK_ite rfl (lowKK_rootCall i) lowKK_nil) ih
  have hlowA : LowKK [.call "h" "setHas" [Syntax.n 1, Syntax.v "nn"], .assign "ans" (Syntax.v "h"),
      .ite (word (Syntax.v "a") aBroken) [.assign "ans" (Syntax.n 2)] []] :=
    lowKK_append (xs := [_]) (lowKK_call (lowerArgs_two rfl rfl)) (lowK_any _ (k := .skip) rfl)
  unfold caseBody
  rw [List.append_assoc]
  refine frag_append (starts_frag o hA hcode hlen hks (l := Lr) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
    (List.mem_cons_of_mem _ hla))) (hfL "z" (by simp)) (hfL "k" (by simp)) (hfL "ks" (by simp)) (hfL "u" (by simp)) hF)
    (frag_exists (lowKK_append hlowP hlowA) fun vz => ?_)
  let L3 : List (String × Value) := ("ks", BitVec.ofNat 64 starts.length) :: ("k", BitVec.ofNat 64 starts.length) ::
    ("z", vz) :: Lr
  have hc3 : Fresh "c" L3 = true := fresh_cons (by decide) (fresh_cons (by decide) (fresh_cons (by decide)
    (hfL "c" (by simp))))
  have hr3 : ∀ G w, RunF s0 L3 G w → eval w (.var "r") = some (BitVec.ofNat 64 r) := fun G w h =>
    vals_mem h (by simp [L3, Lr])
  refine frag_append (picks_frag o (R := r) (by omega) (P := RunF s0 L3 (StartsAt s0 A bytes r starts starts.length))
    (Q := RunF s0 L3 (Picked s0 A bytes r starts)) (runF_clock _ _ _) (runF_clock _ _ _) (hr3 _) (hr3 _)
    (fun w y v h hy => by subst hy; exact runF_restore h hc3 v) (fun w y v h hy
        => by subst hy; exact runF_restore h hc3 v)
    (rootCall_frag o hA hcode hlen hr hks hc3) _ (List.nodup_range) (List.mem_range.2 hr)
    fun i hi => by have := List.mem_range.1 hi; omega) ?_
  -- whether the input's end is in slot 1
  have hh3 : Fresh "h" L3 = true := fresh_cons (by decide) (fresh_cons (by decide) (fresh_cons (by decide)
    (hfL "h" (by simp))))
  let S1 := setOf (Ends bytes (.ref r) (startSet starts starts.length))
  refine frag_append (xs := [_]) (has_frag o hA hcode (rt := "h") (l := L3) hh3 (lower_n 1) rfl h1 hlen
    (fun _ _ => rfl) (fun w h => vals_mem h (by simp [L3, Lr])) (S := S1) fun m hm => ⟨hm.2.1, hm.1.1.2.2.pows⟩)
    (frag_exists (lowK_any _ (k := .skip) rfl) fun vh => ?_)
  refine frag_pure (vh = bw (S1 bytes.length)) (fun w h => let ⟨_, _, _, hv⟩ := h.2; hv)
    (lowK_any _ (k := .skip) rfl)
    fun hvh => ?_
  let G : (Word → Word) → Prop := fun m' => ∃ m, Picked s0 A bytes r starts m ∧ HasRet S1 bytes.length m vh m'
  let Lt : List (String × Value) := ("ans", ansOf r starts bytes) :: ("nn", BitVec.ofNat 64 bytes.length) ::
    ("r", BitVec.ofNat 64 r) :: l
  have hsub : ∀ (X : List (String × Value)) (v : Value), (∀ q ∈ Lr, q.1 ≠ "ans" → q ∈ X) →
      v = ansOf r starts bytes →
      ∀ w, RunF s0 (("ans", v) :: without "ans" X) G w → RunF s0 Lt (RoundMem s0 A bytes r starts) w :=
    fun X v hX hv w h => runF_mono h (fun q hq => by
      simp only [Lt, List.mem_cons] at hq
      rcases hq with rfl | rfl | rfl | hq
      · rw [hv]; exact List.mem_cons_self ..
      · exact List.mem_cons_of_mem _ (mem_without (hX _ (by simp [Lr]) (show ("nn" : String) ≠ "ans" by decide))
          (show ("nn" : String) ≠ "ans" by decide))
      · exact List.mem_cons_of_mem _ (mem_without (hX _ (by simp [Lr]) (show ("r" : String) ≠ "ans" by decide))
          (show ("r" : String) ≠ "ans" by decide))
      · have hne : q.1 ≠ "ans" := ScanRun.fresh_ne (hfr "ans" (by simp)) q hq
        exact List.mem_cons_of_mem _ (mem_without (hX _ (by simp [Lr, hq]) hne) hne))
      fun m' ⟨m, hm, hmm, _⟩ => hmm ▸ hm.1
  refine frag_append (xs := [_]) (runF_set o rfl (w := BitVec.ofNat 64 2) (by
      rw [ScanRun.lookup_cons_ne (by decide), ScanRun.lookup_cons_ne (by decide), ScanRun.lookup_cons_ne (by decide),
        ScanRun.lookup_cons_ne (by decide), lookup_head]) (v := vh)
    fun w h => vals_mem h (List.mem_cons_self ..)) ?_
  have hb : aBroken < aInput := by rw [aInput_eq]; decide
  refine ScanRun.frag_if o rfl (lowK_any _ (k := .skip) rfl) lowKK_nil rfl rfl (runF_clock _ _ _)
    (b := brokenAt starts starts.length) (fun w h => ?_) (fun hbt => ?_) fun hbf => ?_
  · have ha : w.locals "a" = some A := h.1.vals ("a", A) (List.mem_cons_of_mem _ (mem_without
      (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ hla))))))) (show ("a" : String) ≠ "ans"
          by decide)))
    rw [load_at hA h.1.memaddrs ha hb (by decide)]
    obtain ⟨m, hm, hmm, _⟩ := h.2
    rw [hmm]; exact congrArg some hm.2.2
  · have hX : ∀ q ∈ Lr, q.1 ≠ "ans" → q ∈ ("ans", vh) :: without "ans" (("h", vh) :: L3) := fun q hq hne =>
      List.mem_cons_of_mem _ (mem_without (.tail _ (.tail _ (.tail _ (.tail _ hq)))) hne)
    exact frag_conseq (runF_set o rfl (w := vh) (lookup_head _ _ _) (v := BitVec.ofNat 64 2) fun _ _ => rfl)
      (fun _ h => h) (hsub _ _ hX (by simp [ansOf, hbt]))
  · exact frag_nil o fun w h => hsub (("h", vh) :: L3) vh (fun q hq _ => .tail _ (.tail _ (.tail _ (.tail _ hq))))
      (by simp only [ansOf, hbf, Bool.false_eq_true, if_false]; exact hvh) w h

/-! ## A round of `main` -/

theorem declared_picks : ∀ L : List Nat, declared (L.map pick) = []
  | [] => rfl
  | _ :: L => declared_picks L

/-- **A round of `main`**: a case in range, its answer in the area's answer word, the rest kept. -/
theorem round_frag (o : Oracle σ) {ofs : Nat} {A : Word} {s0 : PancakeState σ} (hA : Area ofs A s0)
    (hcode : ProgCode s0.code ofs) {bytes : List (BitVec 8)} (hlen : bytes.length ≤ inputMax) {r : Nat}
    (hr : r < AbnfRules.grammar.size) {starts : List Word} (hks : starts.length ≤ startsMax)
    {l : List (String × Value)} (hla : ("a", A) ∈ l)
    (hfr : ∀ y ∈ ["z", "k", "ks", "u", "c", "h", "ans", "nn", "r"], Fresh y l = true)
    {F : (Word → Word) → Prop} (hF : ∀ m, F m → RoundMem s0 A bytes r starts m) :
    Frag o (round AbnfRules.grammar.size) (RunF s0 l F)
      (RunF s0 l fun m => RoundMem s0 A bytes r starts m ∧ m (at_ A aAnswer) = ansOf r starts bytes) := by
  have hI := inputMax_eq
  have hsz := size_lt
  have hb : aBroken < aInput := by rw [aInput_eq]; decide
  have hans : aAnswer < aInput := by rw [aInput_eq]; decide
  have hsets := input_sets
  have hla' : ∀ G w, RunF s0 l G w → w.locals "a" = some A := fun G w h => h.1.vals _ hla
  unfold round
  -- the flag cleared
  refine frag_append (xs := [_]) (runF_store o hA (d := Syntax.atOff (Syntax.v "a") aBroken) (e := Syntax.n 0) rfl rfl
    (y := aBroken) (by omega) (by decide) (fun w h => by simp only [eval, hla' _ w h]; rfl) (val := fun _ => 0)
    (fun _ _ => rfl) (G := fun m => RoundMem s0 A bytes r starts m ∧ m (at_ A aBroken) = 0)
    fun m hm => ⟨roundMem_upd hA.hA hlen hks (hF m hm) (.inl rfl) 0, upd_eq _ _ _⟩) ?_
  -- the header read
  have hr1 : Fresh "r" l = true := hfr "r" (by simp)
  have hn1 : Fresh "nn" (("r", BitVec.ofNat 64 r) :: l) = true := fresh_cons (by decide) (hfr "nn" (by simp))
  have ha1 : Fresh "ans" (("nn", BitVec.ofNat 64 bytes.length) :: ("r", BitVec.ofNat 64 r) :: l) = true :=
    fresh_cons (by decide) (fresh_cons (by decide) (hfr "ans" (by simp)))
  refine frag_append (xs := [_]) (runF_dec o rfl hr1 (v := BitVec.ofNat 64 r) fun w h => ?_)
    (frag_append (xs := [_]) (runF_dec o rfl hn1 (v := BitVec.ofNat 64 bytes.length) fun w h => ?_)
    (frag_append (xs := [_]) (runF_dec o rfl ha1 (v := BitVec.ofNat 64 2) fun _ _ => rfl) ?_))
  · rw [load_eval hA h.1.memaddrs (y := 0) (by omega) (by decide) (by rw [at_zero]; exact hla' _ w h)]
    exact congrArg some h.2.1.2.rule
  · rw [load_at hA h.1.memaddrs (h.1.vals _ (List.mem_cons_of_mem _ hla)) (by rw [aInput_eq]; decide) (by decide)]
    exact congrArg some h.2.1.1.2.1
  let Lt : List (String × Value) := ("ans", ansOf r starts bytes) :: ("nn", BitVec.ofNat 64 bytes.length) ::
    ("r", BitVec.ofNat 64 r) :: l
  have hdecl : declared (caseBody AbnfRules.grammar.size) = ["z", "k", "ks", "h"] := by
    unfold caseBody; rw [declared_append, declared_append, declared_picks]; rfl
  have hval : ∀ (G : (Word → Word) → Prop) w, RunF s0 (("ans", BitVec.ofNat 64 2) :: ("nn", BitVec.ofNat 64
      bytes.length) ::
      ("r", BitVec.ofNat 64 r) :: l) G w → eval w (FramerCode.or2E (FramerCode.or2E (.cmp .less (.var "nn")
        (.const (BitVec.ofNat 64 0))) (.cmp .less (.const (BitVec.ofNat 64 inputMax)) (.var "nn")))
        (FramerCode.or2E (.cmp .less (.var "r") (.const (BitVec.ofNat 64 0)))
          (.cmp .less (.const (BitVec.ofNat 64 (AbnfRules.grammar.size - 1))) (.var "r")))) = some 0 := fun G w h => by
    have hnn : eval w (.var "nn") = some (BitVec.ofNat 64 bytes.length) := vals_mem h (by simp)
    have hrr : eval w (.var "r") = some (BitVec.ofNat 64 r) := vals_mem h (by simp)
    rw [FramerCode.eval_or2 (FramerCode.eval_or2 (FramerCode.eval_lt (by omega) (by omega) hnn rfl)
      (FramerCode.eval_lt (by omega) (by omega) rfl hnn)) (FramerCode.eval_or2
        (FramerCode.eval_lt (by omega) (by omega) hrr rfl) (FramerCode.eval_lt (by omega) (by omega) rfl hrr))]
    simp only [Nat.not_lt_zero, decide_false, Bool.or_false, decide_eq_false (Nat.not_lt.2 hlen),
      decide_eq_false (show ¬(AbnfRules.grammar.size - 1 < r) by omega)]
    rfl
  refine frag_append (xs := [_]) (M := RunF s0 Lt (RoundMem s0 A bytes r starts)) (frag_ite o rfl (runF_clock _ _ _)
    (fun w h => ⟨_, hval _ w h⟩) (frag_unsat lowKK_nil fun w ⟨h, hne⟩ => hne (hval _ w h)) (noDecl _ rfl)
    (frag_conseq (case_frag o hA hcode hlen hr hks hla hfr fun m hm => hm) (fun _ h => h.1) fun _ h => h)
    fun w y v h hy => ?_) ?_
  · rw [hdecl] at hy
    have hy' : Fresh y Lt = true := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
      rcases hy with rfl | rfl | rfl | rfl <;>
        exact fresh_cons (by decide) (fresh_cons (by decide) (fresh_cons (by decide) (hfr _ (by simp))))
    exact runF_restore h hy' v
  -- the answer stored
  refine frag_conseq (runF_store o hA (d := Syntax.atOff (Syntax.v "a") aAnswer) (e := Syntax.v "ans") rfl rfl
    (y := aAnswer) (by omega) (by decide) (fun w h => by
      simp only [eval, show w.locals "a" = some A from h.1.vals _ (.tail _ (.tail _ (.tail _ hla)))]; rfl)
    (val := fun _ => ansOf r starts bytes) (fun w h => vals_mem h (List.mem_cons_self ..))
    (G := fun m => RoundMem s0 A bytes r starts m ∧ m (at_ A aAnswer) = ansOf r starts bytes)
    fun m hm => ⟨roundMem_upd hA.hA hlen hks hm (.inr rfl) _, upd_eq _ _ _⟩) (fun _ h => h)
    fun w h => runF_mono h (fun q hq => .tail _ (.tail _ (.tail _ hq))) fun _ h => h

/-- **`main` answers as `matches?`.** From the one start 0, the round answers whether rule `r` matches the whole input.
This holds whenever `matches?` gives an answer. -/
theorem ansOf_matches {r depth : Nat} {bytes : List (BitVec 8)} {b : Bool}
    (h : Abnf.matches? AbnfRules.grammar depth r (bytes.map BitVec.toNat) = .ok b) :
    ansOf r [0] bytes = bw b := by
  have hm := AbnfEnds.matches?_ok h
  have hin : (bytes.map BitVec.toNat).toArray = inputOf bytes := rfl
  rw [hin, List.length_map] at hm
  have hb : brokenAt [0] ([0] : List Word).length = false := by simp [brokenAt, inputMax]
  have e : setOf (Ends bytes (.ref r) (startSet [0] ([0] : List Word).length)) bytes.length = true ↔
      Matches AbnfRules.grammar (inputOf bytes) (.ref r) 0 bytes.length := by
    rw [setOf_iff]
    constructor
    · rintro ⟨y, hy, hmy⟩
      have : y = 0 := by simp [startSet, inputMax] at hy; exact hy.1.symm
      subst this; exact hmy
    · intro hmy
      exact ⟨0, by simp [startSet, inputMax], hmy⟩
  unfold ansOf
  rw [hb, if_neg Bool.false_ne_true]
  cases hc : setOf (Ends bytes (.ref r) (startSet [0] ([0] : List Word).length)) bytes.length <;> cases b
  · rfl
  · rw [hc] at e; exact absurd (e.2 (hm.1 rfl)) (by decide)
  · rw [hc] at e; exact absurd (hm.2 (e.1 rfl)) (by decide)
  · rfl

/-! ## The functions' names -/

theorem tl_rule {i : Nat} (hi : i ≠ commentRule) :
    ∃ rest, (funName i).toList = 'r' :: 'u' :: 'l' :: 'e' :: (Nat.toDigits 10 i ++ '_' :: rest) := by
  unfold funName
  rw [if_neg (by simpa using hi)]
  refine ⟨(String.ofList ((AbnfRules.names[i]?.getD "").toList.map fun c => if c == '-' then '_' else c)).toList,
    ?_⟩
  rw [String.toList_append, String.toList_append, String.toList_append, show "rule".toList = ['r', 'u', 'l', 'e'] from
      rfl,
    show "_".toList = ['_'] from rfl]
  show ['r', 'u', 'l', 'e'] ++ (Nat.repr i).toList ++ ['_'] ++ _ = _
  rw [Nat.toList_repr]; simp only [List.append_assoc, List.cons_append, List.nil_append]

/-- No two rules' functions share a name. -/
theorem funName_inj {i j : Nat} (h : funName i = funName j) : i = j := by
  have hc : (funName commentRule).toList = "ruleComment".toList := by rw [funName_comment]
  by_cases hi : i = commentRule <;> by_cases hj : j = commentRule
  · rw [hi, hj]
  · obtain ⟨rest, e⟩ := tl_rule hj
    rw [hi] at h
    have e2 := congrArg String.toList h
    rw [hc, e] at e2
    have hd := Nat.toDigits_ne_nil (b := 10) (n := j)
    cases hD : Nat.toDigits 10 j with
    | nil => exact absurd hD hd
    | cons c D =>
      rw [hD] at e2
      have hcd : c.isDigit = true := Nat.isDigit_of_mem_toDigits (by decide) (by decide) (hD ▸ List.mem_cons_self ..)
      simp only [List.cons_append, show "ruleComment".toList = ['r', 'u', 'l', 'e', 'C', 'o', 'm', 'm', 'e', 'n', 't']
        from rfl, List.cons.injEq] at e2
      rw [← e2.2.2.2.2.1] at hcd; exact absurd hcd (by decide)
  · obtain ⟨rest, e⟩ := tl_rule hi
    have e2 := congrArg String.toList h
    rw [hj, hc, e] at e2
    cases hD : Nat.toDigits 10 i with
    | nil => exact absurd hD Nat.toDigits_ne_nil
    | cons c D =>
      rw [hD] at e2
      have hcd : c.isDigit = true := Nat.isDigit_of_mem_toDigits (by decide) (by decide) (hD ▸ List.mem_cons_self ..)
      simp only [List.cons_append, show "ruleComment".toList = ['r', 'u', 'l', 'e', 'C', 'o', 'm', 'm', 'e', 'n', 't']
        from rfl, List.cons.injEq] at e2
      rw [e2.2.2.2.2.1] at hcd; exact absurd hcd (by decide)
  · obtain ⟨r1, e1⟩ := tl_rule hi
    obtain ⟨r2, e2⟩ := tl_rule hj
    have e := congrArg String.toList h
    rw [e1, e2] at e
    simp only [List.cons.injEq, true_and] at e
    have := congrArg (List.takeWhile Char.isDigit) e
    rw [takeWhile_digits i (z := '_' :: r1) (by simp), takeWhile_digits j (z := '_' :: r2) (by simp)] at this
    rw [← digitsVal_toDigits i, ← digitsVal_toDigits j, this]

theorem names_nodup (ofs : Nat) : ((functions .none ofs).map (·.name)).Nodup := by
  unfold functions
  rw [List.map_append, List.map_map]
  have hr : List.map ((fun x => x.name) ∘ ruleFun .none ofs) order = order.map funName := by
    congr 1; funext i; exact ruleFun_name _ _ _
  rw [hr]
  have hset : ∀ a ∈ ["setClear", "setAdd", "setUnion", "setCopy", "setVoid", "setMinus", "setGrow", "setEmpty",
      "setHas", "leafClass", "leafText", "tables"], ∀ i, a ≠ funName i := fun a ha i e => by
    have hr0 : ∃ rest, (funName i).toList = 'r' :: rest := by
      by_cases hi : i = commentRule
      · rw [hi, funName_comment]; exact ⟨_, rfl⟩
      · obtain ⟨rest, e⟩ := tl_rule hi; exact ⟨_, e⟩
    obtain ⟨rest, e'⟩ := hr0
    rw [← e] at e'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with h | h | h | h | h | h | h | h | h | h | h | h <;> rw [h] at e' <;>
      (have := congrArg List.head? e'; simp at this)
  refine List.nodup_append.2 ⟨by show ["setClear", "setAdd", "setUnion", "setCopy", "setVoid", "setMinus", "setGrow",
      "setEmpty", "setHas", "leafClass", "leafText", "tables"].Nodup; decide,
    AbnfOrder.facts.2.1.map funName fun _ _ hne e => hne (funName_inj e), fun a ha b hb e => ?_⟩
  obtain ⟨i, -, rfl⟩ := List.mem_map.1 hb
  exact hset a ha i e

/-- The code a run of the program holds: each function by its name, as it lowers. -/
noncomputable def progCode (ofs : Nat) : String → Option (List String × PancakeProg) := fun name =>
  ((functions .none ofs).find? (·.name == name)).bind fun f => (Lower.lower f).map ((f.params.map (·.2)), ·)

theorem find_name : ∀ {L : List Syntax.PFun} {f : Syntax.PFun}, (L.map (·.name)).Nodup → f ∈ L →
    L.find? (·.name == f.name) = some f
  | g :: L, f, hnd, hf => by
    rw [List.find?_cons]
    rcases List.mem_cons.1 hf with rfl | hf
    · simp
    · have hne : g.name ≠ f.name := fun e => (List.nodup_cons.1 hnd).1 (by
        show g.name ∈ _; rw [e]; exact List.mem_map.2 ⟨f, hf, rfl⟩)
      rw [show (g.name == f.name) = false from beq_false_of_ne hne]
      exact find_name (List.nodup_cons.1 hnd).2 hf

/-- **The program's code holds each of its functions.** -/
theorem progCode_ok (ofs : Nat) : ProgCode (progCode ofs) ofs := fun f hf body hb => by
  simp only [progCode, find_name (names_nodup ofs) hf, Option.bind_some, hb, Option.map_some]

/-! ## The premises can hold -/

/-- A memory at 0 holding the tables and every slot empty. -/
noncomputable def baseMem (a : Word) : Word :=
  @ite _ (∃ k, k < slots ∧ a = slotW 0 k 0) (Classical.propDecidable _) 1 (tablesMem a)

theorem low_base {x : Nat} (hx : x < aSets) : baseMem (at_ 0 x) = tablesMem (at_ 0 x) := by
  unfold baseMem; exact if_neg fun ⟨_, hk, e⟩ => notInSlot hk hx ⟨0, by decide, e⟩

theorem base_slot {k i : Nat} (hk : k < slots) (hi : i < setSize / 8) :
    baseMem (slotW 0 k i) = if i = 0 then 1 else 0 := by
  by_cases h0 : i = 0
  · subst h0; rw [if_pos rfl]; unfold baseMem; exact if_pos ⟨k, hk, rfl⟩
  · rw [if_neg h0]
    unfold baseMem
    refine (if_neg fun ⟨k', hk', e⟩ => h0 (slotW_inj hk hk' hi (by decide) e).2).trans
      (tablesMem_high (Nat.le_trans (aSets_le_off k) (Nat.le_add_right _ _))
        (Nat.lt_of_lt_of_le (off_small hk _ (by rw [setSize_eq] at hi ⊢; omega)) (by decide)))

theorem setAt_base {k : Nat} (hk : k < slots) : SetAt baseMem 0 k (fun _ => false) where
  lo := by rw [base_slot hk (by decide), if_pos rfl]; decide
  hi := by rw [base_slot hk (by decide), if_neg (by decide)]; decide
  bits := fun w hw j hj => by rw [base_slot hk (bitIdx hw), if_neg (by omega)]; simp
  small := fun _ h => nomatch h
  win := fun _ h => nomatch h
  some := fun h => by rw [base_slot hk (by decide), base_slot hk (by decide)] at h; simp at h

theorem tables_low {x : Nat} (hx : x < aPow) : tablesMem (at_ 0 x) = 0 := by
  unfold tablesMem tablesOf
  rw [at0 (by have := pow_lt; have := aSets_le; omega), if_pos hx]

theorem below_pow {x : Nat} (hx : x < aInput) : x < aPow := Nat.lt_of_lt_of_le hx input_pow

theorem base_witness : Base (bareState ()) 0 [] baseMem := by
  refine ⟨fun k hk => ⟨_, setAt_base hk⟩, ?_,
    reads_keep (by decide) (by simp) reads_witness fun _ hx => low_base hx⟩
  rw [low_base aLen_low, tables_low (below_pow (by rw [aInput_eq]; decide))]; rfl

theorem caseAt_witness : CaseAt baseMem 0 0 [] := by
  refine ⟨?_, ?_, fun _ h => nomatch h⟩
  · rw [low_base (head_low (by rw [aInput_eq]; decide)), tables_low (below_pow (by rw [aInput_eq]; decide))]; rfl
  · rw [low_base (head_low (by rw [aInput_eq]; decide)), tables_low (below_pow (by rw [aInput_eq]; decide))]; rfl

theorem roundMem_witness : RoundMem (bareState ()) 0 [] 0 [] baseMem := ⟨base_witness, caseAt_witness⟩

theorem startsAt_witness : StartsAt (bareState ()) 0 [] 0 [] 0 baseMem := by
  refine ⟨roundMem_witness, setAt_base (by have := slots_two; omega), ?_⟩
  rw [low_base (head_low (by rw [aInput_eq]; decide)), tables_low (below_pow (by rw [aInput_eq]; decide))]; rfl

theorem holds_none {k : Nat} (hk : k < slots) {P : Nat → Prop} (hP : ∀ e, ¬P e) : Holds 0 baseMem k P := by
  unfold Holds
  rw [← setOf_eq (T := fun _ => false) fun e => Iff.intro (fun h => absurd h Bool.false_ne_true) fun h => absurd h (hP
      e)]
  exact setAt_base hk

theorem holds_witness : Holds 0 baseMem 0 (fun _ => False) :=
  holds_none (by have := slots_two; omega) fun _ h => h

theorem kept_witness : Kept 0 0 0 baseMem baseMem := kept_refl _

theorem named_witness : Named [(s!"c{0}", 0)] 0 1 := named_one (name_c 0) (Nat.le_refl _) Nat.zero_lt_one

theorem notRL_witness : NotRL 0 s!"e{0}" := notRL_e 0

theorem reach_witness : Reach #[] (.seq []) (fun _ => true) 0 0 := ⟨0, rfl, .zero⟩

theorem slotE_witness : SlotE (Syntax.n 0) := .inl ⟨0, rfl⟩

theorem slotIs_witness : SlotIs [] (Syntax.n 0) 0 := .inl rfl

theorem seqPre_witness : SeqPre (σ := Unit) Oracle.idle (ofs := 0) 0 0 [] (fun _ => none) := fun _ h => nomatch h

/-- A state at 0 holding the program's code. -/
noncomputable def codeState : PancakeState Unit := { bareState () with code := progCode 0 }

theorem codeState_area : Area 0 0 codeState := ⟨rfl, rfl, fun _ _ _ => rfl⟩

/-- `gen`, with the program's code, does what it is to: any steps, the empty input. -/
theorem genOk_witness : GenOk (σ := Unit) Oracle.idle 0 0 codeState [] steps (gen .none steps) :=
  gen_ok Oracle.idle codeState_area (progCode_ok 0) (Nat.zero_le _) steps

theorem roundBody_witness : RoundBody (σ := Unit) 0 (bareState ()) [] (.seq []) 0 none (fun _ => false) 0 0 0 0 0
    (· = baseMem) baseMem := by
  have h0 : 0 < slots := by have := slots_two; omega
  have hreach : ∀ j e, ¬Reach (inputOf ([] : List (BitVec 8))) (.seq []) (fun _ => false) j e :=
    fun _ _ ⟨_, h, _⟩ => Bool.false_ne_true h
  refine ⟨baseMem, ⟨baseMem, rfl, base_witness, kept_refl _, fun _ => ⟨?_, ?_, ?_⟩, fun h => nomatch h⟩, ?_,
    base_witness, kept_refl _⟩
  · exact holds_none h0 fun e ⟨j, _, _, h⟩ => hreach j e h
  · exact holds_none h0 fun e h => hreach 0 e h.1
  · exact fun _ ⟨_, _, h⟩ => absurd h.1 (hreach _ _)
  · exact holds_none h0 fun e ⟨_, h, _⟩ => hreach 0 _ (setOf_iff.1 h).1

theorem progCode_witness : ProgCode (progCode 0) 0 := progCode_ok 0

theorem allSets_witness : AllSets 0 baseMem := base_witness.1

theorem altPre_witness : AltPre (σ := Unit) Oracle.idle (ofs := 0) 0 0 [] (fun _ => none) := fun _ h => nomatch h

theorem avoid_witness : Avoid [] 0 0 := fun _ h => nomatch h

theorem bodyOk_witness : BodyOk (σ := Unit) Oracle.idle 0 (progCode 0) commentRule :=
  bodies_ok Oracle.idle (progCode_ok 0) commentRule comment_in

theorem cnt_witness : Cnt #[] (.seq []) 0 (fun _ => true) 0 := cnt_lo

theorem does_witness : Does (σ := Unit) Oracle.idle 0 codeState [] false (.seq []) (Syntax.n 0) (Syntax.n 1) 2 0
    ([.call s!"c{0}" "setCopy" [Syntax.n 1, Syntax.n 0]], 1) :=
  (nil_ok Oracle.idle codeState_area (progCode_ok 0) (Nat.zero_le _) (.inl ⟨0, rfl⟩) (.inl ⟨1, rfl⟩) slots_two 0
    false).2

theorem done_witness : Done #[] (.seq []) 0 (fun _ => true) 0 0 := ⟨0, Nat.le_refl _, Nat.le_refl _, 0, rfl, .zero⟩

theorem front_witness : Front #[] (.seq []) 0 (fun _ => true) 0 0 :=
  ⟨⟨0, rfl, .zero⟩, fun ⟨_, _, h, _⟩ => absurd h (Nat.not_lt_zero _)⟩

theorem genName_witness : GenName s!"c{0}" 0 := name_c 0

end DN.News.AbnfMain
