-- SPDX-License-Identifier: AGPL-3.0-or-later
import DN.News.RecoverArea

/-!
# DN.News.RecoverFirst

Recovery's first phases as the program runs them (`RecoverProg.begin`, `firstPass`, `journalGiven`) are those of
`DN.News.RecoverSpec`: from an area holding a state, each leaves it holding the state the phase gives, and what it
asks or gives.
-/

namespace DN.News.RecoverArea

open DN.Compiler DN.Compiler.Wp DN.Compiler.Frag DN.Compiler.Bytes DN.News.Journal DN.News.Recovery
open DN.News.RecoverProg
open DN.News.RecoverSpec (RSt)
open DN.News.ScanRun (at_ at_add vals_lookup kept_has without frag_if without_cons_self)
open DN.News.FramerCode (bw ult_eval)
open DN.News.FrameSpec (Byte)

variable {σ : Type}

/-! ## A name -/

/-- A name's kind, as `classify` gives it: 1 the journal, 2 to 5 a final, temporary, quarantine or tail name, 0 none
the store gives. -/
def kindOf : Option Name → Nat
  | some .journal => 1
  | some (.final _) => 2
  | some (.temp _) => 3
  | some (.quarantine _) => 4
  | some (.tail _) => 5
  | none => 0

/-- A name's number. -/
def numOf : Name → Nat
  | .journal => 0
  | .final s | .temp s | .quarantine s | .tail s => s

/-- The kind a name's first octet gives, as `classify` tests it. -/
def letterKind (c : Byte) : Nat :=
  if c.toNat = 106 then 5 else if c.toNat = 113 then 4 else if c.toNat = 116 then 3 else if c.toNat = 97 then 2 else 0

/-- What `classify` reads of digits after `acc`: their value, an octet that is not one skipped. -/
def digitsFrom (acc : Nat) (ds : Bytes) : Nat := ds.foldl (fun v c => ((digitValue c).map (16 * v + ·)).getD v) acc

/-- Whether each octet is a digit. -/
def allDigits (ds : Bytes) : Bool := ds.all fun c => (digitValue c).isSome

theorem foldlM_digits : ∀ (ds : Bytes) (acc : Nat),
    ds.foldlM hexStep acc = if allDigits ds then some (digitsFrom acc ds) else none
  | [], acc => by simp [allDigits, digitsFrom]
  | c :: ds, acc => by
    simp only [List.foldlM_cons, allDigits, List.all_cons, digitsFrom, List.foldl_cons]
    cases hd : digitValue c with
    | none => simp [hexStep, hd]
    | some d =>
      simp only [hexStep, hd, Option.map_some, Option.getD_some, Option.isSome_some, Bool.true_and]
      exact foldlM_digits ds (16 * acc + d)

theorem digitsFrom_lt : ∀ (ds : Bytes) (acc k : Nat), acc < 16 ^ k → digitsFrom acc ds < 16 ^ (k + ds.length)
  | [], acc, k, h => by simpa [digitsFrom] using h
  | c :: ds, acc, k, h => by
    simp only [digitsFrom, List.foldl_cons, List.length_cons]
    have := digitsFrom_lt ds (((digitValue c).map (16 * acc + ·)).getD acc) (k + 1) (by
      cases hd : digitValue c with
      | none => simp only [Option.map_none, Option.getD_none]; rw [Nat.pow_succ]; omega
      | some d =>
        have := digitValue_lt c d hd
        simp only [Option.map_some, Option.getD_some]; rw [Nat.pow_succ]; omega)
    rw [show k + (ds.length + 1) = k + 1 + ds.length by omega]
    exact this

theorem digitsFrom_snoc (acc : Nat) (ds : Bytes) (c : Byte) :
    digitsFrom acc (ds ++ [c]) = ((digitValue c).map (16 * digitsFrom acc ds + ·)).getD (digitsFrom acc ds) := by
  simp [digitsFrom]

theorem allDigits_snoc (ds : Bytes) (c : Byte) : allDigits (ds ++ [c]) = (allDigits ds && (digitValue c).isSome) := by
  simp [allDigits]

/-- **What a name of seventeen octets is**: its kind from its first octet once the others are digits, and their value
its number. -/
theorem parse_17 {c : Byte} {ds : Bytes} (hl : ds.length = 16) :
    kindOf (parseName (c :: ds)) = (if allDigits ds then letterKind c else 0) ∧
      ∀ n, parseName (c :: ds) = some n → numOf n = digitsFrom 0 ds := by
  have hj : (c :: ds == journalName) = false := by
    rw [beq_eq_false_iff_ne]; intro e
    have := congrArg List.length e
    have h7 : journalName.length = 7 := rfl
    simp only [List.length_cons, hl, h7] at this
    omega
  have hv : hexValue ds = if allDigits ds then some (digitsFrom 0 ds) else none := by
    simp only [hexValue, if_pos hl, foldlM_digits]
  unfold parseName
  rw [if_neg (by simp [hj])]
  dsimp only
  have ea : (CommandSpec.ascii "a").headD 0 = BitVec.ofNat 8 97 := rfl
  have et : (CommandSpec.ascii "t").headD 0 = BitVec.ofNat 8 116 := rfl
  have eq : (CommandSpec.ascii "q").headD 0 = BitVec.ofNat 8 113 := rfl
  have ejj : (CommandSpec.ascii "j").headD 0 = BitVec.ofNat 8 106 := rfl
  rw [ea, et, eq, ejj, hv]
  have hc := c.isLt
  have key : ∀ k : Nat, k < 256 → ((c == BitVec.ofNat 8 k) = true ↔ c.toNat = k) := fun k hk => by
    rw [beq_iff_eq]
    constructor
    · rintro rfl; simp; omega
    · intro e; apply BitVec.eq_of_toNat_eq; simp; omega
  by_cases h1 : c.toNat = 97
  · rw [if_pos ((key 97 (by decide)).mpr h1)]
    cases hd : allDigits ds <;> simp [kindOf, letterKind, h1, numOf]
  rw [if_neg (fun e => h1 ((key 97 (by decide)).mp e))]
  by_cases h2 : c.toNat = 116
  · rw [if_pos ((key 116 (by decide)).mpr h2)]
    cases hd : allDigits ds <;> simp [kindOf, letterKind, h2, numOf]
  rw [if_neg (fun e => h2 ((key 116 (by decide)).mp e))]
  by_cases h3 : c.toNat = 113
  · rw [if_pos ((key 113 (by decide)).mpr h3)]
    cases hd : allDigits ds <;> simp [kindOf, letterKind, h3, numOf]
  rw [if_neg (fun e => h3 ((key 113 (by decide)).mp e))]
  by_cases h4 : c.toNat = 106
  · rw [if_pos ((key 106 (by decide)).mpr h4)]
    cases hd : allDigits ds <;> simp [kindOf, letterKind, h4, numOf]
  rw [if_neg (fun e => h4 ((key 106 (by decide)).mp e))]
  simp [kindOf, letterKind, h1, h2, h3, h4]

/-- A name of a length other than seventeen octets, not the journal's, is none the store gives. -/
theorem parse_other {b : Bytes} (hj : b ≠ journalName) (hl : b.length ≠ 17) : parseName b = none := by
  unfold parseName
  rw [if_neg (by simpa using hj)]
  cases b with
  | nil => rfl
  | cons k ds =>
    have hv : hexValue ds = none := by
      simp only [hexValue]; rw [if_neg (by simp at hl; omega)]
    dsimp only
    simp [hv]

/-! ## A name read -/

/-- The locals `classify` sets. -/
def clsNames : List String := ["rk", "rl", "rq", "rc", "rlet", "rv", "rok", "rj"]

theorem cls_step : ∀ y ∈ clsNames, y ∈ stepLocals := fun y hy => List.mem_filter.2 ⟨by revert y hy; decide, by
  have : ∀ y ∈ clsNames, y ≠ "jsc" := by decide
  simp only [bne_iff_ne, ne_eq]; exact this y hy⟩

theorem shl4_or {V d : Nat} (hV : V < 2 ^ 60) (hd : d < 16) :
    (BitVec.ofNat 64 V <<< 4) ||| BitVec.ofNat 64 d = BitVec.ofNat 64 (16 * V + d) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_or, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (by omega : V < 2 ^ 64), Nat.mod_eq_of_lt (by omega : d < 2 ^ 64),
    Nat.mod_eq_of_lt (by omega : 16 * V + d < 2 ^ 64), Nat.shiftLeft_eq, Nat.mod_eq_of_lt
        (by omega : V * 2 ^ 4 < 2 ^ 64)]
  rw [← Nat.shiftLeft_eq, ← Nat.shiftLeft_add_eq_or_of_lt (by omega : d < 2 ^ 4), Nat.shiftLeft_eq]
  omega

/-- A local of `classify`'s set, with what else holds. -/
theorem cls_set (o : Oracle σ) {A : Word} {cfg : Config} {J : Bytes} {r : RSt} {s0 : PancakeState σ}
    (h : PBase A s0) {ws : Nat → Word} {os : List (Nat × Word)} {l : List (String × Value)}
    (hl : ScanRun.Outside clsNames l = true) {y : String} (hy : y ∈ clsNames) {e : Syntax.PExpr} {E : PancakeExp}
    (he : Lower.lowerExp e = some E) {F F' : Assn σ} (hF' : Safe.ClockFree F')
    (hv : ∀ u, Mid A cfg J r s0 ws os l u → F u → ∃ val, eval u E = some val ∧ F' (setL u y val)) :
    Frag o [.assign y e] (fun u => Mid A cfg J r s0 ws os l u ∧ F u) (fun u => Mid A cfg J r s0 ws os l u ∧ F' u) :=
  mid_put o h (cls_step y hy) (ScanRun.fresh_of_outside hl hy) he hF' hv

/-- The digit `classify` reads, after the number `V` and with the verdict `ok` so far. -/
theorem digit_frag (o : Oracle σ) {A : Word} {cfg : Config} {J : Bytes} {r : RSt} {s0 : PancakeState σ}
    (h : PBase A s0) {ws : Nat → Word} {os : List (Nat × Word)} {l : List (String × Value)}
    (hl : ScanRun.Outside clsNames l = true) {G : Assn σ} (hGc : Safe.ClockFree G)
    (hG : ∀ u y v, y ∈ ["rv", "rok"] → G u → G (setL u y v)) {c : Byte} {V : Nat} (hV : V < 2 ^ 60) {ok : Bool} :
    Frag o [.ite (Syntax.eAnd (Syntax.eLe (Syntax.n 48) (Syntax.v "rc")) (Syntax.eLe (Syntax.v "rc") (Syntax.n 57)))
        [.assign "rv" (Syntax.eOr (.shl (Syntax.v "rv") (Syntax.n 4)) (Syntax.eSub (Syntax.v "rc") (Syntax.n 48)))]
        [.ite (Syntax.eAnd (Syntax.eLe (Syntax.n 97) (Syntax.v "rc")) (Syntax.eLe (Syntax.v "rc") (Syntax.n 102)))
          [.assign "rv" (Syntax.eOr (.shl (Syntax.v "rv") (Syntax.n 4)) (Syntax.eSub (Syntax.v "rc") (Syntax.n 87)))]
          [.assign "rok" (ScanProg.lit 0)]]]
      (fun u => Mid A cfg J r s0 ws os l u ∧ G u ∧ u.locals "rc" = some (.ofNat 64 c.toNat) ∧
        u.locals "rv" = some (.ofNat 64 V) ∧ u.locals "rok" = some (bw ok))
      (fun u => Mid A cfg J r s0 ws os l u ∧ G u ∧ u.locals "rc" = some (.ofNat 64 c.toNat) ∧
        u.locals "rv" = some (.ofNat 64 (((digitValue c).map (16 * V + ·)).getD V)) ∧
        u.locals "rok" = some (bw (ok && (digitValue c).isSome))) := by
  have hc := c.isLt
  let Q : Assn σ := fun u => Mid A cfg J r s0 ws os l u ∧ G u ∧ u.locals "rc" = some (.ofNat 64 c.toNat) ∧
    u.locals "rv" = some (.ofNat 64 (((digitValue c).map (16 * V + ·)).getD V)) ∧
    u.locals "rok" = some (bw (ok && (digitValue c).isSome))
  have hQc : Safe.ClockFree Q := fun s k ⟨h1, h2, h3⟩ => ⟨mid_clock s k h1, hGc s k h2, h3⟩
  have hrange : ∀ (lo hi : Nat), lo < 2 ^ 63 → hi < 2 ^ 63 → ∀ (u : PancakeState σ),
      u.locals "rc" = some (.ofNat 64 c.toNat) →
      eval u (.op .and_ (.cmp .notLess (.var "rc") (.const (.ofNat 64 lo))) (.cmp .notLess (.const (.ofNat 64 hi))
        (.var "rc"))) = some (bw (decide (lo ≤ c.toNat) && decide (c.toNat ≤ hi))) := fun lo hi hlo hhi u hu =>
    FramerCode.eval_and (FramerCode.eval_le (t := u) (a := .const _) (b := .var "rc") hlo (by omega) rfl hu)
      (FramerCode.eval_le (t := u) (a := .var "rc") (b := .const _) (by omega) hhi hu rfl)
  have hset : ∀ (k : Nat) (u : PancakeState σ), u.locals "rc" = some (.ofNat 64 c.toNat) →
      u.locals "rv" = some (.ofNat 64 V) → k ≤ c.toNat → c.toNat - k < 16 →
      eval u (.op .or_ (.shiftL (.var "rv") (.const (.ofNat 64 4))) (.op .sub (.var "rc") (.const (.ofNat 64 k)))) =
        some (.ofNat 64 (16 * V + (c.toNat - k))) := fun k u hrc hrv hk hk16 => by
    have h4 : (decide ((BitVec.ofNat 64 4).toNat ≠ 0) && decide ((BitVec.ofNat 64 4).toNat ≥ 64)) = false := by decide
    simp only [eval, hrc, hrv, h4, Bool.false_eq_true, if_false]
    have e4 : (BitVec.ofNat 64 4).toNat = 4 := rfl
    rw [e4, BitVec.ofNat_sub_ofNat_of_le _ _ (by omega) (by omega), shl4_or hV hk16]
  refine frag_ite o (C := .op .and_ (.cmp .notLess (.var "rc") (.const (.ofNat 64 48)))
    (.cmp .notLess (.const (.ofNat 64 57)) (.var "rc"))) rfl hQc
    (fun u hu => ⟨_, hrange 48 57 (by decide) (by decide) u hu.2.2.1⟩) ?_ (noDecl _ rfl) ?_ (noDecl _ rfl)
  · refine set_frag o (E := .op .or_ (.shiftL (.var "rv") (.const (.ofNat 64 4)))
      (.op .sub (.var "rc") (.const (.ofNat 64 48)))) rfl hQc fun u ⟨⟨hm, hg, hrc, hrv, hok⟩, hne⟩ => ?_
    rw [hrange 48 57 (by decide) (by decide) u hrc] at hne
    have hd : 48 ≤ c.toNat ∧ c.toNat ≤ 57 := by
      cases e : (decide (48 ≤ c.toNat) && decide (c.toNat ≤ 57)) with
      | true => simp only [Bool.and_eq_true, decide_eq_true_eq] at e; exact e
      | false => rw [e] at hne; exact absurd rfl hne
    have hdv : digitValue c = some (c.toNat - 48) := by simp only [digitValue]; rw [if_pos hd]
    refine ⟨_, hset 48 u hrc hrv hd.1 (by omega), kept_has hm.kept (h.bound "rv" (by decide)),
      mid_setL hm (by decide) (ScanRun.fresh_of_outside hl (by decide)) _, hG u "rv" _ (by simp) hg,
      by simp [setL, setLocal, hrc], by simp [setL, setLocal, hdv], by simp [setL, setLocal, hok, hdv]⟩
  · refine frag_ite o (C := .op .and_ (.cmp .notLess (.var "rc") (.const (.ofNat 64 97)))
      (.cmp .notLess (.const (.ofNat 64 102)) (.var "rc"))) rfl hQc
      (fun u hu => ⟨_, hrange 97 102 (by decide) (by decide) u hu.1.2.2.1⟩) ?_ (noDecl _ rfl) ?_ (noDecl _ rfl)
    · refine set_frag o (E := .op .or_ (.shiftL (.var "rv") (.const (.ofNat 64 4)))
        (.op .sub (.var "rc") (.const (.ofNat 64 87)))) rfl hQc fun u ⟨⟨⟨hm, hg, hrc, hrv, hok⟩, h0⟩, hne⟩ => ?_
      rw [hrange 97 102 (by decide) (by decide) u hrc] at hne
      rw [hrange 48 57 (by decide) (by decide) u hrc] at h0
      have hd : 97 ≤ c.toNat ∧ c.toNat ≤ 102 := by
        cases e : (decide (97 ≤ c.toNat) && decide (c.toNat ≤ 102)) with
        | true => simp only [Bool.and_eq_true, decide_eq_true_eq] at e; exact e
        | false => rw [e] at hne; exact absurd rfl hne
      have hd0 : ¬ (48 ≤ c.toNat ∧ c.toNat ≤ 57) := by omega
      have hdv : digitValue c = some (c.toNat - 87) := by simp only [digitValue]; rw [if_neg hd0, if_pos hd]
      refine ⟨_, hset 87 u hrc hrv (by omega) (by omega), kept_has hm.kept (h.bound "rv" (by decide)),
        mid_setL hm (by decide) (ScanRun.fresh_of_outside hl (by decide)) _, hG u "rv" _ (by simp) hg,
        by simp [setL, setLocal, hrc], by simp [setL, setLocal, hdv], by simp [setL, setLocal, hok, hdv]⟩
    · refine set_frag o (E := .op .add (.var "jz") (.const (.ofNat 64 0))) rfl hQc
        fun u ⟨⟨⟨hm, hg, hrc, hrv, _⟩, h0⟩, h1⟩ => ?_
      rw [hrange 97 102 (by decide) (by decide) u hrc] at h1
      rw [hrange 48 57 (by decide) (by decide) u hrc] at h0
      have hd0 : ¬ (48 ≤ c.toNat ∧ c.toNat ≤ 57) := by
        intro hd; simp only [bw, decide_eq_true hd.1, decide_eq_true hd.2, Bool.and_self] at h0; cases h0
      have hd1 : ¬ (97 ≤ c.toNat ∧ c.toNat ≤ 102) := by
        intro hd; simp only [bw, decide_eq_true hd.1, decide_eq_true hd.2, Bool.and_self] at h1; cases h1
      have hdv : digitValue c = none := by simp only [digitValue]; rw [if_neg hd0, if_neg hd1]
      refine ⟨0, by simp [eval, jz_kept h hm.kept], kept_has hm.kept (h.bound "rok" (by decide)),
        mid_setL hm (by decide) (ScanRun.fresh_of_outside hl (by decide)) _, hG u "rok" _ (by simp) hg,
        by simp [setL, setLocal, hrc], by simp [setL, setLocal, hrv, hdv], by simp [setL, setLocal, hdv, bw]⟩

/-- A test of the name's first octet. -/
theorem letter_frag (o : Oracle σ) {A : Word} {cfg : Config} {J : Bytes} {r : RSt} {s0 : PancakeState σ}
    (h : PBase A s0) {ws : Nat → Word} {os : List (Nat × Word)} {l : List (String × Value)}
    (hl : ScanRun.Outside clsNames l = true) {G : Assn σ} (hGc : Safe.ClockFree G)
    (hG : ∀ u v, G u → G (setL u "rlet" v)) {c : Byte} {prev k m : Nat} (hk : k < 256) :
    Frag o [.ite (Syntax.eEq (Syntax.v "rc") (Syntax.n k)) [.assign "rlet" (ScanProg.lit m)] []]
      (fun u => Mid A cfg J r s0 ws os l u ∧ G u ∧ u.locals "rc" = some (.ofNat 64 c.toNat) ∧
        u.locals "rlet" = some (.ofNat 64 prev))
      (fun u => Mid A cfg J r s0 ws os l u ∧ G u ∧ u.locals "rc" = some (.ofNat 64 c.toNat) ∧
        u.locals "rlet" = some (.ofNat 64 (if c.toNat = k then m else prev))) := by
  have hc := c.isLt
  let Q : Assn σ := fun u => Mid A cfg J r s0 ws os l u ∧ G u ∧ u.locals "rc" = some (.ofNat 64 c.toNat) ∧
    u.locals "rlet" = some (.ofNat 64 (if c.toNat = k then m else prev))
  have hQc : Safe.ClockFree Q := fun s k ⟨h1, h2, h3⟩ => ⟨mid_clock s k h1, hGc s k h2, h3⟩
  have hev : ∀ (u : PancakeState σ), u.locals "rc" = some (.ofNat 64 c.toNat) →
      eval u (.cmp .equal (.var "rc") (.const (.ofNat 64 k))) = some (bw (decide (c.toNat = k))) := fun u hu =>
    FramerCode.eval_eq (t := u) (a := .var "rc") (b := .const _) (by omega) (by omega) hu rfl
  refine frag_ite o (C := .cmp .equal (.var "rc") (.const (.ofNat 64 k))) rfl hQc
    (fun u hu => ⟨_, hev u hu.2.2.1⟩) ?_ (noDecl _ rfl) (frag_nil o fun u ⟨⟨hm, hg, hrc, hlet⟩, h0⟩ => ?_)
        (noDecl _ rfl)
  · refine set_frag o (E := .op .add (.var "jz") (.const (.ofNat 64 m))) rfl hQc fun u ⟨⟨hm, hg, hrc, _⟩, hne⟩ => ?_
    rw [hev u hrc] at hne
    have hkc : c.toNat = k := by
      cases e : decide (c.toNat = k) with
      | true => exact of_decide_eq_true e
      | false => rw [e] at hne; exact absurd rfl hne
    refine ⟨.ofNat 64 m, by simp [eval, jz_kept h hm.kept], kept_has hm.kept (h.bound "rlet" (by decide)),
      mid_setL hm (by decide) (ScanRun.fresh_of_outside hl (by decide)) _, hG u _ hg, by simp [setL, setLocal, hrc],
      by simp [setL, setLocal, hkc]⟩
  · rw [hev u hrc] at h0
    have hkc : c.toNat ≠ k := fun e => by simp [e, bw] at h0
    exact ⟨hm, hg, hrc, by rw [if_neg hkc]; exact hlet⟩

/-- **A name read**, as `parseName` reads it: its kind into `rk` and, of a file's name, its number into `rv`. -/
theorem classify_frag (o : Oracle σ) {A : Word} {cfg : Config} {J : Bytes} {r : RSt} {s0 : PancakeState σ}
    (h : PBase A s0) (hL : r.name.length ≤ nameMax) {ws : Nat → Word} {os : List (Nat × Word)}
    {l : List (String × Value)} (hl : ScanRun.Outside clsNames l = true) (hws : ws rNameLen = .ofNat 64 r.name.length) :
    Frag o RecoverProg.classify (Mid A cfg J r s0 ws os l) (fun u => Mid A cfg J r s0 ws os l u ∧
      u.locals "rk" = some (.ofNat 64 (kindOf (parseName r.name))) ∧
      ∀ n, parseName r.name = some n → n ≠ .journal → u.locals "rv" = some (.ofNat 64 (numOf n))) := by
  have hn := nums
  let M : Assn σ := Mid A cfg J r s0 ws os l
  let Q : Assn σ := fun u => M u ∧ u.locals "rk" = some (.ofNat 64 (kindOf (parseName r.name))) ∧
    ∀ n, parseName r.name = some n → n ≠ .journal → u.locals "rv" = some (.ofNat 64 (numOf n))
  have hQc : Safe.ClockFree Q := fun s k ⟨h1, h2⟩ => ⟨mid_clock s k h1, h2⟩
  have hname : ∀ u, M u → ∀ i (hi : i < r.name.length),
      memLoadByte u.memory u.memaddrs u.be (at_ A rName + BitVec.ofNat 64 i) = some r.name[i] := fun u hu i hi => by
    rw [at_add]; exact hu.rest.name i hi
  -- the kind zero, the name's length and its place
  let F3 : Assn σ := fun u => u.locals "rk" = some 0 ∧ u.locals "rl" = some (.ofNat 64 r.name.length) ∧
    u.locals "rq" = some (at_ A rName)
  have hF3c : Safe.ClockFree F3 := fun _ _ h => h
  obtain ⟨E2, hE2⟩ : ∃ E, Lower.lowerExp (rw rNameLen) = some E := ⟨_, rfl⟩
  have s123 : Frag o [.assign "rk" (ScanProg.lit 0), .assign "rl" (rw rNameLen),
      .assign "rq" (Syntax.atOff rp rName)] M (fun u => M u ∧ F3 u) := by
    refine frag_conseq (P0 := fun u => M u ∧ True) ?_ (fun u hu => ⟨hu, trivial⟩) fun _ h => h
    refine frag_append (xs := [_]) (cls_set o h hl (y := "rk") (by decide)
      (E := .op .add (.var "jz") (.const (.ofNat 64 0))) rfl (F' := fun u => u.locals "rk" = some 0)
      (fun _ _ h => h) fun u hu _ => ⟨0, by simp [eval, jz_kept h hu.kept], by simp [setL, setLocal]⟩) ?_
    refine frag_append (xs := [_]) (cls_set o h hl (y := "rl") (by decide) hE2
      (F' := fun u => u.locals "rk" = some 0 ∧ u.locals "rl" = some (.ofNat 64 r.name.length)) (fun _ _ h => h)
      fun u hu hf => ⟨_, rw_eval h.hA (by rw [hu.kept.memaddrs]; exact h.dom) (rsc_kept h hu.kept) (by decide)
        (by decide) hE2, by simp [setL, setLocal, hf], by
          simp only [setL, setLocal, if_pos]; rw [hu.words rNameLen (by decide), hws]⟩) ?_
    exact cls_set o h hl (y := "rq") (by decide) (E := .op .add (.var "rsc") (.const (.ofNat 64 56))) rfl hF3c
      fun u hu hf => ⟨at_ A rName, by simp [eval, rsc_kept h hu.kept, at_, show rName = 56 from rfl],
        by simp [setL, setLocal, hf.1], by simp [setL, setLocal, hf.2], by simp [setL, setLocal]⟩
  refine frag_append (xs := [_, _, _]) s123 ?_
  -- the journal's name
  obtain ⟨EB, hEB⟩ : ∃ E, Lower.lowerExp (ScanProg.bytesAre (Syntax.v "rq") journalName) = some E := ⟨_, rfl⟩
  let C1 : PancakeExp := .op .and_ (.cmp .equal (.var "rl") (.const (.ofNat 64 7))) EB
  have hcond : ∀ u, M u → F3 u → ∃ ys : Bytes, ys.length = 7 ∧
      (∀ i (h1 : i < ys.length) (h2 : i < r.name.length), ys[i] = r.name[i]) ∧
      eval u C1 = some (bw (decide (r.name.length = 7) && decide (ys = journalName))) := fun u hu hf => by
    obtain ⟨ys, hyl, hy⟩ := Bytes.bytes_exist (u := u) (a := at_ A rName) 7 fun i hi => by
      rw [at_add, hu.kept.memaddrs]; exact h.dom _ (by omega)
    obtain ⟨E, hE, hv⟩ := ScanRun.bytesAre_eval (u := u) (p := Syntax.v "rq") (P := .var "rq") rfl hf.2.2
      (bs := journalName) (by rw [hyl]; rfl) hy
    obtain rfl : EB = E := Option.some.inj (hEB.symm.trans hE)
    refine ⟨ys, hyl, fun i h1 h2 => Option.some.inj ((hy i h1).symm.trans (hname u hu i h2)),
      FramerCode.eval_and (FramerCode.eval_eq (t := u) (a := .var "rl") (b := .const _) (by omega) (by decide)
        hf.2.1 rfl) hv⟩
  have hC1 : Lower.lowerExp (Syntax.eAnd (Syntax.eEq (Syntax.v "rl") (Syntax.n journalName.length))
      (ScanProg.bytesAre (Syntax.v "rq") journalName)) = some C1 := by
    simp only [Syntax.eAnd, Syntax.eEq, Lower.lowerExp, hEB]; rfl
  refine frag_ite o hC1 hQc (fun u ⟨hu, hf⟩ => let ⟨_, _, _, hv⟩ := hcond u hu hf; ⟨_, hv⟩) ?_ (noDecl _ rfl) ?_
    (noDecl _ rfl)
  · refine set_frag o (E := .op .add (.var "jz") (.const (.ofNat 64 1))) rfl hQc fun u ⟨⟨hu, hf⟩, hne⟩ => ?_
    obtain ⟨ys, hyl, hyn, hv⟩ := hcond u hu hf
    rw [hv] at hne
    have h7 : r.name.length = 7 ∧ ys = journalName := by
      cases e : (decide (r.name.length = 7) && decide (ys = journalName)) with
      | true => simp only [Bool.and_eq_true, decide_eq_true_eq] at e; exact e
      | false => rw [e] at hne; exact absurd rfl hne
    have hj : r.name = journalName := by
      rw [← h7.2]; exact List.ext_getElem (by rw [h7.1, hyl]) fun i h1 h2 => (hyn i h2 h1).symm
    have hp : parseName r.name = some .journal := by rw [hj]; unfold parseName; simp
    refine ⟨1, by simp [eval, jz_kept h hu.kept], kept_has hu.kept (h.bound "rk" (by decide)),
      mid_setL hu (by decide) (ScanRun.fresh_of_outside hl (by decide)) _, by simp [setL, setLocal, hp, kindOf],
      fun n hn hnj => ?_⟩
    rw [hp] at hn; cases hn; exact absurd rfl hnj
  have hnj : ∀ u, (M u ∧ F3 u) ∧ eval u C1 = some 0 → r.name ≠ journalName := fun u ⟨⟨hu, hf⟩, h0⟩ hj => by
    obtain ⟨ys, hyl, hyn, hv⟩ := hcond u hu hf
    rw [hv] at h0
    have h7 : r.name.length = 7 := by rw [hj]; rfl
    have hy : ys = journalName := by
      rw [← hj]; exact List.ext_getElem (by rw [hyl, h7]) fun i h1 h2 => hyn i h1 h2
    rw [h7, hy] at h0; simp [bw] at h0
  have hev17 : ∀ u, F3 u → eval u (.cmp .equal (.var "rl") (.const (.ofNat 64 17))) =
      some (bw (decide (r.name.length = 17))) := fun u hf =>
    FramerCode.eval_eq (t := u) (a := .var "rl") (b := .const _) (by omega) (by decide) hf.2.1 rfl
  refine frag_ite o (C := .cmp .equal (.var "rl") (.const (.ofNat 64 17))) rfl hQc
    (fun u hu => ⟨_, hev17 u hu.1.2⟩) ?_ (noDecl _ rfl) (frag_nil o fun u hu => ?_) (noDecl _ rfl)
  rotate_left
  · -- of another length: none the store gives
    obtain ⟨⟨⟨hm, hf⟩, h1⟩, h0⟩ := hu
    rw [hev17 u hf] at h0
    have h17 : r.name.length ≠ 17 := fun e => by simp [e, bw] at h0
    have hp := parse_other (hnj u ⟨⟨hm, hf⟩, h1⟩) h17
    exact ⟨hm, by rw [hp]; exact hf.1, fun n hn => by rw [hp] at hn; cases hn⟩
  -- seventeen octets
  refine frag_pure (r.name.length = 17 ∧ r.name ≠ journalName) (fun u hu => ⟨?_, hnj u hu.1⟩)
    (lowK_any _ (k := .skip) (c := _) rfl) fun ⟨h17, _⟩ => ?_
  · obtain ⟨⟨⟨_, hf⟩, _⟩, hne⟩ := hu
    rw [hev17 u hf] at hne
    cases e : decide (r.name.length = 17) with
    | true => exact of_decide_eq_true e
    | false => rw [e] at hne; exact absurd rfl hne
  obtain ⟨c, ds, hcd⟩ : ∃ c ds, r.name = c :: ds := by
    cases hc : r.name with
    | nil => rw [hc] at h17; cases h17
    | cons c ds => exact ⟨c, ds, rfl⟩
  have hds : ds.length = 16 := by rw [hcd] at h17; simpa using h17
  obtain ⟨hpk, hpn⟩ := parse_17 (c := c) hds
  rw [← hcd] at hpk hpn
  have hcL : ∀ u, M u → memLoadByte u.memory u.memaddrs u.be (at_ A rName) = some c := fun u hu => by
    have := hname u hu 0 (by omega)
    simp only [BitVec.add_zero] at this
    rw [this]; simp [hcd]
  have hdL : ∀ u, M u → ∀ j (hj : j < 16), memLoadByte u.memory u.memaddrs u.be
      (at_ A rName + BitVec.ofNat 64 (j + 1)) = some ds[j] := fun u hu j hj => by
    rw [hname u hu (j + 1) (by omega)]; simp [hcd]
  let G0 : Assn σ := fun u => u.locals "rk" = some 0 ∧ u.locals "rq" = some (at_ A rName)
  have hG0c : Safe.ClockFree G0 := fun _ _ h => h
  have hG0 : ∀ u v, G0 u → G0 (setL u "rlet" v) := fun u v ⟨h1, h2⟩ => by
    exact ⟨by simp [setL, setLocal, h1], by simp [setL, setLocal, h2]⟩
  refine frag_conseq (P0 := fun u => M u ∧ G0 u) ?_ (fun u hu => ⟨hu.1.1.1, hu.1.1.2.1, hu.1.1.2.2.2⟩) fun _ h => h
  -- the first octet, and the kind it gives
  refine frag_append (xs := [_]) (cls_set o h hl (y := "rc") (by decide) (E := .loadByte (.var "rq")) rfl
    (F' := fun u => G0 u ∧ u.locals "rc" = some (.ofNat 64 c.toNat)) (fun _ _ h => h) fun u hu hf =>
      ⟨.ofNat 64 c.toNat, by simp only [eval, hf.2, hcL u hu]; rw [Bytes.setWidth8_64],
        ⟨by simp [setL, setLocal, hf.1], by simp [setL, setLocal, hf.2]⟩, by simp [setL, setLocal]⟩) ?_
  refine frag_append (xs := [_]) (cls_set o h hl (y := "rlet") (by decide)
    (E := .op .add (.var "jz") (.const (.ofNat 64 0))) rfl
    (F' := fun u => G0 u ∧ u.locals "rc" = some (.ofNat 64 c.toNat) ∧ u.locals "rlet" = some (.ofNat 64 0))
    (fun _ _ h => h) fun u hu hf => ⟨0, by simp [eval, jz_kept h hu.kept],
      hG0 u _ hf.1, by simp [setL, setLocal, hf.2], by simp [setL, setLocal]⟩) ?_
  refine frag_append (xs := [_]) (letter_frag o h hl hG0c hG0 (prev := 0) (k := 97) (m := 2) (by decide)) ?_
  refine frag_append (xs := [_]) (letter_frag o h hl hG0c hG0 (k := 116) (m := 3) (by decide)) ?_
  refine frag_append (xs := [_]) (letter_frag o h hl hG0c hG0 (k := 113) (m := 4) (by decide)) ?_
  refine frag_append (xs := [_]) (letter_frag o h hl hG0c hG0 (k := 106) (m := 5) (by decide)) ?_
  -- the digits
  let G1 : Assn σ := fun u => G0 u ∧ u.locals "rlet" = some (.ofNat 64 (letterKind c))
  let H (j : Nat) : Assn σ := fun u => G1 u ∧ u.locals "rj" = some (.ofNat 64 (j + 1)) ∧ j ≤ 16
  let I (j : Nat) : Assn σ := fun u => M u ∧ H j u ∧
    u.locals "rv" = some (.ofNat 64 (digitsFrom 0 (ds.take j))) ∧ u.locals "rok" = some (bw (allDigits (ds.take j)))
  have hIc : ∀ j, Safe.ClockFree (I j) := fun _ s k ⟨h1, h2⟩ => ⟨mid_clock s k h1, h2⟩
  have hHs : ∀ j u y v, y ∈ ["rv", "rok"] → H j u → H j (setL u y v) := fun j u y v hy ⟨⟨⟨h1, h2⟩, h3⟩, h4, h5⟩ => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl <;>
      exact ⟨⟨⟨by simp [setL, setLocal, h1], by simp [setL, setLocal, h2]⟩, by simp [setL, setLocal, h3]⟩,
        by simp [setL, setLocal, h4], h5⟩
  refine frag_append (xs := [_, _, _]) (M := I 0) ?_ ?_
  · refine frag_conseq (P0 := fun u => M u ∧ G1 u) ?_ (fun u ⟨hm, ⟨h1, h2⟩, _, h4⟩ => ⟨hm, ⟨h1, h2⟩, h4⟩)
      fun _ h => h
    refine frag_append (xs := [_]) (cls_set o h hl (y := "rv") (by decide)
      (E := .op .add (.var "jz") (.const (.ofNat 64 0))) rfl
      (F' := fun u => G1 u ∧ u.locals "rv" = some (.ofNat 64 0)) (fun _ _ h => h) fun u hu hf =>
        ⟨0, by simp [eval, jz_kept h hu.kept], ⟨⟨by simp [setL, setLocal, hf.1.1], by simp [setL, setLocal, hf.1.2]⟩,
          by simp [setL, setLocal, hf.2]⟩, by simp [setL, setLocal]⟩) ?_
    refine frag_append (xs := [_]) (cls_set o h hl (y := "rok") (by decide)
      (E := .op .add (.var "jz") (.const (.ofNat 64 1))) rfl
      (F' := fun u => G1 u ∧ u.locals "rv" = some (.ofNat 64 0) ∧ u.locals "rok" = some 1) (fun _ _ h => h)
      fun u hu hf => ⟨1, by simp [eval, jz_kept h hu.kept], ⟨⟨by simp [setL, setLocal, hf.1.1.1],
        by simp [setL, setLocal, hf.1.1.2]⟩, by simp [setL, setLocal, hf.1.2]⟩, by simp [setL, setLocal, hf.2],
        by simp [setL, setLocal]⟩) ?_
    exact frag_conseq (cls_set o h hl (y := "rj") (by decide) (E := .op .add (.var "jz") (.const (.ofNat 64 1))) rfl
      (F' := fun u => G1 u ∧ u.locals "rv" = some (.ofNat 64 0) ∧ u.locals "rok" = some 1 ∧
        u.locals "rj" = some 1) (fun _ _ h => h) fun u hu hf => ⟨1, by simp [eval, jz_kept h hu.kept],
          ⟨⟨by simp [setL, setLocal, hf.1.1.1], by simp [setL, setLocal, hf.1.1.2]⟩, by simp [setL, setLocal, hf.1.2]⟩,
          by simp [setL, setLocal, hf.2.1], by simp [setL, setLocal, hf.2.2], by simp [setL, setLocal]⟩)
      (fun _ h => h) fun u ⟨hm, hg, hv, hk, hj⟩ =>
        ⟨hm, ⟨hg, by simpa using hj, by omega⟩, by simpa [digitsFrom] using hv, by simpa [allDigits, bw] using hk⟩
  have hHc : ∀ j, Safe.ClockFree (H j) := fun _ _ _ h => h
  have hbody : ∀ j, decide (j + 1 < 17) = true → Frag o [.assign "rc" (.loadb (Syntax.eAdd (Syntax.v "rq")
      (Syntax.v "rj"))),
      .ite (Syntax.eAnd (Syntax.eLe (Syntax.n 48) (Syntax.v "rc")) (Syntax.eLe (Syntax.v "rc") (Syntax.n 57)))
        [.assign "rv" (Syntax.eOr (.shl (Syntax.v "rv") (Syntax.n 4)) (Syntax.eSub (Syntax.v "rc") (Syntax.n 48)))]
        [.ite (Syntax.eAnd (Syntax.eLe (Syntax.n 97) (Syntax.v "rc")) (Syntax.eLe (Syntax.v "rc") (Syntax.n 102)))
          [.assign "rv" (Syntax.eOr (.shl (Syntax.v "rv") (Syntax.n 4)) (Syntax.eSub (Syntax.v "rc") (Syntax.n 87)))]
          [.assign "rok" (ScanProg.lit 0)]],
      ScanProg.inc "rj"] (I j) (I (j + 1)) := fun j hj => by
    simp only [decide_eq_true_eq] at hj
    have hj16 : j < 16 := by omega
    have hV : digitsFrom 0 (ds.take j) < 2 ^ 60 := by
      have := digitsFrom_lt (ds.take j) 0 0 (by decide)
      rw [List.length_take, Nat.min_eq_left (by omega), Nat.zero_add] at this
      have : 16 ^ j ≤ 16 ^ 15 := Nat.pow_le_pow_right (by decide) (by omega)
      omega
    refine frag_append (xs := [_]) (cls_set o h hl (y := "rc") (by decide)
      (E := .loadByte (.op .add (.var "rq") (.var "rj"))) rfl
      (F := fun u => H j u ∧ u.locals "rv" = some (.ofNat 64 (digitsFrom 0 (ds.take j))) ∧
        u.locals "rok" = some (bw (allDigits (ds.take j))))
      (F' := fun u => H j u ∧ u.locals "rc" = some (.ofNat 64 ds[j].toNat) ∧
        u.locals "rv" = some (.ofNat 64 (digitsFrom 0 (ds.take j))) ∧
        u.locals "rok" = some (bw (allDigits (ds.take j)))) (fun _ _ h => h)
      fun u hu ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4, h5⟩, h6, h7⟩ => ⟨.ofNat 64 ds[j].toNat, by
          simp only [eval, h2, h4]; rw [hdL u hu j hj16]; simp only; rw [Bytes.setWidth8_64],
        ⟨⟨⟨by simp [setL, setLocal, h1], by simp [setL, setLocal, h2]⟩, by simp [setL, setLocal, h3]⟩,
          by simp [setL, setLocal, h4], h5⟩, by simp [setL, setLocal], by simp [setL, setLocal, h6],
          by simp [setL, setLocal, h7]⟩) ?_
    refine frag_append (xs := [_]) (digit_frag o h hl (G := H j) (hHc j) (hHs j) hV) ?_
    have htk : ds.take (j + 1) = ds.take j ++ [ds[j]] := List.take_succ_eq_append_getElem (by omega)
    exact frag_conseq (cls_set o h hl (y := "rj") (by decide)
      (E := .op .add (.var "rj") (.const (.ofNat 64 1))) rfl
      (F' := fun u => H (j + 1) u ∧ u.locals "rv" = some (.ofNat 64 (digitsFrom 0 (ds.take (j + 1)))) ∧
        u.locals "rok" = some (bw (allDigits (ds.take (j + 1))))) (fun _ _ h => h)
      fun u _ ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4, _⟩, _, h7, h8⟩ => ⟨.ofNat 64 (j + 1 + 1), by
          simp only [eval, h4]; rw [BitVec.ofNat_add (j + 1) 1],
        ⟨⟨⟨by simp [setL, setLocal, h1], by simp [setL, setLocal, h2]⟩, by simp [setL, setLocal, h3]⟩,
          by simp [setL, setLocal], by omega⟩,
        by simp only [setL, setLocal]; rw [htk, digitsFrom_snoc]; simpa using h7,
        by simp only [setL, setLocal]; rw [htk, allDigits_snoc]; simpa using h8⟩) (fun _ h => h) fun _ h => h
  refine frag_append (xs := [_]) (frag_count o (c := Syntax.eLt (Syntax.v "rj") (Syntax.n 17))
    (C := .cmp .less (.var "rj") (.const (.ofNat 64 17))) rfl (lowK_any _ (k := .skip) (c := _) rfl) (I := I) hIc
    (fun i => noDecl (P' := I i) _ rfl) (g := fun j => decide (j + 1 < 17))
    (fun j u ⟨_, ⟨_, h4, _⟩, _⟩ => by
      rw [FramerCode.eval_lt (t := u) (a := .var "rj") (b := .const _) (by omega) (by decide) h4 rfl]; rfl)
    hbody 0) ?_
  -- the kind once each is a digit
  have hall : ds.take 16 = ds := List.take_of_length_le (by omega)
  refine frag_conseq (P0 := I 16) ?_ (fun u ⟨j, hI, hg⟩ => by
    have : j = 16 := by have := hI.2.2.2; simp only [decide_eq_false_iff_not] at hg; omega
    subst this; exact hI) fun _ h => h
  refine ScanRun.flagIf_frag o (x := "rok") (lowK_any _ (k := .skip) (c := _) rfl) rfl (b := allDigits ds) hQc
    (fun u hu => by rw [← hall]; exact hu.2.2.2) (fun hb => ?_) fun hb u ⟨hm, ⟨⟨⟨h1, _⟩, _⟩, _⟩, _⟩ => ?_
  · refine set_frag o (E := .var "rlet") rfl hQc fun u ⟨hm, ⟨⟨⟨_, _⟩, h3⟩, _, _⟩, h6, _⟩ => ?_
    refine ⟨_, h3, kept_has hm.kept (h.bound "rk" (by decide)),
      mid_setL hm (by decide) (ScanRun.fresh_of_outside hl (by decide)) _, by simp [setL, setLocal, hpk, hb],
      fun n hn _ => ?_⟩
    simp only [setL, setLocal]; rw [hpn n hn, ← hall]; simpa using h6
  · refine ⟨hm, by rw [hpk, hb]; simpa using h1, fun n hn _ => ?_⟩
    have := hpk; rw [hn, hb] at this
    cases n <;> simp [kindOf] at this

/-! ## A new journal -/

/-- The highest article numbers all zero. -/
def HighZ (A : Word) (u : PancakeState σ) : Prop := ∀ x, x < groupsMax → u.memory (at_ A (rHigh + x * 8)) = 0

theorem highZ_scalar {A : Word} {u : PancakeState σ} (h : HighZ A u) {y : Nat} (hy : y ∈ scalarOffs) (v : Word) :
    HighZ A (stW u A y v) := fun x hx => by
  have hn := nums
  have := (free_scalar y hy).1
  simp only [Free] at this
  rw [stW_word (by omega) (by omega) (by omega)]; exact h x hx

/-- The words a new journal sets before phase 10. -/
def freshSets (synced : Bool) : List (Nat × Nat) :=
  [(rFresh, 1), (rNext, 1), (rJournalEnd, firstFrame), (rI, 0), (rWait, if synced then 1 else 0)]

/-- **A new journal**: phase 10 next, and no group with an article number yet. -/
theorem fresh_frag (o : Oracle σ) {A : Word} {cfg : Config} {J : Bytes} {r : RSt} {s0 : PancakeState σ}
    (h : PBase A s0) (hp : r.phase < 5) {ws : Nat → Word} {os : List (Nat × Word)} {l : List (String × Value)}
    (synced : Bool) :
    Frag o (RecoverProg.fresh synced) (Mid A cfg J r s0 ws os l)
      (fun u => Mid A cfg J r s0 (upd ((freshSets synced).foldl (fun ws p => upd ws p.1 (.ofNat 64 p.2)) ws) rPhase
        (.ofNat 64 10)) os (("rc", .ofNat 64 groupsMax) :: without "rc" l) u ∧ HighZ A u) := by
  have hn := nums
  let ws5 := (freshSets synced).foldl (fun ws p => upd ws p.1 (.ofNat 64 p.2)) ws
  refine frag_append (xs := (freshSets synced).map fun p => rset p.1 (Syntax.n p.2))
    (mid_consts o h (freshSets synced) ws (by cases synced <;> decide)) ?_
  refine frag_append (xs := [_]) (mid_assign o h (y := "rc") (by decide)
    (E := .op .add (.var "jz") (.const (.ofNat 64 0))) rfl (val := .ofNat 64 0)
    fun u hu => by simp [eval, jz_kept h hu.kept]) ?_
  let I (i : Nat) : Assn σ := fun u => Mid A cfg J r s0 ws5 os (("rc", .ofNat 64 i) :: without "rc" l) u ∧
    (∀ x, x < i → u.memory (at_ A (rHigh + x * 8)) = 0) ∧ i ≤ groupsMax
  have hIc : ∀ i, Safe.ClockFree (I i) := fun _ s k ⟨h1, h2⟩ => ⟨mid_clock s k h1, h2⟩
  have hbody : ∀ i, decide (i < groupsMax) = true → Frag o
      [.store (Syntax.eAdd (Syntax.atOff rp rHigh) (Syntax.eMul (Syntax.v "rc") (Syntax.n 8))) (Syntax.n 0),
       ScanProg.inc "rc"] (I i) (I (i + 1)) := fun i hi => by
    simp only [decide_eq_true_eq] at hi
    let M (u : PancakeState σ) : Prop := Mid A cfg J r s0 ws5 os (("rc", .ofNat 64 i) :: without "rc" l) u ∧
      (∀ x, x < i + 1 → u.memory (at_ A (rHigh + x * 8)) = 0)
    have hMc : Safe.ClockFree M := fun s k ⟨h1, h2⟩ => ⟨mid_clock s k h1, h2⟩
    refine frag_append (xs := [_]) (M := M) (store_frag o (D := .op .add (.op .add (.var "rsc")
      (.const (.ofNat 64 rHigh))) (.mul (.var "rc") (.const (.ofNat 64 8)))) (E := .const (.ofNat 64 0)) rfl rfl hMc
      fun u ⟨hu, hz, _⟩ => ⟨at_ A (rHigh + i * 8), 0, ?_, rfl, ?_, mid_high h hp hu hi 0, fun x hx => ?_⟩) ?_
    · have hrc : u.locals "rc" = some (.ofNat 64 i) := ScanRun.vals_lookup hu.vals (by simp)
      simp only [eval, rsc_kept h hu.kept, hrc]
      rw [← BitVec.ofNat_mul, BitVec.add_assoc, ← BitVec.ofNat_add]; rfl
    · have := h.dom (rHigh + i * 8) (by omega)
      rw [hu.kept.memaddrs]; simp only [at_] at this ⊢
      rwa [byteAlign_of_aligned h.hA (X := rHigh + i * 8) (by omega)] at this
    · show (stW u A (rHigh + i * 8) 0).memory (at_ A (rHigh + x * 8)) = 0
      by_cases e : x = i
      · subst e; simp [stW]
      · rw [stW_word (by omega) (by omega) (by omega)]; exact hz x (by omega)
    · refine frag_conseq (mid_assign_and o h (y := "rc") (by decide)
        (E := .op .add (.var "rc") (.const (.ofNat 64 1))) rfl (val := .ofNat 64 (i + 1)) (fun u hu => by
          have hrc : u.locals "rc" = some (.ofNat 64 i) := ScanRun.vals_lookup hu.vals (by simp)
          simp only [eval, hrc]; rw [BitVec.ofNat_add]) (F := fun u => ∀ x, x < i + 1 →
            u.memory (at_ A (rHigh + x * 8)) = 0) (fun _ _ h => h) fun _ h => h)
        (fun u hu => hu) fun u ⟨hu, hz⟩ => ⟨mid_vals hu fun q hq => ?_, hz, by omega⟩
      rw [without_cons_self]; exact hq
  refine frag_append (xs := [_]) (M := fun u => ∃ i, I i u ∧ decide (i < groupsMax) = false)
    (frag_conseq (frag_count o (c := Syntax.eLt (Syntax.v "rc") (Syntax.n groupsMax))
      (C := .cmp .less (.var "rc") (.const (.ofNat 64 groupsMax))) rfl (lowK_any _ (k := .skip) (c := _) rfl) hIc
      (fun i => noDecl (P' := I i) _ rfl) (g := fun i => decide (i < groupsMax))
      (fun i u ⟨hu, _, _⟩ => by
        rw [FramerCode.eval_lt (t := u) (a := .var "rc") (b := .const _) (x := i) (y := groupsMax) (by omega)
          (by decide) (ScanRun.vals_lookup hu.vals (by simp)) rfl]; rfl) hbody 0)
      (fun u hu => ⟨hu, fun _ h => absurd h (Nat.not_lt_zero _), Nat.zero_le _⟩) fun _ h => h) ?_
  refine frag_conseq (P0 := fun u => Mid A cfg J r s0 ws5 os (("rc", .ofNat 64 groupsMax) :: without "rc" l) u ∧
    HighZ A u) ?_ (fun u ⟨i, ⟨hu, hz, hi⟩, hg⟩ => by
      have : i = groupsMax := by simp only [decide_eq_false_iff_not] at hg; omega
      subst this; exact ⟨hu, hz⟩) fun _ h => h
  exact mid_set_and o h (x := rPhase) (by decide) (E := .const (.ofNat 64 10)) rfl (fun _ _ _ => rfl)
    (fun _ _ h => h) fun u v hz => highZ_scalar hz (by decide) v

/-! ## Phase 1 -/

/-- **`raise`**: `rm` the higher of it and `rv`, as numbers below `2 ^ 64`. -/
theorem raise_frag (o : Oracle σ) {A : Word} {cfg : Config} {J : Bytes} {r : RSt} {s0 : PancakeState σ}
    {ws : Nat → Word} {os : List (Nat × Word)} {l : List (String × Value)}
    (hl : ScanRun.Fresh "rm" l = true) {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) {F : Assn σ}
    (hFc : Safe.ClockFree F) (hF : ∀ u v, F u → F (setL u "rm" v)) :
    Frag o [RecoverProg.raise "rm" (Syntax.v "rv")]
      (fun u => Mid A cfg J r s0 ws os l u ∧ F u ∧ u.locals "rm" = some (.ofNat 64 a) ∧
        u.locals "rv" = some (.ofNat 64 b))
      (fun u => Mid A cfg J r s0 ws os l u ∧ F u ∧ u.locals "rm" = some (.ofNat 64 (max a b)) ∧
        u.locals "rv" = some (.ofNat 64 b)) := by
  have hQc : Safe.ClockFree (fun u => Mid A cfg J r s0 ws os l u ∧ F u ∧
      u.locals "rm" = some (.ofNat 64 (max a b)) ∧ u.locals "rv" = some (.ofNat 64 b)) :=
    fun s k ⟨h1, h2, h3⟩ => ⟨mid_clock s k h1, hFc s k h2, h3⟩
  refine frag_if o (C := .cmp .less (.op .xor (.var "rm") (.const (.ofNat 64 top)))
    (.op .xor (.var "rv") (.const (.ofNat 64 top)))) rfl (lowK_any _ (k := .skip) (c := _) rfl) (fun k => ⟨k, rfl⟩)
    rfl rfl hQc (b := decide (a < b)) (fun u ⟨_, _, hm, hv⟩ => ult_eval ha hb hm hv) (fun hlt => ?_) fun hge => ?_
  · refine set_frag o (E := .var "rv") rfl hQc fun u ⟨hm, hf, hrm, hrv⟩ => ⟨_, hrv, ⟨_, hrm⟩,
      mid_setL hm (by decide) hl _, hF u _ hf, ?_, by simp [setL, setLocal, hrv]⟩
    simp only [decide_eq_true_eq] at hlt
    simp [setL, setLocal, Nat.max_eq_right (Nat.le_of_lt hlt)]
  · exact frag_nil o fun u ⟨hm, hf, hrm, hrv⟩ => ⟨hm, hf, by
      simp only [decide_eq_false_iff_not, Nat.not_lt] at hge; rw [Nat.max_eq_left hge]; exact hrm, hrv⟩

/-- A number a name of the store's carries is below `2 ^ 64`. -/
theorem num_lt {b : Bytes} {n : Name} (h : parseName b = some n) : numOf n < 2 ^ 64 := by
  by_cases hl : b.length = 17
  · obtain ⟨c, ds, rfl⟩ : ∃ c ds, b = c :: ds := by
      cases b with
      | nil => cases hl
      | cons c ds => exact ⟨c, ds, rfl⟩
    have hds : ds.length = 16 := by simpa using hl
    rw [(parse_17 (c := c) hds).2 n h]
    have := digitsFrom_lt ds 0 0 (by decide)
    rw [hds] at this; simpa using this
  · by_cases hj : b = journalName
    · subst hj
      have : parseName journalName = some .journal := by unfold parseName; simp
      rw [this] at h; cases h; simp [numOf]
    · rw [parse_other hj hl] at h; cases h

/-- The words a name of the first pass sets besides how many there are. -/
def namedWs (r : RSt) (ws : Nat → Word) : Name → Nat → Word
  | .journal => upd ws rJournal (.ofNat 64 1)
  | .final s | .temp s | .quarantine s => upd ws rMaxSeq (.ofNat 64 (max r.maxSeq s))
  | .tail s => upd (upd (upd ws rMaxSeq (.ofNat 64 (max r.maxSeq s))) rTails (.ofNat 64 1)) rMaxTail
      (.ofNat 64 (max r.maxTail s))

theorem kind_le (n : Option Name) : kindOf n ≤ 5 := by
  cases n with
  | none => decide
  | some n => cases n <;> simp [kindOf]

/-- **A name of the first pass**: counted, its number noted, the next name asked for. -/
theorem named_frag (o : Oracle σ) {A : Word} {cfg : Config} {J : Bytes} {r : RSt} {s0 : PancakeState σ}
    (h : PBase A s0) {n : Name} (hpn : parseName r.name = some n) (hms : r.maxSeq < 2 ^ 64)
    (hmt : r.maxTail < 2 ^ 64) :
    Frag o ([rset rNames (Syntax.eAdd (rw rNames) (Syntax.n 1)),
      .ite (Syntax.eEq (Syntax.v "rk") (Syntax.n 1)) [rset rJournal (Syntax.n 1)]
        [.assign "rm" (rw rMaxSeq), RecoverProg.raise "rm" (Syntax.v "rv"), rset rMaxSeq (Syntax.v "rm"),
         .ite (Syntax.eEq (Syntax.v "rk") (Syntax.n 5))
           [rset rTails (Syntax.n 1), .assign "rm" (rw rMaxTail), RecoverProg.raise "rm" (Syntax.v "rv"),
            rset rMaxTail (Syntax.v "rm")] []],
      rset rFirst (Syntax.n 0)] ++ stop asksName)
      (fun u => Mid A cfg J r s0 (scalars cfg r) [] [("rgo", 1)] u ∧
        u.locals "rk" = some (.ofNat 64 (kindOf (some n))) ∧
        (n ≠ .journal → u.locals "rv" = some (.ofNat 64 (numOf n))))
      (POut A cfg J s0 ({ RecoverSpec.firstName { r with names := r.names + 1 } n with first := false },
        some .askName)) := by
  have hs : numOf n < 2 ^ 64 := num_lt hpn
  have hk := kind_le (some n)
  let F0 : Assn σ := fun u => u.locals "rk" = some (.ofNat 64 (kindOf (some n))) ∧
    (n ≠ .journal → u.locals "rv" = some (.ofNat 64 (numOf n)))
  have hF0c : Safe.ClockFree F0 := fun _ _ h => h
  let ws1 := upd (scalars cfg r) rNames (.ofNat 64 (r.names + 1))
  refine frag_append (xs := [_]) (mid_set_and o h (x := rNames) (by decide)
    (E := .op .add (rwE rNames) (.const (.ofNat 64 1))) rfl (val := .ofNat 64 (r.names + 1))
    (fun u hu _ => by
      simp only [eval, mid_rw h hu (x := rNames) (by decide) (E := rwE rNames) rfl]
      rw [show scalars cfg r rNames = .ofNat 64 r.names from rfl, BitVec.ofNat_add]) hF0c
    (fun _ _ h => h)) ?_
  let Q1 : Assn σ := fun u => Mid A cfg J r s0 (namedWs r ws1 n) [] [("rgo", 1)] u ∧ F0 u
  have hQ1c : Safe.ClockFree Q1 := fun s k ⟨h1, h2⟩ => ⟨mid_clock s k h1, h2⟩
  refine frag_append (xs := [_]) (M := Q1) (frag_if o (C := .cmp .equal (.var "rk") (.const (.ofNat 64 1))) rfl
    (lowK_any _ (k := .skip) (c := _) rfl) (lowK_any _ (k := .skip) (c := _) rfl) rfl rfl hQ1c
    (b := decide (kindOf (some n) = 1))
    (fun u ⟨_, hrk, _⟩ => FramerCode.eval_eq (t := u) (a := .var "rk") (b := .const _) (by omega) (by decide) hrk rfl)
    (fun hb => ?_) fun hb => ?_) ?_
  · -- the journal
    have hj : n = .journal := by
      simp only [decide_eq_true_eq] at hb; cases n <;> simp_all [kindOf]
    subst hj
    exact mid_set_and o h (x := rJournal) (by decide) (E := .const (.ofNat 64 1)) rfl (fun _ _ _ => rfl) hF0c
      fun _ _ h => h
  · -- a file's: the highest number, a tail's too
    have hj : n ≠ .journal := fun e => by subst e; simp [kindOf] at hb
    let F1 (m : Nat) : Assn σ := fun u => F0 u ∧ u.locals "rm" = some (.ofNat 64 m) ∧
      u.locals "rv" = some (.ofNat 64 (numOf n))
    have hF1c : ∀ m, Safe.ClockFree (F1 m) := fun _ _ _ h => h
    have hrm : ∀ (x : Nat) (ws : Nat → Word) (m : Nat), x ∈ scalarOffs → ws x = .ofNat 64 m →
        Frag o [.assign "rm" (rw x)] (fun u => Mid A cfg J r s0 ws [] [("rgo", 1)] u ∧ F0 u)
          (fun u => Mid A cfg J r s0 ws [] [("rgo", 1)] u ∧ F1 m u) := fun x ws m hx hm =>
      mid_put o h (y := "rm") (by decide) (by decide) (rw_lower hx) (hF1c _) fun u hu hf0 => ⟨_,
        mid_rw h hu hx (rw_lower hx), ⟨by simp [setL, setLocal, hf0.1], fun e => by simp [setL, setLocal, hf0.2 e]⟩,
        by simp [setL, setLocal, hm], by simp [setL, setLocal, hf0.2 hj]⟩
    have hF0m : ∀ u v, F0 u → F0 (setL u "rm" v) := fun u v hf0 =>
      ⟨by simp [setL, setLocal, hf0.1], fun e => by simp [setL, setLocal, hf0.2 e]⟩
    let wsM := upd ws1 rMaxSeq (.ofNat 64 (max r.maxSeq (numOf n)))
    let wsT := upd (upd wsM rTails (.ofNat 64 1)) rMaxTail (.ofNat 64 (max r.maxTail (numOf n)))
    have hnw : namedWs r ws1 n = if kindOf (some n) = 5 then wsT else wsM := by
      cases n with
      | journal => exact absurd rfl hj
      | tail s => rfl
      | _ s => rfl
    refine frag_conseq (P0' := fun u => Mid A cfg J r s0 (if kindOf (some n) = 5 then wsT else wsM) [] [("rgo", 1)] u ∧
      F0 u) ?_ (fun _ h => h) fun u ⟨hu, hf⟩ => ⟨by rw [hnw]; exact hu, hf⟩
    refine frag_append (xs := [_]) (hrm rMaxSeq ws1 r.maxSeq (by decide) rfl) ?_
    refine frag_append (xs := [_]) (raise_frag o (by decide) hms hs (F := F0) hF0c hF0m) ?_
    refine frag_append (xs := [_]) (mid_set_and o h (x := rMaxSeq) (by decide) (E := .var "rm") rfl
      (val := .ofNat 64 (max r.maxSeq (numOf n))) (F := F1 (max r.maxSeq (numOf n))) (fun _ _ hf => hf.2.1)
      (hF1c _) fun _ _ h => h) ?_
    let Q2 : Assn σ := fun u => Mid A cfg J r s0 (if kindOf (some n) = 5 then wsT else wsM) [] [("rgo", 1)] u ∧ F0 u
    have hQ2c : Safe.ClockFree Q2 := fun s k ⟨h1, h2⟩ => ⟨mid_clock s k h1, h2⟩
    refine frag_conseq (frag_if o (C := .cmp .equal (.var "rk") (.const (.ofNat 64 5))) rfl
      (lowK_any _ (k := .skip) (c := _) rfl) (fun k => ⟨k, rfl⟩) rfl rfl hQ2c (b := decide (kindOf (some n) = 5))
      (fun u ⟨_, hrk, _⟩ => FramerCode.eval_eq (t := u) (a := .var "rk") (b := .const _) (by omega) (by decide)
        hrk.1 rfl) (fun h5 => ?_) fun h5 => ?_) (fun _ h => h) fun _ h => h
    · simp only [decide_eq_true_eq] at h5
      refine frag_conseq (P0' := fun u => Mid A cfg J r s0 wsT [] [("rgo", 1)] u ∧ F0 u) ?_ (fun _ h => h)
        fun u ⟨hu, hf⟩ => ⟨by rw [if_pos h5]; exact hu, hf⟩
      refine frag_append (xs := [_]) (mid_set_and o h (x := rTails) (by decide) (E := .const (.ofNat 64 1)) rfl
        (fun _ _ _ => rfl) (hF1c _) fun _ _ h => h) ?_
      refine frag_append (xs := [_]) (frag_conseq (hrm rMaxTail _ r.maxTail (by decide) rfl)
        (fun u ⟨hu, hf⟩ => ⟨hu, hf.1⟩) fun _ h => h) ?_
      refine frag_append (xs := [_]) (raise_frag o (by decide) hmt hs (F := F0) hF0c hF0m) ?_
      exact frag_conseq (mid_set_and o h (x := rMaxTail) (by decide) (E := .var "rm") rfl
        (val := .ofNat 64 (max r.maxTail (numOf n))) (F := F1 (max r.maxTail (numOf n))) (fun _ _ hf => hf.2.1)
        (hF1c _) fun _ _ h => h) (fun _ h => h) fun u ⟨hu, hf⟩ => ⟨hu, hf.1⟩
    · simp only [decide_eq_false_iff_not] at h5
      exact frag_nil o fun u ⟨hu, hf⟩ => ⟨by rw [if_neg h5]; exact hu, hf.1⟩
  -- the name counted, the next asked for
  refine frag_append (xs := [_]) (mid_set_and o h (x := rFirst) (by decide) (E := .const (.ofNat 64 0)) rfl
    (fun _ _ _ => rfl) hF0c fun _ _ h => h) ?_
  refine frag_conseq (stop_frag o h asksName (fun _ h => by simp at h)) (fun u hu => hu.1) fun u hu => ?_
  refine mid_end hu ?_ ?_ ⟨vals_lookup hu.vals rfl, outs_lookup hu.outs rfl⟩
  · cases n <;> exact offs_all (by and_intros <;> rfl)
  · cases n <;> exact fun hr => { hr with }

/-- **Phase 1**: a name of the first pass, or none left. -/
theorem firstPass_frag (o : Oracle σ) {A : Word} {cfg : Config} {J : Bytes} {r : RSt} {s0 : PancakeState σ}
    (h : PIn A cfg J r s0) (hp : r.phase = 1) (hnm : r.names < 2 ^ 64) (hms : r.maxSeq < 2 ^ 64)
    (hmt : r.maxTail < 2 ^ 64) :
    Frag o RecoverProg.firstPass (Like s0) (POut A cfg J s0 (RecoverSpec.firstPass r)) := by
  have hb := h.toPBase
  refine frag_conseq (P0 := Mid A cfg J r s0 (scalars cfg r) [] [("rgo", 1)]) ?_ (fun u hu => mid_start h hu)
    fun _ h => h
  rw [RecoverSpec.firstPass]
  refine frag_if o (C := rwE rEnd) (rw_lower (by decide)) (lowK_any _ (k := .skip) (c := _) rfl)
    (lowK_any _ (k := .skip) (c := _) rfl) rfl rfl pout_clock (b := r.ended)
    (fun u hu => mid_rw hb hu (by decide) (rw_lower (by decide))) (fun hE => ?_) fun hE => ?_
  · rw [if_pos hE]
    refine frag_if o (C := rwE rJournal) (rw_lower (by decide)) (lowK_any _ (k := .skip) (c := _) rfl)
      (lowK_any _ (k := .skip) (c := _) rfl) rfl rfl pout_clock (b := r.journal)
      (fun u hu => mid_rw hb hu (by decide) (rw_lower (by decide))) (fun hJ => ?_) fun hJ => ?_
    · -- the journal among the names
      rw [if_pos hJ]
      refine frag_append (xs := [_]) (mid_set o hb (x := rPhase) (by decide) (E := .const (.ofNat 64 2)) rfl
        fun _ _ => rfl) ?_
      refine frag_conseq (stop_frag o hb asksJournal (fun _ h => by simp at h)) (fun _ h => h) fun u hu =>
        mid_end hu (offs_all (by and_intros <;> rfl))
        (fun hr => ⟨fun h9 => by simp at h9, hr.nameLen, hr.name, hr.unknown, hr.config, fun h3 => by simp at h3,
          hr.slots, fun h5 => by simp at h5⟩) ⟨vals_lookup hu.vals rfl, outs_lookup hu.outs rfl⟩
    · rw [if_neg (by simp [hJ])]
      refine frag_if o (C := .cmp .equal (rwE rNames) (.const (.ofNat 64 0))) rfl
        (lowK_any _ (k := .skip) (c := _) rfl) (lowK_any _ (k := .skip) (c := _) rfl) rfl rfl pout_clock
        (b := decide (r.names = 0)) (fun u hu => FramerCode.eval_eq (t := u) (x := r.names) (y := 0) hnm (by decide)
          (mid_rw hb hu (by decide) (rw_lower (by decide))) rfl) (fun h0 => ?_) fun h0 => ?_
      · -- no file at all: a new store
        rw [if_pos (of_decide_eq_true h0)]
        refine frag_conseq (fresh_frag o hb (by omega) true) (fun _ h => h) fun u ⟨hu, hz⟩ =>
          mid_end hu (offs_all (by and_intros <;> rfl)) (fun hr => ⟨fun h9 => by simp [RecoverSpec.startNew] at h9,
            hr.nameLen, hr.name, hr.unknown, hr.config, fun _ hf => by simp [RecoverSpec.startNew] at hf, hr.slots,
            fun _ x hx => by simpa [RecoverSpec.startNew, highOf] using hz x hx⟩) (vals_lookup hu.vals rfl)
      · rw [if_neg (by simpa using h0)]
        refine frag_append (xs := [_]) (mid_out o hb (x := rFault) (by decide) (fun _ h => by simp at h)
          (E := .const (.ofNat 64 (faultCode .noJournal))) rfl fun _ _ => rfl) ?_
        exact frag_conseq (stop_frag o hb refused (by decide)) (fun _ h => h) fun u hu =>
          mid_end hu (offs_all (by and_intros <;> rfl))
          (fun hr => { hr with }) ⟨vals_lookup hu.vals rfl, outs_lookup hu.outs rfl, outs_lookup hu.outs rfl, trivial⟩
  · -- a name
    rw [if_neg (by simp [hE])]
    refine frag_append (xs := RecoverProg.classify) (classify_frag o hb h.area.rest.nameLen (by decide) rfl) ?_
    cases hq : parseName r.name with
    | none =>
      refine frag_if o (C := .cmp .equal (.var "rk") (.const (.ofNat 64 0))) rfl
        (lowK_any _ (k := .skip) (c := _) rfl) (lowK_any _ (k := .skip) (c := _) rfl) rfl rfl pout_clock
        (b := true) (fun u ⟨_, hrk, _⟩ => by
          rw [FramerCode.eval_eq (t := u) (a := .var "rk") (b := .const _) (x := kindOf none) (y := 0) (by decide)
            (by decide) hrk rfl]; rfl)
        (fun _ => ?_) fun e => absurd e (by decide)
      refine frag_append (xs := [_]) (frag_conseq (mid_out o hb (x := rFault) (by decide) (fun _ h => by simp at h)
        (E := .const (.ofNat 64 (faultCode (.badName [])))) rfl fun _ _ => rfl) (fun u hu => hu.1) fun _ h => h) ?_
      exact frag_conseq (stop_frag o hb refused (by decide)) (fun _ h => h) fun u hu =>
        mid_end hu (offs_all (by and_intros <;> rfl))
        (fun hr => { hr with }) ⟨vals_lookup hu.vals rfl, outs_lookup hu.outs rfl, outs_lookup hu.outs rfl, rfl⟩
    | some n =>
      have hk0 : kindOf (some n) ≠ 0 := by cases n <;> simp [kindOf]
      refine frag_if o (C := .cmp .equal (.var "rk") (.const (.ofNat 64 0))) rfl
        (lowK_any _ (k := .skip) (c := _) rfl) (lowK_any _ (k := .skip) (c := _) rfl) rfl rfl pout_clock
        (b := false) (fun u ⟨_, hrk, _⟩ => by
          rw [FramerCode.eval_eq (t := u) (a := .var "rk") (b := .const _) (x := kindOf (some n)) (y := 0)
            (Nat.lt_of_le_of_lt (kind_le _) (by decide)) (by decide) hrk rfl]
          simp [hk0]) (fun e => absurd e (by decide)) fun _ => ?_
      exact frag_conseq (named_frag o hb hq hms hmt) (fun u ⟨hu, hrk, hrv⟩ => ⟨hu, hrk, fun hj => hrv n rfl hj⟩)
        fun _ h => h

/-! ## Phase 2 -/

/-- **Phase 2**: the scanner set to read the journal, of the length the caller gave. -/
theorem journalGiven_frag (o : Oracle σ) {A : Word} {cfg : Config} {J : Bytes} {r : RSt} {s0 : PancakeState σ}
    (h : PIn A cfg J r s0) (hp : r.phase = 2) (hj : r.jsize = J.length) :
    Frag o RecoverProg.journalGiven (Like s0) (POut A cfg J s0 (RecoverSpec.journalGiven r)) := by
  have hb := h.toPBase
  have hn := nums
  have hp3 : r.phase < 3 := by omega
  let M := Mid A cfg J r s0 (scalars cfg r) [] [("rgo", 1)]
  have step : ∀ (qs : List (Nat × Word)) (x : Nat) (e : Syntax.PExpr) (E : PancakeExp) (val : Word), x % 8 = 0 →
      x < ScanProg.size → Lower.lowerExp e = some E → (∀ u, M u → eval u E = some val) →
      (∀ k ∈ qs.map Prod.fst, k ≠ rScan + x ∧ k < 2 ^ 64) →
      Frag o [RecoverProg.sset x e] (fun u => M u ∧ Outs A qs u) (fun u => M u ∧ Outs A ((rScan + x, val) :: qs) u) :=
    fun qs x e E val hx hxs he hv hq => mid_sset o hb hp3 hx hxs (fun _ h => by simp at h) he (fun _ _ h => h)
      (fun u hu _ => hv u hu)
      fun u _ hf => outs_stW hf (by omega) hq val
  refine frag_conseq (P0 := fun u => M u ∧ Outs A [] u) ?_ (fun u hu => ⟨mid_start h hu, fun _ h => nomatch h⟩)
    fun _ h => h
  refine frag_append (xs := [_]) (step [] ScanProg.sSize _ (rwE rJournalSize) (.ofNat 64 r.jsize) (by decide)
    (by decide) (rw_lower (by decide)) (fun u hu => mid_rw hb hu (by decide) (rw_lower (by decide)))
    (by decide)) ?_
  refine frag_append (xs := [_]) (step _ ScanProg.sBase _ (.const (.ofNat 64 0)) (.ofNat 64 0) (by decide)
    (by decide) rfl (fun _ _ => rfl) (by simp only [List.map]; decide)) ?_
  refine frag_append (xs := [_]) (step _ ScanProg.sLen _ (.const (.ofNat 64 0)) (.ofNat 64 0) (by decide)
    (by decide) rfl (fun _ _ => rfl) (by simp only [List.map]; decide)) ?_
  refine frag_append (xs := [_]) (step _ ScanProg.sPos _ (.const (.ofNat 64 0)) (.ofNat 64 0) (by decide)
    (by decide) rfl (fun _ _ => rfl) (by simp only [List.map]; decide)) ?_
  refine frag_append (xs := [_]) (step _ ScanProg.sKeyed _ (.const (.ofNat 64 0)) (.ofNat 64 0) (by decide)
    (by decide) rfl (fun _ _ => rfl) (by simp only [List.map]; decide)) ?_
  refine frag_append (xs := [_]) (step _ ScanProg.sCount _ (.const (.ofNat 64 0)) (.ofNat 64 0) (by decide)
    (by decide) rfl (fun _ _ => rfl) (by simp only [List.map]; decide)) ?_
  refine frag_conseq (mid_set_and o hb (x := rPhase) (by decide) (E := .const (.ofNat 64 3)) rfl (fun _ _ _ => rfl)
    (fun _ _ h => h) ?_) (fun _ h => h) fun u ⟨hu, hf⟩ => ?_
  · exact fun u v hf => outs_keep hf (by decide) (by simp only [List.map]; decide) v
  refine mid_end hu (offs_all (by and_intros <;> rfl)) (fun hr => ⟨fun h9 => by simp at h9,
    hr.nameLen, hr.name, hr.unknown, hr.config, fun _ _ => ⟨?_, ScanRun.valid_start J⟩, hr.slots,
    fun h5 => by simp at h5⟩) (vals_lookup hu.vals rfl)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, fun i hi => absurd hi (Nat.not_lt_zero _), fun k hk => nomatch hk⟩ <;>
    rw [at_at]
  · rw [outs_lookup hf rfl, hj]
  all_goals exact outs_lookup hf rfl

/-- The words phase 0 sets. -/
def beginSets : List (Nat × Nat) :=
  [(rNames, 0), (rJournal, 0), (rMaxSeq, 0), (rTails, 0), (rMaxTail, 0), (rCommits, 0), (rRecords, 0), (rUnknown, 0),
   (rTorn, 0), (rFresh, 0), (rTidied, 0), (rWait, 0), (rFirst, 1), (rPhase, 1)]

/-- **Phase 0**, the first name asked for. -/
theorem begin_frag (o : Oracle σ) {A : Word} {cfg : Config} {J : Bytes} {r : RSt} {s0 : PancakeState σ}
    (h : PIn A cfg J r s0) : Frag o RecoverProg.begin (Like s0) (POut A cfg J s0 (RecoverSpec.begin r)) := by
  have hb := h.toPBase
  refine frag_conseq (P0 := Mid A cfg J r s0 (scalars cfg r) [] [("rgo", 1)]) ?_ (fun u hu => mid_start h hu)
    fun _ h => h
  refine frag_append (xs := beginSets.map fun p => rset p.1 (Syntax.n p.2))
    (mid_consts o hb beginSets (scalars cfg r) (by decide)) ?_
  refine frag_conseq (stop_frag o hb asksName (fun _ h => by simp at h)) (fun _ h => h) fun u hu => ?_
  refine mid_end hu (offs_all (by and_intros <;> rfl)) (fun hr => ?_) ⟨vals_lookup hu.vals rfl, outs_lookup hu.outs rfl⟩
  exact ⟨fun hp => by simp at hp, hr.nameLen, hr.name, fun g hg => by
    simp at hg, hr.config, fun h3 => by simp at h3,
    fun i hi => by simp at hi, fun h5 => by simp at h5⟩

end DN.News.RecoverArea
