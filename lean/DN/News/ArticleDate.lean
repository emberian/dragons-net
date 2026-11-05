-- SPDX-License-Identifier: AGPL-3.0-or-later
import DN.News.ArticleCal

/-!
# DN.News.ArticleDate

`artDate`'s reading of a date-time, modelled byte by byte and shown to agree with `DN.News.ArticleSpec.dateValue`.
The time and the zone are one loop over the bytes past the year (`tzStep`).
-/

namespace DN.News.ArticleDate

open DN.News.ArticleSpec (Bytes number? COLON PLUS MINUS named)
open DN.News.CommandSpec (isDigit value)

/-! ## The time and the zone -/

/-- `artDate`'s state in its loop over the time and the zone. -/
structure TZ where
  ph : Nat
  np : Nat
  cv : Nat
  cd : Nat
  hh : Nat
  mi : Nat
  se : Nat
  bad : Nat
  zl : Nat
  z0 : Nat
  zd : Nat
  zv : Nat
  zg : Nat

/-- The state before the loop. -/
def tz0 : TZ := ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩

/-- A part of the time ended: its number kept, a flag if it had no digit. -/
def tzFinish (t : TZ) : TZ :=
  { t with
    bad := if t.cd = 0 then 1 else t.bad, hh := if t.np = 0 then t.cv else t.hh
    mi := if t.np = 1 then t.cv else t.mi, se := if t.np = 2 then t.cv else t.se, np := t.np + 1, cv := 0, cd := 0 }

/-- Whether a byte is a digit, as a number. -/
def dig (b : Nat) : Prop := 48 ≤ b ∧ b ≤ 57

instance (b : Nat) : Decidable (dig b) := inferInstanceAs (Decidable (_ ∧ _))

/-- The zone's part of the loop's state. Its length and first byte; whether the next four are digits, and their number;
whether it starts as `GMT`. -/
structure ZF where
  zl : Nat
  z0 : Nat
  zd : Nat
  zv : Nat
  zg : Nat

/-- The zone's fields of the loop's state. -/
def zfOf (t : TZ) : ZF := ⟨t.zl, t.z0, t.zd, t.zv, t.zg⟩

/-- The loop's state with the zone's fields `z`. -/
def withZ (t : TZ) (z : ZF) : TZ := { t with zl := z.zl, z0 := z.z0, zd := z.zd, zv := z.zv, zg := z.zg }

/-- The time's fields of the loop's state. -/
def tfOf (t : TZ) : Nat × Nat × Nat × Nat × Nat := (t.np, t.hh, t.mi, t.se, t.bad)

/-- The zone's first byte kept. -/
def zFirst (z : ZF) (b : Nat) : ZF := if z.zl = 0 then { z with z0 := b } else z

/-- The flag of `GMT` cleared at a letter that differs. -/
def zGmt (z : ZF) (b : Nat) : ZF :=
  if (z.zl = 0 ∧ ArticleRun.lowN b ≠ 103) ∨ (z.zl = 1 ∧ ArticleRun.lowN b ≠ 109) ∨
      (z.zl = 2 ∧ ArticleRun.lowN b ≠ 116) then { z with zg := 0 } else z

/-- A digit taken into the zone's number, or the flag of digits cleared. -/
def zDig (z : ZF) (b : Nat) : ZF := if dig b then { z with zv := z.zv * 10 + (b - 48) } else { z with zd := 0 }

/-- The zone's bytes 1 to 4 read as digits. -/
def zNum (z : ZF) (b : Nat) : ZF := if 1 ≤ z.zl ∧ z.zl ≤ 4 then zDig z b else z

/-- One byte of the zone. -/
def zStep (z : ZF) (b : Nat) : ZF :=
  let z4 := zNum (zGmt (zFirst z b) b) b
  { z4 with zl := z4.zl + 1 }

/-- One byte of the time or the zone, white space and line ends left out. -/
def tzStep (t : TZ) (b : Nat) : TZ :=
  if t.ph = 0 ∧ (dig b ∨ b = 58) then
    if b = 58 then tzFinish t else { t with cv := min 1000 (t.cv * 10 + (b - 48)), cd := t.cd + 1 }
  else
    let t1 := if t.ph = 0 then { tzFinish t with ph := 1 } else t
    withZ t1 (zStep (zfOf t1) b)

/-- A part of the time as `artDate` keeps it: its number, at most 1000. -/
def tPart (p : Bytes) : Nat := min 1000 (value p)

/-- The `i`-th part's number, or 0. -/
def tAt (D : List Bytes) (i : Nat) : Nat := (D[i]?.map tPart).getD 0

/-- What the loop keeps over the time: the parts ended `D`, and the one going on, reversed in `acc`. -/
def TInv (t : TZ) (D : List Bytes) (acc : Bytes) : Prop :=
  t.ph = 0 ∧ t.np = D.length ∧ t.bad ≤ 1 ∧ (t.bad = 0 ↔ ∀ d ∈ D, d ≠ []) ∧ t.cd = acc.length ∧
    t.cv = tPart acc.reverse ∧ t.hh = tAt D 0 ∧ t.mi = tAt D 1 ∧ t.se = tAt D 2 ∧
    t.zl = 0 ∧ t.z0 = 0 ∧ t.zd = 1 ∧ t.zv = 0 ∧ t.zg = 1

theorem tInv0 : TInv tz0 [] [] := by
  exact ⟨rfl, rfl, by decide, Iff.intro (fun _ d h => nomatch h) (fun _ => rfl), rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    rfl, rfl, rfl⟩

theorem tAt_fin (D : List Bytes) (p : Bytes) (i : Nat) :
    (if D.length = i then tPart p else tAt D i) = tAt (D ++ [p]) i := by
  unfold tAt
  by_cases h : D.length = i
  · subst h; rw [if_pos rfl]; simp
  · rw [if_neg h]
    by_cases h2 : i < D.length
    · rw [List.getElem?_append_left h2]
    · rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by simp; omega)]

theorem tInv_finish {t : TZ} {D : List Bytes} {acc : Bytes} (h : TInv t D acc) :
    TInv (tzFinish t) (D ++ [acc.reverse]) [] := by
  obtain ⟨hph, hnp, hb1, hbad, hcd, hcv, hhh, hmi, hse, hzl, hz0, hzd, hzv, hzg⟩ := h
  unfold tzFinish
  refine ⟨hph, by simp [hnp], ?_, ?_, rfl, rfl, ?_, ?_, ?_, hzl, hz0, hzd, hzv, hzg⟩
  · dsimp only; split <;> omega
  · dsimp only
    simp only [List.mem_append, List.mem_singleton]
    constructor
    · intro h0 d hd
      split at h0
      · omega
      · rename_i hc
        rcases hd with hd | rfl
        · exact hbad.1 h0 d hd
        · intro e; apply hc; rw [hcd]; simpa using e
    · intro hall
      have ha : acc ≠ [] := fun e => hall _ (.inr rfl) (by rw [e]; rfl)
      rw [if_neg (by rw [hcd]; simpa using ha)]
      exact hbad.2 fun d hd => hall d (.inl hd)
  · show (if t.np = 0 then t.cv else t.hh) = _; rw [hnp, hcv, hhh]; exact tAt_fin D _ 0
  · show (if t.np = 1 then t.cv else t.mi) = _; rw [hnp, hcv, hmi]; exact tAt_fin D _ 1
  · show (if t.np = 2 then t.cv else t.se) = _; rw [hnp, hcv, hse]; exact tAt_fin D _ 2

theorem tInv_digit {t : TZ} {D : List Bytes} {acc : Bytes} (h : TInv t D acc) {b : BitVec 8} (hd : dig b.toNat)
    (hc : b.toNat ≠ 58) : TInv (tzStep t b.toNat) D (b :: acc) := by
  obtain ⟨hph, hnp, hb1, hbad, hcd, hcv, hhh, hmi, hse, hzl, hz0, hzd, hzv, hzg⟩ := h
  unfold tzStep
  rw [if_pos ⟨hph, .inl hd⟩, if_neg hc]
  refine ⟨hph, hnp, hb1, hbad, by simp [hcd], ?_, hhh, hmi, hse, hzl, hz0, hzd, hzv, hzg⟩
  show min 1000 (t.cv * 10 + (b.toNat - 48)) = tPart (b :: acc).reverse
  rw [hcv, List.reverse_cons]
  unfold tPart
  rw [ArticleScan.value_snoc, ArticleScan.min_step]

theorem tInv_colon {t : TZ} {D : List Bytes} {acc : Bytes} (h : TInv t D acc) :
    TInv (tzStep t 58) (D ++ [acc.reverse]) [] := by
  have := tInv_finish h
  unfold tzStep
  rw [if_pos ⟨h.1, .inr rfl⟩, if_pos rfl]
  exact this

/-- A byte of the time: a digit or a colon. -/
def timeByte (b : BitVec 8) : Bool := isDigit b || b == COLON

theorem timeByte_iff (b : BitVec 8) : timeByte b = true ↔ dig b.toNat ∨ b.toNat = 58 := by
  unfold timeByte dig isDigit
  rw [Bool.or_eq_true, ArticleScan.beq_byte]
  simp [COLON]

/-- **The loop over the time** ends with the parts that `splitOn` cuts, the last one still going on. -/
theorem time_fold : ∀ (T : Bytes) (t : TZ) (D : List Bytes) (acc : Bytes), T.all timeByte = true →
    TInv t D acc → ∃ D' acc', TInv (T.foldl (fun t b => tzStep t b.toNat) t) D' acc' ∧
      D' ++ [acc'.reverse] = D ++ List.splitOnPPrepend (· == COLON) T acc
  | [], t, D, acc, _, h => ⟨D, acc, h, by simp [List.splitOnPPrepend]⟩
  | b :: T, t, D, acc, hT, h => by
    simp only [List.all_cons, Bool.and_eq_true] at hT
    have hb := (timeByte_iff b).1 hT.1
    by_cases hc : b.toNat = 58
    · have hb' : (b == COLON) = true := by rw [ArticleScan.beq_byte]; simp [hc, COLON]
      obtain ⟨D', acc', h', e⟩ := time_fold T _ _ [] hT.2 (hc ▸ tInv_colon h)
      refine ⟨D', acc', by simpa only [List.foldl_cons, hc] using h', ?_⟩
      rw [e]; simp [List.splitOnPPrepend, hb']
    · have hb' : (b == COLON) = false := by rw [ArticleScan.beq_byte]; simp [hc, COLON]
      obtain ⟨D', acc', h', e⟩ := time_fold T _ _ _ hT.2 (tInv_digit h (hb.resolve_right hc) hc)
      refine ⟨D', acc', by simpa only [List.foldl_cons] using h', ?_⟩
      rw [e]; simp [List.splitOnPPrepend, hb']

/-- The time `dateValue` reads from its parts: hours and minutes, seconds if given. -/
def timeOf (parts : List Bytes) : Option (Nat × Nat × Nat) :=
  match parts.map number? with
  | [some h, some mi] => some (h, mi, 0)
  | [some h, some mi, some s] => some (h, mi, s)
  | _ => none

theorem number_digits {p : Bytes} (h : p.all isDigit = true) :
    number? p = if p = [] then none else some (value p) := by
  unfold number?
  cases p with
  | nil => rfl
  | cons b q => simp only [List.isEmpty_cons, Bool.not_false, h, Bool.and_self, if_true]; rfl

theorem timeOf_eq {P : List Bytes} (hd : ∀ p ∈ P, p.all isDigit = true) :
    timeOf P = if (P.length = 2 ∨ P.length = 3) ∧ (∀ p ∈ P, p ≠ []) then
      some (value (P.getD 0 []), value (P.getD 1 []), if P.length = 3 then value (P.getD 2 []) else 0) else none := by
  unfold timeOf
  rw [List.map_congr_left (fun p hp => number_digits (hd p hp))]
  rcases P with _ | ⟨p0, _ | ⟨p1, _ | ⟨p2, _ | ⟨p3, P⟩⟩⟩⟩
  · rfl
  · by_cases h0 : p0 = [] <;> simp [h0]
  · by_cases h0 : p0 = [] <;> by_cases h1 : p1 = [] <;> simp [h0, h1]
  · by_cases h0 : p0 = [] <;> by_cases h1 : p1 = [] <;> by_cases h2 : p2 = [] <;> simp [h0, h1, h2]
  · by_cases h0 : p0 = [] <;> by_cases h1 : p1 = [] <;> by_cases h2 : p2 = [] <;> by_cases h3 : p3 = [] <;>
      simp [h0, h1, h2, h3]

/-- **The time as the loop reads it**: the parts' numbers, at most 1000, if two or three parts, none empty. -/
theorem time_of {t : TZ} {P : List Bytes} (h : TInv t P []) (hd : ∀ p ∈ P, p.all isDigit = true) :
    (¬(t.bad = 0 ∧ 2 ≤ t.np ∧ t.np ≤ 3) → timeOf P = none) ∧
    (t.bad = 0 ∧ 2 ≤ t.np ∧ t.np ≤ 3 → ∃ hr mn sc, timeOf P = some (hr, mn, sc) ∧ t.hh = min 1000 hr ∧
      t.mi = min 1000 mn ∧ t.se = min 1000 sc) := by
  obtain ⟨-, hnp, hb1, hbad, -, -, hhh, hmi, hse, -⟩ := h
  rw [timeOf_eq hd]
  refine ⟨fun hc => if_neg fun ⟨h1, h2⟩ => hc ⟨hbad.2 h2, by omega, by omega⟩, fun ⟨h0, h1, h2⟩ => ?_⟩
  rw [if_pos ⟨by omega, hbad.1 h0⟩]
  refine ⟨_, _, _, rfl, ?_, ?_, ?_⟩
  · rw [hhh]; unfold tAt; rcases P with _ | ⟨p0, P⟩
    · simp at hnp; omega
    · rfl
  · rw [hmi]; unfold tAt; rcases P with _ | ⟨p0, _ | ⟨p1, P⟩⟩
    · simp at hnp; omega
    · simp at hnp; omega
    · rfl
  · rw [hse]; unfold tAt; rcases P with _ | ⟨p0, _ | ⟨p1, _ | ⟨p2, P⟩⟩⟩
    · simp at hnp; omega
    · simp at hnp; omega
    · simp
    · have hP : P = [] := List.eq_nil_of_length_eq_zero (by simp at hnp; omega)
      subst hP; rfl

/-! ### The zone -/

/-- The zone's fields after its bytes. -/
def zOf (Z : List Nat) : ZF := Z.foldl zStep ⟨0, 0, 1, 0, 1⟩

theorem tzStep_zone {t : TZ} (h : t.ph ≠ 0) (b : Nat) :
    (tzStep t b).ph = t.ph ∧ zfOf (tzStep t b) = zStep (zfOf t) b ∧ tfOf (tzStep t b) = tfOf t := by
  unfold tzStep
  rw [if_neg (fun h' => h h'.1), if_neg h]
  exact ⟨rfl, rfl, rfl⟩

theorem zone_fold : ∀ (Z : List Nat) (t : TZ), t.ph ≠ 0 →
    (Z.foldl tzStep t).ph = t.ph ∧ zfOf (Z.foldl tzStep t) = Z.foldl zStep (zfOf t) ∧
      tfOf (Z.foldl tzStep t) = tfOf t
  | [], _, _ => ⟨rfl, rfl, rfl⟩
  | b :: Z, t, h => by
    obtain ⟨e1, e2, e3⟩ := tzStep_zone h b
    obtain ⟨f1, f2, f3⟩ := zone_fold Z (tzStep t b) (by rw [e1]; exact h)
    exact ⟨f1.trans e1, by rw [List.foldl_cons, f2, e2]; rfl, f3.trans e3⟩

theorem zFirst_zl (z : ZF) (b : Nat) : (zFirst z b).zl = z.zl := by unfold zFirst; split <;> rfl
theorem zGmt_zl (z : ZF) (b : Nat) : (zGmt z b).zl = z.zl := by unfold zGmt; split <;> rfl
theorem zDig_zg (z : ZF) (b : Nat) : (zDig z b).zg = z.zg := by unfold zDig; split <;> rfl
theorem zNum_zl (z : ZF) (b : Nat) : (zNum z b).zl = z.zl := by unfold zNum zDig; split <;> (try split) <;> rfl

theorem zStep_zl (z : ZF) (b : Nat) : (zStep z b).zl = z.zl + 1 := by
  show (zNum (zGmt (zFirst z b) b) b).zl + 1 = z.zl + 1
  rw [zNum_zl, zGmt_zl, zFirst_zl]

theorem zl_fold : ∀ (Z : List Nat) (z : ZF), (Z.foldl zStep z).zl = z.zl + Z.length
  | [], _ => rfl
  | b :: Z, z => by rw [List.foldl_cons, zl_fold Z, List.length_cons, zStep_zl]; omega

/-- What the program makes of the zone: GMT, or a sign and four digits of hours and minutes below 60. -/
def progZone (z : ZF) : Option Int :=
  if z.zl = 3 ∧ z.zg = 1 then some 0
  else if z.zl ≠ 5 ∨ z.zd = 0 then none
  else if 60 ≤ z.zv % 100 then none
  else if z.z0 = 43 then some ((z.zv / 100 * 3600 + z.zv % 100 * 60 : Nat) : Int)
  else if z.z0 = 45 then some (-((z.zv / 100 * 3600 + z.zv % 100 * 60 : Nat) : Int))
  else none

/-- What `dateValue` makes of the zone. -/
def specZone (Z : Bytes) : Option Int :=
  if named Z "GMT" then some 0 else
    match Z with
    | sign :: digits => (number? digits).bind fun n =>
      if digits.length != 4 || n % 100 ≥ 60 then none else
        let o : Int := ((n / 100) * 3600 + (n % 100) * 60 : Nat)
        if sign == PLUS then some o else if sign == MINUS then some (-o) else none
    | [] => none

theorem lowerB_beq (b : BitVec 8) (c : Nat) (hc : c < 256) :
    (ArticleSpec.lowerB b == BitVec.ofNat 8 c) = decide (ArticleRun.lowN b.toNat = c) := by
  rw [ArticleScan.beq_byte, ArticleRun.lowerB_nat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hc]

theorem gmt_low : List.map ArticleSpec.lowerB (DN.News.CommandSpec.ascii "GMT") = [103#8, 109#8, 116#8] := by
  decide

theorem named_gmt_len {Z : Bytes} (h : Z.length ≠ 3) : named Z "GMT" = false := by
  unfold named ArticleSpec.sameName
  rw [gmt_low]
  exact beq_eq_false_iff_ne.2 fun e => h (by simpa using congrArg List.length e)

theorem named_gmt3 (b0 b1 b2 : BitVec 8) : named [b0, b1, b2] "GMT" =
    decide (ArticleRun.lowN b0.toNat = 103 ∧ ArticleRun.lowN b1.toNat = 109 ∧ ArticleRun.lowN b2.toNat = 116) := by
  unfold named ArticleSpec.sameName
  rw [gmt_low]
  simp only [List.map_cons, List.map_nil, List.cons_beq_cons, lowerB_beq _ _ (by decide : 103 < 256),
    lowerB_beq _ _ (by decide : 109 < 256), lowerB_beq _ _ (by decide : 116 < 256), Bool.decide_and]
  rw [show (([] : List (BitVec 8)) == []) = true from rfl, Bool.and_true]

theorem zStep_0 (z0 zd zv zg b : Nat) :
    zStep ⟨0, z0, zd, zv, zg⟩ b = ⟨1, b, zd, zv, if ArticleRun.lowN b ≠ 103 then 0 else zg⟩ := by
  unfold zStep zNum zGmt zFirst; by_cases h1 : ArticleRun.lowN b = 103 <;> simp [h1]

theorem zStep_1 (z0 zd zv zg b : Nat) :
    zStep ⟨1, z0, zd, zv, zg⟩ b =
      { zDig ⟨1, z0, zd, zv, if ArticleRun.lowN b ≠ 109 then 0 else zg⟩ b with zl := 2 } := by
  unfold zStep zNum zGmt zFirst zDig
  by_cases h1 : ArticleRun.lowN b = 109 <;> by_cases h2 : dig b <;> simp [h1, h2]

theorem zStep_2 (z0 zd zv zg b : Nat) :
    zStep ⟨2, z0, zd, zv, zg⟩ b =
      { zDig ⟨2, z0, zd, zv, if ArticleRun.lowN b ≠ 116 then 0 else zg⟩ b with zl := 3 } := by
  unfold zStep zNum zGmt zFirst zDig
  by_cases h1 : ArticleRun.lowN b = 116 <;> by_cases h2 : dig b <;> simp [h1, h2]

theorem zStep_34 {k : Nat} (hk : k = 3 ∨ k = 4) (z0 zd zv zg b : Nat) :
    zStep ⟨k, z0, zd, zv, zg⟩ b = { zDig ⟨k, z0, zd, zv, zg⟩ b with zl := k + 1 } := by
  unfold zStep zNum zGmt zFirst zDig; rcases hk with rfl | rfl <;> by_cases h2 : dig b <;> simp [h2]

theorem isDigit_dig (b : BitVec 8) : isDigit b = decide (dig b.toNat) := by
  unfold isDigit dig; simp

/-- **The zone as the loop reads it** is the zone `dateValue` reads. -/
theorem zone_eq (Z : Bytes) : progZone (zOf (Z.map (·.toNat))) = specZone Z := by
  have hzl : (zOf (Z.map (·.toNat))).zl = Z.length := by
    unfold zOf; rw [zl_fold]; simp
  by_cases h3 : Z.length = 3
  · rcases Z with _ | ⟨b0, _ | ⟨b1, _ | ⟨b2, _ | ⟨b3, Z⟩⟩⟩⟩ <;> simp at h3
    simp only [zOf, List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil, zStep_0, zStep_1, zStep_2]
    unfold progZone specZone
    simp only [zDig_zg, named_gmt3]
    by_cases hg : ArticleRun.lowN b0.toNat = 103 ∧ ArticleRun.lowN b1.toNat = 109 ∧ ArticleRun.lowN b2.toNat = 116
    · obtain ⟨g0, g1, g2⟩ := hg
      simp [g0, g1, g2]
    · rw [decide_eq_false hg]
      have : ¬((if ArticleRun.lowN b2.toNat ≠ 116 then 0 else if ArticleRun.lowN b1.toNat ≠ 109 then 0 else
          if ArticleRun.lowN b0.toNat ≠ 103 then 0 else 1) = 1) := by
        intro e; apply hg
        by_cases a0 : ArticleRun.lowN b0.toNat = 103 <;> by_cases a1 : ArticleRun.lowN b1.toNat = 109 <;>
          by_cases a2 : ArticleRun.lowN b2.toNat = 116 <;> simp_all
      simp only [this, and_false, if_false, Bool.false_eq_true, ne_eq, show ¬(3 = 5) by decide, not_false_eq_true,
        true_or, if_true]
      exact (Option.bind_fun_none _).symm.trans (by congr 1)
  by_cases h5 : Z.length = 5
  · rcases Z with _ | ⟨b0, _ | ⟨b1, _ | ⟨b2, _ | ⟨b3, _ | ⟨b4, _ | ⟨b5, Z⟩⟩⟩⟩⟩⟩ <;> simp at h5
    simp only [zOf, List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil, zStep_0, zStep_1, zStep_2,
      zStep_34 (k := 3) (.inl rfl), zStep_34 (k := 4) (.inr rfl)]
    unfold progZone specZone
    rw [named_gmt_len (by simp)]
    simp only [Bool.false_eq_true, if_false]
    have hv : value [b1, b2, b3, b4] = (((0 * 10 + (b1.toNat - 48)) * 10 + (b2.toNat - 48)) * 10 + (b3.toNat - 48)) *
        10 + (b4.toNat - 48) := by simp only [value, List.foldl]; omega
    have hp : (b0 == PLUS) = decide (b0.toNat = 43) := by rw [ArticleScan.beq_byte]; rfl
    have hm : (b0 == MINUS) = decide (b0.toNat = 45) := by rw [ArticleScan.beq_byte]; rfl
    unfold number?
    simp only [List.isEmpty_cons, Bool.not_false, Bool.true_and, List.all_cons, List.all_nil, isDigit_dig, hp, hm,
      List.length_cons, List.length_nil]
    rw [hv]
    by_cases d1 : dig b1.toNat <;> by_cases d2 : dig b2.toNat <;> by_cases d3 : dig b3.toNat <;>
      by_cases d4 : dig b4.toNat <;> simp [zDig, d1, d2, d3, d4]
  · unfold progZone specZone
    rw [hzl, if_neg (fun h => h3 h.1), if_pos (Or.inl h5), named_gmt_len h3]
    simp only [Bool.false_eq_true, if_false]
    cases Z with
    | nil => rfl
    | cons sg digits =>
      have hl : digits.length ≠ 4 := by simp at h5; omega
      cases number? digits <;> simp [hl]

/-! ### The loop's verdict -/

/-- The loop's state at its end: a part of the time still going on is ended. -/
def tzEnd (rest : Bytes) : TZ :=
  let t := rest.foldl (fun t b => tzStep t b.toNat) tz0
  if t.ph = 0 then tzFinish t else t

theorem tw_head {p : BitVec 8 → Bool} : ∀ {l : Bytes} {z : BitVec 8} {Z : Bytes},
    l.drop (l.takeWhile p).length = z :: Z → p z = false
  | [], _, _, h => by simp at h
  | x :: l, z, Z, h => by
    cases hx : p x
    · simp only [List.takeWhile, hx, List.length_nil, List.drop_zero] at h; cases h; exact hx
    · simp only [List.takeWhile, hx, List.length_cons, List.drop_succ_cons] at h; exact tw_head h

/-- The first byte past the time: the time's last part ended, the zone begun. -/
theorem tzStep_switch {t : TZ} (h : t.ph = 0) {b : Nat} (hb : ¬(dig b ∨ b = 58)) :
    (tzStep t b).ph = 1 ∧ zfOf (tzStep t b) = zStep (zfOf (tzFinish t)) b ∧ tfOf (tzStep t b) = tfOf (tzFinish t) := by
  unfold tzStep
  rw [if_neg (fun h' => hb h'.2), if_pos h]
  exact ⟨rfl, rfl, rfl⟩

/-- **The loop's end**: the time's parts as `splitOn` cuts them, the zone's fields as `zOf` reads them. -/
theorem tz_end (rest : Bytes) : ∃ t', TInv t' ((rest.takeWhile timeByte).splitOn COLON) [] ∧
    tfOf (tzEnd rest) = tfOf t' ∧
      zfOf (tzEnd rest) = zOf ((rest.drop (rest.takeWhile timeByte).length).map (·.toNat)) := by
  have hsplit := List.takeWhile_append_dropWhile (p := timeByte) (l := rest)
  have hdrop : rest.drop (rest.takeWhile timeByte).length = rest.dropWhile timeByte := ArticleScan.drop_tw rest
  generalize hT : rest.takeWhile timeByte = T at hsplit hdrop ⊢
  rw [hdrop]
  generalize hZ : rest.dropWhile timeByte = Z at hsplit ⊢
  obtain ⟨D, acc, hI, he⟩ := time_fold T tz0 [] [] (by rw [← hT]; exact List.all_takeWhile) tInv0
  have hparts : T.splitOn COLON = D ++ [acc.reverse] := by
    have e : T.splitOn COLON = List.splitOnPPrepend (· == COLON) T [] := List.splitOnP_eq_splitOnPPrepend
    rw [e, ← List.nil_append (List.splitOnPPrepend _ _ _), ← he]
  rw [hparts]
  unfold tzEnd
  rw [← hsplit, List.foldl_append]
  generalize ht1 : T.foldl (fun t b => tzStep t b.toNat) tz0 = t1 at hI
  have hfin := tInv_finish hI
  have hz0 : zfOf (tzFinish t1) = ⟨0, 0, 1, 0, 1⟩ := by
    obtain ⟨-, -, -, -, -, -, -, -, -, hzl, hz0, hzd, hzv, hzg⟩ := hfin
    simp only [zfOf, hzl, hz0, hzd, hzv, hzg]
  cases Z with
  | nil =>
    simp only [List.foldl_nil, hI.1, if_true]
    exact ⟨_, hfin, rfl, by rw [hz0]; rfl⟩
  | cons z Z =>
    have hz : timeByte z = false := tw_head (l := rest) (by rw [hT, hdrop, hZ])
    have hz' : ¬(dig z.toNat ∨ z.toNat = 58) := fun h => by rw [(timeByte_iff z).2 h] at hz; cases hz
    obtain ⟨s1, s2, s3⟩ := tzStep_switch hI.1 hz'
    obtain ⟨f1, f2, f3⟩ := zone_fold (Z.map (·.toNat)) (tzStep t1 z.toNat) (by rw [s1]; decide)
    rw [List.foldl_cons, List.foldl_map] at *
    refine ⟨_, hfin, ?_, ?_⟩
    · rw [if_neg (by rw [f1, s1]; decide)]; exact f3.trans s3
    · rw [if_neg (by rw [f1, s1]; decide), f2, s2, hz0]; rfl

/-! ## The date's parts -/

open DN.News.ArticleSpec (tokens LPAREN indexOf monthNames dayNames daysFromCivil daysIn weekday)
open DN.News.CommandSpec (wordsFrom isWS)

theorem wordsFrom_flatten : ∀ (m cur : Bytes), (wordsFrom m cur).flatten = cur.reverse ++ m.filter (!isWS ·)
  | [], cur => by
    simp only [wordsFrom, List.filter_nil, List.append_nil]
    cases cur <;> simp
  | b :: rest, cur => by
    simp only [wordsFrom]
    cases hb : isWS b
    · simp only [Bool.false_eq_true, if_false, wordsFrom_flatten rest, List.filter_cons, hb, Bool.not_false, if_true,
        List.reverse_cons, List.append_assoc, List.singleton_append]
    · simp only [if_true, List.filter_cons, hb, Bool.not_true, Bool.false_eq_true, if_false]
      cases cur with
      | nil => simp [wordsFrom_flatten rest]
      | cons c cur => simp [wordsFrom_flatten rest]

/-- **The words run together** are the bytes but white space and line ends. -/
theorem tokens_flatten (l : Bytes) : (tokens l).flatten = l.filter (!ArticleScan.gap ·) := by
  rw [ArticleScan.tokens_fm]
  show (wordsFrom (l.map ArticleScan.fm) []).flatten = _
  rw [wordsFrom_flatten, List.reverse_nil, List.nil_append]
  induction l with
  | nil => rfl
  | cons b l ih =>
    simp only [List.map_cons, List.filter_cons, ArticleScan.f_gap]
    cases hg : ArticleScan.gap b
    · simp only [Bool.not_false, if_true, ArticleScan.f_word hg, ih]
    · simp only [Bool.not_true, Bool.false_eq_true, if_false, ih]

theorem dv_commas {v : Bytes} {a b c : Bytes} {r : List Bytes}
    (h : (v.takeWhile (· != LPAREN)).splitOn ArticleSpec.COMMA = a :: b :: c :: r) :
    ArticleSpec.dateValue v = none := by
  simp only [ArticleSpec.dateValue, h]
  rfl

/-- `dateValue` past its front: the date's words read. It is `dateValue`'s text, so that it unfolds to it. -/
def dvRest (wd : Option Bytes) (ts : List Bytes) : Option Int := do
  let (dayT, monthT, yearT, rest) ← match ts with
    | a :: b :: c :: more => some (a, b, c, more.flatten)
    | _ => none
  let day ← number? dayT
  let month := (← indexOf monthT monthNames 0) + 1
  let year ← number? yearT
  let timeT := rest.takeWhile fun b => isDigit b || b == COLON
  let zoneT := rest.drop timeT.length
  let parts := timeT.splitOn COLON
  let (h, mi, s) ← match parts.map number? with
    | [some h, some mi] => some (h, mi, 0)
    | [some h, some mi, some s] => some (h, mi, s)
    | _ => none
  let offset : Int ← if named zoneT "GMT" then some 0 else
    match zoneT with
    | sign :: digits =>
      let n ← number? digits
      if digits.length != 4 || n % 100 ≥ 60 then none
      else
        let o : Int := ((n / 100) * 3600 + (n % 100) * 60 : Nat)
        if sign == PLUS then some o else if sign == MINUS then some (-o) else none
    | [] => none
  guard (1900 ≤ year && 1 ≤ day && day ≤ daysIn year month && h ≤ 23 && mi ≤ 59 && s ≤ 60)
  let days := daysFromCivil year month day
  match wd with
  | some w => guard (indexOf w dayNames 0 == some (weekday days))
  | none => pure ()
  pure (days * 86400 + (h * 3600 + mi * 60 + s : Nat) - offset)

theorem dv_one {v : Bytes} (h : (v.takeWhile (· != LPAREN)).splitOn ArticleSpec.COMMA = [v.takeWhile (· != LPAREN)]) :
    ArticleSpec.dateValue v = dvRest none (tokens (v.takeWhile (· != LPAREN))) := by
  simp only [ArticleSpec.dateValue, h, dvRest]
  rfl

/-! ### Commas -/

theorem sp_free {p : BitVec 8 → Bool} : ∀ (l acc : Bytes), (∀ b ∈ l, p b = false) →
    List.splitOnPPrepend p l acc = [acc.reverse ++ l]
  | [], acc, _ => by simp [List.splitOnPPrepend]
  | b :: l, acc, h => by
    have hb := h b List.mem_cons_self
    simp only [List.splitOnPPrepend, hb, Bool.false_eq_true, if_false]
    rw [sp_free l (b :: acc) fun x hx => h x (List.mem_cons_of_mem _ hx)]
    simp

theorem sp_sep {p : BitVec 8 → Bool} : ∀ (l1 : Bytes) (b : BitVec 8) (l2 acc : Bytes), (∀ x ∈ l1, p x = false) →
    p b = true → List.splitOnPPrepend p (l1 ++ b :: l2) acc = (acc.reverse ++ l1) :: List.splitOnPPrepend p l2 []
  | [], b, l2, acc, _, hb => by simp [List.splitOnPPrepend, hb]
  | x :: l1, b, l2, acc, h, hb => by
    have hx := h x List.mem_cons_self
    simp only [List.cons_append, List.splitOnPPrepend, hx, Bool.false_eq_true, if_false]
    rw [sp_sep l1 b l2 (x :: acc) (fun y hy => h y (List.mem_cons_of_mem _ hy)) hb]
    simp

theorem sp_length {p : BitVec 8 → Bool} : ∀ (l acc : Bytes),
    (List.splitOnPPrepend p l acc).length = (l.filter p).length + 1
  | [], _ => by simp [List.splitOnPPrepend]
  | b :: l, acc => by
    cases hb : p b
    · simp only [List.splitOnPPrepend, hb, Bool.false_eq_true, if_false, List.filter_cons]; exact sp_length l _
    · simp only [List.splitOnPPrepend, hb, if_true, List.filter_cons, List.length_cons]; rw [sp_length l []]

theorem dv_two_name {v w r name : Bytes}
    (h : (v.takeWhile (· != LPAREN)).splitOn ArticleSpec.COMMA = [w, r]) (hn : tokens w = [name]) :
    ArticleSpec.dateValue v = dvRest (some name) (tokens r) := by
  simp only [ArticleSpec.dateValue, h, hn, dvRest]
  rfl

theorem dv_two_bad {v w r : Bytes} (h : (v.takeWhile (· != LPAREN)).splitOn ArticleSpec.COMMA = [w, r])
    (hn : ∀ name, tokens w ≠ [name]) : ArticleSpec.dateValue v = none := by
  cases hw : tokens w with
  | nil => simp only [ArticleSpec.dateValue, h, hw]; rfl
  | cons x l =>
    cases l with
    | nil => exact absurd hw (hn x)
    | cons y l => simp only [ArticleSpec.dateValue, h, hw]; rfl

/-- The comma that ends the day of the week. -/
def isComma (b : BitVec 8) : Bool := b == ArticleSpec.COMMA

theorem isComma_toNat (b : BitVec 8) : isComma b = decide (b.toNat = 44) := by
  unfold isComma; rw [ArticleScan.beq_byte]; rfl

theorem comma_many {l : Bytes} (h : 2 ≤ (l.filter isComma).length) :
    ∃ a b c r, l.splitOn ArticleSpec.COMMA = a :: b :: c :: r := by
  have e : l.splitOn ArticleSpec.COMMA = List.splitOnPPrepend isComma l [] :=
    List.splitOnP_eq_splitOnPPrepend
  have hl : (l.splitOn ArticleSpec.COMMA).length = (l.filter isComma).length + 1 := by
    rw [e]; exact sp_length l []
  rcases hs : l.splitOn ArticleSpec.COMMA with _ | ⟨a, _ | ⟨b, _ | ⟨c, r⟩⟩⟩
  · rw [hs] at hl; simp only [List.length_nil] at hl; omega
  · rw [hs] at hl; simp only [List.length_cons, List.length_nil] at hl; omega
  · rw [hs] at hl; simp only [List.length_cons, List.length_nil] at hl; omega
  · exact ⟨a, b, c, r, rfl⟩

theorem comma_none {l : Bytes} (h : (l.filter isComma).length = 0) :
    l.splitOn ArticleSpec.COMMA = [l] := by
  have e : l.splitOn ArticleSpec.COMMA = List.splitOnPPrepend isComma l [] := List.splitOnP_eq_splitOnPPrepend
  rw [e, sp_free l [] fun b hb => by
    rw [List.length_eq_zero_iff, List.filter_eq_nil_iff] at h; simpa using h b hb]
  rfl

theorem comma_one {l1 l2 : Bytes} {c : BitVec 8} (h1 : l1.all (fun b => !isComma b) = true)
    (hc : isComma c = true) (h2 : (l2.filter isComma).length = 0) :
    (l1 ++ c :: l2).splitOn ArticleSpec.COMMA = [l1, l2] := by
  have e : (l1 ++ c :: l2).splitOn ArticleSpec.COMMA = List.splitOnPPrepend isComma (l1 ++ c :: l2) [] :=
    List.splitOnP_eq_splitOnPPrepend
  rw [e, sp_sep l1 c l2 [] (fun x hx => by simpa using List.all_eq_true.1 h1 x hx) hc,
    sp_free l2 [] fun b hb => by rw [List.length_eq_zero_iff, List.filter_eq_nil_iff] at h2; simpa using h2 b hb]
  simp

/-! ### The date past its front -/

/-- `dvRest` past the three words, its options taken apart. -/
def dvC (wd : Option Bytes) (d m y rest : Bytes) : Option Int :=
  match number? d, indexOf m monthNames 0, number? y, timeOf ((rest.takeWhile timeByte).splitOn COLON),
    specZone (rest.drop (rest.takeWhile timeByte).length) with
  | some day, some mo, some year, some (h, mi, s), some off =>
    if 1900 ≤ year ∧ 1 ≤ day ∧ day ≤ daysIn year (mo + 1) ∧ h ≤ 23 ∧ mi ≤ 59 ∧ s ≤ 60 then
      if wd.all fun w => indexOf w dayNames 0 == some (weekday (daysFromCivil year (mo + 1) day)) then
        some (daysFromCivil year (mo + 1) day * 86400 + ((h * 3600 + mi * 60 + s : Nat) : Int) - off)
      else none
    else none
  | _, _, _, _, _ => none

theorem dvRest_short {wd : Option Bytes} {ts : List Bytes} (h : ts.length < 3) : dvRest wd ts = none := by
  rcases ts with _ | ⟨a, _ | ⟨b, _ | ⟨c, ts⟩⟩⟩
  · rfl
  · rfl
  · rfl
  · simp at h; omega

/-- **`dvRest` of three words and more** is `dvC`. -/
theorem dvRest_cons (wd : Option Bytes) (d m y : Bytes) (more : List Bytes) :
    dvRest wd (d :: m :: y :: more) = dvC wd d m y more.flatten := by
  cases hd : number? d <;> cases hm : indexOf m monthNames 0 <;> cases hy : number? y <;>
    simp only [dvRest, dvC, hd, hm, hy, Option.bind_eq_bind, Option.bind_some, Option.bind_none] <;> try rfl
  rename_i day mo year
  simp only [timeOf, specZone, show timeByte = fun b => isDigit b || b == COLON from rfl]
  generalize more.flatten = rest
  generalize List.takeWhile (fun b => isDigit b || b == COLON) rest = T
  generalize List.drop T.length rest = Z
  generalize List.map number? (List.splitOn COLON T) = L
  have hG : ∀ (c : Prop) [Decidable c] (x : Option Int), ((if c then some () else failure).bind fun _ => x) =
      if c then x else none := by
    intro c _ x; split <;> rfl
  split
  rotate_left 2
  · split <;> simp_all
  all_goals
    by_cases hg : named Z "GMT" = true
    · simp only [hg, if_true]
      cases wd <;> simp only [guard, hG, Bool.and_eq_true, decide_eq_true_eq, and_assoc, Option.all_none,
        Option.all_some, Option.pure_def, Option.bind_some, if_true] <;> rfl
    · simp only [hg, Bool.false_eq_true, if_false]
      rcases Z with _ | ⟨sg, digits⟩
      · rfl
      · dsimp only
        cases hn : number? digits
        · rfl
        · simp only [Option.bind_some]
          split
          · rfl
          · split
            · cases wd <;> simp only [guard, hG, Bool.and_eq_true, decide_eq_true_eq, and_assoc, Option.all_none,
                Option.all_some, Option.pure_def, Option.bind_some, if_true] <;> rfl
            · split
              · cases wd <;> simp only [guard, hG, Bool.and_eq_true, decide_eq_true_eq, and_assoc, Option.all_none,
                  Option.all_some, Option.pure_def, Option.bind_some, if_true] <;> rfl
              · rfl

theorem dvC_none {wd : Option Bytes} {d m y rest : Bytes}
    (h : number? d = none ∨ indexOf m monthNames 0 = none ∨ number? y = none ∨
      timeOf ((rest.takeWhile timeByte).splitOn COLON) = none ∨
      specZone (rest.drop (rest.takeWhile timeByte).length) = none) : dvC wd d m y rest = none := by
  unfold dvC
  split
  · rcases h with h | h | h | h | h <;> simp_all
  · rfl

theorem dvC_some {wd : Option Bytes} {d m y rest : Bytes} {day mo year h mi s : Nat} {off : Int}
    (hd : number? d = some day) (hm : indexOf m monthNames 0 = some mo) (hy : number? y = some year)
    (ht : timeOf ((rest.takeWhile timeByte).splitOn COLON) = some (h, mi, s))
    (hz : specZone (rest.drop (rest.takeWhile timeByte).length) = some off) :
    dvC wd d m y rest = if 1900 ≤ year ∧ 1 ≤ day ∧ day ≤ daysIn year (mo + 1) ∧ h ≤ 23 ∧ mi ≤ 59 ∧ s ≤ 60 then
      (if wd.all fun w => indexOf w dayNames 0 == some (weekday (daysFromCivil year (mo + 1) day)) then
        some (daysFromCivil year (mo + 1) day * 86400 + ((h * 3600 + mi * 60 + s : Nat) : Int) - off) else none)
      else none := by
  unfold dvC; rw [hd, hm, hy, ht, hz]

/-! ### The parts' bounds -/

theorem parts_digits : ∀ (T acc : Bytes), T.all timeByte = true → acc.all isDigit = true →
    ∀ p ∈ List.splitOnPPrepend (· == COLON) T acc, p.all isDigit = true
  | [], acc, _, ha => by simpa [List.splitOnPPrepend] using ha
  | b :: T, acc, hT, ha => by
    simp only [List.all_cons, Bool.and_eq_true] at hT
    cases hb : b == COLON
    · simp only [List.splitOnPPrepend, hb, Bool.false_eq_true, if_false]
      refine parts_digits T (b :: acc) hT.2 ?_
      have : isDigit b = true := by
        have := hT.1; unfold timeByte at this; simpa [hb] using this
      simp [this, ha]
    · simp only [List.splitOnPPrepend, hb, if_true, List.mem_cons]
      rintro p (rfl | hp)
      · simpa using ha
      · exact parts_digits T [] hT.2 rfl p hp

/-- The bound of the zone's number after `zl` of its bytes. -/
def zcap : Nat → Nat
  | 0 | 1 => 1
  | 2 => 10
  | 3 => 100
  | 4 => 1000
  | _ => 10000

/-- The zone's fields within their bounds. -/
def ZB (z : ZF) : Prop := z.zg ≤ 1 ∧ z.zd ≤ 1 ∧ z.z0 < 256 ∧ z.zv < zcap z.zl

theorem zStep_5 {zl : Nat} (h : 5 ≤ zl) (z0 zd zv zg b : Nat) :
    zStep ⟨zl, z0, zd, zv, zg⟩ b = ⟨zl + 1, z0, zd, zv, zg⟩ := by
  unfold zStep zNum zGmt zFirst
  simp [show zl ≠ 0 by omega, show zl ≠ 1 by omega, show zl ≠ 2 by omega, show ¬zl ≤ 4 by omega]

theorem zcap_big {k : Nat} (h : 5 ≤ k) : zcap k = 10000 := by
  match k, h with
  | _ + 5, _ => rfl

theorem zb_step {z : ZF} (h : ZB z) {b : Nat} (hb : b < 256) : ZB (zStep z b) := by
  obtain ⟨zl, z0, zd, zv, zg⟩ := z
  obtain ⟨h1, h2, h3, h4⟩ := h
  simp only at h1 h2 h3 h4
  have hz : ∀ (k g : Nat), g ≤ 1 → zcap (k + 1) = zcap k * 10 → zv < zcap k →
      ZB { zDig ⟨k, z0, zd, zv, g⟩ b with zl := k + 1 } := by
    intro k g g1 hk g4
    unfold zDig; split
    · rename_i hd; unfold dig at hd
      exact ⟨g1, h2, h3, by dsimp only; rw [hk]; omega⟩
    · exact ⟨g1, by dsimp only; omega, h3, by dsimp only; rw [hk]; omega⟩
  rcases (by omega : zl = 0 ∨ zl = 1 ∨ zl = 2 ∨ zl = 3 ∨ zl = 4 ∨ 5 ≤ zl) with e | e | e | e | e | e
  · subst e; rw [zStep_0]
    exact ⟨by dsimp only; split <;> omega, h2, hb, h4⟩
  · subst e; rw [zStep_1]; exact hz 1 _ (by split <;> omega) rfl h4
  · subst e; rw [zStep_2]; exact hz 2 _ (by split <;> omega) rfl h4
  · subst e; rw [zStep_34 (.inl rfl)]; exact hz 3 _ h1 rfl h4
  · subst e; rw [zStep_34 (.inr rfl)]; exact hz 4 _ h1 rfl h4
  · rw [zStep_5 e]
    exact ⟨h1, h2, h3, by dsimp only; rw [zcap_big (by omega)]; rw [zcap_big e] at h4; exact h4⟩

theorem zb_fold : ∀ (Z : List Nat) (z : ZF), (∀ b ∈ Z, b < 256) → ZB z → ZB (Z.foldl zStep z)
  | [], _, _, h => h
  | b :: Z, _, hZ, h => zb_fold Z _ (fun x hx => hZ x (List.mem_cons_of_mem _ hx)) (zb_step h (hZ b List.mem_cons_self))

theorem zb_zOf (Z : Bytes) : ZB (zOf (Z.map (·.toNat))) :=
  zb_fold _ _ (fun b hb => by
    obtain ⟨x, -, rfl⟩ := List.mem_map.1 hb; exact x.isLt) ⟨by decide, by decide, by decide, by decide⟩

/-! ### The calendar -/

/-- **Days 400 years apart** are 146097 days apart. -/
theorem civil_shift (Y M D k : Nat) (hY : 1 ≤ Y) :
    daysFromCivil (Y + 400 * k) M D = daysFromCivil Y M D + 146097 * (k : Int) := by
  simp only [daysFromCivil]
  generalize (153 * (if M > 2 then M - 3 else M + 9) + 2) / 5 + D - 1 = doy
  by_cases hM : M ≤ 2 <;> simp only [hM, if_true, if_false] <;> omega

theorem weekday_shift (x : Int) (k : Nat) : weekday (x + 146097 * (k : Int)) = weekday x := by
  unfold weekday; congr 1; omega

/-- The program's day of the week, from the day plus 700004, which is 4 past a multiple of 7. -/
theorem weekday_nat {x : Int} (h : -700004 ≤ x) : weekday x = (x + 700004).toNat % 7 := by
  unfold weekday; omega

/-- The days of month `M` as the program counts them, from the year's place in the 400 years. -/
def dmOf (y4 M : Nat) : Nat :=
  if M = 2 then 28 + (if y4 % 4 = 0 ∧ y4 ≠ 100 ∧ y4 ≠ 200 ∧ y4 ≠ 300 then 1 else 0)
  else if M = 4 ∨ M = 6 ∨ M = 9 ∨ M = 11 then 30 else 31

theorem daysIn_eq (Y M : Nat) : daysIn Y M = dmOf (Y % 400) M := by
  unfold daysIn dmOf ArticleSpec.leap
  by_cases h2 : M = 2
  · subst h2
    simp only [beq_self_eq_true, if_true]
    by_cases hl : Y % 400 % 4 = 0 ∧ Y % 400 ≠ 100 ∧ Y % 400 ≠ 200 ∧ Y % 400 ≠ 300
    · rw [if_pos hl, if_pos]; simp only [Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true, bne_iff_ne, ne_eq]; omega
    · rw [if_neg hl, if_neg]; simp only [Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true, bne_iff_ne, ne_eq]; omega
  · simp only [show (M == 2) = false from beq_eq_false_iff_ne.2 h2, h2, Bool.false_eq_true, if_false,
      Bool.or_eq_true, beq_iff_eq]
    split <;> split <;> first | rfl | omega

theorem daysIn_le (y m : Nat) : daysIn y m ≤ 31 := by
  unfold daysIn; split <;> (try split) <;> (try split) <;> omega

/-- **A year from `yearBig` on** starts at least 35780167 days after 1970. Times 86400, less the largest offset, that
is still past `2 ^ 41`. -/
theorem civil_big {Y M D : Nat} (hY : ArticleProg.yearBig ≤ Y) : 35780167 ≤ daysFromCivil Y M D := by
  have : ArticleProg.yearBig = 100000 := rfl
  simp only [daysFromCivil]
  generalize (153 * (if M > 2 then M - 3 else M + 9) + 2) / 5 + D - 1 = doy
  by_cases hM : M ≤ 2 <;> simp only [hM, if_true, if_false] <;> omega

/-- The days of the years the program counts in full. -/
theorem civil_range {Y M D : Nat} (h1 : 1900 ≤ Y) (h2 : Y < 100000) (hM : 1 ≤ M) (hM' : M ≤ 12) (hD : D ≤ 31) :
    -26333 ≤ daysFromCivil Y M D ∧ daysFromCivil Y M D < 36600000 := by
  simp only [daysFromCivil]
  have hdoy : (153 * (if M > 2 then M - 3 else M + 9) + 2) / 5 ≤ 337 := by split <;> omega
  generalize (153 * (if M > 2 then M - 3 else M + 9) + 2) / 5 = q at hdoy
  by_cases hM2 : M ≤ 2 <;> simp only [hM2, if_true, if_false] <;> omega

/-- The offset a zone gives, at most 99 hours and 59 minutes. -/
theorem progZone_bound {z : ZF} (hz : ZB z) {off : Int} (h : progZone z = some off) :
    -359940 ≤ off ∧ off ≤ 359940 := by
  obtain ⟨-, -, -, h4⟩ := hz
  unfold progZone at h
  split at h
  · cases h; omega
  · split at h
    · cases h
    · rename_i h5
      have e : z.zl = 5 := by omega
      rw [e] at h4
      have h4' : z.zv < 10000 := h4
      split at h
      · cases h
      · rename_i hm
        split at h
        · cases h; omega
        · split at h
          · cases h; omega
          · cases h

/-! ## Witnesses: each premise can hold -/

theorem dig_witness : dig 48 := ⟨Nat.le_refl _, by decide⟩

theorem zb_witness : ZB ⟨0, 0, 1, 0, 1⟩ := ⟨by decide, by decide, by decide, by decide⟩

end DN.News.ArticleDate
