-- SPDX-License-Identifier: AGPL-3.0-or-later
import DN.News.ScanDecode

/-!
# DN.News.ScanStep

If it goes on, the scanner's reading of the record a checked frame holds, `ScanProg.recordOf`, gives
`Journal.recordOf`'s type and a commit's fields (`recordOf_frag`); the premises can hold (`Witness`).
-/

namespace DN.News.ScanRun

open DN.Compiler DN.Compiler.Wp DN.Compiler.Frag DN.Compiler.Bytes DN.News DN.News.Journal DN.News.ScanProg
open DN.News.FramerCode (bw bw_ne0 bw_eq0 eval_eq eval_and)

variable {σ : Type}

/-! ## The record -/

/-- The locals the reading of a record sets. -/
def recNames : List String := "jpp" :: "jwhy" :: "jrec" :: decNames

/-- What `recordOf` reads: the frame checked, its type `t` and payload `pl`, `o'` octets into the window. -/
structure RecIn (A : Word) (o' t : Nat) (pl : Bytes) (s : PancakeState σ) : Prop where
  hA : A.toNat % 8 = 0
  dom : Dom A s.memaddrs
  sp : s.locals "jsc" = some A
  jz : s.locals "jz" = some 0
  jw : s.locals "jw" = some (at_ A sWindow)
  jo : s.locals "jo" = some (BitVec.ofNat 64 o')
  jf : s.locals "jf" = some (at_ A (sWindow + o'))
  jt : s.locals "jt" = some (BitVec.ofNat 64 t)
  jpl : s.locals "jpl" = some (BitVec.ofNat 64 pl.length)
  jwhy : s.locals "jwhy" = some 0
  payload : ∀ i (h : i < pl.length),
    memLoadByte s.memory s.memaddrs s.be (at_ A (sWindow + o' + 13 + i)) = some pl[i]
  room : o' + maxFrame ≤ windowRoom
  len : pl.length ≤ maxPayload
  ht : t < 256
  bound : ∀ y ∈ recNames, ∃ v, s.locals y = some v

/-- The type of the record a frame holds, zero for none. -/
def recType (t : Nat) (pl : Bytes) : Nat := ((Journal.recordOf spec t pl).map Record.type).getD 0

theorem recType_le (t : Nat) (pl : Bytes) : recType t pl ≤ 3 := by
  unfold recType
  cases Journal.recordOf spec t pl with
  | none => simp
  | some r => cases r <;> simp [Record.type, formatType, commitType, startType]

/-- What `recordOf` leaves: `jrec` the record's type, `jwhy` the code of one that is none, a commit's fields. -/
structure RecOut (A : Word) (o' t : Nat) (pl : Bytes) (s0 u : PancakeState σ) : Prop where
  kept : Kept recNames (FieldW A) s0 u
  jpp : u.locals "jpp" = some (at_ A (sWindow + o' + 13))
  jrec : u.locals "jrec" = some (BitVec.ofNat 64 (recType t pl))
  why : u.locals "jwhy" = some (BitVec.ofNat 64 (if (Journal.recordOf spec t pl).isSome then 0 else
    whyCode .notARecord))
  commit : ∀ c, Journal.recordOf spec t pl = some (.commit c) → CommitAt A o' pl c u

theorem recOut_clock {A : Word} {o' t : Nat} {pl : Bytes} {s0 : PancakeState σ} :
    Safe.ClockFree (RecOut A o' t pl s0) := fun _ _ h => { h with kept := { h.kept with } }

theorem recordOf_eq (t : Nat) (pl : Bytes) : Journal.recordOf spec t pl =
    if t = formatType then (if pl.length = 36 ∧ pl.take 20 = magic then some (.format (pl.drop 20)) else none)
    else if t = commitType then (decodeCommit pl).map .commit
    else if t = startType then (if pl.length = 0 then some .start else none) else none := by
  have hm : magic.length = 20 := rfl
  have hk : keyLength = 16 := rfl
  unfold Journal.recordOf
  by_cases h1 : t = formatType
  · rw [if_pos (by simp [h1]), if_pos h1]
    by_cases h : pl.length = 36 ∧ pl.take 20 = magic
    · rw [if_pos (by simp [hm, hk, h.1, h.2]), if_pos h, hm]
    · rw [if_neg (by simp only [hm, hk, Bool.and_eq_true, beq_iff_eq]; exact h), if_neg h]
  rw [if_neg (by simp [h1]), if_neg h1]
  by_cases h2 : t = commitType
  · rw [if_pos (by simp [h2]), if_pos h2]; rfl
  rw [if_neg (by simp [h2]), if_neg h2]
  by_cases h3 : t = startType
  · rw [if_pos (by simp [h3]), if_pos h3]
    by_cases h : pl.length = 0
    · rw [if_pos (by simp [List.length_eq_zero_iff.mp h]), if_pos h]
    · rw [if_neg (by intro e; exact h (List.length_eq_zero_iff.mpr (List.isEmpty_iff.mp e))), if_neg h]
  rw [if_neg (by simp [h3]), if_neg h3]

/-- **The scanner's reading of a record is `Journal.recordOf`**: if it goes on, `jrec` holds the type of the
record the frame holds, `jwhy` `notARecord`'s code if it holds none, and the area a commit's fields. -/
theorem recordOf_frag (o : Oracle σ) {A : Word} {o' t : Nat} {pl : Bytes} {s0 : PancakeState σ}
    (h : RecIn A o' t pl s0) {fail : List Syntax.PStmt} (hfl : LowKK fail) (hfd : declared fail = []) :
    Frag o (ScanProg.recordOf fail) (Like s0) (RecOut A o' t pl s0) := by
  have hn := nums
  have hl := h.len
  have hlocal : ∀ u, Kept recNames (FieldW A) s0 u → ∀ y, y ∉ recNames → u.locals y = s0.locals y :=
    fun u hu y hy => hu.locals y hy
  have hbd : ∀ u, Kept recNames (FieldW A) s0 u → ∀ y ∈ recNames, ∃ v, u.locals y = some v := fun u hu y hy =>
    kept_has hu (h.bound y hy)
  -- `jrec` zero, `jpp` the payload
  let Q2 (u : PancakeState σ) : Prop := Kept recNames (FieldW A) s0 u ∧
    u.locals "jpp" = some (at_ A (sWindow + o' + 13)) ∧ u.locals "jrec" = some 0 ∧ u.locals "jwhy" = some 0
  have hQ2c : Safe.ClockFree Q2 := fun _ _ ⟨h1, h2⟩ => ⟨{ h1 with }, h2⟩
  have f1 :
      Frag o [.assign "jrec" (lit 0), .assign "jpp" (Syntax.atOff (Syntax.v "jf") headerLength)] (Like s0) Q2 := by
    refine frag_append (xs := [_]) (set_frag o (E := .op .add (.var "jz") (.const 0)) rfl
      (P' := fun u => Kept recNames (FieldW A) s0 u ∧ u.locals "jrec" = some 0 ∧ u.locals "jwhy" = some 0)
      (fun _ _ ⟨h1, h2⟩ => ⟨{ h1 with }, h2⟩) fun u hu => ⟨0, by
        simp [eval, (hlocal u (kept_of_like hu) "jz" (by decide)).trans h.jz], hbd u (kept_of_like hu) "jrec"
          (by decide), kept_set (kept_of_like hu) (by decide) _, by simp [setL, setLocal],
        by simp [setL, setLocal, hu.locals, h.jwhy]⟩) ?_
    exact set_frag o (E := .op .add (.var "jf") (.const (BitVec.ofNat 64 headerLength))) rfl hQ2c fun u hu =>
      ⟨at_ A (sWindow + o' + 13), by simp only [eval, (hlocal u hu.1 "jf" (by decide)).trans h.jf, at_add]; rfl,
      hbd u hu.1 "jpp" (by decide),
      kept_set hu.1 (by decide) _, by simp [setL, setLocal], by simp [setL, setLocal, hu.2.1],
      by simp [setL, setLocal, hu.2.2]⟩
  let Q3 (u : PancakeState σ) : Prop := Kept recNames (FieldW A) s0 u ∧
    u.locals "jpp" = some (at_ A (sWindow + o' + 13)) ∧ u.locals "jrec" = some (BitVec.ofNat 64 (recType t pl)) ∧
    u.locals "jwhy" = some 0 ∧ ∀ c, Journal.recordOf spec t pl = some (.commit c) → CommitAt A o' pl c u
  have hQ3c : Safe.ClockFree Q3 := fun _ _ ⟨h1, h2⟩ => ⟨{ h1 with }, h2⟩
  have hjt : ∀ u, Kept recNames (FieldW A) s0 u → u.locals "jt" = some (BitVec.ofNat 64 t) := fun u hu =>
    (hlocal u hu "jt" (by decide)).trans h.jt
  have hjpl : ∀ u, Kept recNames (FieldW A) s0 u → u.locals "jpl" = some (BitVec.ofNat 64 pl.length) := fun u hu =>
    (hlocal u hu "jpl" (by decide)).trans h.jpl
  have hht := h.ht
  have hrt : recType t pl = if t = formatType then (if pl.length = 36 ∧ pl.take 20 = magic then 1 else 0)
      else if t = commitType then (if (decodeCommit pl).isSome then 2 else 0)
      else if t = startType then (if pl.length = 0 then 3 else 0) else 0 := by
    unfold recType; rw [recordOf_eq]
    by_cases h1 : t = formatType
    · rw [if_pos h1, if_pos h1]
      by_cases hm : pl.length = 36 ∧ pl.take 20 = magic
      · rw [if_pos hm, if_pos hm]; rfl
      · rw [if_neg hm, if_neg hm]; rfl
    rw [if_neg h1, if_neg h1]
    by_cases h2 : t = commitType
    · rw [if_pos h2, if_pos h2]; cases decodeCommit pl <;> rfl
    rw [if_neg h2, if_neg h2]
    by_cases h3 : t = startType
    · rw [if_pos h3, if_pos h3]
      by_cases hz : pl.length = 0
      · rw [if_pos hz, if_pos hz]; rfl
      · rw [if_neg hz, if_neg hz]; rfl
    rw [if_neg h3, if_neg h3]; rfl
  have hev1 : ∀ u, Q2 u → eval u (.cmp .equal (.var "jt") (.const (BitVec.ofNat 64 formatType))) =
      some (bw (decide (t = formatType))) := fun u hu =>
    eval_eq (a := .var "jt") (by omega) (by decide) (hjt u hu.1) rfl
  refine frag_append (xs := [_, _]) f1 (frag_append (xs := [_]) (frag_ite o (C := .cmp .equal (.var "jt")
    (.const (BitVec.ofNat 64 formatType))) rfl hQ3c (fun u hu => ⟨_, hev1 u hu⟩) ?_ (noDecl _ rfl) ?_ (noDecl _ rfl))
    ?_)
  · -- a format: its length and its magic
    refine frag_pure (t = formatType) (fun u ⟨hu, hne⟩ => by rw [hev1 u hu] at hne; simpa using bw_ne0 hne)
      (lowK_any _ (k := .skip) (c := _) rfl) fun h1 => ?_
    obtain ⟨E, hE⟩ : ∃ E, Lower.lowerExp (ScanProg.bytesAre (Syntax.v "jpp") magic) = some E := ⟨_, rfl⟩
    have hmag : ∀ u, Q2 u → ∃ ys : Bytes, (pl.length = 36 → ys = pl.take 20) ∧
        eval u E = some (bw (decide (ys = magic))) := fun u hu => by
      have hdm : ∀ i, i < 20 → u.memaddrs (byteAlign (at_ A (sWindow + o' + 13) + BitVec.ofNat 64 i)) = true :=
        fun i hi => by
          rw [hu.1.memaddrs, at_add]; have := h.room; exact h.dom _ (by simp only [ScanProg.size]; omega)
      by_cases h36 : pl.length = 36
      · obtain ⟨E', hE', hv⟩ := bytesAre_eval (u := u) (p := Syntax.v "jpp") (P := .var "jpp") rfl hu.2.1
          (ys := pl.take 20) (bs := magic) (by simp [h36]; rfl) fun i hi => by
            have hi' : i < pl.length := by simp at hi; omega
            rw [at_add, kept_load hu.1 (not_field h.hA (Or.inr (by omega)) (by have := h.room; omega)),
              h.payload i hi']
            simp [List.getElem_take]
        rw [hE] at hE'; cases hE'
        exact ⟨pl.take 20, fun _ => rfl, hv⟩
      · obtain ⟨ys, hyl, hy⟩ := bytes_exist (u := u) (a := at_ A (sWindow + o' + 13)) 20 hdm
        obtain ⟨E', hE', hv⟩ := bytesAre_eval (u := u) (p := Syntax.v "jpp") (P := .var "jpp") rfl hu.2.1
          (ys := ys) (bs := magic) (by rw [hyl]; rfl) hy
        rw [hE] at hE'; cases hE'
        exact ⟨ys, fun e => absurd e h36, hv⟩
    have hcf : ∀ u, Q2 u → eval u (.op .and_ (.cmp .equal (.var "jpl") (.const (BitVec.ofNat 64 36))) E) =
        some (bw (decide (pl.length = 36 ∧ pl.take 20 = magic))) := fun u hu => by
      obtain ⟨ys, hys, hv⟩ := hmag u hu
      rw [eval_and (eval_eq (a := .var "jpl") (by omega) (by decide) (hjpl u hu.1) rfl) hv]
      by_cases h36 : pl.length = 36
      · rw [hys h36]; simp [h36]
      · simp [h36]
    refine frag_ite o (C := .op .and_ (.cmp .equal (.var "jpl") (.const (BitVec.ofNat 64 36))) E)
      (by unfold Syntax.eAnd; rw [Lower.lowerExp, hE]; rfl) hQ3c
      (fun u hu => ⟨_, hcf u hu.1⟩) ?_ (noDecl _ rfl) (frag_nil o fun u ⟨⟨hu, _⟩, h0⟩ => ?_) (noDecl _ rfl)
    · refine set_frag o (E := .op .add (.var "jz") (.const (BitVec.ofNat 64 formatType))) rfl hQ3c
        fun u ⟨⟨hu, _⟩, hne⟩ => ?_
      rw [hcf u hu] at hne
      have hm := bw_ne0 hne
      simp only [decide_eq_true_eq] at hm
      refine ⟨BitVec.ofNat 64 formatType, by simp [eval, (hlocal u hu.1 "jz" (by decide)).trans h.jz], ⟨_, hu.2.2.1⟩,
        kept_set hu.1 (by decide) _, by simp [setL, setLocal, hu.2.1], ?_, by simp [setL, setLocal, hu.2.2.2],
        fun c e => ?_⟩
      · rw [hrt, if_pos h1, if_pos hm]; simp [setL, setLocal]; rfl
      · rw [recordOf_eq, if_pos h1, if_pos hm] at e; cases e
    · rw [hcf u hu] at h0
      have hm := bw_eq0 h0
      simp only [decide_eq_false_iff_not] at hm
      refine ⟨hu.1, hu.2.1, by rw [hrt, if_pos h1, if_neg hm]; exact hu.2.2.1, hu.2.2.2, fun c e => ?_⟩
      rw [recordOf_eq, if_pos h1, if_neg hm] at e; cases e
  · -- not a format: a commit, a start, or none
    have hev2 : ∀ u, Q2 u → eval u (.cmp .equal (.var "jt") (.const (BitVec.ofNat 64 commitType))) =
        some (bw (decide (t = commitType))) := fun u hu =>
      eval_eq (a := .var "jt") (by omega) (by decide) (hjt u hu.1) rfl
    refine frag_pure (t ≠ formatType) (fun u ⟨hu, h0⟩ => by rw [hev1 u hu] at h0; simpa using bw_eq0 h0)
      (lowKK_ite rfl (lowKK_decode hfl) (lowK_any _ (k := .skip) (c := _) rfl)) fun h1 => ?_
    refine frag_ite o (C := .cmp .equal (.var "jt") (.const (BitVec.ofNat 64 commitType))) rfl hQ3c
      (fun u hu => ⟨_, hev2 u hu.1⟩) ?_ (noDecl _ rfl) ?_ (noDecl _ rfl)
    · -- a commit
      refine frag_pure (t = commitType) (fun u ⟨⟨hu, _⟩, hne⟩ => by rw [hev2 u hu] at hne; simpa using bw_ne0 hne)
        (lowKK_decode hfl) fun h2 => ?_
      refine frag_each o (lowKK_decode hfl) fun s ⟨⟨hs, _⟩, _⟩ => ?_
      have hdec : DecIn A o' pl s := {
        hA := h.hA
        dom := by rw [hs.1.memaddrs]; exact h.dom
        sp := (hlocal s hs.1 "jsc" (by decide)).trans h.sp
        jz := (hlocal s hs.1 "jz" (by decide)).trans h.jz
        jw := (hlocal s hs.1 "jw" (by decide)).trans h.jw
        jo := (hlocal s hs.1 "jo" (by decide)).trans h.jo
        jpp := hs.2.1
        jpl := hjpl s hs.1
        payload := fun i hi => by
          rw [kept_load hs.1 (not_field h.hA (Or.inr (by omega)) (by have := h.room; omega))]; exact h.payload i hi
        room := h.room
        len := h.len
        bound := fun y hy => hbd s hs.1 y (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hy)))
        jrec := hbd s hs.1 "jrec" (by decide) }
      refine frag_conseq (decode_frag o hdec hfl hfd) (fun _ h => h) fun u hu => ?_
      obtain ⟨hjok, hcm⟩ := decOut_commit hu
      have hk : Kept recNames (FieldW A) s0 u :=
        kept_trans hs.1 (kept_widen hu.1.1 (fun x hx => by
          simp only [List.mem_cons] at hx; rcases hx with rfl | hx
          · decide
          · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hx))) fun _ h => h)
      refine ⟨hk, (hu.1.1.locals "jpp" (by decide)).trans hs.2.1, ?_,
        (hu.1.1.locals "jwhy" (by decide)).trans hs.2.2.2, fun c e => ?_⟩
      · rw [hrt, if_neg h1, if_pos h2]
        cases hd : decodeCommit pl with
        | none =>
          have : okHOf pl = false := by
            have e := scan_okH pl; rw [scanCommit_eq, hd] at e
            cases hh : okHOf pl
            · rfl
            · rw [hh, if_pos rfl] at e; cases e
          rw [hu.2.1 this, hs.2.2.1]; rfl
        | some c => rw [(hcm c hd).1]; rfl
      · rw [recordOf_eq, if_neg h1, if_pos h2] at e
        cases hd : decodeCommit pl with
        | none => rw [hd] at e; cases e
        | some c' =>
          rw [hd] at e
          simp only [Option.map_some, Option.some.injEq, Record.commit.injEq] at e
          subst e
          exact (hcm c' hd).2
    · -- a start, or none
      refine frag_pure (t ≠ commitType) (fun u ⟨⟨hu, _⟩, h0⟩ => by rw [hev2 u hu] at h0; simpa using bw_eq0 h0)
        (lowK_any _ (k := .skip) (c := _) rfl) fun h2 => ?_
      have hev3 : ∀ u, Q2 u → eval u (.op .and_ (.cmp .equal (.var "jt") (.const (BitVec.ofNat 64 startType)))
          (.cmp .equal (.var "jpl") (.const 0))) = some (bw (decide (t = startType) && decide (pl.length = 0))) :=
        fun u hu => eval_and (eval_eq (a := .var "jt") (by omega) (by decide) (hjt u hu.1) rfl)
          (eval_eq (a := .var "jpl") (y := 0) (by omega) (by decide) (hjpl u hu.1) rfl)
      refine frag_ite o (C := .op .and_ (.cmp .equal (.var "jt") (.const (BitVec.ofNat 64 startType)))
        (.cmp .equal (.var "jpl") (.const 0))) rfl hQ3c (fun u hu => ⟨_, hev3 u hu.1.1⟩) ?_ (noDecl _ rfl)
        (frag_nil o fun u ⟨⟨⟨hu, _⟩, _⟩, h0⟩ => ?_) (noDecl _ rfl)
      · refine set_frag o (E := .op .add (.var "jz") (.const (BitVec.ofNat 64 startType))) rfl hQ3c
          fun u ⟨⟨⟨hu, _⟩, _⟩, hne⟩ => ?_
        rw [hev3 u hu] at hne
        have hs := bw_ne0 hne
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hs
        refine ⟨BitVec.ofNat 64 startType, by simp [eval, (hlocal u hu.1 "jz" (by decide)).trans h.jz],
          ⟨_, hu.2.2.1⟩, kept_set hu.1 (by decide) _, by simp [setL, setLocal, hu.2.1], ?_,
          by simp [setL, setLocal, hu.2.2.2], fun c e => ?_⟩
        · rw [hrt, if_neg h1, if_neg h2, if_pos hs.1, if_pos hs.2]; simp [setL, setLocal]; rfl
        · rw [recordOf_eq, if_neg h1, if_neg h2, if_pos hs.1, if_pos hs.2] at e; cases e
      · rw [hev3 u hu] at h0
        have hs := bw_eq0 h0
        refine ⟨hu.1, hu.2.1, ?_, hu.2.2.2, fun c e => ?_⟩
        · rw [hrt, if_neg h1, if_neg h2]
          by_cases h3 : t = startType
          · rw [if_pos h3, if_neg (by simpa [h3] using hs)]; exact hu.2.2.1
          · rw [if_neg h3]; exact hu.2.2.1
        · rw [recordOf_eq, if_neg h1, if_neg h2] at e
          by_cases h3 : t = startType
          · rw [if_pos h3] at e; split at e <;> cases e
          · rw [if_neg h3] at e; cases e
  · -- none: `notARecord`
    have hrt0 : recType t pl = 0 ↔ Journal.recordOf spec t pl = none := by
      unfold recType
      cases Journal.recordOf spec t pl with
      | none => simp
      | some r => cases r <;> simp [Record.type, formatType, commitType, startType]
    have hev : ∀ u, Q3 u → eval u (.cmp .equal (.var "jrec") (.const 0)) = some (bw (decide (recType t pl = 0))) :=
      fun u hu => eval_eq (a := .var "jrec") (y := 0) (Nat.lt_of_le_of_lt (recType_le t pl) (by decide)) (by decide)
        hu.2.2.1 rfl
    refine frag_ite o (C := .cmp .equal (.var "jrec") (.const 0)) rfl recOut_clock (fun u hu => ⟨_, hev u hu⟩) ?_
      (noDecl _ rfl) (frag_nil o fun u ⟨hu, h0⟩ => ?_) (noDecl _ rfl)
    · refine set_frag o (E := .op .add (.var "jz") (.const (BitVec.ofNat 64 (whyCode .notARecord)))) rfl recOut_clock
        fun u ⟨hu, hne⟩ => ?_
      rw [hev u hu] at hne
      have hz := bw_ne0 hne
      simp only [decide_eq_true_eq] at hz
      have hnone := hrt0.mp hz
      exact ⟨BitVec.ofNat 64 (whyCode .notARecord), by simp [eval, (hlocal u hu.1 "jz" (by decide)).trans h.jz],
        ⟨_, hu.2.2.2.1⟩,
        kept_set hu.1 (by decide) _, by simp [setL, setLocal, hu.2.1], by simp [setL, setLocal, hu.2.2.1],
        by simp [setL, setLocal, hnone], fun c e => by rw [hnone] at e; cases e⟩
    · rw [hev u hu] at h0
      have hz := bw_eq0 h0
      simp only [decide_eq_false_iff_not] at hz
      have hsome : (Journal.recordOf spec t pl).isSome = true := by
        cases e : Journal.recordOf spec t pl
        · exact absurd (hrt0.mpr e) hz
        · rfl
      exact ⟨hu.1, hu.2.1, hu.2.2.1, by rw [if_pos hsome]; exact hu.2.2.2.1, hu.2.2.2.2⟩

/-! ## The premises can hold -/

section Witness

/-- A state of the area at zero: the window at its place, the frame at its start, an empty payload. -/
def zLocals (x : String) : Option Value :=
  if x = "jw" ∨ x = "jf" then some (at_ 0 sWindow)
  else if x = "jpp" then some (at_ 0 (sWindow + 0 + 13))
  else if x = "ji" then some (BitVec.ofNat 64 22)
  else some 0

/-- Its memory: the Message-ID's place and the first group's. -/
def zMem (a : Word) : Word :=
  if a = at_ 0 sIdAt then BitVec.ofNat 64 22 else if a = at_ 0 sGroups then BitVec.ofNat 64 13 else 0

/-- A state with these locals and memory, every word addressable. -/
def zState : PancakeState Unit := { bareState () with locals := zLocals, memory := zMem, memaddrs := fun _ => true }

theorem dom_witness : Dom 0 zState.memaddrs := fun _ _ => rfl

theorem msgW_witness : MsgW 0 (at_ 0 sMessage) := ⟨sMessage, Nat.le_refl _, by decide, rfl⟩

theorem kept_witness : Kept [] (fun _ => False) zState zState := kept_refl _ _ _

theorem stable_witness : Stable (σ := Unit) [] (fun _ => False) (fun _ => True) := fun _ _ _ _ => trivial

theorem zBound (y : String) : ∃ v, zState.locals y = some v := by
  simp only [zState, zLocals]; split
  · exact ⟨_, rfl⟩
  · split
    · exact ⟨_, rfl⟩
    · split <;> exact ⟨_, rfl⟩

theorem fwIn_witness : FwIn false 0 none 0 0 [] zState where
  hA := by decide
  dom := dom_witness
  sp := rfl
  jz := rfl
  jq := rfl
  jf := rfl
  jr := rfl
  jky := fun _ => rfl
  keyed := fun h => by cases h
  key := fun _ h => by cases h
  bytes := fun i h => by simp at h
  room := by decide
  q := by decide
  len := by decide
  bound := fun y _ => zBound y

theorem fwOut_witness : FwOut 0 none 0 [] zState (setL zState "jwhy" (BitVec.ofNat 64 1)) where
  kept := kept_set (kept_refl _ _ _) (by decide) _
  why := rfl
  len := fun h => by simp [fault, headerLength] at h
  type := fun h => by simp [fault, headerLength] at h

theorem keyIn_witness : KeyIn 0 (at_ 0 sWindow) none 0 [] zState where
  sp := rfl
  jz := rfl
  key := fun _ h => by cases h
  jt := rfl
  jpl := rfl
  jf := rfl
  payload := fun i h => by simp at h
  k := zBound _
  jhk := zBound _
  short := by decide

theorem mBase_witness : MBase 0 zState (fun _ => True) 0 0 zState := ⟨kept_refl _ _ _, trivial, rfl, rfl⟩

theorem decIn_witness : DecIn 0 0 [] zState where
  hA := by decide
  dom := dom_witness
  sp := rfl
  jz := rfl
  jw := rfl
  jo := rfl
  jpp := rfl
  jpl := rfl
  payload := fun i h => by simp at h
  room := by decide
  len := by decide
  bound := fun y _ => zBound y
  jrec := zBound _

theorem dAt_witness : DAt 0 zState false zState := ⟨kept_refl _ _ _, ⟨22, rfl, by decide⟩, rfl⟩

theorem slotAt_witness : SlotAt 0 0 [] 0 ⟨[], 0⟩ zState := ⟨0, by decide, by decide, by decide, rfl, Nat.le_refl _⟩

theorem twoSlots_witness : TwoSlots 0 0 [] 0 0 ⟨[], 0⟩ ⟨[], 0⟩ zState := ⟨slotAt_witness, slotAt_witness, rfl, rfl⟩

theorem bFacts_witness : BFacts 0 0 [] zState := ⟨rfl, rfl, by decide, by decide⟩

theorem tFacts_witness : TFacts 0 0 [] zState := fun r hr => by
  have : r = ([], 10) := by simp [scanGroups, gcOf, mlOf] at hr; exact hr.symm
  subst this
  exact ⟨rfl, rfl, bFacts_witness, fun h hh => by simp at hh, rfl, rfl, rfl⟩

theorem decOut_witness : DecOut 0 zState 0 [] zState :=
  ⟨⟨kept_refl _ _ _, ⟨22, rfl, by decide⟩, by decide⟩, fun _ => rfl,
    fun h => absurd h (by decide)⟩

theorem recIn_witness : RecIn 0 0 0 [] zState where
  hA := by decide
  dom := dom_witness
  sp := rfl
  jz := rfl
  jw := rfl
  jo := rfl
  jf := rfl
  jt := rfl
  jpl := rfl
  jwhy := rfl
  payload := fun i h => by simp at h
  room := by decide
  len := by decide
  ht := by decide
  bound := fun y _ => zBound y

theorem recOut_witness : RecOut 0 0 0 [] zState (setL zState "jwhy" (BitVec.ofNat 64 (whyCode .notARecord))) where
  kept := kept_set (kept_refl _ _ _) (by decide) _
  jpp := rfl
  jrec := by decide
  why := by decide
  commit := fun c h => absurd h (by rw [recordOf_eq]; simp [formatType, commitType, startType])

end Witness

end DN.News.ScanRun
