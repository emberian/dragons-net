-- SPDX-License-Identifier: AGPL-3.0-or-later
import DN.News.ScanRun

/-!
# DN.News.ScanRecord

The record a checked frame holds, as the scanner reads it. `scanCommit` reads a commit's payload field after
field, refusing each as soon as it cannot be one a correct store writes, in the order `ScanProg.decode`
reads them; it is `Journal.decodeCommit` (`scanCommit_eq`).
-/

namespace DN.News.ScanRun

open DN.News DN.News.Journal

/-- A group's name and number within the bounds a correct store writes. -/
def bounded (g : Group) : Bool :=
  1 ≤ g.name.length && g.name.length ≤ 64 && 1 ≤ g.number && g.number < 2 ^ 31

/-- One group at `i`, as the scanner reads it: the group and where it ends. -/
def oneGroup (pl : Bytes) (i : Nat) : Option (Group × Nat) :=
  if pl.length < i + 1 then none
  else if pl.length < i + 1 + (pl.getD i 0).toNat then none
  else if pl.length < i + 1 + (pl.getD i 0).toNat + 4 then none
  else if bounded ⟨(pl.drop (i + 1)).take (pl.getD i 0).toNat,
      readLE ((pl.drop (i + 1 + (pl.getD i 0).toNat)).take 4)⟩ = false then none
  else some (⟨(pl.drop (i + 1)).take (pl.getD i 0).toNat, readLE ((pl.drop (i + 1 + (pl.getD i 0).toNat)).take 4)⟩,
    i + 1 + (pl.getD i 0).toNat + 4)

/-- `n` groups from `i` in the payload, as the scanner reads them, each name's length and number checked
before the next; the groups and where they end. -/
def scanGroups (pl : Bytes) : Nat → Nat → Option (List Group × Nat)
  | 0, i => some ([], i)
  | n + 1, i => (oneGroup pl i).bind fun r => (scanGroups pl n r.2).map fun q => (r.1 :: q.1, q.2)

theorem scanGroups_succ (pl : Bytes) (n i : Nat) : scanGroups pl (n + 1) i =
    (oneGroup pl i).bind fun r => (scanGroups pl n r.2).map fun q => (r.1 :: q.1, q.2) := rfl

/-- …and one group more is read after the others. -/
theorem scanGroups_snoc (pl : Bytes) : ∀ n i, scanGroups pl (n + 1) i =
    (scanGroups pl n i).bind fun r => (oneGroup pl r.2).map fun q => (r.1 ++ [q.1], q.2)
  | 0, i => by
    rw [scanGroups_succ]
    simp only [scanGroups, Option.bind_some, List.nil_append]
    cases oneGroup pl i <;> rfl
  | n + 1, i => by
    rw [scanGroups_succ, scanGroups_succ]
    cases oneGroup pl i with
    | none => rfl
    | some r =>
      simp only [Option.bind_some]
      rw [scanGroups_snoc pl n r.2]
      cases scanGroups pl n r.2 with
      | none => rfl
      | some q =>
        simp only [Option.bind_some, Option.map_some]
        cases oneGroup pl q.2 <;> rfl

theorem oneGroup_le {pl : Bytes} {i : Nat} {r : Group × Nat} (h : oneGroup pl i = some r) :
    i + 1 + r.1.name.length + 4 = r.2 ∧ r.2 ≤ pl.length ∧ r.1.name = (pl.drop (i + 1)).take r.1.name.length ∧
      r.1.number = readLE ((pl.drop (i + 1 + r.1.name.length)).take 4) ∧ bounded r.1 = true := by
  simp only [oneGroup] at h
  split at h
  · cases h
  split at h
  · cases h
  split at h
  · cases h
  split at h
  · cases h
  rename_i h1 h2 h3 h4
  cases h
  simp only [List.length_take, List.length_drop]
  refine ⟨by omega, by omega, by rw [Nat.min_eq_left (by omega)], by rw [Nat.min_eq_left (by omega)], ?_⟩
  simpa using h4

theorem scanGroups_le {pl : Bytes} : ∀ {n i : Nat} {r : List Group × Nat}, scanGroups pl n i = some r →
    r.1.length = n ∧ i ≤ r.2 ∧ (n ≠ 0 → r.2 ≤ pl.length)
  | 0, i, r, h => by simp [scanGroups] at h; subst h; simp
  | n + 1, i, r, h => by
    rw [scanGroups_snoc] at h
    cases hs : scanGroups pl n i with
    | none => rw [hs] at h; cases h
    | some q =>
      rw [hs] at h
      cases ho : oneGroup pl q.2 with
      | none => simp [ho] at h
      | some g =>
        simp [ho] at h
        subst h
        obtain ⟨h1, h2, h3⟩ := scanGroups_le hs
        obtain ⟨e1, e2, -⟩ := oneGroup_le ho
        simp only [List.length_append, List.length_singleton]
        omega

theorem scanGroups_bounded {pl : Bytes} : ∀ {n i : Nat} {r : List Group × Nat}, scanGroups pl n i = some r →
    ∀ g ∈ r.1, bounded g = true
  | 0, i, r, h => by simp [scanGroups] at h; subst h; simp
  | n + 1, i, r, h => by
    rw [scanGroups_snoc] at h
    cases hs : scanGroups pl n i with
    | none => rw [hs] at h; cases h
    | some q =>
      rw [hs] at h
      cases ho : oneGroup pl q.2 with
      | none => simp [ho] at h
      | some g =>
        simp [ho] at h
        subst h
        intro x hx
        simp only [List.mem_append, List.mem_singleton] at hx
        rcases hx with hx | rfl
        · exact scanGroups_bounded hs x hx
        · exact (oneGroup_le ho).2.2.2.2

theorem scanGroups_none {pl : Bytes} {i : Nat} : ∀ {n m : Nat}, n ≤ m → scanGroups pl n i = none →
    scanGroups pl m i = none
  | n, m, hnm, h => by
    induction m with
    | zero => have : n = 0 := by omega
              subst this; exact h
    | succ m ih =>
      by_cases e : n = m + 1
      · subst e; exact h
      · rw [scanGroups_snoc, ih (by omega)]; rfl

theorem scanGroups_eq (pl : Bytes) : ∀ n i, i ≤ pl.length →
    scanGroups pl n i = (takeGroups n (pl.drop i)).bind fun r =>
      if r.1.all bounded then some (r.1, pl.length - r.2.length) else none
  | 0, i, hi => by simp [scanGroups, takeGroups]; omega
  | n + 1, i, hi => by
    simp only [scanGroups, oneGroup]
    by_cases h1 : pl.length < i + 1
    · rw [if_pos h1]
      have : pl.drop i = [] := List.drop_eq_nil_of_le (by omega)
      simp [this, takeGroups, takeGroup, takeCounted]
    rw [if_neg h1]
    have hd : pl.drop i = pl[i] :: pl.drop (i + 1) := List.drop_eq_getElem_cons (by omega)
    have hg : pl.getD i 0 = pl[i] := by
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show i < pl.length by omega)]
    rw [hg, hd]
    have hl : (pl.drop (i + 1)).length = pl.length - (i + 1) := List.length_drop
    by_cases h2 : pl.length < i + 1 + pl[i].toNat
    · rw [if_pos h2]
      simp [takeGroups, takeGroup, takeCounted, show ¬ pl[i].toNat ≤ pl.length - (i + 1) by omega]
    rw [if_neg h2]
    by_cases h3 : pl.length < i + 1 + pl[i].toNat + 4
    · rw [if_pos h3]
      simp [takeGroups, takeGroup, takeCounted, takeLE, show pl[i].toNat ≤ pl.length - (i + 1) by omega,
        List.drop_drop, show ¬ 4 ≤ pl.length - (i + 1 + pl[i].toNat) by omega]
    rw [if_neg h3]
    have ih := scanGroups_eq pl n (i + 1 + pl[i].toNat + 4) (by omega)
    have hle1 : pl[i].toNat ≤ pl.length - (i + 1) := by omega
    have hle2 : 4 ≤ pl.length - (i + 1 + pl[i].toNat) := by omega
    simp only [takeGroups, takeGroup, takeCounted, takeLE, List.length_drop, hle1, if_true, List.drop_drop]
    by_cases h4 : bounded ⟨(pl.drop (i + 1)).take pl[i].toNat, readLE ((pl.drop (i + 1 + pl[i].toNat)).take 4)⟩ = false
    · rw [if_pos h4]
      cases hT : takeGroups n (List.drop (i + 1 + pl[i].toNat + 4) pl) <;> simp [hT, h4, hle2]
    · rw [if_neg h4, Option.bind_some, ih]
      have h4' :
          bounded ⟨(pl.drop (i + 1)).take pl[i].toNat, readLE ((pl.drop (i + 1 + pl[i].toNat)).take 4)⟩ = true := by
        simpa using h4
      cases hT : takeGroups n (List.drop (i + 1 + pl[i].toNat + 4) pl) with
      | none => simp [hT, hle2]
      | some r =>
        simp [hT, h4', hle2]

theorem takeGroups_length : ∀ (n : Nat) (bs : Bytes) {gs : List Group} {r : Bytes},
    takeGroups n bs = some (gs, r) → gs.length = n
  | 0, bs, gs, r, h => by simp [takeGroups] at h; rw [h.1]; rfl
  | n + 1, bs, gs, r, h => by
    simp only [takeGroups] at h
    cases hg : takeGroup bs with
    | none => rw [hg] at h; cases h
    | some p =>
      rw [hg] at h
      cases ht : takeGroups n p.2 with
      | none => simp [ht] at h
      | some q =>
        simp [ht] at h
        rw [← h.1, List.length_cons, takeGroups_length n p.2 ht]

/-- The commit a payload holds, as the scanner reads it: each field refused as soon as it cannot be one a
correct store writes. -/
def scanCommit (pl : Bytes) : Option Commit :=
  if pl.length < 9 + (pl.getD 8 0).toNat + 1 then none
  else if 16 < (pl.getD (9 + (pl.getD 8 0).toNat) 0).toNat then none
  else match scanGroups pl (pl.getD (9 + (pl.getD 8 0).toNat) 0).toNat (10 + (pl.getD 8 0).toNat) with
  | none => none
  | some (gs, k) =>
    if k + 12 ≠ pl.length then none
    else if readLE (pl.take 8) = 0 ∨ (pl.getD 8 0).toNat < 1 ∨ 250 < (pl.getD 8 0).toNat ∨
        (pl.getD (9 + (pl.getD 8 0).toNat) 0).toNat < 1 ∨
        readLE ((pl.drop (k + 4)).take 4) < readLE ((pl.drop k).take 4) then none
    else if (gs.map Group.name).Nodup then
      some ⟨readLE (pl.take 8), (pl.drop 9).take (pl.getD 8 0).toNat, gs, readLE ((pl.drop k).take 4),
        readLE ((pl.drop (k + 4)).take 4), readLE ((pl.drop (k + 8)).take 4)⟩
    else none

theorem takeGroups_drop : ∀ (n : Nat) (bs : Bytes) {gs : List Group} {r : Bytes},
    takeGroups n bs = some (gs, r) → ∃ j, j ≤ bs.length ∧ r = bs.drop j
  | 0, bs, gs, r, h => by simp [takeGroups] at h; exact ⟨0, Nat.zero_le _, by rw [← h.2]; rfl⟩
  | n + 1, bs, gs, r, h => by
    simp only [takeGroups, takeGroup, takeCounted, takeLE] at h
    cases bs with
    | nil => simp at h
    | cons b rest =>
      by_cases h1 : b.toNat ≤ rest.length
      · by_cases h2 : 4 ≤ rest.length - b.toNat
        · simp [h1, h2] at h
          cases ht : takeGroups n (List.drop (b.toNat + 4) rest) with
          | none => simp [ht] at h
          | some q =>
            simp [ht] at h
            obtain ⟨j, hj, e⟩ := takeGroups_drop n _ ht
            refine ⟨1 + (b.toNat + 4) + j, by simp at hj ⊢; omega, ?_⟩
            rw [← h.2, e, List.drop_drop, show 1 + (b.toNat + 4) + j = (b.toNat + 4 + j) + 1 by omega,
              List.drop_succ_cons]
        · simp [h1, h2] at h
      · simp [h1] at h

/-- What `decodeCommit` does after the groups: three numbers, nothing after them, and the commit checked. -/
def tailOf (seq : Nat) (mid : Bytes) (gs : List Group) (rest : Bytes) : Option Commit := do
  let (headerSize, bs) ← takeLE 4 rest
  let (fileSize, bs) ← takeLE 4 bs
  let (fileCrc, bs) ← takeLE 4 bs
  let c : Commit := ⟨seq, mid, gs, headerSize, fileSize, fileCrc⟩
  if bs.isEmpty && c.ok then some c else none

theorem tailOf_eq (seq : Nat) (mid : Bytes) (gs : List Group) (rest : Bytes) :
    tailOf seq mid gs rest = if rest.length = 12 then
      (if (Commit.mk seq mid gs (readLE (rest.take 4)) (readLE ((rest.drop 4).take 4))
          (readLE ((rest.drop 8).take 4))).ok then
        some ⟨seq, mid, gs, readLE (rest.take 4), readLE ((rest.drop 4).take 4), readLE ((rest.drop 8).take 4)⟩
      else none) else none := by
  unfold tailOf
  simp only [Option.bind_eq_bind, takeLE]
  by_cases h4 : 4 ≤ rest.length
  · rw [if_pos h4, Option.bind_some]
    by_cases h8 : 4 ≤ (rest.drop 4).length
    · rw [if_pos h8, Option.bind_some]
      by_cases h12 : 4 ≤ ((rest.drop 4).drop 4).length
      · rw [if_pos h12, Option.bind_some]
        simp only [List.drop_drop]
        by_cases hl : rest.length = 12
        · have he : (rest.drop (4 + 4 + 4)).isEmpty = true := by
            simp only [List.isEmpty_iff, List.drop_eq_nil_iff]; omega
          rw [if_pos hl, he, Bool.true_and]
        · have he : (rest.drop (4 + 4 + 4)).isEmpty = false := by
            simp only [List.isEmpty_eq_false_iff, ne_eq, List.drop_eq_nil_iff]
            simp only [List.length_drop] at h12; omega
          rw [if_neg hl, he, Bool.false_and]; rfl
      · rw [if_neg h12, Option.bind_none, if_neg (by simp only [List.length_drop] at h12; omega)]
    · rw [if_neg h8, Option.bind_none, if_neg (by simp only [List.length_drop] at h8; omega)]
  · rw [if_neg h4, Option.bind_none, if_neg (by omega)]

/-- `decodeCommit` past the Message-ID: the groups, then the rest. -/
theorem decodeCommit_bind (pl : Bytes) (h9 : ¬ pl.length < 9) (h1 : ¬ pl.length < 9 + (pl[8]'(by omega)).toNat + 1) :
    decodeCommit pl = (takeGroups (pl[9 + (pl[8]'(by omega)).toNat]'(by omega)).toNat
      (pl.drop (10 + (pl[8]'(by omega)).toNat))).bind
      fun r => tailOf (readLE (pl.take 8)) ((pl.drop 9).take (pl[8]'(by omega)).toNat) r.1 r.2 := by
  have hd8 : pl.drop 8 = pl[8] :: pl.drop 9 := List.drop_eq_getElem_cons (by omega)
  have hdm : pl.drop (9 + pl[8].toNat) = pl[9 + pl[8].toNat] :: pl.drop (10 + pl[8].toNat) := by
    rw [List.drop_eq_getElem_cons (by omega)]; congr 2; omega
  have hm : pl[8].toNat ≤ pl.length - 9 := by omega
  simp only [decodeCommit, Option.bind_eq_bind, takeLE, if_pos (show 8 ≤ pl.length by omega), Option.bind_some,
    hd8, takeCounted, List.length_drop, if_pos hm, List.drop_drop, hdm, Bool.not_true, Bool.or_false]
  rfl

theorem scanCommit_eq (pl : Bytes) : scanCommit pl = decodeCommit pl := by
  unfold scanCommit
  by_cases h9 : pl.length < 9
  · rw [if_pos (by omega)]
    symm
    by_cases h8 : pl.length < 8
    · simp only [decodeCommit, Option.bind_eq_bind, takeLE, if_neg (show ¬ 8 ≤ pl.length by omega), Option.bind_none]
    · have : pl.drop 8 = [] := List.drop_eq_nil_of_le (by omega)
      simp only [decodeCommit, Option.bind_eq_bind, takeLE, if_pos (show 8 ≤ pl.length by omega), Option.bind_some,
        this, takeCounted, Option.bind_none]
  have hd8 : pl.drop 8 = pl[8] :: pl.drop 9 := List.drop_eq_getElem_cons (by omega)
  have hg8 : pl.getD 8 0 = pl[8] := by
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show 8 < pl.length by omega)]
  rw [hg8]
  by_cases h1 : pl.length < 9 + pl[8].toNat + 1
  · rw [if_pos h1]
    symm
    by_cases hm : pl[8].toNat ≤ pl.length - 9
    · have : pl.drop (9 + pl[8].toNat) = [] := List.drop_eq_nil_of_le (by omega)
      simp only [decodeCommit, Option.bind_eq_bind, takeLE, if_pos (show 8 ≤ pl.length by omega), Option.bind_some,
        hd8, takeCounted, List.length_drop, if_pos hm, List.drop_drop, this, Option.bind_none]
    · simp only [decodeCommit, Option.bind_eq_bind, takeLE, if_pos (show 8 ≤ pl.length by omega), Option.bind_some,
        hd8, takeCounted, List.length_drop, if_neg hm, Option.bind_none]
  rw [if_neg h1]
  have hdm : pl.drop (9 + pl[8].toNat) = pl[9 + pl[8].toNat] :: pl.drop (10 + pl[8].toNat) := by
    rw [List.drop_eq_getElem_cons (by omega)]; congr 2; omega
  have hgm : pl.getD (9 + pl[8].toNat) 0 = pl[9 + pl[8].toNat] := by
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show 9 + pl[8].toNat < pl.length by omega)]
  rw [hgm, scanGroups_eq pl _ _ (by omega)]
  have hdec := decodeCommit_bind pl h9 h1
  rw [hdec]
  have hid : ((pl.drop 9).take pl[8].toNat).length = pl[8].toNat := by simp; omega
  cases hT : takeGroups (pl[9 + pl[8].toNat]).toNat (pl.drop (10 + pl[8].toNat)) with
  | none => simp only [Option.bind_none]; split <;> rfl
  | some r =>
    obtain ⟨gs, rest⟩ := r
    obtain ⟨j, hj, hr⟩ := takeGroups_drop _ _ hT
    have hgl := takeGroups_length _ _ hT
    simp only [List.length_drop] at hj
    subst hr
    simp only [Option.bind_some, tailOf_eq, List.drop_drop, List.length_drop]
    clear hdec hgm hdm hd8 hg8 hT
    have l0 : pl.length - (pl.length - (10 + pl[8].toNat + j)) = 10 + pl[8].toNat + j := by omega
    rw [l0]
    have hseq := readLE_take_lt pl 8
    have hfs := readLE_take_lt (pl.drop (10 + pl[8].toNat + j + 4)) 4
    have hcrc := readLE_take_lt (pl.drop (10 + pl[8].toNat + j + 8)) 4
    have hall : (gs.all fun g => 1 ≤ g.name.length && g.name.length ≤ 64 && 1 ≤ g.number && g.number < 2 ^ 31) =
        gs.all bounded := rfl
    by_cases hg16 : 16 < pl[9 + pl[8].toNat].toNat
    · rw [if_pos hg16]
      split
      · rw [if_neg]
        simp [Commit.ok, hgl]; omega
      · rfl
    rw [if_neg hg16]
    by_cases hb : gs.all bounded = true
    · rw [if_pos hb]
      simp only
      by_cases hL : pl.length - (10 + pl[8].toNat + j) = 12
      · rw [if_neg (show ¬ (10 + pl[8].toNat + j + 12 ≠ pl.length) by omega), if_pos hL]
        by_cases hbad : readLE (pl.take 8) = 0 ∨ pl[8].toNat < 1 ∨ 250 < pl[8].toNat ∨
            pl[9 + pl[8].toNat].toNat < 1 ∨ readLE ((pl.drop (10 + pl[8].toNat + j + 4)).take 4) <
              readLE ((pl.drop (10 + pl[8].toNat + j)).take 4)
        · rw [if_pos hbad, if_neg]
          simp only [Commit.ok, hid, hgl, hall, hb, Bool.and_eq_true, decide_eq_true_eq]
          omega
        · rw [if_neg hbad]
          by_cases hnd : (gs.map Group.name).Nodup
          · rw [if_pos hnd, if_pos]
            simp only [Commit.ok, hid, hgl, hall, hb, hnd, Bool.and_eq_true, decide_eq_true_eq, decide_true, and_true]
            omega
          · rw [if_neg hnd, if_neg]
            simp [Commit.ok, hnd]
      · rw [if_pos (show 10 + pl[8].toNat + j + 12 ≠ pl.length by omega), if_neg hL]
    · rw [if_neg hb]
      simp only
      split
      · rw [if_neg]
        simp only [Commit.ok, hall, hb, Bool.and_eq_true, Bool.false_eq_true, and_false, false_and,
          not_false_eq_true]
      · rfl

end DN.News.ScanRun
