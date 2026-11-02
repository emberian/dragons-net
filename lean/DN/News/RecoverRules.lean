-- SPDX-License-Identifier: AGPL-3.0-or-later
import DN.News.RecoverSlots

/-!
# DN.News.RecoverRules

Recovery's phase 4 as the program runs it (`RecoverProg.rules`) is `RecoverSpec.rules`: the commits checked for a
number or Message-ID twice, a group the configuration lacks, numbers that do not rise.
-/

namespace DN.News.RecoverArea

open DN.Compiler DN.Compiler.Wp DN.Compiler.Frag DN.Compiler.Bytes DN.News.Journal DN.News.Recovery
open DN.News.RecoverProg
open DN.News.RecoverSpec (RSt hits hits_succ hits_le hits_mono firstIdx firstIdx_succ firstIdx_lt firstIdx_some
  firstIdx_mono firstIdx_isSome dupAt dupAt_hits bytes_take_succ_iff find_first)
open DN.News.ScanRun (at_ at_add vals_lookup kept_has without lookup_head frag_if)
open DN.News.FramerCode (bw ev_var)

variable {σ : Type}

/-- The search for a number two commits have, inner loop: whether one after `k` has `k`'s. -/
theorem seqInner_frag (o : Oracle σ) {A : Word} {cfg : Config} {J : Bytes} {r : RSt} {s0 : PancakeState σ}
    (h : PBase A s0) (hsq : ∀ c ∈ r.commits, c.seq < 2 ^ 64) (hcap : r.commits.length ≤ capacity)
    {k : Nat} (hk : k < r.commits.length) :
    Frag o seqInner (Mid A cfg J r s0 (scalars cfg r) [] [("rj", .ofNat 64 (k + 1)), ("rdup", bw false),
        ("rv", .ofNat 64 r.commits[k].seq), ("ri", .ofNat 64 k), ("rcm", .ofNat 64 r.commits.length), ("rgo", 1)])
      (Mid A cfg J r s0 (scalars cfg r) [] [("rdup", bw (dupAt (·.seq) r.commits k)),
        ("rv", .ofNat 64 r.commits[k].seq), ("ri", .ofNat 64 k), ("rcm", .ofNat 64 r.commits.length), ("rgo", 1)]) := by
  have hn := nums
  let n := r.commits.length
  let L (j : Nat) : List (String × Value) := [("rj", .ofNat 64 j), ("rdup", bw (hits (·.seq) r.commits k j)),
    ("rv", .ofNat 64 r.commits[k].seq), ("ri", .ofNat 64 k), ("rcm", .ofNat 64 n), ("rgo", 1)]
  let I (j : Nat) : Assn σ := fun u => Mid A cfg J r s0 (scalars cfg r) [] (L j) u ∧ k + 1 ≤ j ∧ j ≤ n
  have hIc : ∀ j, Safe.ClockFree (I j) := fun _ s c ⟨h1, h2⟩ => ⟨mid_clock s c h1, h2⟩
  have hsk := hsq _ (List.getElem_mem hk)
  refine frag_conseq (frag_count o (c := Syntax.eLt (Syntax.v "rj") (Syntax.v "rcm"))
    (C := .cmp .less (.var "rj") (.var "rcm")) rfl (lowK_any _ (k := .skip) (c := _) rfl) hIc
    (fun j => noDecl (P' := I j) _ rfl) (g := fun j => decide (j < n)) (fun j u ⟨hu, _, _⟩ => by
      rw [FramerCode.eval_lt (t := u) (a := .var "rj") (b := .var "rcm") (x := j) (y := n)
        (by omega) (by omega) (ev_var (vals_lookup hu.vals rfl)) (ev_var (vals_lookup hu.vals rfl))]
      rfl) (fun j hj => ?_) (k + 1)) (fun u hu => ⟨mid_lookups hu ⟨rfl, by
        rw [hits_le _ _ _ _ (Nat.le_refl _)]; rfl, rfl, rfl, rfl, rfl, trivial⟩, Nat.le_refl _, hk⟩) ?_
  · refine frag_pure (k + 1 ≤ j) (fun _ h => h.2.1) (lowK_any _ (k := .skip) (c := _) rfl) fun hkj => ?_
    have hj' : j < n := of_decide_eq_true hj
    have hjc : j < capacity := by omega
    have hsj := hsq _ (List.getElem_mem hj')
    let L2 : List (String × Value) := [("rsl", at_ A (slotAt j)), ("rj", .ofNat 64 j),
      ("rdup", bw (hits (·.seq) r.commits k (j + 1))), ("rv", .ofNat 64 r.commits[k].seq),
      ("ri", .ofNat 64 k), ("rcm", .ofNat 64 n), ("rgo", 1)]
    refine frag_conseq (P0 := Mid A cfg J r s0 (scalars cfg r) [] (L j))
      (P0' := Mid A cfg J r s0 (scalars cfg r) [] (("rj", .ofNat 64 (j + 1)) :: without "rj" L2)) ?_ (fun _ h => h.1)
      fun u hu => ⟨mid_lookups hu ⟨rfl, rfl, rfl, rfl, rfl, rfl, trivial⟩, by omega, hj'⟩
    rotate_left
    refine frag_append (xs := [_]) (mid_slotAt o h (y := "rsl") (by decide) (x := "rj") (i := j) rfl) ?_
    refine frag_append (xs := [_]) (M := Mid A cfg J r s0 (scalars cfg r) [] L2) ?_ ?_
    · refine frag_if o (C := .cmp .equal (slotWE slotSeq) (.var "rv")) rfl
        (lowK_any _ (k := .skip) (c := _) rfl) (fun k => ⟨k, rfl⟩) rfl rfl mid_clock
        (b := decide (r.commits[j].seq = r.commits[k].seq))
        (fun u hu => FramerCode.eval_eq hsj hsk ((slotP_eval h hu hjc (p := "rsl") rfl (by decide) (by decide)).trans
          (congrArg some ((hu.rest.slots j hj' hjc).seq))) (ev_var (vals_lookup hu.vals rfl))) (fun e => ?_) fun e => ?_
      · have ht : hits (·.seq) r.commits k (j + 1) = true := by
          rw [hits_succ]
          simp [List.getElem?_eq_getElem hj', List.getElem?_eq_getElem hk, of_decide_eq_true e]; omega
        refine frag_conseq (mid_assign o h (y := "rdup") (by decide) (E := .op .add (.var "jz") (.const 1)) rfl
          (val := bw true) fun u hu => by simp [eval, jz_kept h hu.kept, bw]) (fun _ h => h) fun u hu => ?_
        exact mid_lookups hu ⟨rfl, rfl, by rw [ht]; rfl, rfl, rfl, rfl, rfl, trivial⟩
      · have ht : hits (·.seq) r.commits k (j + 1) = hits (·.seq) r.commits k j := by
          rw [hits_succ]
          have : r.commits[j].seq ≠ r.commits[k].seq := of_decide_eq_false e
          simp [List.getElem?_eq_getElem hj', List.getElem?_eq_getElem hk, this]
        exact frag_nil o fun u hu => mid_lookups hu ⟨rfl, rfl, by rw [ht]; rfl, rfl, rfl, rfl, rfl, trivial⟩
    · exact mid_assign o h (y := "rj") (by decide) (E := .op .add (.var "rj") (.const (.ofNat 64 1))) rfl
        (val := .ofNat 64 (j + 1)) fun u hu =>
            by simp only [eval, vals_lookup hu.vals (x := "rj") rfl, BitVec.ofNat_add]
  intro u ⟨j, ⟨hu, _, hjn⟩, hgj⟩
  have : j = n := by simp only [decide_eq_false_iff_not] at hgj; omega
  subst this
  exact mid_lookups hu ⟨by rw [dupAt_hits _ hk]; rfl, rfl, rfl, rfl, rfl, trivial⟩

/-- **Two commits with one number** searched for: the first commit a later one repeats, its number in `rv`. -/
theorem seqDups_frag (o : Oracle σ) {A : Word} {cfg : Config} {J : Bytes} {r : RSt} {s0 : PancakeState σ}
    (h : PBase A s0) (hsq : ∀ c ∈ r.commits, c.seq < 2 ^ 64) (hcap : r.commits.length ≤ capacity) :
    Frag o seqDups (Mid A cfg J r s0 (scalars cfg r) [] [("rcm", .ofNat 64 r.commits.length), ("rgo", 1)])
      (fun u => Mid A cfg J r s0 (scalars cfg r) [] [("ri", .ofNat 64 ((firstIdx
          (dupAt (·.seq) r.commits) r.commits.length).getD r.commits.length)),
        ("rdup", bw (firstIdx (dupAt (·.seq) r.commits) r.commits.length).isSome),
        ("rcm", .ofNat 64 r.commits.length), ("rgo", 1)] u ∧
        ∀ i (hi : i < r.commits.length), firstIdx (dupAt (·.seq) r.commits)
          r.commits.length = some i → u.locals "rv" = some (.ofNat 64 r.commits[i].seq)) := by
  have hn := nums
  let n := r.commits.length
  let R (k : Nat) (f : Option Nat) : Assn σ := fun u => Mid A cfg J r s0 (scalars cfg r) []
    [("ri", .ofNat 64 (f.getD k)), ("rdup", bw f.isSome), ("rcm", .ofNat 64 n), ("rgo", 1)] u ∧
    ∀ i (hi : i < n), f = some i → u.locals "rv" = some (.ofNat 64 r.commits[i].seq)
  refine frag_append (xs := [_]) (mid_assign o h (y := "rdup") (by decide) (E := .op .add (.var "jz") (.const 0)) rfl
    (val := bw false) fun u hu => by simp [eval, jz_kept h hu.kept, bw]) ?_
  refine frag_append (xs := [_]) (mid_assign o h (y := "ri") (by decide) (E := .op .add (.var "jz") (.const 0)) rfl
    (val := .ofNat 64 0) fun u hu => by simp [eval, jz_kept h hu.kept]) ?_
  refine frag_conseq (P0 := R 0 none) (firstIdx_frag o rfl (by exact lowK_any _ (k := .skip) (c := _) rfl) rfl
    (R := R) (fun _ _ s t ⟨h1, h2⟩ => ⟨mid_clock s t h1, h2⟩)
    (fun k u hkn ⟨hu, _⟩ => search_guard (e := 1) (by decide) (by decide) (fun _ hj => (firstIdx_lt hj).1) hkn
      (by omega) (vals_lookup hu.vals rfl) (by rw [← bw_nat]; exact vals_lookup hu.vals rfl) (vals_lookup hu.vals rfl))
    (fun k hf hkn => ?_) fun _ _ _ hu => hu) (fun u hu => ⟨mid_lookups hu ⟨rfl, rfl, rfl, rfl, trivial⟩,
      fun _ _ hi => nomatch hi⟩) fun _ h => h
  have hkc : k < capacity := by omega
  refine frag_conseq (P0 := Mid A cfg J r s0 (scalars cfg r) [] [("ri", .ofNat 64 k), ("rdup", bw false),
    ("rcm", .ofNat 64 n), ("rgo", 1)]) ?_ (fun u hu => hu.1) fun _ h => h
  refine frag_append (xs := [_]) (mid_slotAt o h (y := "rsl") (by decide) (x := "ri") (i := k) rfl) ?_
  refine frag_append (xs := [_]) (mid_assign o h (y := "rv") (by decide) (slotW_lower slotSeq)
    (val := .ofNat 64 r.commits[k].seq) fun u hu => (slotP_eval h hu hkc (p := "rsl") rfl (by decide)
      (by decide)).trans (congrArg some ((hu.rest.slots k hkn hkc).seq))) ?_
  refine frag_append (xs := [_]) (mid_assign o h (y := "rj") (by decide)
    (E := .op .add (.var "ri") (.const (.ofNat 64 1))) rfl (val := .ofNat 64 (k + 1)) fun u hu => by
      simp only [eval, vals_lookup hu.vals (x := "ri") rfl, BitVec.ofNat_add]) ?_
  refine frag_append (xs := seqInner) (frag_conseq (seqInner_frag o h hsq hcap hkn)
    (fun u hu => mid_lookups hu ⟨rfl, rfl, rfl, rfl, rfl, rfl, trivial⟩) fun _ h => h) ?_
  refine frag_if o (C := .var "rdup") rfl (fun k => ⟨k, rfl⟩) (lowK_any _ (k := .skip) (c := _) rfl) rfl rfl
    (hQ := by exact fun s t ⟨h1, h2⟩ => ⟨mid_clock s t h1, h2⟩) (b := dupAt (·.seq) r.commits k) (fun u hu =>
      vals_lookup hu.vals rfl) (fun e => ?_) fun e => ?_
  · exact frag_nil o fun u hu => by
      rw [e] at hu ⊢
      exact ⟨mid_lookups hu ⟨rfl, rfl, rfl, rfl, trivial⟩, fun i _ hi => by cases hi; exact vals_lookup hu.vals rfl⟩
  · rw [e]
    refine frag_conseq (mid_assign o h (y := "ri") (by decide) (E := .op .add (.var "ri") (.const (.ofNat 64 1)))
      rfl (val := .ofNat 64 (k + 1)) fun u hu => by
        simp only [eval, vals_lookup hu.vals (x := "ri") rfl, BitVec.ofNat_add]) (fun _ h => h) fun u hu => ?_
    exact ⟨mid_lookups hu ⟨rfl, rfl, rfl, rfl, trivial⟩, fun _ _ hi => nomatch hi⟩

/-- **Two Message-IDs of one length compared**, octet by octet until one differs: `rok` whether they are the same. -/
theorem idCmp_frag (o : Oracle σ) {A : Word} {cfg : Config} {J : Bytes} {r : RSt} {s0 : PancakeState σ}
    (h : PBase A s0) {ws : Nat → Word} {os : List (Nat × Word)} {l : List (String × Value)}
    (hfo : ScanRun.Fresh "rok" l = true) (hfm : ScanRun.Fresh "rm" l = true) {a b : Bytes}
    (hab : a.length = b.length) (hlen : a.length ≤ 250) (hrl : l.lookup "rl" = some (.ofNat 64 a.length))
    {pa pb : Word} (hpa : l.lookup "rsl" = some pa) (hpb : l.lookup "rcp" = some pb)
    (hA : ∀ u, Mid A cfg J r s0 ws os l u → ∀ m (hm : m < a.length),
      memLoadByte u.memory u.memaddrs u.be (pa + BitVec.ofNat 64 slotId + BitVec.ofNat 64 m) = some a[m])
    (hB : ∀ u, Mid A cfg J r s0 ws os l u → ∀ m (hm : m < b.length),
      memLoadByte u.memory u.memaddrs u.be (pb + BitVec.ofNat 64 slotId + BitVec.ofNat 64 m) = some b[m]) :
    Frag o idCmp
      (Mid A cfg J r s0 ws os l)
          (fun u => Mid A cfg J r s0 ws os l u ∧ u.locals "rok" = some (bw (decide (a = b)))) := by
  have hrok : "rok" ∈ stepLocals := by decide
  have hrm : "rm" ∈ stepLocals := by decide
  let I (m : Nat) : Assn σ := fun u => Mid A cfg J r s0 ws os l u ∧
    u.locals "rok" = some (bw (decide (a.take m = b.take m))) ∧
    (a.take m = b.take m → u.locals "rm" = some (.ofNat 64 m)) ∧ m ≤ a.length
  have hIc : ∀ m, Safe.ClockFree (I m) := fun _ s k ⟨h1, h2, h3, h4⟩ => ⟨mid_clock s k h1, h2, h3, h4⟩
  refine frag_append (xs := [_]) (frag_conseq (mid_put o h (y := "rok") hrok hfo
    (E := .op .add (.var "jz") (.const (.ofNat 64 1))) rfl (F := fun _ => True)
    (F' := fun u => u.locals "rok" = some (bw true)) (fun _ _ h => h) fun u hu _ => ⟨bw true, by
      simp [eval, jz_kept h hu.kept, bw], by simp [setL, setLocal]⟩) (fun u hu => ⟨hu, trivial⟩) fun _ h => h) ?_
  refine frag_append (xs := [_]) (frag_conseq (mid_put o h (y := "rm") hrm hfm
    (E := .op .add (.var "jz") (.const (.ofNat 64 0))) rfl (F := fun u => u.locals "rok" = some (bw true))
    (F' := fun u => u.locals "rok" = some (bw true) ∧ u.locals "rm" = some (.ofNat 64 0)) (fun _ _ h => h)
    fun u hu hf => ⟨.ofNat 64 0, by simp [eval, jz_kept h hu.kept], by simp [setL, setLocal, hf]⟩) (fun _ h => h)
    fun u ⟨hu, h1, h2⟩ => (⟨hu, by simpa using h1, fun _ => h2, Nat.zero_le _⟩ : I 0 u)) ?_
  refine frag_conseq (frag_count o (c := Syntax.eAnd (Syntax.v "rok") (Syntax.eLt (Syntax.v "rm") (Syntax.v "rl")))
    (C := .op .and_ (.var "rok") (.cmp .less (.var "rm") (.var "rl"))) rfl (lowK_any _ (k := .skip) (c := _) rfl) hIc
    (fun m => noDecl (P' := I m) _ rfl) (g := fun m => decide (a.take m = b.take m) && decide (m < a.length))
    (fun m u ⟨hu, h1, h2, _⟩ => by
      by_cases heq : a.take m = b.take m
      · rw [FramerCode.eval_and (ev_var h1) (FramerCode.eval_lt (x := m) (y := a.length) (by omega) (by omega)
          (ev_var (h2 heq)) (ev_var (vals_lookup hu.vals hrl)))]
        simp only [heq, decide_true]; rfl
      · obtain ⟨w, hw⟩ := kept_has hu.kept (h.bound "rm" (by decide))
        obtain ⟨p, hp⟩ := FramerCode.cmp_bw (c := .less) (ev_var hw) (ev_var (vals_lookup hu.vals hrl))
        rw [FramerCode.eval_and (ev_var h1) hp]
        simp only [heq, decide_false, Bool.false_and]; rfl) (fun m hm => ?_) 0) (fun _ h => h) ?_
  · simp only [Bool.and_eq_true, decide_eq_true_eq] at hm
    obtain ⟨heq, hml⟩ := hm
    have hmb : m < b.length := by omega
    have hev : ∀ u, I m u → eval u (.cmp .equal (.cmp .equal
        (.loadByte (.op .add (.op .add (.var "rsl") (.const (.ofNat 64 slotId))) (.var "rm")))
        (.loadByte (.op .add (.op .add (.var "rcp") (.const (.ofNat 64 slotId))) (.var "rm")))) (.const 0)) =
          some (bw (decide (a[m].toNat ≠ (b[m]'hmb).toNat))) := fun u ⟨hu, _, hrm', _⟩ => by
      have hm' := hrm' heq
      refine ScanRun.e_ne (x := a[m].toNat) (y := (b[m]'hmb).toNat) (by have := a[m].isLt; omega)
        (by have := (b[m]'hmb).isLt; omega) ?_ ?_
      · simp only [eval, vals_lookup hu.vals hpa, hm', hA u hu m hml]; rw [Bytes.setWidth8_64]
      · simp only [eval, vals_lookup hu.vals hpb, hm', hB u hu m hmb]; rw [Bytes.setWidth8_64]
    refine frag_if o rfl (lowK_any _ (k := .skip) (c := _) rfl) (lowK_any _ (k := .skip) (c := _) rfl) rfl rfl
      (hIc _) (b := decide (a[m].toNat ≠ (b[m]'hmb).toNat)) hev (fun hne => ?_) fun hsame => ?_
    · simp only [decide_eq_true_eq] at hne
      have hd : a.take (m + 1) ≠ b.take (m + 1) := fun e => hne (by rw [((bytes_take_succ_iff hab hml).mp e).2])
      exact frag_conseq (mid_put o h (y := "rok") hrok hfo (E := .op .add (.var "jz") (.const (.ofNat 64 0))) rfl
        (F := fun _ => True) (F' := fun u => u.locals "rok" = some (bw false)) (fun _ _ h => h) fun u hu _ => ⟨bw
            false, by
          simp [eval, jz_kept h hu.kept, bw], by simp [setL, setLocal]⟩) (fun u hu => ⟨hu.1, trivial⟩)
        fun u ⟨hu, h1⟩ => ⟨hu, by simpa [hd] using h1, fun e => absurd e hd, by omega⟩
    · simp only [decide_eq_false_iff_not, Decidable.not_not] at hsame
      have he : a[m] = b[m]'hmb := BitVec.eq_of_toNat_eq hsame
      have hs : a.take (m + 1) = b.take (m + 1) := (bytes_take_succ_iff hab hml).mpr ⟨heq, he⟩
      exact frag_conseq (mid_put o h (y := "rm") hrm hfm (E := .op .add (.var "rm") (.const (.ofNat 64 1))) rfl
        (F := fun u => u.locals "rok" = some (bw true) ∧ u.locals "rm" = some (.ofNat 64 m))
        (F' := fun u => u.locals "rok" = some (bw true) ∧ u.locals "rm" = some (.ofNat 64 (m + 1))) (fun _ _ h => h)
        fun u _ ⟨h1, h2⟩ => ⟨.ofNat 64 (m + 1), by simp only [eval, h2]; rw [BitVec.ofNat_add],
            by simp [setL, setLocal, h1],
          by simp [setL, setLocal]⟩) (fun u ⟨hu, h1, h2, _⟩ => ⟨hu, by simpa [heq] using h1, h2 heq⟩)
        fun u ⟨hu, h1, h2⟩ => ⟨hu, by simpa [hs] using h1, fun _ => h2, by omega⟩
  intro u ⟨m, ⟨hu, h1, _, hml⟩, hgm⟩
  refine ⟨hu, ?_⟩
  by_cases heq : a.take m = b.take m
  · have : m = a.length := by simp only [heq, decide_true, Bool.true_and, decide_eq_false_iff_not] at hgm; omega
    subst this
    have : a = b := by rwa [List.take_length, hab, List.take_length] at heq
    simpa [heq, this] using h1
  · have : a ≠ b := fun e => heq (by rw [e])
    simpa [heq, this] using h1

/-- The value `rdup` has once two commits with one Message-ID are found, or not. -/
def dupWord (b : Bool) : Word := .ofNat 64 (if b then 2 else 0)

/-- The search for a Message-ID two commits have, middle loop: whether one after `k` has `k`'s, compared by tag,
length and octets. -/
theorem idMid_frag (o : Oracle σ) {A : Word} {cfg : Config} {J : Bytes} {r : RSt} {s0 : PancakeState σ}
    (h : PBase A s0) (hcap : r.commits.length ≤ capacity) {k : Nat} (hk : k < r.commits.length) :
    Frag o idMid (Mid A cfg J r s0 (scalars cfg r) [] [("rj", .ofNat 64 (k + 1)), ("rdup", dupWord false),
        ("rv", (SipHash.tag cfg.key r.commits[k].messageId).toBitVec), ("rl", .ofNat 64 r.commits[k].messageId.length),
        ("rsl", at_ A (slotAt k)), ("ri", .ofNat 64 k), ("rcm", .ofNat 64 r.commits.length), ("rgo", 1)])
      (Mid A cfg J r s0 (scalars cfg r) [] [("rdup", dupWord (dupAt (·.messageId) r.commits k)),
        ("rv", (SipHash.tag cfg.key r.commits[k].messageId).toBitVec), ("rl", .ofNat 64 r.commits[k].messageId.length),
        ("rsl", at_ A (slotAt k)), ("ri", .ofNat 64 k), ("rcm", .ofNat 64 r.commits.length), ("rgo", 1)]) := by
  have hn := nums
  let n := r.commits.length
  let a := r.commits[k].messageId
  let LB : List (String × Value) := [("rv", (SipHash.tag cfg.key a).toBitVec), ("rl", .ofNat 64 a.length),
    ("rsl", at_ A (slotAt k)), ("ri", .ofNat 64 k), ("rcm", .ofNat 64 n), ("rgo", 1)]
  let seen (j : Nat) : Bool := hits (·.messageId) r.commits k j
  let I (j : Nat) : Assn σ := fun u => Mid A cfg J r s0 (scalars cfg r) [] (("rj", .ofNat 64 j) ::
    ("rdup", dupWord (seen j)) :: LB) u ∧ k + 1 ≤ j ∧ j ≤ n
  have hIc : ∀ j, Safe.ClockFree (I j) := fun _ s c ⟨h1, h2⟩ => ⟨mid_clock s c h1, h2⟩
  have hkc : k < capacity := by omega
  have hsucc : ∀ j (hj : j < n), k < j → seen (j + 1) = (seen j || decide (r.commits[j].messageId = a)) := by
    intro j hj hkj
    show hits _ _ _ _ = _
    rw [hits_succ]
    simp [List.getElem?_eq_getElem hj, List.getElem?_eq_getElem hk, hkj, a, seen]
  refine frag_conseq (frag_count o
    (c := Syntax.eAnd (Syntax.eEq (Syntax.v "rdup") (Syntax.n 0)) (Syntax.eLt (Syntax.v "rj") (Syntax.v "rcm")))
    (C := .op .and_ (.cmp .equal (.var "rdup") (.const 0)) (.cmp .less (.var "rj") (.var "rcm"))) rfl
    (lowK_any _ (k := .skip) (c := _) rfl) hIc (fun j => noDecl (P' := I j) _ rfl)
    (g := fun j => !seen j && decide (j < n)) (fun j u ⟨hu, _, _⟩ => flag_guard (e := 2) (by decide) (by decide)
      (by omega) (by omega) (vals_lookup hu.vals rfl) (vals_lookup hu.vals rfl) (vals_lookup hu.vals rfl))
    (fun j hj => ?_) (k + 1)) (fun u hu => ⟨by
        have e : seen (k + 1) = false := hits_le _ _ _ _ (Nat.le_refl _)
        rw [e]; exact hu, Nat.le_refl _, hk⟩) ?_
  · refine frag_pure (k + 1 ≤ j) (fun _ h => h.2.1) (lowK_any _ (k := .skip) (c := _) rfl) fun hkj => ?_
    simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at hj
    obtain ⟨hf, hjn⟩ := hj
    have hjc : j < capacity := by omega
    let b := r.commits[j].messageId
    have h1 : seen (j + 1) = decide (b = a) := by rw [hsucc j hjn (by omega), hf]; rfl
    let L1 : List (String × Value) := ("rcp", at_ A (slotAt j)) :: without "rcp" (("rj", .ofNat 64 j) ::
      ("rdup", dupWord false) :: LB)
    let LE : List (String × Value) := ("rcp", at_ A (slotAt j)) :: ("rj", .ofNat 64 j) ::
      ("rdup", dupWord (seen (j + 1))) :: LB
    refine frag_conseq (P0 := Mid A cfg J r s0 (scalars cfg r) [] (("rj", .ofNat 64 j) :: ("rdup", dupWord false) ::
        LB))
      (P0' := Mid A cfg J r s0 (scalars cfg r) [] (("rj", .ofNat 64 (j + 1)) :: without "rj" LE)) ?_
      (fun u ⟨hu, _⟩ => by rw [hf] at hu; exact hu)
      fun u hu => ⟨mid_lookups hu ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, trivial⟩, by omega, hjn⟩
    refine frag_append (xs := [_]) (mid_slotAt o h (x := "rj") (y := "rcp") (by decide) (i := j) rfl) ?_
    refine frag_append (xs := [_]) (M := Mid A cfg J r s0 (scalars cfg r) [] LE) ?_ ?_
    · have hev : ∀ u, Mid A cfg J r s0 (scalars cfg r) [] L1 u → eval u (.op .and_
          (.cmp .equal (slotPE "rcp" slotTag) (.var "rv"))
          (.cmp .equal (.op .and_ (.shiftR (slotPE "rcp" slotMisc) (.const (.ofNat 64 8))) (.const (.ofNat 64 255)))
            (.var "rl"))) = some (bw (decide ((SipHash.tag cfg.key b).toBitVec = (SipHash.tag cfg.key a).toBitVec) &&
              decide (b.length = a.length))) := fun u hu => by
        have hsj := hu.rest.slots j hjn hjc
        have hsk := hu.rest.slots k hk hkc
        have et := slotP_eval h hu hjc (p := "rcp") rfl (x := slotTag) (by decide) (by decide)
        have em := slotP_eval h hu hjc (p := "rcp") rfl (x := slotMisc) (by decide) (by decide)
        rw [hsj.tag] at et
        rw [hsj.misc] at em
        refine FramerCode.eval_and ?_ ?_
        · rw [eval_equal u et (ev_var (vals_lookup hu.vals rfl))]
          by_cases e : (SipHash.tag cfg.key b).toBitVec = (SipHash.tag cfg.key a).toBitVec
          · rw [if_pos e, decide_eq_true e]; rfl
          · rw [if_neg e, decide_eq_false e]; rfl
        · have e8 : eval u (.op .and_ (.shiftR (slotPE "rcp" slotMisc) (.const (.ofNat 64 8)))
              (.const (.ofNat 64 255))) = some (.ofNat 64 b.length) := by
            simp only [eval, em]
            rw [show (BitVec.ofNat 64 8).toNat = 8 from rfl]
            simp only [show ((8 : Nat) ≠ 0 && 8 ≥ 64) = false from rfl, Bool.false_eq_true, if_false]
            rw [misc_len (by have := hsj.idLen; omega) (by have := hsj.count; simp [ScanProg.groupsMax] at this; omega)]
          exact FramerCode.eval_eq (Nat.lt_of_le_of_lt hsj.idLen (by decide)) (Nat.lt_of_le_of_lt hsk.idLen
            (by decide)) e8
            (ev_var (vals_lookup hu.vals rfl))
      refine frag_if o (C := .op .and_ (.cmp .equal (slotPE "rcp" slotTag) (.var "rv"))
          (.cmp .equal (.op .and_ (.shiftR (slotPE "rcp" slotMisc) (.const (.ofNat 64 8))) (.const (.ofNat 64 255)))
            (.var "rl"))) rfl (lowK_any _ (k := .skip) (c := _) rfl) (fun k => ⟨k, rfl⟩) rfl rfl mid_clock
        (b := decide ((SipHash.tag cfg.key b).toBitVec = (SipHash.tag cfg.key a).toBitVec) &&
          decide (b.length = a.length)) hev (fun e => ?_) fun e => ?_
      · simp only [Bool.and_eq_true, decide_eq_true_eq] at e
        have hab : a.length = b.length := e.2.symm
        refine frag_pure (a.length ≤ 250) (fun u hu => (hu.rest.slots k hk hkc).idLen)
          (lowK_any _ (k := .skip) (c := _) rfl) fun hal => ?_
        refine frag_append (xs := [_, _, _]) (idCmp_frag o h (l := L1) rfl rfl (a := a) (b := b) hab hal rfl rfl rfl
          (fun u hu => slot_id (hu.rest.slots k hk hkc)) (fun u hu => slot_id (hu.rest.slots j hjn hjc))) ?_
        refine frag_if o (C := .var "rok") rfl (lowK_any _ (k := .skip) (c := _) rfl) (fun k => ⟨k, rfl⟩) rfl rfl
          mid_clock (b := decide (a = b)) (fun u ⟨_, hr⟩ => hr) (fun e => ?_) fun e => ?_
        · have e' : decide (b = a) = true := by rw [decide_eq_true_eq] at e ⊢; exact e.symm
          refine frag_conseq (mid_assign o h (y := "rdup") (by decide) (E := .op .add (.var "jz") (.const 2)) rfl
            (val := dupWord true) fun u hu => by simp [eval, jz_kept h hu.kept, dupWord]) (fun u hu => hu.1) fun u
                hu => ?_
          exact mid_lookups hu ⟨rfl, rfl, by rw [h1, e']; rfl, rfl, rfl, rfl, rfl, rfl, rfl, trivial⟩
        · have e' : decide (b = a) = false := by rw [decide_eq_false_iff_not] at e ⊢; exact fun h => e h.symm
          exact frag_nil o fun u ⟨hu, _⟩ => mid_lookups hu ⟨rfl, rfl, by rw [h1, e']; rfl, rfl, rfl, rfl, rfl, rfl,
            rfl, trivial⟩
      · have e' : decide (b = a) = false := by
          rw [decide_eq_false_iff_not]
          intro hba
          rw [hba] at e
          simp at e
        exact frag_nil o fun u hu => mid_lookups hu ⟨rfl, rfl, by rw [h1, e']; rfl, rfl, rfl, rfl, rfl, rfl, rfl,
          trivial⟩
    · exact mid_assign o h (y := "rj") (by decide) (E := .op .add (.var "rj") (.const (.ofNat 64 1))) rfl
        (val := .ofNat 64 (j + 1)) fun u hu =>
            by simp only [eval, vals_lookup hu.vals (x := "rj") rfl, BitVec.ofNat_add]
  intro u ⟨j, ⟨hu, _, hjn⟩, hgj⟩
  have hd : dupAt (·.messageId) r.commits k = seen n := dupAt_hits _ hk
  cases e : seen j
  · have : j = n := by simp only [e, Bool.not_false, Bool.true_and, decide_eq_false_iff_not] at hgj; omega
    subst this
    rw [hd]; exact mid_lookups hu ⟨by rw [e]; rfl, rfl, rfl, rfl, rfl, rfl, rfl, trivial⟩
  · have hn' : seen n = true := hits_mono _ _ _ e hjn
    rw [hd, hn']; exact mid_lookups hu ⟨by rw [e]; rfl, rfl, rfl, rfl, rfl, rfl, rfl, trivial⟩

theorem dupWord_ne {b : Bool} : dupWord b ≠ 0 ↔ b = true := by cases b <;> decide

/-- **Two commits with one Message-ID** searched for: the first commit a later one repeats, its Message-ID's length
in `rl`. -/
theorem idDups_frag (o : Oracle σ) {fail : List Syntax.PStmt} (hfl : LowKK fail) (hfd : declared fail = [])
    {A : Word} {cfg : Config} {J : Bytes} {r : RSt} {s0 : PancakeState σ}
    (h : PBase A s0) (hcap : r.commits.length ≤ capacity) :
    Frag o (idDups fail)
      (Mid A cfg J r s0 (scalars cfg r) [] [("rdup", dupWord false), ("rcm", .ofNat 64 r.commits.length), ("rgo", 1)])
      (fun u => Mid A cfg J r s0 (scalars cfg r) [] [("ri", .ofNat 64 ((firstIdx
          (dupAt (·.messageId) r.commits) r.commits.length).getD r.commits.length)),
        ("rdup", dupWord (firstIdx (dupAt (·.messageId) r.commits) r.commits.length).isSome),
        ("rcm", .ofNat 64 r.commits.length), ("rgo", 1)] u ∧
        ∀ i (hi : i < r.commits.length), firstIdx (dupAt (·.messageId) r.commits)
          r.commits.length = some i → u.locals "rl" = some (.ofNat 64 r.commits[i].messageId.length)) := by
  have hn := nums
  let n := r.commits.length
  let R (k : Nat) (f : Option Nat) : Assn σ := fun u => Mid A cfg J r s0 (scalars cfg r) []
    [("ri", .ofNat 64 (f.getD k)), ("rdup", dupWord f.isSome), ("rcm", .ofNat 64 n), ("rgo", 1)] u ∧
    ∀ i (hi : i < n), f = some i → u.locals "rl" = some (.ofNat 64 r.commits[i].messageId.length)
  refine frag_append (xs := [_]) (mid_assign o h (y := "ri") (by decide) (E := .op .add (.var "jz") (.const 0)) rfl
    (val := .ofNat 64 0) fun u hu => by simp [eval, jz_kept h hu.kept]) ?_
  refine frag_conseq (P0 := R 0 none) (firstIdx_frag o rfl (lowKK_append (xs := [_, _])
    (lowK_any _ (k := .skip) (c := _) rfl) (lowKK_append (xs := [_]) (lowKK_kept hfl "rl" 250)
      (lowK_any _ (k := .skip) (c := _) rfl))) rfl (R := R) (fun _ _ s t ⟨h1, h2⟩ => ⟨mid_clock s t h1, h2⟩)
    (fun k u hkn ⟨hu, _⟩ => search_guard (e := 2) (by decide) (by decide) (fun _ hj => (firstIdx_lt hj).1) hkn
      (by omega) (vals_lookup hu.vals rfl) (vals_lookup hu.vals rfl) (vals_lookup hu.vals rfl))
    (fun k hf hkn => ?_) fun _ _ _ hu => hu) (fun u hu => ⟨mid_lookups hu ⟨rfl, rfl, rfl, rfl, trivial⟩,
      fun _ _ hi => nomatch hi⟩) fun _ h => h
  have hkc : k < capacity := by omega
  refine frag_conseq (P0 := Mid A cfg J r s0 (scalars cfg r) [] [("ri", .ofNat 64 k), ("rdup", dupWord false),
    ("rcm", .ofNat 64 n), ("rgo", 1)]) ?_ (fun u hu => hu.1) fun _ h => h
  refine frag_append (xs := [_]) (mid_slotAt o h (y := "rsl") (by decide) (x := "ri") (i := k) rfl) ?_
  refine frag_append (xs := [_]) (mid_assign o h (y := "rl") (by decide)
    (E := .op .and_ (.shiftR (slotWE slotMisc) (.const (.ofNat 64 8))) (.const (.ofNat 64 255))) rfl
    (val := .ofNat 64 r.commits[k].messageId.length) fun u hu => by
      have hsk := hu.rest.slots k hkn hkc
      have em := slotP_eval h hu hkc (p := "rsl") rfl (x := slotMisc) (by decide) (by decide)
      rw [hsk.misc] at em
      simp only [eval, em]
      rw [show (BitVec.ofNat 64 8).toNat = 8 from rfl]
      simp only [show ((8 : Nat) ≠ 0 && 8 ≥ 64) = false from rfl, Bool.false_eq_true, if_false]
      rw [misc_len (by have := hsk.idLen; omega) (by have := hsk.count; simp [ScanProg.groupsMax] at this; omega)])
    ?_
  refine frag_append (xs := [_]) (ScanRun.kept_skip o hfl hfd (by decide) mid_clock fun u hu =>
    ⟨_, vals_lookup hu.vals rfl, (hu.rest.slots k hkn hkc).idLen⟩) ?_
  refine frag_append (xs := [_]) (mid_assign o h (y := "rv") (by decide) (slotW_lower slotTag)
    (val := (SipHash.tag cfg.key r.commits[k].messageId).toBitVec) fun u hu =>
      (slotP_eval h hu hkc (p := "rsl") rfl (by decide) (by decide)).trans
          (congrArg some ((hu.rest.slots k hkn hkc).tag))) ?_
  refine frag_append (xs := [_]) (mid_assign o h (y := "rj") (by decide)
    (E := .op .add (.var "ri") (.const (.ofNat 64 1))) rfl (val := .ofNat 64 (k + 1)) fun u hu => by
      simp only [eval, vals_lookup hu.vals (x := "ri") rfl, BitVec.ofNat_add]) ?_
  refine frag_append (frag_conseq (idMid_frag o h hcap hkn)
    (fun u hu => mid_lookups hu ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, trivial⟩) fun _ h => h) ?_
  refine frag_ifw o (C := .var "rdup") rfl (fun k => ⟨k, rfl⟩) (lowK_any _ (k := .skip) (c := _) rfl) rfl rfl
    (by exact fun s t ⟨h1, h2⟩ => ⟨mid_clock s t h1, h2⟩) (w := dupWord (dupAt (·.messageId) r.commits k))
    (fun u hu => vals_lookup hu.vals rfl) (fun e => ?_) fun e => ?_
  · have e' := dupWord_ne.1 e
    rw [e']
    exact frag_nil o fun u hu =>
      ⟨mid_lookups hu ⟨rfl, rfl, rfl, rfl, trivial⟩, fun i _ hi => by cases hi; exact vals_lookup hu.vals rfl⟩
  · have e' : dupAt (·.messageId) r.commits k = false := by
      cases e2 : dupAt (·.messageId) r.commits k
      · rfl
      · rw [e2] at e; exact absurd e (by decide)
    rw [e']
    refine frag_conseq (mid_assign o h (y := "ri") (by decide) (E := .op .add (.var "ri") (.const (.ofNat 64 1)))
      rfl (val := .ofNat 64 (k + 1)) fun u hu => by
        simp only [eval, vals_lookup hu.vals (x := "ri") rfl, BitVec.ofNat_add]) (fun _ h => h) fun u hu => ?_
    exact ⟨mid_lookups hu ⟨rfl, rfl, rfl, rfl, trivial⟩, fun _ _ hi => nomatch hi⟩

/-- The highest article numbers, `h x` at place `x`. -/
def HighIs (A : Word) (h : Nat → Nat) (u : PancakeState σ) : Prop :=
  ∀ x, x < groupsMax → u.memory (at_ A (rHigh + x * 8)) = .ofNat 64 (h x)

theorem highIs_clock {A : Word} {h : Nat → Nat} : Safe.ClockFree (HighIs (σ := σ) A h) := fun _ _ hh => hh

/-- A highest article number read, its place in `rc`. -/
theorem high_eval {A : Word} {cfg : Config} {J : Bytes} {r : RSt} {s0 : PancakeState σ} (h : PBase A s0)
    {ws : Nat → Word} {os : List (Nat × Word)} {l : List (String × Value)} {u : PancakeState σ}
    (hu : Mid A cfg J r s0 ws os l u) {x : Nat} (hx : x < groupsMax) (hl : l.lookup "rc" = some (.ofNat 64 x)) :
    eval u (.loadWord (.op .add (.op .add (.var "rsc") (.const (.ofNat 64 rHigh)))
        (.mul (.var "rc") (.const (.ofNat 64 8)))))
      = some (u.memory (at_ A (rHigh + x * 8))) := by
  have hn := nums
  exact load_index_eval (rsc_kept h hu.kept) (vals_lookup hu.vals hl)
    (area_dom h hu.kept.memaddrs (by omega) (by omega))

/-- **A highest article number stored**, before the rules hold. -/
theorem high_store (o : Oracle σ) {A : Word} {cfg : Config} {J : Bytes} {r : RSt} {s0 : PancakeState σ}
    (h : PBase A s0) (hp : r.phase < 5) {ws : Nat → Word} {os : List (Nat × Word)} {l : List (String × Value)}
    {x : Nat} (hx : x < groupsMax) (hl : l.lookup "rc" = some (.ofNat 64 x)) {e : Syntax.PExpr} {E : PancakeExp}
    (he : Lower.lowerExp e = some E) {val : Nat}
        (hv : ∀ u, Mid A cfg J r s0 ws os l u → eval u E = some (.ofNat 64 val))
    {hh : Nat → Nat} :
    Frag o [.store (Syntax.eAdd (Syntax.atOff rp rHigh) (Syntax.eMul (Syntax.v "rc") (Syntax.n 8))) e]
      (fun u => Mid A cfg J r s0 ws os l u ∧ HighIs A hh u)
      (fun u => Mid A cfg J r s0 ws os l u ∧ HighIs A (fun y => if y = x then val else hh y) u) := by
  have hn := nums
  refine store_frag o (D := .op .add (.op .add (.var "rsc") (.const (.ofNat 64 rHigh)))
    (.mul (.var "rc") (.const (.ofNat 64 8)))) rfl he (fun s k ⟨h1, h2⟩ => ⟨mid_clock s k h1, h2⟩)
    fun u ⟨hu, hh'⟩ => ⟨at_ A (rHigh + x * 8), _, ?_, hv u hu, ?_, mid_high h hp hu hx _, fun y hy => ?_⟩
  · exact index_eval (rsc_kept h hu.kept) (vals_lookup hu.vals hl) rHigh 8
  · have := h.dom (rHigh + x * 8) (by omega)
    rw [hu.kept.memaddrs]; simp only [at_] at this ⊢
    rwa [byteAlign_of_aligned h.hA (X := rHigh + x * 8) (by omega)] at this
  · show (stW u A (rHigh + x * 8) _).memory _ = _
    by_cases e : y = x
    · subst e; simp [stW]
    · rw [stW_word (by omega) (by omega) (by omega)]; dsimp only; rw [if_neg e]; exact hh' y hy

/-- A group's word of slot `i` read, its index in `rg`. -/
theorem groupW_eval {A : Word} {cfg : Config} {J : Bytes} {r : RSt} {s0 : PancakeState σ} (h : PBase A s0)
    {ws : Nat → Word} {os : List (Nat × Word)} {l : List (String × Value)} {u : PancakeState σ}
    (hu : Mid A cfg J r s0 ws os l u) {i : Nat} (hi : i < capacity) (hl : l.lookup "rsl" = some (at_ A (slotAt i)))
    {t : Nat} (ht : t < 16) (hg : l.lookup "rg" = some (.ofNat 64 t)) :
    eval u (.loadWord (.op .add (.op .add (.var "rsl") (.const (.ofNat 64 slotGroups))) (.mul (.var "rg")
      (.const (.ofNat 64 8))))) = some (u.memory (at_ A (slotAt i + slotGroups + t * 8))) := by
  have hn := nums
  obtain ⟨s1, s2⟩ := slotAt_le hi
  have hal := slotAt_aligned i
  have hd := h.dom (slotAt i + slotGroups + t * 8) (by omega)
  rw [← hu.kept.memaddrs] at hd
  simp only [eval, vals_lookup hu.vals hl, vals_lookup hu.vals hg]
  rw [← BitVec.ofNat_mul, at_add, at_add]
  show (if u.memaddrs (at_ A (slotAt i + slotGroups + t * 8)) then _ else _) = _
  rw [show u.memaddrs (at_ A (slotAt i + slotGroups + t * 8)) = true by
    simp only [at_] at hd ⊢; rwa [byteAlign_of_aligned h.hA (X := slotAt i + slotGroups + t * 8) (by omega)] at hd]
  rfl

/-- Whether group `t` of `gs` has a number not above `H` at its place in the configuration. -/
def groupBad (cfg : Config) (H : Nat → Nat) (gs : List Group) (t : Nat) : Bool :=
  match gs[t]? with
  | some g => decide (g.number ≤ H (groupIx cfg g.name))
  | none => false

/-- The word of a group in a slot: its place in the configuration and its article number. -/
def gWord (cfg : Config) (g : Group) : Word := (BitVec.ofNat 64 (groupIx cfg g.name) <<< 32) ||| .ofNat 64 g.number

theorem lowKK_groupsCheck {fail : List Syntax.PStmt} (hfl : LowKK fail) : LowKK (groupsCheck fail) :=
  lowKK_while rfl (lowKK_append (xs := [_, _]) (lowK_any _ (k := .skip) (c := _) rfl)
    (lowKK_append (xs := [_]) (lowKK_kept hfl _ _) (lowK_any _ (k := .skip) (c := _) rfl)))

theorem lowKK_groupsStore {fail : List Syntax.PStmt} (hfl : LowKK fail) : LowKK (groupsStore fail) :=
  lowKK_append (xs := [_]) (lowK_any _ (k := .skip) (c := _) rfl) (lowKK_append (xs := [_])
    (lowKK_while rfl (lowKK_append (xs := [_, _]) (lowK_any _ (k := .skip) (c := _) rfl)
      (lowKK_append (xs := [_]) (lowKK_kept hfl _ _) (lowK_any _ (k := .skip) (c := _) rfl))))
    (lowK_any _ (k := .skip) (c := _) rfl))

/-- **The groups of commit `i` checked** against the highest numbers `H`: the first not above, its number in `rv`
and its place in `rc`. -/
theorem checkGroups_frag (o : Oracle σ) {fail : List Syntax.PStmt} (hfl : LowKK fail) (hfd : declared fail = [])
    {A : Word} {cfg : Config} {J : Bytes} {r : RSt} {s0 : PancakeState σ} (h : PBase A s0) {ws : Nat → Word}
    {os : List (Nat × Word)} {i : Nat} (hi : i < r.commits.length) (hic : i < capacity)
    (hix : ∀ g ∈ r.commits[i].groups, groupIx cfg g.name < groupsMax)
    (hnum : ∀ g ∈ r.commits[i].groups, g.number < 2 ^ 31) {H : Nat → Nat} (hH : ∀ x, H x < 2 ^ 31) (vcm : Value) :
    Frag o (groupsCheck fail) (fun u => Mid A cfg J r s0 ws os [("rg", .ofNat 64 0), ("rbad", bw false),
        ("rgc", .ofNat 64 r.commits[i].groups.length), ("rsl", at_ A (slotAt i)), ("ri", .ofNat 64 i), ("rcm", vcm),
        ("rgo", 1)] u ∧ HighIs A H u)
      (fun u => Mid A cfg J r s0 ws os [("rbad", bw (firstIdx (groupBad cfg H r.commits[i].groups)
          r.commits[i].groups.length).isSome), ("rgc", .ofNat 64 r.commits[i].groups.length),
        ("rsl", at_ A (slotAt i)), ("ri", .ofNat 64 i), ("rcm", vcm), ("rgo", 1)] u ∧ HighIs A H u ∧
        ∀ t (ht : t < r.commits[i].groups.length), firstIdx (groupBad cfg H r.commits[i].groups)
          r.commits[i].groups.length = some t →
          u.locals "rv" = some (.ofNat 64 r.commits[i].groups[t].number) ∧
          u.locals "rc" = some (.ofNat 64 (groupIx cfg r.commits[i].groups[t].name))) := by
  have hn := nums
  -- the count of groups below sixteen, from the slot
  refine frag_pure (r.commits[i].groups.length ≤ 16) (fun u ⟨hu, _⟩ => (hu.rest.slots i hi hic).count)
    (lowKK_groupsCheck hfl) fun hgc => ?_
  let gs := r.commits[i].groups
  have hgc' : gs.length ≤ 16 := hgc
  let base : List (String × Value) := [("rgc", .ofNat 64 gs.length), ("rsl", at_ A (slotAt i)), ("ri", .ofNat 64 i),
    ("rcm", vcm), ("rgo", 1)]
  let R (k : Nat) (f : Option Nat) : Assn σ := fun u =>
    Mid A cfg J r s0 ws os (("rg", .ofNat 64 (f.getD k)) :: ("rbad", bw f.isSome) :: base) u ∧ HighIs A H u ∧
    ∀ t (ht : t < gs.length), f = some t →
      u.locals "rv" = some (.ofNat 64 gs[t].number) ∧ u.locals "rc" = some (.ofNat 64 (groupIx cfg gs[t].name))
  refine frag_conseq (P0 := R 0 none) (firstIdx_frag o rfl (lowKK_append (xs := [_, _])
    (lowK_any _ (k := .skip) (c := _) rfl) (lowKK_append (xs := [_]) (lowKK_kept hfl _ _)
      (lowK_any _ (k := .skip) (c := _) rfl))) rfl (R := R) (fun _ _ s t ⟨h1, h2⟩ => ⟨mid_clock s t h1, h2⟩)
    (fun k u hkn ⟨hu, _⟩ => search_guard (e := 1) (by decide) (by decide) (fun _ hj => (firstIdx_lt hj).1) hkn
      (by omega) (vals_lookup hu.vals rfl) (by rw [← bw_nat]; exact vals_lookup hu.vals rfl)
      (vals_lookup hu.vals rfl))
    (fun k hf hkn => ?_) fun _ _ _ hu => hu)
    (fun u ⟨hu, hh⟩ => ⟨mid_lookups hu ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, trivial⟩, hh, fun _ _ e => nomatch e⟩)
    fun u ⟨hu, hh, hfd⟩ => ⟨mid_lookups hu ⟨rfl, rfl, rfl, rfl, rfl, rfl, trivial⟩, hh, hfd⟩
  let L1 : List (String × Value) := ("rg", .ofNat 64 k) :: ("rbad", bw false) :: base
  refine frag_conseq (P0 := fun u => Mid A cfg J r s0 ws os L1 u ∧ HighIs A H u) ?_ (fun u ⟨hu, hh, _⟩ => ⟨hu, hh⟩)
    fun _ h => h
  have hkn : k < gs.length := hkn
  have hgk : gs[k] ∈ gs := List.getElem_mem hkn
  have hixk := hix _ hgk
  have hnk := hnum _ hgk
  have hHk := hH (groupIx cfg gs[k].name)
  -- the group's word, its place, its number
  refine frag_append (xs := [_]) (frag_conseq (mid_assign_and o h (y := "rx") (by decide)
    (E := .loadWord (.op .add (.op .add (.var "rsl") (.const (.ofNat 64 slotGroups))) (.mul (.var "rg")
      (.const (.ofNat 64 8))))) rfl (val := gWord cfg gs[k])
    (fun u hu => by
      rw [groupW_eval h hu hic rfl (by omega) rfl]
      exact congrArg some ((hu.rest.slots i hi hic).groups k hkn)) highIs_clock (fun _ h => h))
    (fun _ h => h) fun _ h => h) ?_
  refine frag_append (xs := [_]) (frag_conseq (mid_assign_and o h (y := "rc") (by decide)
    (E := .op .add (.var "jz") (.shiftR (.var "rx") (.const (.ofNat 64 32)))) rfl
    (val := .ofNat 64 (groupIx cfg gs[k].name))
    (fun u hu => by
      simp only [eval, jz_kept h hu.kept, vals_lookup hu.vals (x := "rx") rfl]
      rw [show (BitVec.ofNat 64 32).toNat = 32 from rfl]
      simp only [show ((32 : Nat) ≠ 0 && 32 ≥ 64) = false from rfl, Bool.false_eq_true, if_false]
      rw [gWord, group_ix (by omega) (by omega)]; simp) highIs_clock (fun _ h => h))
    (fun _ h => h) fun _ h => h) ?_
  refine frag_append (xs := [_]) (ScanRun.kept_skip o hfl hfd (by decide)
    (fun s c ⟨h1, h2⟩ => ⟨mid_clock s c h1, h2⟩) fun u ⟨hu, _⟩ =>
      ⟨_, vals_lookup hu.vals rfl, by simp only [groupsMax] at hixk ⊢; omega⟩) ?_
  refine frag_append (xs := [_]) (frag_conseq (mid_assign_and o h (y := "rv") (by decide)
    (E := .op .and_ (.var "rx") (.const (.ofNat 64 (2 ^ 32 - 1)))) rfl
    (val := .ofNat 64 gs[k].number)
    (fun u hu => by
      simp only [eval, vals_lookup hu.vals (x := "rx") rfl]
      rw [gWord, sizes_low (by omega)]) highIs_clock (fun _ h => h)) (fun _ h => h) fun _ h => h) ?_
  have hbad : groupBad cfg H gs k = decide (gs[k].number ≤ H (groupIx cfg gs[k].name)) := by
    simp only [groupBad, List.getElem?_eq_getElem hkn]
  refine frag_if o (C := FramerCode.leE (.var "rv") (.loadWord (.op .add (.op .add (.var "rsc")
      (.const (.ofNat 64 rHigh))) (.mul (.var "rc") (.const (.ofNat 64 8)))))) rfl
    (lowK_any _ (k := .skip) (c := _) rfl) (lowK_any _ (k := .skip) (c := _) rfl) rfl rfl
      (by exact fun s t ⟨h1, h2⟩ => ⟨mid_clock s t h1, h2⟩)
    (b := groupBad cfg H gs k) (fun u ⟨hu, hh⟩ => by
      rw [hbad]
      exact FramerCode.eval_le (by omega) (by omega) (ev_var (vals_lookup hu.vals rfl))
        ((high_eval h hu hixk rfl).trans (congrArg some (hh _ hixk)))) (fun e => ?_) fun e => ?_
  · rw [e]
    refine frag_conseq (mid_assign_and o h (y := "rbad") (by decide) (E := .op .add (.var "jz") (.const 1)) rfl
      (val := bw true) (fun u hu => by simp [eval, jz_kept h hu.kept, bw]) highIs_clock (fun _ h => h))
      (fun _ h => h) fun u ⟨hu, hh⟩ => ?_
    exact ⟨mid_lookups hu ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, trivial⟩, hh, fun t _ e2 => by
      cases e2; exact ⟨vals_lookup hu.vals rfl, vals_lookup hu.vals rfl⟩⟩
  · rw [e]
    refine frag_conseq (mid_assign_and o h (y := "rg") (by decide)
      (E := .op .add (.var "rg") (.const (.ofNat 64 1))) rfl (val := .ofNat 64 (k + 1)) (fun u hu => by
        simp only [eval, vals_lookup hu.vals (x := "rg") rfl, BitVec.ofNat_add]) highIs_clock (fun _ h => h))
      (fun _ h => h) fun u ⟨hu, hh⟩ => ?_
    exact ⟨mid_lookups hu ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, trivial⟩, hh, fun _ _ e2 => nomatch e2⟩

/-- A name the configuration has: its place, below the count, holds it. -/
theorem ix_known {cfg : Config} (hc : cfg.groups.length ≤ groupsMax) {nm : Bytes}
    (hk : cfg.groups.contains nm = true) :
    groupIx cfg nm < cfg.groups.length ∧ cfg.groups.getD (groupIx cfg nm) [] = nm := by
  rw [groupIx_eq, Nat.min_eq_left hc]
  rcases ix_spec cfg nm _ hc with ⟨h1, _⟩ | ⟨h1, h2⟩
  · rw [(ix_none hc nm).1 h1] at hk; cases hk
  · exact ⟨h1, h2⟩

theorem ix_inj {cfg : Config} (hc : cfg.groups.length ≤ groupsMax) {a b : Bytes}
    (ha : cfg.groups.contains a = true) (hb : cfg.groups.contains b = true) (h : groupIx cfg a = groupIx cfg b) :
    a = b := by
  have e1 := (ix_known hc ha).2
  have e2 := (ix_known hc hb).2
  rw [h] at e1; rw [← e1, e2]

theorem highIn_snoc : ∀ (cs : List Commit) (c : Commit) (nm : Bytes),
    highIn (cs ++ [c]) nm = max (highIn cs nm) (Recovery.highOf c.groups nm)
  | [], c, nm => by simp [highIn]
  | d :: cs, c, nm => by
    simp only [List.cons_append, highIn, highIn_snoc cs c nm]
    omega

theorem highOf_none : ∀ {gs : List Group} {nm : Bytes}, (∀ g ∈ gs, g.name ≠ nm) → Recovery.highOf gs nm = 0
  | [], _, _ => rfl
  | g :: gs, nm, h => by
    simp only [Recovery.highOf, beq_iff_eq, h g (List.mem_cons_self ..), if_false,
      highOf_none fun x hx => h x (List.mem_cons_of_mem _ hx)]
    rfl

theorem highOf_mem : ∀ {gs : List Group}, (gs.map Group.name).Nodup → ∀ {g : Group}, g ∈ gs →
    Recovery.highOf gs g.name = g.number
  | [], _, _, hg => nomatch hg
  | x :: gs, hnd, g, hg => by
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at hnd
    rcases List.mem_cons.1 hg with rfl | hg
    · simp only [Recovery.highOf, beq_self_eq_true, if_true]
      rw [highOf_none fun y hy e => hnd.1 ⟨y, hy, e⟩]; omega
    · have hne : x.name ≠ g.name := fun e => hnd.1 ⟨g, hg, e.symm⟩
      simp only [Recovery.highOf, beq_iff_eq, hne, if_false, highOf_mem hnd.2 hg]
      omega

theorem highOf_snoc (cfg : Config) (cs : List Commit) (c : Commit) (x : Nat) :
    highOf cfg (cs ++ [c]) x = match c.groups.find? (fun g => groupIx cfg g.name = x) with
      | some g => g.number
      | none => highOf cfg cs x := by
  simp only [highOf, List.foldl_append, List.foldl_cons, List.foldl_nil]
  rfl

/-- What a commit's groups are: known to the configuration, of names apart. -/
def FitsCfg (cfg : Config) (c : Commit) : Prop :=
  (c.groups.map Group.name).Nodup ∧ ∀ g ∈ c.groups, cfg.groups.contains g.name = true

/-- Each commit's numbers above the highest its groups had before it. -/
def Rising (cs : List Commit) : Prop :=
  ∀ i (hi : i < cs.length), ∀ g ∈ cs[i].groups, highIn (cs.take i) g.name < g.number

/-- **The last number is the highest** where numbers rise: a group's place holds what `highIn` says, of each first
`n` commits. -/
theorem high_take {cfg : Config} (hc : cfg.groups.length ≤ groupsMax) {cs : List Commit}
    (hf : ∀ c ∈ cs, FitsCfg cfg c) (hr : Rising cs) : ∀ n, n ≤ cs.length → ∀ nm, cfg.groups.contains nm = true →
      highIn (cs.take n) nm = highOf cfg (cs.take n) (groupIx cfg nm) := by
  intro n
  induction n with
  | zero => intro _ _ _; rfl
  | succ n ih =>
    intro hn nm hk
    have hlt : n < cs.length := by omega
    have hfc := hf (cs[n]'hlt) (List.getElem_mem hlt)
    have hlast : ∀ g ∈ (cs[n]'hlt).groups, highIn (cs.take n) g.name < g.number := hr n hlt
    rw [List.take_succ_eq_append_getElem hlt, highIn_snoc, highOf_snoc, ih (by omega) nm hk]
    cases e : (cs[n]'hlt).groups.find? (fun g => groupIx cfg g.name = groupIx cfg nm) with
    | some g =>
      have hg := List.mem_of_find?_eq_some e
      have hgn : g.name = nm := ix_inj hc (hfc.2 g hg) hk (by simpa using List.find?_some e)
      have := hlast g hg
      rw [← hgn, highOf_mem hfc.1 hg, ← ih (by omega) _ (by rw [hgn]; exact hk)]
      dsimp only
      omega
    | none =>
      have hno : ∀ g ∈ (cs[n]'hlt).groups, g.name ≠ nm := fun g hg e2 => by
        have := List.find?_eq_none.1 e g hg
        simp [e2] at this
      rw [highOf_none hno]; dsimp only; omega

/-- The highest numbers after the first `t` groups of `gs` stored over `H`. -/
def storedUpTo (cfg : Config) (H : Nat → Nat) (gs : List Group) (t : Nat) (x : Nat) : Nat :=
  match (gs.take t).find? (fun g => groupIx cfg g.name = x) with
  | some g => g.number
  | none => H x

theorem storedUpTo_succ {cfg : Config} {H : Nat → Nat} {gs : List Group} {t : Nat} (ht : t < gs.length)
    (hc : cfg.groups.length ≤ groupsMax) (hnd : (gs.map Group.name).Nodup)
    (hk : ∀ g ∈ gs, cfg.groups.contains g.name = true) :
    storedUpTo cfg H gs (t + 1) =
      fun y => if y = groupIx cfg gs[t].name then gs[t].number else storedUpTo cfg H gs t y := by
  funext y
  simp only [storedUpTo, List.take_succ_eq_append_getElem ht, List.find?_append, List.find?_cons, List.find?_nil]
  by_cases e : y = groupIx cfg gs[t].name
  · subst e
    have hnone : (gs.take t).find? (fun g => decide (groupIx cfg g.name = groupIx cfg gs[t].name)) = none := by
      rw [List.find?_eq_none]
      intro g hg he
      obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hg
      simp only [List.length_take] at hj
      have hn : (gs.take t)[j].name = gs[t].name := ix_inj hc (hk _ (List.mem_of_mem_take hg))
        (hk _ (List.getElem_mem ht)) (by simpa using he)
      rw [List.getElem_take] at hn
      have hjt : j < t := by omega
      have h2 := List.pairwise_iff_getElem.1 hnd j t (by simp; omega) (by simp; omega) hjt
      simp only [List.getElem_map] at h2
      exact h2 hn
    simp [hnone]
  · simp only [if_neg e]
    cases (gs.take t).find? (fun g => decide (groupIx cfg g.name = y)) with
    | some g => rfl
    | none => simp [Ne.symm e]

theorem storedUpTo_zero (cfg : Config) (H : Nat → Nat) (gs : List Group) : storedUpTo cfg H gs 0 = H := by
  funext y; simp [storedUpTo]

/-- **The numbers of commit `i`'s groups stored** at their places, and the next commit. -/
theorem storeGroups_frag (o : Oracle σ) {fail : List Syntax.PStmt} (hfl : LowKK fail) (hfd : declared fail = [])
    {A : Word} {cfg : Config} {J : Bytes} {r : RSt} {s0 : PancakeState σ} (h : PBase A s0) (hp : r.phase < 5)
    {ws : Nat → Word} {os : List (Nat × Word)} {i : Nat} (hi : i < r.commits.length) (hic : i < capacity)
    (hc : cfg.groups.length ≤ groupsMax) (hnd : (r.commits[i].groups.map Group.name).Nodup)
    (hk : ∀ g ∈ r.commits[i].groups, cfg.groups.contains g.name = true)
    (hnum : ∀ g ∈ r.commits[i].groups, g.number < 2 ^ 31) {H : Nat → Nat} (vcm : Value) :
    Frag o (groupsStore fail)
      (fun u => Mid A cfg J r s0 ws os [("rbad", bw false), ("rgc", .ofNat 64 r.commits[i].groups.length),
        ("rsl", at_ A (slotAt i)), ("ri", .ofNat 64 i), ("rcm", vcm), ("rgo", 1)] u ∧ HighIs A H u)
      (fun u => Mid A cfg J r s0 ws os [("ri", .ofNat 64 (i + 1)), ("rbad", bw false), ("rcm", vcm), ("rgo", 1)] u ∧
        HighIs A (storedUpTo cfg H r.commits[i].groups r.commits[i].groups.length) u) := by
  have hn := nums
  refine frag_pure (r.commits[i].groups.length ≤ 16) (fun u ⟨hu, _⟩ => (hu.rest.slots i hi hic).count)
    (lowKK_groupsStore hfl) fun hgc => ?_
  let gs := r.commits[i].groups
  have hgc' : gs.length ≤ 16 := hgc
  let base : List (String × Value) := [("rbad", bw false), ("rgc", .ofNat 64 gs.length), ("rsl", at_ A (slotAt i)),
    ("ri", .ofNat 64 i), ("rcm", vcm), ("rgo", 1)]
  let I (t : Nat) : Assn σ := fun u => Mid A cfg J r s0 ws os (("rg", .ofNat 64 t) :: base) u ∧
    HighIs A (storedUpTo cfg H gs t) u ∧ t ≤ gs.length
  have hIc : ∀ t, Safe.ClockFree (I t) := fun _ s c ⟨h1, h2⟩ => ⟨mid_clock s c h1, h2⟩
  refine frag_append (xs := [_]) (frag_conseq (mid_assign_and o h (y := "rg") (by decide)
    (E := .op .add (.var "jz") (.const 0)) rfl (val := .ofNat 64 0) (fun u hu => by simp [eval, jz_kept h hu.kept])
    (F := HighIs A H) (fun _ _ h => h) (fun _ h => h)) (fun _ h => h) fun u ⟨hu, hh⟩ =>
      (⟨mid_lookups hu ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, trivial⟩, by rw [storedUpTo_zero]; exact hh,
        Nat.zero_le _⟩ : I 0 u)) ?_
  refine frag_append (xs := [_]) (frag_conseq (frag_count o (c := Syntax.eLt (Syntax.v "rg") (Syntax.v "rgc"))
    (C := .cmp .less (.var "rg") (.var "rgc")) rfl
    (lowKK_append (xs := [_, _]) (lowK_any _ (k := .skip) (c := _) rfl)
      (lowKK_append (xs := [_]) (lowKK_kept hfl _ _) (lowK_any _ (k := .skip) (c := _) rfl))) hIc
    (fun t => noDecl (P' := I t) _ rfl) (g := fun t => decide (t < gs.length)) (fun t u ⟨hu, _, _⟩ => by
      rw [FramerCode.eval_lt (t := u) (a := .var "rg") (b := .var "rgc") (x := t) (y := gs.length) (by omega)
        (by omega) (ev_var (vals_lookup hu.vals rfl)) (ev_var (vals_lookup hu.vals rfl))]; rfl) (fun t ht => ?_) 0)
    (fun _ h => h) (fun u ⟨t, ⟨hu, hh, htn⟩, hg⟩ => by
      have : t = gs.length := by simp only [decide_eq_false_iff_not] at hg; omega
      subst this
      exact (⟨hu, hh⟩ : Mid A cfg J r s0 ws os (("rg", .ofNat 64 gs.length) :: base) u ∧
        HighIs A (storedUpTo cfg H gs gs.length) u))) ?_
  · have htn : t < gs.length := of_decide_eq_true ht
    have hgt : gs[t] ∈ gs := List.getElem_mem htn
    obtain ⟨hix, _⟩ := ix_known hc (hk _ hgt)
    have hix64 : groupIx cfg gs[t].name < groupsMax := by omega
    have hnt := hnum _ hgt
    let F (t' : Nat) : Assn σ := fun u => HighIs A (storedUpTo cfg H gs t') u ∧ t ≤ gs.length
    refine frag_append (xs := [_]) (frag_conseq (mid_assign_and o h (y := "rx") (by decide)
      (E := .loadWord (.op .add (.op .add (.var "rsl") (.const (.ofNat 64 slotGroups))) (.mul (.var "rg")
        (.const (.ofNat 64 8))))) rfl (val := gWord cfg gs[t])
      (fun u hu => by
        rw [groupW_eval h hu hic rfl (by omega) rfl]
        exact congrArg some ((hu.rest.slots i hi hic).groups t htn)) (F := F t) (fun _ _ h => h) (fun _ h => h))
      (fun u ⟨hu, hh, _⟩ => ⟨hu, hh, by omega⟩) fun _ h => h) ?_
    refine frag_append (xs := [_]) (mid_assign_and o h (y := "rc") (by decide)
      (E := .op .add (.var "jz") (.shiftR (.var "rx") (.const (.ofNat 64 32)))) rfl
      (val := .ofNat 64 (groupIx cfg gs[t].name))
      (fun u hu => by
        simp only [eval, jz_kept h hu.kept, vals_lookup hu.vals (x := "rx") rfl]
        rw [show (BitVec.ofNat 64 32).toNat = 32 from rfl]
        simp only [show ((32 : Nat) ≠ 0 && 32 ≥ 64) = false from rfl, Bool.false_eq_true, if_false]
        rw [gWord, group_ix (by omega) (by omega)]; simp) (fun _ _ h => h) (fun _ h => h)) ?_
    refine frag_append (xs := [_]) (ScanRun.kept_skip o hfl hfd (by decide)
      (fun s c ⟨h1, h2⟩ => ⟨mid_clock s c h1, h2⟩) fun u ⟨hu, _⟩ =>
        ⟨_, vals_lookup hu.vals rfl, by simp only [groupsMax] at hix64 ⊢; omega⟩) ?_
    refine frag_append (xs := [_]) (M := fun u => Mid A cfg J r s0 ws os
      (("rc", .ofNat 64 (groupIx cfg gs[t].name)) :: without "rc" (("rx", gWord cfg gs[t]) ::
        without "rx" (("rg", .ofNat 64 t) :: base))) u ∧ F (t + 1) u)
      (frag_conseq (high_store o h hp hix64 rfl (E := .op .and_ (.var "rx")
      (.const (.ofNat 64 (2 ^ 32 - 1)))) rfl (val := gs[t].number) (hh := storedUpTo cfg H gs t)
      (fun u hu => by
        simp only [eval, vals_lookup hu.vals (x := "rx") rfl]
        rw [gWord, sizes_low (by omega)])) (fun u ⟨hu, hh, _⟩ => ⟨hu, hh⟩)
      (fun u ⟨hu, hh⟩ => ⟨hu, (storedUpTo_succ htn hc (by simpa [gs] using hnd) (by simpa [gs] using hk)) ▸ hh,
        by omega⟩)) ?_
    exact frag_conseq (mid_assign_and o h (y := "rg") (by decide)
      (E := .op .add (.var "rg") (.const (.ofNat 64 1))) rfl (val := .ofNat 64 (t + 1)) (fun u hu => by
        simp only [eval, vals_lookup hu.vals (x := "rg") rfl, BitVec.ofNat_add]) (F := F (t + 1)) (fun _ _ h => h)
        (fun _ h => h)) (fun _ h => h) fun u ⟨hu, hh, _⟩ =>
      ⟨mid_lookups hu ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, trivial⟩, hh, by omega⟩
  exact frag_conseq (mid_assign_and o h (y := "ri") (by decide)
    (E := .op .add (.var "ri") (.const (.ofNat 64 1))) rfl (val := .ofNat 64 (i + 1)) (fun u hu => by
      simp only [eval, vals_lookup hu.vals (x := "ri") rfl, BitVec.ofNat_add]) (F := HighIs A _) (fun _ _ h => h)
      (fun _ h => h)) (fun _ h => h) fun u ⟨hu, hh⟩ => ⟨mid_lookups hu ⟨rfl, rfl, rfl, rfl, trivial⟩, hh⟩

theorem highOf_lt {cfg : Config} {cs : List Commit} (hc : ∀ c ∈ cs, ∀ g ∈ c.groups, g.number < 2 ^ 31) (x : Nat) :
    highOf cfg cs x < 2 ^ 31 := by
  have key : ∀ (ds : List Commit) (acc : Nat), acc < 2 ^ 31 → (∀ c ∈ ds, ∀ g ∈ c.groups, g.number < 2 ^ 31) →
      ds.foldl (fun h c => match c.groups.find? (fun g => groupIx cfg g.name = x) with
        | some g => g.number
        | none => h) acc < 2 ^ 31 := by
    intro ds
    induction ds with
    | nil => intro acc h _; exact h
    | cons d ds ih =>
      intro acc hacc hd
      simp only [List.foldl_cons]
      refine ih _ ?_ fun c hc' => hd c (List.mem_cons_of_mem _ hc')
      cases e : d.groups.find? (fun g => groupIx cfg g.name = x) with
      | some g => exact hd d (List.mem_cons_self ..) g (List.mem_of_find?_eq_some e)
      | none => exact hacc
  exact key cs 0 (by decide) hc

theorem storedUpTo_all (cfg : Config) (cs : List Commit) {i : Nat} (hi : i < cs.length) :
    storedUpTo cfg (highOf cfg (cs.take i)) cs[i].groups cs[i].groups.length = highOf cfg (cs.take (i + 1)) := by
  funext x
  rw [List.take_succ_eq_append_getElem hi, highOf_snoc]
  simp only [storedUpTo, List.take_length]

/-- Whether commit `i` has a group whose number is not above what the commits before it left at its place. -/
def badC (cfg : Config) (cs : List Commit) (i : Nat) : Bool :=
  match cs[i]? with
  | some c => (firstIdx (groupBad cfg (highOf cfg (cs.take i)) c.groups) c.groups.length).isSome
  | none => false

/-- What the check of commit `i` leaves where it finds a number not above: that number in `rv`, its group's place in
`rc`. -/
def BadAt (cfg : Config) (cs : List Commit) (i : Nat) (u : PancakeState σ) : Prop :=
  ∀ (hi : i < cs.length) t (ht : t < cs[i].groups.length),
    firstIdx (groupBad cfg (highOf cfg (cs.take i)) cs[i].groups) cs[i].groups.length = some t →
    u.locals "rv" = some (.ofNat 64 cs[i].groups[t].number) ∧
    u.locals "rc" = some (.ofNat 64 (groupIx cfg cs[i].groups[t].name))

/-- **Commit `k` checked**, and its numbers stored when they rise. -/
theorem highsOne_frag (o : Oracle σ) {fail : List Syntax.PStmt} (hfl : LowKK fail) (hfd : declared fail = [])
    {A : Word} {cfg : Config} {J : Bytes} {r : RSt} {s0 : PancakeState σ} (h : PBase A s0) (hp : r.phase < 5)
    {ws : Nat → Word} {os : List (Nat × Word)} (hcap : r.commits.length ≤ capacity)
    (hc : cfg.groups.length ≤ groupsMax) (hok : ∀ c ∈ r.commits, c.ok = true)
    (hk : ∀ c ∈ r.commits, ∀ g ∈ c.groups, cfg.groups.contains g.name = true) {k : Nat} (hkn : k < r.commits.length)
    (vcm : Value) :
    Frag o (highsBody fail)
      (fun u => Mid A cfg J r s0 ws os [("ri", .ofNat 64 k), ("rbad", bw false), ("rcm", vcm), ("rgo", 1)] u ∧
        HighIs A (highOf cfg (r.commits.take k)) u)
      (fun u => if badC cfg r.commits k then
          Mid A cfg J r s0 ws os [("ri", .ofNat 64 k), ("rbad", bw true), ("rcm", vcm), ("rgo", 1)] u ∧
            HighIs A (highOf cfg (r.commits.take k)) u ∧ BadAt cfg r.commits k u
        else Mid A cfg J r s0 ws os [("ri", .ofNat 64 (k + 1)), ("rbad", bw false), ("rcm", vcm), ("rgo", 1)] u ∧
            HighIs A (highOf cfg (r.commits.take (k + 1))) u) := by
  have hn := nums
  have hkc : k < capacity := by omega
  let cs := r.commits
  have hck : cs[k] ∈ cs := List.getElem_mem hkn
  obtain ⟨-, -, -, hgc, hgr, -, -, -⟩ := ok_bounds (hok _ hck)
  have hnum : ∀ g ∈ cs[k].groups, g.number < 2 ^ 31 := fun g hg => (hgr g hg).2.2
  have hix : ∀ g ∈ cs[k].groups, groupIx cfg g.name < groupsMax := fun g hg => by
    have := (ix_known hc (hk _ hck g hg)).1; omega
  have hnd := ok_nodup (hok _ hck)
  have hH : ∀ x, highOf cfg (cs.take k) x < 2 ^ 31 := highOf_lt fun c hc' g hg =>
    (ok_bounds (hok c (List.mem_of_mem_take hc'))).2.2.2.2.1 g hg |>.2.2
  unfold highsBody
  refine frag_append (xs := [_]) (mid_assign_and o h (y := "rsl") (by decide)
    (E := .op .add (.op .add (.var "rsc") (.const (.ofNat 64 rSlots))) (.mul (.var "ri") (.const (.ofNat 64 slotSize))))
    rfl (fun u hu => index_eval (rsc_kept h hu.kept) (vals_lookup hu.vals rfl) rSlots slotSize) highIs_clock
    (fun _ h => h)) ?_
  refine frag_append (xs := [_]) (mid_assign_and o h (y := "rgc") (by decide)
    (E := .op .and_ (slotWE slotMisc) (.const (.ofNat 64 255))) rfl (val := .ofNat 64 cs[k].groups.length)
    (fun u hu => by
      have em := slotP_eval h hu hkc (p := "rsl") rfl (x := slotMisc) (by decide) (by decide)
      rw [(hu.rest.slots k hkn hkc).misc] at em
      simp only [eval, em]
      rw [misc_count (g := cs[k].groups.length) (by simp only [ScanProg.groupsMax] at hgc; omega)])
    highIs_clock (fun _ h => h)) ?_
  refine frag_append (xs := [_]) (ScanRun.kept_skip o hfl hfd (by decide)
    (fun s c ⟨h1, h2⟩ => ⟨mid_clock s c h1, h2⟩) fun u ⟨hu, _⟩ => ⟨_, vals_lookup hu.vals rfl, hgc⟩) ?_
  refine frag_append (xs := [_]) (M := fun u => Mid A cfg J r s0 ws os
        [("rg", .ofNat 64 0), ("rbad", bw false), ("rgc", .ofNat 64 cs[k].groups.length), ("rsl", at_ A (slotAt k)),
          ("ri", .ofNat 64 k), ("rcm", vcm), ("rgo", 1)] u ∧ HighIs A (highOf cfg (cs.take k)) u)
    (frag_conseq (mid_assign_and o h (y := "rg") (by decide)
    (E := .op .add (.var "jz") (.const 0)) rfl (val := .ofNat 64 0) (fun u hu => by simp [eval, jz_kept h hu.kept])
    highIs_clock (fun _ h => h)) (fun _ h => h) fun u ⟨hu, hh⟩ =>
      ⟨mid_lookups hu ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, trivial⟩, hh⟩) ?_
  refine frag_append (xs := [_]) (checkGroups_frag o hfl hfd h hkn hkc hix hnum hH vcm) ?_
  have hb : badC cfg cs k = (firstIdx (groupBad cfg (highOf cfg (cs.take k)) cs[k].groups)
      cs[k].groups.length).isSome := by
    show (match r.commits[k]? with | some c => _ | none => false) = _
    rw [List.getElem?_eq_getElem hkn]
  refine frag_if o (C := .var "rbad") rfl (fun k => ⟨k, rfl⟩) (lowKK_groupsStore hfl) rfl rfl (fun s c h => by
      by_cases e : badC cfg cs k
      · rw [if_pos e] at h ⊢; exact ⟨mid_clock s c h.1, h.2.1, h.2.2⟩
      · rw [if_neg e] at h ⊢; exact ⟨mid_clock s c h.1, h.2⟩)
    (b := badC cfg cs k) (fun u ⟨hu, _⟩ => by rw [hb]; exact vals_lookup hu.vals rfl) (fun e => ?_) fun e => ?_
  · refine frag_nil o fun u ⟨hu, hh, hf⟩ => ?_
    rw [if_pos e]
    rw [← hb, e] at hu
    exact ⟨mid_lookups hu ⟨rfl, rfl, rfl, rfl, trivial⟩, hh, fun _ t ht h2 => hf t ht h2⟩
  · refine frag_conseq (storeGroups_frag o hfl hfd h hp hkn hkc hc hnd (hk _ hck) hnum
      (J := J) (ws := ws) (os := os) vcm)
      (fun u ⟨hu, hh, _⟩ => ⟨by rw [← hb, e] at hu; exact hu, hh⟩) fun u ⟨hu, hh⟩ => ?_
    rw [if_neg (by rw [e]; decide)]
    exact ⟨hu, by rw [← storedUpTo_all cfg cs hkn]; exact hh⟩

theorem lowKK_highsBody {fail : List Syntax.PStmt} (hfl : LowKK fail) : LowKK (highsBody fail) :=
  lowKK_append (lowKK_append (lowKK_append (xs := [_, _]) (lowK_any _ (k := .skip) (c := _) rfl)
    (lowKK_append (xs := [_]) (lowKK_kept hfl _ _) (lowK_any _ (k := .skip) (c := _) rfl))) (lowKK_groupsCheck hfl))
    (lowKK_ite rfl (fun k => ⟨k, rfl⟩) (lowKK_groupsStore hfl))

/-- **The commits checked in turn**: the first whose numbers do not rise, or each one's stored. -/
theorem highsLoop_frag (o : Oracle σ) {fail : List Syntax.PStmt} (hfl : LowKK fail) (hfd : declared fail = [])
    {A : Word} {cfg : Config} {J : Bytes} {r : RSt} {s0 : PancakeState σ} (h : PBase A s0) (hp : r.phase < 5)
    {ws : Nat → Word} {os : List (Nat × Word)} (hcap : r.commits.length ≤ capacity)
    (hc : cfg.groups.length ≤ groupsMax) (hok : ∀ c ∈ r.commits, c.ok = true)
    (hk : ∀ c ∈ r.commits, ∀ g ∈ c.groups, cfg.groups.contains g.name = true) :
    Frag o (highs fail) (fun u => Mid A cfg J r s0 ws os [("rcm", .ofNat 64 r.commits.length), ("rgo", 1)] u ∧
        HighIs A (fun _ => 0) u)
      (fun u => Mid A cfg J r s0 ws os
          [("ri", .ofNat 64 ((firstIdx (badC cfg r.commits) r.commits.length).getD r.commits.length)),
           ("rbad", bw (firstIdx (badC cfg r.commits) r.commits.length).isSome),
           ("rcm", .ofNat 64 r.commits.length), ("rgo", 1)] u ∧
        HighIs A (highOf cfg (r.commits.take
          ((firstIdx (badC cfg r.commits) r.commits.length).getD r.commits.length))) u ∧
        ∀ i, firstIdx (badC cfg r.commits) r.commits.length = some i → BadAt cfg r.commits i u) := by
  have hn := nums
  let cs := r.commits
  let n := cs.length
  let R (k : Nat) (f : Option Nat) : Assn σ := fun u => Mid A cfg J r s0 ws os
    [("ri", .ofNat 64 (f.getD k)), ("rbad", bw f.isSome), ("rcm", .ofNat 64 n), ("rgo", 1)] u ∧
    HighIs A (highOf cfg (cs.take (f.getD k))) u ∧ ∀ i, f = some i → BadAt cfg cs i u
  refine frag_append (xs := [_]) (mid_assign_and o h (y := "rbad") (by decide) (E := .op .add (.var "jz") (.const 0))
    rfl (val := bw false) (fun u hu => by simp [eval, jz_kept h hu.kept, bw]) highIs_clock (fun _ h => h)) ?_
  refine frag_append (xs := [_]) (frag_conseq (mid_assign_and o h (y := "ri") (by decide)
    (E := .op .add (.var "jz") (.const 0)) rfl (val := .ofNat 64 0) (fun u hu => by simp [eval, jz_kept h hu.kept])
    highIs_clock (fun _ h => h)) (fun _ h => h) fun u ⟨hu, hh⟩ => (⟨mid_lookups hu ⟨rfl, rfl, rfl, rfl, trivial⟩,
      hh, fun _ hi => nomatch hi⟩ : R 0 none u)) ?_
  refine firstIdx_frag o rfl (lowKK_highsBody hfl) rfl (R := R) (fun _ _ s t ⟨h1, h2⟩ => ⟨mid_clock s t h1, h2⟩)
    (fun k u hkn ⟨hu, _⟩ => search_guard (e := 1) (by decide) (by decide) (fun _ hj => (firstIdx_lt hj).1) hkn
      (by omega) (vals_lookup hu.vals rfl) (by rw [← bw_nat]; exact vals_lookup hu.vals rfl)
      (vals_lookup hu.vals rfl))
    (fun k hf hkn => ?_) fun _ _ _ hu => hu
  refine frag_conseq (highsOne_frag o hfl hfd h hp hcap hc hok hk hkn (J := J) (ws := ws) (os := os)
    (.ofNat 64 n)) (fun u ⟨hu, hh, _⟩ => ⟨hu, hh⟩) fun u hu => ?_
  by_cases e : badC cfg cs k
  · rw [if_pos e] at hu
    rw [if_pos e]
    obtain ⟨hu, hh, hb⟩ := hu
    exact ⟨hu, hh, fun i hi => by cases hi; exact hb⟩
  · rw [if_neg e] at hu
    rw [if_neg e]
    obtain ⟨hu, hh⟩ := hu
    exact ⟨hu, hh, fun _ hi => nomatch hi⟩

/-- The highest numbers where the first `k` commits rise: what `highIn` says. -/
theorem high_prefix {cfg : Config} (hc : cfg.groups.length ≤ groupsMax) {cs : List Commit}
    (hf : ∀ c ∈ cs, FitsCfg cfg c) {k : Nat} (hk : k ≤ cs.length) (hr : Rising (cs.take k)) {nm : Bytes}
    (hnm : cfg.groups.contains nm = true) : highIn (cs.take k) nm = highOf cfg (cs.take k) (groupIx cfg nm) := by
  have := high_take hc (cs := cs.take k) (fun c hc' => hf c (List.mem_of_mem_take hc')) hr k (by simp; omega) nm hnm
  rwa [List.take_take, Nat.min_self] at this

/-- The program's check of commit `k` is the specification's where the commits before it rise. -/
theorem badC_eq {cfg : Config} (hc : cfg.groups.length ≤ groupsMax) {cs : List Commit}
    (hf : ∀ c ∈ cs, FitsCfg cfg c) {k : Nat} (hk : k < cs.length) (hr : Rising (cs.take k)) :
    badC cfg cs k = RecoverSpec.badAt cs k := by
  simp only [badC, RecoverSpec.badAt, List.getElem?_eq_getElem hk]
  rw [firstIdx_isSome]
  apply Bool.eq_iff_iff.2
  simp only [List.any_eq_true, List.mem_range]
  constructor
  · rintro ⟨t, ht, hb⟩
    simp only [groupBad, List.getElem?_eq_getElem ht, decide_eq_true_eq] at hb
    refine ⟨cs[k].groups[t], List.getElem_mem ht, ?_⟩
    simp only [RecoverSpec.badGroup, decide_eq_true_eq]
    rw [high_prefix hc hf (by omega) hr ((hf _ (List.getElem_mem hk)).2 _ (List.getElem_mem ht))]
    exact hb
  · rintro ⟨g, hg, hb⟩
    obtain ⟨t, ht, rfl⟩ := List.getElem_of_mem hg
    refine ⟨t, ht, ?_⟩
    simp only [groupBad, List.getElem?_eq_getElem ht, decide_eq_true_eq]
    simp only [RecoverSpec.badGroup, decide_eq_true_eq] at hb
    rw [← high_prefix hc hf (by omega) hr ((hf _ (List.getElem_mem hk)).2 _ hg)]
    exact hb

/-- One more commit rises where it has no number not above. -/
theorem rising_succ {cs : List Commit} {k : Nat} (hk : k < cs.length) (hr : Rising (cs.take k))
    (hb : RecoverSpec.badAt cs k = false) : Rising (cs.take (k + 1)) := by
  intro i hi g hg
  simp only [List.length_take] at hi
  rw [List.take_take, Nat.min_eq_left (by omega)]
  rw [List.getElem_take] at hg
  rcases Nat.lt_succ_iff_lt_or_eq.1 (show i < k + 1 by omega) with hik | rfl
  · have := hr i (by simp; omega) g (by rw [List.getElem_take]; exact hg)
    rwa [List.take_take, Nat.min_eq_left (by omega)] at this
  · simp only [RecoverSpec.badAt, List.getElem?_eq_getElem hk, List.any_eq_false] at hb
    have := hb g hg
    simp only [RecoverSpec.badGroup, decide_eq_true_eq, Nat.not_le] at this
    exact this

/-- **Rising, as the program checks it**: while no commit before `k` has a number not above, the first `k` commits
rise. -/
theorem badC_rising {cfg : Config} (hc : cfg.groups.length ≤ groupsMax) {cs : List Commit}
    (hf : ∀ c ∈ cs, FitsCfg cfg c) : ∀ k, k ≤ cs.length → firstIdx (badC cfg cs) k = none → Rising (cs.take k)
  | 0, _, _ => fun i hi => by simp at hi
  | k + 1, hk, hn => by
    rw [firstIdx_succ] at hn
    have hk' : firstIdx (badC cfg cs) k = none := by
      cases e : firstIdx (badC cfg cs) k with
      | none => rfl
      | some _ => rw [e] at hn; cases hn
    have hb : badC cfg cs k = false := by
      rw [hk'] at hn
      cases e : badC cfg cs k with
      | false => rfl
      | true => rw [e] at hn; cases hn
    have hr := badC_rising hc hf k (by omega) hk'
    exact rising_succ (by omega) hr (by rw [← badC_eq hc hf (by omega) hr]; exact hb)

/-- **The first commit the program finds** with a number not above is the specification's. -/
theorem firstBad_eq {cfg : Config} (hc : cfg.groups.length ≤ groupsMax) {cs : List Commit}
    (hf : ∀ c ∈ cs, FitsCfg cfg c) : ∀ k, k ≤ cs.length → firstIdx (badC cfg cs) k = firstIdx (RecoverSpec.badAt cs) k
  | 0, _ => rfl
  | k + 1, hk => by
    rw [firstIdx_succ, firstIdx_succ, firstBad_eq hc hf k (by omega)]
    cases e : firstIdx (RecoverSpec.badAt cs) k with
    | some _ => rfl
    | none =>
      have hr := badC_rising hc hf k (by omega) (by rw [firstBad_eq hc hf k (by omega)]; exact e)
      rw [badC_eq hc hf (by omega) hr]

/-- **The group the program refuses** where commit `i` is the first with a number not above: its first such group,
the specification's. -/
theorem notAbove_eq {cfg : Config} (hc : cfg.groups.length ≤ groupsMax) {cs : List Commit}
    (hf : ∀ c ∈ cs, FitsCfg cfg c) {i : Nat} (hi : firstIdx (badC cfg cs) cs.length = some i) :
    ∃ (hil : i < cs.length) (t : Nat) (ht : t < cs[i].groups.length),
      firstIdx (groupBad cfg (highOf cfg (cs.take i)) cs[i].groups) cs[i].groups.length = some t ∧
      notAbove? [] cs = some (cs[i].groups[t].name, cs[i].groups[t].number) := by
  obtain ⟨hil, hb, h0⟩ := firstIdx_some hi
  have hr := badC_rising hc hf i (by omega) h0
  have hc' : cs[i] ∈ cs := List.getElem_mem hil
  have hpe : RecoverSpec.testAt (RecoverSpec.badGroup cs i) cs[i].groups =
      groupBad cfg (highOf cfg (cs.take i)) cs[i].groups := by
    funext t
    simp only [groupBad, RecoverSpec.testAt]
    cases e : cs[i].groups[t]? with
    | none => rfl
    | some g =>
      have hg : g ∈ cs[i].groups := List.mem_of_getElem? e
      simp only [RecoverSpec.badGroup]
      rw [high_prefix hc hf (by omega) hr ((hf _ hc').2 g hg)]
  simp only [badC, List.getElem?_eq_getElem hil] at hb
  obtain ⟨t, ht⟩ := Option.isSome_iff_exists.1 hb
  obtain ⟨htl, -, -⟩ := firstIdx_some ht
  refine ⟨hil, t, htl, ht, ?_⟩
  rw [RecoverSpec.notAbove_first, ← firstBad_eq hc hf _ (Nat.le_refl _), hi]
  simp only [Option.bind_some, List.getElem?_eq_getElem hil]
  rw [find_first, hpe, ht]
  simp [List.getElem?_eq_getElem htl]

theorem lowKK_idDups {fail : List Syntax.PStmt} (hfl : LowKK fail) : LowKK (idDups fail) :=
  lowKK_append (xs := [_]) (lowK_any _ (k := .skip) (c := _) rfl) (lowKK_while rfl
    (lowKK_append (xs := [_, _]) (lowK_any _ (k := .skip) (c := _) rfl) (lowKK_append (xs := [_])
      (lowKK_kept hfl _ _) (lowK_any _ (k := .skip) (c := _) rfl))))

theorem lowKK_highs {fail : List Syntax.PStmt} (hfl : LowKK fail) : LowKK (highs fail) :=
  lowKK_append (xs := [_, _]) (lowK_any _ (k := .skip) (c := _) rfl) (lowKK_while rfl (lowKK_highsBody hfl))

/-- The program past the check of how many commits there are. -/
theorem lowKK_rising {fail : List Syntax.PStmt} (hfl : LowKK fail) : LowKK (rising fail) :=
  lowKK_append (lowKK_append (lowK_any _ (k := .skip) (c := _) rfl) (lowKK_highs hfl))
    (lowK_any _ (k := .skip) (c := _) rfl)

theorem lowKK_ruleChecks {fail : List Syntax.PStmt} (hfl : LowKK fail) : LowKK (ruleChecks fail) :=
  lowKK_append (lowK_any _ (k := .skip) (c := _) rfl) (lowKK_append (xs := [_])
    (lowKK_ite rfl (fun k => ⟨k, rfl⟩) (lowKK_idDups hfl))
    (lowKK_ite rfl (lowK_any _ (k := .skip) (c := _) rfl)
      (lowKK_ite rfl (lowK_any _ (k := .skip) (c := _) rfl) (lowKK_rising hfl))))

theorem highIs_scalar {A : Word} {u : PancakeState σ} {H : Nat → Nat} (h : HighIs A H u) {y : Nat}
    (hy : y ∈ scalarOffs) (v : Word) : HighIs A H (stW u A y v) := fun x hx => by
  have hn := nums
  have := (free_scalar y hy).1
  simp only [Free] at this
  rw [stW_word (by omega) (by omega) (by omega)]; exact h x hx

/-- **Phase 4**, the rules: no more commits than the index holds, no number or Message-ID twice, no group the
configuration lacks, numbers that rise; then phase 5. -/
theorem rules_frag (o : Oracle σ) {fail : List Syntax.PStmt} (hfl : LowKK fail) (hfd : declared fail = [])
    {A : Word} {cfg : Config} {J : Bytes} {r : RSt} {s0 : PancakeState σ} (h : PIn A cfg J r s0)
    (hp : r.phase = 4) (hfr : r.fresh = false) (hok : ∀ c ∈ r.commits, c.ok = true)
    (hcl : r.commits.length < 2 ^ 62)
    (hk : r.commits.length ≤ capacity → r.unknown = none →
      ∀ c ∈ r.commits, ∀ g ∈ c.groups, cfg.groups.contains g.name = true) :
    Frag o (RecoverProg.rules fail) (Like s0) (POut A cfg J s0 (RecoverSpec.rules r)) := by
  have hb := h.toPBase
  refine from_start h ?_
  refine frag_append (xs := [_]) (mid_assign o hb (y := "rcm") (by decide) (rw_lower (by decide))
    (val := .ofNat 64 r.commits.length) fun u hu => by rw [mid_rw hb hu (by decide) (rw_lower (by decide))]; rfl) ?_
  refine frag_if o (C := FramerCode.leE (.const (.ofNat 64 (capacity + 1))) (.var "rcm")) rfl
    (lowK_any _ (k := .skip) (c := _) rfl) (lowKK_append (lowK_any _ (k := .skip) (c := _) rfl) (lowKK_ruleChecks hfl))
    rfl rfl pout_clock
    (b := decide (capacity + 1 ≤ r.commits.length))
    (fun u hu => FramerCode.eval_le (by decide) (by omega) rfl (vals_lookup hu.vals (lookup_head _ _ _)))
    (fun e => ?_) fun e => ?_
  · -- too many commits
    rw [RecoverSpec.rules, if_pos (of_decide_eq_true e)]
    refine frag_append (xs := [_]) (mid_out o hb (x := rFaultA) (by decide) apart_nil (E := .var "rcm") rfl
      (val := .ofNat 64 r.commits.length) fun u hu => vals_lookup hu.vals (lookup_head _ _ _)) ?_
    refine frag_conseq (refused_frag o hb (.tooMany 0) (by rfl)) (fun _ h => h) fun u hu => ?_
    exact mid_end hu (fun _ _ => rfl) (fun hr => hr) ⟨vals_lookup hu.vals rfl, outs_lookup hu.outs rfl,
      outs_lookup hu.outs rfl, outs_lookup hu.outs rfl⟩
  have hcap : r.commits.length ≤ capacity := by have := of_decide_eq_false e; omega
  rw [RecoverSpec.rules, if_neg (by have := of_decide_eq_false e; omega)]
  refine frag_append (xs := held "rcm")
    (M := Mid A cfg J r s0 (scalars cfg r) [] [("rcm", .ofNat 64 r.commits.length), ("rgo", 1)])
    (frag_conseq (held_frag o hb rfl hcap) (fun _ h => h) fun u hu => mid_lookups hu ⟨rfl, rfl, trivial⟩) ?_
  unfold ruleChecks
  refine frag_append (xs := seqDups) (seqDups_frag o hb (fun c hc => (ok_bounds (hok c hc)).1) hcap) ?_
  have hsq := RecoverSpec.seqTwice_first r.commits
  have hid := RecoverSpec.idTwice_first r.commits
  cases hs : firstIdx (dupAt (·.seq) r.commits) r.commits.length with
  | some i =>
    -- a number twice
    obtain ⟨hi, -, -⟩ := firstIdx_some hs
    have hsq' : seqTwice? r.commits = some r.commits[i].seq := by
      rw [hsq, hs]; simp [List.getElem?_eq_getElem hi]
    rw [hsq']
    simp only [Option.getD_some, Option.isSome_some]
    let P (u : PancakeState σ) : Prop := Mid A cfg J r s0 (scalars cfg r) [] [("ri", .ofNat 64 i), ("rdup", bw true),
      ("rcm", .ofNat 64 r.commits.length), ("rgo", 1)] u ∧
      ∀ i' (hi' : i' < r.commits.length), some i = some i' → u.locals "rv" = some (.ofNat 64 r.commits[i'].seq)
    have hPc : Safe.ClockFree P := fun s k ⟨h1, h2⟩ => ⟨mid_clock s k h1, h2⟩
    refine frag_append (xs := [_]) (M := P) (frag_if o (C := .var "rdup") rfl (fun k => ⟨k, rfl⟩) (lowKK_idDups hfl)
      rfl rfl hPc (b := true) (fun u ⟨hu, _⟩ => vals_lookup hu.vals rfl) (fun _ => frag_nil o fun _ h => h)
      fun e => absurd e (by decide)) ?_
    refine frag_if o (C := .var "rdup") rfl (lowK_any _ (k := .skip) (c := _) rfl)
      (lowKK_ite rfl (lowK_any _ (k := .skip) (c := _) rfl) (lowKK_rising hfl)) rfl rfl pout_clock (b := true)
      (fun u ⟨hu, _⟩ => vals_lookup hu.vals rfl) (fun _ => ?_) fun e => absurd e (by decide)
    refine frag_if o (C := .cmp .equal (.var "rdup") (.const (.ofNat 64 1))) rfl
      (lowK_any _ (k := .skip) (c := _) rfl) (lowK_any _ (k := .skip) (c := _) rfl) rfl rfl pout_clock (b := true)
      (fun u ⟨hu, _⟩ => FramerCode.eval_eq (x := 1) (y := 1) (by decide) (by decide)
        (ev_var (vals_lookup hu.vals rfl)) rfl) (fun _ => ?_) fun e => absurd e (by decide)
    refine frag_append (xs := [_]) (frag_conseq (mid_out o hb (x := rFaultA) (by decide) apart_nil (E := .var "rv") rfl
      (l := [("rv", .ofNat 64 r.commits[i].seq), ("rgo", 1)]) (val := .ofNat 64 r.commits[i].seq)
      fun u hu => vals_lookup hu.vals rfl) (fun u ⟨hu, hrv⟩ => mid_lookups (mid_add hu (hrv i hi rfl))
        ⟨rfl, rfl, trivial⟩) fun _ h => h) ?_
    refine frag_conseq (refused_frag o hb (.seqTwice 0) (by rfl)) (fun _ h => h) fun u hu => ?_
    exact mid_end hu (fun _ _ => rfl) (fun hr => hr) ⟨vals_lookup hu.vals rfl, outs_lookup hu.outs rfl,
      outs_lookup hu.outs rfl, outs_lookup hu.outs rfl⟩
  | none =>
    simp only [Option.getD_none, Option.isSome_none]
    have hsq' : seqTwice? r.commits = none := by rw [hsq, hs]; rfl
    rw [hsq']
    let n := r.commits.length
    let fd := firstIdx (dupAt (·.messageId) r.commits) n
    let Q (u : PancakeState σ) : Prop := Mid A cfg J r s0 (scalars cfg r) [] [("ri", .ofNat 64 (fd.getD n)),
        ("rdup", dupWord fd.isSome), ("rcm", .ofNat 64 n), ("rgo", 1)] u ∧
      ∀ i (hi : i < n), fd = some i → u.locals "rl" = some (.ofNat 64 r.commits[i].messageId.length)
    have hQc : Safe.ClockFree Q := fun s k ⟨h1, h2⟩ => ⟨mid_clock s k h1, h2⟩
    refine frag_append (xs := [_]) (M := Q) (frag_if o (C := .var "rdup") rfl (fun k => ⟨k, rfl⟩)
      (lowKK_idDups hfl) rfl rfl hQc (b := false) (fun u ⟨hu, _⟩ => vals_lookup hu.vals rfl)
      (fun e => absurd e (by decide)) fun _ => frag_conseq (idDups_frag o hfl hfd hb hcap)
        (fun u ⟨hu, _⟩ => mid_lookups hu ⟨rfl, rfl, rfl, trivial⟩) fun _ h => h) ?_
    cases hd : fd with
    | some i =>
      -- a Message-ID twice
      obtain ⟨hi, -, -⟩ := firstIdx_some hd
      have hid' : idTwice? r.commits = some r.commits[i].messageId := by
        rw [hid]; show fd.bind _ = _; rw [hd]; simp [List.getElem?_eq_getElem hi]
      rw [hid']
      refine frag_ifw o (c := Syntax.v "rdup") (C := .var "rdup") rfl (lowK_any _ (k := .skip) (c := _) rfl)
        (lowKK_ite rfl (lowK_any _ (k := .skip) (c := _) rfl) (lowKK_rising hfl))
        rfl rfl pout_clock (w := dupWord true) (fun u ⟨hu, _⟩ => vals_lookup hu.vals (by rw [hd]; rfl)) (fun _ => ?_)
        fun e => absurd e (by decide)
      refine frag_if o (C := .cmp .equal (.var "rdup") (.const (.ofNat 64 1))) rfl
        (lowK_any _ (k := .skip) (c := _) rfl) (lowK_any _ (k := .skip) (c := _) rfl) rfl rfl pout_clock (b := false)
        (fun u ⟨hu, _⟩ => FramerCode.eval_eq (x := 2) (y := 1) (by decide) (by decide)
          (ev_var (vals_lookup hu.vals (by rw [hd]; rfl))) rfl) (fun e => absurd e (by decide)) fun _ => ?_
      have hic : i < capacity := by omega
      obtain ⟨-, s2⟩ := slotAt_le hic
      have hx : rSlots + slotId + i * slotSize = slotAt i + slotId := by simp only [slotAt]; omega
      have hsz : slotId + 250 ≤ slotSize := by decide
      refine frag_append (xs := [_]) (frag_conseq (mid_out o hb (x := rFaultAt) (by decide) apart_nil
        (E := .op .add (.const (.ofNat 64 (rSlots + slotId))) (.mul (.var "ri") (.const (.ofNat 64 slotSize)))) rfl
        (l := [("ri", .ofNat 64 i), ("rl", .ofNat 64 r.commits[i].messageId.length), ("rgo", 1)])
        (val := .ofNat 64 (slotAt i + slotId)) fun u hu => by
          simp only [eval, vals_lookup hu.vals (x := "ri") rfl]
          rw [← BitVec.ofNat_mul, ← BitVec.ofNat_add, hx]) (fun u ⟨hu, hrl⟩ =>
          mid_lookups (mid_add hu (hrl i hi hd)) ⟨by rw [hd]; rfl, rfl, rfl, trivial⟩) fun _ h => h) ?_
      refine frag_append (xs := [_]) (mid_out o hb (x := rFaultLen) (by decide) (apart_of (by rfl))
        (E := .var "rl") rfl (val := .ofNat 64 r.commits[i].messageId.length) fun u hu => vals_lookup hu.vals rfl) ?_
      refine frag_conseq (refused_frag o hb (.idTwice []) (by rfl)) (fun _ h => h) fun u hu => ?_
      have hsl := hu.rest.slots i hi hic
      exact mid_end hu (fun _ _ => rfl) (fun hr => hr) ⟨vals_lookup hu.vals rfl, outs_lookup hu.outs rfl,
        outs_lookup hu.outs rfl, _, outs_lookup hu.outs rfl, outs_lookup hu.outs rfl, by have := hsl.idLen; omega,
        hsl.id⟩
    | none =>
      have hid' : idTwice? r.commits = none := by rw [hid]; show fd.bind _ = _; rw [hd]; rfl
      rw [hid']
      refine frag_ifw o (c := Syntax.v "rdup") (C := .var "rdup") rfl (lowK_any _ (k := .skip) (c := _) rfl)
        (lowKK_ite rfl (lowK_any _ (k := .skip) (c := _) rfl) (lowKK_rising hfl))
        rfl rfl pout_clock (w := dupWord false) (fun u ⟨hu, _⟩ => vals_lookup hu.vals (by rw [hd]; rfl))
        (fun e => absurd rfl e) fun _ => ?_
      refine frag_conseq (P0 := Mid A cfg J r s0 (scalars cfg r) [] [("rcm", .ofNat 64 n), ("rgo", 1)]) ?_
        (fun u ⟨hu, _⟩ => mid_lookups hu ⟨rfl, rfl, trivial⟩) fun _ h => h
      cases hun : r.unknown with
      | some g =>
        -- a group the configuration lacks
        refine frag_if o (C := .cmp .equal (rwE rUnknown) (.const (.ofNat 64 1))) rfl
          (lowK_any _ (k := .skip) (c := _) rfl) (lowKK_rising hfl) rfl rfl pout_clock (b := true)
          (fun u hu => FramerCode.eval_eq (x := 1) (y := 1) (by decide) (by decide)
            (by rw [mid_rw hb hu (by decide) (rw_lower (by decide))]; show some (bw r.unknown.isSome) = _
                rw [hun]; rfl) rfl) (fun _ => ?_) fun e => absurd e (by decide)
        refine frag_append (xs := [_]) (mid_out o hb (x := rFaultAt) (by decide) apart_nil
          (E := .const (.ofNat 64 rUnknownName)) rfl fun _ _ => rfl) ?_
        refine frag_append (xs := [_]) (mid_out o hb (x := rFaultLen) (by decide) (apart_of (by rfl))
          (E := rwE rUnknownLen) rfl (val := .ofNat 64 g.length) fun u hu =>
            (rw_eval hb.hA (by rw [hu.kept.memaddrs]; exact hb.dom) (rsc_kept hb hu.kept) (x := rUnknownLen)
              (by decide) (by decide) rfl).trans (congrArg some (hu.rest.unknown g hun).1)) ?_
        refine frag_conseq (refused_frag o hb (.unknownGroup []) (by rfl)) (fun _ h => h) fun u hu => ?_
        obtain ⟨-, hgl, hgb⟩ := hu.rest.unknown g hun
        exact mid_end hu (fun _ _ => rfl) (fun hr => hr) ⟨vals_lookup hu.vals rfl, outs_lookup hu.outs rfl,
          outs_lookup hu.outs rfl, _, outs_lookup hu.outs rfl, outs_lookup hu.outs rfl,
          by have : rUnknownName = 416 := rfl; have := nums; omega, hgb⟩
      | none =>
        refine frag_if o (C := .cmp .equal (rwE rUnknown) (.const (.ofNat 64 1))) rfl
          (lowK_any _ (k := .skip) (c := _) rfl) (lowKK_rising hfl) rfl rfl pout_clock (b := false)
          (fun u hu => FramerCode.eval_eq (x := 0) (y := 1) (by decide) (by decide)
            (by rw [mid_rw hb hu (by decide) (rw_lower (by decide))]; show some (bw r.unknown.isSome) = _
                rw [hun]; rfl) rfl) (fun e => absurd e (by decide)) fun _ => ?_
        have hcfg : cfg.groups.length ≤ groupsMax := h.area.rest.config.count
        have hfit : ∀ c ∈ r.commits, FitsCfg cfg c := fun c hc => ⟨ok_nodup (hok c hc), hk hcap hun c hc⟩
        unfold rising
        rw [List.append_assoc]
        refine frag_append (xs := zeroHigh) (zeroHigh_frag o hb (by omega)) ?_
        refine frag_append (xs := highs fail) (frag_conseq (highsLoop_frag o hfl hfd hb (by omega) hcap hcfg hok
          (hk hcap hun)) (fun u ⟨hu, hz⟩ => ⟨mid_lookups hu ⟨rfl, rfl, trivial⟩, hz⟩) fun _ h => h) ?_
        cases hbd : firstIdx (badC cfg r.commits) r.commits.length with
        | some i =>
          -- a number not above
          obtain ⟨hil, t, ht, hgt, hna⟩ := notAbove_eq hcfg hfit hbd
          rw [hna]
          simp only [Option.getD_some, Option.isSome_some]
          have hci : r.commits[i] ∈ r.commits := List.getElem_mem hil
          have hkn : cfg.groups.contains r.commits[i].groups[t].name = true :=
            hk hcap hun _ hci _ (List.getElem_mem ht)
          obtain ⟨hixl, hixn⟩ := ix_known hcfg hkn
          have hgx : cfg.groups[groupIx cfg r.commits[i].groups[t].name] = r.commits[i].groups[t].name := by
            have e : cfg.groups.getD (groupIx cfg r.commits[i].groups[t].name) [] =
                cfg.groups[groupIx cfg r.commits[i].groups[t].name] := by
              rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hixl]; rfl
            exact e.symm.trans hixn
          refine frag_if o (C := .var "rbad") rfl (lowK_any _ (k := .skip) (c := _) rfl)
            (lowK_any _ (k := .skip) (c := _) rfl) rfl rfl pout_clock (b := true)
            (fun u ⟨hu, _⟩ => vals_lookup hu.vals rfl) (fun _ => ?_) fun e => absurd e (by decide)
          let ix := groupIx cfg r.commits[i].groups[t].name
          refine frag_append (xs := [_]) (frag_conseq (mid_out o hb (x := rFaultA) (by decide) apart_nil
            (E := .var "rv") rfl (l := [("rv", .ofNat 64 r.commits[i].groups[t].number), ("rc", .ofNat 64 ix),
              ("rgo", 1)]) (val := .ofNat 64 r.commits[i].groups[t].number) fun u hu => vals_lookup hu.vals rfl)
            (fun u ⟨hu, _, hbad⟩ => mid_lookups (mid_add (mid_add hu (hbad i rfl hil t ht hgt).2)
              (hbad i rfl hil t ht hgt).1) ⟨rfl, rfl, rfl, trivial⟩) fun _ h => h) ?_
          have hgm : groupsMax = 64 := rfl
          have hgs : rGroupSlot = 72 := rfl
          have hix64 : ix * rGroupSlot ≤ 63 * 72 := Nat.mul_le_mul (by omega) (by omega)
          refine frag_append (xs := [_]) (mid_out o hb (x := rFaultAt) (by decide) (apart_of (by rfl))
            (E := .op .add (.const (.ofNat 64 (rGroups + 8))) (.mul (.var "rc") (.const (.ofNat 64 rGroupSlot)))) rfl
            (val := .ofNat 64 (rGroups + 8 + ix * rGroupSlot)) fun u hu => by
              simp only [eval, vals_lookup hu.vals (x := "rc") rfl]
              rw [← BitVec.ofNat_mul, ← BitVec.ofNat_add]) ?_
          refine frag_append (xs := [_]) (mid_out o hb (x := rFaultLen) (by decide) (apart_of (by rfl))
            (E := .loadWord (.op .add (.op .add (.var "rsc") (.const (.ofNat 64 rGroups)))
              (.mul (.var "rc") (.const (.ofNat 64 rGroupSlot))))) rfl
            (val := .ofNat 64 r.commits[i].groups[t].name.length) fun u hu => by
              have hg : rGroups = 640 := rfl
              have h72 : ix * rGroupSlot = ix * 72 := rfl
              rw [load_index_eval (rsc_kept hb hu.kept) (vals_lookup hu.vals (x := "rc") rfl)
                (area_dom hb hu.kept.memaddrs (by have := nums; omega) (by rw [h72]; omega)),
                hu.rest.config.len ix hixl, hgx]) ?_
          refine frag_conseq (refused_frag o hb (.numberNotAbove [] 0) (by rfl)) (fun _ h => h) fun u hu => ?_
          have hnm := hu.rest.config.name ix hixl
          rw [hgx] at hnm
          have hsh := hu.rest.config.short ix hixl
          rw [hgx] at hsh
          exact mid_end hu (fun _ _ => rfl) (fun hr => hr) ⟨vals_lookup hu.vals rfl, outs_lookup hu.outs rfl,
            outs_lookup hu.outs rfl, outs_lookup hu.outs rfl, _, outs_lookup hu.outs rfl, outs_lookup hu.outs rfl,
            by have := nums; omega, (show rGroups + 8 + ix * rGroupSlot = rGroups + ix * rGroupSlot + 8 by omega) ▸ hnm⟩
        | none =>
          have hna : notAbove? [] r.commits = none := by
            rw [RecoverSpec.notAbove_first, ← firstBad_eq hcfg hfit _ (Nat.le_refl _), hbd]; rfl
          rw [hna]
          simp only [Option.getD_none, Option.isSome_none, List.take_length]
          refine frag_if o (C := .var "rbad") rfl (lowK_any _ (k := .skip) (c := _) rfl)
            (lowK_any _ (k := .skip) (c := _) rfl) rfl rfl pout_clock (b := false)
            (fun u ⟨hu, _⟩ => vals_lookup hu.vals rfl) (fun e => absurd e (by decide)) fun _ => ?_
          refine frag_conseq (P0 := fun u => Mid A cfg J r s0 (scalars cfg r) [] [("rgo", 1)] u ∧
            HighIs A (highOf cfg r.commits) u) ?_ (fun u ⟨hu, hh, _⟩ => ⟨mid_lookups hu ⟨rfl, trivial⟩, hh⟩)
            fun _ h => h
          refine frag_append (xs := [_]) (mid_set_and o hb (x := rI) (by decide) (E := .const (.ofNat 64 0)) rfl
            (val := .ofNat 64 0) (fun _ _ _ => rfl) highIs_clock fun u v hh => highIs_scalar hh (by decide) v) ?_
          refine frag_append (xs := [_]) (mid_set_and o hb (x := rWait) (by decide) (E := .const (.ofNat 64 0)) rfl
            (val := .ofNat 64 0) (fun _ _ _ => rfl) highIs_clock fun u v hh => highIs_scalar hh (by decide) v) ?_
          refine frag_conseq (mid_set_and o hb (x := rPhase) (by decide) (E := .const (.ofNat 64 5)) rfl
            (val := .ofNat 64 5) (fun _ _ _ => rfl) highIs_clock fun u v hh => highIs_scalar hh (by decide) v)
            (fun _ h => h) fun u ⟨hu, hh⟩ => ?_
          refine mid_end hu (offs_all (by
              and_intros <;> first | rfl | (show bw r.unknown.isSome = _; rw [hun]; rfl)))
            (fun hr => ⟨fun h9 => by simp at h9, hr.nameLen, hr.name, (fun _ hg => nomatch hg), hr.config,
              (fun _ hf => hr.scan (by omega) hf), hr.slots, fun _ => ?_⟩) (vals_lookup hu.vals rfl)
          show HighAt A cfg (if r.fresh then [] else r.commits) u
          rw [hfr]; exact hh

end DN.News.RecoverArea
