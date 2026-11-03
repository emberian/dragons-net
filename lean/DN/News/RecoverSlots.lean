-- SPDX-License-Identifier: AGPL-3.0-or-later
import DN.News.RecoverScan
import DN.News.RecoverSearch

/-!
# DN.News.RecoverSlots

What phases 4 to 13 share: slot words read, the index's commit count, a local raised or listed again. Also `Rest` of a
later phase, a branch on a word, the refusals' stop, slot fields and search loops.
-/

namespace DN.News.RecoverArea

open DN.Compiler DN.Compiler.Wp DN.Compiler.Frag DN.News.Journal DN.News.Recovery
open DN.News.RecoverProg
open DN.News.RecoverSpec (RSt firstIdx firstIdx_succ firstIdx_mono)
open DN.News.ScanRun (at_ at_add vals_lookup without lookup_head frag_if)
open DN.News.FramerCode (bw ev_var ult_eval)

variable {σ : Type}

theorem apart_nil {x : Nat} : ∀ q ∈ ([] : List (Nat × Word)), q.1 ≠ x := fun _ h => nomatch h

/-- `Rest` of a state of a later phase, its other fields alike. -/
theorem rest_phase {A : Word} {cfg : Config} {J : Bytes} {r r' : RSt} {u : PancakeState σ} (h : Rest A cfg J r u)
    (hp : 5 ≤ r.phase) (hseq : r'.phase = 9 ∨ r'.phase = 12 → r'.seq = r.seq ∧ (r.phase = 9 ∨ r.phase = 12))
    (hn : r'.name = r.name) (hu : r'.unknown = r.unknown) (hs : r'.scan = r.scan) (hf : r'.fresh = r.fresh)
    (hc : r'.commits = r.commits) : Rest A cfg J r' u where
  seq := fun h9 => by obtain ⟨e, h9'⟩ := hseq h9; rw [e]; exact h.seq h9'
  nameLen := hn ▸ h.nameLen
  name := hn ▸ h.name
  unknown := hu ▸ h.unknown
  config := h.config
  scan := fun _ hfr => hs ▸ h.scan (by omega) (hf ▸ hfr)
  slots := hc ▸ h.slots
  high := fun _ => hf ▸ hc ▸ h.high hp

/-- A word of `scalars` one more. -/
theorem mid_inc (o : Oracle σ) {A : Word} {cfg : Config} {J : Bytes} {r : RSt} {s0 : PancakeState σ}
    (h : PBase A s0) {ws : Nat → Word} {os : List (Nat × Word)} {l : List (String × Value)} {x : Nat}
    (hx : x ∈ scalarOffs) (hE : Lower.lowerExp (Syntax.eAdd (rw x) (Syntax.n 1)) =
      some (.op .add (rwE x) (.const (.ofNat 64 1)))) {k : Nat} (hk : ws x = .ofNat 64 k) :
    Frag o [rset x (Syntax.eAdd (rw x) (Syntax.n 1))] (Mid A cfg J r s0 ws os l)
      (Mid A cfg J r s0 (upd ws x (.ofNat 64 (k + 1))) os l) :=
  mid_set o h hx hE fun u hu => by simp only [eval, mid_rw h hu hx (rw_lower hx), hk, BitVec.ofNat_add]

/-- `ri` given the word of `rI`, and that word one more. -/
theorem ri_frag (o : Oracle σ) {A : Word} {cfg : Config} {J : Bytes} {r : RSt} {s0 : PancakeState σ}
    (h : PBase A s0) {ws : Nat → Word} {os : List (Nat × Word)} {k : Nat} (hk : ws rI = .ofNat 64 k) :
    Frag o [.assign "ri" (rw rI), rset rI (Syntax.eAdd (Syntax.v "ri") (Syntax.n 1))]
      (Mid A cfg J r s0 ws os [("rgo", 1)])
      (Mid A cfg J r s0 (upd ws rI (.ofNat 64 (k + 1))) os [("ri", .ofNat 64 k), ("rgo", 1)]) :=
  frag_append (xs := [_]) (mid_assign o h (y := "ri") (by decide) (rw_lower (by decide)) (val := .ofNat 64 k)
    fun u hu => by rw [mid_rw h hu (by decide) (rw_lower (by decide)), hk])
    (mid_set o h (x := rI) (by decide) (E := .op .add (.var "ri") (.const (.ofNat 64 1))) rfl fun u hu => by
      simp only [eval, vals_lookup hu.vals (x := "ri") rfl, BitVec.ofNat_add])

/-- A word of the slot whose address is in `p`, as the program lowers it. -/
def slotPE (p : String) (x : Nat) : PancakeExp :=
  if x = 0 then .loadWord (.var p) else .loadWord (.op .add (.var p) (.const (.ofNat 64 x)))

/-- A word of the slot at `rsl`. -/
abbrev slotWE (x : Nat) : PancakeExp := slotPE "rsl" x

theorem slotP_lower (p : String) (x : Nat) :
    Lower.lowerExp (.loadw 1 (Syntax.atOff (Syntax.v p) x)) = some (slotPE p x) := by
  by_cases h0 : x = 0
  · subst h0; simp [slotPE, Syntax.atOff, Lower.lowerExp, Syntax.v]
  · simp [slotPE, Syntax.atOff, h0, Lower.lowerExp, Syntax.eAdd, Syntax.v, Syntax.n]

theorem slotW_lower (x : Nat) : Lower.lowerExp (slotW x) = some (slotWE x) := slotP_lower "rsl" x

/-- **A word of slot `i` read**, its address in `p`. -/
theorem slotP_eval {A : Word} {cfg : Config} {J : Bytes} {r : RSt} {s0 : PancakeState σ} (h : PBase A s0)
    {ws : Nat → Word} {os : List (Nat × Word)} {l : List (String × Value)} {u : PancakeState σ}
    (hu : Mid A cfg J r s0 ws os l u) {i : Nat} (hi : i < capacity) {p : String}
    (hl : l.lookup p = some (at_ A (slotAt i))) {x : Nat} (hx : x % 8 = 0) (hxs : x < slotSize) :
    eval u (slotPE p x) = some (u.memory (at_ A (slotAt i + x))) := by
  have hn := nums
  obtain ⟨s1, s2⟩ := slotAt_le hi
  obtain ⟨E, hE, hv⟩ := ScanRun.e_loadw (u := u) (A := at_ A (slotAt i)) (p := p) (n := slotSize)
    (at_aligned h.hA (slotAt_aligned i)) (fun y hy => by
      rw [at_at, hu.kept.memaddrs]; exact h.dom _ (by omega)) (vals_lookup hu.vals hl) hx hxs
  have e : some E = some (slotPE p x) := hE.symm.trans (slotP_lower p x)
  cases e; rw [hv, at_at]

/-- **How many commits the index holds**, into `rcm`, while it holds no more than it can. -/
theorem held_frag (o : Oracle σ) {A : Word} {cfg : Config} {J : Bytes} {r : RSt} {s0 : PancakeState σ}
    (h : PBase A s0) {ws : Nat → Word} {os : List (Nat × Word)} {l : List (String × Value)}
    (hws : ws rCommits = .ofNat 64 r.commits.length) (hcap : r.commits.length ≤ capacity) :
    Frag o (held "rcm") (Mid A cfg J r s0 ws os l)
      (Mid A cfg J r s0 ws os (("rcm", .ofNat 64 r.commits.length) :: without "rcm" l)) := by
  refine frag_append (xs := [_]) (mid_assign o h (y := "rcm") (by decide) (rw_lower (by decide))
    (val := .ofNat 64 r.commits.length) fun u hu => by rw [mid_rw h hu (by decide) (rw_lower (by decide)), hws]) ?_
  refine frag_if o (C := .cmp .less (.const (.ofNat 64 capacity)) (.var "rcm")) rfl
    (lowK_any _ (k := .skip) (c := _) rfl) (fun k => ⟨k, rfl⟩) rfl rfl mid_clock (b := false)
    (fun u hu => by
      rw [FramerCode.eval_lt (x := capacity) (y := r.commits.length) (by decide)
        (by have : capacity = 4096 := rfl; omega) rfl (ev_var (vals_lookup hu.vals (lookup_head _ _ _)))]
      rw [decide_eq_false (Nat.not_lt.2 hcap)]) (fun e => absurd e (by decide))
    fun _ => frag_nil o fun _ h => h

/-- A local's value, listed again on top. -/
theorem mid_again {A : Word} {cfg : Config} {J : Bytes} {r : RSt} {s0 : PancakeState σ} {ws : Nat → Word}
    {os : List (Nat × Word)} {l : List (String × Value)} {u : PancakeState σ} (hu : Mid A cfg J r s0 ws os l u)
    {y : String} {v : Value} (hy : l.lookup y = some v) : Mid A cfg J r s0 ws os ((y, v) :: without y l) u := by
  refine { hu with vals := fun q hq => ?_ }
  simp only [List.mem_cons, without, List.mem_filter, bne_iff_ne] at hq
  rcases hq with rfl | ⟨hq, _⟩
  · exact vals_lookup hu.vals hy
  · exact hu.vals q hq

/-- **`rm` raised** to the number `e` gives, if below it. -/
theorem mid_raise (o : Oracle σ) {A : Word} {cfg : Config} {J : Bytes} {r : RSt} {s0 : PancakeState σ}
    (h : PBase A s0) {ws : Nat → Word} {os : List (Nat × Word)} {l : List (String × Value)} {a b : Nat}
    (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) (hm : l.lookup "rm" = some (.ofNat 64 a)) {e : Syntax.PExpr}
    {E : PancakeExp} (he : Lower.lowerExp e = some E)
        (hv : ∀ u, Mid A cfg J r s0 ws os l u → eval u E = some (.ofNat 64 b)) :
    Frag o [RecoverProg.raise "rm" e] (Mid A cfg J r s0 ws os l)
      (Mid A cfg J r s0 ws os (("rm", .ofNat 64 (max a b)) :: without "rm" l)) := by
  refine frag_if o (C := .cmp .less (.op .xor (.var "rm") (.const (.ofNat 64 top)))
    (.op .xor E (.const (.ofNat 64 top)))) (by simp [ult, Lower.lowerExp, he, Syntax.eLt, Syntax.eXor, Syntax.v,
      Syntax.n]) (lowKK_one rfl (a := .assign "rm" E) (by simp [Lower.lowerStmt1, he])) (fun k => ⟨k, rfl⟩) rfl rfl
    mid_clock
    (b := decide (a < b)) (fun u hu => ult_eval ha hb (vals_lookup hu.vals hm) (hv u hu)) (fun hlt => ?_) fun hge => ?_
  · rw [Nat.max_eq_right (Nat.le_of_lt (of_decide_eq_true hlt))]
    exact mid_assign o h (y := "rm") (by decide) he hv
  · rw [Nat.max_eq_left (Nat.not_lt.1 (of_decide_eq_false hge))]
    exact frag_nil o fun u hu => mid_again hu hm

/-- The highest number of the first `j` commits and `m`. -/
def seqMax (m : Nat) (cs : List Commit) (j : Nat) : Nat := ((cs.take j).map (·.seq)).foldl max m

theorem seqMax_succ (m : Nat) (cs : List Commit) {j : Nat} (hj : j < cs.length) :
    seqMax m cs (j + 1) = max (seqMax m cs j) cs[j].seq := by
  simp only [seqMax, List.take_succ_eq_append_getElem hj, List.map_append, List.foldl_append, List.map_cons,
    List.map_nil, List.foldl_cons, List.foldl_nil]

theorem seqMax_lt {m : Nat} {cs : List Commit} (hm : m < 2 ^ 64) (hc : ∀ c ∈ cs, c.seq < 2 ^ 64) (j : Nat) :
    seqMax m cs j < 2 ^ 64 := by
  rw [seqMax, foldl_max_start]
  have := foldl_max_lt (B := 2 ^ 64) ((cs.take j).map (·.seq)) (fun x hx => by
    simp only [List.mem_map] at hx
    obtain ⟨c, hc', rfl⟩ := hx
    exact hc c (List.mem_of_mem_take hc')) (by decide)
  omega

theorem bw_nat (t : Bool) : bw t = .ofNat 64 (if t then 1 else 0) := by cases t <;> rfl

/-- Each local of `l'` with its value in `l`. -/
def Within (l : List (String × Value)) : List (String × Value) → Prop
  | [] => True
  | q :: rest => l.lookup q.1 = some q.2 ∧ Within l rest

theorem within_mem {l : List (String × Value)} : ∀ {l' : List (String × Value)}, Within l l' →
    ∀ q ∈ l', l.lookup q.1 = some q.2
  | [], _, _, hq => nomatch hq
  | _ :: _, ⟨h1, h2⟩, q, hq => by
    rcases List.mem_cons.1 hq with rfl | hq
    · exact h1
    · exact within_mem h2 q hq

/-- Locals listed anew, each as the list had it. -/
theorem mid_lookups {A : Word} {cfg : Config} {J : Bytes} {r : RSt} {s0 : PancakeState σ} {ws : Nat → Word}
    {os : List (Nat × Word)} {l l' : List (String × Value)} {u : PancakeState σ} (hu : Mid A cfg J r s0 ws os l u)
    (h : Within l l') : Mid A cfg J r s0 ws os l' u :=
  { hu with vals := fun q hq => vals_lookup hu.vals (within_mem h q hq) }

/-- A local's value added to those listed. -/
theorem mid_add {A : Word} {cfg : Config} {J : Bytes} {r : RSt} {s0 : PancakeState σ} {ws : Nat → Word}
    {os : List (Nat × Word)} {l : List (String × Value)} {u : PancakeState σ} (hu : Mid A cfg J r s0 ws os l u)
    {y : String} {v : Value} (hy : u.locals y = some v) : Mid A cfg J r s0 ws os ((y, v) :: l) u :=
  { hu with vals := fun q hq => (List.mem_cons.1 hq).elim (fun e => e ▸ hy) (hu.vals q) }

/-- The octets of slot `i`'s Message-ID, from `slotId` past the slot's address. -/
theorem slot_id {A : Word} {cfg : Config} {i : Nat} {c : Commit} {u : PancakeState σ} (hs : SlotR A cfg i c u) :
    ∀ m (hm : m < c.messageId.length), memLoadByte u.memory u.memaddrs u.be
      (at_ A (slotAt i) + BitVec.ofNat 64 slotId + BitVec.ofNat 64 m) = some c.messageId[m] := fun m hm => by
  rw [at_add, at_add]; exact hs.id m hm

/-- Slot `i`'s address into the local `y`. -/
theorem mid_slotAt (o : Oracle σ) {A : Word} {cfg : Config} {J : Bytes} {r : RSt} {s0 : PancakeState σ}
    (h : PBase A s0) {ws : Nat → Word} {os : List (Nat × Word)} {l : List (String × Value)} {x y : String}
    (hy : y ∈ stepLocals) {i : Nat} (hx : l.lookup x = some (.ofNat 64 i)) :
    Frag o [.assign y (Syntax.eAdd (Syntax.atOff rp rSlots) (Syntax.eMul (Syntax.v x) (Syntax.n slotSize)))]
      (Mid A cfg J r s0 ws os l) (Mid A cfg J r s0 ws os ((y, at_ A (slotAt i)) :: without y l)) :=
  mid_assign o h hy
    (E := .op .add (.op .add (.var "rsc") (.const (.ofNat 64 rSlots))) (.mul (.var x) (.const (.ofNat 64 slotSize))))
    rfl fun _ hu => index_eval (rsc_kept h hu.kept) (vals_lookup hu.vals hx) rSlots slotSize

/-- **A branch on a word known**: its arm when the word is not zero, the other when it is. -/
theorem frag_ifw (o : Oracle σ) {c : Syntax.PExpr} {C : PancakeExp} (hc : Lower.lowerExp c = some C)
    {t e : List Syntax.PStmt} (hlt : LowKK t) (hle : LowKK e) (hdt : declared t = []) (hde : declared e = [])
    {P Q : Assn σ} (hQ : Safe.ClockFree Q) {w : Word} (hv : ∀ u, P u → eval u C = some w)
    (ht : w ≠ 0 → Frag o t P Q) (he : w = 0 → Frag o e P Q) : Frag o [.ite c t e] P Q := by
  refine frag_ite o hc hQ (fun u hu => ⟨_, hv u hu⟩) ?_ (noDecl _ hdt) ?_ (noDecl _ hde)
  · by_cases hw : w = 0
    · exact frag_unsat hlt fun u ⟨hu, hne⟩ => hne (by rw [hv u hu, hw])
    · exact frag_conseq (ht hw) (fun u h => h.1) fun _ h => h
  · by_cases hw : w = 0
    · exact frag_conseq (he hw) (fun u h => h.1) fun _ h => h
    · exact frag_unsat hle fun u ⟨hu, h0⟩ => hw (Option.some.inj ((hv u hu).symm.trans h0))

theorem ok_nodup {c : Commit} (h : c.ok = true) : (c.groups.map Group.name).Nodup := by
  simp only [Commit.ok, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1.1.1.2

/-- **A phase from its start**: the area holding `r`, nothing listed yet but the step going on. -/
theorem from_start {o : Oracle σ} {prog : List Syntax.PStmt} {A : Word} {cfg : Config} {J : Bytes} {r : RSt}
    {s0 : PancakeState σ} (h : PIn A cfg J r s0) {Q : Assn σ}
    (k : Frag o prog (Mid A cfg J r s0 (scalars cfg r) [] [("rgo", 1)]) Q) : Frag o prog (Like s0) Q :=
  frag_conseq k (fun _ hu => mid_start h hu) fun _ h => h

/-- **A refusal's code given and the step stopped**, after its fields. -/
theorem refused_frag (o : Oracle σ) {A : Word} {cfg : Config} {J : Bytes} {r : RSt} {s0 : PancakeState σ}
    (h : PBase A s0) (f : Fault) {ws : Nat → Word} {os : List (Nat × Word)} {l : List (String × Value)}
    (hos : (os.map Prod.fst).all (fun y => decide (y ≠ rFault) && decide (y ≠ rStatus)) = true) :
    Frag o ([rset rFault (Syntax.n (faultCode f))] ++ stop refused) (Mid A cfg J r s0 ws os l)
      (Mid A cfg J r s0 ws ((rStatus, .ofNat 64 refused) :: (rFault, .ofNat 64 (faultCode f)) :: os)
        (("rgo", 0) :: without "rgo" l)) := by
  have h1 : ∀ q ∈ os, q.1 ≠ rFault ∧ q.1 ≠ rStatus := fun q hq => by
    have := List.all_eq_true.1 hos q.1 (List.mem_map_of_mem hq)
    simp only [Bool.and_eq_true, decide_eq_true_eq] at this
    exact this
  refine frag_append (xs := [_]) (mid_out o h (x := rFault) (by decide) (fun q hq => (h1 q hq).1)
    (E := .const (.ofNat 64 (faultCode f))) rfl fun _ _ => rfl) ?_
  exact stop_frag o h refused fun q hq => by
    rcases List.mem_cons.1 hq with rfl | hq
    · show rFault ≠ rStatus; decide
    · exact (h1 q hq).2

/-! ## Fields of a word -/

theorem testBit_hi {x k i : Nat} (hx : x < 2 ^ k) (hi : k ≤ i) : x.testBit i = false :=
  Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hx (Nat.pow_le_pow_right (by decide) hi))

theorem testBit_mask {k i : Nat} : (2 ^ k - 1).testBit i = decide (i < k) := Nat.testBit_two_pow_sub_one k i

/-- The low half of a word of two halves. -/
theorem sizes_low {h f : Nat} (hf : f < 2 ^ 32) :
    ((BitVec.ofNat 64 h <<< 32) ||| BitVec.ofNat 64 f) &&& BitVec.ofNat 64 (2 ^ 32 - 1) = BitVec.ofNat 64 f := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ofNat, testBit_mask]
  by_cases h32 : i < 32
  · simp [h32, hi]
  · simp [testBit_hi hf (Nat.le_of_not_lt h32), h32]

/-- The high half of a word of two halves. -/
theorem group_ix {a b : Nat} (ha : a < 2 ^ 32) (hb : b < 2 ^ 32) :
    ((BitVec.ofNat 64 a <<< 32) ||| BitVec.ofNat 64 b) >>> 32 = BitVec.ofNat 64 a := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_ushiftRight, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ofNat]
  have hb' := testBit_hi hb (Nat.le_add_right 32 i)
  by_cases h32 : i < 32
  · simp [hb', hi, show 32 + i < 64 by omega]
  · simp [hb', hi, show ¬(32 + i < 64) by omega, testBit_hi ha (Nat.le_of_not_lt h32)]

/-- Bits 8 to 15 of a slot's third word: a Message-ID's length. -/
theorem misc_len {crc len g : Nat} (hl : len < 256) (hg : g < 256) :
    (((BitVec.ofNat 64 crc <<< 16) ||| (BitVec.ofNat 64 len <<< 8)) ||| BitVec.ofNat 64 g) >>> 8 &&&
      BitVec.ofNat 64 255 = BitVec.ofNat 64 len := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft,
    BitVec.getLsbD_ofNat, show (255 : Nat) = 2 ^ 8 - 1 from rfl, testBit_mask]
  have hg' := testBit_hi (k := 8) hg (Nat.le_add_right 8 i)
  by_cases h8 : i < 8
  · simp [h8, hg', hi, show 8 + i < 16 by omega, show 8 + i < 64 by omega]
  · simp [h8, testBit_hi (k := 8) hl (Nat.le_of_not_lt h8)]

/-- The low byte of a slot's third word: a commit's count of groups. -/
theorem misc_count {crc len g : Nat} (hg : g < 256) :
    (((BitVec.ofNat 64 crc <<< 16) ||| (BitVec.ofNat 64 len <<< 8)) ||| BitVec.ofNat 64 g) &&&
      BitVec.ofNat 64 255 = BitVec.ofNat 64 g := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ofNat,
    show (255 : Nat) = 2 ^ 8 - 1 from rfl, testBit_mask]
  by_cases h8 : i < 8
  · simp [h8, hi, show i < 16 by omega]
  · simp [h8, testBit_hi (k := 8) hg (Nat.le_of_not_lt h8)]

/-! ## Search loops -/

/-- **A search loop**: `R k (firstIdx p k)` carried through the body while nothing is found below `n`. -/
theorem firstIdx_frag (o : Oracle σ) {c : Syntax.PExpr} {C : PancakeExp} (hc : Lower.lowerExp c = some C)
    {body : List Syntax.PStmt} (hlow : LowKK body) (hd : declared body = [])
    {p : Nat → Bool} {n : Nat} {R : Nat → Option Nat → Assn σ} (hR : ∀ k f, Safe.ClockFree (R k f))
    (hg : ∀ k u, k ≤ n → R k (firstIdx p k) u → eval u C = some (bw ((firstIdx p k).isNone && decide (k < n))))
    (hbody : ∀ k, firstIdx p k = none → k < n → Frag o body (R k none) (R (k + 1) (if p k then some k else none)))
    (hfound : ∀ k i u, R k (some i) u → R n (some i) u) :
    Frag o [.while c body] (R 0 none) (R n (firstIdx p n)) := by
  let I (k : Nat) : Assn σ := fun u => R k (firstIdx p k) u ∧ k ≤ n
  refine frag_conseq (frag_count o hc hlow (I := I) (fun k s t h => ⟨hR _ _ s t h.1, h.2⟩)
    (fun k => noDecl (P' := I k) _ hd) (g := fun k => (firstIdx p k).isNone && decide (k < n))
    (fun k u h => hg k u h.2 h.1) (fun k hk => ?_) 0) (fun u h => ⟨h, Nat.zero_le _⟩) ?_
  · simp only [Bool.and_eq_true, Option.isNone_iff_eq_none, decide_eq_true_eq] at hk
    obtain ⟨hf, hkn⟩ := hk
    have hf1 : firstIdx p (k + 1) = if p k then some k else none := by
      rw [firstIdx_succ, hf]; rfl
    exact frag_conseq (hbody k hf hkn) (fun u h => by have h1 := h.1; rw [hf] at h1; exact h1)
      fun u h => ⟨by rw [hf1]; exact h, hkn⟩
  · rintro u ⟨k, ⟨hu, hkn⟩, hgk⟩
    cases e : firstIdx p k with
    | none =>
      have : k = n := by simp only [e, Option.isNone_none, Bool.true_and, decide_eq_false_iff_not] at hgk; omega
      subst this; exact hu
    | some i =>
      rw [firstIdx_mono e n hkn]; rw [e] at hu; exact hfound k i u hu

/-- **The test of a search loop**, `d = 0 && i < c`. Flag `d` is `e` once search `f` found its index, which `i` then
holds, below the count `k` so far. -/
theorem search_guard {u : PancakeState σ} {d i c : String} {f : Option Nat} {k n e : Nat} (he : 0 < e)
    (he64 : e < 2 ^ 64) (hfk : ∀ j, f = some j → j < k) (hkn : k ≤ n) (hn : n < 2 ^ 63)
    (hi : u.locals i = some (.ofNat 64 (f.getD k)))
    (hd : u.locals d = some (.ofNat 64 (if f.isSome then e else 0)))
    (hc : u.locals c = some (.ofNat 64 n)) :
    eval u (.op .and_ (.cmp .equal (.var d) (.const 0)) (.cmp .less (.var i) (.var c))) =
      some (bw (f.isNone && decide (k < n))) := by
  cases f with
  | none =>
    rw [FramerCode.eval_and (FramerCode.eval_eq (x := 0) (y := 0) (by decide) (by decide) (ev_var hd) rfl)
      (FramerCode.eval_lt (x := k) (y := n) (by omega) (by omega) (ev_var hi) (ev_var hc))]
    rfl
  | some j =>
    have := hfk j rfl
    rw [FramerCode.eval_and (FramerCode.eval_eq (x := e) (y := 0) he64 (by decide) (ev_var hd) rfl)
      (FramerCode.eval_lt (x := j) (y := n) (by omega) (by omega) (ev_var hi) (ev_var hc))]
    rw [decide_eq_false (by omega)]; rfl

/-- **The test of a flag loop**, `d = 0 && i < c`: the flag `d` is `e` once `t` is set. -/
theorem flag_guard {u : PancakeState σ} {d i c : String} {t : Bool} {j n e : Nat} (he : 0 < e) (he64 : e < 2 ^ 64)
    (hj : j < 2 ^ 63) (hn : n < 2 ^ 63) (hd : u.locals d = some (.ofNat 64 (if t then e else 0)))
    (hi : u.locals i = some (.ofNat 64 j)) (hc : u.locals c = some (.ofNat 64 n)) :
    eval u (.op .and_ (.cmp .equal (.var d) (.const 0)) (.cmp .less (.var i) (.var c))) =
      some (bw (!t && decide (j < n))) := by
  rw [FramerCode.eval_and (FramerCode.eval_eq (x := if t then e else 0) (y := 0) (by split <;> omega) (by decide)
    (ev_var hd) rfl) (FramerCode.eval_lt hj hn (ev_var hi) (ev_var hc))]
  cases t
  · rfl
  · rw [if_pos rfl, decide_eq_false (by omega)]; rfl

end DN.News.RecoverArea
