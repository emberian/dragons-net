-- SPDX-License-Identifier: AGPL-3.0-or-later
import DN.News.WordsRun
import DN.Server.SessionText

/-!
# DN.Server.SessionWords

The session's scan of a line's words, `scanWords`: `w` their count and the first places as `WordsRun.spans` gives
them (`scanWords_frag`); a word compared with a text in any case, `wordIsAt` (`wordIsAt_frag`); CAPABILITIES's
keyword check, `CommandSpec.isKeyword` (`keyword_frag`). Each a fragment of the function holding it: if it goes on,
its locals hold these; a run that does not end is not excluded.
-/

namespace DN.Server.SessionWords

open DN.Compiler DN.Compiler.Wp DN.Compiler.WpRet DN.Compiler.Bytes DN.Compiler.Preservation DN.Compiler.Frag DN.Server
  DN.News DN.News.WordsRun DN.News.FrameSpec DN.Server.SessionText
open DN.Server.SessionLayout (framerHead texts textAt ownOff ownTexts ownRet ownVSel ownVs ownVl ownLo ownHi ownFs
  ownFl ownNamed ownWs ownWl ownStore conns tableOff connSlot cFramer)
open DN.News.FramerCode (bw)
open DN.Server.SessionCheck (zeroState)

variable {σ : Type}

/-- The statements setting the `j`-th word's place and on, the name `sel` picks of each in `nm`, to `e` when the
word is the `w`-th. -/
def ifsFrom (sel : String × String → String) (e : Syntax.PExpr) : List (String × String) → Nat → List Syntax.PStmt
  | [], _ => []
  | p :: rest, j =>
    .ite (Syntax.eEq (Syntax.v "w") (Syntax.n (j + 1))) [.assign (sel p) e] [] :: ifsFrom sel e rest (j + 1)

/-- The names of the words' starts and lengths, from the `j`-th. -/
def scanNmFrom (j m : Nat) : List (String × String) := (List.range' j m).map fun j => (s!"s{j}", s!"l{j}")

theorem starts_eq : ∀ (j m : Nat), (List.range' j m).map (fun j => Syntax.PStmt.ite
    (Syntax.eEq (Syntax.v "w") (Syntax.n (j + 1))) [.assign s!"s{j}" (Syntax.v "q")] []) =
    ifsFrom Prod.fst (Syntax.v "q") (scanNmFrom j m) j
  | _, 0 => rfl
  | j, m + 1 => by
    simp only [List.range'_succ, List.map_cons, scanNmFrom] at *
    rw [ifsFrom, ← scanNmFrom, ← starts_eq (j + 1) m]

theorem ends_eq (pos : Syntax.PExpr) : ∀ (j m : Nat), (List.range' j m).map (fun j => Syntax.PStmt.ite
    (Syntax.eEq (Syntax.v "w") (Syntax.n (j + 1))) [.assign s!"l{j}" (Syntax.eSub pos (Syntax.v "ws"))] []) =
    ifsFrom Prod.snd (Syntax.eSub pos (Syntax.v "ws")) (scanNmFrom j m) j
  | _, 0 => rfl
  | j, m + 1 => by
    simp only [List.range'_succ, List.map_cons, scanNmFrom] at *
    rw [ifsFrom, ← scanNmFrom, ← ends_eq pos (j + 1) m]

/-- A word set when `w` is `j + 1`: the locals after it, from `s`. -/
def ifSet (s : PancakeState σ) (W j : Nat) (x : String) (v : Value) : PancakeState σ :=
  if W = j + 1 then { s with locals := setLocal s.locals x v } else s

theorem eqE_eval {s : PancakeState σ} {W j : Nat} (hW : W < 2 ^ 64) (hj : j + 1 < 2 ^ 64)
    (h : s.locals "w" = some (BitVec.ofNat 64 W)) :
    eval s (.cmp .equal (.var "w") (.const (BitVec.ofNat 64 (j + 1)))) = some (if W = j + 1 then 1 else 0) := by
  simp only [eval, h]
  by_cases e : W = j + 1
  · subst e; simp
  · have : BitVec.ofNat 64 W ≠ BitVec.ofNat 64 (j + 1) := fun h' => e (NatToDec.ofNat64_inj hW hj h')
    simp [e, this]

/-- **One word's place set** when it is the `w`-th. -/
theorem ifw_frag (o : Oracle σ) {s1 : PancakeState σ} {W j : Nat} (hW : W < 2 ^ 64) (hj : j + 1 < 2 ^ 64)
    (hw : s1.locals "w" = some (BitVec.ofNat 64 W)) {x : String} {e : Syntax.PExpr} {E : PancakeExp}
    (he : Lower.lowerExp e = some E) {v : Value} (hv : eval s1 E = some v) (hx : ∃ old, s1.locals x = some old) :
    Frag o [.ite (Syntax.eEq (Syntax.v "w") (Syntax.n (j + 1))) [.assign x e] []] (Like s1)
      (Like (ifSet s1 W j x v)) := by
  refine frag_oneR (a := .cond (.cmp .equal (.var "w") (.const (BitVec.ofNat 64 (j + 1)))) (.assign x E) .skip)
    (by simp [Lower.lowerStmt1, Lower.lowerStmtsFold, Syntax.eEq, Syntax.v, Syntax.n, Lower.lowerExp, he]) rfl
    (like_clock _) fun R => ?_
  have hc : ∀ u, Like s1 u → eval u (.cmp .equal (.var "w") (.const (BitVec.ofNat 64 (j + 1)))) =
      some (if W = j + 1 then 1 else 0) := fun u h => by rw [like_eval h]; exact eqE_eval hW hj hw
  by_cases e : W = j + 1
  · refine WpRet.cond (fun u h => ⟨_, hc u h⟩) (WpRet.assign fun u ⟨h, _⟩ => ?_)
      (fun u ⟨h, he'⟩ => absurd he' (by rw [hc u h]; simp [e]))
    obtain ⟨old, hold⟩ := hx
    exact ⟨v, old, by rw [like_eval h]; exact hv, by rw [h.locals]; exact hold, by
      simp only [ifSet, if_pos e]
      exact ⟨by rw [h.locals], h.memory, h.memaddrs, h.be, h.ffi, h.base, h.code⟩⟩
  · simp only [ifSet, if_neg e]
    exact WpRet.cond (fun u h => ⟨_, hc u h⟩) (fun u ⟨h, hne⟩ => absurd (hc u h) (by simp [e]; exact hne))
      (conseq (WpRet.skip o _ R) (fun s h => h.1) (fun _ _ h => h) (fun _ h => h))

/-- The state after the setters from the `j`-th: the `w`-th word's name set, if among them. -/
def ifsRes (s : PancakeState σ) (sel : String × String → String) (nm : List (String × String)) (j W : Nat)
    (v : Value) : PancakeState σ :=
  if h : j < W ∧ W ≤ j + nm.length then
    { s with locals := setLocal s.locals (sel (nm[W - 1 - j]'(by omega))) v }
  else s

/-- **The setters**: the `w`-th word's name, if among them, set to `e`'s value. -/
theorem ifs_frag (o : Oracle σ) (sel : String × String → String) {e : Syntax.PExpr} {E : PancakeExp}
    (he : Lower.lowerExp e = some E) : ∀ (nm : List (String × String)) (j : Nat) (s1 : PancakeState σ) (W : Nat)
    (v : Value), W < 2 ^ 64 → j + nm.length < 2 ^ 64 → s1.locals "w" = some (BitVec.ofNat 64 W) →
    eval s1 E = some v → (∀ p ∈ nm, sel p ≠ "w") → (∀ p ∈ nm, ExpAvoids (· = sel p) E) →
    (∀ p ∈ nm, ∃ old, s1.locals (sel p) = some old) →
    Frag o (ifsFrom sel e nm j) (Like s1) (Like (ifsRes s1 sel nm j W v))
  | [], j, s1, W, v, _, _, _, _, _, _, _ => by
    have : ifsRes s1 sel [] j W v = s1 := by simp only [ifsRes]; rw [dif_neg (by simp only [List.length_nil]; omega)]
    rw [this]
    exact fun k R Q _ hk => ⟨k, rfl, hk⟩
  | p :: rest, j, s1, W, v, hW, hj, hw, hv, hsw, hav, hb => by
    have h1 := ifw_frag o (j := j) hW (by simp at hj; omega) hw he hv (hb p (by simp))
    let s2 := ifSet s1 W j (sel p) v
    have hw2 : s2.locals "w" = some (BitVec.ofNat 64 W) := by
      simp only [s2, ifSet]; split
      · simp [setLocal, Ne.symm (hsw p (by simp)), hw]
      · exact hw
    have hv2 : eval s2 E = some v := by
      simp only [s2, ifSet]; split
      · exact eval_set_avoid (hav p (by simp)) hv
      · exact hv
    have hb2 : ∀ q ∈ rest, ∃ old, s2.locals (sel q) = some old := fun q hq => by
      simp only [s2, ifSet]; split
      · by_cases e : sel q = sel p
        · exact ⟨v, by simp [setLocal, e]⟩
        · simpa [setLocal, e] using hb q (by simp [hq])
      · exact hb q (by simp [hq])
    have h2 := ifs_frag o sel he rest (j + 1) s2 W v hW (by simp at hj; omega) hw2 hv2
      (fun q hq => hsw q (by simp [hq])) (fun q hq => hav q (by simp [hq])) hb2
    have e2 : ifsRes s2 sel rest (j + 1) W v = ifsRes s1 sel (p :: rest) j W v := by
      simp only [s2, ifSet, ifsRes]
      by_cases e : W = j + 1
      · subst e
        rw [if_pos rfl, dif_neg (by omega), dif_pos (by simp)]
        simp
      · rw [if_neg e]
        by_cases r : j + 1 < W ∧ W ≤ j + 1 + rest.length
        · rw [dif_pos r, dif_pos (by simp; omega)]
          congr 3
          simp only [show W - 1 - j = W - 1 - (j + 1) + 1 by omega, List.getElem_cons_succ]
        · rw [dif_neg r, dif_neg (by simp; omega)]
    rw [← e2]
    exact frag_append (xs := [_]) h1 h2

/-! ### The words of the line -/

/-- What a scan keeps for word `j`: an ended word's start and length, the start of the one not ended. -/
def slot (st : List (Nat × Nat) × Option Nat) (j : Nat) : Nat × Nat :=
  if h : j < st.1.length then st.1[j] else if j = st.1.length then (st.2.getD 0, 0) else (0, 0)

/-- How many words a scan has met. -/
def count (st : List (Nat × Nat) × Option Nat) : Nat := st.1.length + if st.2.isSome then 1 else 0

/-- The locals a scan writes. -/
def scanNames (nm : List (String × String)) : List String :=
  ["w", "inw", "ws", "q", "cq"] ++ nm.flatMap fun p => [p.1, p.2]

/-- The line's octets in the framer's block at `B`, their number in `kept`. -/
structure LineIn (B : Word) (L : List Byte) (s : PancakeState σ) : Prop where
  blk : s.locals "blk" = some B
  kept : s.locals "kept" = some (BitVec.ofNat 64 L.length)
  bytes : ∀ j (h : j < L.length),
    memLoadByte s.memory s.memaddrs s.be (B + BitVec.ofNat 64 40 + BitVec.ofNat 64 j) = some L[j]
  short : L.length < 2 ^ 62

/-- The scan after `q` octets, from the state `s0` before it. -/
structure ScanAt (L : List Byte) (nm : List (String × String)) (s0 : PancakeState σ) (q ql : Nat)
    (s : PancakeState σ) : Prop where
  frame : ∀ y, y ∉ scanNames nm → s.locals y = s0.locals y
  memory : s.memory = s0.memory
  memaddrs : s.memaddrs = s0.memaddrs
  be : s.be = s0.be
  ffi : s.ffi = s0.ffi
  base : s.baseAddr = s0.baseAddr
  code : s.code = s0.code
  hq : s.locals "q" = some (BitVec.ofNat 64 ql)
  hw : s.locals "w" = some (BitVec.ofNat 64 (count (scanTo L q)))
  hinw : s.locals "inw" = some (if (scanTo L q).2.isSome then 1 else 0)
  hws : ∃ v, s.locals "ws" = some v ∧ ∀ st, (scanTo L q).2 = some st → v = BitVec.ofNat 64 st
  slots : ∀ j (h : j < nm.length), s.locals nm[j].1 = some (BitVec.ofNat 64 (slot (scanTo L q) j).1) ∧
    s.locals nm[j].2 = some (BitVec.ofNat 64 (slot (scanTo L q) j).2)

theorem scanAt_clock {L : List Byte} {nm : List (String × String)} {s0 : PancakeState σ} {q ql : Nat} :
    Safe.ClockFree (ScanAt L nm s0 q ql) := fun _ _ h => { h with }

/-- The names a scan writes are distinct. -/
structure NmOk (nm : List (String × String)) : Prop where
  own : ∀ p ∈ nm, p.1 ∉ ["w", "inw", "ws", "q", "cq"] ∧ p.2 ∉ ["w", "inw", "ws", "q", "cq"] ∧ p.1 ≠ p.2
  apart : nm.Pairwise fun a b => a.1 ≠ b.1 ∧ a.1 ≠ b.2 ∧ a.2 ≠ b.1 ∧ a.2 ≠ b.2
  short : nm.length < 2 ^ 62

theorem NmOk.inw_snd {nm : List (String × String)} (h : NmOk nm) : ∀ p ∈ nm, "inw" ≠ p.2 := fun p hp e =>
  (h.own p hp).2.1 (by rw [← e]; simp)

theorem NmOk.own2 {nm : List (String × String)} (h : NmOk nm) :
    ∀ p ∈ nm, p.1 ∉ ["w", "inw", "ws", "q", "cq"] ∧ p.2 ∉ ["w", "inw", "ws", "q", "cq"] := fun p hp =>
  ⟨(h.own p hp).1, (h.own p hp).2.1⟩

theorem nm_fst_mem {nm : List (String × String)} {j : Nat} (h : j < nm.length) : nm[j].1 ∈ scanNames nm := by
  simp only [scanNames, List.mem_append, List.mem_flatMap]
  exact Or.inr ⟨nm[j], List.getElem_mem h, by simp⟩

theorem nm_snd_mem {nm : List (String × String)} {j : Nat} (h : j < nm.length) : nm[j].2 ∈ scanNames nm := by
  simp only [scanNames, List.mem_append, List.mem_flatMap]
  exact Or.inr ⟨nm[j], List.getElem_mem h, by simp⟩

theorem nm_own {nm : List (String × String)} (h : NmOk nm) {j : Nat} (hj : j < nm.length) :
    nm[j].1 ∉ ["w", "inw", "ws", "q", "cq"] ∧ nm[j].2 ∉ ["w", "inw", "ws", "q", "cq"] ∧ nm[j].1 ≠ nm[j].2 :=
  h.own _ (List.getElem_mem hj)

theorem nm_apart {nm : List (String × String)} (h : NmOk nm) {i j : Nat} (hi : i < nm.length) (hj : j < nm.length)
    (hij : i ≠ j) : nm[i].1 ≠ nm[j].1 ∧ nm[i].1 ≠ nm[j].2 ∧ nm[i].2 ≠ nm[j].1 ∧ nm[i].2 ≠ nm[j].2 := by
  have hp := List.pairwise_iff_getElem.mp h.apart
  rcases Nat.lt_or_gt_of_ne hij with hlt | hgt
  · exact hp i j hi hj hlt
  · obtain ⟨a, b, c, d⟩ := hp j i hj hi hgt
    exact ⟨Ne.symm a, Ne.symm c, Ne.symm b, Ne.symm d⟩

theorem scanAt_like {L : List Byte} {nm : List (String × String)} {s0 t u : PancakeState σ} {q ql : Nat}
    (h : ScanAt L nm s0 q ql t) (hl : Like t u) : ScanAt L nm s0 q ql u where
  frame y hy := by rw [hl.locals]; exact h.frame y hy
  memory := hl.memory.trans h.memory
  memaddrs := hl.memaddrs.trans h.memaddrs
  be := hl.be.trans h.be
  ffi := hl.ffi.trans h.ffi
  base := hl.base.trans h.base
  code := hl.code.trans h.code
  hq := by rw [hl.locals]; exact h.hq
  hw := by rw [hl.locals]; exact h.hw
  hinw := by rw [hl.locals]; exact h.hinw
  hws := by rw [hl.locals]; exact h.hws
  slots j hj := by rw [hl.locals]; exact h.slots j hj

/-- A local the scan does not track set: the scan as it was. -/
theorem scanAt_set {L : List Byte} {nm : List (String × String)} {s0 s : PancakeState σ} {q ql : Nat}
    (h : ScanAt L nm s0 q ql s) {x : String} (hx : x ∈ scanNames nm) (hq : x ≠ "q") (hw : x ≠ "w")
    (hi : x ≠ "inw") (hs : x ≠ "ws") (hn : ∀ j (hj : j < nm.length), x ≠ nm[j].1 ∧ x ≠ nm[j].2) (v : Value) :
    ScanAt L nm s0 q ql { s with locals := setLocal s.locals x v } where
  frame y hy := by
    have : y ≠ x := fun e => hy (e ▸ hx)
    simp only [setLocal, if_neg this]; exact h.frame y hy
  memory := h.memory
  memaddrs := h.memaddrs
  be := h.be
  ffi := h.ffi
  base := h.base
  code := h.code
  hq := by simp only [setLocal, if_neg (Ne.symm hq)]; exact h.hq
  hw := by simp only [setLocal, if_neg (Ne.symm hw)]; exact h.hw
  hinw := by simp only [setLocal, if_neg (Ne.symm hi)]; exact h.hinw
  hws := by simp only [setLocal, if_neg (Ne.symm hs)]; exact h.hws
  slots j hj := by
    simp only [setLocal, if_neg (Ne.symm (hn j hj).1), if_neg (Ne.symm (hn j hj).2)]
    exact h.slots j hj

theorem cq_apart {nm : List (String × String)} (hnm : NmOk nm) (j : Nat) (hj : j < nm.length) :
    "cq" ≠ nm[j].1 ∧ "cq" ≠ nm[j].2 := by
  obtain ⟨h1, h2, -⟩ := nm_own hnm hj
  exact ⟨fun e => h1 (by rw [← e]; simp), fun e => h2 (by rw [← e]; simp)⟩

theorem q_apart {nm : List (String × String)} (hnm : NmOk nm) (j : Nat) (hj : j < nm.length) :
    "q" ≠ nm[j].1 ∧ "q" ≠ nm[j].2 := by
  obtain ⟨h1, h2, -⟩ := nm_own hnm hj
  exact ⟨fun e => h1 (by rw [← e]; simp), fun e => h2 (by rw [← e]; simp)⟩

theorem scanAt_restore {L : List Byte} {nm : List (String × String)} (hnm : NmOk nm) {s0 s : PancakeState σ}
    {q ql : Nat} (h : ScanAt L nm s0 q ql s) (v : Option Value) : ScanAt L nm s0 q ql (restore s "cq" v) where
  frame y hy := by
    simp only [restore, resVar]
    rw [if_neg (fun (e : y = "cq") => hy (e ▸ (by simp [scanNames] : "cq" ∈ scanNames nm)))]; exact h.frame y hy
  memory := h.memory
  memaddrs := h.memaddrs
  be := h.be
  ffi := h.ffi
  base := h.base
  code := h.code
  hq := by simp only [restore, resVar]; rw [if_neg (by decide)]; exact h.hq
  hw := by simp only [restore, resVar]; rw [if_neg (by decide)]; exact h.hw
  hinw := by simp only [restore, resVar]; rw [if_neg (by decide)]; exact h.hinw
  hws := by simp only [restore, resVar]; rw [if_neg (by decide)]; exact h.hws
  slots j hj := by
    simp only [restore, resVar]
    rw [if_neg (Ne.symm (cq_apart hnm j hj).1), if_neg (Ne.symm (cq_apart hnm j hj).2)]; exact h.slots j hj

/-- The position moved on. -/
theorem scanAt_inc {L : List Byte} {nm : List (String × String)} (hnm : NmOk nm) {s0 s : PancakeState σ}
    {q ql : Nat} (h : ScanAt L nm s0 q ql s) :
    ScanAt L nm s0 q (ql + 1) { s with locals := setLocal s.locals "q" (BitVec.ofNat 64 (ql + 1)) } where
  frame y hy := by
    simp only [setLocal, if_neg (fun e : y = "q" => hy (e ▸ (by simp [scanNames] : "q" ∈ scanNames nm)))]
    exact h.frame y hy
  memory := h.memory
  memaddrs := h.memaddrs
  be := h.be
  ffi := h.ffi
  base := h.base
  code := h.code
  hq := by simp [setLocal]
  hw := by simp only [setLocal, if_neg (by decide : ("w" : String) ≠ "q")]; exact h.hw
  hinw := by simp only [setLocal, if_neg (by decide : ("inw" : String) ≠ "q")]; exact h.hinw
  hws := by simp only [setLocal, if_neg (by decide : ("ws" : String) ≠ "q")]; exact h.hws
  slots j hj := by
    simp only [setLocal, if_neg (Ne.symm (q_apart hnm j hj).1), if_neg (Ne.symm (q_apart hnm j hj).2)]
    exact h.slots j hj

theorem scanAt_of_eq {L : List Byte} {nm : List (String × String)} {s0 s : PancakeState σ} {q q' ql : Nat}
    (h : ScanAt L nm s0 q ql s) (e : scanTo L q' = scanTo L q) : ScanAt L nm s0 q' ql s where
  frame := h.frame
  memory := h.memory
  memaddrs := h.memaddrs
  be := h.be
  ffi := h.ffi
  base := h.base
  code := h.code
  hq := h.hq
  hw := by rw [e]; exact h.hw
  hinw := by rw [e]; exact h.hinw
  hws := by rw [e]; exact h.hws
  slots := by rw [e]; exact h.slots

theorem ifsRes_locals (s : PancakeState σ) (sel : String × String → String) (nm : List (String × String)) (W : Nat)
    (v : Value) (y : String) : (ifsRes s sel nm 0 W v).locals y =
      if h : 0 < W ∧ W ≤ nm.length then (if y = sel (nm[W - 1]'(by omega)) then some v else s.locals y)
      else s.locals y := by
  simp only [ifsRes, Nat.zero_add, Nat.sub_zero]
  split <;> rfl

theorem slot_lt {cl : List (Nat × Nat)} {c : Option Nat} {j : Nat} (h : j < cl.length) : slot (cl, c) j = cl[j] := by
  simp [slot, h]

theorem slot_eq {cl : List (Nat × Nat)} {c : Option Nat} : slot (cl, c) cl.length = (c.getD 0, 0) := by
  simp [slot]

theorem slot_gt {cl : List (Nat × Nat)} {c : Option Nat} {j : Nat} (h : cl.length < j) : slot (cl, c) j = (0, 0) := by
  simp only [slot]
  rw [dif_neg (by omega), if_neg (by omega)]

theorem ifsRes_fields (s : PancakeState σ) (sel : String × String → String) (nm : List (String × String))
    (j W : Nat) (v : Value) :
      (ifsRes s sel nm j W v).memory = s.memory ∧ (ifsRes s sel nm j W v).memaddrs = s.memaddrs ∧
      (ifsRes s sel nm j W v).be = s.be ∧ (ifsRes s sel nm j W v).ffi = s.ffi ∧
      (ifsRes s sel nm j W v).baseAddr = s.baseAddr ∧ (ifsRes s sel nm j W v).code = s.code := by
  unfold ifsRes; split <;> exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- **A word started** at `q`: `w` one on, `ws` and `inw` set, the word's start in its name. -/
theorem scanAt_start {L : List Byte} {nm : List (String × String)} (hnm : NmOk nm) {s0 s : PancakeState σ} {q : Nat}
    (h : ScanAt L nm s0 q q s) (hc : (scanTo L q).2 = none) (hb : CommandSpec.isWS (L.getD q 0) = false) :
    ScanAt L nm s0 (q + 1) q (ifsRes (setL (setL (setL s "w" (BitVec.ofNat 64 ((scanTo L q).1.length + 1))) "ws"
      (BitVec.ofNat 64 q)) "inw" 1) Prod.fst nm 0 ((scanTo L q).1.length + 1) (BitVec.ofNat 64 q)) := by
  have e : scanTo L (q + 1) = ((scanTo L q).1, some q) := by
    simp only [scanTo, hb, Bool.false_eq_true, if_false, hc, Option.getD_none]
  generalize hst : scanTo L q = st at h hc e
  obtain ⟨cl, c⟩ := st
  simp only at hc e ⊢
  subst hc
  have hw := h.hw
  simp only [count] at hw
  have own := fun j hj => nm_own hnm (j := j) hj
  obtain ⟨f1, f2, f3, f4, f5, f6⟩ := ifsRes_fields (setL (setL (setL s "w" (BitVec.ofNat 64 (cl.length + 1))) "ws"
    (BitVec.ofNat 64 q)) "inw" 1) Prod.fst nm 0 (cl.length + 1) (BitVec.ofNat 64 q)
  -- a local outside the setter's name, the three set or not
  have hloc : ∀ y, (∀ (hW : cl.length < nm.length), y ≠ nm[cl.length].1) →
      (ifsRes (setL (setL (setL s "w" (BitVec.ofNat 64 (cl.length + 1))) "ws" (BitVec.ofNat 64 q)) "inw" 1) Prod.fst
        nm 0 (cl.length + 1) (BitVec.ofNat 64 q)).locals y =
      setLocal (setLocal (setLocal s.locals "w" (BitVec.ofNat 64 (cl.length + 1))) "ws" (BitVec.ofNat 64 q)) "inw" 1
          y := by
    intro y hy
    rw [ifsRes_locals]
    split
    · rename_i hW
      simp only [Nat.add_sub_cancel]
      rw [if_neg (hy (by omega))]; rfl
    · rfl
  refine ⟨fun y hy => ?_, f1.trans h.memory, f2.trans h.memaddrs, f3.trans h.be, f4.trans h.ffi, f5.trans h.base,
    f6.trans h.code, ?_, ?_, ?_, ?_, fun j hj => ?_⟩
  · rw [hloc y fun hW e => hy (e ▸ nm_fst_mem hW)]
    have h1 : y ≠ "w" := fun e => hy (by simp [scanNames, e])
    have h2 : y ≠ "ws" := fun e => hy (by simp [scanNames, e])
    have h3 : y ≠ "inw" := fun e => hy (by simp [scanNames, e])
    simp only [setLocal, if_neg h1, if_neg h2, if_neg h3]
    exact h.frame y hy
  · rw [hloc "q" fun hW e => (q_apart hnm _ hW).1 e]
    simp only [setLocal, if_neg (by decide : ("q" : String) ≠ "w"), if_neg (by decide : ("q" : String) ≠ "ws"),
      if_neg (by decide : ("q" : String) ≠ "inw")]
    exact h.hq
  · rw [hloc "w" fun hW e => (own _ hW).1 (by rw [← e]; simp)]
    simp [setLocal, count, e]
  · rw [hloc "inw" fun hW e => (own _ hW).1 (by rw [← e]; simp)]
    simp [setLocal, e]
  · rw [hloc "ws" fun hW e => (own _ hW).1 (by rw [← e]; simp)]
    exact ⟨BitVec.ofNat 64 q, by simp [setLocal], fun st hs => by rw [e] at hs; cases hs; rfl⟩
  · rw [e]
    have hj' := h.slots j hj
    rw [hst] at hj'
    obtain ⟨o1, o2, o12⟩ := own j hj
    have n1 : ∀ y ∈ ["w", "inw", "ws", "q", "cq"], nm[j].1 ≠ y := fun y hy e => o1 (e ▸ hy)
    have n2 : ∀ y ∈ ["w", "inw", "ws", "q", "cq"], nm[j].2 ≠ y := fun y hy e => o2 (e ▸ hy)
    have s1 : ∀ x ∈ [nm[j].1, nm[j].2], setLocal (setLocal (setLocal s.locals "w" (BitVec.ofNat 64 (cl.length + 1)))
        "ws" (BitVec.ofNat 64 q)) "inw" 1 x = s.locals x := fun x hx => by
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
      rcases hx with rfl | rfl
      · simp [setLocal, n1 "w" (by simp), n1 "ws" (by simp), n1 "inw" (by simp)]
      · simp [setLocal, n2 "w" (by simp), n2 "ws" (by simp), n2 "inw" (by simp)]
    by_cases hjc : j = cl.length
    · subst hjc
      constructor
      · rw [ifsRes_locals, dif_pos ⟨by omega, by omega⟩]
        simp only [Nat.add_sub_cancel, if_true]
        simp [slot_eq]
      · rw [hloc _ fun _ e => o12 (Eq.symm e), s1 _ (by simp), hj'.2, slot_eq, slot_eq]
    · have e1 : slot (cl, some q) j = slot (cl, none) j := by
        rcases Nat.lt_or_gt_of_ne hjc with hl | hg
        · rw [slot_lt hl, slot_lt hl]
        · rw [slot_gt hg, slot_gt hg]
      rw [e1]
      constructor
      · rw [hloc _ fun hW e => (nm_apart hnm hj hW hjc).1 e, s1 _ (by simp)]; exact hj'.1
      · rw [hloc _ fun hW e => (nm_apart hnm hj hW hjc).2.2.1 e, s1 _ (by simp)]; exact hj'.2

/-- **A word closed**: its length set in its name and `inw` cleared, the slots stand with the word listed. -/
theorem close_slots {nm : List (String × String)} (hnm : NmOk nm) {s : PancakeState σ} {cl : List (Nat × Nat)}
    {st n : Nat} (hs : ∀ j (h : j < nm.length), s.locals nm[j].1 = some (BitVec.ofNat 64 (slot (cl, some st) j).1) ∧
      s.locals nm[j].2 = some (BitVec.ofNat 64 (slot (cl, some st) j).2)) :
    (∀ y, y ≠ "inw" → (∀ hW : cl.length < nm.length, y ≠ nm[cl.length].2) →
      (setL (ifsRes s Prod.snd nm 0 (cl.length + 1) (BitVec.ofNat 64 n)) "inw" 0).locals y = s.locals y) ∧
    ∀ j (h : j < nm.length),
      (setL (ifsRes s Prod.snd nm 0 (cl.length + 1) (BitVec.ofNat 64 n)) "inw" 0).locals nm[j].1 =
        some (BitVec.ofNat 64 (slot (cl ++ [(st, n)], none) j).1) ∧
      (setL (ifsRes s Prod.snd nm 0 (cl.length + 1) (BitVec.ofNat 64 n)) "inw" 0).locals nm[j].2 =
        some (BitVec.ofNat 64 (slot (cl ++ [(st, n)], none) j).2) := by
  have own := fun j hj => nm_own hnm (j := j) hj
  have hloc : ∀ y, (∀ (hW : cl.length < nm.length), y ≠ nm[cl.length].2) →
      (ifsRes s Prod.snd nm 0 (cl.length + 1) (BitVec.ofNat 64 n)).locals y = s.locals y := by
    intro y hy
    rw [ifsRes_locals]
    split
    · simp only [Nat.add_sub_cancel]
      rw [if_neg (hy (by omega))]
    · rfl
  refine ⟨fun y h1 hy => by simp only [setL, setLocal, if_neg h1]; exact hloc y hy, fun j hj => ?_⟩
  have hj' := hs j hj
  obtain ⟨o1, o2, o12⟩ := own j hj
  have i1 : nm[j].1 ≠ "inw" := fun e => o1 (by rw [e]; simp)
  have i2 : nm[j].2 ≠ "inw" := fun e => o2 (by rw [e]; simp)
  simp only [setL, setLocal, if_neg i1, if_neg i2]
  by_cases hjc : j = cl.length
  · subst hjc
    rw [hloc _ fun _ e => o12 e, hj'.1, slot_eq, slot_lt (by simp)]
    refine ⟨by simp, ?_⟩
    rw [ifsRes_locals, dif_pos ⟨by omega, by omega⟩]
    simp
  · have e1 : slot (cl ++ [(st, n)], none) j = slot (cl, some st) j := by
      rcases Nat.lt_or_gt_of_ne hjc with hl | hg
      · rw [slot_lt (by simp; omega), slot_lt hl, List.getElem_append_left hl]
      · by_cases hj2 : j = cl.length + 1
        · subst hj2
          rw [slot_gt hg, show cl.length + 1 = (cl ++ [(st, n)]).length by simp, slot_eq]; rfl
        · rw [slot_gt hg, slot_gt (by simp; omega)]
    rw [e1]
    exact ⟨by rw [hloc _ fun hW e => (nm_apart hnm hj hW hjc).2.1 e]; exact hj'.1,
      by rw [hloc _ fun hW e => (nm_apart hnm hj hW hjc).2.2.2 e]; exact hj'.2⟩

/-- **A word ended** at `q`: its length in its name, `inw` cleared. -/
theorem scanAt_end {L : List Byte} {nm : List (String × String)} (hnm : NmOk nm) {s0 s : PancakeState σ} {q st : Nat}
    (h : ScanAt L nm s0 q q s) (hc : (scanTo L q).2 = some st) (hb : CommandSpec.isWS (L.getD q 0) = true) :
    ScanAt L nm s0 (q + 1) q (setL (ifsRes s Prod.snd nm 0 ((scanTo L q).1.length + 1)
      (BitVec.ofNat 64 (q - st))) "inw" 0) := by
  have e : scanTo L (q + 1) = ((scanTo L q).1 ++ [(st, q - st)], none) := by
    simp only [scanTo, hb, if_true, hc]
  generalize hst : scanTo L q = sc at h hc e
  obtain ⟨cl, c⟩ := sc
  simp only at hc e ⊢
  subst hc
  have own := fun j hj => nm_own hnm (j := j) hj
  obtain ⟨f1, f2, f3, f4, f5, f6⟩ := ifsRes_fields s Prod.snd nm 0 (cl.length + 1) (BitVec.ofNat 64 (q - st))
  obtain ⟨hloc, hsl⟩ := close_slots hnm (n := q - st) fun j hj => by have := h.slots j hj; rwa [hst] at this
  refine ⟨fun y hy => ?_, f1.trans h.memory, f2.trans h.memaddrs, f3.trans h.be, f4.trans h.ffi, f5.trans h.base,
    f6.trans h.code, ?_, ?_, ?_, ?_, fun j hj => by rw [e]; exact hsl j hj⟩
  · rw [hloc y (fun e => hy (by simp [scanNames, e])) fun hW e => hy (e ▸ nm_snd_mem hW)]
    exact h.frame y hy
  · rw [hloc "q" (by decide) fun hW e => (q_apart hnm _ hW).2 e]
    exact h.hq
  · rw [hloc "w" (by decide) fun hW e => (own _ hW).2.1 (by rw [← e]; simp), h.hw, e, hst]
    simp [count]
  · simp [setL, setLocal, e]
  · rw [hloc "ws" (by decide) fun hW e => (own _ hW).2.1 (by rw [← e]; simp)]
    obtain ⟨v, hv, -⟩ := h.hws
    exact ⟨v, hv, fun st' hs => by rw [e] at hs; cases hs⟩

theorem lowKK_ifs (sel : String × String → String) {e : Syntax.PExpr} {E : PancakeExp}
    (he : Lower.lowerExp e = some E) :
    ∀ (nm : List (String × String)) (j : Nat), LowKK (ifsFrom sel e nm j)
  | [], _ => fun k => ⟨k, rfl⟩
  | p :: rest, j => lowKK_append (xs := [_]) (lowKK_one rfl
      (a := .cond (.cmp .equal (.var "w") (.const (BitVec.ofNat 64 (j + 1)))) (.assign (sel p) E) .skip)
      (by simp [Lower.lowerStmt1, Lower.lowerStmtsFold, Syntax.eEq, Syntax.v, Syntax.n, Lower.lowerExp, he]))
      (lowKK_ifs sel he rest (j + 1))

/-- The octet at `q` of the line, read as `kept` reads it. -/
theorem kept_eval {B : Word} {L : List Byte} {s : PancakeState σ} {q : Nat} (hq : q < L.length)
    (hb : s.locals "blk" = some B) (hql : s.locals "q" = some (BitVec.ofNat 64 q))
    (hm : memLoadByte s.memory s.memaddrs s.be (B + BitVec.ofNat 64 40 + BitVec.ofNat 64 q) = some L[q]) :
    eval s (.loadByte (.op .add (.op .add (.var "blk") (.const (BitVec.ofNat 64 framerHead))) (.var "q"))) =
      some (L[q].setWidth 64) := by
  simp only [eval, hb, hql, show framerHead = 40 from rfl, hm]

/-- A space or a tab, as the scan tests it. -/
theorem ws_eval {s : PancakeState σ} {b : Byte} (h : s.locals "cq" = some (b.setWidth 64)) :
    eval s (.cmp .less (.const 0) (.op .add (.cmp .equal (.var "cq") (.const (BitVec.ofNat 64 32)))
      (.cmp .equal (.var "cq") (.const (BitVec.ofNat 64 9))))) = some (bw (CommandSpec.isWS b)) := by
  simp only [eval, h]
  rw [SessionCheck.byte_eq b 32 (by decide), SessionCheck.byte_eq b 9 (by decide)]
  rw [show (0 : Word) = BitVec.ofNat 64 0 from rfl] at *
  have := SessionCheck.or_word (decide (b = BitVec.ofNat 8 32)) (decide (b = BitVec.ofNat 8 9))
  refine congrArg some (Eq.trans ?_ (this.trans ?_))
  · rfl
  · congr 1

theorem declared_ifs (sel : String × String → String) (e : Syntax.PExpr) :
    ∀ (nm : List (String × String)) (j : Nat), declared (ifsFrom sel e nm j) = []
  | [], _ => rfl
  | _ :: rest, j => by simp only [ifsFrom, declared]; exact declared_ifs sel e rest (j + 1)

theorem nm_snd_mem' {nm : List (String × String)} (p : String × String) (hp : p ∈ nm) : p.2 ∈ scanNames nm := by
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hp; exact nm_snd_mem hj

theorem nm_get {nm : List (String × String)} {p : String × String} (hp : p ∈ nm) : ∃ j, ∃ hj : j < nm.length,
    nm[j] = p := List.getElem_of_mem hp

/-- The scan's loop body, the names of `nm` set. -/
def scanBody (nm : List (String × String)) : List Syntax.PStmt :=
  [.dec "cq" (Session.kept (Syntax.v "q")),
   .ite (SessionStore.or2 (Syntax.eEq (Syntax.v "cq") (Syntax.n 32)) (Syntax.eEq (Syntax.v "cq") (Syntax.n 9)))
     [.ite (Syntax.v "inw") (ifsFrom Prod.snd (Syntax.eSub (Syntax.v "q") (Syntax.v "ws")) nm 0 ++
       [.assign "inw" (Syntax.n 0)]) []]
     [.ite (Syntax.eEq (Syntax.v "inw") (Syntax.n 0))
       ([SessionStore.inc "w", .assign "ws" (Syntax.v "q"), .assign "inw" (Syntax.n 1)] ++
         ifsFrom Prod.fst (Syntax.v "q") nm 0) []],
   SessionStore.inc "q"]

theorem scanTo_same_ws {L : List Byte} {q : Nat} (hb : CommandSpec.isWS (L.getD q 0) = true)
    (hc : (scanTo L q).2 = none) : scanTo L (q + 1) = scanTo L q := by
  simp only [scanTo, hb, if_true, hc]
  rw [← hc]

theorem scanTo_same_in {L : List Byte} {q st : Nat} (hb : CommandSpec.isWS (L.getD q 0) = false)
    (hc : (scanTo L q).2 = some st) : scanTo L (q + 1) = scanTo L q := by
  simp only [scanTo, hb, Bool.false_eq_true, if_false, hc, Option.getD_some]
  rw [← hc]

/-- **One octet scanned.** -/
theorem body_frag (o : Oracle σ) {L : List Byte} {nm : List (String × String)} (hnm : NmOk nm) {s0 : PancakeState σ}
    {B : Word} (hl : LineIn B L s0) (hbk : "blk" ∉ scanNames nm) {q : Nat} (hq : q < L.length) :
    Frag o (scanBody nm) (ScanAt L nm s0 q q) (ScanAt L nm s0 (q + 1) (q + 1)) := by
  have hcq := cq_apart hnm
  have hbyte : ∀ s, ScanAt L nm s0 q q s → eval s (.loadByte (.op .add (.op .add (.var "blk")
      (.const (BitVec.ofNat 64 framerHead))) (.var "q"))) = some (L[q].setWidth 64) := fun s h =>
    kept_eval hq (by rw [h.frame "blk" hbk]; exact hl.blk) h.hq
        (by rw [h.memory, h.memaddrs, h.be]; exact hl.bytes q hq)
  have hgd : L.getD q 0 = L[q] := by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hq]
  let P1 : Assn σ := fun s => ScanAt L nm s0 q q s ∧ s.locals "cq" = some (L[q].setWidth 64)
  have f1 : Frag o [.dec "cq" (Session.kept (Syntax.v "q"))] (ScanAt L nm s0 q q) P1 :=
    frag_dec o rfl fun s h => ⟨_, hbyte s h, scanAt_set h (by simp [scanNames]) (by decide) (by decide)
      (by decide) (by decide) (fun j hj => hcq j hj) _, by simp [setLocal]⟩
  have hbound : ∀ s, ScanAt L nm s0 q q s → ∀ p ∈ nm, (∃ old, s.locals p.1 = some old) ∧ ∃ old, s.locals p.2 = some
      old :=
    fun s h p hp => by
      obtain ⟨j, hj, rfl⟩ := nm_get hp
      exact ⟨⟨_, (h.slots j hj).1⟩, ⟨_, (h.slots j hj).2⟩⟩
  have hown := hnm.own2
  have hle := scanTo_le L q
  let C : PancakeExp := .cmp .less (.const 0) (.op .add (.cmp .equal (.var "cq") (.const (BitVec.ofNat 64 32)))
    (.cmp .equal (.var "cq") (.const (BitVec.ofNat 64 9))))
  have hC : ∀ s, P1 s → eval s C = some (bw (CommandSpec.isWS L[q])) := fun s h => ws_eval h.2
  have hnmw : nm.length < 2 ^ 62 := hnm.short
  -- a space or a tab: a word in it ends
  have fws : Frag o [.ite (Syntax.v "inw") (ifsFrom Prod.snd (Syntax.eSub (Syntax.v "q") (Syntax.v "ws")) nm 0 ++
      [.assign "inw" (Syntax.n 0)]) []] (fun s => P1 s ∧ eval s C ≠ some 0) (ScanAt L nm s0 (q + 1) q) := by
    refine frag_ite o (C := .var "inw") rfl (scanAt_clock) (fun s h => ⟨_, h.1.1.hinw⟩) ?_
        (fun _ _ _ _ h => by simp [declared_append, declared_ifs, declared] at h)
      (frag_nil o fun s ⟨⟨⟨h, _⟩, hws⟩, hz⟩ => ?_) (fun _ _ _ _ h => by simp [declared] at h)
    · refine frag_each o (lowKK_append (lowKK_ifs Prod.snd rfl nm 0) (lowKK_one rfl rfl))
        fun s ⟨⟨⟨h, hcq⟩, hws⟩, hin⟩ => ?_
      have hb : CommandSpec.isWS (L.getD q 0) = true := by
        rw [hgd]; cases e : CommandSpec.isWS L[q]
        · exact absurd (by rw [hC s ⟨h, hcq⟩, e]; rfl) hws
        · rfl
      obtain ⟨st, hst⟩ : ∃ st, (scanTo L q).2 = some st := by
        cases e : (scanTo L q).2 with
        | none => exact absurd (by simp only [eval]; rw [h.hinw, e]; rfl) hin
        | some st => exact ⟨st, rfl⟩
      have hstq := hle.2.1 st hst
      obtain ⟨wv, hwv, hwst⟩ := h.hws
      have hwv' := hwst st hst
      subst hwv'
      have hcount : count (scanTo L q) = (scanTo L q).1.length + 1 := by simp [count, hst]
      have hcl : (scanTo L q).1.length + 1 ≤ q := by have := hle.2.2; simp [hst] at this; omega
      have hshort := hl.short
      have f1 := ifs_frag o Prod.snd (e := Syntax.eSub (Syntax.v "q") (Syntax.v "ws"))
        (E := .op .sub (.var "q") (.var "ws")) rfl nm 0 s ((scanTo L q).1.length + 1) (BitVec.ofNat 64 (q - st))
        (by omega) (by omega) (by rw [h.hw, hcount]) (by
          simp only [eval, h.hq, hwv]; rw [SessionCheck.sub_small q st (by omega) (by omega)])
        (fun p hp e => (hown p hp).2 (by rw [e]; simp))
        (fun p hp => ⟨fun e => (hown p hp).2 (by rw [← e]; simp), fun e => (hown p hp).2 (by rw [← e]; simp)⟩)
        (fun p hp => (hbound s h p hp).2)
      refine frag_append f1 (frag_conseq (assign_frag o (x := "inw") (e := Syntax.n 0) (E := .const 0) rfl
        (v := 0) rfl ⟨_, by
          rw [ifsRes_locals]; split
          · rw [if_neg (hnm.inw_snd _ (List.getElem_mem _))]; exact h.hinw
          · exact h.hinw⟩) (fun _ h => h) fun u hu => scanAt_like (scanAt_end hnm h hst hb) hu)
    · have hb : CommandSpec.isWS (L.getD q 0) = true := by
        rw [hgd]; cases e : CommandSpec.isWS L[q]
        · exact absurd (by rw [hC s ⟨h, ‹_›⟩, e]; rfl) hws
        · rfl
      have hst : (scanTo L q).2 = none := by
        cases e : (scanTo L q).2 with
        | none => rfl
        | some st => exact absurd hz (by simp only [eval]; rw [h.hinw, e]; simp)
      exact scanAt_of_eq h (scanTo_same_ws hb hst)
  -- another octet: a word starts at it
  have fin : Frag o [.ite (Syntax.eEq (Syntax.v "inw") (Syntax.n 0))
      ([SessionStore.inc "w", .assign "ws" (Syntax.v "q"), .assign "inw" (Syntax.n 1)] ++
        ifsFrom Prod.fst (Syntax.v "q") nm 0) []] (fun s => P1 s ∧ eval s C = some 0) (ScanAt L nm s0 (q + 1) q) := by
    refine frag_ite o (C := .cmp .equal (.var "inw") (.const 0)) rfl scanAt_clock
      (fun s h => ⟨_, by simp only [eval, h.1.1.hinw]; rfl⟩) ?_
      (fun _ _ _ _ h => by simp [declared_ifs, declared, SessionStore.inc] at h)
      (frag_nil o fun s ⟨⟨⟨h, hcq⟩, hws⟩, hz⟩ => ?_) (fun _ _ _ _ h => by simp [declared] at h)
    · refine frag_each o (lowKK_append (xs := [_, _, _]) (lowKK_append (xs := [_]) (lowKK_one rfl rfl)
        (lowKK_append (xs := [_]) (lowKK_one rfl rfl) (lowKK_one rfl rfl))) (lowKK_ifs Prod.fst rfl nm 0))
        fun s ⟨⟨⟨h, hcq⟩, hws⟩, hin⟩ => ?_
      have hb : CommandSpec.isWS (L.getD q 0) = false := by
        rw [hgd]; cases e : CommandSpec.isWS L[q]
        · rfl
        · exact absurd hws (by rw [hC s ⟨h, hcq⟩, e]; decide)
      have hst : (scanTo L q).2 = none := by
        cases e : (scanTo L q).2 with
        | none => rfl
        | some st => exact absurd hin (by simp only [eval]; rw [h.hinw, e]; simp)
      have hcount : count (scanTo L q) = (scanTo L q).1.length := by simp [count, hst]
      have hcl : (scanTo L q).1.length ≤ q := by have := hle.2.2; simp [hst] at this; omega
      have hshort := hl.short
      have hw1 := h.hw
      rw [hcount] at hw1
      have s1 := assign_frag o (s := s) (x := "w") (e := Syntax.eAdd (Syntax.v "w") (Syntax.n 1))
        (E := .op .add (.var "w") (.const 1)) rfl (v := BitVec.ofNat 64 ((scanTo L q).1.length + 1))
        (by simp only [eval, hw1]; rw [BitVec.ofNat_add]; rfl) ⟨_, hw1⟩
      let W := (scanTo L q).1.length + 1
      let s1' := setL s "w" (BitVec.ofNat 64 W)
      have s2 := assign_frag o (s := s1') (x := "ws") (e := Syntax.v "q") (E := .var "q") rfl
        (v := BitVec.ofNat 64 q) (by simp [s1', setL, setLocal, eval, h.hq]) (by
          obtain ⟨v, hv, -⟩ := h.hws; exact ⟨v, by simp [s1', setL, setLocal, hv]⟩)
      let s2' := setL s1' "ws" (BitVec.ofNat 64 q)
      have s3 := assign_frag o (s := s2') (x := "inw") (e := Syntax.n 1) (E := .const 1) rfl (v := 1) rfl
        ⟨0, by simp [s2', s1', setL, setLocal, h.hinw, hst]⟩
      let s3' := setL s2' "inw" 1
      have hnotw : ∀ p ∈ nm, p.1 ≠ "w" ∧ p.1 ≠ "ws" ∧ p.1 ≠ "inw" ∧ p.1 ≠ "q" := fun p hp =>
        ⟨fun e => (hown p hp).1 (by rw [e]; simp), fun e => (hown p hp).1 (by rw [e]; simp),
          fun e => (hown p hp).1 (by rw [e]; simp), fun e => (hown p hp).1 (by rw [e]; simp)⟩
      have s4 := ifs_frag o Prod.fst (e := Syntax.v "q") (E := .var "q") rfl nm 0 s3' W (BitVec.ofNat 64 q)
        (by omega) (by omega) (by simp [s3', s2', s1', setL, setLocal, W])
        (by simp [s3', s2', s1', setL, setLocal, eval, h.hq])
        (fun p hp => (hnotw p hp).1) (fun p hp => fun e => (hnotw p hp).2.2.2 e.symm)
        (fun p hp => by
          obtain ⟨old, hold⟩ := (hbound s h p hp).1
          exact ⟨old, by
            simp [s3', s2', s1', setL, setLocal, (hnotw p hp).1, (hnotw p hp).2.1, (hnotw p hp).2.2.1, hold]⟩)
      refine frag_append (xs := [_]) s1 (frag_append (xs := [_]) s2 (frag_append (xs := [_]) s3
        (frag_conseq s4 (fun _ h => h) fun u hu => scanAt_like (scanAt_start hnm h hst hb) hu)))
    · have hb : CommandSpec.isWS (L.getD q 0) = false := by
        rw [hgd]; cases e : CommandSpec.isWS L[q]
        · rfl
        · exact absurd hws (by rw [hC s ⟨h, hcq⟩, e]; decide)
      obtain ⟨st, hst⟩ : ∃ st, (scanTo L q).2 = some st := by
        cases e : (scanTo L q).2 with
        | none => exact absurd hz (by simp only [eval]; rw [h.hinw, e]; simp)
        | some st => exact ⟨st, rfl⟩
      exact scanAt_of_eq h (scanTo_same_in hb hst)
  have f2 : Frag o [.ite (SessionStore.or2 (Syntax.eEq (Syntax.v "cq") (Syntax.n 32)) (Syntax.eEq (Syntax.v "cq")
      (Syntax.n 9))) [.ite (Syntax.v "inw") (ifsFrom Prod.snd (Syntax.eSub (Syntax.v "q") (Syntax.v "ws")) nm 0 ++
      [.assign "inw" (Syntax.n 0)]) []] [.ite (Syntax.eEq (Syntax.v "inw") (Syntax.n 0))
      ([SessionStore.inc "w", .assign "ws" (Syntax.v "q"), .assign "inw" (Syntax.n 1)] ++
        ifsFrom Prod.fst (Syntax.v "q") nm 0) []]] P1 (ScanAt L nm s0 (q + 1) q) :=
    frag_ite o (C := C) rfl scanAt_clock (fun s h => ⟨_, hC s h⟩) fws (fun _ _ _ _ h => by simp [declared] at h)
      fin (fun _ _ _ _ h => by simp [declared] at h)
  have f3 : Frag o [SessionStore.inc "q"] (ScanAt L nm s0 (q + 1) q) (ScanAt L nm s0 (q + 1) (q + 1)) :=
    frag_one (a := .assign "q" (.op .add (.var "q") (.const 1))) rfl rfl rfl scanAt_clock
      (Safe.assign fun s h => ⟨BitVec.ofNat 64 (q + 1), _, by simp only [eval, h.hq]; rw [BitVec.ofNat_add]; rfl,
        h.hq, scanAt_inc hnm h⟩)
  exact frag_append (xs := [_]) f1 (frag_append (xs := [_]) f2 f3)

/-- The words' places at the end of the line. -/
structure WordsAt (L : List Byte) (nm : List (String × String)) (s0 s : PancakeState σ) : Prop where
  frame : ∀ y, y ∉ scanNames nm → s.locals y = s0.locals y
  memory : s.memory = s0.memory
  memaddrs : s.memaddrs = s0.memaddrs
  be : s.be = s0.be
  ffi : s.ffi = s0.ffi
  base : s.baseAddr = s0.baseAddr
  code : s.code = s0.code
  hw : s.locals "w" = some (BitVec.ofNat 64 (spans L).length)
  slots : ∀ j (h : j < nm.length), s.locals nm[j].1 = some (BitVec.ofNat 64 ((spans L).getD j (0, 0)).1) ∧
    s.locals nm[j].2 = some (BitVec.ofNat 64 ((spans L).getD j (0, 0)).2)

theorem getD_slot {cl : List (Nat × Nat)} (j : Nat) : slot (cl, none) j = cl.getD j (0, 0) := by
  rcases Nat.lt_trichotomy j cl.length with h | h | h
  · rw [slot_lt h]; simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]
  · subst h; rw [slot_eq]; simp [List.getD_eq_getElem?_getD]
  · rw [slot_gt h]; simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega : cl.length ≤ j)]

/-- **The line ended outside a word.** -/
theorem wordsAt_none {L : List Byte} {nm : List (String × String)} {s0 s : PancakeState σ}
    (h : ScanAt L nm s0 L.length L.length s) (hc : (scanTo L L.length).2 = none) : WordsAt L nm s0 s := by
  have hsp : spans L = (scanTo L L.length).1 := by rw [spans_end, hc]; simp
  refine ⟨h.frame, h.memory, h.memaddrs, h.be, h.ffi, h.base, h.code, ?_, fun j hj => ?_⟩
  · rw [h.hw, hsp]; simp [count, hc]
  · have := h.slots j hj
    generalize hst : scanTo L L.length = st at this hc hsp
    obtain ⟨cl, c⟩ := st
    simp only at hc hsp
    subst hc
    rw [hsp, ← getD_slot]
    exact this

/-- **The line ended inside a word**, its length set at the line's end. -/
theorem wordsAt_close {L : List Byte} {nm : List (String × String)} (hnm : NmOk nm) {s0 s : PancakeState σ} {st : Nat}
    (h : ScanAt L nm s0 L.length L.length s) (hc : (scanTo L L.length).2 = some st) :
    WordsAt L nm s0 (setL (ifsRes s Prod.snd nm 0 ((scanTo L L.length).1.length + 1)
      (BitVec.ofNat 64 (L.length - st))) "inw" 0) := by
  have hsp : spans L = (scanTo L L.length).1 ++ [(st, L.length - st)] := by rw [spans_end, hc]; simp
  generalize hst : scanTo L L.length = sc at h hc hsp
  obtain ⟨cl, c⟩ := sc
  simp only at hc hsp ⊢
  subst hc
  have own := fun j hj => nm_own hnm (j := j) hj
  obtain ⟨f1, f2, f3, f4, f5, f6⟩ := ifsRes_fields s Prod.snd nm 0 (cl.length + 1) (BitVec.ofNat 64 (L.length - st))
  obtain ⟨hloc, hsl⟩ := close_slots hnm (n := L.length - st) fun j hj => by have := h.slots j hj; rwa [hst] at this
  refine ⟨fun y hy => ?_, f1.trans h.memory, f2.trans h.memaddrs, f3.trans h.be, f4.trans h.ffi, f5.trans h.base,
    f6.trans h.code, ?_, fun j hj => by rw [hsp, ← getD_slot]; exact hsl j hj⟩
  · rw [hloc y (fun e => hy (by simp [scanNames, e])) fun hW e => hy (e ▸ nm_snd_mem hW)]
    exact h.frame y hy
  · rw [hloc "w" (by decide) fun hW e => (own _ hW).2.1 (by rw [← e]; simp), h.hw, hst, hsp]
    simp [count]

/-- The scan's locals in the order it declares them. -/
def scanDecl (nm : List (String × String)) : List String := ["w"] ++ nm.flatMap (fun p => [p.1, p.2]) ++
    ["inw", "ws", "q"]

theorem scanWords_eq (k : Nat) : Session.scanWords k = (scanDecl (scanNmFrom 0 k)).map (fun x => .dec x (Syntax.n 0)) ++
    [.while (Syntax.eLt (Syntax.v "q") (Syntax.v "kept")) (scanBody (scanNmFrom 0 k)),
     .ite (Syntax.v "inw") (ifsFrom Prod.snd (Syntax.eSub (Syntax.v "kept") (Syntax.v "ws")) (scanNmFrom 0 k) 0 ++
       [.assign "inw" (Syntax.n 0)]) []] := by
  simp only [Session.scanWords, Session.endWord, List.range_eq_range', starts_eq, ends_eq, scanBody, scanDecl,
    scanNmFrom, List.map_append, List.flatMap_map, List.map_flatMap, List.map_cons, List.map_nil, List.append_assoc,
    List.cons_append, List.nil_append]

theorem scanAt_zero {L : List Byte} {nm : List (String × String)} {s0 s : PancakeState σ}
    (h : Zeros s0 (scanDecl nm) s) : ScanAt L nm s0 0 0 s where
  frame y hy := h.frame y fun e => hy (by
    simp only [scanDecl, List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at e
    simp only [scanNames, List.mem_append, List.mem_cons, List.mem_nil_iff, or_false]
    rcases e with (e | e) | e
    · exact Or.inl (Or.inl e)
    · exact Or.inr e
    · rcases e with e | e | e <;> simp [e])
  memory := h.memory
  memaddrs := h.memaddrs
  be := h.be
  ffi := h.ffi
  base := h.base
  code := h.code
  hq := h.zero "q" (by simp [scanDecl])
  hw := by rw [h.zero "w" (by simp [scanDecl])]; simp [scanTo, count]
  hinw := by rw [h.zero "inw" (by simp [scanDecl])]; simp [scanTo]
  hws := ⟨0, h.zero "ws" (by simp [scanDecl]), fun st hs => by simp [scanTo] at hs⟩
  slots j hj := by
    have hm : nm[j] ∈ nm := List.getElem_mem hj
    rw [h.zero _ (by simp only [scanDecl, List.mem_append, List.mem_flatMap]; exact Or.inl (Or.inr ⟨_, hm, by simp⟩)),
      h.zero _ (by simp only [scanDecl, List.mem_append, List.mem_flatMap]; exact Or.inl (Or.inr ⟨_, hm, by simp⟩))]
    simp [scanTo, slot]

theorem lowKK_scanBody (nm : List (String × String)) : LowKK (scanBody nm) :=
  lowKK_append (xs := [_]) (lowKK_dec rfl) (lowKK_append (xs := [_]) (lowKK_ite rfl
    (lowKK_ite rfl (lowKK_append (lowKK_ifs Prod.snd rfl nm 0) (lowKK_one rfl rfl)) (fun k => ⟨k, rfl⟩))
    (lowKK_ite rfl (lowKK_append (xs := [_, _, _]) (lowKK_append (xs := [_]) (lowKK_one rfl rfl)
      (lowKK_append (xs := [_]) (lowKK_one rfl rfl) (lowKK_one rfl rfl))) (lowKK_ifs Prod.fst rfl nm 0))
      (fun k => ⟨k, rfl⟩))) (lowKK_one rfl rfl))

/-- **The session's scan of the line's words**: from the line in the framer's block, if it goes on, `w` holds how
many words it has and the first ones' places hold where they start and how long they are, every other local and
word as they were. -/
theorem scanWords_frag (o : Oracle σ) (k : Nat) (hnm : NmOk (scanNmFrom 0 k))
    (hbk : "blk" ∉ scanNames (scanNmFrom 0 k)) (hkk : "kept" ∉ scanNames (scanNmFrom 0 k)) {L : List Byte}
    {B : Word} {s0 : PancakeState σ} (hl : LineIn B L s0) :
    Frag o (Session.scanWords k) (Like s0) (WordsAt L (scanNmFrom 0 k) s0) := by
  let nm := scanNmFrom 0 k
  rw [scanWords_eq]
  have f1 : Frag o ((scanDecl nm).map fun x => .dec x (Syntax.n 0)) (Like s0) (ScanAt L nm s0 0 0) :=
    frag_conseq (decs_frag o s0 (scanDecl nm) []) (fun s (h : Like s0 s) => ⟨fun _ h => by simp at h,
      fun y _ => by rw [h.locals], h.memory, h.memaddrs, h.be, h.ffi, h.base, h.code⟩)
      (fun s h => scanAt_zero (L := L) (by simpa using h))
  have hshort := hl.short
  let I (q : Nat) : Assn σ := fun s => q ≤ L.length ∧ ScanAt L nm s0 q q s
  have hcond : ∀ q s, I q s →
      eval s (.cmp .less (.var "q") (.var "kept")) = some (if decide (q < L.length) then 1 else 0) := fun q s h => by
    simp only [eval, h.2.hq, h.2.frame "kept" hkk, hl.kept, WpBytes.signedLt_small (a := q) (b := L.length)
      (by omega) (by omega)]
  have f2 := frag_count o (c := Syntax.eLt (Syntax.v "q") (Syntax.v "kept")) rfl (lowKK_scanBody nm) (I := I)
    (fun _ _ _ h => ⟨h.1, scanAt_clock _ _ h.2⟩)
    (fun q u y v h hy => by
      simp [scanBody, declared, SessionStore.inc] at hy; subst hy; exact ⟨h.1, scanAt_restore hnm h.2 v⟩) hcond
    (fun q hg => frag_conseq (body_frag o (L := L) hnm hl hbk (of_decide_eq_true hg)) (fun _ h => h.2)
      fun _ h => ⟨of_decide_eq_true hg, h⟩) 0
  -- the last word ended at the line's end
  have hle := scanTo_le L L.length
  have hown := hnm.own2
  have f3 : Frag o [.ite (Syntax.v "inw") (ifsFrom Prod.snd (Syntax.eSub (Syntax.v "kept") (Syntax.v "ws")) nm 0 ++
      [.assign "inw" (Syntax.n 0)]) []] (ScanAt L nm s0 L.length L.length) (WordsAt L nm s0) := by
    refine frag_ite o (C := .var "inw") rfl (fun _ _ h => { h with }) (fun s h => ⟨_, h.hinw⟩) ?_
      (fun _ _ _ _ h => by simp [declared_append, declared_ifs, declared] at h)
      (frag_nil o fun s ⟨h, hz⟩ => ?_) (fun _ _ _ _ h => by simp [declared] at h)
    · refine frag_each o (lowKK_append (lowKK_ifs Prod.snd rfl nm 0) (lowKK_one rfl rfl)) fun s ⟨h, hin⟩ => ?_
      obtain ⟨st, hst⟩ : ∃ st, (scanTo L L.length).2 = some st := by
        cases e : (scanTo L L.length).2 with
        | none => exact absurd (by simp only [eval]; rw [h.hinw, e]; rfl) hin
        | some st => exact ⟨st, rfl⟩
      have hstq := hle.2.1 st hst
      obtain ⟨wv, hwv, hwst⟩ := h.hws
      have hwv' := hwst st hst
      subst hwv'
      have hcount : count (scanTo L L.length) = (scanTo L L.length).1.length + 1 := by simp [count, hst]
      have hcl : (scanTo L L.length).1.length + 1 ≤ L.length := by have := hle.2.2; simp [hst] at this; omega
      have f1 := ifs_frag o Prod.snd (e := Syntax.eSub (Syntax.v "kept") (Syntax.v "ws"))
        (E := .op .sub (.var "kept") (.var "ws")) rfl nm 0 s ((scanTo L L.length).1.length + 1)
        (BitVec.ofNat 64 (L.length - st)) (by omega) (by have : nm.length < 2 ^ 62 := hnm.short; omega)
        (by rw [h.hw, hcount]) (by
          simp only [eval, h.frame "kept" hkk, hl.kept, hwv]
          rw [SessionCheck.sub_small L.length st (by omega) (by omega)])
        (fun p hp e => (hown p hp).2 (by rw [e]; simp))
        (fun p hp => ⟨fun e => hkk (by rw [e]; exact nm_snd_mem' p hp), fun e => (hown p hp).2 (by rw [← e]; simp)⟩)
        (fun p hp => by obtain ⟨j, hj, rfl⟩ := nm_get hp; exact ⟨_, (h.slots j hj).2⟩)
      refine frag_append f1 (frag_conseq (assign_frag o (x := "inw") (e := Syntax.n 0) (E := .const 0) rfl
        (v := 0) rfl ⟨_, by
          rw [ifsRes_locals]; split
          · rw [if_neg (hnm.inw_snd _ (List.getElem_mem _))]; exact h.hinw
          · exact h.hinw⟩) (fun _ h => h) fun u hu => ?_)
      have := wordsAt_close hnm h hst
      exact ⟨fun y hy => by rw [hu.locals]; exact this.frame y hy, hu.memory.trans this.memory,
        hu.memaddrs.trans this.memaddrs, hu.be.trans this.be, hu.ffi.trans this.ffi, hu.base.trans this.base,
        hu.code.trans this.code, by rw [hu.locals]; exact this.hw, fun j hj => by rw [hu.locals]; exact this.slots j hj⟩
    · have hst : (scanTo L L.length).2 = none := by
        cases e : (scanTo L L.length).2 with
        | none => rfl
        | some st => exact absurd hz (by simp only [eval]; rw [h.hinw, e]; simp)
      exact wordsAt_none h hst
  refine frag_append f1 (frag_append (xs := [_])
    (frag_conseq f2 (fun _ h => ⟨Nat.zero_le _, h⟩) fun s ⟨q, h, hz⟩ => ?_) f3)
  have : q = L.length := by have := h.1; have := of_decide_eq_false hz; omega
  subst this; exact h.2

/-! ### A word as a name -/

/-- `fold`, as it lowers, of an octet's word. -/
def foldE (E : PancakeExp) : PancakeExp :=
  .op .sub E (.mul (.const 32) (.op .and_ (.cmp .less (.const 96) E) (.cmp .less E (.const 123))))

theorem fold_lower {e : Syntax.PExpr} {E : PancakeExp} (he : Lower.lowerExp e = some E) :
    Lower.lowerExp (Session.fold e) = some (foldE E) := by
  simp [Session.fold, foldE, Lower.lowerExp, Syntax.eSub, Syntax.eMul, Syntax.eAnd, Syntax.eLt, Syntax.n, he]

/-- **`fold` is `upper`.** -/
theorem fold_eval {s : PancakeState σ} {E : PancakeExp} {b : Byte} (h : eval s E = some (b.setWidth 64)) :
    eval s (foldE E) = some ((CommandSpec.upper b).setWidth 64) := by
  have hb := b.isLt
  simp only [foldE, eval, h, setWidth8_64]
  rw [show (96 : Word) = BitVec.ofNat 64 96 from rfl, show (123 : Word) = BitVec.ofNat 64 123 from rfl,
    WpBytes.signedLt_small (a := 96) (b := b.toNat) (by decide) (by omega),
    WpBytes.signedLt_small (a := b.toNat) (b := 123) (by omega) (by decide)]
  simp only [CommandSpec.upper]
  by_cases e : 97 ≤ b.toNat ∧ b.toNat ≤ 122
  · rw [if_pos e, if_pos (by simp; omega), if_pos (by simp; omega)]
    congr 1
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_sub, BitVec.toNat_setWidth]
    omega
  · rw [if_neg e]
    by_cases a : 96 < b.toNat
    · rw [if_pos (by simpa using a), if_neg (by simp; omega), show ((1 : Word) &&& 0) = 0 from rfl,
        show (32 : Word) * 0 = 0 from rfl]
      simp
    · rw [if_neg (by simpa using a)]
      simp

/-- A word of the line, `S` its start in the local `sn`, its length in `ln`. -/
structure WordAt (sn ln : String) (B S : Word) (w : List Byte) (s : PancakeState σ) : Prop where
  blk : s.locals "blk" = some B
  start : s.locals sn = some S
  len : s.locals ln = some (BitVec.ofNat 64 w.length)
  bytes : ∀ i (h : i < w.length),
    memLoadByte s.memory s.memaddrs s.be (B + BitVec.ofNat 64 40 + (S + BitVec.ofNat 64 i)) = some w[i]
  short : w.length < 2 ^ 62

/-- The comparison so far: the word as long as the text, and its first `i` octets in upper case the text's. -/
def prefixIs (w T : List Byte) (i : Nat) : Bool := decide
    (w.length = T.length ∧ (w.take i).map CommandSpec.upper = T.take i)

theorem prefixIs_step {w T : List Byte} {i : Nat} (hi : i < w.length) (hl : w.length = T.length) :
    prefixIs w T (i + 1) = (prefixIs w T i && decide (CommandSpec.upper w[i] = T[i]'(by omega))) := by
  simp only [prefixIs, hl, true_and]
  rw [List.take_add_one, List.getElem?_eq_getElem hi]
  simp only [Option.toList_some, List.map_append, List.map_cons, List.map_nil]
  have hT : List.take (i + 1) T = List.take i T ++ [T[i]'(by omega)] := by
    rw [List.take_add_one, List.getElem?_eq_getElem (by omega)]; rfl
  rw [hT]
  by_cases e : List.map CommandSpec.upper (List.take i w) = List.take i T
  · rw [e]; simp only [List.append_cancel_left_eq, List.cons.injEq, and_true, decide_true, Bool.true_and]
  · simp only [e, decide_false, Bool.false_and]
    rw [decide_eq_false_iff_not]
    intro h
    exact e (List.append_inj_left' h (by simp))

theorem prefixIs_full {w T : List Byte} : prefixIs w T w.length = decide (w.map CommandSpec.upper = T) := by
  simp only [prefixIs, List.take_length]
  by_cases hl : w.length = T.length
  · rw [hl, List.take_length]
    simp
  · simp only [hl, false_and, decide_false]
    symm; rw [decide_eq_false_iff_not]
    intro e; exact hl (by rw [← e, List.length_map])

theorem prefixIs_mono {w T : List Byte} {i j : Nat} (hij : i ≤ j) (h : prefixIs w T j = true) :
    prefixIs w T i = true := by
  simp only [prefixIs, decide_eq_true_eq] at h ⊢
  refine ⟨h.1, ?_⟩
  have := congrArg (List.take i) h.2
  rwa [← List.map_take, List.take_take, List.take_take, Nat.min_eq_left hij] at this

/-- Two octets differ, as `ne` tests them. -/
theorem ne_bytes (x y : Byte) :
    (if (if x.setWidth 64 = y.setWidth 64 then (1 : Word) else 0) = 0 then (1 : Word) else 0) = bw
        (decide (x ≠ y)) := by
  by_cases e : x = y
  · subst e; simp [bw]
  · have : x.setWidth 64 ≠ y.setWidth 64 := fun h => e (by
      apply BitVec.eq_of_toNat_eq
      have := congrArg BitVec.toNat h
      simp only [BitVec.toNat_setWidth] at this
      have := x.isLt; have := y.isLt
      omega)
    simp [this, e, bw]

theorem textAddr_lower {t : Nat} (ht : t < texts.length) : Lower.lowerExp (Session.textAddr t) =
    some (.op .add .base (.const (BitVec.ofNat 64 (ownOff + ownTexts + textAt t)))) := by
  obtain ⟨T0, hT0⟩ := SessionAppend.lay
  have hT := SessionAppend.text_below ht
  rw [hT0.eq] at hT
  have hpos : (ownOff + ownTexts + textAt t == 0) = false := by
    rw [beq_eq_false_iff_ne]; have := SessionAppend.nums.own64; omega
  simp [Session.textAddr, SessionStore.at_, Syntax.atOff, hpos, Lower.lowerExp, Syntax.eAdd, Syntax.n]

theorem wordIsAt_low (sn ln : String) {t : Nat} (ht : t < texts.length) : LowKK (Session.wordIsAt sn ln t) := by
  have hTA := textAddr_lower ht
  have hlow : LowKK [.ite (SessionStore.ne (Session.fold (Session.kept (Syntax.eAdd (Syntax.v sn) (Syntax.v "jq"))))
      (.loadb (Syntax.eAdd (Session.textAddr t) (Syntax.v "jq")))) [.assign "eqk" (Syntax.n 0)] [],
      SessionStore.inc "jq"] :=
    lowKK_append (xs := [_]) (lowKK_ite (by simp [SessionStore.ne, Syntax.eEq, Syntax.n, Lower.lowerExp, fold_lower,
      Session.kept, Syntax.eAdd, Syntax.v, hTA]; rfl) (lowKK_one rfl rfl (a := .assign "eqk" (.const 0)))
      (fun k => ⟨k, rfl⟩)) (lowKK_one rfl rfl)
  obtain ⟨BODY, hBl⟩ := lowKK_fold hlow
  rw [Session.wordIsAt]
  exact lowKK_append (xs := [_]) (lowKK_one rfl rfl) (lowKK_append (xs := [_]) (lowKK_one rfl rfl)
    (lowKK_one rfl (by
      simp only [Lower.lowerStmt1, hBl]; simp [Syntax.eAnd, Syntax.eLt, Syntax.v, Lower.lowerExp]; rfl)))

/-- **The word's comparison with text `t`**: if it goes on, `eqk` is one when the word in upper case is the text. -/
theorem wordIsAt_frag (o : Oracle σ) {sn ln : String} (hsn : sn ≠ "eqk" ∧ sn ≠ "jq") (hln : ln ≠ "eqk" ∧ ln ≠ "jq")
    {t : Nat} (ht : t < texts.length) {b B S : Word} {w : List Byte} {s1 : PancakeState σ}
    (hw : WordAt sn ln B S w s1) (hb : s1.baseAddr = b)
    (htx : SessionAppend.TextsIn b s1.memory s1.memaddrs s1.be)
    (he : ∃ v, s1.locals "eqk" = some v) (hj : ∃ v, s1.locals "jq" = some v) :
    Frag o (Session.wordIsAt sn ln t) (Like s1) (fun u => SessionCheck.ButFor ["eqk", "jq"] s1 u ∧
      (∃ v, u.locals "jq" = some v) ∧ u.locals "eqk" = some
          (bw (decide (w.map CommandSpec.upper = texts.getD t [])))) := by
  rw [Session.wordIsAt]
  obtain ⟨T0, hT0⟩ := SessionAppend.lay
  have hT := SessionAppend.text_below ht
  have hroom := hT0.room
  rw [hT0.eq] at hT
  have hTA := textAddr_lower ht
  have hbytes := htx t ht
  generalize ownOff + ownTexts + textAt t = X at hT hTA hbytes
  have hlen : (texts.getD t []).length = Session.textLen t := rfl
  generalize texts.getD t [] = T at hbytes hlen ⊢
  generalize Session.textLen t = tl at hT hlen ⊢
  subst hlen
  have hshort := hw.short
  have hB : s1.locals "blk" = some B := hw.blk
  let I (i : Nat) (u : PancakeState σ) : Prop := SessionCheck.ButFor ["eqk", "jq"] s1 u ∧
    u.locals "jq" = some (BitVec.ofNat 64 i) ∧ i ≤ w.length ∧ u.locals "eqk" = some (bw (prefixIs w T i))
  have Iclock : ∀ i, Safe.ClockFree (I i) := fun _ _ _ ⟨h1, h2, h3, h4⟩ => ⟨{ h1 with }, h2, h3, h4⟩
  have keep : ∀ u y, y ∉ ["eqk", "jq"] → SessionCheck.ButFor ["eqk", "jq"] s1 u → u.locals y = s1.locals y :=
    fun u y hy h => h.locals y hy
  have nb : "blk" ∉ ["eqk", "jq"] := by decide
  have nsn : sn ∉ ["eqk", "jq"] := by simp [hsn.1, hsn.2]
  have nln : ln ∉ ["eqk", "jq"] := by simp [hln.1, hln.2]
  let body : List Syntax.PStmt := [.ite (SessionStore.ne (Session.fold (Session.kept (Syntax.eAdd (Syntax.v sn)
      (Syntax.v "jq")))) (.loadb (Syntax.eAdd (Session.textAddr t) (Syntax.v "jq")))) [.assign "eqk" (Syntax.n 0)] [],
    SessionStore.inc "jq"]
  let CE : PancakeExp := .cmp .equal (.cmp .equal (foldE (SessionCheck.kb (.var sn) (.var "jq")))
    (.loadByte (.op .add (.op .add .base (.const (BitVec.ofNat 64 X))) (.var "jq")))) (.const 0)
  have hCE : Lower.lowerExp (SessionStore.ne (Session.fold (Session.kept (Syntax.eAdd (Syntax.v sn) (Syntax.v "jq"))))
      (.loadb (Syntax.eAdd (Session.textAddr t) (Syntax.v "jq")))) = some CE := by
    simp [SessionStore.ne, Syntax.eEq, Syntax.n, Lower.lowerExp, fold_lower, Session.kept, Syntax.eAdd, Syntax.v,
      hTA, SessionCheck.kb, framerHead, CE]
  have hCv : ∀ i u, I i u → (hi : i < w.length) → (hT : i < T.length) →
      eval u CE = some (bw (decide (CommandSpec.upper w[i] ≠ T[i]))) := fun i u h hi hT => by
    have hA : eval u (.op .add (.var sn) (.var "jq")) = some (S + BitVec.ofNat 64 i) := by
      simp only [eval, keep u sn nsn h.1, hw.start, h.2.1]
    have hk := SessionCheck.kb_eval (by rw [keep u "blk" nb h.1, hB]) hA
      (by rw [h.1.memory, h.1.memaddrs, h.1.be]; exact hw.bytes i hi)
    have hf := fold_eval hk
    have ht := hbytes i hT
    rw [← hb, ← h.1.base, ← h.1.memory, ← h.1.memaddrs, ← h.1.be, List.getElem!_eq_getElem?_getD,
      List.getElem?_eq_getElem hT, Option.getD_some] at ht
    simp only [CE, eval, hf, h.2.1, ht]
    rw [← ne_bytes]
  have hbody : ∀ i, i < w.length → prefixIs w T i = true → Frag o body (I i) (I (i + 1)) := fun i hi hp => by
    have hlT : w.length = T.length := by simp only [prefixIs, decide_eq_true_eq] at hp; exact hp.1
    have hiT : i < T.length := hlT ▸ hi
    let M : Assn σ := fun u => SessionCheck.ButFor ["eqk", "jq"] s1 u ∧ u.locals "jq" = some (BitVec.ofNat 64 i) ∧
      u.locals "eqk" = some (bw (prefixIs w T (i + 1)))
    have hstep := prefixIs_step hi hlT
    rw [hp, Bool.true_and] at hstep
    have f1 : Frag o [.ite (SessionStore.ne (Session.fold (Session.kept (Syntax.eAdd (Syntax.v sn) (Syntax.v "jq"))))
        (.loadb (Syntax.eAdd (Session.textAddr t) (Syntax.v "jq")))) [.assign "eqk" (Syntax.n 0)] []] (I i) M := by
      refine frag_ite o hCE (fun _ _ ⟨h1, h2, h3⟩ => ⟨{ h1 with }, h2, h3⟩) (fun s h => ⟨_, hCv i s h hi hiT⟩) ?_
        (fun _ _ _ _ h => by simp [declared] at h) (frag_nil o fun s ⟨h, hz⟩ => ?_)
        (fun _ _ _ _ h => by simp [declared] at h)
      · refine frag_one (a := .assign "eqk" (.const 0)) rfl rfl rfl
          (fun _ _ ⟨h1, h2, h3⟩ => ⟨{ h1 with }, h2, h3⟩) (Safe.assign fun s ⟨h, hn⟩ => ⟨0, _, rfl, h.2.2.2, ?_⟩)
        have hne : CommandSpec.upper w[i] ≠ T[i] := by
          intro e; apply hn; rw [hCv i s h hi hiT]; simp [e, bw]
        exact ⟨SessionCheck.but_set h.1 (by simp) 0, by simp [setLocal, h.2.1], by simp [setLocal, hstep, hne, bw]⟩
      · have he' : CommandSpec.upper w[i] = T[i] := by
          have := SessionCheck.bw_eq0 ((hCv i s h hi hiT).symm.trans hz)
          simpa using this
        exact ⟨h.1, h.2.1, by rw [h.2.2.2, hp, hstep, he']; simp⟩
    have f2 : Frag o [SessionStore.inc "jq"] M (I (i + 1)) :=
      frag_one (a := .assign "jq" (.op .add (.var "jq") (.const 1))) rfl rfl rfl (Iclock (i + 1))
        (Safe.assign fun s h => ⟨BitVec.ofNat 64 (i + 1), _, by simp only [eval, h.2.1]; rw [BitVec.ofNat_add]; rfl,
          h.2.1, SessionCheck.but_set h.1 (by simp) _, by simp [setLocal], by omega, by simp [setLocal, h.2.2]⟩)
    exact frag_append (xs := [_]) f1 f2
  have hlow : LowKK body := lowKK_append (xs := [_]) (lowKK_ite hCE (lowKK_one rfl rfl (a := .assign "eqk" (.const 0)))
    (fun k => ⟨k, rfl⟩)) (lowKK_one rfl rfl)
  let COND : PancakeExp := .op .and_ (.var "eqk") (.cmp .less (.var "jq") (.var ln))
  have hcond : ∀ i u, I i u → eval u COND = some (bw (prefixIs w T i && decide (i < w.length))) := fun i u h =>
    SessionCheck.eval_and (by simp only [eval]; exact h.2.2.2)
      (SessionCheck.eval_lt (by omega) (by omega) (by simp only [eval]; exact h.2.1)
        (by simp only [eval]; rw [keep u ln nln h.1]; exact hw.len))
  have f3 := frag_count o (c := Syntax.eAnd (Syntax.v "eqk") (Syntax.eLt (Syntax.v "jq") (Syntax.v ln))) (C := COND)
    (by simp [Syntax.eAnd, Syntax.eLt, Syntax.v, Lower.lowerExp, COND]) hlow Iclock
    (fun _ _ _ _ _ hy => by simp [body, declared, SessionStore.inc] at hy) hcond
    (fun i hg => by simp only [Bool.and_eq_true, decide_eq_true_eq] at hg; exact hbody i hg.2 hg.1) 0
  have hT64 : T.length < 2 ^ 64 := by omega
  have e0 : eval s1 (.cmp .equal (.var ln) (.const (BitVec.ofNat 64 T.length))) = some (bw (prefixIs w T 0)) := by
    rw [SessionCheck.eval_eq (x := w.length) (y := T.length) (by omega) hT64 (by simp only [eval]; exact hw.len)
      (SessionCheck.eval_const rfl)]
    simp [prefixIs]
  have f1 := assign_frag o (x := "eqk") (e := Syntax.eEq (Syntax.v ln) (Syntax.n T.length)) rfl e0 he
  have f2 := assign_frag o (s := setL s1 "eqk" (bw (prefixIs w T 0))) (x := "jq") (e := Syntax.n 0) rfl
    (v := 0) rfl (by simp only [setL, setLocal, if_neg (by decide : ("jq" : String) ≠ "eqk")]; exact hj)
  have f12 := frag_conseq (frag_append (xs := [_]) f1 f2) (fun _ h => h) fun u (hu : Like _ u) =>
    (show I 0 u from ⟨⟨fun y hy => by
        have h1 : y ≠ "eqk" := fun e => hy (by simp [e])
        have h2 : y ≠ "jq" := fun e => hy (by simp [e])
        simp [hu.locals, setL, setLocal, h1, h2], hu.memory, hu.memaddrs, hu.be, hu.base, hu.ffi, hu.code⟩,
      by simp [hu.locals, setL, setLocal], Nat.zero_le _, by simp [hu.locals, setL, setLocal]⟩)
  refine frag_conseq (frag_append (xs := [_, _]) f12 f3) (fun _ h => h) fun u ⟨i, h, hz⟩ => ⟨h.1, ⟨_, h.2.1⟩, ?_⟩
  rw [h.2.2.2, count_exit (p := prefixIs w T) (fun _ _ hij h => prefixIs_mono hij h) h.2.2.1 hz, prefixIs_full]

/-- The comparison from any state the premises hold in. -/
theorem wordIsAt_any (o : Oracle σ) {sn ln : String} (hsn : sn ≠ "eqk" ∧ sn ≠ "jq") (hln : ln ≠ "eqk" ∧ ln ≠ "jq")
    {t : Nat} (ht : t < texts.length) {b B S : Word} {w : List Byte} {P : Assn σ}
    (hP : ∀ s, P s → WordAt sn ln B S w s ∧ s.baseAddr = b ∧ SessionAppend.TextsIn b s.memory s.memaddrs s.be ∧
      (∃ v, s.locals "eqk" = some v) ∧ ∃ v, s.locals "jq" = some v) :
    Frag o (Session.wordIsAt sn ln t) P (fun u => ∃ s1, P s1 ∧ SessionCheck.ButFor ["eqk", "jq"] s1 u ∧
      (∃ v, u.locals "jq" = some v) ∧ u.locals "eqk" = some
          (bw (decide (w.map CommandSpec.upper = texts.getD t [])))) :=
  frag_each o (wordIsAt_low sn ln ht) fun s hs => by
    obtain ⟨h1, h2, h3, h4, h5⟩ := hP s hs
    exact frag_conseq (wordIsAt_frag o hsn hln ht h1 h2 h3 h4 h5) (fun _ h => h) fun u hu => ⟨s, hs, hu⟩

/-! ### The line's words in place -/

/-- A word of the line in place: its start in `sn`, its length in `ln`. -/
theorem wordAt_of {B : Word} {L : List Byte} {s : PancakeState σ} (hl : LineIn B L s) {p : Nat × Nat}
    (hp : p ∈ spans L) {sn ln : String} (hs : s.locals sn = some (BitVec.ofNat 64 p.1))
    (hn : s.locals ln = some (BitVec.ofNat 64 p.2)) : WordAt sn ln B (BitVec.ofNat 64 p.1) (cut L p) s := by
  have hb := spans_bound L p hp
  have hlen := cut_length hb
  have hsh := hl.short
  refine ⟨hl.blk, hs, by rw [hlen]; exact hn, fun i hi => ?_, by omega⟩
  rw [cut_get hb i hi, ← BitVec.ofNat_add]
  exact hl.bytes (p.1 + i) (by rw [hlen] at hi; omega)

/-! ### The keyword of CAPABILITIES -/

/-- `isAlphaE` as it lowers. -/
def alphaE (E : PancakeExp) : PancakeExp :=
  SessionCheck.or2E (.op .and_ (.cmp .less (.const (BitVec.ofNat 64 64)) E)
    (.cmp .less E (.const (BitVec.ofNat 64 91))))
    (.op .and_ (.cmp .less (.const (BitVec.ofNat 64 96)) E) (.cmp .less E (.const (BitVec.ofNat 64 123))))

theorem alpha_lower {e : Syntax.PExpr} {E : PancakeExp} (he : Lower.lowerExp e = some E) :
    Lower.lowerExp (Session.isAlphaE e) = some (alphaE E) := by
  simp [Session.isAlphaE, alphaE, SessionStore.or2, SessionCheck.or2E, Syntax.eAnd, Syntax.eLt, Syntax.eAdd,
    Syntax.n, Lower.lowerExp, he]

theorem alpha_eval {s : PancakeState σ} {E : PancakeExp} {b : Byte} (h : eval s E = some (b.setWidth 64)) :
    eval s (alphaE E) = some (bw (CommandSpec.isAlpha b)) := by
  have hb := b.isLt
  rw [setWidth8_64] at h
  have c : ∀ k : Nat, k < 2 ^ 63 → eval s (.const (BitVec.ofNat 64 k)) = some (BitVec.ofNat 64 k) := fun _ _ => rfl
  rw [alphaE, SessionCheck.eval_or2 (SessionCheck.eval_and (SessionCheck.eval_lt (by decide) (by omega) (c 64
    (by decide)) h) (SessionCheck.eval_lt (by omega) (by decide) h (c 91 (by decide))))
    (SessionCheck.eval_and (SessionCheck.eval_lt (by decide) (by omega) (c 96 (by decide)) h)
      (SessionCheck.eval_lt (by omega) (by decide) h (c 123 (by decide))))]
  congr 2
  simp only [CommandSpec.isAlpha]
  generalize b.toNat = x
  by_cases h1 : 64 < x <;> by_cases h2 : x < 91 <;> by_cases h3 : 96 < x <;> by_cases h4 : x < 123 <;>
    simp [h1, h2, h3, h4] <;> omega

/-- The keyword test after `i` octets. -/
def kwOk (w : List Byte) (i : Nat) : Bool :=
  decide (3 ≤ w.length) && CommandSpec.isAlpha (w.getD 0 0) && ((w.drop 1).take (i - 1)).all CommandSpec.keywordRest

theorem kwOk_full (w : List Byte) : kwOk w w.length = CommandSpec.isKeyword w := by
  cases w with
  | nil => rfl
  | cons a rest =>
    simp only [kwOk, CommandSpec.isKeyword, List.length_cons, List.getD_cons_zero, List.drop_one, List.tail_cons,
      Nat.add_sub_cancel, List.take_length]
    by_cases h : 2 ≤ rest.length
    · simp [h, show 3 ≤ rest.length + 1 by omega]; rfl
    · simp [h, show ¬ 3 ≤ rest.length + 1 by omega]

theorem kwOk_step {w : List Byte} {i : Nat} (h1 : 1 ≤ i) (hi : i < w.length) :
    kwOk w (i + 1) = (kwOk w i && CommandSpec.keywordRest w[i]) := by
  simp only [kwOk]
  rw [show i + 1 - 1 = (i - 1) + 1 by omega, List.take_add_one, List.getElem?_drop,
    show 1 + (i - 1) = i by omega, List.getElem?_eq_getElem hi]
  simp [Bool.and_assoc]

theorem kwOk_mono {w : List Byte} {i j : Nat} (hij : i ≤ j) (h : kwOk w j = true) : kwOk w i = true := by
  simp only [kwOk, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h ⊢
  refine ⟨h.1, fun x hx => h.2 x ?_⟩
  exact List.take_subset_take_left _ (by omega) hx

/-- `isDigitE` as it lowers. -/
def digitE (E : PancakeExp) : PancakeExp :=
  .op .and_ (.cmp .less (.const (BitVec.ofNat 64 47)) E) (.cmp .less E (.const (BitVec.ofNat 64 58)))

theorem digitE_eval {s : PancakeState σ} {E : PancakeExp} {b : Byte} (h : eval s E = some (b.setWidth 64)) :
    eval s (digitE E) = some (bw (CommandSpec.isDigit b)) := by
  simp only [digitE, eval, h]; rw [← SessionCheck.digit_eval b]; rfl

/-- The keyword's later octets' test as it lowers. -/
def restE (E : PancakeExp) : PancakeExp :=
  SessionCheck.or2E (SessionCheck.or2E (alphaE E) (digitE E))
    (SessionCheck.or2E (.cmp .equal E (.const (BitVec.ofNat 64 46))) (.cmp .equal E (.const (BitVec.ofNat 64 45))))

theorem rest_eval {s : PancakeState σ} {E : PancakeExp} {b : Byte} (h : eval s E = some (b.setWidth 64)) :
    eval s (restE E) = some (bw (CommandSpec.keywordRest b)) := by
  have hb := b.isLt
  have h' := h
  rw [setWidth8_64] at h'
  rw [restE, SessionCheck.eval_or2 (SessionCheck.eval_or2 (alpha_eval h) (digitE_eval h))
    (SessionCheck.eval_or2 (SessionCheck.eval_eq (by omega) (by decide) h' (y := 46) rfl)
      (SessionCheck.eval_eq (by omega) (by decide) h' (y := 45) rfl))]
  congr 2
  simp only [CommandSpec.keywordRest]
  have e46 : (b == 46#8) = decide (b.toNat = 46) := by
    by_cases e : b.toNat = 46
    · simp [show b = 46#8 from BitVec.eq_of_toNat_eq (by simp [e])]
    · simp [e]; intro h; exact e (by rw [h]; rfl)
  have e45 : (b == 45#8) = decide (b.toNat = 45) := by
    by_cases e : b.toNat = 45
    · simp [show b = 45#8 from BitVec.eq_of_toNat_eq (by simp [e])]
    · simp [e]; intro h; exact e (by rw [h]; rfl)
  rw [e46, e45]
  simp only [Bool.or_assoc]

/-- **CAPABILITIES's keyword check is `CommandSpec.isKeyword`**, of the second word, if it goes on. -/
theorem keyword_frag (o : Oracle σ) {B S : Word} {w : List Byte} {s1 : PancakeState σ}
    (hw : WordAt "s1" "l1" B S w s1) (hok : ∃ v, s1.locals "ok" = some v) (hjq : ∃ v, s1.locals "jq" = some v) :
    Frag o Session.keywordCheck (Like s1) (fun u => SessionCheck.ButFor ["ok", "jq", "cz"] s1 u ∧
      (∃ v, u.locals "jq" = some v) ∧ u.locals "ok" = some (bw (CommandSpec.isKeyword w))) := by
  have hshort := hw.short
  have keep : ∀ u y, y ∉ ["ok", "jq", "cz"] → SessionCheck.ButFor ["ok", "jq", "cz"] s1 u → u.locals y = s1.locals y :=
    fun u y hy h => h.locals y hy
  have hle : eval s1 (SessionCheck.leE (.const (BitVec.ofNat 64 3)) (.var "l1")) =
      some (bw (decide (3 ≤ w.length))) :=
    SessionCheck.eval_le (by decide) (by omega) rfl (by simp only [eval]; exact hw.len)
  have f1 := assign_frag o (x := "ok") (e := Syntax.eLe (Syntax.n 3) (Syntax.v "l1")) rfl hle hok
  let s2 := setL s1 "ok" (bw (decide (3 ≤ w.length)))
  have f2 : Frag o [.ite (Syntax.v "ok") [.assign "ok" (Session.isAlphaE (Session.kept (Syntax.v "s1")))] []]
      (Like s2) (Like (setL s1 "ok" (bw (kwOk w 1)))) := by
    refine frag_ite o (C := .var "ok") rfl (like_clock _) (fun s h => ⟨bw (decide (3 ≤ w.length)), by
      simp only [eval]; rw [h.locals]; simp [s2, setL, setLocal]⟩) ?_ (fun _ _ _ _ h => by simp [declared] at h)
      (frag_nil o fun s ⟨h, hz⟩ => ?_) (fun _ _ _ _ h => by simp [declared] at h)
    · refine frag_one (a := .assign "ok" (alphaE (.loadByte (.op .add (.op .add (.var "blk")
        (.const (BitVec.ofNat 64 framerHead))) (.var "s1"))))) (by simp [Lower.lowerStmt1, alpha_lower,
        Session.kept, Syntax.eAdd, Syntax.v, Syntax.n, Lower.lowerExp]) rfl rfl (like_clock _)
        (Safe.assign fun s ⟨h, hn⟩ => ?_)
      have hv : s.locals "ok" = some (bw (decide (3 ≤ w.length))) := by rw [h.locals]; simp [s2, setL, setLocal]
      have h3 : 3 ≤ w.length := by
        cases e : decide (3 ≤ w.length)
        · rw [e] at hv; exact absurd (by simp only [eval]; rw [hv]; rfl) hn
        · exact of_decide_eq_true e
      have hb := hw.bytes 0 (by omega)
      rw [show S + BitVec.ofNat 64 0 = S by simp] at hb
      have hk : eval s (.loadByte (.op .add (.op .add (.var "blk") (.const (BitVec.ofNat 64 framerHead)))
          (.var "s1"))) = some (w[0].setWidth 64) := by
        simp only [eval, h.locals, h.memory, h.memaddrs, h.be, s2, setL, setLocal]
        simp only [show ("blk" = "ok") = False by decide, show ("s1" = "ok") = False by decide, if_false, hw.blk,
          hw.start, show framerHead = 40 from rfl]
        rw [hb]
      refine ⟨_, _, alpha_eval hk, hv, ?_⟩
      have e1 : kwOk w 1 = CommandSpec.isAlpha w[0] := by
        simp [kwOk, h3, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show 0 < w.length by omega)]
      rw [e1]
      exact ⟨by rw [h.locals]; funext y; simp [s2, setL, setLocal]; split <;> rfl, h.memory, h.memaddrs, h.be, h.ffi,
        h.base, h.code⟩
    · have hv : s.locals "ok" = some (bw (decide (3 ≤ w.length))) := by rw [h.locals]; simp [s2, setL, setLocal]
      have hz' : some (bw (decide (3 ≤ w.length))) = some 0 := by simp only [eval] at hz; rw [hv] at hz; exact hz
      have hd : decide (3 ≤ w.length) = false := SessionCheck.bw_eq0 hz'
      have e1 : kwOk w 1 = false := by simp [kwOk, hd]
      rw [e1, ← hd]
      exact h
  have f3 := assign_frag o (s := setL s1 "ok" (bw (kwOk w 1))) (x := "jq") (e := Syntax.n 1) rfl (v := 1) rfl
    (by simp only [setL, setLocal, if_neg (by decide : ("jq" : String) ≠ "ok")]; exact hjq)
  let I (i : Nat) (u : PancakeState σ) : Prop := SessionCheck.ButFor ["ok", "jq", "cz"] s1 u ∧
    u.locals "jq" = some (BitVec.ofNat 64 i) ∧ 1 ≤ i ∧ (i = 1 ∨ i ≤ w.length) ∧ (kwOk w i = true → i ≤ w.length) ∧
    u.locals "ok" = some (bw (kwOk w i))
  have Iclock : ∀ i, Safe.ClockFree (I i) := fun _ _ _ ⟨h1, h2⟩ => ⟨{ h1 with }, h2⟩
  let body : List Syntax.PStmt := [.dec "cz" (Session.kept (Syntax.eAdd (Syntax.v "s1") (Syntax.v "jq"))),
    .assign "ok" (SessionStore.or2
      (SessionStore.or2 (Session.isAlphaE (Syntax.v "cz")) (Session.isDigitE (Syntax.v "cz")))
      (SessionStore.or2 (Syntax.eEq (Syntax.v "cz") (Syntax.n 46)) (Syntax.eEq (Syntax.v "cz") (Syntax.n 45)))),
    SessionStore.inc "jq"]
  have hrest : Lower.lowerExp (SessionStore.or2 (SessionStore.or2 (Session.isAlphaE (Syntax.v "cz"))
      (Session.isDigitE (Syntax.v "cz"))) (SessionStore.or2 (Syntax.eEq (Syntax.v "cz") (Syntax.n 46))
      (Syntax.eEq (Syntax.v "cz") (Syntax.n 45)))) = some (restE (.var "cz")) := by
    simp [SessionStore.or2, SessionCheck.or2E, restE, alpha_lower, Session.isDigitE, digitE, Syntax.eAnd, Syntax.eLt,
      Syntax.eAdd, Syntax.eEq, Syntax.n, Syntax.v, Lower.lowerExp]
  have hbody : ∀ i, i < w.length → kwOk w i = true → Frag o body (I i) (I (i + 1)) := fun i hi hp => by
    let M1 : Assn σ := fun u => SessionCheck.ButFor ["ok", "jq", "cz"] s1 u ∧ u.locals "jq" = some (BitVec.ofNat 64 i) ∧
      1 ≤ i ∧ u.locals "cz" = some (w[i].setWidth 64) ∧ ∃ v, u.locals "ok" = some v
    let M2 : Assn σ := fun u => SessionCheck.ButFor ["ok", "jq", "cz"] s1 u ∧ u.locals "jq" = some (BitVec.ofNat 64 i) ∧
      1 ≤ i ∧ u.locals "ok" = some (bw (CommandSpec.keywordRest w[i]))
    have g1 : Frag o [body[0]] (I i) M1 := frag_dec o (E := SessionCheck.kb (.var "s1") (.var "jq")) rfl fun s h => by
      have hA : eval s (.op .add (.var "s1") (.var "jq")) = some (S + BitVec.ofNat 64 i) := by
        simp only [eval, keep s "s1" (by decide) h.1, hw.start, h.2.1]
      refine ⟨_, SessionCheck.kb_eval (by rw [keep s "blk" (by decide) h.1]; exact hw.blk) hA
        (by rw [h.1.memory, h.1.memaddrs, h.1.be]; exact hw.bytes i hi), ?_⟩
      exact ⟨SessionCheck.but_set h.1 (by simp) _, by simp [setLocal, h.2.1], h.2.2.1, by simp [setLocal],
        bw (kwOk w i), by simp [setLocal, h.2.2.2.2.2]⟩
    have g2 : Frag o [body[1]] M1 M2 :=
      frag_one (a := .assign "ok" (restE (.var "cz"))) (by
          show Lower.lowerStmt1 (.assign "ok" _) = _; simp only [Lower.lowerStmt1, hrest]) rfl rfl
        (fun _ _ ⟨h1, h2⟩ => ⟨{ h1 with }, h2⟩) (Safe.assign fun s h => by
          obtain ⟨v, hv⟩ := h.2.2.2.2
          exact ⟨_, v, rest_eval (by simp only [eval]; exact h.2.2.2.1), hv, SessionCheck.but_set h.1 (by simp) _,
            by simp [setLocal, h.2.1], h.2.2.1, by simp [setLocal]⟩)
    have g3 : Frag o [body[2]] M2 (I (i + 1)) :=
      frag_one (a := .assign "jq" (.op .add (.var "jq") (.const 1))) rfl rfl rfl (Iclock (i + 1))
        (Safe.assign fun s h => ⟨BitVec.ofNat 64 (i + 1), _, by simp only [eval, h.2.1]; rw [BitVec.ofNat_add]; rfl,
          h.2.1, SessionCheck.but_set h.1 (by simp) _, by simp [setLocal], by omega, Or.inr (by omega),
          fun _ => by omega, by simp [setLocal, h.2.2.2, kwOk_step h.2.2.1 hi, hp]⟩)
    exact frag_append (xs := [_]) g1 (frag_append (xs := [_]) g2 g3)
  have hlow : LowKK body := lowKK_append (xs := [_]) (lowKK_dec (E := SessionCheck.kb (.var "s1") (.var "jq")) rfl)
    (lowKK_append (xs := [_]) (lowKK_one rfl (a := .assign "ok" (restE (.var "cz")))
      (by show Lower.lowerStmt1 (.assign "ok" _) = _; simp only [Lower.lowerStmt1, hrest])) (lowKK_one rfl rfl))
  let COND : PancakeExp := .op .and_ (.var "ok") (.cmp .less (.var "jq") (.var "l1"))
  have hcond : ∀ i u, I i u → eval u COND = some (bw (kwOk w i && decide (i < w.length))) := fun i u h =>
    SessionCheck.eval_and (by simp only [eval]; exact h.2.2.2.2.2)
      (SessionCheck.eval_lt (by rcases h.2.2.2.1 with e | e <;> omega) (by omega) (by simp only [eval]; exact h.2.1)
        (by simp only [eval]; rw [keep u "l1" (by decide) h.1]; exact hw.len))
  have f4 := frag_count o (c := Syntax.eAnd (Syntax.v "ok") (Syntax.eLt (Syntax.v "jq") (Syntax.v "l1"))) (C := COND)
    (by simp [Syntax.eAnd, Syntax.eLt, Syntax.v, Lower.lowerExp, COND]) hlow Iclock
    (fun i u y v h hy => by
      simp [body, declared, SessionStore.inc] at hy; subst hy
      refine ⟨SessionCheck.but_restore h.1 (by simp) v, ?_⟩
      simp only [restore, resVar, if_neg (by decide : ("jq" : String) ≠ "cz"),
        if_neg (by decide : ("ok" : String) ≠ "cz")]
      exact h.2) hcond
    (fun i hg => by simp only [Bool.and_eq_true, decide_eq_true_eq] at hg; exact hbody i hg.2 hg.1) 1
  have f123 := frag_conseq (frag_append (xs := [_]) f1 (frag_append (xs := [_]) f2 f3)) (fun _ h => h)
    fun u (hu : Like _ u) => (show I 1 u from ⟨⟨fun y hy => by
        have h1 : y ≠ "ok" := fun e => hy (by simp [e])
        have h2 : y ≠ "jq" := fun e => hy (by simp [e])
        simp [hu.locals, setL, setLocal, h1, h2], hu.memory, hu.memaddrs, hu.be, hu.base, hu.ffi, hu.code⟩,
      by simp [hu.locals, setL, setLocal], Nat.le_refl _, Or.inl rfl, fun e => by
        simp only [kwOk, Bool.and_eq_true, decide_eq_true_eq] at e; omega,
      by simp [hu.locals, setL, setLocal]⟩)
  refine frag_conseq (frag_append (xs := [_, _, _]) f123 f4) (fun _ h => h) fun u ⟨i, h, hz⟩ =>
    ⟨h.1, ⟨_, h.2.1⟩, ?_⟩
  rw [h.2.2.2.2.2, ← kwOk_full]
  have three : ∀ j, kwOk w j = true → 3 ≤ w.length := fun j e => by
    simp only [kwOk, Bool.and_eq_true, decide_eq_true_eq] at e; exact e.1.1
  rcases h.2.2.2.1 with e1 | e1
  · subst e1
    cases e : kwOk w 1
    · cases e2 : kwOk w w.length
      · rfl
      · have := three _ e2
        rw [kwOk_mono (by omega) e2] at e; exact absurd e (by decide)
    · rw [e, Bool.true_and, decide_eq_false_iff_not] at hz
      have := three _ e; omega
  · rw [count_exit (p := kwOk w) (fun _ _ hij h => kwOk_mono hij h) e1 hz]

theorem lowKK_keyword : LowKK Session.keywordCheck := lowK_any _ (k := .skip) (c := _) rfl

theorem nm2_ok : NmOk (scanNmFrom 0 2) := ⟨by decide, by decide, by decide⟩

theorem nm4_ok : NmOk (scanNmFrom 0 4) := ⟨by decide, by decide, by decide⟩

/-! ### The premises can hold -/

/-- A state of no memory, every local zero. -/
theorem lineIn_witness : LineIn 0 [] zeroState := ⟨rfl, rfl, fun _ h => absurd h (by simp), by decide⟩

theorem scanAt_witness : ScanAt [] [] zeroState 0 0 zeroState :=
  ⟨fun _ _ => rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ⟨0, rfl, fun _ h => by simp [scanTo] at h⟩,
    fun _ h => absurd h (by simp)⟩

theorem wordsAt_witness : WordsAt [] [] zeroState zeroState :=
  ⟨fun _ _ => rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun _ h => absurd h (by simp)⟩

theorem wordAt_witness : WordAt "s1" "l1" 0 0 [] zeroState := ⟨rfl, rfl, rfl, fun _ h => absurd h (by simp), by decide⟩

end DN.Server.SessionWords
