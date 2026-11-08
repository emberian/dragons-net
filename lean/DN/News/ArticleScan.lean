-- SPDX-License-Identifier: AGPL-3.0-or-later
import DN.News.ArticleRun

/-!
# DN.News.ArticleScan

The article program's scanners of a field's body, proven to read it as `DN.News.ArticleSpec` does, if they return.
`artMsgIds` reads message identifiers (`msgIds`), `artReceived` a date's start (`receivedDate`). `artTok` reads the
next word (`tokens`), `artNum` a number (`number?`).
-/

namespace DN.News.ArticleScan

open DN.Compiler DN.Compiler.Wp DN.Compiler.WpRet DN.Compiler.Frag DN.News.AbnfProg
open DN.News.AbnfSets DN.News.FunRun DN.News.AbnfLeaves DN.News.ArticleRun
open DN.News.ScanRun (at_ at_add vals_lookup without)
open DN.News.FramerCode (bw ev_var bw_ne0 bw_eq0)
open DN.News.AbnfComment (ev_inc)
open DN.News.ArticleProg (artMax guardL)
open DN.News.ArticleLines (seg seg_succ seg_length)
open DN.News.ArticleSpec (Bytes msgIds msgIdsFrom)

variable {σ : Type}

theorem beq_byte (b c : BitVec 8) : (b == c) = decide (b.toNat = c.toNat) := by
  rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff, BitVec.toNat_inj]

theorem seg_over (a : Bytes) {i e : Nat} (h : e ≤ i) : seg a i e = [] := by
  simp only [seg, show e - i = 0 by omega, List.take_zero]

/-! ## Message identifiers -/

/-- `artMsgIds`'s loop state: the place, the comment depth, an identifier's flag, start and length so far. Then the
flags of a long one and of one found, and the words of `xMsgS` and `xMsgL`. -/
structure IdsSt where
  i : Nat
  dep : Nat
  cur : Nat
  cs : Nat
  cl : Nat
  long : Nat
  found : Nat
  w1 : Word
  w2 : Word

/-- One turn of `artMsgIds`'s loop. -/
def idsStep (idMax : Nat) (a : Bytes) (q : IdsSt) : IdsSt :=
  let b := (a[q.i]!).toNat
  if q.cur ≠ 0 then
    if b = 62 then
      if q.found = 0 then
        { q with
          i := q.i + 1, cur := 0, cl := q.cl + 1, long := (if idMax < q.cl + 1 then 1 else q.long), found := 1
          w1 := BitVec.ofNat 64 q.cs, w2 := BitVec.ofNat 64 (q.cl + 1) }
      else { q with i := q.i + 1, cur := 0, cl := q.cl + 1, long := (if idMax < q.cl + 1 then 1 else q.long) }
    else { q with i := q.i + 1, cl := q.cl + 1 }
  else if q.dep = 0 then
    if b = 40 then { q with i := q.i + 1, dep := 1 }
    else if b = 60 then { q with i := q.i + 1, cur := 1, cs := q.i, cl := 1 }
    else { q with i := q.i + 1 }
  else if b = 92 then { q with i := q.i + 2 }
  else if b = 40 then { q with i := q.i + 1, dep := q.dep + 1 }
  else if b = 41 then { q with i := q.i + 1, dep := q.dep - 1 }
  else { q with i := q.i + 1 }

/-- The first identifier's place and length, as `xMsgS` and `xMsgL` hold them; -1 and 0 if there is none. -/
def IdsFirst (a : Bytes) (S E : Nat) (ids : List Bytes) (w1 w2 : Word) : Prop :=
  match ids with
  | [] => w1 = BitVec.ofNat 64 (2 ^ 64 - 1) ∧ w2 = 0
  | id :: _ => ∃ cs, S ≤ cs ∧ cs + id.length ≤ E ∧ seg a cs (cs + id.length) = id ∧ w1 = BitVec.ofNat 64 cs ∧
      w2 = BitVec.ofNat 64 id.length

theorem idsFirst_snoc {a : Bytes} {S E : Nat} {l : List Bytes} (hl : l ≠ []) (x : Bytes) {w1 w2 : Word} :
    IdsFirst a S E (l ++ [x]) w1 w2 ↔ IdsFirst a S E l w1 w2 := by
  cases l with
  | nil => exact absurd rfl hl
  | cons y l => rfl

/-- What `artMsgIds`'s loop keeps: the identifiers are those found, `acc` reversed, and those of the bytes left. -/
def IdsInv (idMax : Nat) (a : Bytes) (S E : Nat) (q : IdsSt) : Prop :=
  S ≤ q.i ∧ q.i ≤ E + 1 ∧ q.cur ≤ 1 ∧ q.long ≤ 1 ∧ q.found ≤ 1 ∧ q.dep ≤ q.i ∧ q.cl ≤ q.i ∧ q.cs ≤ q.i ∧
    ∃ acc : List Bytes,
      msgIds (seg a S E) =
        msgIdsFrom q.dep (if q.cur = 0 then none else some (seg a q.cs q.i).reverse) (seg a q.i E) acc ∧
      q.long = (if acc.any (·.length > idMax) then 1 else 0) ∧ (q.found = 0 ↔ acc = []) ∧
      IdsFirst a S E acc.reverse q.w1 q.w2 ∧ (q.cur ≠ 0 → q.dep = 0 ∧ S ≤ q.cs ∧ q.cs < q.i ∧ q.cl = q.i - q.cs)

theorem ids_init (idMax : Nat) (a : Bytes) {S E : Nat} (hSE : S ≤ E) :
    IdsInv idMax a S E ⟨S, 0, 0, 0, 0, 0, 0, BitVec.ofNat 64 (2 ^ 64 - 1), 0⟩ :=
  ⟨Nat.le_refl _, Nat.le_succ_of_le hSE, Nat.zero_le _, Nat.zero_le _, Nat.zero_le _, Nat.zero_le _, Nat.zero_le _,
    Nat.zero_le _, [], rfl, by simp, by simp, ⟨rfl, rfl⟩, fun h => absurd rfl h⟩

theorem ids_cur (dep : Nat) (cur : Bytes) (b : BitVec 8) (rest : Bytes) (acc : List Bytes) :
    msgIdsFrom dep (some cur) (b :: rest) acc =
      if b.toNat = 62 then msgIdsFrom dep none rest ((b :: cur).reverse :: acc)
      else msgIdsFrom dep (some (b :: cur)) rest acc := by
  simp only [msgIdsFrom, beq_byte, decide_eq_true_eq]; rfl

theorem ids_top (b : BitVec 8) (rest : Bytes) (acc : List Bytes) :
    msgIdsFrom 0 none (b :: rest) acc = if b.toNat = 40 then msgIdsFrom 1 none rest acc
      else if b.toNat = 60 then msgIdsFrom 0 (some [b]) rest acc else msgIdsFrom 0 none rest acc := by
  simp only [msgIdsFrom, beq_byte, decide_eq_true_eq]; rfl

theorem ids_deep (d : Nat) (b : BitVec 8) (rest : Bytes) (acc : List Bytes) :
    msgIdsFrom (d + 1) none (b :: rest) acc =
      if b.toNat = 92 then (match rest with | _ :: after => msgIdsFrom (d + 1) none after acc | [] => acc.reverse)
      else if b.toNat = 40 then msgIdsFrom (d + 2) none rest acc
      else if b.toNat = 41 then msgIdsFrom d none rest acc else msgIdsFrom (d + 1) none rest acc := by
  cases rest with
  | nil => simp only [DN.News.ArticleSpec.msgIdsFrom.eq_5, beq_byte, decide_eq_true_eq]; rfl
  | cons c after => simp only [DN.News.ArticleSpec.msgIdsFrom.eq_4, beq_byte, decide_eq_true_eq]; rfl

/-- **A turn keeps the invariant.** -/
theorem ids_step {idMax : Nat} {a : Bytes} {S E : Nat} {q : IdsSt} (hE : E ≤ a.length) (h : IdsInv idMax a S E q)
    (hi : q.i < E) : IdsInv idMax a S E (idsStep idMax a q) := by
  obtain ⟨hSi, -, hc1, hl1, hf1, hdi, hcl, hcs, acc, hids, hlong, hfound, hfirst, hcur⟩ := h
  have hia : q.i < a.length := by omega
  rw [seg_cons a hi hE] at hids
  have hb' : a[q.i]! = a[q.i] := getElem!_pos a q.i hia
  generalize hb : a[q.i]! = b at hids
  by_cases hc : q.cur = 0
  · rw [if_pos hc] at hids
    by_cases hd : q.dep = 0
    · rw [hd, ids_top] at hids
      by_cases h40 : b.toNat = 40
      · rw [if_pos h40] at hids
        rw [show idsStep idMax a q = { q with i := q.i + 1, dep := 1 } by simp [idsStep, hc, hd, hb, h40]]
        unfold IdsInv; dsimp only
        exact ⟨by omega, by omega, hc1, hl1, hf1, by omega, by omega, by omega, acc, by rw [if_pos hc]; exact hids,
          hlong, hfound, hfirst, fun h => absurd hc h⟩
      rw [if_neg h40] at hids
      by_cases h60 : b.toNat = 60
      · rw [if_pos h60] at hids
        rw [show idsStep idMax a q = { q with i := q.i + 1, cur := 1, cs := q.i, cl := 1 } by
          simp [idsStep, hc, hd, hb, h60]]
        unfold IdsInv; dsimp only
        refine ⟨by omega, by omega, by decide, hl1, hf1, by omega, by omega, by omega, acc, ?_, hlong, hfound, hfirst,
          fun _ => ⟨hd, hSi, by omega, by omega⟩⟩
        rw [hids, hd, seg_succ a (Nat.le_refl _) hia, DN.News.ArticleLines.seg_self, List.nil_append, ← hb', hb]
        rfl
      rw [if_neg h60] at hids
      rw [show idsStep idMax a q = { q with i := q.i + 1 } by simp [idsStep, hc, hd, hb, h40, h60]]
      unfold IdsInv; dsimp only
      exact ⟨by omega, by omega, hc1, hl1, hf1, by omega, by omega, by omega, acc,
        by rw [if_pos hc, hd]; exact hids, hlong, hfound, hfirst, fun h => absurd hc h⟩
    obtain ⟨d, hd'⟩ : ∃ d, q.dep = d + 1 := ⟨q.dep - 1, by omega⟩
    rw [hd', ids_deep] at hids
    by_cases h92 : b.toNat = 92
    · rw [if_pos h92] at hids
      rw [show idsStep idMax a q = { q with i := q.i + 2 } by simp [idsStep, hc, hd, hb, h92]]
      unfold IdsInv; dsimp only
      refine ⟨by omega, by omega, hc1, hl1, hf1, by omega, by omega, by omega, acc, ?_, hlong, hfound, hfirst,
        fun h => absurd hc h⟩
      rw [if_pos hc, hd', hids]
      by_cases h1 : q.i + 1 < E
      · rw [seg_cons a h1 hE]
      · rw [seg_over a (show E ≤ q.i + 1 by omega), seg_over a (show E ≤ q.i + 2 by omega)]
        unfold msgIdsFrom; rfl
    rw [if_neg h92] at hids
    by_cases h40 : b.toNat = 40
    · rw [if_pos h40] at hids
      rw [show idsStep idMax a q = { q with i := q.i + 1, dep := q.dep + 1 } by simp [idsStep, hc, hd, hb, h40]]
      unfold IdsInv; dsimp only
      exact ⟨by omega, by omega, hc1, hl1, hf1, by omega, by omega, by omega, acc,
        by rw [if_pos hc, hd']; exact hids, hlong, hfound, hfirst, fun h => absurd hc h⟩
    rw [if_neg h40] at hids
    by_cases h41 : b.toNat = 41
    · rw [if_pos h41] at hids
      rw [show idsStep idMax a q = { q with i := q.i + 1, dep := q.dep - 1 } by
        simp [idsStep, hc, hd, hb, h41]]
      unfold IdsInv; dsimp only
      exact ⟨by omega, by omega, hc1, hl1, hf1, by omega, by omega, by omega, acc,
        by rw [if_pos hc, hd', Nat.add_sub_cancel]; exact hids, hlong, hfound, hfirst, fun h => absurd hc h⟩
    rw [if_neg h41] at hids
    rw [show idsStep idMax a q = { q with i := q.i + 1 } by simp [idsStep, hc, hd, hb, h92, h40, h41]]
    unfold IdsInv; dsimp only
    exact ⟨by omega, by omega, hc1, hl1, hf1, by omega, by omega, by omega, acc,
      by rw [if_pos hc, hd']; exact hids, hlong, hfound, hfirst, fun h => absurd hc h⟩
  · obtain ⟨hd0, hScs, hcsi, hcleq⟩ := hcur hc
    rw [if_neg hc, ids_cur] at hids
    have hnew : (b :: (seg a q.cs q.i).reverse).reverse = seg a q.cs (q.i + 1) := by
      rw [List.reverse_cons, List.reverse_reverse, seg_succ a (by omega) hia, ← hb', hb]
    have hlen : (seg a q.cs (q.i + 1)).length = q.cl + 1 := by rw [seg_length a (by omega) (by omega)]; omega
    by_cases h62 : b.toNat = 62
    · rw [if_pos h62, hnew] at hids
      by_cases hf : q.found = 0
      · have hacc : acc = [] := hfound.1 hf
        subst hacc
        rw [show idsStep idMax a q = { q with
            i := q.i + 1, cur := 0, cl := q.cl + 1, long := (if idMax < q.cl + 1 then 1 else q.long), found := 1
            w1 := BitVec.ofNat 64 q.cs, w2 := BitVec.ofNat 64 (q.cl + 1) } by simp [idsStep, hc, hb, h62, hf]]
        unfold IdsInv; dsimp only
        refine ⟨by omega, by omega, by decide, ?_, by decide, by omega, by omega, by omega,
          [seg a q.cs (q.i + 1)], by rw [hids, hd0]; rfl, ?_, by simp, ?_, fun h => absurd rfl h⟩
        · split <;> omega
        · simp only [List.any_cons, List.any_nil, Bool.or_false, hlen, gt_iff_lt, decide_eq_true_eq]
          have : q.long = 0 := by simpa using hlong
          by_cases hm : idMax < q.cl + 1 <;> simp [hm, this]
        · refine ⟨q.cs, hScs, ?_, ?_, rfl, by rw [hlen]⟩
          · rw [hlen]; omega
          · rw [hlen, show q.cs + (q.cl + 1) = q.i + 1 by omega]
      · have hacc : acc ≠ [] := fun e => hf (hfound.2 e)
        rw [show idsStep idMax a q = { q with
            i := q.i + 1, cur := 0, cl := q.cl + 1, long := (if idMax < q.cl + 1 then 1 else q.long) } by
          simp [idsStep, hc, hb, h62, hf]]
        unfold IdsInv; dsimp only
        refine ⟨by omega, by omega, by decide, ?_, hf1, by omega, by omega, by omega,
          seg a q.cs (q.i + 1) :: acc, by rw [hids, hd0]; rfl, ?_, ?_, ?_, fun h => absurd rfl h⟩
        · split <;> omega
        · simp only [List.any_cons, hlen, gt_iff_lt]
          rw [hlong]
          by_cases hm : idMax < q.cl + 1 <;> by_cases ha : (acc.any fun x => decide (x.length > idMax)) = true <;>
            simp [hm, ha]
        · simp [hf]
        · rw [List.reverse_cons, idsFirst_snoc (by simpa using hacc)]; exact hfirst
    · rw [if_neg h62] at hids
      rw [show idsStep idMax a q = { q with i := q.i + 1, cl := q.cl + 1 } by simp [idsStep, hc, hb, h62]]
      unfold IdsInv; dsimp only
      refine ⟨by omega, by omega, hc1, hl1, hf1, by omega, by omega, by omega, acc, ?_, hlong, hfound, hfirst,
        fun _ => ⟨hd0, hScs, by omega, by omega⟩⟩
      rw [if_neg hc, hids, ← hnew, List.reverse_reverse]

/-! ### The program -/

theorem bw_t {P : Prop} [Decidable P] (h : P) : bw (decide P) = bw true := by rw [decide_eq_true h]
theorem bw_f {P : Prop} [Decidable P] (h : ¬P) : bw (decide P) = bw false := by rw [decide_eq_false h]

/-- A branch on a condition known true. -/
theorem frag_ifT (o : Oracle σ) {c : Syntax.PExpr} {C : PancakeExp} (hc : Lower.lowerExp c = some C)
    {t e : List Syntax.PStmt} (hlt : LowKK t) (hle : LowKK e) (hdt : declared t = []) (hde : declared e = [])
    {P Q : Assn σ} (hQ : Safe.ClockFree Q) (hv : ∀ u, P u → eval u C = some (bw true)) (ht : Frag o t P Q) :
    Frag o [.ite c t e] P Q :=
  DN.News.ScanRun.frag_if o hc hlt hle hdt hde hQ hv (fun _ => ht) fun h => absurd h (by decide)

/-- A branch on a condition known false. -/
theorem frag_ifF (o : Oracle σ) {c : Syntax.PExpr} {C : PancakeExp} (hc : Lower.lowerExp c = some C)
    {t e : List Syntax.PStmt} (hlt : LowKK t) (hle : LowKK e) (hdt : declared t = []) (hde : declared e = [])
    {P Q : Assn σ} (hQ : Safe.ClockFree Q) (hv : ∀ u, P u → eval u C = some (bw false)) (he : Frag o e P Q) :
    Frag o [.ite c t e] P Q :=
  DN.News.ScanRun.frag_if o hc hlt hle hdt hde hQ hv (fun h => absurd h (by decide)) fun _ => he

/-- `artMsgIds`'s locals in its loop, the byte read in front in its body. -/
def idsL (S E : Nat) (A : Word) (q : IdsSt) : List (String × Value) :=
  [("found", BitVec.ofNat 64 q.found), ("long", BitVec.ofNat 64 q.long), ("cl", BitVec.ofNat 64 q.cl),
   ("cs", BitVec.ofNat 64 q.cs), ("cur", BitVec.ofNat 64 q.cur), ("dep", BitVec.ofNat 64 q.dep),
   ("i", BitVec.ofNat 64 q.i), ("a", A), ("s", BitVec.ofNat 64 S), ("e", BitVec.ofNat 64 E)]

theorem runF_idsL {s0 u : PancakeState σ} {l : List (String × Value)} {F : (Word → Word) → Prop}
    (h : RunF s0 l F u) {S E : Nat} {A : Word} {q : IdsSt}
    (h1 : l.lookup "found" = some (BitVec.ofNat 64 q.found)) (h2 : l.lookup "long" = some (BitVec.ofNat 64 q.long))
    (h3 : l.lookup "cl" = some (BitVec.ofNat 64 q.cl)) (h4 : l.lookup "cs" = some (BitVec.ofNat 64 q.cs))
    (h5 : l.lookup "cur" = some (BitVec.ofNat 64 q.cur)) (h6 : l.lookup "dep" = some (BitVec.ofNat 64 q.dep))
    (h7 : l.lookup "i" = some (BitVec.ofNat 64 q.i)) (h8 : l.lookup "a" = some A)
    (h9 : l.lookup "s" = some (BitVec.ofNat 64 S)) (h10 : l.lookup "e" = some (BitVec.ofNat 64 E)) :
    RunF s0 (idsL S E A q) F u :=
  ⟨⟨fun p hp => by
    simp only [idsL, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first | exact vals_lookup h.1.vals h1 | exact vals_lookup h.1.vals h2 | exact vals_lookup h.1.vals h3 |
      exact vals_lookup h.1.vals h4 | exact vals_lookup h.1.vals h5 | exact vals_lookup h.1.vals h6 |
      exact vals_lookup h.1.vals h7 | exact vals_lookup h.1.vals h8 | exact vals_lookup h.1.vals h9 |
      exact vals_lookup h.1.vals h10,
    h.1.memaddrs, h.1.base, h.1.code, h.1.be⟩, h.2⟩

/-- The body's locals read off another list, the byte read in front. -/
theorem runF_idsB {s0 u : PancakeState σ} {l : List (String × Value)} {F : (Word → Word) → Prop}
    (h : RunF s0 l F u) {S E : Nat} {A : Word} {q : IdsSt} {vb : Value} (hb : l.lookup "b" = some vb := by rfl)
    (h1 : l.lookup "found" = some (BitVec.ofNat 64 q.found) := by rfl)
    (h2 : l.lookup "long" = some (BitVec.ofNat 64 q.long) := by rfl)
    (h3 : l.lookup "cl" = some (BitVec.ofNat 64 q.cl) := by rfl)
    (h4 : l.lookup "cs" = some (BitVec.ofNat 64 q.cs) := by rfl)
    (h5 : l.lookup "cur" = some (BitVec.ofNat 64 q.cur) := by rfl)
    (h6 : l.lookup "dep" = some (BitVec.ofNat 64 q.dep) := by rfl)
    (h7 : l.lookup "i" = some (BitVec.ofNat 64 q.i) := by rfl) (h8 : l.lookup "a" = some A := by rfl)
    (h9 : l.lookup "s" = some (BitVec.ofNat 64 S) := by rfl) (h10 : l.lookup "e" = some (BitVec.ofNat 64 E) := by rfl) :
    RunF s0 (("b", vb) :: idsL S E A q) F u :=
  runF_push h hb (runF_idsL h h1 h2 h3 h4 h5 h6 h7 h8 h9 h10)

/-- The memory in `artMsgIds`'s loop: the first identifier's words. -/
def idsMem (A : Word) (m0 : Word → Word) (q : IdsSt) : Word → Word :=
  upd (upd m0 (at_ A ArticleProg.xMsgS) q.w1) (at_ A ArticleProg.xMsgL) q.w2

theorem idsMem_store (A : Word) (m0 : Word → Word) (q : IdsSt) (w1 w2 : Word) :
    upd (upd (idsMem A m0 q) (at_ A ArticleProg.xMsgS) w1) (at_ A ArticleProg.xMsgL) w2 =
      idsMem A m0 { q with w1 := w1, w2 := w2 } := by
  funext x; unfold idsMem upd
  by_cases h1 : x = at_ A ArticleProg.xMsgL <;> by_cases h2 : x = at_ A ArticleProg.xMsgS <;> simp [h1, h2]

theorem idsMem_input {A : Word} (hA8 : A.toNat % 8 = 0) {a : Bytes} (ha : a.length ≤ artMax) {m0 : Word → Word}
    {dm : Word → Bool} {be : Bool} (hin : InputAt m0 dm be A a) (q : IdsSt) : InputAt (idsMem A m0 q) dm be A a :=
  input_keep hA8 ha hin fun x hx => by
    have h23 := w_ge 23; have h24 := w_ge 24; have := X_lt; have := sets_le_X
    show upd (upd m0 (at_ A (ArticleProg.w 23)) q.w1) (at_ A (ArticleProg.w 24)) q.w2 (at_ A x) = m0 (at_ A x)
    rw [upd_ne _ (DN.News.ScanRun.at_ne (by omega) (w_lt64 (by decide)) (by omega)),
      upd_ne _ (DN.News.ScanRun.at_ne (by omega) (w_lt64 (by decide)) (by omega))]

/-- `artMsgIds`'s loop body. -/
def idsBody (idMax : Nat) : List Syntax.PStmt :=
  ArticleProg.readIn "b" "i" ++
  [.ite (Syntax.v "cur")
    [inc "cl",
     ArticleProg.ifs (Syntax.eEq (Syntax.v "b") (Syntax.n 62))
       [.assign "cur" (Syntax.n 0),
        ArticleProg.ifs (Syntax.eLt (Syntax.n idMax) (Syntax.v "cl")) [.assign "long" (Syntax.n 1)],
        ArticleProg.ifs (Syntax.eEq (Syntax.v "found") (Syntax.n 0))
          [ArticleProg.setW ArticleProg.xMsgS (Syntax.v "cs"), ArticleProg.setW ArticleProg.xMsgL (Syntax.v "cl"),
           .assign "found" (Syntax.n 1)]],
     inc "i"]
    [.ite (Syntax.eEq (Syntax.v "dep") (Syntax.n 0))
      [.ite (Syntax.eEq (Syntax.v "b") (Syntax.n 40)) [.assign "dep" (Syntax.n 1)]
         [ArticleProg.ifs (Syntax.eEq (Syntax.v "b") (Syntax.n 60))
           [.assign "cur" (Syntax.n 1), .assign "cs" (Syntax.v "i"), .assign "cl" (Syntax.n 1)]],
       inc "i"]
      [.ite (Syntax.eAnd (Syntax.eEq (Syntax.v "b") (Syntax.n 92)) (Syntax.n 1))
         [.assign "i" (Syntax.eAdd (Syntax.v "i") (Syntax.n 2))]
         [.ite (Syntax.eEq (Syntax.v "b") (Syntax.n 40)) [inc "dep"]
            [ArticleProg.ifs (Syntax.eEq (Syntax.v "b") (Syntax.n 41))
              [.assign "dep" (Syntax.eSub (Syntax.v "dep") (Syntax.n 1))]],
          inc "i"]]]]

theorem artMsgIds_body (r : ArticleSpec.Rules) : guardL (ArticleProg.artMsgIds r .none).body =
    [areaAt ArticleProg.ofs, ArticleProg.setW ArticleProg.xMsgS ArticleProg.neg1,
     ArticleProg.setW ArticleProg.xMsgL (Syntax.n 0), .dec "i" (Syntax.v "s"), .dec "dep" (Syntax.n 0),
     .dec "cur" (Syntax.n 0), .dec "cs" (Syntax.n 0), .dec "cl" (Syntax.n 0), .dec "long" (Syntax.n 0),
     .dec "found" (Syntax.n 0), .while (Syntax.eLt (Syntax.v "i") (Syntax.v "e")) (idsBody r.idMax),
     .ret (Syntax.v "long")] := rfl

/-- An assignment, the locals then read off as `l'`. -/
theorem set_to (o : Oracle σ) {s1 : PancakeState σ} {F : (Word → Word) → Prop} {l l' : List (String × Value)}
    {x : String} {e : Syntax.PExpr} {Ex : PancakeExp} (he : Lower.lowerExp e = some Ex) {w : Value}
    (hl : l.lookup x = some w) {v : Value} (hv : ∀ u, RunF s1 l F u → eval u Ex = some v)
    (hq : ∀ u, RunF s1 ((x, v) :: without x l) F u → RunF s1 l' F u) :
    Frag o [.assign x e] (RunF s1 l F) (RunF s1 l' F) :=
  frag_conseq (runF_set o he hl hv) (fun _ h => h) hq

section body
variable (o : Oracle σ) {s1 : PancakeState σ} {S E : Nat} {A : Word} {vb : Value} {F : (Word → Word) → Prop}

/-- An assignment in the body, the locals read off as those of `q'`. -/
theorem ids_set {q q' : IdsSt} {x : String} {e : Syntax.PExpr} {Ex : PancakeExp} (he : Lower.lowerExp e = some Ex)
    {w : Value} (hl : (("b", vb) :: idsL S E A q).lookup x = some w) {v : Value}
    (hv : ∀ u, RunF s1 (("b", vb) :: idsL S E A q) F u → eval u Ex = some v)
    (hq : ∀ u, RunF s1 ((x, v) :: without x (("b", vb) :: idsL S E A q)) F u →
      RunF s1 (("b", vb) :: idsL S E A q') F u) :
    Frag o [.assign x e] (RunF s1 (("b", vb) :: idsL S E A q) F) (RunF s1 (("b", vb) :: idsL S E A q') F) :=
  set_to o he hl hv hq

theorem ids_long {idMax : Nat} (hidm : idMax < 2 ^ 62) {q : IdsSt} (hcl : q.cl < 2 ^ 62) :
    Frag o [ArticleProg.ifs (Syntax.eLt (Syntax.n idMax) (Syntax.v "cl")) [.assign "long" (Syntax.n 1)]]
      (RunF s1 (("b", vb) :: idsL S E A q) F)
      (RunF s1 (("b", vb) :: idsL S E A { q with long := if idMax < q.cl then 1 else q.long }) F) := by
  have hv : ∀ u, RunF s1 (("b", vb) :: idsL S E A q) F u →
      eval u (.cmp .less (.const (BitVec.ofNat 64 idMax)) (.var "cl")) = some (bw (decide (idMax < q.cl))) :=
    fun u h => FramerCode.eval_lt (by omega) (by omega) rfl (ev_var (vals_lookup h.1.vals rfl))
  by_cases hm : idMax < q.cl
  · refine frag_ifT o rfl (lowK_any _ (k := .skip) rfl) lowKK_nil rfl rfl (runF_clock _ _ _)
      (fun u h => (hv u h).trans (by rw [bw_t hm])) ?_
    exact ids_set o rfl rfl (v := BitVec.ofNat 64 1) (fun _ _ => rfl) fun u h => by rw [if_pos hm]; exact runF_idsB h
  · refine frag_ifF o rfl (lowK_any _ (k := .skip) rfl) lowKK_nil rfl rfl (runF_clock _ _ _)
      (fun u h => (hv u h).trans (by rw [bw_f hm])) (frag_nil o fun u h => ?_)
    rw [if_neg hm]; exact h

/-- The first identifier's words, if none was found yet. -/
def fnd (q : IdsSt) : IdsSt :=
  if q.found = 0 then { q with found := 1, w1 := BitVec.ofNat 64 q.cs, w2 := BitVec.ofNat 64 q.cl } else q

/-- The first identifier's words written. -/
def wq (q : IdsSt) : IdsSt := { q with w1 := BitVec.ofNat 64 q.cs, w2 := BitVec.ofNat 64 q.cl }

theorem ids_found (hD : ArtDom A s1.memaddrs) {m0 : Word → Word} {q : IdsSt} (hf1 : q.found ≤ 1) :
    Frag o [ArticleProg.ifs (Syntax.eEq (Syntax.v "found") (Syntax.n 0))
        [ArticleProg.setW ArticleProg.xMsgS (Syntax.v "cs"), ArticleProg.setW ArticleProg.xMsgL (Syntax.v "cl"),
         .assign "found" (Syntax.n 1)]]
      (RunF s1 (("b", vb) :: idsL S E A q) (· = idsMem A m0 q))
      (RunF s1 (("b", vb) :: idsL S E A (fnd q)) (· = idsMem A m0 (fnd q))) := by
  have hv : ∀ u, RunF s1 (("b", vb) :: idsL S E A q) (· = idsMem A m0 q) u →
      eval u (.cmp .equal (.var "found") (.const (BitVec.ofNat 64 0))) = some (bw (decide (q.found = 0))) :=
    fun u h => FramerCode.eval_eq (by omega) (by decide) (ev_var (vals_lookup h.1.vals rfl)) rfl
  by_cases hf : q.found = 0
  · refine frag_ifT o rfl (lowK_any _ (k := .skip) rfl) lowKK_nil rfl rfl (runF_clock _ _ _)
      (fun u h => (hv u h).trans (by rw [bw_t hf])) ?_
    refine frag_append (xs := [_]) (runF_storeA o (atOffW_lower 23) rfl (y := ArticleProg.w 23)
      (artDom_w hD (by decide)) (fun u h => atA_eval (vals_lookup h.1.vals rfl)) (val := fun _ => BitVec.ofNat 64 q.cs)
      (fun u h => ev_var (vals_lookup h.1.vals rfl))
      (G := (· = upd (idsMem A m0 q) (at_ A ArticleProg.xMsgS) (BitVec.ofNat 64 q.cs))) fun m hm => by subst hm; rfl) ?_
    refine frag_append (xs := [_]) (runF_storeA o (atOffW_lower 24) rfl (y := ArticleProg.w 24)
      (artDom_w hD (by decide)) (fun u h => atA_eval (vals_lookup h.1.vals rfl)) (val := fun _ => BitVec.ofNat 64 q.cl)
      (fun u h => ev_var (vals_lookup h.1.vals rfl))
      (G := (· = idsMem A m0 (wq q))) fun m hm => by
        subst hm; exact idsMem_store A m0 q _ _) ?_
    refine frag_conseq (ids_set o (q := q) (q' := { wq q with found := 1 }) (F := (· = idsMem A m0 (wq q))) rfl rfl
      (v := BitVec.ofNat 64 1) (fun _ _ => rfl) fun u h => runF_idsB h) (fun _ h => h) fun u h => ?_
    unfold fnd; rw [if_pos hf]; exact h
  · refine frag_ifF o rfl (lowK_any _ (k := .skip) rfl) lowKK_nil rfl rfl (runF_clock _ _ _)
      (fun u h => (hv u h).trans (by rw [bw_f hf])) (frag_nil o fun u h => ?_)
    unfold fnd; rw [if_neg hf]; exact h

end body

/-- **A turn of the body is a step**: the locals and the memory those of `idsStep`. -/
theorem ids_body (o : Oracle σ) {idMax : Nat} (hidm : idMax < 2 ^ 62) {A : Word} {s1 : PancakeState σ}
    (hD : ArtDom A s1.memaddrs) {a : Bytes} {m0 : Word → Word}
    (hin : ∀ q, InputAt (idsMem A m0 q) s1.memaddrs s1.be A a) {S E : Nat} (hE : E ≤ a.length) (hEM : E ≤ artMax)
    {q : IdsSt} (hq : IdsInv idMax a S E q) (hi : q.i < E) :
    Frag o (idsBody idMax) (RunF s1 (idsL S E A q) (· = idsMem A m0 q))
      (RunF s1 (idsL S E A (idsStep idMax a q)) (· = idsMem A m0 (idsStep idMax a q))) := by
  obtain ⟨hSi, -, hc1, hl1, hf1, hdi, hcl, hcs, -⟩ := hq
  have hM := artMax_eq
  have hia : q.i < a.length := by omega
  have hbl : (a[q.i]!).toNat < 256 := (a[q.i]!).isLt
  refine frag_append (xs := [_, _]) (frag_append (xs := [_]) (kept_frag o (by decide) (runF_clock _ _ _) fun u h =>
    ⟨q.i, vals_lookup h.1.vals rfl, by omega⟩) (runF_dec o rfl rfl (v := BitVec.ofNat 64 (a[q.i]!).toNat) fun u h =>
      inByte_eval (input_run (hin q) h) (vals_lookup h.1.vals rfl) hia (vals_lookup h.1.vals rfl))) ?_
  refine frag_conseq (P0' := RunF s1 (("b", BitVec.ofNat 64 (a[q.i]!).toNat) :: idsL S E A (idsStep idMax a q))
    (· = idsMem A m0 (idsStep idMax a q))) ?_ (fun _ h => h)
    fun u h => runF_mono h (fun p hp => List.mem_cons_of_mem _ hp) fun _ e => e
  have evb : ∀ {q' : IdsSt} {G : (Word → Word) → Prop} (u : PancakeState σ),
      RunF s1 (("b", BitVec.ofNat 64 (a[q.i]!).toNat) :: idsL S E A q') G u → ∀ k, k < 2 ^ 64 →
      eval u (.cmp .equal (.var "b") (.const (BitVec.ofNat 64 k))) = some (bw (decide ((a[q.i]!).toNat = k))) :=
    fun u h k hk => FramerCode.eval_eq (by omega) hk (ev_var (vals_lookup h.1.vals rfl)) rfl
  by_cases hc : q.cur = 0
  · refine frag_ifF o rfl (lowK_any _ (k := .skip) rfl) (lowK_any _ (k := .skip) rfl) rfl rfl (runF_clock _ _ _)
      (fun u h => by rw [ev_var (vals_lookup h.1.vals rfl), hc]; rfl) ?_
    by_cases hd : q.dep = 0
    · refine frag_ifT o rfl (lowK_any _ (k := .skip) rfl) (lowK_any _ (k := .skip) rfl) rfl rfl (runF_clock _ _ _)
        (fun u h => (FramerCode.eval_eq (by omega) (by decide) (ev_var (vals_lookup h.1.vals rfl)) rfl).trans
          (by rw [bw_t hd])) ?_
      by_cases h40 : (a[q.i]!).toNat = 40
      · rw [show idsStep idMax a q = { q with i := q.i + 1, dep := 1 } by
        unfold idsStep; generalize (a[q.i]!).toNat = bt at *; simp [hc, hd, h40]]
        refine frag_append (xs := [_]) (frag_ifT o rfl (lowK_any _ (k := .skip) rfl) (lowK_any _ (k := .skip) rfl) rfl
          rfl (runF_clock _ _ _) (fun u h => (evb u h 40 (by decide)).trans (by rw [bw_t h40]))
          (ids_set o rfl rfl (q' := { q with dep := 1 }) (v := BitVec.ofNat 64 1) (fun _ _ => rfl)
            fun u h => runF_idsB h))
          ?_
        exact ids_set o rfl rfl (v := BitVec.ofNat 64 (q.i + 1)) (fun u h => ev_inc (vals_lookup h.1.vals rfl))
          fun u h => runF_idsB h
      refine frag_append (xs := [_]) (frag_ifF o rfl (lowK_any _ (k := .skip) rfl) (lowK_any _ (k := .skip) rfl) rfl
        rfl (runF_clock _ _ _) (fun u h => (evb u h 40 (by decide)).trans (by rw [bw_f h40])) (P := RunF s1 _ _)
        (Q := RunF s1 (("b", BitVec.ofNat 64 (a[q.i]!).toNat) :: idsL S E A
          (if (a[q.i]!).toNat = 60 then { q with cur := 1, cs := q.i, cl := 1 } else q)) (· = idsMem A m0 q)) ?_) ?_
      · by_cases h60 : (a[q.i]!).toNat = 60
        · refine frag_ifT o rfl (lowK_any _ (k := .skip) rfl) lowKK_nil rfl rfl (runF_clock _ _ _)
            (fun u h => (evb u h 60 (by decide)).trans (by rw [bw_t h60])) ?_
          refine frag_append (xs := [_]) (ids_set o rfl rfl (q' := { q with cur := 1 }) (v := BitVec.ofNat 64 1)
            (fun _ _ => rfl) fun u h => runF_idsB h) ?_
          refine frag_append (xs := [_]) (ids_set o rfl rfl (q' := { q with cur := 1, cs := q.i })
            (v := BitVec.ofNat 64 q.i) (fun u h => ev_var (vals_lookup h.1.vals rfl)) fun u h => runF_idsB h) ?_
          exact ids_set o rfl rfl (v := BitVec.ofNat 64 1) (fun _ _ => rfl) fun u h => by
            rw [if_pos h60]; exact runF_idsB h
        · refine frag_ifF o rfl (lowK_any _ (k := .skip) rfl) lowKK_nil rfl rfl (runF_clock _ _ _)
            (fun u h => (evb u h 60 (by decide)).trans (by rw [bw_f h60])) (frag_nil o fun u h => ?_)
          rw [if_neg h60]; exact h
      · by_cases h60 : (a[q.i]!).toNat = 60
        · rw [show idsStep idMax a q = { q with i := q.i + 1, cur := 1, cs := q.i, cl := 1 } by
            unfold idsStep; generalize (a[q.i]!).toNat = bt at *; simp [hc, hd, h60]]
          simp only [h60, if_true]
          exact ids_set o rfl rfl (v := BitVec.ofNat 64 (q.i + 1)) (fun u h => ev_inc (vals_lookup h.1.vals rfl))
            fun u h => runF_idsB h
        · rw [show idsStep idMax a q = { q with i := q.i + 1 } by
          unfold idsStep; generalize (a[q.i]!).toNat = bt at *; simp [hc, hd, h40, h60]]
          simp only [h60, if_false]
          exact ids_set o rfl rfl (v := BitVec.ofNat 64 (q.i + 1)) (fun u h => ev_inc (vals_lookup h.1.vals rfl))
            fun u h => runF_idsB h
    · refine frag_ifF o rfl (lowK_any _ (k := .skip) rfl) (lowK_any _ (k := .skip) rfl) rfl rfl (runF_clock _ _ _)
        (fun u h => (FramerCode.eval_eq (by omega) (by decide) (ev_var (vals_lookup h.1.vals rfl)) rfl).trans
          (by rw [bw_f hd])) ?_
      have ev92 : ∀ u, RunF s1 (("b", BitVec.ofNat 64 (a[q.i]!).toNat) :: idsL S E A q) (· = idsMem A m0 q) u →
          eval u (.op .and_ (.cmp .equal (.var "b") (.const (BitVec.ofNat 64 92))) (.const (BitVec.ofNat 64 1))) =
            some (bw (decide ((a[q.i]!).toNat = 92) && true)) :=
        fun u h => FramerCode.eval_and (evb u h 92 (by decide)) rfl
      by_cases h92 : (a[q.i]!).toNat = 92
      · rw [show idsStep idMax a q = { q with i := q.i + 2 } by
        unfold idsStep; generalize (a[q.i]!).toNat = bt at *; simp [hc, hd, h92]]
        refine frag_ifT o rfl (lowK_any _ (k := .skip) rfl) (lowK_any _ (k := .skip) rfl) rfl rfl (runF_clock _ _ _)
          (fun u h => (ev92 u h).trans (by rw [decide_eq_true h92]; rfl)) ?_
        exact ids_set o rfl rfl (v := BitVec.ofNat 64 (q.i + 2)) (fun u h => ev_inc (vals_lookup h.1.vals rfl))
          fun u h => runF_idsB h
      refine frag_ifF o rfl (lowK_any _ (k := .skip) rfl) (lowK_any _ (k := .skip) rfl) rfl rfl (runF_clock _ _ _)
        (fun u h => (ev92 u h).trans (by rw [decide_eq_false h92]; rfl)) ?_
      by_cases h40 : (a[q.i]!).toNat = 40
      · rw [show idsStep idMax a q = { q with i := q.i + 1, dep := q.dep + 1 } by
        unfold idsStep; generalize (a[q.i]!).toNat = bt at *; simp [hc, hd, h40]]
        refine frag_append (xs := [_]) (frag_ifT o rfl (lowK_any _ (k := .skip) rfl) (lowK_any _ (k := .skip) rfl) rfl
          rfl (runF_clock _ _ _) (fun u h => (evb u h 40 (by decide)).trans (by rw [bw_t h40]))
          (ids_set o rfl rfl (q' := { q with dep := q.dep + 1 }) (v := BitVec.ofNat 64 (q.dep + 1))
            (fun u h => ev_inc (vals_lookup h.1.vals rfl)) fun u h => runF_idsB h)) ?_
        exact ids_set o rfl rfl (v := BitVec.ofNat 64 (q.i + 1)) (fun u h => ev_inc (vals_lookup h.1.vals rfl))
          fun u h => runF_idsB h
      by_cases h41 : (a[q.i]!).toNat = 41
      · rw [show idsStep idMax a q = { q with i := q.i + 1, dep := q.dep - 1 } by
        unfold idsStep; generalize (a[q.i]!).toNat = bt at *; simp [hc, hd, h41]]
        refine frag_append (xs := [_]) (frag_ifF o rfl (lowK_any _ (k := .skip) rfl) (lowK_any _ (k := .skip) rfl) rfl
          rfl (runF_clock _ _ _) (fun u h => (evb u h 40 (by decide)).trans (by rw [bw_f h40]))
          (frag_ifT o rfl (lowK_any _ (k := .skip) rfl) lowKK_nil rfl rfl (runF_clock _ _ _)
            (fun u h => (evb u h 41 (by decide)).trans (by rw [bw_t h41]))
            (ids_set o rfl rfl (q' := { q with dep := q.dep - 1 }) (v := BitVec.ofNat 64 (q.dep - 1))
              (fun u h => DN.News.ArticleRun.ev_sub (y := 1)
                (by rw [show 1 + (q.dep - 1) = q.dep by omega]; exact ev_var (vals_lookup h.1.vals rfl)) rfl)
              fun u h => runF_idsB h))) ?_
        exact ids_set o rfl rfl (v := BitVec.ofNat 64 (q.i + 1)) (fun u h => ev_inc (vals_lookup h.1.vals rfl))
          fun u h => runF_idsB h
      rw [show idsStep idMax a q = { q with i := q.i + 1 } by
        unfold idsStep; generalize (a[q.i]!).toNat = bt at *; simp [hc, hd, h92, h40, h41]]
      refine frag_append (xs := [_]) (frag_ifF o rfl (lowK_any _ (k := .skip) rfl) (lowK_any _ (k := .skip) rfl) rfl
        rfl (runF_clock _ _ _) (fun u h => (evb u h 40 (by decide)).trans (by rw [bw_f h40]))
        (frag_ifF o rfl (lowK_any _ (k := .skip) rfl) lowKK_nil rfl rfl (runF_clock _ _ _)
          (fun u h => (evb u h 41 (by decide)).trans (by rw [bw_f h41])) (frag_nil o fun _ h => h))) ?_
      exact ids_set o rfl rfl (v := BitVec.ofNat 64 (q.i + 1)) (fun u h => ev_inc (vals_lookup h.1.vals rfl))
        fun u h => runF_idsB h
  · have hc' : q.cur = 1 := by omega
    refine frag_ifT o rfl (lowK_any _ (k := .skip) rfl) (lowK_any _ (k := .skip) rfl) rfl rfl (runF_clock _ _ _)
      (fun u h => by rw [ev_var (vals_lookup h.1.vals rfl), hc']; rfl) ?_
    refine frag_append (xs := [_]) (ids_set o rfl rfl (q' := { q with cl := q.cl + 1 })
      (v := BitVec.ofNat 64 (q.cl + 1)) (fun u h => ev_inc (vals_lookup h.1.vals rfl)) fun u h => runF_idsB h) ?_
    by_cases h62 : (a[q.i]!).toNat = 62
    · let q3 : IdsSt := { q with cl := q.cl + 1, cur := 0, long := if idMax < q.cl + 1 then 1 else q.long }
      refine frag_append (xs := [_]) (frag_ifT o rfl (lowK_any _ (k := .skip) rfl) lowKK_nil rfl rfl
        (runF_clock _ _ _) (fun u h => (evb u h 62 (by decide)).trans (by rw [bw_t h62]))
        (Q := RunF s1 (("b", BitVec.ofNat 64 (a[q.i]!).toNat) :: idsL S E A (fnd q3)) (· = idsMem A m0 (fnd q3)))
        (frag_append (xs := [_]) (ids_set o rfl rfl (q' := { q with cl := q.cl + 1, cur := 0 })
          (v := BitVec.ofNat 64 0) (fun _ _ => rfl) fun u h => runF_idsB h)
        (frag_append (xs := [_]) (ids_long o hidm (by dsimp only; omega)) (ids_found o hD (by dsimp only; omega))))) ?_
      have hstep : idsStep idMax a q = { fnd q3 with i := q.i + 1 } := by
        unfold idsStep; generalize (a[q.i]!).toNat = bt at *
        by_cases hf : q.found = 0 <;> simp [fnd, q3, hc, h62, hf]
      rw [hstep]
      exact ids_set o rfl rfl (v := BitVec.ofNat 64 (q.i + 1))
        (fun u h => by
          have : (fnd q3).i = q.i := by unfold fnd; split <;> rfl
          rw [← this]; exact ev_inc (vals_lookup h.1.vals rfl))
        fun u h => runF_idsB h
    · rw [show idsStep idMax a q = { q with i := q.i + 1, cl := q.cl + 1 } by
      unfold idsStep; generalize (a[q.i]!).toNat = bt at *; simp [hc, h62]]
      refine frag_append (xs := [_]) (frag_ifF o rfl (lowK_any _ (k := .skip) rfl) lowKK_nil rfl rfl
        (runF_clock _ _ _) (fun u h => (evb u h 62 (by decide)).trans (by rw [bw_f h62])) (frag_nil o fun _ h => h)) ?_
      exact ids_set o rfl rfl (v := BitVec.ofNat 64 (q.i + 1)) (fun u h => ev_inc (vals_lookup h.1.vals rfl))
        fun u h => runF_idsB h

/-- What `artMsgIds` gives back: 1 if an identifier is longer than the bound. The first one's place and length go in
`xMsgS` and `xMsgL`. -/
def IdsRet (idMax : Nat) (A : Word) (a : Bytes) (S E : Nat) (m0 : Word → Word) : Ret := fun v m =>
  v = bw ((msgIds (seg a S E)).any (·.length > idMax)) ∧ ∃ w1 w2,
    m = upd (upd m0 (at_ A ArticleProg.xMsgS) w1) (at_ A ArticleProg.xMsgL) w2 ∧
      IdsFirst a S E (msgIds (seg a S E)) w1 w2

theorem long_bw {idMax : Nat} {acc : List Bytes} :
    BitVec.ofNat 64 (if acc.any (·.length > idMax) then 1 else 0) = bw (acc.any (·.length > idMax)) := by
  split <;> rename_i h <;> simp only [h] <;> rfl

/-- **`artMsgIds` reads the message identifiers** from `S` to `E` as `msgIds` does, if it returns. -/
theorem artMsgIds_ok (o : Oracle σ) {r : ArticleSpec.Rules} (hidm : r.idMax < 2 ^ 62) {A : Word} {s1 : PancakeState σ}
    (hA : Area ArticleProg.ofs A s1) (hD : ArtDom A s1.memaddrs) {a : Bytes} (hlen : a.length ≤ artMax)
    (hin : InputAt s1.memory s1.memaddrs s1.be A a) {S E : Nat} (hSE : S ≤ E) (hE : E ≤ a.length)
    (hs : s1.locals "s" = some (BitVec.ofNat 64 S)) (he : s1.locals "e" = some (BitVec.ofNat 64 E)) :
    ∃ body, Lower.lower (gd (ArticleProg.artMsgIds r .none)) = some body ∧
      SafeR o (fun s => s = s1) body (IdsRet r.idMax A a S E s1.memory) fun _ => False := by
  have hM := artMax_eq
  have hEM : E ≤ artMax := by omega
  refine body_of ?_
  show FragR o _ (guardL (ArticleProg.artMsgIds r .none).body) _ _
  rw [artMsgIds_body]
  let L0 : List (String × Value) := [("a", A), ("s", BitVec.ofNat 64 S), ("e", BitVec.ofNat 64 E)]
  obtain ⟨EA, hEA⟩ := atOff_lower ArticleProg.ofs
  refine fragR_conseq (P0 := RunF s1 [("s", BitVec.ofNat 64 S), ("e", BitVec.ofNat 64 E)] (· = s1.memory))
    ?_ (entry_two hs he) fun _ h => h
  refine fragR_append (xs := [_]) (fragR_of (runF_dec o hEA rfl (v := A) fun u h => areaAt_eval hA h.1.base hEA)) ?_
  refine fragR_append (xs := [_]) (fragR_of (runF_storeA o (atOffW_lower 23) rfl (y := ArticleProg.w 23)
    (artDom_w hD (by decide)) (fun u h => atA_eval (vals_lookup h.1.vals rfl))
    (val := fun _ => BitVec.ofNat 64 (2 ^ 64 - 1)) (fun _ _ => rfl)
    (G := (· = upd s1.memory (at_ A ArticleProg.xMsgS) (BitVec.ofNat 64 (2 ^ 64 - 1)))) fun m hm => by
      subst hm; rfl)) ?_
  let q0 : IdsSt := ⟨S, 0, 0, 0, 0, 0, 0, BitVec.ofNat 64 (2 ^ 64 - 1), 0⟩
  refine fragR_append (xs := [_]) (fragR_of (runF_storeA o (atOffW_lower 24) rfl (y := ArticleProg.w 24)
    (artDom_w hD (by decide)) (fun u h => atA_eval (vals_lookup h.1.vals rfl)) (val := fun _ => BitVec.ofNat 64 0)
    (fun _ _ => rfl) (G := (· = idsMem A s1.memory q0)) fun m hm => by subst hm; rfl)) ?_
  refine fragR_append (xs := [_]) (fragR_of (runF_dec o rfl rfl (v := BitVec.ofNat 64 S) fun u h =>
    ev_var (vals_lookup h.1.vals rfl))) ?_
  refine fragR_append (xs := [_]) (fragR_of (runF_dec o rfl rfl (v := BitVec.ofNat 64 0) fun _ _ => rfl)) ?_
  refine fragR_append (xs := [_]) (fragR_of (runF_dec o rfl rfl (v := BitVec.ofNat 64 0) fun _ _ => rfl)) ?_
  refine fragR_append (xs := [_]) (fragR_of (runF_dec o rfl rfl (v := BitVec.ofNat 64 0) fun _ _ => rfl)) ?_
  refine fragR_append (xs := [_]) (fragR_of (runF_dec o rfl rfl (v := BitVec.ofNat 64 0) fun _ _ => rfl)) ?_
  refine fragR_append (xs := [_]) (fragR_of (runF_dec o rfl rfl (v := BitVec.ofNat 64 0) fun _ _ => rfl)) ?_
  refine fragR_append (xs := [_]) (fragR_of (runF_dec o rfl rfl (v := BitVec.ofNat 64 0) fun _ _ => rfl)) ?_
  let I : Assn σ := fun u => ∃ q, RunF s1 (idsL S E A q) (· = idsMem A s1.memory q) u ∧ IdsInv r.idMax a S E q
  have hIc : Safe.ClockFree I := fun u k ⟨q, h, hv⟩ => ⟨q, runF_clock _ _ _ u k h, hv⟩
  have hcond : ∀ u q, RunF s1 (idsL S E A q) (· = idsMem A s1.memory q) u → IdsInv r.idMax a S E q →
      eval u (.cmp .less (.var "i") (.var "e")) = some (bw (decide (q.i < E))) := fun u q h hq =>
    FramerCode.eval_lt (by have := hq.2.1; omega) (by omega) (ev_var (vals_lookup h.1.vals rfl))
      (ev_var (vals_lookup h.1.vals rfl))
  have hlow : LowKK (idsBody r.idMax) := lowK_any _ (k := .skip) rfl
  refine fragR_append (xs := [_]) (fragR_of (frag_conseq (frag_while o rfl hlow hIc
    (fun u z v ⟨q, h, hv⟩ hz => by
      change z ∈ ["b"] at hz
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hz; subst hz
      exact ⟨q, runF_restore h rfl v, hv⟩) (fun u ⟨q, h, hv⟩ => ⟨_, hcond u q h hv⟩) ?_)
    (fun u h => ⟨q0, h, ids_init r.idMax a hSE⟩) fun _ h => h)) ?_
  · refine frag_conseq (P0 := fun u => ∃ q, (fun q u => RunF s1 (idsL S E A q) (· = idsMem A s1.memory q) u ∧
      IdsInv r.idMax a S E q ∧ q.i < E) q u) (frag_exists hlow fun q => ?_)
      (fun u ⟨⟨q, h, hv⟩, h0⟩ => ⟨q, h, hv, by
        rw [hcond u q h hv] at h0; exact of_decide_eq_true (bw_ne0 h0)⟩) fun _ h => h
    refine frag_pure (IdsInv r.idMax a S E q ∧ q.i < E) (fun u h => h.2) hlow fun ⟨hq, hi⟩ => ?_
    exact frag_conseq (ids_body o hidm hD (idsMem_input hA.hA hlen hin) hE hEM hq hi) (fun u h => h.1)
      fun u h => ⟨_, h, ids_step hE hq hi⟩
  refine fragR_ret o rfl fun u ⟨⟨q, h, hq⟩, h0⟩ => ⟨_, ev_var (vals_lookup h.1.vals rfl), ?_⟩
  rw [hcond u q h hq] at h0
  have hge : E ≤ q.i := by have := of_decide_eq_false (bw_eq0 h0); omega
  obtain ⟨-, -, -, -, -, -, -, -, acc, hids, hlong, -, hfirst, -⟩ := hq
  rw [seg_over a hge, DN.News.ArticleSpec.msgIdsFrom.eq_1] at hids
  refine ⟨?_, q.w1, q.w2, h.2, by rw [hids]; exact hfirst⟩
  rw [hids, List.any_reverse, hlong]; exact long_bw

/-! ## The date of a Received field -/

open DN.News.ArticleSpec (receivedDate BACKSLASH LPAREN RPAREN DQUOTE RBRACKET LBRACKET SEMICOLON)

/-- `artReceived`'s loop state: the place, whether in a quoted string (1) or a domain literal (2), the comment depth. -/
structure RecvSt where
  i : Nat
  mode : Nat
  dep : Nat

/-- One turn of `artReceived`'s loop that does not return, on byte `b`. -/
def recvStepB (q : RecvSt) (b : Nat) : RecvSt :=
  if (q.mode = 1 ∨ 0 < q.dep) ∧ b = 92 then { q with i := q.i + 2 }
  else if 0 < q.dep then
    if b = 40 then { q with i := q.i + 1, dep := q.dep + 1 }
    else if b = 41 then { q with i := q.i + 1, dep := q.dep - 1 } else { q with i := q.i + 1 }
  else if q.mode = 1 then if b = 34 then { q with i := q.i + 1, mode := 0 } else { q with i := q.i + 1 }
  else if q.mode = 2 then if b = 93 then { q with i := q.i + 1, mode := 0 } else { q with i := q.i + 1 }
  else if b = 34 then { q with i := q.i + 1, mode := 1 }
  else if b = 91 then { q with i := q.i + 1, mode := 2 }
  else if b = 40 then { q with i := q.i + 1, dep := 1 }
  else { q with i := q.i + 1 }

/-- One turn of `artReceived`'s loop that does not return. -/
def recvStep (a : Bytes) (q : RecvSt) : RecvSt := recvStepB q (a[q.i]!).toNat

/-- What `artReceived`'s loop keeps: the date is that of the bytes left, read from its state. -/
def RecvInv (a : Bytes) (S E : Nat) (q : RecvSt) : Prop :=
  S ≤ q.i ∧ q.i ≤ E + 1 ∧ q.mode ≤ 2 ∧ q.dep ≤ q.i ∧ (q.mode ≠ 0 → q.dep = 0) ∧
    receivedDate 0 0 (seg a S E) = receivedDate q.mode q.dep (seg a q.i E)

theorem recv_cons (mode depth : Nat) (b : BitVec 8) (rest : Bytes) :
    receivedDate mode depth (b :: rest) =
      if ((mode == 1 || decide (depth > 0)) && b == BACKSLASH) = true then
        (match rest with | _ :: after => receivedDate mode depth after | [] => [])
      else if depth > 0 then
        receivedDate mode (if (b == LPAREN) = true then depth + 1 else if (b == RPAREN) = true then depth - 1
          else depth) rest
      else if (mode == 1) = true then receivedDate (if (b == DQUOTE) = true then 0 else 1) 0 rest
      else if (mode == 2) = true then receivedDate (if (b == RBRACKET) = true then 0 else 2) 0 rest
      else if (b == DQUOTE) = true then receivedDate 1 0 rest
      else if (b == LBRACKET) = true then receivedDate 2 0 rest
      else if (b == LPAREN) = true then receivedDate 0 1 rest
      else if (b == SEMICOLON) = true then rest else receivedDate 0 0 rest := by
  cases rest with
  | nil => rw [DN.News.ArticleSpec.receivedDate.eq_3]
  | cons c d => rw [DN.News.ArticleSpec.receivedDate.eq_2]

/-- A `;` outside strings, literals and comments: the date is what follows it. -/
theorem recv_semi {a : Bytes} {S E : Nat} {q : RecvSt} (hE : E ≤ a.length) (h : RecvInv a S E q) (hi : q.i < E)
    (hm : q.mode = 0) (hd : q.dep = 0) (hb : (a[q.i]!).toNat = 59) :
    receivedDate 0 0 (seg a S E) = seg a (q.i + 1) E := by
  obtain ⟨-, -, -, -, -, hr⟩ := h
  rw [hr, seg_cons a hi hE, recv_cons, hm, hd]
  generalize a[q.i]! = b at hb
  simp [beq_byte, hb, BACKSLASH, LPAREN, DQUOTE, LBRACKET, SEMICOLON]

/-- **A turn that does not return keeps the invariant.** -/
theorem recv_step {a : Bytes} {S E : Nat} {q : RecvSt} (hE : E ≤ a.length) (h : RecvInv a S E q) (hi : q.i < E)
    (hno : ¬(q.mode = 0 ∧ q.dep = 0 ∧ (a[q.i]!).toNat = 59)) : RecvInv a S E (recvStep a q) := by
  obtain ⟨hSi, -, hm2, hdi, hmd, hr⟩ := h
  rw [seg_cons a hi hE, recv_cons] at hr
  unfold recvStep recvStepB
  generalize hb : a[q.i]! = b at hr hno ⊢
  have hbl : b.toNat < 256 := b.isLt
  simp only [beq_byte, BACKSLASH, LPAREN, RPAREN, DQUOTE, RBRACKET, LBRACKET, SEMICOLON, BitVec.toNat_ofNat,
    Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq, gt_iff_lt] at hr
  by_cases h92 : (q.mode = 1 ∨ 0 < q.dep) ∧ b.toNat = 92
  · rw [if_pos h92] at hr ⊢
    unfold RecvInv; dsimp only
    refine ⟨by omega, by omega, hm2, by omega, hmd, ?_⟩
    rw [hr]
    by_cases h1 : q.i + 1 < E
    · rw [seg_cons a h1 hE]
    · rw [seg_over a (show E ≤ q.i + 1 by omega), seg_over a (show E ≤ q.i + 2 by omega)]
      rfl
  rw [if_neg h92] at hr ⊢
  by_cases hd : 0 < q.dep
  · have hm0 : q.mode = 0 := Decidable.byContradiction fun hne => absurd (hmd hne) (by omega)
    rw [if_pos hd] at hr ⊢
    by_cases h40 : b.toNat = 40
    · rw [if_pos h40] at hr ⊢
      unfold RecvInv; dsimp only
      exact ⟨by omega, by omega, hm2, by omega, fun h => absurd hm0 h, hr⟩
    rw [if_neg h40] at hr ⊢
    by_cases h41 : b.toNat = 41
    · rw [if_pos h41] at hr ⊢
      unfold RecvInv; dsimp only
      exact ⟨by omega, by omega, hm2, by omega, fun h => absurd hm0 h, hr⟩
    rw [if_neg h41] at hr ⊢
    unfold RecvInv; dsimp only
    exact ⟨by omega, by omega, hm2, by omega, fun h => absurd hm0 h, hr⟩
  rw [if_neg hd] at hr ⊢
  have hd0 : q.dep = 0 := by omega
  by_cases hm1 : q.mode = 1
  · rw [if_pos hm1] at hr ⊢
    by_cases h34 : b.toNat = 34
    · rw [if_pos h34] at hr ⊢
      unfold RecvInv; dsimp only
      exact ⟨by omega, by omega, by decide, by omega, fun h => absurd rfl h, by rw [hr, hd0]⟩
    rw [if_neg h34] at hr ⊢
    unfold RecvInv; dsimp only
    exact ⟨by omega, by omega, hm2, by omega, fun _ => hd0, by rw [hr, hd0, hm1]⟩
  rw [if_neg hm1] at hr ⊢
  by_cases hm2' : q.mode = 2
  · rw [if_pos hm2'] at hr ⊢
    by_cases h93 : b.toNat = 93
    · rw [if_pos h93] at hr ⊢
      unfold RecvInv; dsimp only
      exact ⟨by omega, by omega, by decide, by omega, fun h => absurd rfl h, by rw [hr, hd0]⟩
    rw [if_neg h93] at hr ⊢
    unfold RecvInv; dsimp only
    exact ⟨by omega, by omega, hm2, by omega, fun _ => hd0, by rw [hr, hd0, hm2']⟩
  rw [if_neg hm2'] at hr ⊢
  have hm0 : q.mode = 0 := by omega
  by_cases h34 : b.toNat = 34
  · rw [if_pos h34] at hr ⊢
    unfold RecvInv; dsimp only
    exact ⟨by omega, by omega, by decide, by omega, fun _ => hd0, by rw [hd0]; exact hr⟩
  rw [if_neg h34] at hr ⊢
  by_cases h91 : b.toNat = 91
  · rw [if_pos h91] at hr ⊢
    unfold RecvInv; dsimp only
    exact ⟨by omega, by omega, by decide, by omega, fun _ => hd0, by rw [hd0]; exact hr⟩
  rw [if_neg h91] at hr ⊢
  by_cases h40 : b.toNat = 40
  · rw [if_pos h40] at hr ⊢
    unfold RecvInv; dsimp only
    exact ⟨by omega, by omega, by omega, by omega, fun h => absurd hm0 h, by rw [hm0]; exact hr⟩
  rw [if_neg h40] at hr ⊢
  have h59 : b.toNat ≠ 59 := fun e => hno ⟨hm0, hd0, e⟩
  rw [if_neg h59] at hr
  unfold RecvInv; dsimp only
  exact ⟨by omega, by omega, hm2, by omega, fun h => absurd hm0 h, by rw [hr, hm0, hd0]⟩

/-! ### The program -/

/-- A branch that may return, on a condition known true. -/
theorem fragR_ifT (o : Oracle σ) {R : Ret} {c : Syntax.PExpr} {C : PancakeExp} (hc : Lower.lowerExp c = some C)
    {t e : List Syntax.PStmt} (hlt : LowKK t) (hle : LowKK e) (hdt : declared t = []) (hde : declared e = [])
    {P Q : Assn σ} (hQ : Safe.ClockFree Q) (hv : ∀ u, P u → eval u C = some (bw true)) (ht : FragR o R t P Q) :
    FragR o R [.ite c t e] P Q :=
  fragR_if o hc hlt hle hQ (noDecl _ hdt) (noDecl _ hde) hv (fun _ => ht) fun h => absurd h (by decide)

/-- A branch that may return, on a condition known false. -/
theorem fragR_ifF (o : Oracle σ) {R : Ret} {c : Syntax.PExpr} {C : PancakeExp} (hc : Lower.lowerExp c = some C)
    {t e : List Syntax.PStmt} (hlt : LowKK t) (hle : LowKK e) (hdt : declared t = []) (hde : declared e = [])
    {P Q : Assn σ} (hQ : Safe.ClockFree Q) (hv : ∀ u, P u → eval u C = some (bw false)) (he : FragR o R e P Q) :
    FragR o R [.ite c t e] P Q :=
  fragR_if o hc hlt hle hQ (noDecl _ hdt) (noDecl _ hde) hv (fun h => absurd h (by decide)) fun _ => he

/-- `artReceived`'s locals in its loop. -/
def recvL (S E : Nat) (A : Word) (q : RecvSt) : List (String × Value) :=
  [("dep", BitVec.ofNat 64 q.dep), ("mode", BitVec.ofNat 64 q.mode), ("i", BitVec.ofNat 64 q.i), ("a", A),
   ("s", BitVec.ofNat 64 S), ("e", BitVec.ofNat 64 E)]

theorem runF_recvL {s0 u : PancakeState σ} {l : List (String × Value)} {F : (Word → Word) → Prop}
    (h : RunF s0 l F u) {S E : Nat} {A : Word} {q : RecvSt}
    (h1 : l.lookup "dep" = some (BitVec.ofNat 64 q.dep)) (h2 : l.lookup "mode" = some (BitVec.ofNat 64 q.mode))
    (h3 : l.lookup "i" = some (BitVec.ofNat 64 q.i)) (h4 : l.lookup "a" = some A)
    (h5 : l.lookup "s" = some (BitVec.ofNat 64 S)) (h6 : l.lookup "e" = some (BitVec.ofNat 64 E)) :
    RunF s0 (recvL S E A q) F u :=
  ⟨⟨fun p hp => by
    simp only [recvL, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first | exact vals_lookup h.1.vals h1 | exact vals_lookup h.1.vals h2 | exact vals_lookup h.1.vals h3 |
      exact vals_lookup h.1.vals h4 | exact vals_lookup h.1.vals h5 | exact vals_lookup h.1.vals h6,
    h.1.memaddrs, h.1.base, h.1.code, h.1.be⟩, h.2⟩

/-- The body's locals read off another list, the byte read in front. -/
theorem runF_recvB {s0 u : PancakeState σ} {l : List (String × Value)} {F : (Word → Word) → Prop}
    (h : RunF s0 l F u) {S E : Nat} {A : Word} {q : RecvSt} {vb : Value} (hb : l.lookup "b" = some vb := by rfl)
    (h1 : l.lookup "dep" = some (BitVec.ofNat 64 q.dep) := by rfl)
    (h2 : l.lookup "mode" = some (BitVec.ofNat 64 q.mode) := by rfl)
    (h3 : l.lookup "i" = some (BitVec.ofNat 64 q.i) := by rfl) (h4 : l.lookup "a" = some A := by rfl)
    (h5 : l.lookup "s" = some (BitVec.ofNat 64 S) := by rfl) (h6 : l.lookup "e" = some (BitVec.ofNat 64 E) := by rfl) :
    RunF s0 (("b", vb) :: recvL S E A q) F u :=
  runF_push h hb (runF_recvL h h1 h2 h3 h4 h5 h6)

/-- `artReceived`'s loop body. -/
def recvBody : List Syntax.PStmt :=
  ArticleProg.readIn "b" "i" ++
  [.ite (Syntax.eAnd (or2 (Syntax.eEq (Syntax.v "mode") (Syntax.n 1)) (Syntax.eLt (Syntax.n 0) (Syntax.v "dep")))
      (Syntax.eEq (Syntax.v "b") (Syntax.n 92)))
    [.assign "i" (Syntax.eAdd (Syntax.v "i") (Syntax.n 2))]
    [.ite (Syntax.eLt (Syntax.n 0) (Syntax.v "dep"))
      [.ite (Syntax.eEq (Syntax.v "b") (Syntax.n 40)) [inc "dep"]
        [ArticleProg.ifs (Syntax.eEq (Syntax.v "b") (Syntax.n 41))
          [.assign "dep" (Syntax.eSub (Syntax.v "dep") (Syntax.n 1))]],
       inc "i"]
      [.ite (Syntax.eEq (Syntax.v "mode") (Syntax.n 1))
        [ArticleProg.ifs (Syntax.eEq (Syntax.v "b") (Syntax.n 34)) [.assign "mode" (Syntax.n 0)], inc "i"]
        [.ite (Syntax.eEq (Syntax.v "mode") (Syntax.n 2))
          [ArticleProg.ifs (Syntax.eEq (Syntax.v "b") (Syntax.n 93)) [.assign "mode" (Syntax.n 0)], inc "i"]
          [.ite (Syntax.eEq (Syntax.v "b") (Syntax.n 34)) [.assign "mode" (Syntax.n 1), inc "i"]
            [.ite (Syntax.eEq (Syntax.v "b") (Syntax.n 91)) [.assign "mode" (Syntax.n 2), inc "i"]
              [.ite (Syntax.eEq (Syntax.v "b") (Syntax.n 40)) [.assign "dep" (Syntax.n 1), inc "i"]
                [ArticleProg.ifs (Syntax.eEq (Syntax.v "b") (Syntax.n 59))
                  [.ret (Syntax.eAdd (Syntax.v "i") (Syntax.n 1))], inc "i"]]]]]]]]

theorem artReceived_body : guardL ArticleProg.artReceived.body =
    [areaAt ArticleProg.ofs, .dec "i" (Syntax.v "s"), .dec "mode" (Syntax.n 0), .dec "dep" (Syntax.n 0),
     .while (Syntax.eLt (Syntax.v "i") (Syntax.v "e")) recvBody, .ret (Syntax.v "e")] := rfl

/-- What `artReceived` gives back: the place `P` from which the field's date is (`receivedDate`). -/
def RecvRet (a : Bytes) (S E : Nat) (m0 : Word → Word) : Ret := fun v m =>
  m = m0 ∧ ∃ P, v = BitVec.ofNat 64 P ∧ S ≤ P ∧ P ≤ E ∧ seg a P E = receivedDate 0 0 (seg a S E)

/-- **A turn of the body**: it returns at the date's `;`, or is a step. -/
theorem recv_body (o : Oracle σ) {A : Word} {s1 : PancakeState σ} {a : Bytes}
    (hin : InputAt s1.memory s1.memaddrs s1.be A a) {S E : Nat} (hE : E ≤ a.length) (hEM : E ≤ artMax)
    {q : RecvSt} (hq : RecvInv a S E q) (hi : q.i < E) :
    FragR o (RecvRet a S E s1.memory) recvBody (RunF s1 (recvL S E A q) (· = s1.memory))
      (fun u => RunF s1 (recvL S E A (recvStep a q)) (· = s1.memory) u ∧
        ¬(q.mode = 0 ∧ q.dep = 0 ∧ (a[q.i]!).toNat = 59)) := by
  have hq' := hq
  obtain ⟨hSi, -, hm2, hdi, hmd, -⟩ := hq'
  have hM := artMax_eq
  have hia : q.i < a.length := by omega
  have hbl : (a[q.i]!).toNat < 256 := (a[q.i]!).isLt
  refine fragR_append (xs := [_, _]) (fragR_of (frag_append (xs := [_]) (kept_frag o (by decide) (runF_clock _ _ _)
    fun u h => ⟨q.i, vals_lookup h.1.vals rfl, by omega⟩) (runF_dec o rfl rfl (v := BitVec.ofNat 64 (a[q.i]!).toNat)
      fun u h => inByte_eval (input_run hin h) (vals_lookup h.1.vals rfl) hia (vals_lookup h.1.vals rfl)))) ?_
  have hsemi := recv_semi hE hq hi
  unfold recvStep
  generalize (a[q.i]!).toNat = bt at hbl hsemi ⊢
  let LB : RecvSt → List (String × Value) := fun q' => ("b", BitVec.ofNat 64 bt) :: recvL S E A q'
  have evb : ∀ {q' : RecvSt} (u : PancakeState σ), RunF s1 (LB q') (· = s1.memory) u → ∀ k, k < 2 ^ 64 →
      eval u (.cmp .equal (.var "b") (.const (BitVec.ofNat 64 k))) = some (bw (decide (bt = k))) :=
    fun u h k hk => FramerCode.eval_eq (by omega) hk (ev_var (vals_lookup h.1.vals rfl)) rfl
  have evm : ∀ (u : PancakeState σ), RunF s1 (LB q) (· = s1.memory) u → ∀ k, k < 2 ^ 64 →
      eval u (.cmp .equal (.var "mode") (.const (BitVec.ofNat 64 k))) = some (bw (decide (q.mode = k))) :=
    fun u h k hk => FramerCode.eval_eq (by omega) hk (ev_var (vals_lookup h.1.vals rfl)) rfl
  have evd : ∀ (u : PancakeState σ), RunF s1 (LB q) (· = s1.memory) u →
      eval u (.cmp .less (.const (BitVec.ofNat 64 0)) (.var "dep")) = some (bw (decide (0 < q.dep))) :=
    fun u h => FramerCode.eval_lt (by decide) (by omega) rfl (ev_var (vals_lookup h.1.vals rfl))
  have ev1 : ∀ (u : PancakeState σ), RunF s1 (LB q) (· = s1.memory) u →
      eval u (.op .and_ (FramerCode.or2E (.cmp .equal (.var "mode") (.const (BitVec.ofNat 64 1)))
        (.cmp .less (.const (BitVec.ofNat 64 0)) (.var "dep")))
        (.cmp .equal (.var "b") (.const (BitVec.ofNat 64 92)))) =
        some (bw (decide ((q.mode = 1 ∨ 0 < q.dep) ∧ bt = 92))) := fun u h => by
    rw [FramerCode.eval_and (FramerCode.eval_or2 (evm u h 1 (by decide)) (evd u h)) (evb u h 92 (by decide)),
      Bool.decide_and, Bool.decide_or]
  have lk : ∀ xs : List Syntax.PStmt, (∃ c, Block.lowerK xs .skip = some c) → LowKK xs :=
    fun xs ⟨c, hc⟩ => lowK_any xs hc
  have inc_i : ∀ q' : RecvSt, q'.i = q.i →
      Frag o [inc "i"] (RunF s1 (LB q') (· = s1.memory)) (RunF s1 (LB { q' with i := q.i + 1 }) (· = s1.memory)) :=
    fun q' e => set_to o (l := LB q') rfl rfl (v := BitVec.ofNat 64 (q.i + 1)) (fun u h => by
      rw [← e]; exact ev_inc (vals_lookup h.1.vals rfl)) fun u h => runF_recvB h
  have post : ∀ q' : RecvSt, recvStepB q bt = q' → ∀ u, RunF s1 (LB q') (· = s1.memory) u →
      RunF s1 (recvL S E A (recvStepB q bt)) (· = s1.memory) u := fun q' e u h => by
    rw [e]; exact runF_mono h (fun p hp => List.mem_cons_of_mem _ hp) fun _ e => e
  by_cases hret : q.mode = 0 ∧ q.dep = 0 ∧ bt = 59
  · obtain ⟨hm0, hd0, h59⟩ := hret
    have hdate := hsemi hm0 hd0 h59
    refine fragR_ifF o rfl (lk _ ⟨_, rfl⟩) (lk _ ⟨_, rfl⟩) rfl rfl (fun u k h => ⟨runF_clock _ _ _ u k h.1, h.2⟩)
      (fun u h => (ev1 u h).trans (by rw [bw_f (by omega)])) ?_
    refine fragR_ifF o rfl (lk _ ⟨_, rfl⟩) (lk _ ⟨_, rfl⟩) rfl rfl (fun u k h => ⟨runF_clock _ _ _ u k h.1, h.2⟩)
      (fun u h => (evd u h).trans (by rw [bw_f (by omega)])) ?_
    refine fragR_ifF o rfl (lk _ ⟨_, rfl⟩) (lk _ ⟨_, rfl⟩) rfl rfl (fun u k h => ⟨runF_clock _ _ _ u k h.1, h.2⟩)
      (fun u h => (evm u h 1 (by decide)).trans (by rw [bw_f (by omega)])) ?_
    refine fragR_ifF o rfl (lk _ ⟨_, rfl⟩) (lk _ ⟨_, rfl⟩) rfl rfl (fun u k h => ⟨runF_clock _ _ _ u k h.1, h.2⟩)
      (fun u h => (evm u h 2 (by decide)).trans (by rw [bw_f (by omega)])) ?_
    refine fragR_ifF o rfl (lk _ ⟨_, rfl⟩) (lk _ ⟨_, rfl⟩) rfl rfl (fun u k h => ⟨runF_clock _ _ _ u k h.1, h.2⟩)
      (fun u h => (evb u h 34 (by decide)).trans (by rw [bw_f (by omega)])) ?_
    refine fragR_ifF o rfl (lk _ ⟨_, rfl⟩) (lk _ ⟨_, rfl⟩) rfl rfl (fun u k h => ⟨runF_clock _ _ _ u k h.1, h.2⟩)
      (fun u h => (evb u h 91 (by decide)).trans (by rw [bw_f (by omega)])) ?_
    refine fragR_ifF o rfl (lk _ ⟨_, rfl⟩) (lk _ ⟨_, rfl⟩) rfl rfl (fun u k h => ⟨runF_clock _ _ _ u k h.1, h.2⟩)
      (fun u h => (evb u h 40 (by decide)).trans (by rw [bw_f (by omega)])) ?_
    refine fragR_append (xs := [_]) (fragR_ifT o rfl (lk _ ⟨_, rfl⟩) lowKK_nil rfl rfl (Q := fun _ => False)
      (fun _ _ h => h) (fun u h => (evb u h 59 (by decide)).trans (by rw [bw_t h59])) ?_)
      (fragR_of (frag_unsat (lk _ ⟨_, rfl⟩) fun _ h => h))
    exact fragR_ret o rfl fun u h => ⟨_, ev_inc (vals_lookup h.1.vals rfl), h.2, q.i + 1, rfl, by omega, by omega,
      hdate.symm⟩
  refine fragR_of (frag_conseq (P0' := RunF s1 (recvL S E A (recvStepB q bt)) (· = s1.memory)) ?_ (fun _ h => h)
    fun u h => ⟨h, hret⟩)
  by_cases h92 : (q.mode = 1 ∨ 0 < q.dep) ∧ bt = 92
  · refine frag_ifT o rfl (lk _ ⟨_, rfl⟩) (lk _ ⟨_, rfl⟩) rfl rfl (runF_clock _ _ _)
      (fun u h => (ev1 u h).trans (by rw [bw_t h92])) ?_
    exact frag_conseq (set_to o (l := LB q) rfl rfl (v := BitVec.ofNat 64 (q.i + 2)) (l' := LB { q with i := q.i + 2 })
      (fun u h => ev_inc (vals_lookup h.1.vals rfl)) fun u h => runF_recvB h) (fun _ h => h)
      (post _ (by simp [recvStepB, h92]))
  refine frag_ifF o rfl (lk _ ⟨_, rfl⟩) (lk _ ⟨_, rfl⟩) rfl rfl (runF_clock _ _ _)
    (fun u h => (ev1 u h).trans (by rw [bw_f h92])) ?_
  by_cases hd : 0 < q.dep
  · have hm0 : q.mode = 0 := Decidable.byContradiction fun hne => absurd (hmd hne) (by omega)
    have h92' : bt ≠ 92 := fun e => h92 ⟨.inr hd, e⟩
    refine frag_ifT o rfl (lk _ ⟨_, rfl⟩) (lk _ ⟨_, rfl⟩) rfl rfl (runF_clock _ _ _)
      (fun u h => (evd u h).trans (by rw [bw_t hd])) ?_
    by_cases h40 : bt = 40
    · refine frag_conseq (frag_append (xs := [_]) (frag_ifT o rfl (lk _ ⟨_, rfl⟩) (lk _ ⟨_, rfl⟩) rfl rfl
        (runF_clock _ _ _) (fun u h => (evb u h 40 (by decide)).trans (by rw [bw_t h40]))
        (set_to o (l := LB q) rfl rfl (v := BitVec.ofNat 64 (q.dep + 1)) (l' := LB { q with dep := q.dep + 1 })
          (fun u h => ev_inc (vals_lookup h.1.vals rfl)) fun u h => runF_recvB h)) (inc_i _ rfl)) (fun _ h => h)
        (post _ (by simp [recvStepB, hd, h40]))
    by_cases h41 : bt = 41
    · refine frag_conseq (frag_append (xs := [_]) (frag_ifF o rfl (lk _ ⟨_, rfl⟩) (lk _ ⟨_, rfl⟩) rfl rfl
        (runF_clock _ _ _) (fun u h => (evb u h 40 (by decide)).trans (by rw [bw_f h40]))
        (frag_ifT o rfl (lk _ ⟨_, rfl⟩) lowKK_nil rfl rfl (runF_clock _ _ _)
          (fun u h => (evb u h 41 (by decide)).trans (by rw [bw_t h41]))
          (set_to o (l := LB q) rfl rfl (v := BitVec.ofNat 64 (q.dep - 1)) (l' := LB { q with dep := q.dep - 1 })
            (fun u h => DN.News.ArticleRun.ev_sub (y := 1)
              (by rw [show 1 + (q.dep - 1) = q.dep by omega]; exact ev_var (vals_lookup h.1.vals rfl)) rfl)
            fun u h => runF_recvB h))) (inc_i _ rfl)) (fun _ h => h)
        (post _ (by simp [recvStepB, hd, h41]))
    refine frag_conseq (frag_append (xs := [_]) (frag_ifF o rfl (lk _ ⟨_, rfl⟩) (lk _ ⟨_, rfl⟩) rfl rfl
      (runF_clock _ _ _) (fun u h => (evb u h 40 (by decide)).trans (by rw [bw_f h40]))
      (frag_ifF o rfl (lk _ ⟨_, rfl⟩) lowKK_nil rfl rfl (runF_clock _ _ _)
        (fun u h => (evb u h 41 (by decide)).trans (by rw [bw_f h41])) (frag_nil o fun _ h => h))) (inc_i _ rfl))
      (fun _ h => h) (post _ (by simp [recvStepB, h92', hd, h40, h41]))
  refine frag_ifF o rfl (lk _ ⟨_, rfl⟩) (lk _ ⟨_, rfl⟩) rfl rfl (runF_clock _ _ _)
    (fun u h => (evd u h).trans (by rw [bw_f hd])) ?_
  by_cases hm1 : q.mode = 1
  · have h92' : bt ≠ 92 := fun e => h92 ⟨.inl hm1, e⟩
    refine frag_ifT o rfl (lk _ ⟨_, rfl⟩) (lk _ ⟨_, rfl⟩) rfl rfl (runF_clock _ _ _)
      (fun u h => (evm u h 1 (by decide)).trans (by rw [bw_t hm1])) ?_
    by_cases h34 : bt = 34
    · exact frag_conseq (frag_append (xs := [_]) (frag_ifT o rfl (lk _ ⟨_, rfl⟩) lowKK_nil rfl rfl (runF_clock _ _ _)
        (fun u h => (evb u h 34 (by decide)).trans (by rw [bw_t h34]))
        (set_to o (l := LB q) rfl rfl (v := BitVec.ofNat 64 0) (l' := LB { q with mode := 0 }) (fun _ _ => rfl)
          fun u h => runF_recvB h)) (inc_i _ rfl)) (fun _ h => h)
        (post _ (by simp [recvStepB, hd, hm1, h34]))
    exact frag_conseq (frag_append (xs := [_]) (frag_ifF o rfl (lk _ ⟨_, rfl⟩) lowKK_nil rfl rfl (runF_clock _ _ _)
      (fun u h => (evb u h 34 (by decide)).trans (by rw [bw_f h34])) (frag_nil o fun _ h => h)) (inc_i q rfl))
      (fun _ h => h) (post _ (by simp [recvStepB, h92', hd, hm1, h34]))
  refine frag_ifF o rfl (lk _ ⟨_, rfl⟩) (lk _ ⟨_, rfl⟩) rfl rfl (runF_clock _ _ _)
    (fun u h => (evm u h 1 (by decide)).trans (by rw [bw_f hm1])) ?_
  by_cases hm2' : q.mode = 2
  · refine frag_ifT o rfl (lk _ ⟨_, rfl⟩) (lk _ ⟨_, rfl⟩) rfl rfl (runF_clock _ _ _)
      (fun u h => (evm u h 2 (by decide)).trans (by rw [bw_t hm2'])) ?_
    by_cases h93 : bt = 93
    · exact frag_conseq (frag_append (xs := [_]) (frag_ifT o rfl (lk _ ⟨_, rfl⟩) lowKK_nil rfl rfl (runF_clock _ _ _)
        (fun u h => (evb u h 93 (by decide)).trans (by rw [bw_t h93]))
        (set_to o (l := LB q) rfl rfl (v := BitVec.ofNat 64 0) (l' := LB { q with mode := 0 }) (fun _ _ => rfl)
          fun u h => runF_recvB h)) (inc_i _ rfl)) (fun _ h => h)
        (post _ (by simp [recvStepB, hd, hm2', h93]))
    exact frag_conseq (frag_append (xs := [_]) (frag_ifF o rfl (lk _ ⟨_, rfl⟩) lowKK_nil rfl rfl (runF_clock _ _ _)
      (fun u h => (evb u h 93 (by decide)).trans (by rw [bw_f h93])) (frag_nil o fun _ h => h)) (inc_i q rfl))
      (fun _ h => h) (post _ (by simp [recvStepB, hd, hm2', h93]))
  refine frag_ifF o rfl (lk _ ⟨_, rfl⟩) (lk _ ⟨_, rfl⟩) rfl rfl (runF_clock _ _ _)
    (fun u h => (evm u h 2 (by decide)).trans (by rw [bw_f hm2'])) ?_
  have hm0 : q.mode = 0 := by omega
  have hd0 : q.dep = 0 := by omega
  by_cases h34 : bt = 34
  · refine frag_ifT o rfl (lk _ ⟨_, rfl⟩) (lk _ ⟨_, rfl⟩) rfl rfl (runF_clock _ _ _)
      (fun u h => (evb u h 34 (by decide)).trans (by rw [bw_t h34])) ?_
    exact frag_conseq (frag_append (xs := [_]) (set_to o (l := LB q) rfl rfl (v := BitVec.ofNat 64 1)
      (l' := LB { q with mode := 1 }) (fun _ _ => rfl) fun u h => runF_recvB h) (inc_i _ rfl)) (fun _ h => h)
      (post _ (by simp [recvStepB, hd, hm1, hm2', h34]))
  refine frag_ifF o rfl (lk _ ⟨_, rfl⟩) (lk _ ⟨_, rfl⟩) rfl rfl (runF_clock _ _ _)
    (fun u h => (evb u h 34 (by decide)).trans (by rw [bw_f h34])) ?_
  by_cases h91 : bt = 91
  · refine frag_ifT o rfl (lk _ ⟨_, rfl⟩) (lk _ ⟨_, rfl⟩) rfl rfl (runF_clock _ _ _)
      (fun u h => (evb u h 91 (by decide)).trans (by rw [bw_t h91])) ?_
    exact frag_conseq (frag_append (xs := [_]) (set_to o (l := LB q) rfl rfl (v := BitVec.ofNat 64 2)
      (l' := LB { q with mode := 2 }) (fun _ _ => rfl) fun u h => runF_recvB h) (inc_i _ rfl)) (fun _ h => h)
      (post _ (by simp [recvStepB, hd, hm1, hm2', h91]))
  refine frag_ifF o rfl (lk _ ⟨_, rfl⟩) (lk _ ⟨_, rfl⟩) rfl rfl (runF_clock _ _ _)
    (fun u h => (evb u h 91 (by decide)).trans (by rw [bw_f h91])) ?_
  by_cases h40 : bt = 40
  · refine frag_ifT o rfl (lk _ ⟨_, rfl⟩) (lk _ ⟨_, rfl⟩) rfl rfl (runF_clock _ _ _)
      (fun u h => (evb u h 40 (by decide)).trans (by rw [bw_t h40])) ?_
    exact frag_conseq (frag_append (xs := [_]) (set_to o (l := LB q) rfl rfl (v := BitVec.ofNat 64 1)
      (l' := LB { q with dep := 1 }) (fun _ _ => rfl) fun u h => runF_recvB h) (inc_i _ rfl)) (fun _ h => h)
      (post _ (by simp [recvStepB, hd, hm1, hm2', h40]))
  refine frag_ifF o rfl (lk _ ⟨_, rfl⟩) (lk _ ⟨_, rfl⟩) rfl rfl (runF_clock _ _ _)
    (fun u h => (evb u h 40 (by decide)).trans (by rw [bw_f h40])) ?_
  have h59 : bt ≠ 59 := fun e => hret ⟨hm0, hd0, e⟩
  exact frag_conseq (frag_append (xs := [_]) (frag_ifF o rfl (lk _ ⟨_, rfl⟩) lowKK_nil rfl rfl (runF_clock _ _ _)
    (fun u h => (evb u h 59 (by decide)).trans (by rw [bw_f h59])) (frag_nil o fun _ h => h)) (inc_i q rfl))
    (fun _ h => h) (post _ (by simp [recvStepB, hd, hm1, hm2', h34, h91, h40]))

/-- **`artReceived` finds where a Received field's date starts**, as `receivedDate` reads it, if it returns. -/
theorem artReceived_ok (o : Oracle σ) {A : Word} {s1 : PancakeState σ} (hA : Area ArticleProg.ofs A s1) {a : Bytes}
    (hlen : a.length ≤ artMax) (hin : InputAt s1.memory s1.memaddrs s1.be A a) {S E : Nat} (hSE : S ≤ E)
    (hE : E ≤ a.length) (hs : s1.locals "s" = some (BitVec.ofNat 64 S))
    (he : s1.locals "e" = some (BitVec.ofNat 64 E)) :
    ∃ body, Lower.lower (gd ArticleProg.artReceived) = some body ∧
      SafeR o (fun s => s = s1) body (RecvRet a S E s1.memory) fun _ => False := by
  have hM := artMax_eq
  have hEM : E ≤ artMax := by omega
  refine body_of ?_
  show FragR o _ (guardL ArticleProg.artReceived.body) _ _
  rw [artReceived_body]
  obtain ⟨EA, hEA⟩ := atOff_lower ArticleProg.ofs
  refine fragR_conseq (P0 := RunF s1 [("s", BitVec.ofNat 64 S), ("e", BitVec.ofNat 64 E)] (· = s1.memory))
    ?_ (entry_two hs he) fun _ h => h
  refine fragR_append (xs := [_]) (fragR_of (runF_dec o hEA rfl (v := A) fun u h => areaAt_eval hA h.1.base hEA)) ?_
  refine fragR_append (xs := [_]) (fragR_of (runF_dec o rfl rfl (v := BitVec.ofNat 64 S) fun u h =>
    ev_var (vals_lookup h.1.vals rfl))) ?_
  refine fragR_append (xs := [_]) (fragR_of (runF_dec o rfl rfl (v := BitVec.ofNat 64 0) fun _ _ => rfl)) ?_
  refine fragR_append (xs := [_]) (fragR_of (runF_dec o rfl rfl (v := BitVec.ofNat 64 0) fun _ _ => rfl)) ?_
  let I : Assn σ := fun u => ∃ q, RunF s1 (recvL S E A q) (· = s1.memory) u ∧ RecvInv a S E q
  have hIc : Safe.ClockFree I := fun u k ⟨q, h, hv⟩ => ⟨q, runF_clock _ _ _ u k h, hv⟩
  have hcond : ∀ u q, RunF s1 (recvL S E A q) (· = s1.memory) u → RecvInv a S E q →
      eval u (.cmp .less (.var "i") (.var "e")) = some (bw (decide (q.i < E))) := fun u q h hq =>
    FramerCode.eval_lt (by have := hq.2.1; omega) (by omega) (ev_var (vals_lookup h.1.vals rfl))
      (ev_var (vals_lookup h.1.vals rfl))
  have hlow : LowKK recvBody := lowK_any _ (k := .skip) rfl
  refine fragR_append (xs := [_]) (fragR_conseq (fragR_while o rfl hlow hIc
    (fun u z v ⟨q, h, hv⟩ hz => by
      change z ∈ ["b"] at hz
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hz; subst hz
      exact ⟨q, runF_restore h rfl v, hv⟩) (fun u ⟨q, h, hv⟩ => ⟨_, hcond u q h hv⟩) ?_)
    (fun u h => ⟨⟨S, 0, 0⟩, h, Nat.le_refl _, Nat.le_succ_of_le hSE, Nat.zero_le _, Nat.zero_le _,
      fun h => absurd rfl h, rfl⟩)
    fun _ h => h) ?_
  · refine fragR_conseq (P0 := fun u => ∃ q, (fun q u => RunF s1 (recvL S E A q) (· = s1.memory) u ∧
      RecvInv a S E q ∧ q.i < E) q u) (fragR_exists hlow fun q => ?_)
      (fun u ⟨⟨q, h, hv⟩, h0⟩ => ⟨q, h, hv, by
        rw [hcond u q h hv] at h0; exact of_decide_eq_true (bw_ne0 h0)⟩) fun _ h => h
    refine fragR_pure (RecvInv a S E q ∧ q.i < E) (fun u h => h.2) hlow fun ⟨hq, hi⟩ => ?_
    exact fragR_conseq (recv_body o hin hE hEM hq hi) (fun u h => h.1)
      fun u h => ⟨_, h.1, recv_step hE hq hi h.2⟩
  refine fragR_ret o rfl fun u ⟨⟨q, h, hq⟩, h0⟩ => ⟨_, ev_var (vals_lookup h.1.vals rfl), h.2, E, rfl, hSE,
    Nat.le_refl _, ?_⟩
  rw [hcond u q h hq] at h0
  have hge : E ≤ q.i := by have := of_decide_eq_false (bw_eq0 h0); omega
  rw [hq.2.2.2.2.2, seg_over a hge, DN.News.ArticleSpec.receivedDate.eq_1, DN.News.ArticleLines.seg_self]

/-! ## A number of digits -/

open DN.News.ArticleSpec (number?)
open DN.News.CommandSpec (isDigit value)

theorem value_snoc (l : Bytes) (b : BitVec 8) : value (l ++ [b]) = 10 * value l + (b.toNat - 48) := by
  simp [value, List.foldl_append]

/-- What `artNum` gives back: the digits' number, at most `yearBig`, and it modulo 400 in `xNumMod`. If they are none
or not all digits, -1. -/
def NumRet (A : Word) (a : Bytes) (S E : Nat) (m0 : Word → Word) : Ret := fun v m =>
  match number? (seg a S E) with
  | some n => v = BitVec.ofNat 64 (min ArticleProg.yearBig n) ∧
      m = upd m0 (at_ A ArticleProg.xNumMod) (BitVec.ofNat 64 (n % 400))
  | none => v = BitVec.ofNat 64 (2 ^ 64 - 1) ∧ m = m0

/-- `artNum`'s loop body. -/
def numBody : List Syntax.PStmt :=
  ArticleProg.readIn "b" "i" ++
  [.ite (ArticleProg.isDig (Syntax.v "b"))
    [.assign "val"
      (Syntax.eAdd (Syntax.eMul (Syntax.v "val") (Syntax.n 10)) (Syntax.eSub (Syntax.v "b") (Syntax.n 48))),
     ArticleProg.ifs (Syntax.eLt (Syntax.n ArticleProg.yearBig) (Syntax.v "val"))
       [.assign "val" (Syntax.n ArticleProg.yearBig)],
     .assign "md" (Syntax.eAdd (Syntax.eMul (Syntax.v "md") (Syntax.n 10)) (Syntax.eSub (Syntax.v "b") (Syntax.n 48))),
     .while (Syntax.eLe (Syntax.n 400) (Syntax.v "md")) [.assign "md" (Syntax.eSub (Syntax.v "md") (Syntax.n 400))],
     inc "i"]
    [.ret ArticleProg.neg1]]

theorem artNum_body : guardL ArticleProg.artNum.body =
    [areaAt ArticleProg.ofs, ArticleProg.ifs (Syntax.eLe (Syntax.v "e") (Syntax.v "s")) [.ret ArticleProg.neg1],
     .dec "i" (Syntax.v "s"), .dec "val" (Syntax.n 0), .dec "md" (Syntax.n 0),
     .while (Syntax.eLt (Syntax.v "i") (Syntax.v "e")) numBody,
     ArticleProg.setW ArticleProg.xNumMod (Syntax.v "md"), .ret (Syntax.v "val")] := rfl

theorem ev_madd {u : PancakeState σ} {x y : String} {X B c : Nat} (hx : u.locals x = some (BitVec.ofNat 64 X))
    (hy : u.locals y = some (BitVec.ofNat 64 B)) (hB : c ≤ B) :
    eval u (.op .add (.mul (.var x) (.const (BitVec.ofNat 64 10))) (.op .sub (.var y) (.const (BitVec.ofNat 64 c))))
      = some (BitVec.ofNat 64 (X * 10 + (B - c))) := by
  have hs := DN.News.ArticleRun.ev_sub (u := u) (a := .var y) (b := .const (BitVec.ofNat 64 c)) (x := B - c) (y := c)
    (by rw [show c + (B - c) = B by omega]; exact ev_var hy) rfl
  simp only [eval, hx] at hs ⊢
  rw [hs]
  simp only [Option.some.injEq]
  rw [← BitVec.ofNat_mul, ← BitVec.ofNat_add]

/-- `artNum`'s locals in its loop. -/
def numL (S E : Nat) (A : Word) (i val md : Nat) : List (String × Value) :=
  [("md", BitVec.ofNat 64 md), ("val", BitVec.ofNat 64 val), ("i", BitVec.ofNat 64 i), ("a", A),
   ("s", BitVec.ofNat 64 S), ("e", BitVec.ofNat 64 E)]

/-- What `artNum`'s loop keeps: the digits so far, their number at most `yearBig`, and it modulo 400. -/
def NumInv (a : Bytes) (S E i val md : Nat) : Prop :=
  S ≤ i ∧ i ≤ E ∧ (seg a S i).all isDigit = true ∧ val = min ArticleProg.yearBig (value (seg a S i)) ∧
    md = value (seg a S i) % 400

theorem isDig_bytes (b : BitVec 8) : (decide (48 ≤ b.toNat) && decide (b.toNat ≤ 57)) = isDigit b := rfl

/-- A digit after digits: they are digits still, their number ten times more and the digit's. -/
theorem num_digit {a : Bytes} {S E i : Nat} (hE : E ≤ a.length) (hSi : S ≤ i) (hi : i < E)
    (hall : (seg a S i).all isDigit = true) (hd : isDigit a[i]! = true) :
    (seg a S (i + 1)).all isDigit = true ∧ value (seg a S (i + 1)) = 10 * value (seg a S i) + ((a[i]!).toNat - 48) := by
  have hia : i < a.length := by omega
  rw [seg_succ a hSi hia, ← getElem!_pos a i hia, value_snoc]
  exact ⟨by rw [List.all_append, hall, List.all_cons, hd]; rfl, rfl⟩

/-- A byte that is not a digit: the bytes write no number. -/
theorem num_none {a : Bytes} {S E i : Nat} (hE : E ≤ a.length) (hSi : S ≤ i) (hi : i < E)
    (hd : isDigit a[i]! = false) : number? (seg a S E) = none := by
  unfold number?
  have : (seg a S E).all isDigit = false := by
    cases hc : (seg a S E).all isDigit
    · rfl
    · exact absurd (List.all_eq_true.1 hc _ (seg_mem a hSi hi hE)) (by rw [hd]; decide)
  simp [this]

theorem runF_numL {s0 u : PancakeState σ} {l : List (String × Value)} {F : (Word → Word) → Prop}
    (h : RunF s0 l F u) {S E : Nat} {A : Word} {i val md : Nat}
    (h1 : l.lookup "md" = some (BitVec.ofNat 64 md)) (h2 : l.lookup "val" = some (BitVec.ofNat 64 val))
    (h3 : l.lookup "i" = some (BitVec.ofNat 64 i)) (h4 : l.lookup "a" = some A)
    (h5 : l.lookup "s" = some (BitVec.ofNat 64 S)) (h6 : l.lookup "e" = some (BitVec.ofNat 64 E)) :
    RunF s0 (numL S E A i val md) F u :=
  ⟨⟨fun p hp => by
    simp only [numL, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first | exact vals_lookup h.1.vals h1 | exact vals_lookup h.1.vals h2 | exact vals_lookup h.1.vals h3 |
      exact vals_lookup h.1.vals h4 | exact vals_lookup h.1.vals h5 | exact vals_lookup h.1.vals h6,
    h.1.memaddrs, h.1.base, h.1.code, h.1.be⟩, h.2⟩

/-- The body's locals read off another list, the byte read in front. -/
theorem runF_numB {s0 u : PancakeState σ} {l : List (String × Value)} {F : (Word → Word) → Prop}
    (h : RunF s0 l F u) {S E : Nat} {A : Word} {i val md : Nat} {vb : Value} (hb : l.lookup "b" = some vb := by rfl)
    (h1 : l.lookup "md" = some (BitVec.ofNat 64 md) := by rfl)
    (h2 : l.lookup "val" = some (BitVec.ofNat 64 val) := by rfl)
    (h3 : l.lookup "i" = some (BitVec.ofNat 64 i) := by rfl) (h4 : l.lookup "a" = some A := by rfl)
    (h5 : l.lookup "s" = some (BitVec.ofNat 64 S) := by rfl) (h6 : l.lookup "e" = some (BitVec.ofNat 64 E) := by rfl) :
    RunF s0 (("b", vb) :: numL S E A i val md) F u :=
  runF_push h hb (runF_numL h h1 h2 h3 h4 h5 h6)

/-- **`artNum`'s inner loop takes the remainder modulo 400.** -/
theorem num_mod (o : Oracle σ) {s1 : PancakeState σ} {S E : Nat} {A : Word} {vb : Value} {i val X : Nat}
    (hX : X < 2 ^ 62) :
    Frag o
      [.while (Syntax.eLe (Syntax.n 400) (Syntax.v "md")) [.assign "md" (Syntax.eSub (Syntax.v "md") (Syntax.n 400))]]
      (RunF s1 (("b", vb) :: numL S E A i val X) (· = s1.memory))
      (RunF s1 (("b", vb) :: numL S E A i val (X % 400)) (· = s1.memory)) := by
  let I : Assn σ := fun u => ∃ k, RunF s1 (("b", vb) :: numL S E A i val k) (· = s1.memory) u ∧ k % 400 = X % 400 ∧
    k ≤ X
  have hIc : Safe.ClockFree I := fun u c ⟨k, h, hv⟩ => ⟨k, runF_clock _ _ _ u c h, hv⟩
  have hc : ∀ u k, RunF s1 (("b", vb) :: numL S E A i val k) (· = s1.memory) u → k ≤ X →
      eval u (FramerCode.leE (.const (BitVec.ofNat 64 400)) (.var "md")) = some (bw (decide (400 ≤ k))) :=
    fun u k h hk => FramerCode.eval_le (by decide) (by omega) rfl (ev_var (vals_lookup h.1.vals rfl))
  refine frag_conseq (frag_while o rfl (lowK_any _ (k := .skip) rfl) hIc (fun _ _ _ _ hy => by cases hy)
    (fun u ⟨k, h, _, hk⟩ => ⟨_, hc u k h hk⟩) ?_) (fun u h => ⟨X, h, rfl, Nat.le_refl _⟩) ?_
  · refine frag_conseq (P0 := fun u => ∃ k, (fun k u => RunF s1 (("b", vb) :: numL S E A i val k) (· = s1.memory) u ∧
      k % 400 = X % 400 ∧ k ≤ X ∧ 400 ≤ k) k u) (frag_exists (lowK_any _ (k := .skip) rfl) fun k => ?_)
      (fun u ⟨⟨k, h, hm, hk⟩, h0⟩ => ⟨k, h, hm, hk, by rw [hc u k h hk] at h0; exact of_decide_eq_true (bw_ne0 h0)⟩)
      fun _ h => h
    refine frag_pure (k % 400 = X % 400 ∧ k ≤ X ∧ 400 ≤ k) (fun u h => h.2) (lowK_any _ (k := .skip) rfl)
      fun ⟨hm, hk, h4⟩ => ?_
    exact frag_conseq (set_to o (l := ("b", vb) :: numL S E A i val k) rfl rfl (v := BitVec.ofNat 64 (k - 400))
      (l' := ("b", vb) :: numL S E A i val (k - 400))
      (fun u h => DN.News.ArticleRun.ev_sub (y := 400)
        (by rw [show 400 + (k - 400) = k by omega]; exact ev_var (vals_lookup h.1.vals rfl)) rfl)
      fun u h => runF_numB h) (fun u h => h.1)
      fun u h => ⟨k - 400, h, by omega, by omega⟩
  · intro u ⟨⟨k, h, hm, hk⟩, h0⟩
    rw [hc u k h hk] at h0
    have hlt : k < 400 := by have := of_decide_eq_false (bw_eq0 h0); omega
    rw [show X % 400 = k by rw [← hm]; exact Nat.mod_eq_of_lt hlt]
    exact h

theorem min_step (Y v d : Nat) : min Y (min Y v * 10 + d) = min Y (10 * v + d) := by omega

/-- **A turn of `artNum`'s body**: a digit's step, or -1 at a byte that is not one. -/
theorem num_body (o : Oracle σ) {A : Word} {s1 : PancakeState σ} {a : Bytes}
    (hin : InputAt s1.memory s1.memaddrs s1.be A a) {S E : Nat} (hE : E ≤ a.length) (hEM : E ≤ artMax)
    {i val md : Nat} (hq : NumInv a S E i val md) (hi : i < E) :
    FragR o (NumRet A a S E s1.memory) numBody (RunF s1 (numL S E A i val md) (· = s1.memory))
      (fun u => RunF s1 (numL S E A (i + 1) (min ArticleProg.yearBig (value (seg a S (i + 1))))
        (value (seg a S (i + 1)) % 400)) (· = s1.memory) u ∧ NumInv a S E (i + 1)
          (min ArticleProg.yearBig (value (seg a S (i + 1)))) (value (seg a S (i + 1)) % 400)) := by
  obtain ⟨hSi, -, hall, hval, hmd⟩ := hq
  have hM := artMax_eq
  have hia : i < a.length := by omega
  have hbl : (a[i]!).toNat < 256 := (a[i]!).isLt
  have hY : ArticleProg.yearBig = 100000 := rfl
  refine fragR_append (xs := [_, _]) (fragR_of (frag_append (xs := [_]) (kept_frag o (by decide) (runF_clock _ _ _)
    fun u h => ⟨i, vals_lookup h.1.vals rfl, by omega⟩) (runF_dec o rfl rfl (v := BitVec.ofNat 64 (a[i]!).toNat)
      fun u h => inByte_eval (input_run hin h) (vals_lookup h.1.vals rfl) hia (vals_lookup h.1.vals rfl)))) ?_
  have evd : ∀ u, RunF s1 (("b", BitVec.ofNat 64 (a[i]!).toNat) :: numL S E A i val md) (· = s1.memory) u →
      eval u (.op .and_ (FramerCode.leE (.const (BitVec.ofNat 64 48)) (.var "b"))
        (FramerCode.leE (.var "b") (.const (BitVec.ofNat 64 57)))) = some (bw (isDigit a[i]!)) := fun u h => by
    rw [FramerCode.eval_and (FramerCode.eval_le (by decide) (by omega) rfl (ev_var (vals_lookup h.1.vals rfl)))
      (FramerCode.eval_le (by omega) (by decide) (ev_var (vals_lookup h.1.vals rfl)) rfl), isDig_bytes]
  by_cases hd : isDigit a[i]! = true
  · obtain ⟨hall', hv'⟩ := num_digit hE hSi hi hall hd
    have h48 : 48 ≤ (a[i]!).toNat := by
      have := hd; simp only [isDigit, Bool.and_eq_true, decide_eq_true_eq] at this; exact this.1
    have h57 : (a[i]!).toNat ≤ 57 := by
      have := hd; simp only [isDigit, Bool.and_eq_true, decide_eq_true_eq] at this; exact this.2
    have hvB : val ≤ 100000 := by rw [hval, hY]; exact Nat.min_le_left _ _
    have hmB : md < 400 := by rw [hmd]; exact Nat.mod_lt _ (by decide)
    refine fragR_of (frag_ifT o rfl (lowK_any _ (k := .skip) rfl) (lowKK_ret rfl) rfl rfl (fun u k h =>
      ⟨runF_clock _ _ _ u k h.1, h.2⟩) (fun u h => (evd u h).trans (by rw [hd])) ?_)
    let d := (a[i]!).toNat - 48
    let LB : Nat → Nat → List (String × Value) := fun v m =>
      ("b", BitVec.ofNat 64 (a[i]!).toNat) :: numL S E A i v m
    refine frag_append (xs := [_]) (set_to o (l := LB val md) (l' := LB (val * 10 + d) md) rfl rfl
      (v := BitVec.ofNat 64 (val * 10 + d))
      (fun u h => ev_madd (vals_lookup h.1.vals rfl) (vals_lookup h.1.vals rfl) h48)
      fun u h => runF_numB h) ?_
    have hv1 : ∀ u, RunF s1 (LB (val * 10 + d) md) (· = s1.memory) u →
        eval u (.cmp .less (.const (BitVec.ofNat 64 ArticleProg.yearBig)) (.var "val")) =
          some (bw (decide (ArticleProg.yearBig < val * 10 + d))) := fun u h =>
      FramerCode.eval_lt (by rw [hY]; decide) (by omega) rfl (ev_var (vals_lookup h.1.vals rfl))
    refine frag_append (xs := [_]) (M := RunF s1 (LB (min ArticleProg.yearBig (val * 10 + d)) md) (· = s1.memory))
      ?_ ?_
    · by_cases hb : ArticleProg.yearBig < val * 10 + d
      · refine frag_ifT o rfl (lowK_any _ (k := .skip) rfl) lowKK_nil rfl rfl (runF_clock _ _ _)
          (fun u h => (hv1 u h).trans (by rw [bw_t hb])) ?_
        exact set_to o (l := LB (val * 10 + d) md) rfl rfl (v := BitVec.ofNat 64 ArticleProg.yearBig) (fun _ _ => rfl)
          fun u h => by rw [Nat.min_eq_left (Nat.le_of_lt hb)]; exact runF_numB h
      · refine frag_ifF o rfl (lowK_any _ (k := .skip) rfl) lowKK_nil rfl rfl (runF_clock _ _ _)
          (fun u h => (hv1 u h).trans (by rw [bw_f hb])) (frag_nil o fun u h => ?_)
        rw [Nat.min_eq_right (by omega)]; exact h
    refine frag_append (xs := [_]) (set_to o (l := LB (min ArticleProg.yearBig (val * 10 + d)) md)
      (l' := LB (min ArticleProg.yearBig (val * 10 + d)) (md * 10 + d)) rfl rfl
      (v := BitVec.ofNat 64 (md * 10 + d))
      (fun u h => ev_madd (vals_lookup h.1.vals rfl) (vals_lookup h.1.vals rfl) h48)
      fun u h => runF_numB h) ?_
    refine frag_append (xs := [_]) (num_mod o (by omega)) ?_
    refine frag_conseq (set_to o (l := LB (min ArticleProg.yearBig (val * 10 + d)) ((md * 10 + d) % 400))
      (l' := numL S E A (i + 1) (min ArticleProg.yearBig (val * 10 + d)) ((md * 10 + d) % 400)) rfl rfl
      (v := BitVec.ofNat 64 (i + 1)) (fun u h => ev_inc (vals_lookup h.1.vals rfl))
      fun u h => runF_numL h rfl rfl rfl rfl rfl rfl) (fun _ h => h) fun u h => ?_
    have e1 : min ArticleProg.yearBig (val * 10 + d) = min ArticleProg.yearBig (value (seg a S (i + 1))) := by
      rw [hv', hval]; exact min_step _ _ _
    have e2 : (md * 10 + d) % 400 = value (seg a S (i + 1)) % 400 := by rw [hv', hmd]; omega
    rw [e1, e2] at h
    exact ⟨h, by omega, by omega, hall', rfl, rfl⟩
  · have hd' : isDigit a[i]! = false := by simpa using hd
    refine fragR_ifF o rfl (lowK_any _ (k := .skip) rfl) (lowKK_ret rfl) rfl rfl (fun u k h =>
      ⟨runF_clock _ _ _ u k h.1, h.2⟩) (fun u h => (evd u h).trans (by rw [hd'])) ?_
    refine fragR_ret o rfl fun u h => ⟨_, rfl, ?_⟩
    show match number? (seg a S E) with
      | some n => _ | none => _
    rw [num_none hE hSi hi hd']
    exact ⟨rfl, h.2⟩

/-- **`artNum` reads the number the digits from `S` to `E` write**, as `number?` does, at most `yearBig`, if it
returns. -/
theorem artNum_ok (o : Oracle σ) {A : Word} {s1 : PancakeState σ} (hA : Area ArticleProg.ofs A s1)
    (hD : ArtDom A s1.memaddrs) {a : Bytes} (hlen : a.length ≤ artMax) (hin : InputAt s1.memory s1.memaddrs s1.be A a)
    {S E : Nat} (hS : S ≤ artMax) (hE : E ≤ a.length) (hs : s1.locals "s" = some (BitVec.ofNat 64 S))
    (he : s1.locals "e" = some (BitVec.ofNat 64 E)) :
    ∃ body, Lower.lower (gd ArticleProg.artNum) = some body ∧
      SafeR o (fun s => s = s1) body (NumRet A a S E s1.memory) fun _ => False := by
  have hM := artMax_eq
  have hEM : E ≤ artMax := by omega
  refine body_of ?_
  show FragR o _ (guardL ArticleProg.artNum.body) _ _
  rw [artNum_body]
  obtain ⟨EA, hEA⟩ := atOff_lower ArticleProg.ofs
  refine fragR_conseq (P0 := RunF s1 [("s", BitVec.ofNat 64 S), ("e", BitVec.ofNat 64 E)] (· = s1.memory))
    ?_ (entry_two hs he) fun _ h => h
  refine fragR_append (xs := [_]) (fragR_of (runF_dec o hEA rfl (v := A) fun u h => areaAt_eval hA h.1.base hEA)) ?_
  have hev : ∀ u, RunF s1 [("a", A), ("s", BitVec.ofNat 64 S), ("e", BitVec.ofNat 64 E)] (· = s1.memory) u →
      eval u (FramerCode.leE (.var "e") (.var "s")) = some (bw (decide (E ≤ S))) := fun u h =>
    FramerCode.eval_le (by omega) (by omega) (ev_var (vals_lookup h.1.vals rfl)) (ev_var (vals_lookup h.1.vals rfl))
  by_cases hES : E ≤ S
  · refine fragR_append (xs := [_]) (fragR_ifT o rfl (lowKK_ret rfl) lowKK_nil rfl rfl (Q := fun _ => False)
      (fun _ _ h => h) (fun u h => (hev u h).trans (by rw [bw_t hES])) ?_)
      (fragR_of (frag_unsat (lowK_any _ (k := .skip) rfl) fun _ h => h))
    refine fragR_ret o rfl fun u h => ⟨_, rfl, ?_⟩
    show match number? (seg a S E) with
      | some n => _ | none => _
    rw [seg_over a hES]
    exact ⟨rfl, h.2⟩
  refine fragR_append (xs := [_]) (fragR_ifF o rfl (lowKK_ret rfl) lowKK_nil rfl rfl (runF_clock _ _ _)
    (fun u h => (hev u h).trans (by rw [bw_f hES])) (fragR_of (frag_nil o fun _ h => h))) ?_
  refine fragR_append (xs := [_]) (fragR_of (runF_dec o rfl rfl (v := BitVec.ofNat 64 S) fun u h =>
    ev_var (vals_lookup h.1.vals rfl))) ?_
  refine fragR_append (xs := [_]) (fragR_of (runF_dec o rfl rfl (v := BitVec.ofNat 64 0) fun _ _ => rfl)) ?_
  refine fragR_append (xs := [_]) (fragR_of (runF_dec o rfl rfl (v := BitVec.ofNat 64 0) fun _ _ => rfl)) ?_
  let I : Assn σ := fun u => ∃ t : Nat × Nat × Nat, RunF s1 (numL S E A t.1 t.2.1 t.2.2) (· = s1.memory) u ∧
    NumInv a S E t.1 t.2.1 t.2.2
  have hIc : Safe.ClockFree I := fun u k ⟨t, h, hv⟩ => ⟨t, runF_clock _ _ _ u k h, hv⟩
  have hcond : ∀ u (t : Nat × Nat × Nat), RunF s1 (numL S E A t.1 t.2.1 t.2.2) (· = s1.memory) u →
      NumInv a S E t.1 t.2.1 t.2.2 →
      eval u (.cmp .less (.var "i") (.var "e")) = some (bw (decide (t.1 < E))) := fun u t h hq =>
    FramerCode.eval_lt (by have := hq.2.1; omega) (by omega) (ev_var (vals_lookup h.1.vals rfl))
      (ev_var (vals_lookup h.1.vals rfl))
  have hlow : LowKK numBody := lowK_any _ (k := .skip) rfl
  refine fragR_append (xs := [_]) (fragR_conseq (fragR_while o rfl hlow hIc
    (fun u z v ⟨t, h, hv⟩ hz => by
      change z ∈ ["b"] at hz
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hz; subst hz
      exact ⟨t, runF_restore h rfl v, hv⟩) (fun u ⟨t, h, hv⟩ => ⟨_, hcond u t h hv⟩) ?_)
    (fun u h => ⟨(S, 0, 0), h, Nat.le_refl _, by omega, by simp [DN.News.ArticleLines.seg_self],
      by simp [DN.News.ArticleLines.seg_self, value], by simp [DN.News.ArticleLines.seg_self, value]⟩)
    fun _ h => h) ?_
  · refine fragR_conseq (P0 := fun u => ∃ t : Nat × Nat × Nat, (fun t u => RunF s1 (numL S E A t.1 t.2.1 t.2.2)
      (· = s1.memory) u ∧ NumInv a S E t.1 t.2.1 t.2.2 ∧ t.1 < E) t u) (fragR_exists hlow fun t => ?_)
      (fun u ⟨⟨t, h, hv⟩, h0⟩ => ⟨t, h, hv, by
        rw [hcond u t h hv] at h0; exact of_decide_eq_true (bw_ne0 h0)⟩) fun _ h => h
    refine fragR_pure (NumInv a S E t.1 t.2.1 t.2.2 ∧ t.1 < E) (fun u h => h.2) hlow fun ⟨hq, hi⟩ => ?_
    exact fragR_conseq (num_body o hin hE hEM hq hi) (fun u h => h.1) fun u h => ⟨(_, _, _), h.1, h.2⟩
  have hlow2 : LowKK [ArticleProg.setW ArticleProg.xNumMod (Syntax.v "md"), .ret (Syntax.v "val")] :=
    lowK_any _ (k := .skip) rfl
  refine fragR_conseq (P0 := fun u => ∃ t : Nat × Nat × Nat, (fun t u => RunF s1 (numL S E A t.1 t.2.1 t.2.2)
    (· = s1.memory) u ∧ NumInv a S E t.1 t.2.1 t.2.2 ∧ E ≤ t.1) t u) (fragR_exists hlow2 fun t => ?_)
    (fun u ⟨⟨t, h, hv⟩, h0⟩ => ⟨t, h, hv, by
      rw [hcond u t h hv] at h0; have := of_decide_eq_false (bw_eq0 h0); omega⟩) fun _ h => h
  refine fragR_pure (NumInv a S E t.1 t.2.1 t.2.2 ∧ E ≤ t.1) (fun u h => h.2) hlow2 fun ⟨hq, hge⟩ => ?_
  obtain ⟨-, hiE, hall, hval, hmd⟩ := hq
  have hiE' : t.1 = E := by omega
  rw [hiE'] at hall hval hmd
  refine fragR_append (xs := [_]) (fragR_of (frag_conseq (runF_storeA o (atOffW_lower 25) rfl (y := ArticleProg.w 25)
    (artDom_w hD (by decide)) (fun u h => atA_eval (vals_lookup h.1.vals rfl)) (val := fun _ => BitVec.ofNat 64 t.2.2)
    (fun u h => ev_var (vals_lookup h.1.vals rfl))
    (G := (· = upd s1.memory (at_ A ArticleProg.xNumMod) (BitVec.ofNat 64 t.2.2))) fun m hm => by subst hm; rfl)
    (fun u h => h.1) fun _ h => h)) ?_
  refine fragR_ret o rfl fun u h => ⟨_, ev_var (vals_lookup h.1.vals rfl), ?_⟩
  have hne : (seg a S E).isEmpty = false := by
    have := seg_length a (show S ≤ E by omega) hE
    cases hc : seg a S E with
    | nil => rw [hc] at this; simp at this; omega
    | cons _ _ => rfl
  show match number? (seg a S E) with
    | some n => _ | none => _
  rw [show number? (seg a S E) = some (value (seg a S E)) by simp [number?, hne, hall]]
  exact ⟨by rw [hval], by rw [h.2, hmd]⟩

/-! ## The next word -/

open DN.News.ArticleSpec (tokens)
open DN.News.CommandSpec (isWS wordsFrom words)

/-- A byte between words: white space or a line end. -/
def gap (b : BitVec 8) : Bool := isWS b || b == DN.News.FrameSpec.CR || b == DN.News.FrameSpec.LF

theorem gap_bytes (b : BitVec 8) :
    ((decide (b.toNat = 32) || decide (b.toNat = 9)) || (decide (b.toNat = 13) || decide (b.toNat = 10))) = gap b := by
  revert b; decide

/-- Where the next word starts from `P`: past the gaps, or at `E`. -/
def wordStart (a : Bytes) (P E : Nat) : Nat := P + ((seg a P E).takeWhile gap).length

/-- Where the word from `S` ends: at the next gap, or at `E`. -/
def wordEnd (a : Bytes) (S E : Nat) : Nat := S + ((seg a S E).takeWhile (!gap ·)).length

theorem tw_len {α : Type} {p : α → Bool} : ∀ (l : List α) (k : Nat), k ≤ l.length → (l.take k).all p = true →
    (∀ h : k < l.length, p l[k] = false) → (l.takeWhile p).length = k
  | [], k, hk, _, _ => by simp only [List.length_nil, Nat.le_zero] at hk; simp [hk]
  | x :: l, 0, _, _, hs => by
    have h0 : p x = false := hs (by simp)
    simp [List.takeWhile, h0]
  | x :: l, k + 1, hk, ha, hs => by
    simp only [List.take_succ_cons, List.all_cons, Bool.and_eq_true] at ha
    simp only [List.takeWhile, ha.1, List.length_cons]
    rw [tw_len l k (by simp at hk; omega) ha.2 fun h => hs (by simp; omega)]

theorem seg_drop (a : Bytes) (P k E : Nat) : (seg a P E).drop k = seg a (P + k) E := by
  simp only [seg, List.drop_take, List.drop_drop]; congr 1; omega

/-- The loop's stop at the first byte for which `p` fails: the run of bytes for which it holds. -/
theorem seg_tw {a : Bytes} {p : BitVec 8 → Bool} {P i E : Nat} (hE : E ≤ a.length) (h1 : P ≤ i) (h2 : i ≤ E)
    (hall : (seg a P i).all p = true) (hstop : i = E ∨ p a[i]! = false) :
    P + ((seg a P E).takeWhile p).length = i := by
  rw [tw_len (seg a P E) (i - P) (by rw [seg_length a (by omega) hE]; omega)
    (by rw [DN.News.ArticleLines.seg_take a (i - P) (by omega), show P + (i - P) = i by omega]; exact hall)
    fun h => ?_]
  · omega
  · rcases hstop with rfl | hs
    · rw [seg_length a (by omega) hE] at h; omega
    · have hiE : i < E := by rw [seg_length a (by omega) hE] at h; omega
      have hg := DN.News.ArticleLines.seg_get a (x := P) (e := E) (i := i - P) (by omega)
      rw [show P + (i - P) = i by omega, List.getElem?_eq_getElem h, List.getElem?_eq_getElem (by omega)] at hg
      rw [Option.some.inj hg, ← getElem!_pos a i (by omega)]; exact hs

/-- A line end read as white space, as `tokens` reads it. -/
def fm (b : BitVec 8) : BitVec 8 :=
  if (b == DN.News.FrameSpec.CR || b == DN.News.FrameSpec.LF) = true then DN.News.CommandSpec.SP else b

theorem tokens_fm (v : Bytes) : tokens v = words (v.map fm) := rfl

theorem f_gap (b : BitVec 8) : isWS (fm b) = gap b := by revert b; decide

theorem f_word {b : BitVec 8} (h : gap b = false) : fm b = b := by revert h; revert b; decide

theorem wf_gaps : ∀ (G rest : Bytes), G.all gap = true → wordsFrom (G.map fm ++ rest) [] = wordsFrom rest []
  | [], _, _ => rfl
  | g :: G, rest, h => by
    simp only [List.all_cons, Bool.and_eq_true] at h
    simp only [List.map_cons, List.cons_append, wordsFrom, f_gap, h.1, if_true, List.isEmpty_nil]
    exact wf_gaps G rest h.2

theorem wf_word : ∀ (W rest cur : Bytes), W.all (!gap ·) = true →
    wordsFrom (W.map fm ++ rest) cur = wordsFrom rest (W.reverse ++ cur)
  | [], _, _, _ => rfl
  | w :: W, rest, cur, h => by
    simp only [List.all_cons, Bool.and_eq_true, Bool.not_eq_true'] at h
    have hw : isWS w = false := by have := h.1; simp only [gap, Bool.or_eq_false_iff] at this; exact this.1.1
    simp only [List.map_cons, List.cons_append, wordsFrom, f_word h.1, hw, Bool.false_eq_true, if_false]
    rw [wf_word W rest (w :: cur) h.2, List.reverse_cons, List.append_assoc, List.singleton_append]

theorem head_dw {p : BitVec 8 → Bool} : ∀ {l : Bytes} {d : BitVec 8} {D : Bytes}, l.dropWhile p = d :: D → p d = false
  | [], _, _, h => by simp at h
  | x :: l, d, D, h => by
    cases hx : p x
    · simp only [List.dropWhile, hx] at h; cases h; exact hx
    · simp only [List.dropWhile, hx] at h; exact head_dw h

theorem drop_tw {p : BitVec 8 → Bool} (l : Bytes) : l.drop (l.takeWhile p).length = l.dropWhile p :=
  calc l.drop (l.takeWhile p).length = (l.takeWhile p ++ l.dropWhile p).drop (l.takeWhile p).length := by
        rw [List.takeWhile_append_dropWhile]
    _ = l.dropWhile p := List.drop_left

theorem tw_le {p : BitVec 8 → Bool} : ∀ l : Bytes, (l.takeWhile p).length ≤ l.length
  | [] => Nat.le_refl _
  | x :: l => by
    cases h : p x
    · simp [List.takeWhile, h]
    · have := tw_le (p := p) l; simp [List.takeWhile, h]; omega

/-- **The next word and those after it**, as `tokens` reads the bytes from `P` to `E`. -/
theorem tokens_next {a : Bytes} {P E : Nat} (hPE : P ≤ E) (hE : E ≤ a.length) :
    tokens (seg a P E) = if wordStart a P E = E then [] else
      seg a (wordStart a P E) (wordEnd a (wordStart a P E) E) :: tokens (seg a (wordEnd a (wordStart a P E) E) E) := by
  generalize hl : seg a P E = l
  have hll : l.length = E - P := by rw [← hl, seg_length a hPE hE]
  have hS : seg a (wordStart a P E) E = l.dropWhile gap := by
    unfold wordStart; rw [← seg_drop, hl, drop_tw]
  rw [tokens_fm, ← List.takeWhile_append_dropWhile (p := gap) (l := l), List.map_append]
  show wordsFrom _ [] = _
  rw [wf_gaps _ _ List.all_takeWhile]
  cases hD : l.dropWhile gap with
  | nil =>
    have : wordStart a P E = E := by
      unfold wordStart
      have := List.takeWhile_append_dropWhile (p := gap) (l := l)
      rw [hD, List.append_nil] at this
      rw [hl, this]; omega
    rw [if_pos this]; rfl
  | cons d D =>
    have hd := head_dw hD
    have hne : wordStart a P E ≠ E := by
      intro e
      have h1 := seg_length a (show wordStart a P E ≤ E by omega) hE
      rw [hS, hD, e] at h1; simp at h1
    rw [if_neg hne]
    generalize hS' : wordStart a P E = S' at hS hne ⊢
    have hSE : S' ≤ E := by
      rw [← hS']; unfold wordStart
      have := tw_le (p := gap) (seg a P E); rw [hl] at this ⊢; omega
    rw [hD] at hS
    generalize hD0 : d :: D = D0 at hS
    have hW : seg a S' (wordEnd a S' E) = D0.takeWhile (!gap ·) := by
      have hle := tw_le (p := (!gap ·)) D0
      have h2 := seg_length a hSE hE; rw [hS] at h2
      unfold wordEnd
      rw [hS, ← DN.News.ArticleLines.seg_take a _ (show (D0.takeWhile (!gap ·)).length ≤ E - S' by omega), hS,
        ← DN.News.ArticleLines.takeWhile_take]
    have hR : seg a (wordEnd a S' E) E = D0.dropWhile (!gap ·) := by
      unfold wordEnd; rw [← seg_drop, hS, drop_tw]
    rw [hW, hR, ← hD0]
    have hd' : (!gap d) = true := by simp [hd]
    generalize hR' : (d :: D).dropWhile (!gap ·) = R
    have hsp := List.takeWhile_append_dropWhile (p := (!gap ·)) (l := d :: D)
    rw [hR'] at hsp
    conv => lhs; rw [← hsp]
    rw [List.map_append, wf_word _ _ _ List.all_takeWhile, List.append_nil]
    have hWne : ((d :: D).takeWhile (!gap ·)).reverse.isEmpty = false := by
      simp [List.takeWhile, hd']
    cases R with
    | nil => simp only [List.map_nil, wordsFrom, hWne, List.reverse_reverse, Bool.false_eq_true, if_false]; rfl
    | cons r R'' =>
      have hr : gap r = true := by have := head_dw hR'; simpa using this
      rw [tokens_fm]
      simp only [List.map_cons, words, wordsFrom, f_gap, hr, if_true, hWne, Bool.false_eq_true, if_false,
        List.reverse_reverse, List.isEmpty_nil]

/-- A word found has a byte at least: `xTokLen` is 0 only when no word is left. -/
theorem wordEnd_gt {a : Bytes} {P E : Nat} (hE : E ≤ a.length) (h : wordStart a P E < E) :
    wordStart a P E < wordEnd a (wordStart a P E) E := by
  have hS : seg a (wordStart a P E) E = (seg a P E).dropWhile gap := by unfold wordStart; rw [← seg_drop, drop_tw]
  have hlen := seg_length a (Nat.le_of_lt h) hE
  unfold wordEnd
  rw [hS] at hlen ⊢
  cases hD : (seg a P E).dropWhile gap with
  | nil => rw [hD] at hlen; simp at hlen; omega
  | cons d D =>
    have hd := head_dw hD
    simp [List.takeWhile, hd]

/-! ### The program -/

theorem xTok_eq : ArticleProg.xTok = 506672 := rfl

theorem atOffTok_lower : Lower.lowerExp (Syntax.atOff (Syntax.v "a") ArticleProg.xTok) =
    some (.op .add (.var "a") (.const (BitVec.ofNat 64 ArticleProg.xTok))) := by
  simp only [Syntax.atOff, xTok_eq]; rfl

/-- `artTok`'s first loop body: past the gaps. -/
def tokBody1 : List Syntax.PStmt :=
  [.ite (Syntax.eLt (Syntax.v "i") (Syntax.v "e"))
    (ArticleProg.readIn "b" "i" ++ [.ite (ArticleProg.isGap (Syntax.v "b")) [inc "i"] [.assign "go" (Syntax.n 0)]])
    [.assign "go" (Syntax.n 0)]]

/-- `artTok`'s second loop body: the word, its first eight bytes kept. -/
def tokBody2 : List Syntax.PStmt :=
  [.ite (Syntax.eLt (Syntax.v "i") (Syntax.v "e"))
    (ArticleProg.readIn "c" "i" ++
      [.ite (ArticleProg.isGap (Syntax.v "c")) [.assign "go" (Syntax.n 0)]
        [ArticleProg.ifs (Syntax.eLt (Syntax.v "ln") (Syntax.n 8))
          [.storeb (Syntax.eAdd (Syntax.atOff (Syntax.v "a") ArticleProg.xTok) (Syntax.v "ln")) (Syntax.v "c")],
         ArticleProg.ifs (Syntax.eLt (Syntax.v "ln") (Syntax.n artMax)) [inc "ln"], inc "i"]])
    [.assign "go" (Syntax.n 0)]]

theorem artTok_body : guardL ArticleProg.artTok.body =
    [areaAt ArticleProg.ofs, .dec "i" (Syntax.v "p"), .dec "go" (Syntax.n 1), .while (Syntax.v "go") tokBody1,
     ArticleProg.setW ArticleProg.xTokS (Syntax.v "i"), .dec "ln" (Syntax.n 0), .assign "go" (Syntax.n 1),
     .while (Syntax.v "go") tokBody2, ArticleProg.setW ArticleProg.xTokLen (Syntax.v "ln"), .ret (Syntax.v "i")] := rfl

def tokL1 (P E : Nat) (A : Word) (g i : Nat) : List (String × Value) :=
  [("go", BitVec.ofNat 64 g), ("i", BitVec.ofNat 64 i), ("a", A), ("p", BitVec.ofNat 64 P), ("e", BitVec.ofNat 64 E)]

def tokL2 (P E : Nat) (A : Word) (g ln i : Nat) : List (String × Value) :=
  [("go", BitVec.ofNat 64 g), ("ln", BitVec.ofNat 64 ln), ("i", BitVec.ofNat 64 i), ("a", A),
   ("p", BitVec.ofNat 64 P), ("e", BitVec.ofNat 64 E)]

theorem runF_tokL1 {s0 u : PancakeState σ} {l : List (String × Value)} {F : (Word → Word) → Prop}
    (h : RunF s0 l F u) {P E : Nat} {A : Word} {g i : Nat}
    (h1 : l.lookup "go" = some (BitVec.ofNat 64 g)) (h2 : l.lookup "i" = some (BitVec.ofNat 64 i))
    (h3 : l.lookup "a" = some A) (h4 : l.lookup "p" = some (BitVec.ofNat 64 P))
    (h5 : l.lookup "e" = some (BitVec.ofNat 64 E)) : RunF s0 (tokL1 P E A g i) F u :=
  ⟨⟨fun q hq => by
    simp only [tokL1, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    all_goals first | exact vals_lookup h.1.vals h1 | exact vals_lookup h.1.vals h2 | exact vals_lookup h.1.vals h3 |
      exact vals_lookup h.1.vals h4 | exact vals_lookup h.1.vals h5,
    h.1.memaddrs, h.1.base, h.1.code, h.1.be⟩, h.2⟩

theorem runF_tokL2 {s0 u : PancakeState σ} {l : List (String × Value)} {F : (Word → Word) → Prop}
    (h : RunF s0 l F u) {P E : Nat} {A : Word} {g ln i : Nat}
    (h1 : l.lookup "go" = some (BitVec.ofNat 64 g)) (h2 : l.lookup "ln" = some (BitVec.ofNat 64 ln))
    (h3 : l.lookup "i" = some (BitVec.ofNat 64 i)) (h4 : l.lookup "a" = some A)
    (h5 : l.lookup "p" = some (BitVec.ofNat 64 P)) (h6 : l.lookup "e" = some (BitVec.ofNat 64 E)) :
    RunF s0 (tokL2 P E A g ln i) F u :=
  ⟨⟨fun q hq => by
    simp only [tokL2, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first | exact vals_lookup h.1.vals h1 | exact vals_lookup h.1.vals h2 | exact vals_lookup h.1.vals h3 |
      exact vals_lookup h.1.vals h4 | exact vals_lookup h.1.vals h5 | exact vals_lookup h.1.vals h6,
    h.1.memaddrs, h.1.base, h.1.code, h.1.be⟩, h.2⟩

theorem gap_eval {u : PancakeState σ} {x : String} {b : BitVec 8} (h : u.locals x = some (BitVec.ofNat 64 b.toNat)) :
    eval u (.op .or_ (.op .or_ (.cmp .equal (.var x) (.const (BitVec.ofNat 64 32)))
      (.cmp .equal (.var x) (.const (BitVec.ofNat 64 9))))
      (.op .or_ (.cmp .equal (.var x) (.const (BitVec.ofNat 64 13)))
        (.cmp .equal (.var x) (.const (BitVec.ofNat 64 10))))) = some (bw (gap b)) := by
  have hb := b.isLt
  rw [← gap_bytes, ← DN.News.AbnfComment.bw_or, ← DN.News.AbnfComment.bw_or, ← DN.News.AbnfComment.bw_or]
  exact FramerCode.eval_or (FramerCode.eval_or (FramerCode.eval_eq (by omega) (by decide) (ev_var h) rfl)
    (FramerCode.eval_eq (by omega) (by decide) (ev_var h) rfl))
    (FramerCode.eval_or (FramerCode.eval_eq (by omega) (by decide) (ev_var h) rfl)
      (FramerCode.eval_eq (by omega) (by decide) (ev_var h) rfl))

/-- What `artTok` gives back: the end of the next word. Its start goes in `xTokS`, its length in `xTokLen`, its first
eight bytes from `xTok`. -/
def TokRet (A : Word) (be : Bool) (a : Bytes) (P E : Nat) (m0 : Word → Word) : Ret := fun v m =>
  v = BitVec.ofNat 64 (wordEnd a (wordStart a P E) E) ∧
    m = upd (putB (upd m0 (at_ A ArticleProg.xTokS) (BitVec.ofNat 64 (wordStart a P E))) be A ArticleProg.xTok
      ((seg a (wordStart a P E) (wordEnd a (wordStart a P E) E)).take 8)) (at_ A ArticleProg.xTokLen)
      (BitVec.ofNat 64 (wordEnd a (wordStart a P E) E - wordStart a P E))

theorem flag01 {g : Nat} (h : g = 1 ∨ g = 0) (h0 : BitVec.ofNat 64 g ≠ 0) : g = 1 := by
  rcases h with h | h
  · exact h
  · subst h; exact absurd rfl h0

/-- **`artTok`'s first loop goes past the gaps** to where the next word starts. -/
theorem tok_loop1 (o : Oracle σ) {A : Word} {s1 : PancakeState σ} {a : Bytes}
    (hin : InputAt s1.memory s1.memaddrs s1.be A a) {P E : Nat} (hPE : P ≤ E) (hE : E ≤ a.length) (hEM : E ≤ artMax) :
    Frag o [.while (Syntax.v "go") tokBody1] (RunF s1 (tokL1 P E A 1 P) (· = s1.memory))
      (RunF s1 (tokL1 P E A 0 (wordStart a P E)) (· = s1.memory)) := by
  have hM := artMax_eq
  let I : Assn σ := fun u => ∃ t : Nat × Nat, RunF s1 (tokL1 P E A t.1 t.2) (· = s1.memory) u ∧ P ≤ t.2 ∧ t.2 ≤ E ∧
    (seg a P t.2).all gap = true ∧ (t.1 = 1 ∨ t.1 = 0 ∧ (t.2 = E ∨ gap a[t.2]! = false))
  have hIc : Safe.ClockFree I := fun u k ⟨t, h, hv⟩ => ⟨t, runF_clock _ _ _ u k h, hv⟩
  have hlow : LowKK tokBody1 := lowK_any _ (k := .skip) rfl
  refine frag_conseq (frag_while o rfl hlow hIc (fun _ _ _ _ hy => by cases hy)
    (fun u ⟨t, h, _⟩ => ⟨_, ev_var (vals_lookup h.1.vals rfl)⟩) ?_)
    (fun u h => ⟨(1, P), h, Nat.le_refl _, hPE, by simp [DN.News.ArticleLines.seg_self], .inl rfl⟩) ?_
  · refine frag_conseq (P0 := fun u => ∃ t : Nat × Nat, (fun t u => RunF s1 (tokL1 P E A t.1 t.2) (· = s1.memory) u ∧
      P ≤ t.2 ∧ t.2 ≤ E ∧ (seg a P t.2).all gap = true ∧ t.1 = 1) t u) (frag_exists hlow fun t => ?_)
      (fun u ⟨⟨t, h, h1, h2, h3, h4⟩, h0⟩ => ⟨t, h, h1, h2, h3, flag01 (h4.imp_right fun h => h.1) (by
        rw [ev_var (vals_lookup h.1.vals rfl)] at h0; exact fun e => h0 (by rw [e]))⟩) fun _ h => h
    refine frag_pure (P ≤ t.2 ∧ t.2 ≤ E ∧ (seg a P t.2).all gap = true ∧ t.1 = 1) (fun u h => h.2) hlow
      fun ⟨h1, h2, h3, h4⟩ => ?_
    obtain ⟨g, i⟩ := t
    simp only at h1 h2 h3 h4; subst h4
    refine frag_conseq (P0 := RunF s1 (tokL1 P E A 1 i) (· = s1.memory)) ?_ (fun u h => h.1) fun _ h => h
    refine DN.News.ArticleRun.frag_ifR o rfl (lowK_any _ (k := .skip) rfl) (lowK_any _ (k := .skip) rfl) hIc
      (fun u y v ⟨t, h, hv⟩ hy => by
        change y ∈ ["b"] at hy
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hy; subst hy
        exact ⟨t, runF_restore h rfl v, hv⟩) (fun _ _ _ _ hy => by cases hy) (b := decide (i < E))
      (fun u h => FramerCode.eval_lt (by omega) (by omega) (ev_var (vals_lookup h.1.vals rfl))
        (ev_var (vals_lookup h.1.vals rfl))) (fun hi => ?_) fun hi => ?_
    · have hi' : i < E := of_decide_eq_true hi
      have hia : i < a.length := by omega
      refine frag_append (xs := [_, _]) (frag_append (xs := [_]) (kept_frag o (by decide) (runF_clock _ _ _)
        fun u h => ⟨i, vals_lookup h.1.vals rfl, by omega⟩) (runF_dec o rfl rfl (v := BitVec.ofNat 64 (a[i]!).toNat)
          fun u h => inByte_eval (input_run hin h) (vals_lookup h.1.vals rfl) hia (vals_lookup h.1.vals rfl))) ?_
      refine DN.News.ScanRun.frag_if o rfl (lowK_any _ (k := .skip) rfl) (lowK_any _ (k := .skip) rfl) rfl rfl hIc
        (b := gap a[i]!) (fun u h => gap_eval (vals_lookup h.1.vals rfl)) (fun hg => ?_) fun hg => ?_
      · refine frag_conseq (runF_set o rfl rfl (v := BitVec.ofNat 64 (i + 1)) fun u h =>
          ev_inc (vals_lookup h.1.vals rfl)) (fun _ h => h) fun u h => ⟨(1, i + 1),
            runF_tokL1 h rfl rfl rfl rfl rfl, by omega, by omega, ?_, .inl rfl⟩
        rw [seg_succ a h1 hia, List.all_append, h3, List.all_cons, ← getElem!_pos a i hia, hg]; rfl
      · refine frag_conseq (runF_set o rfl rfl (v := BitVec.ofNat 64 0) fun _ _ => rfl) (fun _ h => h)
          fun u h => ⟨(0, i), runF_tokL1 h rfl rfl rfl rfl rfl, h1, h2, h3, .inr ⟨rfl, .inr hg⟩⟩
    · have hi' : ¬i < E := fun e => by simp [e] at hi
      exact frag_conseq (runF_set o rfl rfl (v := BitVec.ofNat 64 0) fun _ _ => rfl) (fun _ h => h)
        fun u h => ⟨(0, i), runF_tokL1 h rfl rfl rfl rfl rfl, h1, h2, h3, .inr ⟨rfl, .inl (by omega)⟩⟩
  · intro u ⟨⟨t, h, h1, h2, h3, h4⟩, h0⟩
    rw [ev_var (vals_lookup h.1.vals rfl)] at h0
    rcases h4 with e | ⟨e, hs⟩
    · rw [e] at h0; exact absurd (Option.some.inj h0) (by decide)
    · obtain ⟨g, i⟩ := t
      simp only at e h1 h2 h3 hs h; subst e
      rw [← seg_tw hE h1 h2 h3 hs] at h; exact h

/-- **`artTok`'s second loop reads the word** to its end, its first eight bytes put from `xTok`. -/
theorem tok_loop2 (o : Oracle σ) {A : Word} {s1 : PancakeState σ} (hA : Area ArticleProg.ofs A s1)
    (hD : ArtDom A s1.memaddrs) {a : Bytes} (hlen : a.length ≤ artMax) (hin : InputAt s1.memory s1.memaddrs s1.be A a)
    {P E S : Nat} (hSE : S ≤ E) (hE : E ≤ a.length) {M1 : Word → Word}
    (hM1 : ∀ x, x < aSets → M1 (at_ A x) = s1.memory (at_ A x)) :
    Frag o [.while (Syntax.v "go") tokBody2] (RunF s1 (tokL2 P E A 1 0 S) (· = M1))
      (RunF s1 (tokL2 P E A 0 (wordEnd a S E - S) (wordEnd a S E))
        (· = putB M1 s1.be A ArticleProg.xTok ((seg a S (wordEnd a S E)).take 8))) := by
  have hM := artMax_eq
  have hEM : E ≤ artMax := by omega
  have hT := xTok_eq; have hX := X_val; have hF := xFirst_eq; have hsets := sets_le_X
  let Mt : Nat → Word → Word := fun i => putB M1 s1.be A ArticleProg.xTok ((seg a S i).take 8)
  have hinM : ∀ i, InputAt (Mt i) s1.memaddrs s1.be A a := fun i => input_keep hA.hA hlen hin fun x hx => by
    show putB M1 s1.be A ArticleProg.xTok _ (at_ A x) = _
    rw [putB_other s1.be hA.hA _ M1 _ x (by omega) (by have := List.length_take_le 8 (seg a S i); omega), hM1 x hx]
  let I : Assn σ := fun u => ∃ t : Nat × Nat, RunF s1 (tokL2 P E A t.1 (t.2 - S) t.2) (· = Mt t.2) u ∧ S ≤ t.2 ∧
    t.2 ≤ E ∧ (seg a S t.2).all (!gap ·) = true ∧ (t.1 = 1 ∨ t.1 = 0 ∧ (t.2 = E ∨ (!gap a[t.2]!) = false))
  have hIc : Safe.ClockFree I := fun u k ⟨t, h, hv⟩ => ⟨t, runF_clock _ _ _ u k h, hv⟩
  have hlow : LowKK tokBody2 := lowK_any _ (k := .skip) rfl
  refine frag_conseq (frag_while o rfl hlow hIc (fun _ _ _ _ hy => by cases hy)
    (fun u ⟨t, h, _⟩ => ⟨_, ev_var (vals_lookup h.1.vals rfl)⟩) ?_)
    (fun u h => ⟨(1, S), by
      show RunF s1 (tokL2 P E A 1 (S - S) S) (· = putB M1 s1.be A ArticleProg.xTok ((seg a S S).take 8)) u
      rw [Nat.sub_self, DN.News.ArticleLines.seg_self, List.take_nil]; exact h, Nat.le_refl _, hSE,
      by simp [DN.News.ArticleLines.seg_self], .inl rfl⟩) ?_
  · refine frag_conseq (P0 := fun u => ∃ t : Nat × Nat, (fun t u => RunF s1 (tokL2 P E A t.1 (t.2 - S) t.2)
      (· = Mt t.2) u ∧ S ≤ t.2 ∧ t.2 ≤ E ∧ (seg a S t.2).all (!gap ·) = true ∧ t.1 = 1) t u)
      (frag_exists hlow fun t => ?_)
      (fun u ⟨⟨t, h, h1, h2, h3, h4⟩, h0⟩ => ⟨t, h, h1, h2, h3, flag01 (h4.imp_right fun h => h.1) (by
        rw [ev_var (vals_lookup h.1.vals rfl)] at h0; exact fun e => h0 (by rw [e]))⟩) fun _ h => h
    refine frag_pure (S ≤ t.2 ∧ t.2 ≤ E ∧ (seg a S t.2).all (!gap ·) = true ∧ t.1 = 1) (fun u h => h.2) hlow
      fun ⟨h1, h2, h3, h4⟩ => ?_
    obtain ⟨g, i⟩ := t
    simp only at h1 h2 h3 h4; subst h4
    refine frag_conseq (P0 := RunF s1 (tokL2 P E A 1 (i - S) i) (· = Mt i)) ?_ (fun u h => h.1) fun _ h => h
    refine DN.News.ArticleRun.frag_ifR o rfl (lowK_any _ (k := .skip) rfl) (lowK_any _ (k := .skip) rfl) hIc
      (fun u y v ⟨t, h, hv⟩ hy => by
        change y ∈ ["c"] at hy
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hy; subst hy
        exact ⟨t, runF_restore h rfl v, hv⟩) (fun _ _ _ _ hy => by cases hy) (b := decide (i < E))
      (fun u h => FramerCode.eval_lt (by omega) (by omega) (ev_var (vals_lookup h.1.vals rfl))
        (ev_var (vals_lookup h.1.vals rfl))) (fun hi => ?_) fun hi => ?_
    · have hi' : i < E := of_decide_eq_true hi
      have hia : i < a.length := by omega
      refine frag_append (xs := [_, _]) (frag_append (xs := [_]) (kept_frag o (by decide) (runF_clock _ _ _)
        fun u h => ⟨i, vals_lookup h.1.vals rfl, by omega⟩) (runF_dec o rfl rfl (v := BitVec.ofNat 64 (a[i]!).toNat)
          fun u h => inByte_eval (input_run (hinM i) h) (vals_lookup h.1.vals rfl) hia
            (vals_lookup h.1.vals rfl))) ?_
      let LB : Nat → List (String × Value) := fun ln =>
        ("c", BitVec.ofNat 64 (a[i]!).toNat) :: tokL2 P E A 1 ln i
      refine DN.News.ScanRun.frag_if o rfl (lowK_any _ (k := .skip) rfl) (lowK_any _ (k := .skip) rfl) rfl rfl hIc
        (b := gap a[i]!) (fun u h => gap_eval (vals_lookup h.1.vals rfl)) (fun hg => ?_) fun hg => ?_
      · exact frag_conseq (runF_set o rfl rfl (v := BitVec.ofNat 64 0) fun _ _ => rfl) (fun _ h => h)
          fun u h => ⟨(0, i), runF_tokL2 h rfl rfl rfl rfl rfl rfl, h1, h2, h3, .inr ⟨rfl, .inr (by rw [hg]; rfl)⟩⟩
      have hseg : (seg a S i).length = i - S := seg_length a h1 (by omega)
      have hnext : (seg a S (i + 1)) = seg a S i ++ [a[i]!] := by rw [seg_succ a h1 hia, getElem!_pos a i hia]
      refine frag_append (xs := [_]) (M := RunF s1 (LB (i - S)) (· = Mt (i + 1))) ?_ ?_
      · have hlt : ∀ u, RunF s1 (LB (i - S)) (· = Mt i) u →
            eval u (.cmp .less (.var "ln") (.const (BitVec.ofNat 64 8))) = some (bw (decide (i - S < 8))) :=
          fun u h => FramerCode.eval_lt (by omega) (by decide) (ev_var (vals_lookup h.1.vals rfl)) rfl
        by_cases h8 : i - S < 8
        · have hstl : Lower.lowerExp (Syntax.eAdd (Syntax.atOff (Syntax.v "a") ArticleProg.xTok) (Syntax.v "ln")) =
              some (.op .add (.op .add (.var "a") (.const (BitVec.ofNat 64 ArticleProg.xTok))) (.var "ln")) := by
            show Lower.lowerExp (.binop .add (Syntax.atOff (Syntax.v "a") ArticleProg.xTok) (.var "ln")) = _
            rw [Lower.lowerExp, atOffTok_lower]; rfl
          refine frag_ifT o rfl (lowK_any _ (k := .skip) rfl) lowKK_nil rfl rfl (runF_clock _ _ _)
            (fun u h => (hlt u h).trans (by rw [bw_t h8])) ?_
          refine storeb_frag o hstl rfl (runF_clock _ _ _) fun u h => ⟨at_ A (ArticleProg.xTok + (i - S)), _, by
            simp only [eval, vals_lookup h.1.vals (show (LB (i - S)).lookup "a" = some A from rfl),
              vals_lookup h.1.vals (show (LB (i - S)).lookup "ln" = some (BitVec.ofNat 64 (i - S)) from rfl)]
            rw [← at_add]; rfl, ev_var (vals_lookup h.1.vals rfl), ?_, ?_⟩
          · rw [DN.News.ScanRun.align_at hA.hA, h.1.memaddrs]
            exact hD _ (by omega) (by omega) (by omega)
          · refine ⟨⟨h.1.vals, h.1.memaddrs, h.1.base, h.1.code, h.1.be⟩, ?_⟩
            show DN.Compiler.Bytes.putByte u.memory u.be (at_ A (ArticleProg.xTok + (i - S))) _ = Mt (i + 1)
            rw [h.2, h.1.be, DN.News.ArticleRun.setWidth_byte]
            show DN.Compiler.Bytes.putByte (putB M1 s1.be A ArticleProg.xTok ((seg a S i).take 8)) s1.be
              (at_ A (ArticleProg.xTok + (i - S))) a[i]! = putB M1 s1.be A ArticleProg.xTok ((seg a S (i + 1)).take 8)
            rw [hnext, List.take_of_length_le (show (seg a S i ++ [a[i]!]).length ≤ 8 by simp [hseg]; omega),
              List.take_of_length_le (show (seg a S i).length ≤ 8 by omega), putB_snoc, hseg]
        · refine frag_ifF o rfl (lowK_any _ (k := .skip) rfl) lowKK_nil rfl rfl (runF_clock _ _ _)
            (fun u h => (hlt u h).trans (by rw [bw_f h8])) (frag_nil o fun u h => ⟨h.1, ?_⟩)
          rw [h.2]
          show _ = putB M1 s1.be A ArticleProg.xTok ((seg a S (i + 1)).take 8)
          rw [hnext, List.take_append_of_le_length (by omega)]
      refine frag_append (xs := [_]) (M := RunF s1 (LB (i - S + 1)) (· = Mt (i + 1))) ?_ ?_
      · refine frag_ifT o rfl (lowK_any _ (k := .skip) rfl) lowKK_nil rfl rfl (runF_clock _ _ _)
          (fun u h => (FramerCode.eval_lt (by omega) (by omega) (ev_var (vals_lookup h.1.vals rfl)) rfl).trans
            (by rw [bw_t (show i - S < artMax by omega)])) ?_
        exact frag_conseq (runF_set o rfl rfl (v := BitVec.ofNat 64 (i - S + 1)) fun u h =>
          ev_inc (vals_lookup h.1.vals rfl)) (fun _ h => h) fun u h =>
            runF_push h rfl (runF_tokL2 h rfl rfl rfl rfl rfl rfl)
      exact frag_conseq (runF_set o rfl rfl (v := BitVec.ofNat 64 (i + 1)) fun u h =>
        ev_inc (vals_lookup h.1.vals rfl)) (fun _ h => h) fun u h => ⟨(1, i + 1), by
          show RunF s1 (tokL2 P E A 1 (i + 1 - S) (i + 1)) _ u
          rw [show i + 1 - S = i - S + 1 by omega]; exact runF_tokL2 h rfl rfl rfl rfl rfl rfl, by omega, by omega,
          by rw [hnext, List.all_append, h3, List.all_cons, hg]; rfl, .inl rfl⟩
    · have hi' : ¬i < E := fun e => by simp [e] at hi
      exact frag_conseq (runF_set o rfl rfl (v := BitVec.ofNat 64 0) fun _ _ => rfl) (fun _ h => h)
        fun u h => ⟨(0, i), runF_tokL2 h rfl rfl rfl rfl rfl rfl, h1, h2, h3, .inr ⟨rfl, .inl (by omega)⟩⟩
  · intro u ⟨⟨t, h, h1, h2, h3, h4⟩, h0⟩
    rw [ev_var (vals_lookup h.1.vals rfl)] at h0
    rcases h4 with e | ⟨e, hs⟩
    · rw [e] at h0; exact absurd (Option.some.inj h0) (by decide)
    · obtain ⟨g, i⟩ := t
      simp only at e h1 h2 h3 hs h; subst e
      rw [← seg_tw hE h1 h2 h3 hs] at h; exact h

theorem wordStart_le {a : Bytes} {P E : Nat} (hPE : P ≤ E) (hE : E ≤ a.length) : wordStart a P E ≤ E := by
  unfold wordStart; have := tw_le (p := gap) (seg a P E); rw [seg_length a hPE hE] at this; omega

/-- **`artTok` finds the next word** from `P` before `E` (`tokens_next`), if it returns. -/
theorem artTok_ok (o : Oracle σ) {A : Word} {s1 : PancakeState σ} (hA : Area ArticleProg.ofs A s1)
    (hD : ArtDom A s1.memaddrs) {a : Bytes} (hlen : a.length ≤ artMax) (hin : InputAt s1.memory s1.memaddrs s1.be A a)
    {P E : Nat} (hPE : P ≤ E) (hE : E ≤ a.length) (hp : s1.locals "p" = some (BitVec.ofNat 64 P))
    (he : s1.locals "e" = some (BitVec.ofNat 64 E)) :
    ∃ body, Lower.lower (gd ArticleProg.artTok) = some body ∧
      SafeR o (fun s => s = s1) body (TokRet A s1.be a P E s1.memory) fun _ => False := by
  have hM := artMax_eq
  have hEM : E ≤ artMax := by omega
  have hS := wordStart_le hPE hE
  generalize hS' : wordStart a P E = S' at hS
  refine body_of ?_
  show FragR o _ (guardL ArticleProg.artTok.body) _ _
  rw [artTok_body]
  obtain ⟨EA, hEA⟩ := atOff_lower ArticleProg.ofs
  refine fragR_conseq (P0 := RunF s1 [("p", BitVec.ofNat 64 P), ("e", BitVec.ofNat 64 E)] (· = s1.memory))
    ?_ (entry_two hp he) fun _ h => h
  refine fragR_append (xs := [_]) (fragR_of (runF_dec o hEA rfl (v := A) fun u h => areaAt_eval hA h.1.base hEA)) ?_
  refine fragR_append (xs := [_]) (fragR_of (runF_dec o rfl rfl (v := BitVec.ofNat 64 P) fun u h =>
    ev_var (vals_lookup h.1.vals rfl))) ?_
  refine fragR_append (xs := [_]) (fragR_of (runF_dec o rfl rfl (v := BitVec.ofNat 64 1) fun _ _ => rfl)) ?_
  refine fragR_append (xs := [_]) (fragR_of (frag_conseq (tok_loop1 o hin hPE hE hEM) (fun _ h => h)
    fun u h => by rw [hS'] at h; exact h)) ?_
  let M1 := upd s1.memory (at_ A ArticleProg.xTokS) (BitVec.ofNat 64 S')
  refine fragR_append (xs := [_]) (fragR_of (runF_storeA o (atOffW_lower 19) rfl (y := ArticleProg.w 19)
    (artDom_w hD (by decide)) (fun u h => atA_eval (vals_lookup h.1.vals rfl)) (val := fun _ => BitVec.ofNat 64 S')
    (fun u h => ev_var (vals_lookup h.1.vals rfl)) (G := (· = M1)) fun m hm => by subst hm; rfl)) ?_
  refine fragR_append (xs := [_]) (fragR_of (runF_dec o rfl rfl (v := BitVec.ofNat 64 0) fun _ _ => rfl)) ?_
  refine fragR_append (xs := [_]) (fragR_of (frag_conseq (runF_set o rfl rfl (v := BitVec.ofNat 64 1) fun _ _ => rfl)
    (fun _ h => h) (P' := RunF s1 (tokL2 P E A 1 0 S') (· = M1)) fun u h => runF_tokL2 h rfl rfl rfl rfl rfl rfl)) ?_
  have hM1 : ∀ x, x < aSets → M1 (at_ A x) = s1.memory (at_ A x) := fun x hx =>
    upd_ne _ (DN.News.ScanRun.at_ne (by have := X_lt; have := sets_le_X; omega) (w_lt64 (by decide))
      (by have := w_ge 19; show x ≠ ArticleProg.w 19; omega))
  refine fragR_append (xs := [_]) (fragR_of (tok_loop2 o hA hD hlen hin hS hE hM1)) ?_
  refine fragR_append (xs := [_]) (fragR_of (runF_storeA o (atOffW_lower 20) rfl (y := ArticleProg.w 20)
    (artDom_w hD (by decide)) (fun u h => atA_eval (vals_lookup h.1.vals rfl))
    (val := fun _ => BitVec.ofNat 64 (wordEnd a S' E - S')) (fun u h => ev_var (vals_lookup h.1.vals rfl))
    (G := (· = upd (putB M1 s1.be A ArticleProg.xTok ((seg a S' (wordEnd a S' E)).take 8)) (at_ A ArticleProg.xTokLen)
      (BitVec.ofNat 64 (wordEnd a S' E - S')))) fun m hm => by subst hm; rfl)) ?_
  refine fragR_ret o rfl fun u h => ⟨_, ev_var (vals_lookup h.1.vals rfl), ?_⟩
  show _ ∧ _
  rw [hS']
  exact ⟨rfl, h.2⟩

/-! ## Witnesses: each premise can hold -/

theorem idsInv_witness : IdsInv 0 [] 0 0 ⟨0, 0, 0, 0, 0, 0, 0, BitVec.ofNat 64 (2 ^ 64 - 1), 0⟩ :=
  ids_init 0 [] (Nat.le_refl 0)

theorem recvInv_witness : RecvInv [] 0 0 ⟨0, 0, 0⟩ :=
  ⟨Nat.le_refl _, Nat.zero_le _, Nat.zero_le _, Nat.le_refl _, fun h => absurd rfl h, rfl⟩

theorem numInv_witness : NumInv [] 0 0 0 0 0 := ⟨Nat.le_refl _, Nat.le_refl _, rfl, rfl, rfl⟩

end DN.News.ArticleScan
