-- SPDX-License-Identifier: AGPL-3.0-or-later
import DN.News.ScanSpec
import DN.News.ScanFrame

/-!
# DN.News.ScanArea

The scanner's area as a state of reading the journal (`AreaAt`). If it goes on, the step's head reads the
area's words into locals (`head_frag`), and with too few octets in the window for the next frame, the step
moves the window to the frame and asks for octets after it, as `stepSpec` does (`want_frag`). The step's state
between (`Ctx`): what it keeps, the area, and its locals' values listed (`Vals`, read by `vals_lookup`), set by
`ctx_assign`; the frame's place in the window from it (`frameAt_frag`).
-/

namespace DN.News.ScanRun

open DN.Compiler DN.Compiler.Wp DN.Compiler.Frag DN.Compiler.Bytes DN.News.Journal DN.News.ScanProg
open DN.News.FramerCode (bw bw_ne0 bw_eq0 eval_lt)

variable {σ : Type}

/-! ## The area as a state -/

/-- The area's words. -/
def AreaW (A : Word) (a : Word) : Prop := ∃ x, x < ScanProg.size ∧ a = at_ A x

/-- **The area at `A` holds the state `st` of reading `J`**: the journal's length, the window's place, length
and octets, where the next frame starts, the key once read and how many records were read. -/
structure AreaAt (A : Word) (J : Bytes) (st : St) (s : PancakeState σ) : Prop where
  size : s.memory (at_ A sSize) = BitVec.ofNat 64 J.length
  base : s.memory (at_ A sBase) = BitVec.ofNat 64 st.base
  len : s.memory (at_ A sLen) = BitVec.ofNat 64 st.len
  pos : s.memory (at_ A sPos) = BitVec.ofNat 64 st.pos
  keyed : s.memory (at_ A sKeyed) = bw st.key.isSome
  count : s.memory (at_ A sCount) = BitVec.ofNat 64 st.acc.length
  window : ∀ i, i < st.len → memLoadByte s.memory s.memaddrs s.be (at_ A (sWindow + i)) = some (J.getD (st.base + i) 0)
  key : ∀ k, st.key = some k → readByteArray s.memory s.memaddrs s.be (at_ A sKey) 16 = some k

/-- A word of the area, read. -/
theorem e_word {u : PancakeState σ} {A : Word} (hA : A.toNat % 8 = 0) (hd : Dom A u.memaddrs)
    (hsp : u.locals "jsc" = some A) {x : Nat} (hx : x % 8 = 0) (hxs : x < ScanProg.size) :
    ∃ E, Lower.lowerExp (ScanProg.word x) = some E ∧ eval u E = some (u.memory (at_ A x)) :=
  e_loadw hA hd hsp hx hxs

/-- What a step needs: the area at `A` holding a state of reading `J` that keeps its window, a journal
shorter than `2 ^ 62` octets, and the step's locals. -/
structure StepIn (A : Word) (J : Bytes) (st : St) (s : PancakeState σ) : Prop where
  hA : A.toNat % 8 = 0
  dom : Dom A s.memaddrs
  sp : s.locals "jsc" = some A
  jz : s.locals "jz" = some 0
  area : AreaAt A J st s
  valid : Valid J st
  short : J.length < 2 ^ 62
  bound : ∀ y ∈ ScanProg.locals, ∃ v, s.locals y = some v

/-- After the head: the area as it was, its words in locals. -/
structure Hd (A : Word) (J : Bytes) (st : St) (s0 u : PancakeState σ) : Prop where
  kept : Kept ScanProg.locals (fun _ => False) s0 u
  jsz : u.locals "jsz" = some (BitVec.ofNat 64 J.length)
  jb : u.locals "jb" = some (BitVec.ofNat 64 st.base)
  jwl : u.locals "jwl" = some (BitVec.ofNat 64 st.len)
  jp : u.locals "jp" = some (BitVec.ofNat 64 st.pos)
  jky : u.locals "jky" = some (bw st.key.isSome)
  jw : u.locals "jw" = some (at_ A sWindow)
  jrem : u.locals "jrem" = some (BitVec.ofNat 64 (J.length - st.pos))

/-- The head's state, kept where a local it does not list is set. -/
theorem hd_set {A : Word} {J : Bytes} {st : St} {s0 u : PancakeState σ} (h : Hd A J st s0 u) {x : String}
    (hx : x ∈ ScanProg.locals) (hn : x ∉ ["jsz", "jb", "jwl", "jp", "jky", "jw", "jrem"]) (v : Value) :
    Hd A J st s0 (setL u x v) := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hn
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hn
  exact ⟨kept_set h.kept hx v, by simp [setL, setLocal, Ne.symm h1, h.jsz], by simp [setL, setLocal, Ne.symm h2, h.jb],
    by simp [setL, setLocal, Ne.symm h3, h.jwl], by simp [setL, setLocal, Ne.symm h4, h.jp],
    by simp [setL, setLocal, Ne.symm h5, h.jky], by simp [setL, setLocal, Ne.symm h6, h.jw],
    by simp [setL, setLocal, Ne.symm h7, h.jrem]⟩

theorem word_frag (o : Oracle σ) {s : PancakeState σ} {A : Word} (hA : A.toNat % 8 = 0) (hd : Dom A s.memaddrs)
    (hsp : s.locals "jsc" = some A) {y : String} (hy : ∃ v, s.locals y = some v) {x : Nat} (hx : x % 8 = 0)
    (hxs : x < ScanProg.size) :
    Frag o [.assign y (word x)] (Like s) (Like (setL s y (s.memory (at_ A x)))) := by
  obtain ⟨E, hE, hv⟩ := e_word hA hd hsp hx hxs
  exact assign_frag o hE hv hy

/-- **The step's head**: if it goes on, the area's words it keeps in locals, nothing else changed. -/
theorem head_frag (o : Oracle σ) {A : Word} {J : Bytes} {st : St} {s0 : PancakeState σ} (h : StepIn A J st s0)
    {fail : List Syntax.PStmt} (hfl : LowKK fail) (hfd : declared fail = []) :
    Frag o (ScanProg.stepHead fail) (Like s0) (Hd A J st s0) := by
  have hn := nums
  have hv := h.valid
  have hJ := h.short
  have hb : ∀ y ∈ ScanProg.locals, ∃ v, s0.locals y = some v := h.bound
  let s1 := setL s0 "jsz" (s0.memory (at_ A sSize))
  let s2 := setL s1 "jb" (s0.memory (at_ A sBase))
  let s3 := setL s2 "jwl" (s0.memory (at_ A sLen))
  let s4 := setL s3 "jp" (s0.memory (at_ A sPos))
  let s5 := setL s4 "jky" (s0.memory (at_ A sKeyed))
  let s6 := setL s5 "jw" (at_ A sWindow)
  have hsp : ∀ y, y ≠ "jsc" → ∀ (s : PancakeState σ) v, (setL s y v).locals "jsc" = s.locals "jsc" :=
    fun y hy s v => by simp [setL, setLocal, Ne.symm hy]
  have hkeep : ∀ y z (s : PancakeState σ) v, z ≠ y → (setL s y v).locals z = s.locals z :=
    fun y z s v hz => by simp [setL, setLocal, hz]
  have f1 := word_frag o (s := s0) (y := "jsz") h.hA h.dom h.sp (hb _ (by decide)) (x := sSize) (by decide) (by decide)
  have f2 := word_frag o (s := s1) (y := "jb") h.hA h.dom (by rw [hsp _ (by decide)]; exact h.sp)
    (by rw [hkeep _ _ _ _ (by decide)]; exact hb _ (by decide)) (x := sBase) (by decide) (by decide)
  have f3 := word_frag o (s := s2) (y := "jwl") h.hA h.dom (by rw [hsp _ (by decide), hsp _ (by decide)]; exact h.sp)
    (by rw [hkeep _ _ _ _ (by decide), hkeep _ _ _ _ (by decide)]; exact hb _ (by decide)) (x := sLen) (by decide)
    (by decide)
  have f4 : Frag o [kept fail "jwl" windowMax] (Like s3) (Like s3) :=
    kept_skip o hfl hfd (by decide) (like_clock _) fun u hu => ⟨st.len, by
      rw [hu.locals]; simp [s3, setL, setLocal, h.area.len], hv.len⟩
  have f5 := word_frag o (s := s3) (y := "jp") h.hA h.dom (by simp only [s3, s2, s1, setL, setLocal]; simpa using h.sp)
    (by simp only [s3, s2, s1, setL, setLocal]; simpa using hb "jp" (by decide)) (x := sPos) (by decide) (by decide)
  have f6 := word_frag o (s := s4) (y := "jky") h.hA h.dom
    (by simp only [s4, s3, s2, s1, setL, setLocal]; simpa using h.sp)
    (by simp only [s4, s3, s2, s1, setL, setLocal]; simpa using hb "jky" (by decide)) (x := sKeyed) (by decide)
    (by decide)
  have f7 : Frag o [.assign "jw" (Syntax.atOff sp sWindow)] (Like s5) (Like s6) :=
    assign_frag o (E := .op .add (.var "jsc") (.const (BitVec.ofNat 64 sWindow))) rfl
      (by simp only [eval, s5, s4, s3, s2, s1, setL, setLocal]; simp [h.sp, at_])
      (by simp only [s5, s4, s3, s2, s1, setL, setLocal]; simpa using hb "jw" (by decide))
  have f8 : Frag o [.assign "jrem" (Syntax.eSub (Syntax.v "jsz") (Syntax.v "jp"))] (Like s6)
      (Like (setL s6 "jrem" (BitVec.ofNat 64 (J.length - st.pos)))) :=
    assign_frag o (E := .op .sub (.var "jsz") (.var "jp")) rfl
      (by
        simp only [eval, s6, s5, s4, s3, s2, s1, setL, setLocal]
        simp only [if_pos, if_neg, String.reduceEq, not_false_eq_true, Option.some.injEq, h.area.size,
          h.area.pos]
        have := hv.stop; have := hv.pos
        rw [BitVec.ofNat_sub_ofNat_of_le _ _ (by omega) (by omega)])
      (by simp only [s6, s5, s4, s3, s2, s1, setL, setLocal]; simpa using hb "jrem" (by decide))
  refine frag_conseq (frag_append (xs := [_]) f1 (frag_append (xs := [_]) f2 (frag_append (xs := [_]) f3
    (frag_append (xs := [_]) f4 (frag_append (xs := [_]) f5 (frag_append (xs := [_]) f6
    (frag_append (xs := [_]) f7 f8))))))) (fun _ h => h) fun u hu => ?_
  have k7 : Kept ScanProg.locals (fun _ => False) s0 (setL s6 "jrem" (BitVec.ofNat 64 (J.length - st.pos))) :=
    kept_set (kept_set (kept_set (kept_set (kept_set (kept_set (kept_set (kept_refl _ _ _) (by decide) _)
      (by decide) _) (by decide) _) (by decide) _) (by decide) _) (by decide) _) (by decide) _
  have hl : u.locals = (setL s6 "jrem" (BitVec.ofNat 64 (J.length - st.pos))).locals := hu.locals
  refine ⟨kept_trans k7 (kept_of_like hu), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [hl, s6, s5, s4, s3, s2, s1, setL, setLocal, h.area.size, h.area.base, h.area.len, h.area.pos,
      h.area.keyed]

/-! ## Tools -/

/-- Locals that hold the values listed. -/
def Vals (u : PancakeState σ) (l : List (String × Value)) : Prop := ∀ p ∈ l, u.locals p.1 = some p.2

theorem vals_sub {u : PancakeState σ} {l l' : List (String × Value)} (h : Vals u l) (hs : ∀ q ∈ l', q ∈ l) :
    Vals u l' := fun q hq => h q (hs q hq)

/-- The window's words. -/
def WinW (A : Word) (a : Word) : Prop := ∃ x, sWindow ≤ x ∧ x < ScanProg.size ∧ a = at_ A x

/-- **The area kept**: what it holds reads the same where only other words changed. -/
theorem areaAt_keep {A : Word} (hA : A.toNat % 8 = 0) {J : Bytes} {st : St} {u u' : PancakeState σ}
    (h : AreaAt A J st u) (hl : st.len ≤ windowMax) (hd : u'.memaddrs = u.memaddrs) (hb : u'.be = u.be)
    (hm : ∀ x, x < ScanProg.size → x % 8 = 0 → (x < sStatus ∨ (sKey ≤ x ∧ x < sMessage) ∨
      (sWindow ≤ x ∧ x < sWindow + st.len)) → u'.memory (at_ A x) = u.memory (at_ A x)) : AreaAt A J st u' := by
  have hn := nums
  have hload : ∀ x, x < ScanProg.size → (x / 8 * 8 < sStatus ∨ (sKey ≤ x / 8 * 8 ∧ x / 8 * 8 < sMessage) ∨
      (sWindow ≤ x / 8 * 8 ∧ x / 8 * 8 < sWindow + st.len)) →
      memLoadByte u'.memory u'.memaddrs u'.be (at_ A x) = memLoadByte u.memory u.memaddrs u.be (at_ A x) :=
    fun x hx hr => by
      simp only [memLoadByte, align_at hA, hd, hb, hm _ (by omega) (by omega) hr]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, fun i hi => ?_, fun k hk => ?_⟩
  · rw [hm _ (by decide) (by decide) (Or.inl (by decide))]; exact h.size
  · rw [hm _ (by decide) (by decide) (Or.inl (by decide))]; exact h.base
  · rw [hm _ (by decide) (by decide) (Or.inl (by decide))]; exact h.len
  · rw [hm _ (by decide) (by decide) (Or.inl (by decide))]; exact h.pos
  · rw [hm _ (by decide) (by decide) (Or.inl (by decide))]; exact h.keyed
  · rw [hm _ (by decide) (by decide) (Or.inl (by decide))]; exact h.count
  · rw [hload (sWindow + i) (by omega) (Or.inr (Or.inr (by omega)))]; exact h.window i hi
  · rw [← h.key k hk, hd, hb]
    refine readByteArray_congr 16 _ fun j hj => ?_
    rw [at_add]
    have := hload (sKey + j) (by omega) (Or.inr (Or.inl (by omega)))
    rwa [hd, hb] at this

/-- A word of the area stored. -/
theorem setw_frag (o : Oracle σ) {A : Word} (hA : A.toNat % 8 = 0) {x : Nat} (hx : x % 8 = 0)
    (hxs : x < ScanProg.size) {e : Syntax.PExpr} {E : PancakeExp} (he : Lower.lowerExp e = some E)
    {P P' : Assn σ} (hP' : Safe.ClockFree P')
    (h : ∀ u, P u → u.locals "jsc" = some A ∧ Dom A u.memaddrs ∧ ∃ val, eval u E = some val ∧
      P' { u with memory := fun k => if k = at_ A x then val else u.memory k }) :
    Frag o [ScanProg.setw x e] P P' :=
  store_at_frag o hA hx hxs he hP' h

/-- What the area holds, kept where a word from the status's to the key's is stored. -/
theorem areaAt_word {A : Word} (hA : A.toNat % 8 = 0) {J : Bytes} {st : St} {u : PancakeState σ}
    (h : AreaAt A J st u) (hl : st.len ≤ windowMax) {x : Nat} (hx1 : sStatus ≤ x) (hx2 : x < sKey) (v : Word) :
    AreaAt A J st { u with memory := fun k => if k = at_ A x then v else u.memory k } :=
  areaAt_keep hA h hl rfl rfl fun y hy _ hr => by
    have hn := nums
    have hne : at_ A y ≠ at_ A x := fun e => by
      have := at_inj (by simp only [ScanProg.size] at hy; omega) (by omega) e
      simp only [sStatus] at hr hx1; omega
    simp only [if_neg hne]

/-! ## The step's state -/

/-- The value `l` lists first for `x`, found by `List.lookup` (shown by `rfl`). -/
theorem vals_lookup {u : PancakeState σ} : ∀ {l : List (String × Value)}, Vals u l → ∀ {x : String} {v : Value},
    l.lookup x = some v → u.locals x = some v
  | [], _, _, _, hx => by cases hx
  | (y, w) :: l, h, x, v, hx => by
    rw [List.lookup_cons] at hx
    by_cases e : x = y
    · subst e
      rw [beq_self_eq_true] at hx
      cases hx; exact h _ (List.mem_cons_self ..)
    · rw [beq_eq_false_iff_ne.mpr e] at hx
      exact vals_lookup (fun q hq => h q (List.mem_cons_of_mem _ hq)) hx

/-- Whether `l` lists nothing for `x`, a check to compute. -/
def Fresh (x : String) (l : List (String × Value)) : Bool := l.all fun q => q.1 != x

/-- Whether `l` lists nothing for any of `ns`. -/
def Outside (ns : List String) (l : List (String × Value)) : Bool := l.all fun q => !ns.contains q.1

theorem fresh_ne {x : String} {l : List (String × Value)} (h : Fresh x l = true) : ∀ q ∈ l, q.1 ≠ x := by
  simpa [Fresh] using h

theorem outside_ne {ns : List String} {l : List (String × Value)} (h : Outside ns l = true) :
    ∀ q ∈ l, q.1 ∉ ns := fun q hq hn => by
  have := List.all_eq_true.mp h q hq
  simp [hn] at this

theorem fresh_of_outside {ns : List String} {l : List (String × Value)} (h : Outside ns l = true) {x : String}
    (hx : x ∈ ns) : Fresh x l = true := by
  simp only [Fresh, List.all_eq_true, bne_iff_ne]
  exact fun q hq e => outside_ne h q hq (e ▸ hx)

theorem vals_cons {u : PancakeState σ} {l : List (String × Value)} (h : Vals u l) {x : String}
    (hx : Fresh x l = true) (v : Value) : Vals (setL u x v) ((x, v) :: l) := fun p hp => by
  simp only [List.mem_cons] at hp
  rcases hp with rfl | hp
  · simp [setL, setLocal]
  · simp only [setL, setLocal, if_neg (fresh_ne hx p hp)]; exact h p hp

theorem vals_drop {u : PancakeState σ} {pre l : List (String × Value)} (h : Vals u (pre ++ l)) : Vals u l :=
  fun q hq => h q (List.mem_append_right _ hq)

/-- A local listed in the middle set again. -/
theorem vals_update {u : PancakeState σ} {pre l : List (String × Value)} {x : String} {w : Value}
    (h : Vals u (pre ++ (x, w) :: l)) (hp : Fresh x pre = true) (hl : Fresh x l = true) (v : Value) :
    Vals (setL u x v) (pre ++ (x, v) :: l) := fun q hq => by
  simp only [List.mem_append, List.mem_cons] at hq
  rcases hq with hq | rfl | hq
  · simp only [setL, setLocal, if_neg (fresh_ne hp q hq)]; exact h q (List.mem_append_left _ hq)
  · simp [setL, setLocal]
  · simp only [setL, setLocal, if_neg (fresh_ne hl q hq)]
    exact h q (List.mem_append_right _ (List.mem_cons_of_mem _ hq))

/-- Locals outside `xs` kept. -/
theorem vals_kept {u u' : PancakeState σ} {l : List (String × Value)} (h : Vals u l) {xs : List String}
    {w : Word → Prop} (hk : Kept xs w u u') (ho : Outside xs l = true) : Vals u' l := fun q hq => by
  rw [hk.locals _ (outside_ne ho q hq)]; exact h q hq

/-- `l` but for `y`. -/
def without (y : String) (l : List (String × Value)) : List (String × Value) := l.filter fun q => q.1 != y

/-- Fewer names outside. -/
theorem outside_sub {xs ys : List String} {l : List (String × Value)} (h : Outside xs l = true)
    (hs : ∀ y ∈ ys, y ∈ xs) : Outside ys l = true := by
  simp only [Outside, List.all_eq_true, Bool.not_eq_true'] at h ⊢
  intro q hq
  have := h q hq
  rw [Bool.eq_false_iff] at this ⊢
  intro hm
  rw [List.contains_iff_mem] at hm
  exact this (List.contains_iff_mem.mpr (hs _ hm))

/-- Fresh past a pair of another name. -/
theorem fresh_cons {y x : String} {v : Value} {l : List (String × Value)} (hne : x ≠ y)
    (h : Fresh y l = true) : Fresh y ((x, v) :: l) = true := by
  simp only [Fresh, List.all_cons] at h ⊢; simp [hne, h]

/-- Locals kept where one not listed is set. -/
theorem vals_setL {u : PancakeState σ} {l : List (String × Value)} (h : Vals u l) {y : String}
    (hy : Fresh y l = true) (v : Value) : Vals (setL u y v) l :=
  fun q hq => vals_cons h hy v q (List.mem_cons_of_mem _ hq)

/-- A lookup past a pair of another name. -/
theorem lookup_cons_ne {x y : String} (h : y ≠ x) (v : Value) (l : List (String × Value)) :
    ((x, v) :: l).lookup y = l.lookup y := by
  rw [List.lookup_cons, beq_eq_false_iff_ne.mpr h]

/-- A lookup at the head. -/
theorem lookup_head (y : String) (w : Value) (l : List (String × Value)) : ((y, w) :: l).lookup y = some w := by
  rw [List.lookup_cons, beq_self_eq_true]

/-- A lookup past the pairs of another name dropped. -/
theorem lookup_without {x y : String} (h : y ≠ x) : ∀ (l : List (String × Value)), (without x l).lookup y = l.lookup y
  | [] => rfl
  | (k, v) :: l => by
    by_cases hk : k = x
    · subst hk
      have : without k ((k, v) :: l) = without k l := by simp [without]
      rw [this, lookup_without h l, lookup_cons_ne h]
    · have : without x ((k, v) :: l) = (k, v) :: without x l := by simp [without, hk]
      rw [this]
      by_cases hy : y = k
      · subst hy; rw [List.lookup_cons, List.lookup_cons, beq_self_eq_true]
      · rw [lookup_cons_ne hy, lookup_cons_ne hy, lookup_without h l]

/-- A local set, listed on top. -/
theorem vals_set {u : PancakeState σ} {l : List (String × Value)} (h : Vals u l) (y : String) (v : Value) :
    Vals (setL u y v) ((y, v) :: without y l) := fun q hq => by
  simp only [List.mem_cons, without, List.mem_filter, bne_iff_ne] at hq
  rcases hq with rfl | ⟨hq, hne⟩
  · simp [setL, setLocal]
  · simp only [setL, setLocal, if_neg hne]; exact h q hq

/-- Dropping a name twice. -/
theorem without_cons_self (y : String) (v : Value) (l : List (String × Value)) :
    without y ((y, v) :: without y l) = without y l := by
  simp [without, List.filter_filter]

/-- The head set again. -/
theorem vals_head {u : PancakeState σ} {y : String} {w : Value} {l : List (String × Value)}
    (h : Vals u ((y, w) :: l)) (hl : Fresh y l = true) (v : Value) : Vals (setL u y v) ((y, v) :: l) :=
  vals_cons (fun q hq => h q (List.mem_cons_of_mem _ hq)) hl v

/-- A state but for its locals and clock as it was. -/
theorem kept_false_eq {xs : List String} {u u' : PancakeState σ} (h : Kept xs (fun _ => False) u u') :
    u' = { u with locals := u'.locals, clock := u'.clock } := by
  have hm : u'.memory = u.memory := funext fun a => h.memory a id
  have hd := h.memaddrs
  have hb := h.be
  have hf := h.ffi
  have hba := h.base
  have hc := h.code
  cases u; cases u'
  simp only at hm hd hb hf hba hc ⊢
  subst hm hd hb hf hba hc
  rfl

/-- **The step's state**: the locals but the step's and the memory but the area as in `s0`, the area as `st`
says, and the locals `l` lists with their values. -/
structure Ctx (A : Word) (J : Bytes) (st : St) (s0 : PancakeState σ) (l : List (String × Value))
    (u : PancakeState σ) : Prop where
  kept : Kept ScanProg.locals (AreaW A) s0 u
  area : AreaAt A J st u
  vals : Vals u l

theorem ctx_clock {A : Word} {J : Bytes} {st : St} {s0 : PancakeState σ} {l : List (String × Value)} :
    Safe.ClockFree (Ctx A J st s0 l) := fun _ _ h => ⟨{ h.kept with }, { h.area with }, h.vals⟩

section Ctx
variable {A : Word} {J : Bytes} {st : St} {s0 : PancakeState σ}

/-- Where the step keeps its locals, `jz` is zero, `jsc` the area's address and the area addressable. -/
theorem kept_jz (h : StepIn A J st s0) {w : Word → Prop} {u : PancakeState σ} (hk : Kept ScanProg.locals w s0 u) :
    u.locals "jz" = some 0 := (hk.locals "jz" (by decide)).trans h.jz

theorem kept_jsc (h : StepIn A J st s0) {w : Word → Prop} {u : PancakeState σ} (hk : Kept ScanProg.locals w s0 u) :
    u.locals "jsc" = some A := (hk.locals "jsc" (by decide)).trans h.sp

theorem kept_dom (h : StepIn A J st s0) {w : Word → Prop} {u : PancakeState σ} (hk : Kept ScanProg.locals w s0 u) :
    Dom A u.memaddrs := by rw [hk.memaddrs]; exact h.dom

theorem ctx_jz (h : StepIn A J st s0) {l : List (String × Value)} {u : PancakeState σ} (hu : Ctx A J st s0 l u) :
    u.locals "jz" = some 0 := kept_jz h hu.kept

theorem ctx_jsc (h : StepIn A J st s0) {l : List (String × Value)} {u : PancakeState σ} (hu : Ctx A J st s0 l u) :
    u.locals "jsc" = some A := kept_jsc h hu.kept

theorem ctx_dom (h : StepIn A J st s0) {l : List (String × Value)} {u : PancakeState σ} (hu : Ctx A J st s0 l u) :
    Dom A u.memaddrs := kept_dom h hu.kept

/-- **A local of the step set**, to what `E` evaluates to. -/
theorem ctx_assign (o : Oracle σ) (h : StepIn A J st s0) {x : String} {e : Syntax.PExpr} {E : PancakeExp}
    (he : Lower.lowerExp e = some E) (hx : x ∈ ScanProg.locals) {l : List (String × Value)} (hf : Fresh x l = true)
    {v : Value} (hv : ∀ u, Ctx A J st s0 l u → eval u E = some v) :
    Frag o [.assign x e] (Ctx A J st s0 l) (Ctx A J st s0 ((x, v) :: l)) :=
  set_frag o he ctx_clock fun u hu => ⟨v, hv u hu, kept_has hu.kept (h.bound x hx),
    ⟨kept_set hu.kept hx v, { hu.area with }, vals_cons hu.vals hf v⟩⟩

/-- …or set again, where `l` lists it after `pre`. -/
theorem ctx_reassign (o : Oracle σ) (h : StepIn A J st s0) {x : String} {e : Syntax.PExpr} {E : PancakeExp}
    (he : Lower.lowerExp e = some E) (hx : x ∈ ScanProg.locals) {pre l : List (String × Value)} {w : Value}
    (hp : Fresh x pre = true) (hl : Fresh x l = true) {v : Value}
    (hv : ∀ u, Ctx A J st s0 (pre ++ (x, w) :: l) u → eval u E = some v) :
    Frag o [.assign x e] (Ctx A J st s0 (pre ++ (x, w) :: l)) (Ctx A J st s0 (pre ++ (x, v) :: l)) :=
  set_frag o he ctx_clock fun u hu => ⟨v, hv u hu, kept_has hu.kept (h.bound x hx),
    ⟨kept_set hu.kept hx v, { hu.area with }, vals_update hu.vals hp hl v⟩⟩

/-- The head's locals and their values. -/
def hdV (A : Word) (J : Bytes) (st : St) : List (String × Value) :=
  [("jsz", BitVec.ofNat 64 J.length), ("jb", BitVec.ofNat 64 st.base), ("jwl", BitVec.ofNat 64 st.len),
   ("jp", BitVec.ofNat 64 st.pos), ("jky", bw st.key.isSome), ("jw", at_ A sWindow),
   ("jrem", BitVec.ofNat 64 (J.length - st.pos))]

/-- After the head, the step's state. -/
theorem hd_ctx (h : StepIn A J st s0) {u : PancakeState σ} (hu : Hd A J st s0 u) : Ctx A J st s0 (hdV A J st) u := by
  refine ⟨kept_widen hu.kept (fun _ h => h) fun _ h => h.elim, areaAt_keep h.hA h.area h.valid.len hu.kept.memaddrs
    hu.kept.be fun x _ _ _ => hu.kept.memory _ id, fun q hq => ?_⟩
  simp only [hdV, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact hu.jsz
  · exact hu.jb
  · exact hu.jwl
  · exact hu.jp
  · exact hu.jky
  · exact hu.jw
  · exact hu.jrem

/-- The message's words lie in the area. -/
theorem msgW_areaW {a : Word} (h : MsgW A a) : AreaW A a := by
  obtain ⟨x, _, h2, e⟩ := h; exact ⟨x, by have := nums; simp only [ScanProg.size]; omega, e⟩

/-- What the area holds, kept where only the message changed. -/
theorem areaAt_msg {u u' : PancakeState σ} (hA : A.toNat % 8 = 0) (ha : AreaAt A J st u) (hl : st.len ≤ windowMax)
    {xs : List String} (hk : Kept xs (MsgW A) u u') : AreaAt A J st u' :=
  areaAt_keep hA ha hl hk.memaddrs hk.be fun x hx hx8 hr => hk.memory _ (by
    have := nums
    have e := not_msg hA (x := x) (by simp only [sStatus] at hr; omega) (by simp only [ScanProg.size] at hx; omega)
    rwa [align_at hA, show x / 8 * 8 = x by omega] at e)

/-- **The frame's place**: from where it starts in the journal, `q`, its offset in the window into `jo`, its
place into `jf`, its payload's into `jpp`. -/
theorem frameAt_frag (o : Oracle σ) (h : StepIn A J st s0) {fail : List Syntax.PStmt} (hfl : LowKK fail)
    (hfd : declared fail = []) {q : Nat} {l : List (String × Value)} (hq : st.base ≤ q)
    (hqw : q - st.base ≤ windowMax) (hq64 : q < 2 ^ 62) (hjq : l.lookup "jq" = some (BitVec.ofNat 64 q))
    (hjb : l.lookup "jb" = some (BitVec.ofNat 64 st.base)) (hjw : l.lookup "jw" = some (at_ A sWindow))
    (ho : Fresh "jo" l = true) (hf : Fresh "jf" l = true) (hp : Fresh "jpp" l = true) :
    Frag o (ScanProg.frameAt fail) (Ctx A J st s0 l) (Ctx A J st s0
      (("jpp", at_ A (sWindow + (q - st.base) + 13)) :: ("jf", at_ A (sWindow + (q - st.base))) ::
        ("jo", BitVec.ofNat 64 (q - st.base)) :: l)) := by
  have hn := nums
  have f1 := ctx_assign o h (x := "jo") (e := Syntax.eSub (Syntax.v "jq") (Syntax.v "jb"))
    (E := .op .sub (.var "jq") (.var "jb")) rfl (by decide) ho
    (v := BitVec.ofNat 64 (q - st.base)) fun u hu => by
      simp only [eval, vals_lookup hu.vals hjq, vals_lookup hu.vals hjb]
      rw [BitVec.ofNat_sub_ofNat_of_le _ _ (by omega) (by omega)]
  have f2 : Frag o [ScanProg.kept fail "jo" windowMax] (Ctx A J st s0 (("jo", BitVec.ofNat 64 (q - st.base)) :: l))
      (Ctx A J st s0 (("jo", BitVec.ofNat 64 (q - st.base)) :: l)) :=
    kept_skip o hfl hfd (by decide) ctx_clock fun u hu => ⟨q - st.base, vals_lookup hu.vals rfl, hqw⟩
  have f3 := ctx_assign o h (x := "jf") (e := Syntax.eAdd (Syntax.v "jw") (Syntax.v "jo"))
    (E := .op .add (.var "jw") (.var "jo")) rfl (by decide)
    (l := ("jo", BitVec.ofNat 64 (q - st.base)) :: l) hf (v := at_ A (sWindow + (q - st.base))) fun u hu => by
      simp only [eval, vals_lookup hu.vals (x := "jw") hjw, vals_lookup hu.vals (x := "jo") rfl, at_add]
  have f4 := ctx_assign o h (x := "jpp") (e := Syntax.atOff (Syntax.v "jf") headerLength)
    (E := .op .add (.var "jf") (.const (BitVec.ofNat 64 13))) rfl (by decide)
    (l := ("jf", at_ A (sWindow + (q - st.base))) :: ("jo", BitVec.ofNat 64 (q - st.base)) :: l) hp
    (v := at_ A (sWindow + (q - st.base) + 13)) fun u hu => by
      simp only [eval, vals_lookup hu.vals (x := "jf") rfl, at_add]
  exact frag_append (xs := [_]) f1 (frag_append (xs := [_]) f2 (frag_append (xs := [_]) f3 f4))

end Ctx

/-! ## Octets wanted -/

/-- What a want leaves: the window moved to the next frame, how many octets the step wants after it. -/
def WantOut (A : Word) (J : Bytes) (st : St) (s0 u : PancakeState σ) : Prop :=
  Kept ScanProg.locals (AreaW A) s0 u ∧ u.memory (at_ A sStatus) = BitVec.ofNat 64 wanted ∧
    AreaAt A J { st with base := st.pos, len := st.base + st.len - st.pos } u ∧
    u.memory (at_ A sWant) = BitVec.ofNat 64 (min chunk (J.length - (st.base + st.len)))

/-- Below the window, the words in `ws` stored, the rest as in `s0`; the window from `p`, `L` octets. -/
structure Tail (A : Word) (J : Bytes) (p L : Nat) (s0 : PancakeState σ) (ws : List (Nat × Word)) (u : PancakeState σ) :
    Prop where
  kept : Kept ScanProg.locals (AreaW A) s0 u
  win : ∀ j, j < L → memLoadByte u.memory u.memaddrs u.be (at_ A (sWindow + j)) = some (J.getD (p + j) 0)
  stored : ∀ q ∈ ws, u.memory (at_ A q.1) = q.2
  below : ∀ q ∈ ws, q.1 < sWindow
  short : L ≤ windowMax
  rest : ∀ x, x < sWindow → x % 8 = 0 → (∀ q ∈ ws, q.1 ≠ x) → u.memory (at_ A x) = s0.memory (at_ A x)

theorem tail_clock {A : Word} {J : Bytes} {p L : Nat} {s0 : PancakeState σ} {ws : List (Nat × Word)} {F : Assn σ}
    (hF : Safe.ClockFree F) : Safe.ClockFree (fun u => Tail A J p L s0 ws u ∧ F u) :=
  fun _ _ ⟨h1, h2⟩ => ⟨{ h1 with kept := { h1.kept with } }, hF _ _ h2⟩

theorem tail_set {A : Word} {J : Bytes} {p L : Nat} {s0 u : PancakeState σ} {ws : List (Nat × Word)}
    (h : Tail A J p L s0 ws u) {x : String} (hx : x ∈ ScanProg.locals) (v : Value) : Tail A J p L s0 ws (setL u x v) :=
  { h with kept := kept_set h.kept hx v }

theorem tail_store {A : Word} (hA : A.toNat % 8 = 0) {J : Bytes} {p L : Nat} {s0 u : PancakeState σ}
    {ws : List (Nat × Word)} (h : Tail A J p L s0 ws u) {x : Nat} (hx : x < sWindow) (hx8 : x % 8 = 0)
    (hxw : ∀ q ∈ ws, q.1 ≠ x) (v : Word) :
    Tail A J p L s0 ((x, v) :: ws) { u with memory := fun k => if k = at_ A x then v else u.memory k } := by
  have hn := nums
  have hL := h.short
  refine ⟨kept_word h.kept ⟨x, by simp only [ScanProg.size]; omega, rfl⟩ v, fun j hj => ?_, fun q hq => ?_,
    fun q hq => ?_, hL, fun y hy hy8 hyw => ?_⟩
  · rw [load_word_ne]; exact h.win j hj
    rw [align_at hA]
    exact at_ne (by omega) (by omega) (by omega)
  · simp only [List.mem_cons] at hq
    rcases hq with rfl | hq
    · simp
    · have := h.below q hq
      simp only [if_neg (fun e => hxw q hq (at_inj (by omega) (by omega) e))]
      exact h.stored q hq
  · simp only [List.mem_cons] at hq
    rcases hq with rfl | hq
    · exact hx
    · exact h.below q hq
  · simp only [List.mem_cons, forall_eq_or_imp] at hyw
    simp only [if_neg (fun e => hyw.1 (at_inj (by omega) (by omega) e).symm)]
    exact h.rest y hy hy8 hyw.2

/-- **Octets wanted**: if it goes on, where the window does not hold the frame at `jp`, the window moved to start
there and the octets wanted after it, as `stepSpec` says. -/
theorem want_frag (o : Oracle σ) {A : Word} {J : Bytes} {st : St} {s0 : PancakeState σ} (h : StepIn A J st s0)
    {fail : List Syntax.PStmt} (hfl : LowKK fail) (hfd : declared fail = []) (hpos : st.pos < J.length)
    (hw : st.base + st.len < st.pos + min (J.length - st.pos) maxFrame) :
    Frag o (ScanProg.want fail) (Hd A J st s0) (WantOut A J st s0) := by
  have hn := nums
  have hv := h.valid
  have hJ := h.short
  have hbp := hv.base
  have hpl := hv.pos
  have hst := hv.stop
  have hlen := hv.len
  obtain ⟨d, hd⟩ : ∃ d, d = st.pos - st.base := ⟨_, rfl⟩
  obtain ⟨L, hL⟩ : ∃ L, L = st.base + st.len - st.pos := ⟨_, rfl⟩
  obtain ⟨N, hN⟩ : ∃ N, N = J.length - (st.base + st.len) := ⟨_, rfl⟩
  have hLm : L < maxFrame := by
    have := Nat.min_le_right (J.length - st.pos) maxFrame; omega
  have hdl : d + L = st.len := by omega
  have hw0 : ∀ u, Kept ScanProg.locals (fun _ => False) s0 u → Kept ScanProg.locals (AreaW A) s0 u := fun _ hu =>
    kept_widen hu (fun _ h => h) fun _ h => h.elim
  have hbd : ∀ u, Kept ScanProg.locals (AreaW A) s0 u → ∀ y ∈ ScanProg.locals, ∃ v, u.locals y = some v :=
    fun _ hu y hy => kept_has hu (h.bound y hy)
  let V0 : List (String × Value) := [("jsz", BitVec.ofNat 64 J.length), ("jb", BitVec.ofNat 64 st.base),
    ("jwl", BitVec.ofNat 64 st.len), ("jp", BitVec.ofNat 64 st.pos), ("jw", at_ A sWindow)]
  let P (l : List (String × Value)) (u : PancakeState σ) : Prop :=
    Kept ScanProg.locals (fun _ => False) s0 u ∧ Vals u (l ++ V0)
  have hPc : ∀ l, Safe.ClockFree (P l) := fun _ _ _ ⟨h1, h2⟩ => ⟨{ h1 with }, h2⟩
  -- the frame's offset in the window, the octets after it
  have w1 : Frag o [.assign "jx" (Syntax.eSub (Syntax.v "jp") (Syntax.v "jb"))] (Hd A J st s0)
      (P [("jx", BitVec.ofNat 64 d)]) :=
    set_frag o (E := .op .sub (.var "jp") (.var "jb")) rfl (hPc _) fun u hu =>
      ⟨BitVec.ofNat 64 d, by
        simp only [eval, hu.jp, hu.jb]; rw [BitVec.ofNat_sub_ofNat_of_le _ _ (by omega) (by omega), hd],
        hbd u (hw0 u hu.kept) "jx" (by decide), kept_set hu.kept (by decide) _, by
        intro q hq
        simp only [List.mem_cons, List.mem_append, V0, List.not_mem_nil, or_false] at hq
        rcases hq with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [setL, setLocal, hu.jsz, hu.jb, hu.jwl, hu.jp, hu.jw]⟩
  have w2 : Frag o [kept fail "jx" windowMax] (P [("jx", BitVec.ofNat 64 d)]) (P [("jx", BitVec.ofNat 64 d)]) :=
    kept_skip o hfl hfd (by decide) (hPc _) fun u hu => ⟨d, vals_lookup hu.2 rfl, by subst hd; omega⟩
  have w3 : Frag o [.assign "jcnt" (Syntax.eSub (Syntax.v "jwl") (Syntax.v "jx"))] (P [("jx", BitVec.ofNat 64 d)])
      (P [("jcnt", BitVec.ofNat 64 L), ("jx", BitVec.ofNat 64 d)]) :=
    set_frag o (E := .op .sub (.var "jwl") (.var "jx")) rfl (hPc _) fun u hu =>
      ⟨BitVec.ofNat 64 L, by
        simp only [eval, vals_lookup hu.2 (x := "jwl") (v := BitVec.ofNat 64 st.len) rfl,
          vals_lookup hu.2 (x := "jx") (v := BitVec.ofNat 64 d) rfl]
        rw [BitVec.ofNat_sub_ofNat_of_le _ _ (by omega) (by omega)]; congr 2; omega,
        hbd u (hw0 u hu.1) "jcnt" (by decide), kept_set hu.1 (by decide) _, vals_cons hu.2 rfl _⟩
  have w4 : Frag o [.assign "ji" (lit 0)] (P [("jcnt", BitVec.ofNat 64 L), ("jx", BitVec.ofNat 64 d)])
      (P [("ji", BitVec.ofNat 64 0), ("jcnt", BitVec.ofNat 64 L), ("jx", BitVec.ofNat 64 d)]) :=
    set_frag o (E := .op .add (.var "jz") (.const 0)) rfl (hPc _) fun u hu =>
      ⟨BitVec.ofNat 64 0, by simp [eval, kept_jz h hu.1], hbd u (hw0 u hu.1) "ji" (by decide),
        kept_set hu.1 (by decide) _, vals_cons hu.2 rfl _⟩
  -- the window moved to start at the frame
  let V5 : List (String × Value) := [("jcnt", BitVec.ofNat 64 L), ("jsz", BitVec.ofNat 64 J.length),
    ("jp", BitVec.ofNat 64 st.pos)]
  let Q5 (u : PancakeState σ) : Prop := Tail A J st.pos L s0 [] u ∧ Vals u V5
  have hQ5c : Safe.ClockFree Q5 := tail_clock fun _ _ h => h
  have hwin0 : ∀ j, j < st.len → memLoadByte s0.memory s0.memaddrs s0.be (at_ A (sWindow + j)) =
      some (J.getD (st.base + j) 0) := h.area.window
  have hrest : ∀ u, Kept ScanProg.locals (WinW A) s0 u → ∀ x, x < sWindow → u.memory (at_ A x) = s0.memory (at_ A x) :=
    fun u hu x hx => hu.memory _ fun ⟨y, hy1, hy2, e⟩ => by
      have := at_inj (A := A) (by omega) (by simp only [ScanProg.size] at hy2; omega) e; omega
  have hwa : ∀ a, WinW A a → AreaW A a := fun a ⟨x, _, h2, e⟩ => ⟨x, h2, e⟩
  let Mixed (i : Nat) (u : PancakeState σ) : Prop := ∀ j, j < st.len →
    memLoadByte u.memory u.memaddrs u.be (at_ A (sWindow + j)) =
      some (J.getD (if j < i then st.pos + j else st.base + j) 0)
  let I (i : Nat) (u : PancakeState σ) : Prop := Kept ScanProg.locals (WinW A) s0 u ∧
    Vals u (("ji", BitVec.ofNat 64 i) :: ("jx", BitVec.ofNat 64 d) :: ("jw", at_ A sWindow) :: V5) ∧ i ≤ L ∧ Mixed i u
  have hIc : ∀ i, Safe.ClockFree (I i) := fun _ _ _ ⟨h1, h2, h3, h4⟩ => ⟨{ h1 with }, h2, h3, h4⟩
  have hbody : ∀ i, decide (i < L) = true → Frag o ScanProg.copyByte (I i) (I (i + 1)) := fun i hi => by
    simp only [decide_eq_true_eq] at hi
    let M (u : PancakeState σ) : Prop := Kept ScanProg.locals (WinW A) s0 u ∧
      Vals u (("ji", BitVec.ofNat 64 i) :: ("jx", BitVec.ofNat 64 d) :: ("jw", at_ A sWindow) :: V5) ∧ Mixed (i + 1) u
    have hMc : Safe.ClockFree M := fun _ _ ⟨h1, h2, h3⟩ => ⟨{ h1 with }, h2, h3⟩
    have g1 : Frag o [.storeb (Syntax.eAdd (Syntax.v "jw") (Syntax.v "ji"))
        (ScanProg.byte (Syntax.eAdd (Syntax.eAdd (Syntax.v "jw") (Syntax.v "jx")) (Syntax.v "ji")))] (I i) M :=
      storeb_frag o (D := .op .add (.var "jw") (.var "ji"))
        (E := .loadByte (.op .add (.op .add (.var "jw") (.var "jx")) (.var "ji"))) rfl rfl hMc fun u hu => by
        obtain ⟨hk, hvl, hiL, hmx⟩ := hu
        have hjw := vals_lookup hvl (x := "jw") (v := at_ A sWindow) rfl
        have hji := vals_lookup hvl (x := "ji") (v := BitVec.ofNat 64 i) rfl
        have hjx := vals_lookup hvl (x := "jx") (v := BitVec.ofNat 64 d) rfl
        have hsrc := hmx (d + i) (by omega)
        rw [if_neg (by omega), show st.base + (d + i) = st.pos + i by omega] at hsrc
        have hD : eval u (.op .add (.var "jw") (.var "ji")) = some (at_ A (sWindow + i)) := by
          simp only [eval, hjw, hji, at_add]
        have hE : eval u (.loadByte (.op .add (.op .add (.var "jw") (.var "jx")) (.var "ji"))) =
            some ((J.getD (st.pos + i) 0).setWidth 64) := by
          simp only [eval, hjw, hjx, hji, at_add, Nat.add_assoc, hsrc]
        have hdm : u.memaddrs (byteAlign (at_ A (sWindow + i))) = true := by
          rw [hk.memaddrs]; exact h.dom _ (by omega)
        refine ⟨_, _, hD, hE, hdm, kept_put hk ⟨(sWindow + i) / 8 * 8, by omega, by omega, align_at h.hA _⟩ _ _, hvl,
          fun j hj => ?_⟩
        by_cases hij : j = i
        · subst hij
          rw [load_putByte_same _ _ _ _ _ hdm, Bytes.setWidth64_8, if_pos (Nat.lt_succ_self _)]
        · rw [load_putByte_diff _ _ _ _ _ _ (at_ne (by omega) (by omega) (by omega)), hmx j hj]
          by_cases hj' : j < i
          · rw [if_pos hj', if_pos (by omega)]
          · rw [if_neg hj', if_neg (by omega)]
    have g2 : Frag o [ScanProg.inc "ji"] M (I (i + 1)) :=
      set_frag o (E := .op .add (.var "ji") (.const 1)) rfl (hIc (i + 1)) fun u hu => by
        obtain ⟨hk, hvl, hmx⟩ := hu
        have hji := vals_lookup hvl (x := "ji") (v := BitVec.ofNat 64 i) rfl
        refine ⟨BitVec.ofNat 64 (i + 1), by simp only [eval, hji]; rw [BitVec.ofNat_add]; rfl, ⟨_, hji⟩,
          kept_set hk (by decide) _, vals_cons (vals_sub hvl fun q hq => List.mem_cons_of_mem _ hq) rfl _,
          by omega, hmx⟩
    exact frag_append (xs := [_]) g1 g2
  have hloop := frag_count o (c := Syntax.eLt (Syntax.v "ji") (Syntax.v "jcnt"))
    (C := .cmp .less (.var "ji") (.var "jcnt"))
    rfl (lowK_any _ (k := .skip) (c := _) rfl) hIc
    (fun _ _ _ _ _ hy => by rw [show declared ScanProg.copyByte = [] from rfl] at hy; cases hy)
    (g := fun i => decide (i < L))
    (fun i u hu => by
      rw [eval_lt (x := i) (y := L) (by omega) (by omega) (by simp only [eval]; exact vals_lookup hu.2.1 rfl)
        (by simp only [eval]; exact vals_lookup hu.2.1 (v := BitVec.ofNat 64 L) rfl)]
      simp [bw]) hbody 0
  let P4 := P [("ji", BitVec.ofNat 64 0), ("jcnt", BitVec.ofNat 64 L), ("jx", BitVec.ofNat 64 d)]
  have hjx4 : ∀ u, P4 u → eval u (.var "jx") = some (BitVec.ofNat 64 d) := fun u hu => by
    simp only [eval]; exact vals_lookup hu.2 rfl
  have hmem4 : ∀ u, P4 u → ∀ a, memLoadByte u.memory u.memaddrs u.be a = memLoadByte s0.memory s0.memaddrs s0.be a :=
    fun u hu _ => kept_load hu.1 id
  have w5 : Frag o [ScanProg.windowCopy] P4 Q5 := by
    refine frag_ite o (C := .var "jx") rfl hQ5c (fun u hu => ⟨_, hjx4 u hu⟩) ?_ (noDecl _ rfl)
      (frag_nil o fun u ⟨hu, h0⟩ => ?_) (noDecl _ rfl)
    · refine frag_conseq hloop (fun u ⟨hu, _⟩ => ⟨kept_widen hu.1 (fun _ h => h) fun _ h => h.elim,
        vals_sub hu.2 (by simp [V0, V5]), Nat.zero_le _, fun j hj => ?_⟩) fun u ⟨i, hi, hg⟩ => ?_
      · rw [if_neg (Nat.not_lt_zero _), hmem4 u hu]; exact hwin0 j hj
      · simp only [decide_eq_false_iff_not] at hg
        obtain ⟨hk, hvl, hiL, hmx⟩ := hi
        have hiL' : i = L := by omega
        subst hiL'
        refine ⟨⟨kept_widen hk (fun _ h => h) hwa, fun j hj => ?_, fun _ hq => (nomatch hq), fun _ hq => (nomatch hq),
          by omega, fun x hx _ _ => hrest u hk x hx⟩, vals_sub hvl (by simp [V5])⟩
        rw [hmx j (by omega), if_pos hj]
    · rw [hjx4 u hu] at h0
      have hd0 : d = 0 := by
        have := congrArg BitVec.toNat (Option.some.inj h0)
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at this; exact this
      refine ⟨⟨kept_widen hu.1 (fun _ h => h) fun _ h => h.elim, fun j hj => ?_, fun _ hq => (nomatch hq),
        fun _ hq => (nomatch hq), by omega, fun x _ _ _ => hu.1.memory _ id⟩, vals_sub hu.2 (by simp [V0, V5])⟩
      rw [hmem4 u hu, show st.pos + j = st.base + j by omega]; exact hwin0 j (by omega)
  -- the window's new place and length, and the octets wanted
  let T (ws : List (Nat × Word)) (l : List (String × Value)) (u : PancakeState σ) : Prop :=
    Tail A J st.pos L s0 ws u ∧ Vals u l
  have hTc : ∀ ws l, Safe.ClockFree (T ws l) := fun _ _ => tail_clock fun _ _ h => h
  have hTz : ∀ ws l u, T ws l u → u.locals "jz" = some 0 ∧ u.locals "jsc" = some A ∧ Dom A u.memaddrs :=
    fun _ _ _ hu => ⟨kept_jz h hu.1.kept, kept_jsc h hu.1.kept, kept_dom h hu.1.kept⟩
  have hTb : ∀ ws l u, T ws l u → ∀ y ∈ ScanProg.locals, ∃ v, u.locals y = some v :=
    fun _ _ u hu => hbd u hu.1.kept
  let V6 : List (String × Value) := ("jwl", BitVec.ofNat 64 L) :: V5
  have w6 : Frag o [.assign "jwl" (Syntax.v "jcnt")] Q5 (T [] V6) :=
    set_frag o (E := .var "jcnt") rfl (hTc _ _) fun u hu =>
      ⟨BitVec.ofNat 64 L, by simp only [eval]; exact vals_lookup hu.2 rfl, hTb [] V5 u hu "jwl" (by decide),
        tail_set hu.1 (by decide) _, vals_cons hu.2 rfl _⟩
  have w7 : Frag o [ScanProg.setw sBase (Syntax.v "jp")] (T [] V6) (T [(sBase, BitVec.ofNat 64 st.pos)] V6) :=
    setw_frag o h.hA (by decide) (by decide) (E := .var "jp") rfl (hTc _ _) fun u hu =>
      ⟨(hTz _ _ u hu).2.1, (hTz _ _ u hu).2.2, BitVec.ofNat 64 st.pos,
        by simp only [eval]; exact vals_lookup hu.2 rfl,
        tail_store h.hA hu.1 (by decide) (by decide) (by simp) _, hu.2⟩
  have w8 : Frag o [ScanProg.setw sLen (Syntax.v "jwl")] (T [(sBase, BitVec.ofNat 64 st.pos)] V6)
      (T [(sLen, BitVec.ofNat 64 L), (sBase, BitVec.ofNat 64 st.pos)] V6) :=
    setw_frag o h.hA (by decide) (by decide) (E := .var "jwl") rfl (hTc _ _) fun u hu =>
      ⟨(hTz _ _ u hu).2.1, (hTz _ _ u hu).2.2, BitVec.ofNat 64 L,
        by simp only [eval]; exact vals_lookup hu.2 rfl,
        tail_store h.hA hu.1 (by decide) (by decide) (by simp [sBase, sLen]) _, hu.2⟩
  let W2 : List (Nat × Word) := [(sLen, BitVec.ofNat 64 L), (sBase, BitVec.ofNat 64 st.pos)]
  have w9 : Frag o [.assign "jx" (Syntax.eSub (Syntax.v "jsz") (Syntax.eAdd (Syntax.v "jp") (Syntax.v "jwl")))]
      (T W2 V6) (T W2 (("jx", BitVec.ofNat 64 N) :: V6)) :=
    set_frag o (E := .op .sub (.var "jsz") (.op .add (.var "jp") (.var "jwl"))) rfl (hTc _ _) fun u hu =>
      ⟨BitVec.ofNat 64 N, by
        simp only [eval, vals_lookup hu.2 (x := "jsz") (v := BitVec.ofNat 64 J.length) rfl,
          vals_lookup hu.2 (x := "jp") (v := BitVec.ofNat 64 st.pos) rfl,
          vals_lookup hu.2 (x := "jwl") (v := BitVec.ofNat 64 L) rfl]
        rw [← BitVec.ofNat_add, BitVec.ofNat_sub_ofNat_of_le _ _ (by omega) (by omega)]; congr 2; omega,
        hTb _ _ u hu "jx" (by decide), tail_set hu.1 (by decide) _, vals_cons hu.2 rfl _⟩
  have w10 : Frag o [.ite (Syntax.eLt (Syntax.n chunk) (Syntax.v "jx")) [.assign "jx" (lit chunk)] []]
      (T W2 (("jx", BitVec.ofNat 64 N) :: V6)) (T W2 (("jx", BitVec.ofNat 64 (min chunk N)) :: V6)) := by
    have hev : ∀ u, T W2 (("jx", BitVec.ofNat 64 N) :: V6) u →
        eval u (.cmp .less (.const (BitVec.ofNat 64 chunk)) (.var "jx")) = some (bw (decide (chunk < N))) :=
      fun u hu => eval_lt (by decide) (by omega) rfl (by simp only [eval]; exact vals_lookup hu.2 rfl)
    refine frag_ite o (C := .cmp .less (.const (BitVec.ofNat 64 chunk)) (.var "jx")) rfl (hTc _ _)
      (fun u hu => ⟨_, hev u hu⟩) ?_ (noDecl _ rfl) (frag_nil o fun u ⟨hu, h0⟩ => ?_) (noDecl _ rfl)
    · refine set_frag o (E := .op .add (.var "jz") (.const (BitVec.ofNat 64 chunk))) rfl (hTc _ _)
        fun u ⟨hu, hne⟩ => ?_
      rw [hev u hu] at hne
      have hc := bw_ne0 hne
      simp only [decide_eq_true_eq] at hc
      refine ⟨BitVec.ofNat 64 chunk, by simp [eval, (hTz _ _ u hu).1],
        ⟨_, vals_lookup hu.2 (v := BitVec.ofNat 64 N) rfl⟩,
        tail_set hu.1 (by decide) _, ?_⟩
      rw [Nat.min_eq_left (by omega)]
      exact vals_cons (vals_sub hu.2 fun q hq => List.mem_cons_of_mem _ hq) rfl _
    · rw [hev u hu] at h0
      have hc := bw_eq0 h0
      simp only [decide_eq_false_iff_not] at hc
      rw [Nat.min_eq_right (by omega)]
      exact hu
  have w11 : Frag o [ScanProg.setw sWant (Syntax.v "jx")] (T W2 (("jx", BitVec.ofNat 64 (min chunk N)) :: V6))
      (T ((sWant, BitVec.ofNat 64 (min chunk N)) :: W2) []) :=
    setw_frag o h.hA (by decide) (by decide) (E := .var "jx") rfl (hTc _ _) fun u hu =>
      ⟨(hTz _ _ u hu).2.1, (hTz _ _ u hu).2.2, BitVec.ofNat 64 (min chunk N),
        by simp only [eval]; exact vals_lookup hu.2 rfl,
        tail_store h.hA hu.1 (by decide) (by decide) (by simp [W2, sWant, sLen, sBase]) _, fun _ hq => (nomatch hq)⟩
  have w12 : Frag o [ScanProg.setw sStatus (Syntax.n wanted)] (T ((sWant, BitVec.ofNat 64 (min chunk N)) :: W2) [])
      (T ((sStatus, BitVec.ofNat 64 wanted) :: (sWant, BitVec.ofNat 64 (min chunk N)) :: W2) []) :=
    setw_frag o h.hA (by decide) (by decide) (E := .const (BitVec.ofNat 64 wanted)) rfl (hTc _ _)
      fun u hu => ⟨(hTz _ _ u hu).2.1, (hTz _ _ u hu).2.2, BitVec.ofNat 64 wanted, rfl,
        tail_store h.hA hu.1 (by decide) (by decide) (by simp [W2, sWant, sLen, sBase, sStatus]) _,
        fun _ hq => (nomatch hq)⟩
  refine frag_conseq (frag_append (xs := [_]) w1 (frag_append (xs := [_]) w2 (frag_append (xs := [_]) w3
    (frag_append (xs := [_]) w4 (frag_append (xs := [_]) w5 (frag_append (xs := [_]) w6 (frag_append (xs := [_]) w7
    (frag_append (xs := [_]) w8 (frag_append (xs := [_]) w9 (frag_append (xs := [_]) w10
    (frag_append (xs := [_]) w11 w12))))))))))) (fun _ h => h) fun u hu => ?_
  have hk := hu.1.kept
  have hr := hu.1.rest
  have hs := hu.1.stored
  have hrest : ∀ x, x < sWindow → x % 8 = 0 → x ≠ sStatus → x ≠ sWant → x ≠ sLen → x ≠ sBase →
      u.memory (at_ A x) = s0.memory (at_ A x) := fun x h1 h2 h3 h4 h5 h6 =>
    hr x h1 h2 (by simp [W2]; exact ⟨Ne.symm h3, Ne.symm h4, Ne.symm h5, Ne.symm h6⟩)
  have hwant := hs (sWant, BitVec.ofNat 64 (min chunk N)) (by simp only [List.mem_cons, true_or, or_true])
  refine ⟨hk, hs (sStatus, BitVec.ofNat 64 wanted) (by simp), ⟨?_, hs (sBase, BitVec.ofNat 64 st.pos) (by simp [W2]),
    ?_, ?_, ?_, ?_, fun i hi => ?_, fun k hk' => ?_⟩, by rw [← hN]; exact hwant⟩
  · rw [hrest sSize (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact h.area.size
  · rw [hs (sLen, BitVec.ofNat 64 L) (by simp [W2])]; simp only [hL]
  · rw [hrest sPos (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact h.area.pos
  · rw [hrest sKeyed (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact h.area.keyed
  · rw [hrest sCount (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact h.area.count
  · exact hu.1.win i (by simp only at hi; omega)
  · rw [← h.area.key k hk', hk.memaddrs, hk.be]
    refine readByteArray_congr 16 _ fun j hj => ?_
    rw [at_add]
    simp only [memLoadByte, align_at h.hA]
    rw [hrest _ (by omega) (by omega) (by simp only [sKey, sStatus, sGroups, groupsMax, groupSlot]; omega)
      (by simp only [sKey, sWant, sGroups, groupsMax, groupSlot]; omega)
      (by simp only [sKey, sLen, sGroups, groupsMax, groupSlot]; omega)
      (by simp only [sKey, sBase, sGroups, groupsMax, groupSlot]; omega)]

end DN.News.ScanRun
