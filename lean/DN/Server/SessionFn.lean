-- SPDX-License-Identifier: AGPL-3.0-or-later
import DN.Server.SessionClassify

/-!
# DN.Server.SessionFn

What `viewClassify` and `listClassify` share. From their entry `VEntry`: the head finding the connection's block and
the line's length, the scan of the line's words and their bound checks, the arguments' count, their own
declarations (`fdecs_frag`). The state within (`FAt`), given the locals `nms` a function declares and the own words
`offs` it writes; its words checked, an own word written, the reply's code set (`FEnd`) and given back
(`give_run`). The fragments hold if the run goes on.
-/

namespace DN.Server.SessionClassify

open DN.Compiler DN.Compiler.Wp DN.Compiler.WpRet DN.Compiler.Bytes DN.Compiler.Frag DN.News DN.News.WordsRun
  DN.News.FrameSpec DN.Server.SessionWords
open DN.Server.SessionLayout (texts ownOff ownTexts ownRet conns connSlot cFramer)
open DN.News.FramerCode (bw bw_ne0 bw_eq0 eval_eq)

variable {σ : Type}

/-! ### The own words a function writes, apart from those it reads -/

/-- The addresses of the own words at `offs`. -/
def ownWords (offs : List Nat) (b : Word) : List Word := offs.map fun x => b + BitVec.ofNat 64 (ownOff + x)

/-- Own words aligned, below the texts, among those `classify` lets the functions it calls write. -/
def OffsOk (offs : List Nat) : Prop :=
  ∀ X ∈ offs, (ownOff + X) % 8 = 0 ∧ ownOff + X + 8 ≤ ownOff + ownTexts ∧ X ∈ clsOffs

/-- A place `x` past the own words is none of them. -/
theorem not_ownWords {offs : List Nat} (hoff : OffsOk offs) {b : Word} (hb : b.toNat % 8 = 0) {x : Nat}
    (hx : ownOff + ownTexts ≤ x) (h64 : x < 2 ^ 64) : byteAlign (b + BitVec.ofNat 64 x) ∉ ownWords offs b := by
  simp only [ownWords, List.mem_map, not_exists, not_and]
  intro X hX e
  obtain ⟨h1, h2, -⟩ := hoff X hX
  exact own_far hb h1 (by omega) h64 e.symm

theorem ownWords_cls {offs : List Nat} (hoff : OffsOk offs) (b : Word) : ∀ a ∈ ownWords offs b, a ∈ clsWords b := by
  intro a ha
  obtain ⟨X, hX, rfl⟩ := List.mem_map.mp ha
  exact List.mem_map.mpr ⟨X, (hoff X hX).2.2, rfl⟩

/-! ### The program's shared text -/

section FnTree
open DN.Compiler.Syntax DN.Server.Session
open DN.Server.SessionStore (keptIn ld)
open DN.News.SessionSpec (lineLimit)

/-- The connection and its line, bounds checked. -/
def fnHead : List PStmt :=
  [keptIn (v "c") (conns - 1), .dec "blk" (atOff (record (v "c")) cFramer),
   .dec "kept" (ld (atOff (v "blk") 32)), keptIn (v "kept") lineLimit]

/-- The words' places and lengths, bounds checked. -/
def fnKept : List PStmt :=
  [keptIn (v "s1") lineLimit, keptIn (v "l1") lineLimit, keptIn (v "s2") lineLimit, keptIn (v "l2") lineLimit,
   keptIn (v "s3") lineLimit, keptIn (v "l3") lineLimit]

/-- The reply's code set. -/
def fsay (r : News.CommandSpec.Reply) : PStmt := .assign "r" (n (replyCode r))

/-- The arguments' count, and `r` the syntax error's code. -/
def fnArgs : List PStmt := [.dec "args" (eSub (v "w") (n 1)), .dec "r" (n (replyCode .syntax))]

end FnTree

/-- **A branch on a test of value `bw p`**: each arm shown under what `p` is. -/
theorem frag_bw (o : Oracle σ) {c : Syntax.PExpr} {C : PancakeExp} (hc : Lower.lowerExp c = some C)
    {t e : List Syntax.PStmt} (hlt : LowKK t) (hle : LowKK e) {P P' : Assn σ} (hP' : Safe.ClockFree P') {p : Bool}
    (hev : ∀ s, P s → eval s C = some (bw p)) (ht : p = true → Frag o t P P')
    (htc : ∀ u y v, P' u → y ∈ declared t → P' (restore u y v)) (he : p = false → Frag o e P P')
    (hec : ∀ u y v, P' u → y ∈ declared e → P' (restore u y v)) : Frag o [.ite c t e] P P' :=
  frag_ite o hc hP' (fun s h => ⟨_, hev s h⟩)
    (frag_pure (p = true) (fun s ⟨h, hne⟩ => by rw [hev s h] at hne; exact bw_ne0 hne) hlt
      fun hp => frag_conseq (ht hp) (fun _ h => h.1) fun _ h => h) htc
    (frag_pure (p = false) (fun s ⟨h, h0⟩ => by rw [hev s h] at h0; exact bw_eq0 h0) hle
      fun hp => frag_conseq (he hp) (fun _ h => h.1) fun _ h => h) hec

/-! ### The state within -/

/-- The locals the state within fixes. -/
def fFixed : List String := ["blk", "kept", "w", "s1", "l1", "s2", "l2", "s3", "l3", "args", "r"]

/-- Within a function `classify` calls, once its locals are declared, from its entry `e`: every local but `nms` and
every word but `ownWords offs` as at `e`, the line's block and length, the words' count and places, the arguments'
count, `r` the code `R`, the locals `bnd` bound. -/
structure FAt (nms bnd : List String) (offs : List Nat) (R : Nat) (b : Word) (ci : Nat) (L : List Byte)
    (e u : PancakeState σ) : Prop where
  loc : ∀ y, y ∉ nms → u.locals y = e.locals y
  memory : ∀ a, a ∉ ownWords offs b → u.memory a = e.memory a
  memaddrs : u.memaddrs = e.memaddrs
  be : u.be = e.be
  base : u.baseAddr = e.baseAddr
  code : u.code = e.code
  blk : u.locals "blk" = some (SessionFrame.blockAt b ci)
  kept : u.locals "kept" = some (BitVec.ofNat 64 L.length)
  w : u.locals "w" = some (BitVec.ofNat 64 (spans L).length)
  s1 : u.locals "s1" = some (BitVec.ofNat 64 ((spans L).getD 1 (0, 0)).1)
  l1 : u.locals "l1" = some (BitVec.ofNat 64 ((spans L).getD 1 (0, 0)).2)
  s2 : u.locals "s2" = some (BitVec.ofNat 64 ((spans L).getD 2 (0, 0)).1)
  l2 : u.locals "l2" = some (BitVec.ofNat 64 ((spans L).getD 2 (0, 0)).2)
  s3 : u.locals "s3" = some (BitVec.ofNat 64 ((spans L).getD 3 (0, 0)).1)
  l3 : u.locals "l3" = some (BitVec.ofNat 64 ((spans L).getD 3 (0, 0)).2)
  args : u.locals "args" = some (BitVec.ofNat 64 ((spans L).length - 1))
  r : u.locals "r" = some (BitVec.ofNat 64 R)
  bound : ∀ y ∈ bnd, ∃ v, u.locals y = some v

section At
variable {nms bnd : List String} {offs : List Nat} {R : Nat}

theorem fat_clock (b : Word) (ci : Nat) (L : List Byte) (e : PancakeState σ) :
    Safe.ClockFree (FAt nms bnd offs R b ci L e) := fun _ _ h => { h with }

theorem fat_and {b : Word} {ci : Nat} {L : List Byte} {e : PancakeState σ} {q : Assn σ} (hq : Safe.ClockFree q) :
    Safe.ClockFree (fun u => FAt nms bnd offs R b ci L e u ∧ q u) := fun u k h =>
  ⟨fat_clock b ci L e u k h.1, hq u k h.2⟩

/-- The line's octets read through the words written. -/
theorem fat_line (hoff : OffsOk offs) {b : Word} {ci K : Nat} {L : List Byte} {e u : PancakeState σ}
    (he : VEntry b ci K L e) (h : FAt nms bnd offs R b ci L e u) : LineIn (SessionFrame.blockAt b ci) L u := by
  have hsh := he.short
  have h8 := SessionAppend.block_facts.limit
  refine ⟨h.blk, h.kept, fun j hj => ?_, by omega⟩
  obtain ⟨i1, i2⟩ := SessionAppend.block_in (x := 40 + j) he.hci (by rw [SessionAppend.block_facts.head]; omega)
  have hs := SessionAppend.size_lt
  have hb := he.bytes j hj
  rw [add_ofNat, SessionAppend.blockAt_off] at hb ⊢
  rw [h.memaddrs, h.be, load_of_word (h.memory _ (not_ownWords hoff he.hb (by omega) (by omega)))]
  exact hb

/-- The texts read through the words written. -/
theorem fat_texts (hoff : OffsOk offs) {b : Word} {ci K : Nat} {L : List Byte} {e u : PancakeState σ}
    (he : VEntry b ci K L e) (h : FAt nms bnd offs R b ci L e u) :
    SessionAppend.TextsIn b u.memory u.memaddrs u.be := by
  intro k hk i hi
  have hb := he.texts k hk i hi
  have ht := SessionAppend.text_below hk
  obtain ⟨T, hT⟩ := SessionAppend.lay
  have hl : (texts.getD k []).length = Session.textLen k := rfl
  rw [hT.eq] at ht
  have := hT.room
  rw [add_ofNat] at hb ⊢
  rw [h.memaddrs, h.be, load_of_word (h.memory _ (not_ownWords hoff he.hb (by omega) (by omega)))]
  exact hb

/-- The state within from another, the fixed locals but `r` as there. -/
theorem fat_mk {b : Word} {ci : Nat} {L : List Byte} {e u0 u : PancakeState σ} (h : FAt nms bnd offs R b ci L e u0)
    (fx : ∀ y ∈ fFixed, y ≠ "r" → u.locals y = u0.locals y) (hloc : ∀ y, y ∉ nms → u.locals y = e.locals y)
    (hmem : ∀ a, a ∉ ownWords offs b → u.memory a = e.memory a) (hd : u.memaddrs = e.memaddrs) (hbe : u.be = e.be)
    (hba : u.baseAddr = e.baseAddr) (hco : u.code = e.code) {R' : Nat} (hr : u.locals "r" = some (BitVec.ofNat 64 R'))
    (hb : ∀ y ∈ bnd, ∃ v, u.locals y = some v) : FAt nms bnd offs R' b ci L e u :=
  ⟨hloc, hmem, hd, hbe, hba, hco, by rw [fx "blk" (by decide) (by decide)]; exact h.blk,
    by rw [fx "kept" (by decide) (by decide)]; exact h.kept, by rw [fx "w" (by decide) (by decide)]; exact h.w,
    by rw [fx "s1" (by decide) (by decide)]; exact h.s1, by rw [fx "l1" (by decide) (by decide)]; exact h.l1,
    by rw [fx "s2" (by decide) (by decide)]; exact h.s2, by rw [fx "l2" (by decide) (by decide)]; exact h.l2,
    by rw [fx "s3" (by decide) (by decide)]; exact h.s3, by rw [fx "l3" (by decide) (by decide)]; exact h.l3,
    by rw [fx "args" (by decide) (by decide)]; exact h.args, hr, hb⟩

theorem fat_but {b : Word} {ci : Nat} {L : List Byte} {e u0 u : PancakeState σ} (h : FAt nms bnd offs R b ci L e u0)
    {xs : List String} (h2 : SessionCheck.ButFor xs u0 u) (hxs : ∀ y ∈ xs, y ∈ nms ∧ y ∉ fFixed)
    (hk : ∀ y ∈ bnd, (u0.locals y).isSome → (u.locals y).isSome) : FAt nms bnd offs R b ci L e u := by
  have fx : ∀ y ∈ fFixed, u.locals y = u0.locals y := fun y hy => h2.locals y fun e => (hxs y e).2 hy
  exact fat_mk h (fun y hy _ => fx y hy) (fun y hy => by rw [h2.locals y fun e => hy (hxs y e).1]; exact h.loc y hy)
    (fun a ha => by rw [h2.memory]; exact h.memory a ha) (h2.memaddrs.trans h.memaddrs) (h2.be.trans h.be)
    (h2.base.trans h.base) (h2.code.trans h.code) (by rw [fx "r" (by decide)]; exact h.r) fun y hy =>
      Option.isSome_iff_exists.mp (hk y hy (Option.isSome_iff_exists.mpr (h.bound y hy)))

theorem fat_set {b : Word} {ci : Nat} {L : List Byte} {e u : PancakeState σ} (h : FAt nms bnd offs R b ci L e u)
    {x : String} (hx : x ∈ nms ∧ x ∉ fFixed) (v : Value) : FAt nms bnd offs R b ci L e (setL u x v) :=
  fat_but h (SessionCheck.but_set (SessionCheck.but_refl [x] u) (by simp) v)
    (fun y hy => by simp at hy; subst hy; exact hx) fun y _ hy => by
      simp only [setL, setLocal]; split <;> simp_all

theorem fat_restore {b : Word} {ci : Nat} {L : List Byte} {e u : PancakeState σ} (h : FAt nms bnd offs R b ci L e u)
    {y : String} (hy : y ∈ nms ∧ y ∉ fFixed ∧ y ∉ bnd) (v : Option Value) :
    FAt nms bnd offs R b ci L e (restore u y v) :=
  fat_but (xs := [y]) h ⟨fun x hx => by
      have : x ≠ y := fun e => hx (by simp [e])
      simp only [restore, resVar, if_neg this], rfl, rfl, rfl, rfl, rfl, rfl⟩
    (fun x hx => by simp at hx; subst hx; exact ⟨hy.1, hy.2.1⟩) fun x hx hb => by
      have : x ≠ y := fun e => hy.2.2 (e ▸ hx)
      simp only [restore, resVar, if_neg this]; exact hb

/-- Words but the own ones as at `e`, one own word written. -/
theorem ownWords_store {offs : List Nat} {b : Word} {X : Nat} (hX : X ∈ offs) {m m0 m1 : Word → Word}
    (hm : ∀ a, a ≠ b + BitVec.ofNat 64 (ownOff + X) → m a = m0 a) (h0 : ∀ a, a ∉ ownWords offs b → m0 a = m1 a) :
    ∀ a, a ∉ ownWords offs b → m a = m1 a := fun a ha => by
  have hne : a ≠ b + BitVec.ofNat 64 (ownOff + X) := fun heq => ha (by
    rw [heq]; simp only [ownWords, List.mem_map]; exact ⟨X, hX, rfl⟩)
  rw [hm a hne]; exact h0 a ha

/-- An own word written. -/
theorem fat_store {b : Word} {ci : Nat} {L : List Byte} {e u : PancakeState σ} (h : FAt nms bnd offs R b ci L e u)
    {X : Nat} (hX : X ∈ offs) {m : Word → Word} (hm : ∀ a, a ≠ b + BitVec.ofNat 64 (ownOff + X) → m a = u.memory a) :
    FAt nms bnd offs R b ci L e { u with memory := m } :=
  { h with memory := ownWords_store hX hm h.memory }

/-- The reply's code `R'` set, the rest kept. -/
theorem fat_say {b : Word} {ci : Nat} {L : List Byte} {e u : PancakeState σ} (h : FAt nms bnd offs R b ci L e u)
    (hr : "r" ∈ nms) (R' : Nat) : FAt nms bnd offs R' b ci L e (setL u "r" (BitVec.ofNat 64 R')) := by
  have fx : ∀ y, y ≠ "r" → (setL u "r" (BitVec.ofNat 64 R')).locals y = u.locals y := fun y hy => by
    simp only [setL, setLocal, if_neg hy]
  exact fat_mk h (fun y _ hy => fx y hy) (fun y hy => by rw [fx y (fun e => hy (e ▸ hr))]; exact h.loc y hy)
    h.memory h.memaddrs h.be h.base h.code (by simp [setL, setLocal]) fun y hy => by
      by_cases e1 : y = "r"
      · subst e1; simp [setL, setLocal]
      · rw [fx y e1]; exact h.bound y hy

theorem fargs_eval {b : Word} {ci : Nat} {L : List Byte} {e u : PancakeState σ} (h : FAt nms bnd offs R b ci L e u)
    (hsh : L.length < 2 ^ 62) (k : Nat) (hk : k < 2 ^ 63) :
    eval u (.cmp .equal (.var "args") (.const (BitVec.ofNat 64 k))) =
      some (bw (decide ((spans L).length - 1 = k))) := by
  have := spans_length L
  exact eval_eq (by omega) (by omega) (by simp only [eval]; exact h.args) rfl

theorem fcmd {b : Word} {ci K : Nat} {L : List Byte} {e u : PancakeState σ} (he : VEntry b ci K L e)
    (h : FAt nms bnd offs R b ci L e u) (hc : "cmd" ∉ nms) : u.locals "cmd" = some (BitVec.ofNat 64 K) := by
  rw [h.loc "cmd" hc]; exact he.cmd

/-- The word of the line at place one, in `s1` and `l1`. -/
theorem fword1 (hoff : OffsOk offs) {b : Word} {ci K : Nat} {L : List Byte} {e u : PancakeState σ}
    (he : VEntry b ci K L e) (h : FAt nms bnd offs R b ci L e u) (h2 : 2 ≤ (spans L).length) :
    WordAt "s1" "l1" (SessionFrame.blockAt b ci) (BitVec.ofNat 64 ((spans L).getD 1 (0, 0)).1)
      (cut L ((spans L).getD 1 (0, 0))) u :=
  wordAt_of (fat_line hoff he h) (spans_getD_mem (by omega)) h.s1 h.l1

/-- …at place two, in `s2` and `l2`. -/
theorem fword2 (hoff : OffsOk offs) {b : Word} {ci K : Nat} {L : List Byte} {e u : PancakeState σ}
    (he : VEntry b ci K L e) (h : FAt nms bnd offs R b ci L e u) (h3 : 3 ≤ (spans L).length) :
    WordAt "s2" "l2" (SessionFrame.blockAt b ci) (BitVec.ofNat 64 ((spans L).getD 2 (0, 0)).1)
      (cut L ((spans L).getD 2 (0, 0))) u :=
  wordAt_of (fat_line hoff he h) (spans_getD_mem (by omega)) h.s2 h.l2

/-- …at place three, in `s3` and `l3`. -/
theorem fword3 (hoff : OffsOk offs) {b : Word} {ci K : Nat} {L : List Byte} {e u : PancakeState σ}
    (he : VEntry b ci K L e) (h : FAt nms bnd offs R b ci L e u) (h4 : 4 ≤ (spans L).length) :
    WordAt "s3" "l3" (SessionFrame.blockAt b ci) (BitVec.ofNat 64 ((spans L).getD 3 (0, 0)).1)
      (cut L ((spans L).getD 3 (0, 0))) u :=
  wordAt_of (fat_line hoff he h) (spans_getD_mem (by omega)) h.s3 h.l3

end At

theorem ne0_eval {u : PancakeState σ} {x : String} {n : Nat} (hn : n < 2 ^ 63)
    (h : u.locals x = some (BitVec.ofNat 64 n)) :
    eval u (.cmp .equal (.cmp .equal (.var x) (.const (BitVec.ofNat 64 0))) (.const (BitVec.ofNat 64 0))) =
      some (bw (decide (n ≠ 0))) := by
  have e1 := eval_eq (t := u) (a := .var x) (b := .const (BitVec.ofNat 64 0)) (x := n) (y := 0)
    (by omega) (by decide) (by simp only [eval]; exact h) rfl
  simp only [eval] at e1 ⊢
  rw [e1]
  by_cases e : n = 0 <;> simp [e, bw]

/-! ### From the entry to the state within -/

/-- A bound check that holds: nothing happens. -/
theorem keptIn_skip (o : Oracle σ) {x : String} {hi : Nat} (hhi : hi < 2 ^ 63) {P : Assn σ}
    (hcl : Safe.ClockFree P) (hP : ∀ s, P s → ∃ n, s.locals x = some (BitVec.ofNat 64 n) ∧ n ≤ hi) :
    Frag o [SessionStore.keptIn (Syntax.v x) hi] P P :=
  frag_oneR (SessionRun.keptIn_lower rfl hi) rfl hcl fun R => SessionRun.keptG_pass o R hhi fun s h => by
    obtain ⟨n, hn, hle⟩ := hP s h; exact ⟨n, hle, by simp only [eval]; exact hn⟩

theorem lowKK_fnHead : LowKK fnHead :=
  lowKK_append (xs := [_]) (lowKK_one rfl (SessionRun.keptIn_lower rfl _))
    (lowKK_append (xs := [_]) (lowKK_dec SessionCheck.blk_lower)
      (lowKK_append (xs := [_]) (lowKK_dec rfl) (lowKK_one rfl (SessionRun.keptIn_lower rfl _))))

/-- After the head: the block and the line's length bound, the rest as at `e`. -/
def FHead (b : Word) (ci : Nat) (L : List Byte) (e u : PancakeState σ) : Prop :=
  u.locals "blk" = some (SessionFrame.blockAt b ci) ∧ u.locals "kept" = some (BitVec.ofNat 64 L.length) ∧
    (∀ y, y ∉ ["blk", "kept"] → u.locals y = e.locals y) ∧ u.memory = e.memory ∧ u.memaddrs = e.memaddrs ∧
    u.be = e.be ∧ u.baseAddr = e.baseAddr ∧ u.code = e.code

/-- **The head**: connection `ci`'s block and the line's length. -/
theorem fhead_frag (o : Oracle σ) {b : Word} {ci K : Nat} {L : List Byte} {e : PancakeState σ}
    (he : VEntry b ci K L e) : Frag o fnHead (Like e) (FHead b ci L e) := by
  have hci := he.hci
  have hsh := he.short
  obtain ⟨_, _, _, h4, h5, _, _, h8⟩ := SessionAppend.block_facts
  let P1 : Assn σ := fun u => u.locals "blk" = some (SessionFrame.blockAt b ci) ∧
    (∀ y, y ∉ ["blk"] → u.locals y = e.locals y) ∧ u.memory = e.memory ∧ u.memaddrs = e.memaddrs ∧
    u.be = e.be ∧ u.baseAddr = e.baseAddr ∧ u.code = e.code
  have f1 := keptIn_skip o (x := "c") (hi := conns - 1) (by omega) (like_clock e) fun s h =>
    ⟨ci, by rw [h.locals]; exact he.c, by omega⟩
  have f2 : Frag o [.dec "blk" (Syntax.atOff (Session.record (Syntax.v "c")) cFramer)] (Like e) P1 :=
    frag_dec o SessionCheck.blk_lower fun s h => ⟨SessionFrame.blockAt b ci, by
        rw [SessionCheck.blk_eval (h.base.trans he.base) (by rw [h.locals]; exact he.c), SessionCheck.gnBlock_eq],
      by simp [setLocal], fun y hy => by simp at hy; simp [setLocal, hy, h.locals], h.memory, h.memaddrs, h.be,
      h.base, h.code⟩
  -- the line's length, from the block's word
  obtain ⟨i1, i2⟩ := SessionAppend.block_in (x := 32) hci (by rw [SessionAppend.block_facts.head, h8]; omega)
  have hal : (SessionAppend.tOff + ci * connSlot + cFramer + 32) % 8 = 0 := by
    obtain ⟨T, hT⟩ := SessionAppend.lay
    have a2 := SessionAppend.block_facts.slotAl
    have := hT.aligned
    rw [hT.eq]
    have : ci * connSlot % 8 = 0 := by rw [Nat.mul_mod, a2]; simp
    omega
  have hadr : e.memaddrs (SessionFrame.blockAt b ci + BitVec.ofNat 64 32) = true := by
    have := SessionAppend.nums.own64
    rw [SessionAppend.blockAt_off]; exact he.hcov.2 _ (by simp only [Analyzer.floor]; omega) i2 hal
  have f3 : Frag o [.dec "kept" (SessionStore.ld (Syntax.atOff (Syntax.v "blk") 32))] P1 (FHead b ci L e) :=
    frag_dec o (E := .loadWord (.op .add (.var "blk") (.const (BitVec.ofNat 64 32)))) rfl fun s h =>
      ⟨BitVec.ofNat 64 L.length, by
        simp only [eval, h.1, h.2.2.2.1, hadr, if_true, h.2.2.1, he.kept],
      by simp [setLocal, h.1], by simp [setLocal], fun y hy => by
        simp at hy; simp [setLocal, hy.2]; exact h.2.1 y (by simp [hy.1]), h.2.2.1, h.2.2.2.1, h.2.2.2.2.1,
      h.2.2.2.2.2.1, h.2.2.2.2.2.2⟩
  have f4 := keptIn_skip o (x := "kept") (hi := News.SessionSpec.lineLimit) (by rw [h8]; decide)
    (P := FHead b ci L e) (fun _ _ h => h) fun s h => ⟨L.length, h.2.1, hsh⟩
  exact frag_append (xs := [_]) f1 (frag_append (xs := [_]) f2 (frag_append (xs := [_]) f3 f4))

/-- After the scan: its words from the head's state `u1`. -/
def FScan (b : Word) (ci : Nat) (L : List Byte) (e u : PancakeState σ) : Prop :=
  ∃ u1, FHead b ci L e u1 ∧ WordsAt L (scanNmFrom 0 4) u1 u

theorem fscan_clock (b : Word) (ci : Nat) (L : List Byte) (e : PancakeState σ) : Safe.ClockFree (FScan b ci L e) :=
  fun _ _ ⟨u1, h1, h2⟩ => ⟨u1, h1, { h2 with }⟩

/-- If it goes on, the scan of the line's words reaches `FScan`. -/
theorem fscan_frag (o : Oracle σ) {b : Word} {ci K : Nat} {L : List Byte} {e : PancakeState σ}
    (he : VEntry b ci K L e) : Frag o (Session.scanWords 4) (FHead b ci L e) (FScan b ci L e) :=
  frag_each o (lowK_any _ (k := .skip) (c := _) rfl) fun u1 h1 => by
    have hl : LineIn (SessionFrame.blockAt b ci) L u1 := ⟨h1.1, h1.2.1, fun j hj => by
      rw [h1.2.2.2.1, h1.2.2.2.2.1, h1.2.2.2.2.2.1]; exact he.bytes j hj, by have := he.short62; omega⟩
    exact frag_conseq (scanWords_frag o 4 nm4_ok (by decide) (by decide) hl) (fun _ h => h)
      fun u hu => ⟨u1, h1, hu⟩

/-- The six bound checks of the second to fourth words. -/
theorem fkept_frag (o : Oracle σ) {b : Word} {ci K : Nat} {L : List Byte} {e : PancakeState σ}
    (he : VEntry b ci K L e) : Frag o fnKept (FScan b ci L e) (FScan b ci L e) := by
  have h8 := SessionAppend.block_facts.limit
  have hsh := he.short
  have sl : ∀ (j : Nat) (hj : j < 4) (sel : String × String → String), (sel = Prod.fst ∨ sel = Prod.snd) →
      ∀ s, FScan b ci L e s → ∃ n, s.locals (sel (scanNmFrom 0 4)[j]) = some (BitVec.ofNat 64 n) ∧
        n ≤ News.SessionSpec.lineLimit := fun j hj sel hs s ⟨u1, _, h2⟩ => by
    have := h2.slots j (by simp [scanNmFrom]; omega)
    have hb := spans_getD_le L j
    rcases hs with rfl | rfl
    · exact ⟨_, this.1, by omega⟩
    · exact ⟨_, this.2, by omega⟩
  have k : ∀ (j : Nat) (hj : j < 4) (sel : String × String → String), (sel = Prod.fst ∨ sel = Prod.snd) →
      Frag o [SessionStore.keptIn (Syntax.v (sel (scanNmFrom 0 4)[j])) News.SessionSpec.lineLimit]
        (FScan b ci L e) (FScan b ci L e) := fun j hj sel hs =>
    keptIn_skip o (by rw [h8]; decide) (fscan_clock b ci L e) (sl j hj sel hs)
  exact frag_append (xs := [_]) (k 1 (by decide) Prod.fst (Or.inl rfl)) (frag_append (xs := [_])
    (k 1 (by decide) Prod.snd (Or.inr rfl)) (frag_append (xs := [_]) (k 2 (by decide) Prod.fst (Or.inl rfl))
    (frag_append (xs := [_]) (k 2 (by decide) Prod.snd (Or.inr rfl)) (frag_append (xs := [_])
    (k 3 (by decide) Prod.fst (Or.inl rfl)) (k 3 (by decide) Prod.snd (Or.inr rfl))))))

/-- After `args` and `r`: from a scanned state `u2`. -/
def FArgs (b : Word) (ci : Nat) (L : List Byte) (e u : PancakeState σ) : Prop :=
  ∃ u2, FScan b ci L e u2 ∧ (∀ y, y ∉ ["args", "r"] → u.locals y = u2.locals y) ∧
    u.locals "args" = some (BitVec.ofNat 64 ((spans L).length - 1)) ∧
    u.locals "r" = some (BitVec.ofNat 64 (Session.replyCode .syntax)) ∧
    u.memory = u2.memory ∧ u.memaddrs = u2.memaddrs ∧ u.be = u2.be ∧ u.baseAddr = u2.baseAddr ∧ u.code = u2.code

/-- **The arguments' count** and `r`, on a line of words. -/
theorem fargs_frag (o : Oracle σ) {b : Word} {ci : Nat} {L : List Byte} {e : PancakeState σ}
    (hw1 : 1 ≤ (spans L).length) (hsh : L.length < 2 ^ 62) : Frag o fnArgs (FScan b ci L e) (FArgs b ci L e) := by
  have hsp := spans_length L
  let P1 : Assn σ := fun u => ∃ u2, FScan b ci L e u2 ∧ (∀ y, y ∉ ["args"] → u.locals y = u2.locals y) ∧
    u.locals "args" = some (BitVec.ofNat 64 ((spans L).length - 1)) ∧
    u.memory = u2.memory ∧ u.memaddrs = u2.memaddrs ∧ u.be = u2.be ∧ u.baseAddr = u2.baseAddr ∧ u.code = u2.code
  have f1 : Frag o [.dec "args" (Syntax.eSub (Syntax.v "w") (Syntax.n 1))] (FScan b ci L e) P1 :=
    frag_dec o (E := .op .sub (.var "w") (.const 1)) rfl fun s h => ⟨_, by
      obtain ⟨u1, _, h2⟩ := h
      simp only [eval, h2.hw]
      rw [show (1 : Word) = BitVec.ofNat 64 1 from rfl, SessionCheck.sub_small _ 1 hw1 (by omega)],
      s, h, fun y hy => by simp at hy; simp [setLocal, hy], by simp [setLocal], rfl, rfl, rfl, rfl, rfl⟩
  have f2 : Frag o [.dec "r" (Syntax.n (Session.replyCode .syntax))] P1 (FArgs b ci L e) :=
    frag_dec o (E := .const (BitVec.ofNat 64 (Session.replyCode .syntax))) rfl fun s ⟨u2, h, hl, ha, rest⟩ =>
      ⟨BitVec.ofNat 64 (Session.replyCode .syntax), rfl, u2, h, fun y hy => by
      simp at hy; simp only [setLocal, if_neg hy.2]; exact hl y (by simp [hy.1]),
      by simp [setLocal, ha], by simp [setLocal], rest⟩
  exact frag_append (xs := [_]) f1 f2

/-- **A function's own declarations**, constants `ds`: the state within, each holding its constant. -/
theorem fdecs_frag (o : Oracle σ) {nms bnd : List String} {offs : List Nat} {b : Word} {ci : Nat} {L : List Byte}
    {e : PancakeState σ} (ds : List (String × Nat)) (hd : ds.Pairwise (fun a b => a.1 ≠ b.1))
    (hnm : ∀ y ∈ ds.map Prod.fst ++ scanNames (scanNmFrom 0 4) ++ ["blk", "kept", "args", "r"], y ∈ nms)
    (hfx : ∀ y ∈ ds.map Prod.fst, y ∉ fFixed) (hbd : ∀ y ∈ bnd, y ∈ ds.map Prod.fst) :
    Frag o (ds.map fun p => .dec p.1 (Syntax.n p.2)) (FArgs b ci L e)
      (fun u => FAt nms bnd offs (Session.replyCode .syntax) b ci L e u ∧
        ∀ p ∈ ds, u.locals p.1 = some (BitVec.ofNat 64 p.2)) :=
  frag_each o (lowKK_decsC ds) fun u3 h3 => frag_conseq (decsC_frag o u3 ds [] (by simpa using hd))
      (fun u (hu : Like u3 u) => ⟨fun _ h => by simp at h, fun y _ => by rw [hu.locals], hu.memory, hu.memaddrs,
        hu.be, hu.ffi, hu.base, hu.code⟩) fun u hu => by
    simp only [List.nil_append] at hu
    obtain ⟨u2, ⟨u1, h1, h2⟩, hl3, hargs, hr, hm, hdm, hbe, hba, hc⟩ := h3
    have z : ∀ y, y ∉ ds.map Prod.fst → u.locals y = u3.locals y := hu.frame
    have fx : ∀ y ∈ fFixed, y ∉ ds.map Prod.fst := fun y hy e => hfx y e hy
    have a3 : ∀ y, y ∉ ds.map Prod.fst → y ∉ ["args", "r"] → u.locals y = u2.locals y := fun y a b =>
      (z y a).trans (hl3 y b)
    have sl1 := h2.slots 1 (by decide)
    have sl2 := h2.slots 2 (by decide)
    have sl3 := h2.slots 3 (by decide)
    have back : ∀ y, y ∉ ds.map Prod.fst → y ∉ ["args", "r"] → y ∉ scanNames (scanNmFrom 0 4) →
        u.locals y = u1.locals y := fun y a b c => (a3 y a b).trans (h2.frame y c)
    refine ⟨⟨fun y hy => ?_, fun a _ => ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun y hy => ?_⟩,
      hu.val⟩
    · have n1 : y ∉ ds.map Prod.fst := fun e => hy (hnm y (by simp [e]))
      have n2 : y ∉ ["args", "r"] := fun e => hy (hnm y (by simp at e; rcases e with rfl | rfl <;> simp))
      have n3 : y ∉ scanNames (scanNmFrom 0 4) := fun e => hy (hnm y (by simp [e]))
      have n4 : y ∉ ["blk", "kept"] := fun e => hy (hnm y (by simp at e; rcases e with rfl | rfl <;> simp))
      rw [back y n1 n2 n3]; exact h1.2.2.1 y n4
    · rw [hu.memory, hm, h2.memory, h1.2.2.2.1]
    · rw [hu.memaddrs, hdm, h2.memaddrs, h1.2.2.2.2.1]
    · rw [hu.be, hbe, h2.be, h1.2.2.2.2.2.1]
    · rw [hu.base, hba, h2.base, h1.2.2.2.2.2.2.1]
    · rw [hu.code, hc, h2.code, h1.2.2.2.2.2.2.2]
    · rw [back "blk" (fx "blk" (by decide)) (by decide) (by decide)]; exact h1.1
    · rw [back "kept" (fx "kept" (by decide)) (by decide) (by decide)]; exact h1.2.1
    · rw [a3 "w" (fx "w" (by decide)) (by decide)]; exact h2.hw
    · rw [a3 "s1" (fx "s1" (by decide)) (by decide)]; exact sl1.1
    · rw [a3 "l1" (fx "l1" (by decide)) (by decide)]; exact sl1.2
    · rw [a3 "s2" (fx "s2" (by decide)) (by decide)]; exact sl2.1
    · rw [a3 "l2" (fx "l2" (by decide)) (by decide)]; exact sl2.2
    · rw [a3 "s3" (fx "s3" (by decide)) (by decide)]; exact sl3.1
    · rw [a3 "l3" (fx "l3" (by decide)) (by decide)]; exact sl3.2
    · rw [z "args" (fx "args" (by decide))]; exact hargs
    · rw [z "r" (fx "r" (by decide))]; exact hr
    · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp (hbd y hy)
      exact ⟨_, hu.val p (by simpa using hp)⟩

/-! ### Steps within -/

theorem offs_addr {offs : List Nat} (hoff : OffsOk offs) {b : Word} {dm : Word → Bool}
    (hcov : Analyzer.Covers SessionLayout.size dm b) {X : Nat} (hX : X ∈ offs) :
    dm (b + BitVec.ofNat 64 (ownOff + X)) = true := by
  obtain ⟨T, hT⟩ := SessionAppend.lay
  obtain ⟨h1, h2, -⟩ := hoff X hX
  have := hT.above
  have := SessionAppend.nums.own64
  exact SessionAppend.own_addr hcov h1 (by omega) (by rw [hT.eq]; omega)

/-- An own word set. -/
def fset (o : Nat) (e : Syntax.PExpr) : Syntax.PStmt := .store (SessionStore.at_ (ownOff + o)) e

theorem fset_lower {X : Nat} {e : Syntax.PExpr} {E : PancakeExp} (he : Lower.lowerExp e = some E) :
    Lower.lowerStmt1 (fset X e) = some (.store (.op .add .base (.const (BitVec.ofNat 64 (ownOff + X)))) E) := by
  have h0 : ownOff + X ≠ 0 := by have := SessionAppend.nums.own64; omega
  simp [fset, Lower.lowerStmt1, SessionAppend.at_lower h0, he]

/-- **An own word written** with `e`'s value. -/
theorem fset_frag (o : Oracle σ) {offs : List Nat} (hoff : OffsOk offs) {b : Word} {X : Nat} (hX : X ∈ offs)
    {x : Syntax.PExpr} {E : PancakeExp} (hx : Lower.lowerExp x = some E) {P : Assn σ}
    (hP : ∀ u, P u → u.baseAddr = b ∧ Analyzer.Covers SessionLayout.size u.memaddrs b ∧ ∃ v, eval u E = some v)
    {P' : Assn σ} (hcl : Safe.ClockFree P')
    (hP' : ∀ u m, P u → (∀ a, a ≠ b + BitVec.ofNat 64 (ownOff + X) → m a = u.memory a) →
      P' { u with memory := m }) : Frag o [fset X x] P P' :=
  frag_one (fset_lower hx) rfl rfl hcl (Safe.store fun u hu => by
    obtain ⟨hb, hcov, v, hv⟩ := hP u hu
    refine ⟨b + BitVec.ofNat 64 (ownOff + X), v,
      fun k => if k = b + BitVec.ofNat 64 (ownOff + X) then v else u.memory k,
      by simp only [eval, hb], hv, ?_, hP' u _ hu fun a ha => ?_⟩
    · simp only [memStoreWord, offs_addr hoff hcov hX, if_true]
    · simp only [if_neg ha])

/-- The locals the message-id and range checks read bound. -/
def chkBound : List String := ["ok", "val", "jq", "lo", "hi"]

/-- **The message-id check of a word**. -/
theorem fmid_frag (o : Oracle σ) {sn ln : String} (hsn : sn ∉ SessionCheck.midNames)
    (hln : ln ∉ SessionCheck.midNames) {B S : Word} {w : List Byte} {P : Assn σ}
    (hP : ∀ u, P u → (∀ y ∈ chkBound, ∃ v, u.locals y = some v) ∧ WordAt sn ln B S w u) :
    Frag o (Session.messageIdCheckAt (Syntax.v sn) (Syntax.v ln)) P
      (fun u => ∃ u0, P u0 ∧ SessionCheck.MidPost w u0 u ∧ Safe.Keeps u0 u) := by
  have hc := SessionCheck.messageIdCheck_lower (σ := Unit) (s := Syntax.v sn) (l := Syntax.v ln) rfl rfl []
    (bareState ())
  refine frag_pinned o (by simp [Session.messageIdCheckAt])
    (by simp [Session.messageIdCheckAt, Syntax.PStmt.isDec]) hc rfl
    (fun _ _ _ h => ⟨⟨{ h.1.1 with }, h.1.2⟩, h.2⟩) fun s hp => ?_
  obtain ⟨hv, hw⟩ := hP s hp
  obtain ⟨c', hc', hsafe⟩ := SessionCheck.messageIdCheck_safe o (s := Syntax.v sn) (l := Syntax.v ln) rfl rfl
    hsn hln B S w s
  rw [hc] at hc'; cases hc'
  exact Safe.safe_keeps (Safe.conseq hsafe
    (fun u (hu : u = s) => ⟨hu, hu ▸ ⟨hw.start, hw.len, hw.blk, hw.bytes, hw.short, hv "ok" (by decide),
      hv "jq" (by decide)⟩⟩) fun _ h => h)

/-- **The range check of a word**, the locals `ks` but its own two kept bound. -/
theorem frng_frag (o : Oracle σ) {sn ln : String} (hsn : sn ∉ SessionCheck.rngNames)
    (hln : ln ∉ SessionCheck.rngNames) {B S : Word} {w : List Byte} {ks : List String}
    (hks : "dn" ∉ ks ∧ "dp" ∉ ks) {P : Assn σ}
    (hP : ∀ u, P u → (∀ y ∈ chkBound, ∃ v, u.locals y = some v) ∧ WordAt sn ln B S w u) :
    Frag o (Session.rangeCheckAt (Syntax.v sn) (Syntax.v ln)) P
      (fun u => ∃ u0, P u0 ∧ SessionCheck.RngPost w u0 u ∧
        ∀ y ∈ ks, (u0.locals y).isSome → (u.locals y).isSome) := by
  let body := (Session.rangeCheckAt (Syntax.v sn) (Syntax.v ln)).drop 2
  have hsplit : Session.rangeCheckAt (Syntax.v sn) (Syntax.v ln) =
      [("dn", Syntax.n 0), ("dp", Syntax.n 0)].map (fun d => .dec d.1 d.2) ++ body := rfl
  have hB : Lower.lowerStmtsFold body = some _ := rfl
  have hfold : Lower.lowerStmtsFold (Session.rangeCheckAt (Syntax.v sn) (Syntax.v ln)) =
      some (.dec "dn" (.const (BitVec.ofNat 64 0)) (.dec "dp" (.const (BitVec.ofNat 64 0)) _)) := rfl
  rw [hsplit]
  refine frag_decs o [("dn", Syntax.n 0), ("dp", Syntax.n 0)] rfl (by simp [body, Session.rangeCheckAt])
    (by simp [body, Session.rangeCheckAt, Syntax.PStmt.isDec]) hB
    (fun u y w hy ⟨u0, h0, hr, hk⟩ => ⟨u0, h0, ?_, fun z hz hb => ?_⟩) fun R s hp => ?_
  · exact SessionCheck.rngPost_restore hr (by simpa using hy) w
  · have : z ≠ y := by
      rintro rfl; simp at hy; rcases hy with rfl | rfl
      · exact hks.1 hz
      · exact hks.2 hz
    simp only [restore, resVar, if_neg this]; exact hk z hz hb
  obtain ⟨hv, hw⟩ := hP s hp
  obtain ⟨c', hc', hsafe⟩ := SessionCheck.rangeCheck_safe o (s := Syntax.v sn) (l := Syntax.v ln) rfl rfl
    hsn hln B S w s
  rw [hfold] at hc'; cases hc'
  have hk := Safe.safe_keeps (Safe.conseq hsafe (fun u (hu : u = s) => ⟨hu, hu ▸ ⟨hw.start, hw.len, hw.blk, hw.bytes,
    hw.short, hv "ok" (by decide), hv "val" (by decide), hv "jq" (by decide), hv "lo" (by decide),
    hv "hi" (by decide)⟩⟩) fun _ h => h)
  exact WpRet.conseq (WpRet.ofSafe R rfl hk) (fun u (hu : u = s) => hu) (fun _ _ h => h)
    (fun u h => ⟨s, hp, h.1, fun y _ hy => h.2 y hy⟩) s rfl

/-- **A word's comparison with a text**, what else the state holds kept. -/
theorem fcmp_frag (o : Oracle σ) {nms bnd : List String} {offs : List Nat} {R : Nat} (hoff : OffsOk offs)
    (hnm : "eqk" ∈ nms ∧ "jq" ∈ nms) (hbd : "eqk" ∈ bnd ∧ "jq" ∈ bnd) {b : Word} {ci K : Nat} {L : List Byte}
    {e : PancakeState σ} (he : VEntry b ci K L e) {sn ln : String} (hsn : sn ≠ "eqk" ∧ sn ≠ "jq")
    (hln : ln ≠ "eqk" ∧ ln ≠ "jq") {S : Word} {w : List Byte}
    (hW : ∀ u, FAt nms bnd offs R b ci L e u → WordAt sn ln (SessionFrame.blockAt b ci) S w u)
    {t : Nat} (ht : t < texts.length)
    {Q : PancakeState σ → Prop} (hQ : ∀ u u', Q u → SessionCheck.ButFor ["eqk", "jq"] u u' → Q u') :
    Frag o (Session.wordIsAt sn ln t) (fun u => FAt nms bnd offs R b ci L e u ∧ Q u)
      (fun u => FAt nms bnd offs R b ci L e u ∧ Q u ∧
        u.locals "eqk" = some (bw (decide (w.map CommandSpec.upper = texts.getD t [])))) :=
  frag_conseq (wordIsAt_any o hsn hln ht (b := b) (P := fun u => FAt nms bnd offs R b ci L e u ∧ Q u)
    fun s h => ⟨hW s h.1, h.1.base.trans he.base, fat_texts hoff he h.1, h.1.bound "eqk" hbd.1,
      h.1.bound "jq" hbd.2⟩) (fun _ h => h) fun u ⟨s1, h1, hb, hj, hk⟩ =>
    ⟨fat_but h1.1 hb (fun y hy => by
        simp at hy; rcases hy with rfl | rfl
        · exact ⟨hnm.1, by decide⟩
        · exact ⟨hnm.2, by decide⟩) fun y hy hs => by
      by_cases e1 : y = "eqk"
      · subst e1; simp [hk]
      · by_cases e2 : y = "jq"
        · subst e2; obtain ⟨v, hv⟩ := hj; simp [hv]
        · rw [hb.locals y (by simp [e1, e2])]; exact hs, hQ s1 u h1.2 hb, hk⟩

/-- **`groupName` called on the second word**: `gn` zero, its verdict in the return word, what else the state holds
kept. -/
theorem fgn_frag (o : Oracle σ) {nms bnd : List String} {offs : List Nat} {R : Nat} (hoff : OffsOk offs)
    (hret : ownRet ∈ offs)
    (hgnm : "gn" ∈ nms ∧ "gn" ∉ fFixed ∧ "gn" ∉ bnd) (hcn : "c" ∉ nms) {b : Word} {ci K : Nat} {L : List Byte}
    {e : PancakeState σ} (he : VEntry b ci K L e) (hgn : GnCode e.code) (h2 : 2 ≤ (spans L).length)
    {Q : Assn σ} (hQc : Safe.ClockFree Q) (hQ : ∀ u u', Q u → (∀ y, y ≠ "gn" → u'.locals y = u.locals y) → Q u') :
    Frag o (SessionStore.callS "gn" "groupName" [Syntax.v "c", Syntax.v "s1", Syntax.v "l1"])
      (fun u => FAt nms bnd offs R b ci L e u ∧ Q u)
      (fun u => FAt nms bnd offs R b ci L e u ∧ Q u ∧ u.locals "gn" = some 0 ∧
        u.memory (SessionCheck.retW b) = bw (CommandSpec.isGroupName (cut L ((spans L).getD 1 (0, 0))))) := by
  obtain ⟨body, hcode, hlow⟩ := hgn
  let p := (spans L).getD 1 (0, 0)
  let gw := cut L p
  let P2 : Assn σ := fun u => FAt nms bnd offs R b ci L e u ∧ Q u ∧ u.locals "gn" = some 0 ∧
    u.memory (SessionCheck.retW b) = bw (CommandSpec.isGroupName gw)
  have hsh := he.short
  have hci := he.hci
  have fc : Frag o [.call "gn" "groupName" [Syntax.v "c", Syntax.v "s1", Syntax.v "l1"]]
      (fun u => FAt nms bnd offs R b ci L e u ∧ Q u) P2 := by
    refine frag_call o (args := [.var "c", .var "s1", .var "l1"]) rfl (body := body)
      (Pc := fun s s1 => s1 = { decClock s with locals := fun k => (["c", "s1", "l1"].zip
        [BitVec.ofNat 64 ci, BitVec.ofNat 64 p.1, BitVec.ofNat 64 gw.length]).lookup k } ∧
          SessionCheck.GnPre b ci p.1 gw s1)
      (Rc := fun s => SessionCheck.gnRet b gw s.memory) (fun s h => ?_) (fun s h => ?_)
      (fun s u v h hR hsame => ?_)
    · intro s1 ⟨ee, hpre⟩
      have := SessionCheck.groupName_run o b ci p.1 gw s1 hlow s1 ⟨rfl, hpre⟩
      have hm : s1.memory = s.memory := by rw [ee]; rfl
      rw [hm] at this; exact this
    · have hw := fword1 hoff he h.1 h2
      have hb := spans_bound L p (spans_getD_mem (by omega))
      have hgl : gw.length = p.2 := cut_length hb
      refine ⟨[BitVec.ofNat 64 ci, BitVec.ofNat 64 p.1, BitVec.ofNat 64 gw.length], _, ?_,
        Block.lookupCode_of (by rw [h.1.code]; exact hcode) (by decide) rfl, rfl, ?_⟩
      · simp only [evalArgs, eval, h.1.loc "c" hcn, he.c, h.1.s1, h.1.l1, hgl]; rfl
      · exact ⟨by simp only [decClock]; rw [h.1.base, he.base], rfl, by omega, rfl, by omega, rfl,
          by omega, fun j hj => by
            simp only [decClock]; rw [SessionCheck.gnBlock_eq]; exact hw.bytes j hj,
          by simp only [decClock]; rw [h.1.memaddrs]; exact SessionAppend.retW_addr he.hcov⟩
    · obtain ⟨hv, hret', hother⟩ := hR
      have hloc : ∀ y, y ≠ "gn" → ({ u with locals := setLocal s.locals "gn" v } : PancakeState σ).locals y =
          s.locals y := fun y hy => by simp only [setLocal, if_neg hy]
      have hfx : ∀ y ∈ fFixed, y ≠ "gn" := fun y hy e => hgnm.2.1 (e ▸ hy)
      refine ⟨fat_mk h.1 (fun y hy _ => hloc y (hfx y hy)) (fun y hy => by
          rw [hloc y fun e => hy (e ▸ hgnm.1)]; exact h.1.loc y hy) (fun a ha => ?_) (hsame.1.trans h.1.memaddrs)
        (hsame.2.2.1.trans h.1.be) (hsame.2.1.trans h.1.base) (hsame.2.2.2.trans h.1.code)
        (by rw [hloc _ (hfx "r" (by decide))]; exact h.1.r) (fun y hy => by
          rw [hloc y fun e => hgnm.2.2 (e ▸ hy)]; exact h.1.bound y hy),
        hQ s _ h.2 hloc, by simp [setLocal, hv], hret'⟩
      have : a ≠ SessionCheck.retW b := fun ee => ha (by
        rw [ee]; simp only [ownWords, List.mem_map]; exact ⟨ownRet, hret, rfl⟩)
      rw [hother a this]; exact h.1.memory a ha
  have cP2 : Safe.ClockFree P2 := fun u k h => ⟨fat_clock b ci L e u k h.1, hQc u k h.2.1, h.2.2⟩
  rw [SessionStore.callS]
  exact frag_append (xs := [_]) fc (zeroRet_frag o "gn" cP2 fun s h => h.2.2.1)

/-- What the function called last left in the return word, read. -/
theorem ffound_eval {nms bnd : List String} {offs : List Nat} {R : Nat} {b : Word} {ci K : Nat} {L : List Byte}
    {e u : PancakeState σ} (he : VEntry b ci K L e) (h : FAt nms bnd offs R b ci L e u) :
    eval u (.loadWord (.op .add .base (.const (BitVec.ofNat 64 (ownOff + ownRet))))) =
      some (u.memory (SessionCheck.retW b)) := by
  have := SessionAppend.retW_addr he.hcov
  rw [SessionCheck.retW] at this ⊢
  simp only [eval, h.base, he.base, h.memaddrs, this, if_true]

/-! ### The reply's code, set and given back -/

/-- Before the function's last words: every local but `nms` and every word but `ownWords offs` as at `e`, `r`
holding `R`, the locals `bnd` bound. -/
structure FEnd (nms bnd : List String) (offs : List Nat) (b : Word) (e : PancakeState σ) (R : Nat)
    (u : PancakeState σ) : Prop where
  loc : ∀ y, y ∉ nms → u.locals y = e.locals y
  memory : ∀ a, a ∉ ownWords offs b → u.memory a = e.memory a
  r : u.locals "r" = some (BitVec.ofNat 64 R)
  bound : ∀ y ∈ bnd, ∃ v, u.locals y = some v
  memaddrs : u.memaddrs = e.memaddrs
  base : u.baseAddr = e.baseAddr
  be : u.be = e.be
  code : u.code = e.code

section End
variable {nms bnd : List String} {offs : List Nat}

theorem fend_clock (b : Word) (e : PancakeState σ) (R : Nat) : Safe.ClockFree (FEnd nms bnd offs b e R) :=
  fun _ _ h => { h with }

theorem fend_restore {b : Word} {e u : PancakeState σ} {R : Nat} (h : FEnd nms bnd offs b e R u) {y : String}
    (hy : y ∈ nms ∧ y ≠ "r" ∧ y ∉ bnd) (v : Option Value) : FEnd nms bnd offs b e R (restore u y v) :=
  ⟨fun x hx => by
      have : x ≠ y := fun e => hx (e ▸ hy.1)
      simp only [restore, resVar, if_neg this]; exact h.loc x hx, h.memory,
    by simp only [restore, resVar, if_neg (Ne.symm hy.2.1)]; exact h.r,
    fun x hx => by
      have : x ≠ y := fun e => hy.2.2 (e ▸ hx)
      simp only [restore, resVar, if_neg this]; exact h.bound x hx, h.memaddrs, h.base, h.be, h.code⟩

theorem fend_of {bnd' : List String} {R : Nat} {b : Word} {ci : Nat} {L : List Byte} {e u : PancakeState σ}
    (h : FAt nms bnd offs R b ci L e u) (hb : ∀ y ∈ bnd', y ∈ bnd) : FEnd nms bnd' offs b e R u :=
  ⟨h.loc, h.memory, h.r, fun y hy => h.bound y (hb y hy), h.memaddrs, h.base, h.be, h.code⟩

/-- An own word written. -/
theorem fend_store {b : Word} {e u : PancakeState σ} {R : Nat} (h : FEnd nms bnd offs b e R u) {X : Nat}
    (hX : X ∈ offs) {m : Word → Word} (hm : ∀ a, a ≠ b + BitVec.ofNat 64 (ownOff + X) → m a = u.memory a) :
    FEnd nms bnd offs b e R { u with memory := m } :=
  { h with memory := ownWords_store hX hm h.memory }

/-- The reply `X` set. -/
theorem fsay_frag (o : Oracle σ) {bnd' : List String} {R0 : Nat} {b : Word} {ci : Nat} {L : List Byte}
    {e : PancakeState σ} (hr : "r" ∈ nms) (hb : ∀ y ∈ bnd', y ∈ bnd) (X : CommandSpec.Reply) {R : Nat} {P : Assn σ}
    (hP : ∀ u, P u → FAt nms bnd offs R0 b ci L e u ∧ Session.replyCode X = R) :
    Frag o [fsay X] P (FEnd nms bnd' offs b e R) :=
  frag_one (a := .assign "r" (.const (BitVec.ofNat 64 (Session.replyCode X)))) rfl rfl rfl (fend_clock b e R)
    (Safe.assign fun u hu => by
      obtain ⟨h, hX⟩ := hP u hu
      refine ⟨_, _, rfl, h.r, ⟨fun y hy => ?_, h.memory, by simp [setLocal, hX], fun y hy => ?_, h.memaddrs,
        h.base, h.be, h.code⟩⟩
      · have : y ≠ "r" := fun e => hy (e ▸ hr)
        simp only [setLocal, if_neg this]; exact h.loc y hy
      · by_cases e1 : y = "r"
        · subst e1; simp [setLocal]
        · simp only [setLocal, if_neg e1]; exact h.bound y (hb y hy))

/-- **The reply's code given back** in the return word. -/
theorem give_run (o : Oracle σ) (hoff : OffsOk offs) {b : Word} {e : PancakeState σ} {R : Nat}
    (hcov : Analyzer.Covers SessionLayout.size e.memaddrs b)
    (hb : e.baseAddr = b) :
    SafeR o (FEnd nms bnd offs b e R)
      (.seq (.store (.op .add .base (.const (BitVec.ofNat 64 (ownOff + ownRet)))) (.var "r"))
        (.ret (.const (BitVec.ofNat 64 0)))) (CallRet b R e.memory) (fun _ => False) := by
  let M : Assn σ := fun u => u.memory (SessionCheck.retW b) = BitVec.ofNat 64 R ∧
    ∀ a, a ∉ clsWords b → u.memory a = e.memory a
  refine WpRet.seq (M := M) (WpRet.store fun u h => ?_) (WpRet.ret fun u h => ⟨0, rfl, rfl, h.1, h.2⟩)
    (fun _ _ h => h)
  have ha : u.memaddrs (SessionCheck.retW b) = true := by rw [h.memaddrs]; exact SessionAppend.retW_addr hcov
  refine ⟨SessionCheck.retW b, BitVec.ofNat 64 R,
    fun k => if k = SessionCheck.retW b then BitVec.ofNat 64 R else u.memory k,
    by simp only [eval, h.base, hb, SessionCheck.retW], by simp only [eval]; exact h.r,
    by simp only [memStoreWord, ha, if_true], by simp, fun a ha' => ?_⟩
  have h1 : a ≠ SessionCheck.retW b := fun h => ha' (h ▸ retW_mem b)
  have h2 : a ∉ ownWords offs b := fun h => ha' (ownWords_cls hoff b a h)
  simp only [if_neg h1]; exact h.memory a h2

end End

/-- How the last words lower. -/
theorem give_lower : Lower.lowerStmtsFold (SessionStore.give (Syntax.v "r")) =
    some (.seq (.store (.op .add .base (.const (BitVec.ofNat 64 (ownOff + ownRet)))) (.var "r"))
      (.ret (.const (BitVec.ofNat 64 0)))) := by
  simp [SessionStore.give, Lower.lowerStmtsFold, Lower.lowerStmt1,
    SessionAppend.at_lower SessionAppend.ret_facts.2.2.2, Syntax.v, Syntax.n, Lower.lowerExp]

end DN.Server.SessionClassify
