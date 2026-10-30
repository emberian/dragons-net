-- SPDX-License-Identifier: AGPL-3.0-or-later
import DN.Compiler.Abi
import DN.Compiler.Safe

/-!
# DN.Compiler.Preservation

**What `Abi.wordResult` changes in a run, and nothing else.** A function the gate prints through
`Abi.emitWord` or `Abi.emitWordWith` lowers, and its rewrite lowers to the same program with each
return turned into a store of the value at the output slot and a return of zero
(`emitWord_rewrites`, `emitWordWith_rewrites`). A run of the rewrite, from a state that binds
`dn_result` to an address only it can reach, ends as the run of the function does, with a returned
value at that address and zero returned instead (`rewrites_run`, `rewrites_returns`); the rest of
the memory, the external world and the clock end the same.

Two facts carry it. A run that does not fail ends the same way when more of the memory is
addressable and the locals it does not read differ (`wider_run`): a run that reaches outside its
memory fails in the narrower state. And the store a return gains runs on the slot, which the
function's own run cannot reach (`slot_run`). As CakeML's theorem for its compiler does, they speak
of runs that do not fail: a run that fails is one the semantics gives no behaviour.
-/

namespace DN.Compiler.Preservation

open DN.Compiler DN.Compiler.Syntax DN.Compiler.Lower

variable {σ : Type}

/-! ## Names a program does not touch -/

/-- `e` reads no local `hide` names. -/
def ExpAvoids (hide : String → Prop) : PancakeExp → Prop
  | .var x => ¬ hide x
  | .op _ l r | .mul l r | .cmp _ l r | .shiftR l r | .shiftL l r =>
    ExpAvoids hide l ∧ ExpAvoids hide r
  | .loadByte a | .loadWord a => ExpAvoids hide a
  | .const _ | .base => True

/-- `p` reads, writes and declares no local `hide` names. -/
def ProgAvoids (hide : String → Prop) : PancakeProg → Prop
  | .skip => True
  | .dec v e c => ¬ hide v ∧ ExpAvoids hide e ∧ ProgAvoids hide c
  | .assign v e => ¬ hide v ∧ ExpAvoids hide e
  | .store d e | .storeByte d e => ExpAvoids hide d ∧ ExpAvoids hide e
  | .extCall _ c cl a al => ExpAvoids hide c ∧ ExpAvoids hide cl ∧ ExpAvoids hide a ∧
      ExpAvoids hide al
  | .seq a b => ProgAvoids hide a ∧ ProgAvoids hide b
  | .cond e a b => ExpAvoids hide e ∧ ProgAvoids hide a ∧ ProgAvoids hide b
  | .while_ e c => ExpAvoids hide e ∧ ProgAvoids hide c
  | .ret e => ExpAvoids hide e
  | .decCall rt _ args c => ¬ hide rt ∧ (∀ a ∈ args, ExpAvoids hide a) ∧ ProgAvoids hide c

theorem expAvoids_none : ∀ e : PancakeExp, ExpAvoids (fun _ => False) e
  | .var _ => fun h => h
  | .op _ l r | .mul l r | .cmp _ l r | .shiftR l r | .shiftL l r =>
    ⟨expAvoids_none l, expAvoids_none r⟩
  | .loadByte a | .loadWord a => expAvoids_none a
  | .const _ | .base => trivial

/-- Every program avoids no names. -/
theorem progAvoids_none : ∀ p : PancakeProg, ProgAvoids (fun _ => False) p
  | .skip => trivial
  | .dec _ e c => ⟨id, expAvoids_none e, progAvoids_none c⟩
  | .assign _ e => ⟨id, expAvoids_none e⟩
  | .store d e | .storeByte d e => ⟨expAvoids_none d, expAvoids_none e⟩
  | .extCall _ c cl a al =>
    ⟨expAvoids_none c, expAvoids_none cl, expAvoids_none a, expAvoids_none al⟩
  | .seq a b => ⟨progAvoids_none a, progAvoids_none b⟩
  | .cond e a b => ⟨expAvoids_none e, progAvoids_none a, progAvoids_none b⟩
  | .while_ e c => ⟨expAvoids_none e, progAvoids_none c⟩
  | .ret e => expAvoids_none e
  | .decCall _ _ _ c => ⟨id, fun a _ => expAvoids_none a, progAvoids_none c⟩

/-! ## Two states one run cannot tell apart -/

/-- `t` is `s` with more of the memory addressable: the locals the same but those `hide` names,
the addresses of `s` addressable in `t` and holding the same words there, and the rest the same. -/
structure Agree (hide : String → Prop) (s t : PancakeState σ) : Prop where
  locals : ∀ x, ¬ hide x → t.locals x = s.locals x
  dom : ∀ a, s.memaddrs a = true → t.memaddrs a = true
  mem : ∀ a, s.memaddrs a = true → t.memory a = s.memory a
  be : t.be = s.be
  clock : t.clock = s.clock
  ffi : t.ffi = s.ffi
  base : t.baseAddr = s.baseAddr
  code : t.code = s.code

/-- States that agree on every local agree on all but any names. -/
theorem Agree.weaken {hide : String → Prop} {s t : PancakeState σ}
    (h : Agree (fun _ => False) s t) : Agree hide s t :=
  ⟨fun x _ => h.locals x id, h.dom, h.mem, h.be, h.clock, h.ffi, h.base, h.code⟩

theorem Agree.withLocals {hide : String → Prop} {s t : PancakeState σ} (h : Agree hide s t)
    {l1 l2 : String → Option Value} (hl : ∀ x, ¬ hide x → l2 x = l1 x) :
    Agree hide { s with locals := l1 } { t with locals := l2 } :=
  ⟨hl, h.dom, h.mem, h.be, h.clock, h.ffi, h.base, h.code⟩

theorem Agree.withClock {hide : String → Prop} {s t : PancakeState σ} (h : Agree hide s t)
    (k : Nat) : Agree hide { s with clock := k } { t with clock := k } :=
  ⟨h.locals, h.dom, h.mem, h.be, rfl, h.ffi, h.base, h.code⟩

theorem Agree.empty {hide : String → Prop} {s t : PancakeState σ} (h : Agree hide s t) :
    Agree hide (emptyLocals s) (emptyLocals t) :=
  ⟨fun _ _ => rfl, h.dom, h.mem, h.be, h.clock, h.ffi, h.base, h.code⟩

theorem Agree.decClock {hide : String → Prop} {s t : PancakeState σ} (h : Agree hide s t) :
    Agree hide (decClock s) (decClock t) :=
  ⟨h.locals, h.dom, h.mem, h.be, by simp [DN.Compiler.decClock, h.clock], h.ffi, h.base, h.code⟩

theorem Agree.withMemFfi {hide : String → Prop} {s t : PancakeState σ} (h : Agree hide s t)
    {m1 m2 : Word → Word} (hm : ∀ k, s.memaddrs k = true → m2 k = m1 k) (f : σ) :
    Agree hide { s with memory := m1, ffi := f } { t with memory := m2, ffi := f } :=
  ⟨h.locals, h.dom, hm, h.be, h.clock, rfl, h.base, h.code⟩

/-- Setting the same local in both keeps them agreeing. -/
theorem setLocal_agree {hide : String → Prop} {l1 l2 : String → Option Value}
    (hl : ∀ x, ¬ hide x → l2 x = l1 x) (v : String) (val : Value) :
    ∀ x, ¬ hide x → setLocal l2 v val x = setLocal l1 v val x := by
  intro x hx
  simp only [setLocal]
  split
  · rfl
  · exact hl x hx

/-- Restoring a local `hide` does not name keeps them agreeing. -/
theorem resVar_agree {hide : String → Prop} {l1 l2 : String → Option Value}
    (hl : ∀ x, ¬ hide x → l2 x = l1 x) (v : String) {o1 o2 : Option Value} (ho : o2 = o1) :
    ∀ x, ¬ hide x → resVar l2 v o2 x = resVar l1 v o1 x := by
  intro x hx
  simp only [resVar]
  split
  · exact ho
  · exact hl x hx

/-! ## The memory, read and written where the narrower state can -/

section Memory

variable {m1 m2 : Word → Word} {d1 d2 : Word → Bool} {be : Bool}

theorem loadByte_agree (hd : ∀ a, d1 a = true → d2 a = true)
    (hm : ∀ a, d1 a = true → m2 a = m1 a) {w : Word} {b : BitVec 8}
    (h : memLoadByte m1 d1 be w = some b) : memLoadByte m2 d2 be w = some b := by
  unfold memLoadByte at h ⊢
  split at h
  · rename_i hw
    rw [if_pos (hd _ hw), hm _ hw]
    exact h
  · cases h

theorem read_agree (hd : ∀ a, d1 a = true → d2 a = true) (hm : ∀ a, d1 a = true → m2 a = m1 a) :
    ∀ (n : Nat) (a : Word) (bs : List (BitVec 8)),
      readByteArray m1 d1 be a n = some bs → readByteArray m2 d2 be a n = some bs
  | 0, _, _, h => h
  | n + 1, a, bs, h => by
    unfold readByteArray at h ⊢
    cases hb : memLoadByte m1 d1 be a with
    | none => rw [hb] at h; cases h
    | some b =>
      rw [hb] at h
      rw [loadByte_agree hd hm hb]
      cases hr : readByteArray m1 d1 be (a + 1) n with
      | none => rw [hr] at h; cases h
      | some rest =>
        rw [hr] at h
        rw [read_agree hd hm n (a + 1) rest hr]
        exact h

theorem read_length : ∀ (n : Nat) (a : Word) (bs : List (BitVec 8)),
    readByteArray m1 d1 be a n = some bs → bs.length = n
  | 0, _, _, h => by cases h; rfl
  | n + 1, a, bs, h => by
    unfold readByteArray at h
    split at h
    · cases h
    · split at h
      · cases h
      · cases h
        simp only [List.length_cons, Nat.add_right_cancel_iff]
        exact read_length n (a + 1) _ ‹_›

/-- Writing back bytes where a read of as many succeeded writes the same words in both. -/
theorem write_agree (hd : ∀ a, d1 a = true → d2 a = true) :
    ∀ (bytes : List (BitVec 8)) (a : Word) (n : Nat) (arr : List (BitVec 8)) (w1 w2 : Word → Word),
      readByteArray m1 d1 be a n = some arr → bytes.length = n →
      (∀ k, d1 k = true → w2 k = w1 k) →
      ∀ k, d1 k = true → writeByteArray d2 be a bytes w2 k = writeByteArray d1 be a bytes w1 k
  | [], _, _, _, _, _, _, _, hw => hw
  | b :: bs, a, n, arr, w1, w2, hr, hl, hw => by
    cases n with
    | zero => cases hl
    | succ n =>
      unfold readByteArray at hr
      cases hb : memLoadByte m1 d1 be a with
      | none => rw [hb] at hr; cases hr
      | some x =>
        rw [hb] at hr
        cases hrest : readByteArray m1 d1 be (a + 1) n with
        | none => rw [hrest] at hr; cases hr
        | some rest =>
          have hin : d1 (byteAlign a) = true := by
            unfold memLoadByte at hb
            split at hb
            · assumption
            · cases hb
          have ih := write_agree hd bs (a + 1) n rest w1 w2 hrest (by simpa using hl) hw
          intro k hk
          simp only [writeByteArray, memStoreByte, if_pos hin, if_pos (hd _ hin)]
          split
          · rw [ih _ hin]
          · exact ih k hk

end Memory

/-! ## Expressions -/

/-- An expression that avoids the names the states may differ on, and has a value in the
narrower one, has that value in the wider one. -/
theorem eval_agree {hide : String → Prop} {s t : PancakeState σ} (h : Agree hide s t) :
    ∀ e : PancakeExp, ExpAvoids hide e → eval s e ≠ none → eval t e = eval s e := by
  intro e
  induction e with
  | const w => intro _ _; rfl
  | var x => intro hx _; exact h.locals x hx
  | base => intro _ _; simp only [eval, h.base]
  | op bop l r ihl ihr =>
    intro ⟨hl, hr⟩ hne
    have hsl : eval s l ≠ none := fun hn => hne (by simp only [eval, hn])
    have hsr : eval s r ≠ none := fun hn => hne (by
      simp only [eval, hn]; cases eval s l <;> rfl)
    simp only [eval]
    rw [ihl hl hsl, ihr hr hsr]
  | mul l r ihl ihr =>
    intro ⟨hl, hr⟩ hne
    have hsl : eval s l ≠ none := fun hn => hne (by simp only [eval, hn])
    have hsr : eval s r ≠ none := fun hn => hne (by
      simp only [eval, hn]; cases eval s l <;> rfl)
    simp only [eval]
    rw [ihl hl hsl, ihr hr hsr]
  | cmp c l r ihl ihr =>
    intro ⟨hl, hr⟩ hne
    cases c <;>
    · have hsl : eval s l ≠ none := fun hn => hne (by simp only [eval, hn])
      have hsr : eval s r ≠ none := fun hn => hne (by
        simp only [eval, hn]; cases eval s l <;> rfl)
      simp only [eval]
      rw [ihl hl hsl, ihr hr hsr]
  | shiftR l r ihl ihr =>
    intro ⟨hl, hr⟩ hne
    have hsl : eval s l ≠ none := fun hn => hne (by simp only [eval, hn])
    have hsr : eval s r ≠ none := fun hn => hne (by
      simp only [eval, hn]; cases eval s l <;> rfl)
    simp only [eval]
    rw [ihl hl hsl, ihr hr hsr]
  | shiftL l r ihl ihr =>
    intro ⟨hl, hr⟩ hne
    have hsl : eval s l ≠ none := fun hn => hne (by simp only [eval, hn])
    have hsr : eval s r ≠ none := fun hn => hne (by
      simp only [eval, hn]; cases eval s l <;> rfl)
    simp only [eval]
    rw [ihl hl hsl, ihr hr hsr]
  | loadByte a ih =>
    intro ha hne
    have hsa : eval s a ≠ none := fun hn => hne (by simp only [eval, hn])
    obtain ⟨w, hw⟩ := Option.ne_none_iff_exists'.mp hsa
    simp only [eval, ih ha hsa, hw] at hne ⊢
    cases hb : memLoadByte s.memory s.memaddrs s.be w with
    | none => rw [hb] at hne; exact absurd rfl hne
    | some b => rw [h.be, loadByte_agree h.dom h.mem hb]
  | loadWord a ih =>
    intro ha hne
    have hsa : eval s a ≠ none := fun hn => hne (by simp only [eval, hn])
    obtain ⟨w, hw⟩ := Option.ne_none_iff_exists'.mp hsa
    simp only [eval, ih ha hsa, hw] at hne ⊢
    by_cases hd : s.memaddrs w = true
    · rw [if_pos hd, if_pos (h.dom w hd), h.mem w hd]
    · rw [if_neg hd] at hne
      exact absurd rfl hne

theorem eval_agree' {hide : String → Prop} {s t : PancakeState σ} (h : Agree hide s t)
    {e : PancakeExp} (he : ExpAvoids hide e) {v : Value} (hv : eval s e = some v) :
    eval t e = some v := by
  rw [eval_agree h e he (by simp [hv]), hv]

theorem evalArgs_agree {hide : String → Prop} {s t : PancakeState σ} (h : Agree hide s t) :
    ∀ args : List PancakeExp, (∀ a ∈ args, ExpAvoids hide a) → ∀ vs,
      evalArgs s args = some vs → evalArgs t args = some vs
  | [], _, _, hv => hv
  | e :: es, ha, vs, hv => by
    simp only [evalArgs] at hv ⊢
    cases he : eval s e with
    | none => rw [he] at hv; cases hv
    | some v =>
      cases hes : evalArgs s es with
      | none => rw [he, hes] at hv; cases hv
      | some ws =>
        rw [he, hes] at hv
        rw [eval_agree' h (ha e (List.mem_cons_self ..)) he,
          evalArgs_agree h es (fun a hm => ha a (List.mem_cons_of_mem _ hm)) ws hes]
        exact hv

/-! ## Runs -/

/-- A store where the narrower state can store stores the same word in the wider one. -/
theorem storeWord_agree {hide : String → Prop} {s t : PancakeState σ} (h : Agree hide s t)
    {addr val : Word} {m : Word → Word} (hm : memStoreWord s.memory s.memaddrs addr val = some m) :
    ∃ m', memStoreWord t.memory t.memaddrs addr val = some m' ∧
      Agree hide { s with memory := m } { t with memory := m' } := by
  unfold memStoreWord at hm
  split at hm
  · rename_i hd
    cases hm
    refine ⟨fun k => if k = addr then val else t.memory k,
      by simp only [memStoreWord, if_pos (h.dom _ hd)], ?_⟩
    refine ⟨h.locals, h.dom, fun k hk => ?_, h.be, h.clock, h.ffi, h.base, h.code⟩
    simp only
    split
    · rfl
    · exact h.mem k hk
  · cases hm

theorem storeByte_agree {hide : String → Prop} {s t : PancakeState σ} (h : Agree hide s t)
    {addr : Word} {b : BitVec 8} {m : Word → Word}
    (hm : memStoreByte s.memory s.memaddrs s.be addr b = some m) :
    ∃ m', memStoreByte t.memory t.memaddrs t.be addr b = some m' ∧
      Agree hide { s with memory := m } { t with memory := m' } := by
  unfold memStoreByte at hm
  split at hm
  · rename_i hd
    cases hm
    refine ⟨fun k => if k = byteAlign addr then setByte addr b (t.memory (byteAlign addr)) t.be
        else t.memory k, by simp only [memStoreByte, if_pos (h.dom _ hd)], ?_⟩
    refine ⟨h.locals, h.dom, fun k hk => ?_, h.be, h.clock, h.ffi, h.base, h.code⟩
    simp only
    split
    · rw [h.mem _ hd, h.be]
    · exact h.mem k hk
  · cases hm

/-- What a run's ending says once the clock is clamped: the clamp changes only the clock. -/
theorem clamp_agree {hide : String → Prop} {r1 r2 : Option Result × PancakeState σ} (k : Nat)
    (hr : r2.1 = r1.1) (ha : Agree hide r1.2 r2.2) :
    (clampClock k r2).1 = (clampClock k r1).1 ∧ Agree hide (clampClock k r1).2 (clampClock k r2).2 := by
  obtain ⟨x1, s1⟩ := r1
  obtain ⟨x2, s2⟩ := r2
  simp only [clampClock] at hr ha ⊢
  refine ⟨hr, ?_⟩
  rw [ha.clock]
  exact ha.withClock _

theorem clamp_snd_agree {hide : String → Prop} {r1 r2 : Option Result × PancakeState σ} (k : Nat)
    (ha : Agree hide r1.2 r2.2) : Agree hide (clampClock k r1).2 (clampClock k r2).2 := by
  obtain ⟨x1, s1⟩ := r1
  obtain ⟨x2, s2⟩ := r2
  simp only [clampClock] at ha ⊢
  rw [ha.clock]
  exact ha.withClock _

/-- **A run that does not fail ends the same way where more of the memory is addressable.** From
states that agree but on locals the program does not touch, a run that does not end in `Error`
in the narrower one ends the same way in the wider one, in states that agree again. -/
theorem wider_run (o : Oracle σ) :
    ∀ (n : Nat) (hide : String → Prop) (p : PancakeProg) (s t : PancakeState σ), s.clock ≤ n →
      ProgAvoids hide p → Agree hide s t → (PancakeSem o p s).1 ≠ some .error →
      (PancakeSem o p t).1 = (PancakeSem o p s).1 ∧
        Agree hide (PancakeSem o p s).2 (PancakeSem o p t).2 := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ihn =>
  intro hide p
  induction p generalizing hide with
  | skip =>
    intro s t _ _ h _
    rw [PancakeSem.eq_1, PancakeSem.eq_1]
    exact ⟨by trivial, h⟩
  | dec v e c ih =>
    intro s t hc hav h hne
    obtain ⟨hv, he, hcav⟩ := hav
    rw [PancakeSem.eq_2] at hne ⊢
    rw [PancakeSem.eq_2]
    cases hes : eval s e with
    | none => simp [hes] at hne
    | some val =>
      simp only [hes, eval_agree' h he hes] at hne ⊢
      have h' := h.withLocals (setLocal_agree h.locals v val)
      obtain ⟨hr, ha⟩ := ih hide { s with locals := setLocal s.locals v val }
        { t with locals := setLocal t.locals v val } hc hcav h' hne
      exact ⟨hr, ha.withLocals (resVar_agree ha.locals v (h.locals v hv))⟩
  | assign v e =>
    intro s t _ hav h hne
    obtain ⟨hv, he⟩ := hav
    rw [PancakeSem.eq_3] at hne ⊢
    rw [PancakeSem.eq_3]
    cases hes : eval s e with
    | none => simp [hes] at hne
    | some val =>
      cases hl : s.locals v with
      | none => simp [hes, hl] at hne
      | some old =>
        simp only [hl, eval_agree' h he hes, h.locals v hv]
        exact ⟨by trivial, h.withLocals (setLocal_agree h.locals v val)⟩
  | store d e =>
    intro s t _ hav h hne
    obtain ⟨hd, he⟩ := hav
    rw [PancakeSem.eq_4] at hne ⊢
    rw [PancakeSem.eq_4]
    cases hds : eval s d with
    | none => simp [hds] at hne
    | some addr =>
      cases hes : eval s e with
      | none => simp [hds, hes] at hne
      | some val =>
        simp only [hds, hes, eval_agree' h hd hds, eval_agree' h he hes] at hne ⊢
        cases hm : memStoreWord s.memory s.memaddrs addr val with
        | none => simp [hm] at hne
        | some m =>
          obtain ⟨m', hm', ha⟩ := storeWord_agree h hm
          simp only [hm']
          exact ⟨by trivial, ha⟩
  | storeByte d e =>
    intro s t _ hav h hne
    obtain ⟨hd, he⟩ := hav
    rw [PancakeSem.eq_10] at hne ⊢
    rw [PancakeSem.eq_10]
    cases hds : eval s d with
    | none => simp [hds] at hne
    | some addr =>
      cases hes : eval s e with
      | none => simp [hds, hes] at hne
      | some val =>
        simp only [hds, hes, eval_agree' h hd hds, eval_agree' h he hes] at hne ⊢
        cases hm : memStoreByte s.memory s.memaddrs s.be addr (val.setWidth 8) with
        | none => simp [hm] at hne
        | some m =>
          obtain ⟨m', hm', ha⟩ := storeByte_agree h hm
          simp only [hm']
          exact ⟨by trivial, ha⟩
  | extCall name c cl a al =>
    intro s t _ hav h hne
    obtain ⟨hc, hcl, ha, hal⟩ := hav
    rw [PancakeSem.eq_5] at hne ⊢
    rw [PancakeSem.eq_5]
    cases h1 : eval s c with
    | none => simp [h1] at hne
    | some cp =>
      cases h2 : eval s cl with
      | none => simp [h1, h2] at hne
      | some clv =>
        cases h3 : eval s a with
        | none => simp [h1, h2, h3] at hne
        | some ap =>
          cases h4 : eval s al with
          | none => simp [h1, h2, h3, h4] at hne
          | some alv =>
            simp only [h1, h2, h3, h4, eval_agree' h hc h1, eval_agree' h hcl h2,
              eval_agree' h ha h3, eval_agree' h hal h4] at hne ⊢
            cases hconf : readByteArray s.memory s.memaddrs s.be cp clv.toNat with
            | none => simp [hconf] at hne
            | some conf =>
              cases harr : readByteArray s.memory s.memaddrs s.be ap alv.toNat with
              | none => simp [hconf, harr] at hne
              | some arr =>
                simp only [h.be, read_agree h.dom h.mem _ _ _ hconf,
                  read_agree h.dom h.mem _ _ _ harr, h.ffi]
                cases hf : callFFI o s.ffi name conf arr with
                | final ev => exact ⟨by trivial, h.empty⟩
                | ret ffi' bytes =>
                  have hlen : bytes.length = alv.toNat := by
                    rw [Safe.callFFI_ret_length hf]; exact read_length _ _ _ harr
                  have ha := h.withMemFfi
                    (write_agree h.dom bytes ap _ arr s.memory t.memory harr hlen h.mem) ffi'
                  rw [h.be] at ha
                  exact ⟨by trivial, ha⟩
  | seq c1 c2 ih1 ih2 =>
    intro s t hc hav h hne
    obtain ⟨hav1, hav2⟩ := hav
    rw [PancakeSem.eq_6] at hne ⊢
    rw [PancakeSem.eq_6]
    have hne1 : (PancakeSem o c1 s).1 ≠ some .error := by
      intro he
      apply hne
      simp only [clampClock, he]
    obtain ⟨hr1, ha1⟩ := ih1 hide s t hc hav1 h hne1
    obtain ⟨hr, ha⟩ := clamp_agree s.clock hr1 ha1
    have hcl : (clampClock s.clock (PancakeSem o c1 s)).2.clock ≤ n := by
      simp only [clampClock]; omega
    rw [h.clock]
    revert hr ha hne hcl
    generalize clampClock s.clock (PancakeSem o c1 s) = R1
    generalize clampClock s.clock (PancakeSem o c1 t) = R2
    obtain ⟨x1, s1⟩ := R1
    obtain ⟨x2, s2⟩ := R2
    intro hne hr ha hcl
    simp only at hr ha hne hcl ⊢
    subst hr
    cases x2 with
    | none => exact ih2 hide s1 s2 hcl hav2 ha hne
    | some res => exact ⟨by trivial, ha⟩
  | cond e c1 c2 ih1 ih2 =>
    intro s t hc hav h hne
    obtain ⟨he, hav1, hav2⟩ := hav
    rw [PancakeSem.eq_7] at hne ⊢
    rw [PancakeSem.eq_7]
    cases hes : eval s e with
    | none => simp [hes] at hne
    | some w =>
      simp only [hes, eval_agree' h he hes] at hne ⊢
      by_cases hz : w = 0
      · simp only [hz, ne_eq, not_true_eq_false, if_false] at hne ⊢
        exact ih2 hide s t hc hav2 h hne
      · simp only [hz, ne_eq, not_false_eq_true, if_true] at hne ⊢
        exact ih1 hide s t hc hav1 h hne
  | while_ e c _ =>
    intro s t hc hav h hne
    obtain ⟨he, hcav⟩ := hav
    rw [PancakeSem.eq_8] at hne ⊢
    rw [PancakeSem.eq_8]
    cases hes : eval s e with
    | none => simp [hes] at hne
    | some w =>
      simp only [hes, eval_agree' h he hes, h.clock] at hne ⊢
      by_cases hz : w = 0
      · simp only [hz, ne_eq, not_true_eq_false, if_false]
        exact ⟨by trivial, h⟩
      · simp only [hz, ne_eq, not_false_eq_true, if_true] at hne ⊢
        by_cases h0 : s.clock = 0
        · simp only [h0, if_true]
          exact ⟨by trivial, h.empty⟩
        · simp only [h0, if_false] at hne ⊢
          have hne1 : (PancakeSem o c (decClock s)).1 ≠ some .error := by
            intro hx
            apply hne
            simp only [clampClock, hx]
          obtain ⟨hr1, ha1⟩ := ihn (s.clock - 1) (by omega) hide c (decClock s) (decClock t)
            (by simp [decClock]) hcav h.decClock hne1
          obtain ⟨hr, ha⟩ := clamp_agree (s.clock - 1) hr1 ha1
          have hcl : (clampClock (s.clock - 1) (PancakeSem o c (decClock s))).2.clock < n := by
            simp only [clampClock]; omega
          revert hr ha hne hcl
          generalize clampClock (s.clock - 1) (PancakeSem o c (decClock s)) = R1
          generalize clampClock (s.clock - 1) (PancakeSem o c (decClock t)) = R2
          obtain ⟨x1, s1⟩ := R1
          obtain ⟨x2, s2⟩ := R2
          intro hne hr ha hcl
          simp only at hr ha hne hcl ⊢
          subst hr
          have hloop := ihn s1.clock hcl hide (.while_ e c) s1 s2 (Nat.le_refl _) ⟨he, hcav⟩ ha
          cases x2 with
          | none => exact hloop hne
          | some res =>
            cases res with
            | continue_ => exact hloop hne
            | break_ => exact ⟨by trivial, ha⟩
            | error => exact ⟨by trivial, ha⟩
            | timeout => exact ⟨by trivial, ha⟩
            | return_ v => exact ⟨by trivial, ha⟩
            | finalFFI ev => exact ⟨by trivial, ha⟩
  | ret e =>
    intro s t _ hav h hne
    rw [PancakeSem.eq_9] at hne ⊢
    rw [PancakeSem.eq_9]
    cases hes : eval s e with
    | none => simp [hes] at hne
    | some v =>
      simp only [eval_agree' h hav hes]
      exact ⟨by trivial, h.empty⟩
  | decCall rt f args cont _ =>
    intro s t hc hav h hne
    obtain ⟨hrt, hargs, hcav⟩ := hav
    rw [PancakeSem.eq_11] at hne ⊢
    rw [PancakeSem.eq_11]
    cases hvs : evalArgs s args with
    | none => simp [hvs] at hne
    | some vs =>
      simp only [hvs, evalArgs_agree h args hargs vs hvs, h.code] at hne ⊢
      cases hl : lookupCode s.code f vs with
      | none => simp [hl] at hne
      | some bp =>
        obtain ⟨body, params⟩ := bp
        simp only [hl, h.clock] at hne ⊢
        by_cases h0 : s.clock = 0
        · simp only [h0, if_true]
          exact ⟨by trivial, h.empty⟩
        · simp only [h0, if_false] at hne ⊢
          have hb : Agree (fun _ => False) { decClock s with locals := params }
              { decClock t with locals := params } :=
            ⟨fun _ _ => rfl, h.dom, h.mem, h.be, by simp [decClock, h.clock], h.ffi, h.base, h.code⟩
          have hne1 : (PancakeSem o body { decClock s with locals := params }).1 ≠ some .error := by
            intro hx
            apply hne
            simp only [clampClock, hx, callEnded]
          obtain ⟨hr1, ha1⟩ := ihn (s.clock - 1) (by omega) (fun _ => False) body _ _
            (by simp [decClock]) (progAvoids_none body) hb hne1
          obtain ⟨hr, ha⟩ := clamp_agree (s.clock - 1) hr1 ha1
          have hcl : (clampClock (s.clock - 1)
              (PancakeSem o body { decClock s with locals := params })).2.clock < n := by
            simp only [clampClock]; omega
          revert hr ha hne hcl
          generalize clampClock (s.clock - 1) (PancakeSem o body { decClock s with locals := params })
            = R1
          generalize clampClock (s.clock - 1) (PancakeSem o body { decClock t with locals := params })
            = R2
          obtain ⟨x1, s1⟩ := R1
          obtain ⟨x2, s2⟩ := R2
          intro hne hr ha hcl
          simp only at hr ha hne hcl ⊢
          subst hr
          cases x2 with
          | none => simp [callEnded] at hne
          | some res =>
            cases res with
            | return_ v =>
              simp only at hne ⊢
              have hc' := (ha.weaken (hide := hide)).withLocals (setLocal_agree h.locals rt v)
              obtain ⟨hr2, ha2⟩ := ihn s1.clock hcl hide cont { s1 with locals := setLocal s.locals rt v }
                { s2 with locals := setLocal t.locals rt v } (Nat.le_refl _) hcav hc' hne
              exact ⟨hr2, ha2.withLocals (resVar_agree ha2.locals rt (h.locals rt hrt))⟩
            | error => simp [callEnded] at hne
            | break_ => simp [callEnded] at hne
            | continue_ => simp [callEnded] at hne
            | timeout => simp only [callEnded]; exact ⟨by trivial, ha.weaken.empty⟩
            | finalFFI ev => simp only [callEnded]; exact ⟨by trivial, ha.weaken.empty⟩

/-! ## The output slot -/

/-- The parameter `Abi.wordResult` adds: the address of the output slot. -/
def slotName : String := "dn_result"

/-- `Abi.wordResult` as the lowering sees it: each return stores its value at the slot and returns
zero. -/
def retToSlot : PancakeProg → PancakeProg
  | .ret e => .seq (.store (.var slotName) e) (.ret (.const (BitVec.ofNat 64 0)))
  | .dec v e c => .dec v e (retToSlot c)
  | .seq a b => .seq (retToSlot a) (retToSlot b)
  | .cond e a b => .cond e (retToSlot a) (retToSlot b)
  | .while_ e c => .while_ e (retToSlot c)
  | .decCall r f args c => .decCall r f args (retToSlot c)
  | p => p

/-- What the rewritten run returns: zero for a value, every other ending as it was. -/
def slotResult : Option Result → Option Result
  | some (.return_ _) => some (.return_ 0)
  | r => r

/-- What the rewritten run's state holds after an ending: while it goes on, the slot's address in
its local; after a return, the value at the slot. -/
def SlotAfter (a : Word) : Option Result → PancakeState σ → Prop
  | none, t | some .break_, t | some .continue_, t => t.locals slotName = some a
  | some (.return_ v), t => t.memory a = v
  | _, _ => True

theorem SlotAfter.withLocals {a : Word} {r : Option Result} {t : PancakeState σ}
    (h : SlotAfter a r t) {l : String → Option Value} (hl : l slotName = t.locals slotName) :
    SlotAfter a r { t with locals := l } := by
  rcases r with _ | ⟨_ | _ | _ | _ | _ | _⟩ <;> simp only [SlotAfter] at h ⊢ <;>
    first | trivial | (rw [hl]; exact h) | exact h

theorem SlotAfter.withClock {a : Word} {r : Option Result} {t : PancakeState σ}
    (h : SlotAfter a r t) (k : Nat) : SlotAfter a r { t with clock := k } := by
  rcases r with _ | ⟨_ | _ | _ | _ | _ | _⟩ <;> simp only [SlotAfter] at h ⊢ <;>
    first | trivial | exact h

theorem setLocal_slot {l : String → Option Value} {v : String} (hv : ¬ v = slotName) (val : Value) :
    setLocal l v val slotName = l slotName := by
  simp only [setLocal]
  split
  · rename_i h; exact absurd h.symm hv
  · rfl

theorem resVar_slot {l : String → Option Value} {v : String} (hv : ¬ v = slotName)
    (old : Option Value) : resVar l v old slotName = l slotName := by
  simp only [resVar]
  split
  · rename_i h; exact absurd h.symm hv
  · rfl

/-- The address a run's state can reach does not change in the run. -/
theorem memaddrs_run (o : Oracle σ) (p : PancakeProg) (s : PancakeState σ) :
    (PancakeSem o p s).2.memaddrs = s.memaddrs :=
  (Safe.sem_same o s.clock p s (Nat.le_refl _)).1

/-- **The rewritten run ends as the function's does.** From states that agree but on the slot's
name, the wider one binding it to an address only it can reach, a run of a program that avoids the
name and does not end in `Error` ends the same way rewritten, returning zero where it returned a
value and holding that value at the slot. -/
theorem slot_run (o : Oracle σ) (a : Word) :
    ∀ (n : Nat) (p : PancakeProg) (s t : PancakeState σ), s.clock ≤ n →
      ProgAvoids (· = slotName) p → Agree (· = slotName) s t → s.memaddrs a = false →
      t.memaddrs a = true → t.locals slotName = some a → (PancakeSem o p s).1 ≠ some .error →
      (PancakeSem o (retToSlot p) t).1 = slotResult (PancakeSem o p s).1 ∧
        Agree (· = slotName) (PancakeSem o p s).2 (PancakeSem o (retToSlot p) t).2 ∧
        SlotAfter a (PancakeSem o p s).1 (PancakeSem o (retToSlot p) t).2 := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ihn =>
  intro p
  induction p with
  | skip =>
    intro s t _ _ h _ _ hb _
    simp only [retToSlot]
    rw [PancakeSem.eq_1, PancakeSem.eq_1]
    exact ⟨rfl, h, hb⟩
  | dec v e c ih =>
    intro s t hc hav h hout hin hb hne
    obtain ⟨hv, he, hcav⟩ := hav
    simp only [retToSlot]
    rw [PancakeSem.eq_2] at hne ⊢
    rw [PancakeSem.eq_2]
    cases hes : eval s e with
    | none => simp [hes] at hne
    | some val =>
      simp only [hes, eval_agree' h he hes] at hne ⊢
      have h' := h.withLocals (setLocal_agree h.locals v val)
      obtain ⟨hr, ha, hs⟩ := ih { s with locals := setLocal s.locals v val }
        { t with locals := setLocal t.locals v val } hc hcav h' hout hin
        (by simp only [setLocal_slot hv, hb]) hne
      exact ⟨hr, ha.withLocals (resVar_agree ha.locals v (h.locals v hv)),
        hs.withLocals (resVar_slot hv _)⟩
  | assign v e =>
    intro s t _ hav h _ _ hb hne
    obtain ⟨hv, he⟩ := hav
    simp only [retToSlot]
    rw [PancakeSem.eq_3] at hne ⊢
    rw [PancakeSem.eq_3]
    cases hes : eval s e with
    | none => simp [hes] at hne
    | some val =>
      cases hl : s.locals v with
      | none => simp [hes, hl] at hne
      | some old =>
        simp only [hl, eval_agree' h he hes, h.locals v hv]
        exact ⟨by trivial, h.withLocals (setLocal_agree h.locals v val),
          by simp only [SlotAfter, setLocal_slot hv, hb]⟩
  | store d e =>
    intro s t _ hav h _ _ hb hne
    obtain ⟨hd, he⟩ := hav
    simp only [retToSlot]
    rw [PancakeSem.eq_4] at hne ⊢
    rw [PancakeSem.eq_4]
    cases hds : eval s d with
    | none => simp [hds] at hne
    | some addr =>
      cases hes : eval s e with
      | none => simp [hds, hes] at hne
      | some val =>
        simp only [hds, hes, eval_agree' h hd hds, eval_agree' h he hes] at hne ⊢
        cases hm : memStoreWord s.memory s.memaddrs addr val with
        | none => simp [hm] at hne
        | some m =>
          obtain ⟨m', hm', ha⟩ := storeWord_agree h hm
          simp only [hm']
          exact ⟨by trivial, ha, hb⟩
  | storeByte d e =>
    intro s t _ hav h _ _ hb hne
    obtain ⟨hd, he⟩ := hav
    simp only [retToSlot]
    rw [PancakeSem.eq_10] at hne ⊢
    rw [PancakeSem.eq_10]
    cases hds : eval s d with
    | none => simp [hds] at hne
    | some addr =>
      cases hes : eval s e with
      | none => simp [hds, hes] at hne
      | some val =>
        simp only [hds, hes, eval_agree' h hd hds, eval_agree' h he hes] at hne ⊢
        cases hm : memStoreByte s.memory s.memaddrs s.be addr (val.setWidth 8) with
        | none => simp [hm] at hne
        | some m =>
          obtain ⟨m', hm', ha⟩ := storeByte_agree h hm
          simp only [hm']
          exact ⟨by trivial, ha, hb⟩
  | extCall name c cl a' al =>
    intro s t _ hav h _ _ hb hne
    obtain ⟨hc, hcl, ha, hal⟩ := hav
    simp only [retToSlot]
    rw [PancakeSem.eq_5] at hne ⊢
    rw [PancakeSem.eq_5]
    cases h1 : eval s c with
    | none => simp [h1] at hne
    | some cp =>
      cases h2 : eval s cl with
      | none => simp [h1, h2] at hne
      | some clv =>
        cases h3 : eval s a' with
        | none => simp [h1, h2, h3] at hne
        | some ap =>
          cases h4 : eval s al with
          | none => simp [h1, h2, h3, h4] at hne
          | some alv =>
            simp only [h1, h2, h3, h4, eval_agree' h hc h1, eval_agree' h hcl h2,
              eval_agree' h ha h3, eval_agree' h hal h4] at hne ⊢
            cases hconf : readByteArray s.memory s.memaddrs s.be cp clv.toNat with
            | none => simp [hconf] at hne
            | some conf =>
              cases harr : readByteArray s.memory s.memaddrs s.be ap alv.toNat with
              | none => simp [hconf, harr] at hne
              | some arr =>
                simp only [h.be, read_agree h.dom h.mem _ _ _ hconf,
                  read_agree h.dom h.mem _ _ _ harr, h.ffi]
                cases hf : callFFI o s.ffi name conf arr with
                | final ev => exact ⟨by trivial, h.empty, trivial⟩
                | ret ffi' bytes =>
                  have hlen : bytes.length = alv.toNat := by
                    rw [Safe.callFFI_ret_length hf]; exact read_length _ _ _ harr
                  have ha := h.withMemFfi
                    (write_agree h.dom bytes ap _ arr s.memory t.memory harr hlen h.mem) ffi'
                  rw [h.be] at ha
                  exact ⟨by trivial, ha, hb⟩
  | seq c1 c2 ih1 ih2 =>
    intro s t hc hav h hout hin hb hne
    obtain ⟨hav1, hav2⟩ := hav
    simp only [retToSlot]
    rw [PancakeSem.eq_6] at hne ⊢
    rw [PancakeSem.eq_6]
    have hne1 : (PancakeSem o c1 s).1 ≠ some .error := by
      intro he
      apply hne
      simp only [clampClock, he]
    obtain ⟨hr1, ha1, hs1⟩ := ih1 s t hc hav1 h hout hin hb hne1
    have ha := clamp_snd_agree s.clock ha1
    have hr : (clampClock s.clock (PancakeSem o (retToSlot c1) t)).1
        = slotResult (clampClock s.clock (PancakeSem o c1 s)).1 := hr1
    have hs : SlotAfter a (clampClock s.clock (PancakeSem o c1 s)).1
        (clampClock s.clock (PancakeSem o (retToSlot c1) t)).2 := hs1.withClock _
    have hm1 : (clampClock s.clock (PancakeSem o c1 s)).2.memaddrs = s.memaddrs :=
      memaddrs_run o c1 s
    have hm2 : (clampClock s.clock (PancakeSem o (retToSlot c1) t)).2.memaddrs = t.memaddrs :=
      memaddrs_run o (retToSlot c1) t
    have hcl : (clampClock s.clock (PancakeSem o c1 s)).2.clock ≤ n := by
      simp only [clampClock]; omega
    rw [h.clock]
    generalize clampClock s.clock (PancakeSem o c1 s) = R1 at hne ha hr hs hm1 hcl ⊢
    generalize clampClock s.clock (PancakeSem o (retToSlot c1) t) = R2 at ha hr hs hm2 ⊢
    obtain ⟨x1, s1⟩ := R1
    obtain ⟨x2, t1⟩ := R2
    simp only at hne ha hr hs hm1 hm2 hcl ⊢
    cases x1 with
    | none =>
      simp only [slotResult] at hr
      subst hr
      exact ih2 s1 t1 hcl hav2 ha (by rw [hm1]; exact hout) (by rw [hm2]; exact hin) hs hne
    | some res =>
      cases res <;> simp only [slotResult] at hr <;> subst hr <;> exact ⟨rfl, ha, hs⟩
  | cond e c1 c2 ih1 ih2 =>
    intro s t hc hav h hout hin hb hne
    obtain ⟨he, hav1, hav2⟩ := hav
    simp only [retToSlot]
    rw [PancakeSem.eq_7] at hne ⊢
    rw [PancakeSem.eq_7]
    cases hes : eval s e with
    | none => simp [hes] at hne
    | some w =>
      simp only [hes, eval_agree' h he hes] at hne ⊢
      by_cases hz : w = 0
      · simp only [hz, ne_eq, not_true_eq_false, if_false] at hne ⊢
        exact ih2 s t hc hav2 h hout hin hb hne
      · simp only [hz, ne_eq, not_false_eq_true, if_true] at hne ⊢
        exact ih1 s t hc hav1 h hout hin hb hne
  | while_ e c _ =>
    intro s t hc hav h hout hin hb hne
    obtain ⟨he, hcav⟩ := hav
    simp only [retToSlot]
    rw [PancakeSem.eq_8] at hne ⊢
    rw [PancakeSem.eq_8]
    cases hes : eval s e with
    | none => simp [hes] at hne
    | some w =>
      simp only [hes, eval_agree' h he hes, h.clock] at hne ⊢
      by_cases hz : w = 0
      · simp only [hz, ne_eq, not_true_eq_false, if_false]
        exact ⟨by trivial, h, hb⟩
      · simp only [hz, ne_eq, not_false_eq_true, if_true] at hne ⊢
        by_cases h0 : s.clock = 0
        · simp only [h0, if_true]
          exact ⟨by trivial, h.empty, trivial⟩
        · simp only [h0, if_false] at hne ⊢
          have hne1 : (PancakeSem o c (decClock s)).1 ≠ some .error := by
            intro hx
            apply hne
            simp only [clampClock, hx]
          obtain ⟨hr1, ha1, hs1⟩ := ihn (s.clock - 1) (by omega) c (decClock s) (decClock t)
            (by simp [decClock]) hcav h.decClock hout hin hb hne1
          have ha := clamp_snd_agree (s.clock - 1) ha1
          have hr : (clampClock (s.clock - 1) (PancakeSem o (retToSlot c) (decClock t))).1
              = slotResult (clampClock (s.clock - 1) (PancakeSem o c (decClock s))).1 := hr1
          have hs : SlotAfter a (clampClock (s.clock - 1) (PancakeSem o c (decClock s))).1
              (clampClock (s.clock - 1) (PancakeSem o (retToSlot c) (decClock t))).2 :=
            hs1.withClock _
          have hm1 : (clampClock (s.clock - 1) (PancakeSem o c (decClock s))).2.memaddrs
              = s.memaddrs := memaddrs_run o c (decClock s)
          have hm2 : (clampClock (s.clock - 1) (PancakeSem o (retToSlot c) (decClock t))).2.memaddrs
              = t.memaddrs := memaddrs_run o (retToSlot c) (decClock t)
          have hcl : (clampClock (s.clock - 1) (PancakeSem o c (decClock s))).2.clock < n := by
            simp only [clampClock]; omega
          generalize clampClock (s.clock - 1) (PancakeSem o c (decClock s)) = R1
            at hne ha hr hs hm1 hcl ⊢
          generalize clampClock (s.clock - 1) (PancakeSem o (retToSlot c) (decClock t)) = R2
            at ha hr hs hm2 ⊢
          obtain ⟨x1, s1⟩ := R1
          obtain ⟨x2, t1⟩ := R2
          simp only at hne ha hr hs hm1 hm2 hcl ⊢
          have hloop := ihn s1.clock hcl (.while_ e c) s1 t1 (Nat.le_refl _) ⟨he, hcav⟩ ha
            (by rw [hm1]; exact hout) (by rw [hm2]; exact hin)
          cases x1 with
          | none =>
            simp only [slotResult] at hr
            subst hr
            exact hloop hs hne
          | some res =>
            cases res with
            | continue_ =>
              simp only [slotResult] at hr
              subst hr
              exact hloop hs hne
            | break_ =>
              simp only [slotResult] at hr
              subst hr
              exact ⟨rfl, ha, hs⟩
            | error =>
              simp only [slotResult] at hr
              subst hr
              exact ⟨rfl, ha, hs⟩
            | timeout =>
              simp only [slotResult] at hr
              subst hr
              exact ⟨rfl, ha, hs⟩
            | return_ v =>
              simp only [slotResult] at hr
              subst hr
              exact ⟨rfl, ha, hs⟩
            | finalFFI ev =>
              simp only [slotResult] at hr
              subst hr
              exact ⟨rfl, ha, hs⟩
  | ret e =>
    intro s t _ hav h hout hin hb hne
    simp only [retToSlot]
    rw [PancakeSem.eq_9] at hne ⊢
    rw [PancakeSem.eq_6, PancakeSem.eq_4]
    cases hes : eval s e with
    | none => simp [hes] at hne
    | some v =>
      have het := eval_agree' h hav hes
      simp only [eval, hb, het, memStoreWord, hin, if_true, clampClock]
      rw [PancakeSem.eq_9]
      simp only [eval]
      refine ⟨rfl, ⟨fun _ _ => rfl, h.dom, fun k hk => ?_, h.be, ?_, h.ffi, h.base, h.code⟩, ?_⟩
      · simp only [emptyLocals]
        have hka : ¬ k = a := by
          rintro rfl
          simp only [emptyLocals] at hk
          rw [hout] at hk
          cases hk
        rw [if_neg hka]
        exact h.mem k hk
      · simp only [emptyLocals, Nat.min_self, h.clock]
      · simp only [SlotAfter, emptyLocals, if_true]
  | decCall rt f args cont _ =>
    intro s t hc hav h hout hin hb hne
    obtain ⟨hrt, hargs, hcav⟩ := hav
    simp only [retToSlot]
    rw [PancakeSem.eq_11] at hne ⊢
    rw [PancakeSem.eq_11]
    cases hvs : evalArgs s args with
    | none => simp [hvs] at hne
    | some vs =>
      simp only [hvs, evalArgs_agree h args hargs vs hvs, h.code] at hne ⊢
      cases hl : lookupCode s.code f vs with
      | none => simp [hl] at hne
      | some bp =>
        obtain ⟨body, params⟩ := bp
        simp only [hl, h.clock] at hne ⊢
        by_cases h0 : s.clock = 0
        · simp only [h0, if_true]
          exact ⟨by trivial, h.empty, trivial⟩
        · simp only [h0, if_false] at hne ⊢
          have hbody : Agree (fun _ => False) { decClock s with locals := params }
              { decClock t with locals := params } :=
            ⟨fun _ _ => rfl, h.dom, h.mem, h.be, by simp [decClock, h.clock], h.ffi, h.base, h.code⟩
          have hne1 : (PancakeSem o body { decClock s with locals := params }).1 ≠ some .error := by
            intro hx
            apply hne
            simp only [clampClock, hx, callEnded]
          obtain ⟨hr1, ha1⟩ := wider_run o (s.clock - 1) (fun _ => False) body _ _
            (by simp [decClock]) (progAvoids_none body) hbody hne1
          obtain ⟨hr, ha⟩ := clamp_agree (s.clock - 1) hr1 ha1
          have hm1 : (clampClock (s.clock - 1)
              (PancakeSem o body { decClock s with locals := params })).2.memaddrs = s.memaddrs :=
            memaddrs_run o body _
          have hm2 : (clampClock (s.clock - 1)
              (PancakeSem o body { decClock t with locals := params })).2.memaddrs = t.memaddrs :=
            memaddrs_run o body _
          have hcl : (clampClock (s.clock - 1)
              (PancakeSem o body { decClock s with locals := params })).2.clock < n := by
            simp only [clampClock]; omega
          generalize clampClock (s.clock - 1) (PancakeSem o body { decClock s with locals := params })
            = R1 at hne hr ha hm1 hcl ⊢
          generalize clampClock (s.clock - 1) (PancakeSem o body { decClock t with locals := params })
            = R2 at hr ha hm2 ⊢
          obtain ⟨x1, s1⟩ := R1
          obtain ⟨x2, t1⟩ := R2
          simp only at hne hr ha hm1 hm2 hcl ⊢
          subst hr
          cases x2 with
          | none => simp [callEnded] at hne
          | some res =>
            cases res with
            | return_ v =>
              simp only at hne ⊢
              have hc' := (ha.weaken (hide := (· = slotName))).withLocals
                (setLocal_agree h.locals rt v)
              obtain ⟨hr2, ha2, hs2⟩ := ihn s1.clock hcl cont
                { s1 with locals := setLocal s.locals rt v } { t1 with locals := setLocal t.locals rt v }
                (Nat.le_refl _) hcav hc' (by simp only; rw [hm1]; exact hout)
                (by simp only; rw [hm2]; exact hin) (by simp only [setLocal_slot hrt, hb]) hne
              exact ⟨hr2, ha2.withLocals (resVar_agree ha2.locals rt (h.locals rt hrt)),
                hs2.withLocals (resVar_slot hrt _)⟩
            | error => simp [callEnded] at hne
            | break_ => simp [callEnded] at hne
            | continue_ => simp [callEnded] at hne
            | timeout =>
              simp only [callEnded, slotResult]
              exact ⟨by trivial, ha.weaken.empty, trivial⟩
            | finalFFI ev =>
              simp only [callEnded, slotResult]
              exact ⟨by trivial, ha.weaken.empty, trivial⟩

/-! ## The rewrite, lowered -/

section Syntax

open Checked

/-- Whether `e` reads the local `x`. -/
def expReads (x : String) : PExpr → Bool
  | .var y => y == x
  | .binop _ a b | .shr a b | .shl a b => expReads x a || expReads x b
  | .loadw _ a | .loadb a => expReads x a
  | .const _ | .base => false

mutual
/-- Whether `s` declares `x`, at any depth. -/
def declares (x : String) : PStmt → Bool
  | .dec y _ | .call y _ _ => y == x
  | .ite _ a b => declaresL x a || declaresL x b
  | .while _ b => declaresL x b
  | _ => false
def declaresL (x : String) : List PStmt → Bool
  | [] => false
  | s :: rest => declares x s || declaresL x rest
end

mutual
/-- Whether `s` reads or assigns `x`, at any depth. -/
def touches (x : String) : PStmt → Bool
  | .dec _ e | .ret e => expReads x e
  | .assign y e => y == x || expReads x e
  | .store a b | .storeb a b => expReads x a || expReads x b
  | .ffi _ args | .call _ _ args => args.any (expReads x)
  | .ite e a b => expReads x e || touchesL x a || touchesL x b
  | .while e b => expReads x e || touchesL x b
def touchesL (x : String) : List PStmt → Bool
  | [] => false
  | s :: rest => touches x s || touchesL x rest
end

mutual
/-- Whether no statement follows a return in any list of `s`. -/
def retLast : PStmt → Bool
  | .ite _ a b => retLastL a && retLastL b
  | .while _ b => retLastL b
  | _ => true
def retLastL : List PStmt → Bool
  | [] => true
  | s :: rest => retLast s && retLastL rest && (match s with | .ret _ => rest.isEmpty | _ => true)
end

/-- What the gate's scope lets an expression read. -/
theorem expression_reads {p : Profile} {scope : List String} {x : String}
    (hx : scope.contains x = false) :
    ∀ e : PExpr, expression p scope e = .ok () → expReads x e = false := by
  intro e
  induction e with
  | base => intro _; rfl
  | const n => intro _; rfl
  | var y =>
    intro h
    simp only [expression] at h
    split at h
    · rename_i hy
      simp only [expReads, beq_eq_false_iff_ne, ne_eq]
      rintro rfl
      rw [hx] at hy
      cases hy
    · cases h
  | binop op a b iha ihb =>
    intro h
    obtain ⟨ha, hb⟩ := seq_ok h
    simp only [expReads, iha ha, ihb hb, Bool.or_false]
  | loadw sh a ih =>
    intro h
    simp only [expression] at h
    split at h
    · simp only [expReads, ih h]
    · cases h
  | loadb a ih =>
    intro h
    simp only [expression] at h
    simp only [expReads, ih h]
  | shr l r ihl ihr =>
    intro h
    simp only [expression] at h
    split at h
    · split at h
      · simp only [expReads, ihl h, Bool.false_or]
      · cases h
    · cases h
  | shl l r ihl ihr =>
    intro h
    simp only [expression] at h
    split at h
    · split at h
      · simp only [expReads, ihl h, Bool.false_or]
      · cases h
    · cases h

theorem expressions_reads {p : Profile} {scope : List String} {x : String}
    (hx : scope.contains x = false) :
    ∀ args : List PExpr, expressions p scope args = .ok () → args.any (expReads x) = false
  | [], _ => rfl
  | e :: es, h => by
    simp only [expressions] at h
    obtain ⟨he, hes⟩ := seq_ok h
    simp only [List.any_cons, expression_reads hx e he, expressions_reads hx es hes,
      Bool.false_or]

/-- **A name in scope is never declared again**, at any depth. -/
theorem checked_no_redeclaration (p : Profile) (x : String) :
    (∀ (scope : List String) (s : PStmt),
        statement p scope s = .ok () → scope.contains x = true → declares x s = false) ∧
    (∀ (scope : List String) (ss : List PStmt),
        statements p scope ss = .ok () → scope.contains x = true → declaresL x ss = false) := by
  apply statement.mutual_induct p
  · intro scope y e hid h; simp [statement, hid] at h
  · intro scope y e hid hin h
    simp only [statement, if_neg hid, if_pos hin] at h
    cases h
  · intro scope y e hid hin _ hx
    simp only [declares, beq_eq_false_iff_ne, ne_eq]
    rintro rfl
    exact hin hx
  · intro _ _ _ _ _ _; rfl
  · intro _ _ _ _ _ _; rfl
  · intro _ _ _ _ _; rfl
  · intro _ _ _ _ _; rfl
  · intro _ _ _ _; rfl
  · intro scope e a b iha ihb h hx
    simp only [statement] at h
    obtain ⟨_, hrest⟩ := seq_ok h
    obtain ⟨ha, hb⟩ := seq_ok hrest
    simp only [declares, iha ha hx, ihb hb hx, Bool.or_false]
  · intro scope e b ihb h hx
    simp only [statement] at h
    obtain ⟨_, hb⟩ := seq_ok h
    simp only [declares, ihb hb hx]
  · intro _ _ _ _ _ _ _ _ _; rfl
  · intro _ _ _ _ _ _ _ _ _; rfl
  · intro _ _ _ _ _ _ _; rfl
  · intro _ _ _ _ _ _ _; rfl
  · intro scope r fn args h hx
    simp only [declares, beq_eq_false_iff_ne, ne_eq]
    rintro rfl
    simp only [statement] at h
    unfold callCheck at h
    repeat' split at h
    all_goals first | cases h | (rename_i hc; rw [hx] at hc; cases hc) | skip
    all_goals simp_all
  · intro _ _ _; rfl
  · intro scope s rest ihs ihrest h hx
    simp only [statements] at h
    obtain ⟨hs, hrest'⟩ := seq_ok h
    split at hrest'
    · cases hrest'
    have h2 := ihrest hrest' (by
      split <;> first | exact hx | simp only [List.contains_cons, hx, Bool.or_true])
    simp only [declaresL, ihs hs hx, h2, Bool.or_false]

/-- **A name out of scope and never declared is never read or assigned**, at any depth. -/
theorem checked_no_touch (p : Profile) (x : String) :
    (∀ (scope : List String) (s : PStmt), statement p scope s = .ok () →
        scope.contains x = false → declares x s = false → touches x s = false) ∧
    (∀ (scope : List String) (ss : List PStmt), statements p scope ss = .ok () →
        scope.contains x = false → declaresL x ss = false → touchesL x ss = false) := by
  apply statement.mutual_induct p
  · intro scope y e hid h; simp [statement, hid] at h
  · intro scope y e hid hin h
    simp only [statement, if_neg hid, if_pos hin] at h
    cases h
  · intro scope y e hid hin h hx _
    simp only [statement, if_neg hid, if_neg hin] at h
    simp only [touches, expression_reads hx e h]
  · intro scope y e hin h hx _
    simp only [statement, if_pos hin] at h
    simp only [touches, expression_reads hx e h, Bool.or_false, beq_eq_false_iff_ne, ne_eq]
    rintro rfl
    rw [hx] at hin
    cases hin
  · intro scope y e hin h
    simp only [statement, if_neg hin] at h
    cases h
  · intro scope a b h hx _
    simp only [statement] at h
    obtain ⟨ha, hb⟩ := seq_ok h
    simp only [touches, expression_reads hx a ha, expression_reads hx b hb, Bool.or_false]
  · intro scope a b h hx _
    simp only [statement] at h
    obtain ⟨ha, hb⟩ := seq_ok h
    simp only [touches, expression_reads hx a ha, expression_reads hx b hb, Bool.or_false]
  · intro scope e h hx _
    simp only [statement] at h
    simp only [touches, expression_reads hx e h]
  · intro scope e a b iha ihb h hx hd
    simp only [statement] at h
    obtain ⟨he, hrest⟩ := seq_ok h
    obtain ⟨ha, hb⟩ := seq_ok hrest
    simp only [declares, Bool.or_eq_false_iff] at hd
    simp only [touches, expression_reads hx e he, iha ha hx hd.1, ihb hb hx hd.2, Bool.or_false]
  · intro scope e b ihb h hx hd
    simp only [statement] at h
    obtain ⟨he, hb⟩ := seq_ok h
    simp only [declares] at hd
    simp only [touches, expression_reads hx e he, ihb hb hx hd, Bool.or_false]
  · intro scope name c cl a al hin h hx _
    simp only [statement, if_pos hin] at h
    obtain ⟨hc, h1⟩ := seq_ok h
    obtain ⟨hcl, h2⟩ := seq_ok h1
    obtain ⟨ha, hal⟩ := seq_ok h2
    simp only [touches, List.any_cons, List.any_nil, expression_reads hx c hc,
      expression_reads hx cl hcl, expression_reads hx a ha, expression_reads hx al hal,
      Bool.or_false]
  · intro scope name c cl a al hin h
    simp only [statement, if_neg hin] at h
    cases h
  · intro scope name args hshape _ h
    exact absurd h (ffi_other_rejected hshape)
  · intro scope name args hshape _ h
    exact absurd h (ffi_other_rejected hshape)
  · intro scope r fn args h hx _
    simp only [statement] at h
    unfold callCheck at h
    simp only [touches]
    repeat' split at h
    all_goals first | cases h | exact expressions_reads hx args h
  · intro _ _ _ _; rfl
  · intro scope s rest ihs ihrest h hx hd
    simp only [statements] at h
    obtain ⟨hs, hrest'⟩ := seq_ok h
    split at hrest'
    · cases hrest'
    simp only [declaresL, Bool.or_eq_false_iff] at hd
    have h2 := ihrest hrest' (by
      split
      · simp only [declares] at hd
        simp only [List.contains_cons, hx, Bool.or_false]
        exact beq_eq_false_iff_ne.mpr (fun e => (beq_eq_false_iff_ne.mp hd.1) e.symm)
      · simp only [declares] at hd
        simp only [List.contains_cons, hx, Bool.or_false]
        exact beq_eq_false_iff_ne.mpr (fun e => (beq_eq_false_iff_ne.mp hd.1) e.symm)
      · exact hx) hd.2
    simp only [touchesL, ihs hs hx hd.1, h2, Bool.or_false]

/-- **No statement follows a return**, at any depth, in what the gate accepts. -/
theorem checked_retLast (p : Profile) :
    (∀ (scope : List String) (s : PStmt), statement p scope s = .ok () → retLast s = true) ∧
    (∀ (scope : List String) (ss : List PStmt), statements p scope ss = .ok () →
      retLastL ss = true) := by
  apply statement.mutual_induct p
  all_goals try (intros; rfl)
  · intro scope e a b iha ihb h
    simp only [statement] at h
    obtain ⟨_, hrest⟩ := seq_ok h
    obtain ⟨ha, hb⟩ := seq_ok hrest
    simp only [retLast, iha ha, ihb hb, Bool.and_self]
  · intro scope e b ihb h
    simp only [statement] at h
    obtain ⟨_, hb⟩ := seq_ok h
    simp only [retLast, ihb hb]
  · intro scope s rest ihs ihrest h
    simp only [statements] at h
    obtain ⟨hs, hrest'⟩ := seq_ok h
    split at hrest'
    · cases hrest'
    rename_i hexit
    simp only [retLastL, ihs hs, ihrest hrest', Bool.true_and]
    split
    · simp only [exits, Bool.true_and, Bool.not_eq_true'] at hexit
      simpa using hexit
    · rfl

theorem declaresL_append (x : String) :
    ∀ a b : List PStmt, declaresL x (a ++ b) = (declaresL x a || declaresL x b)
  | [], b => by simp [declaresL]
  | s :: rest, b => by
    simp only [List.cons_append, declaresL, declaresL_append x rest b, Bool.or_assoc]

/-- The rewrite declares what the function does. -/
theorem rewrite_declares (x : String) :
    (∀ s : PStmt, declaresL x (Abi.returnWordStmt s) = declares x s) ∧
    (∀ ss : List PStmt, declaresL x (Abi.returnWordStmts ss) = declaresL x ss) := by
  apply Abi.returnWordStmt.mutual_induct
  · intro e; rfl
  · intro e t f iht ihf
    simp only [Abi.returnWordStmt, declaresL, declares, iht, ihf, Bool.or_false]
  · intro e b ihb
    simp only [Abi.returnWordStmt, declaresL, declares, ihb, Bool.or_false]
  · intro s h1 h2 h3
    cases s with
    | ret e => exact absurd rfl (h1 e)
    | ite e t f => exact absurd rfl (h2 e t f)
    | «while» e b => exact absurd rfl (h3 e b)
    | _ => simp [Abi.returnWordStmt, declaresL]
  · rfl
  · intro s rest ih1 ih2
    show declaresL x (Abi.returnWordStmt s ++ Abi.returnWordStmts rest) = _
    rw [declaresL_append, ih1, ih2]; rfl

/-- What a lowered expression reads, it read before lowering. -/
theorem lowerExp_avoids {x : String} :
    ∀ (e : PExpr) (e' : PancakeExp), expReads x e = false → lowerExp e = some e' →
      ExpAvoids (· = x) e' := by
  intro e
  induction e with
  | base => intro e' _ h; cases h; trivial
  | const n => intro e' _ h; cases h; trivial
  | var y =>
    intro e' hr h
    cases h
    exact fun hy => by simp [expReads, hy] at hr
  | binop op a b iha ihb =>
    intro e' hr h
    simp only [expReads, Bool.or_eq_false_iff] at hr
    simp only [lowerExp] at h
    cases ha : lowerExp a with
    | none => simp [ha] at h
    | some a' =>
      cases hb : lowerExp b with
      | none => simp [ha, hb] at h
      | some b' =>
        simp only [ha, hb] at h
        have h1 := iha a' hr.1 ha
        have h2 := ihb b' hr.2 hb
        cases op <;> (simp only [Option.some.injEq] at h; subst h) <;>
          first | exact ⟨h1, h2⟩ | exact ⟨h2, h1⟩
  | loadw sh a ih =>
    intro e' hr h
    simp only [expReads] at hr
    cases sh with
    | zero => simp [lowerExp] at h
    | succ k =>
      cases k with
      | zero =>
        simp only [lowerExp] at h
        cases ha : lowerExp a with
        | none => simp [ha] at h
        | some a' =>
          simp only [ha, Option.some.injEq] at h
          subst h
          exact ih a' hr ha
      | succ _ => simp [lowerExp] at h
  | loadb a ih =>
    intro e' hr h
    simp only [expReads] at hr
    simp only [lowerExp] at h
    cases ha : lowerExp a with
    | none => simp [ha] at h
    | some a' =>
      simp only [ha, Option.some.injEq] at h
      subst h
      exact ih a' hr ha
  | shr l r ihl ihr =>
    intro e' hr h
    simp only [expReads, Bool.or_eq_false_iff] at hr
    simp only [lowerExp] at h
    cases hl : lowerExp l with
    | none => simp [hl] at h
    | some l' =>
      cases hr' : lowerExp r with
      | none => simp [hl, hr'] at h
      | some r' =>
        simp only [hl, hr', Option.some.injEq] at h
        subst h
        exact ⟨ihl l' hr.1 hl, ihr r' hr.2 hr'⟩
  | shl l r ihl ihr =>
    intro e' hr h
    simp only [expReads, Bool.or_eq_false_iff] at hr
    simp only [lowerExp] at h
    cases hl : lowerExp l with
    | none => simp [hl] at h
    | some l' =>
      cases hr' : lowerExp r with
      | none => simp [hl, hr'] at h
      | some r' =>
        simp only [hl, hr', Option.some.injEq] at h
        subst h
        exact ⟨ihl l' hr.1 hl, ihr r' hr.2 hr'⟩

theorem lowerArgs_avoids {x : String} :
    ∀ (args : List PExpr) (as' : List PancakeExp), args.any (expReads x) = false →
      lowerArgs args = some as' → ∀ a ∈ as', ExpAvoids (· = x) a
  | [], as', _, h => by cases h; intro a ha; cases ha
  | e :: es, as', hr, h => by
    simp only [List.any_cons, Bool.or_eq_false_iff] at hr
    simp only [lowerArgs] at h
    cases he : lowerExp e with
    | none => simp [he] at h
    | some e' =>
      cases hes : lowerArgs es with
      | none => simp [he, hes] at h
      | some es' =>
        simp only [he, hes, Option.some.injEq] at h
        subst h
        intro a ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact lowerExp_avoids e a hr.1 he
        · exact lowerArgs_avoids es es' hr.2 hes a ha

theorem fold_dec {n : String} {v : PExpr} {L : List PStmt} (hL : L ≠ []) :
    lowerStmtsFold (.dec n v :: L) =
      match lowerExp v, lowerStmtsFold L with
      | some v', some r' => some (.dec n v' r')
      | _, _ => none := by
  cases L with
  | nil => exact absurd rfl hL
  | cons _ _ => rfl

theorem fold_call {r f : String} {as : List PExpr} {L : List PStmt} (hL : L ≠ []) :
    lowerStmtsFold (.call r f as :: L) =
      match lowerArgs as, lowerStmtsFold L with
      | some as', some r' => some (.decCall r f as' r')
      | _, _ => none := by
  cases L with
  | nil => exact absurd rfl hL
  | cons _ _ => rfl

theorem fold_seq {s : PStmt} (hd : s.isDec = false) {L : List PStmt} (hL : L ≠ []) :
    lowerStmtsFold (s :: L) =
      match lowerStmt1 s, lowerStmtsFold L with
      | some s', some r' => some (.seq s' r')
      | _, _ => none := by
  cases L with
  | nil => exact absurd rfl hL
  | cons _ _ =>
    cases s with
    | dec _ _ => simp [PStmt.isDec] at hd
    | call _ _ _ => simp [PStmt.isDec] at hd
    | _ => rfl

/-- **What the gate lowers reads and declares only what its source does.** -/
theorem lower_avoids (x : String) :
    (∀ s : PStmt, touches x s = false → declares x s = false → ∀ c, lowerStmt1 s = some c →
      ProgAvoids (· = x) c) ∧
    (∀ ss : List PStmt, touchesL x ss = false → declaresL x ss = false → ∀ c,
      lowerStmtsFold ss = some c → ProgAvoids (· = x) c) := by
  apply Abi.returnWordStmt.mutual_induct
  · intro e ht _ c h
    simp only [lowerStmt1] at h
    cases he : lowerExp e with
    | none => simp [he] at h
    | some e' =>
      simp only [he, Option.some.injEq] at h
      subst h
      exact lowerExp_avoids e e' ht he
  · intro e t f iht ihf ht hd c h
    simp only [touches, Bool.or_eq_false_iff] at ht
    simp only [declares, Bool.or_eq_false_iff] at hd
    simp only [lowerStmt1] at h
    cases he : lowerExp e with
    | none => simp [he] at h
    | some e' =>
      cases hft : lowerStmtsFold t with
      | none => simp [he, hft] at h
      | some t' =>
        cases hff : lowerStmtsFold f with
        | none => simp [he, hft, hff] at h
        | some f' =>
          simp only [he, hft, hff, Option.some.injEq] at h
          subst h
          exact ⟨lowerExp_avoids e e' ht.1.1 he, iht ht.1.2 hd.1 t' hft, ihf ht.2 hd.2 f' hff⟩
  · intro e b ihb ht hd c h
    simp only [touches, Bool.or_eq_false_iff] at ht
    simp only [declares] at hd
    simp only [lowerStmt1] at h
    cases he : lowerExp e with
    | none => simp [he] at h
    | some e' =>
      cases hfb : lowerStmtsFold b with
      | none => simp [he, hfb] at h
      | some b' =>
        simp only [he, hfb, Option.some.injEq] at h
        subst h
        exact ⟨lowerExp_avoids e e' ht.1 he, ihb ht.2 hd b' hfb⟩
  · intro s _ _ _ ht hd c h
    cases s with
    | dec n v =>
      simp only [declares, beq_eq_false_iff_ne, ne_eq] at hd
      simp only [touches] at ht
      simp only [lowerStmt1] at h
      cases hv : lowerExp v with
      | none => simp [hv] at h
      | some v' =>
        simp only [hv, Option.some.injEq] at h
        subst h
        exact ⟨hd, lowerExp_avoids v v' ht hv, trivial⟩
    | assign y e =>
      simp only [touches, Bool.or_eq_false_iff, beq_eq_false_iff_ne, ne_eq] at ht
      simp only [lowerStmt1] at h
      cases he : lowerExp e with
      | none => simp [he] at h
      | some e' =>
        simp only [he, Option.some.injEq] at h
        subst h
        exact ⟨ht.1, lowerExp_avoids e e' ht.2 he⟩
    | store a b =>
      simp only [touches, Bool.or_eq_false_iff] at ht
      simp only [lowerStmt1] at h
      cases ha : lowerExp a with
      | none => simp [ha] at h
      | some a' =>
        cases hb : lowerExp b with
        | none => simp [ha, hb] at h
        | some b' =>
          simp only [ha, hb, Option.some.injEq] at h
          subst h
          exact ⟨lowerExp_avoids a a' ht.1 ha, lowerExp_avoids b b' ht.2 hb⟩
    | storeb a b =>
      simp only [touches, Bool.or_eq_false_iff] at ht
      simp only [lowerStmt1] at h
      cases ha : lowerExp a with
      | none => simp [ha] at h
      | some a' =>
        cases hb : lowerExp b with
        | none => simp [ha, hb] at h
        | some b' =>
          simp only [ha, hb, Option.some.injEq] at h
          subst h
          exact ⟨lowerExp_avoids a a' ht.1 ha, lowerExp_avoids b b' ht.2 hb⟩
    | ffi name args =>
      simp only [touches] at ht
      match args, ht, h with
      | [c, cl, a, al], ht, h =>
        simp only [List.any_cons, List.any_nil, Bool.or_false, Bool.or_eq_false_iff] at ht
        simp only [lowerStmt1] at h
        cases h1 : lowerExp c with
        | none => simp [h1] at h
        | some c' =>
          cases h2 : lowerExp cl with
          | none => simp [h1, h2] at h
          | some cl' =>
            cases h3 : lowerExp a with
            | none => simp [h1, h2, h3] at h
            | some a' =>
              cases h4 : lowerExp al with
              | none => simp [h1, h2, h3, h4] at h
              | some al' =>
                simp only [h1, h2, h3, h4, Option.some.injEq] at h
                subst h
                exact ⟨lowerExp_avoids c c' ht.1 h1, lowerExp_avoids cl cl' ht.2.1 h2,
                  lowerExp_avoids a a' ht.2.2.1 h3, lowerExp_avoids al al' ht.2.2.2 h4⟩
      | [], _, h | [_], _, h | [_, _], _, h | [_, _, _], _, h
      | _ :: _ :: _ :: _ :: _ :: _, _, h => simp [lowerStmt1] at h
    | call r f args =>
      simp only [declares, beq_eq_false_iff_ne, ne_eq] at hd
      simp only [touches] at ht
      simp only [lowerStmt1] at h
      cases ha : lowerArgs args with
      | none => simp [ha] at h
      | some as' =>
        simp only [ha, Option.some.injEq] at h
        subst h
        exact ⟨hd, lowerArgs_avoids args as' ht ha, trivial⟩
    | ret e => rename_i h1 _ _; exact absurd rfl (h1 e)
    | ite e t f => rename_i _ h2 _; exact absurd rfl (h2 e t f)
    | «while» e b => rename_i _ _ h3; exact absurd rfl (h3 e b)
  · intro _ _ c h
    simp only [lowerStmtsFold, Option.some.injEq] at h
    subst h
    trivial
  · intro s rest ih1 ih2 ht hd c h
    simp only [touchesL, Bool.or_eq_false_iff] at ht
    simp only [declaresL, Bool.or_eq_false_iff] at hd
    cases rest with
    | nil => exact ih1 ht.1 hd.1 c (by simpa [lowerStmtsFold] using h)
    | cons r rs =>
      have hL : r :: rs ≠ [] := List.cons_ne_nil _ _
      cases hdec : s.isDec with
      | false =>
        rw [fold_seq hdec hL] at h
        cases hs : lowerStmt1 s with
        | none => simp [hs] at h
        | some s' =>
          cases hr : lowerStmtsFold (r :: rs) with
          | none => simp [hs, hr] at h
          | some r' =>
            simp only [hs, hr, Option.some.injEq] at h
            subst h
            exact ⟨ih1 ht.1 hd.1 s' hs, ih2 ht.2 hd.2 r' hr⟩
      | true =>
        cases s with
        | dec n v =>
          rw [fold_dec hL] at h
          have hn := hd.1
          simp only [declares, beq_eq_false_iff_ne, ne_eq] at hn
          have ht1 := ht.1
          simp only [touches] at ht1
          cases hv : lowerExp v with
          | none => simp [hv] at h
          | some v' =>
            cases hr : lowerStmtsFold (r :: rs) with
            | none => simp [hv, hr] at h
            | some r' =>
              simp only [hv, hr, Option.some.injEq] at h
              subst h
              exact ⟨hn, lowerExp_avoids v v' ht1 hv, ih2 ht.2 hd.2 r' hr⟩
        | call rt f args =>
          rw [fold_call hL] at h
          have hn := hd.1
          simp only [declares, beq_eq_false_iff_ne, ne_eq] at hn
          have ht1 := ht.1
          simp only [touches] at ht1
          cases ha : lowerArgs args with
          | none => simp [ha] at h
          | some as' =>
            cases hr : lowerStmtsFold (r :: rs) with
            | none => simp [ha, hr] at h
            | some r' =>
              simp only [ha, hr, Option.some.injEq] at h
              subst h
              exact ⟨hn, lowerArgs_avoids args as' ht1 ha, ih2 ht.2 hd.2 r' hr⟩
        | _ => simp [PStmt.isDec] at hdec

theorem rws_cons (s : PStmt) (rest : List PStmt) :
    Abi.returnWordStmts (s :: rest) = Abi.returnWordStmt s ++ Abi.returnWordStmts rest := rfl

theorem rws_ne_nil : ∀ {ss : List PStmt}, ss ≠ [] → Abi.returnWordStmts ss ≠ []
  | [], h => absurd rfl h
  | s :: rest, _ => by
    rw [rws_cons]
    cases s <;> simp [Abi.returnWordStmt]

/-- A statement the rewrite does not turn into two is one statement after it, a declaration
only if it was one. -/
theorem rewrite_single {s : PStmt} (hd : s.isDec = false) (hr : ∀ e, s ≠ .ret e) :
    ∃ s', Abi.returnWordStmt s = [s'] ∧ s'.isDec = false := by
  cases s with
  | dec _ _ => simp [PStmt.isDec] at hd
  | call _ _ _ => simp [PStmt.isDec] at hd
  | ret e => exact absurd rfl (hr e)
  | ite e t f => exact ⟨_, rfl, rfl⟩
  | «while» e b => exact ⟨_, rfl, rfl⟩
  | assign _ _ => exact ⟨_, rfl, rfl⟩
  | store _ _ => exact ⟨_, rfl, rfl⟩
  | storeb _ _ => exact ⟨_, rfl, rfl⟩
  | ffi _ _ => exact ⟨_, rfl, rfl⟩

/-- **The rewrite lowers to the lowering rewritten**: where no statement follows a return, the
lowering of `Abi.wordResult`'s body is `retToSlot` of the function's. -/
theorem lower_rewrite :
    (∀ s : PStmt, retLast s = true → ∀ c, lowerStmt1 s = some c →
      lowerStmtsFold (Abi.returnWordStmt s) = some (retToSlot c)) ∧
    (∀ ss : List PStmt, retLastL ss = true → ∀ c, lowerStmtsFold ss = some c →
      lowerStmtsFold (Abi.returnWordStmts ss) = some (retToSlot c)) := by
  apply Abi.returnWordStmt.mutual_induct
  · intro e _ c h
    simp only [lowerStmt1] at h
    cases he : lowerExp e with
    | none => simp [he] at h
    | some e' =>
      simp only [he, Option.some.injEq] at h
      subst h
      simp only [Abi.returnWordStmt, lowerStmtsFold, lowerStmt1, lowerExp, he, retToSlot, slotName]
  · intro e t f iht ihf hr c h
    simp only [retLast, Bool.and_eq_true] at hr
    simp only [lowerStmt1] at h
    cases he : lowerExp e with
    | none => simp [he] at h
    | some e' =>
      cases hft : lowerStmtsFold t with
      | none => simp [he, hft] at h
      | some t' =>
        cases hff : lowerStmtsFold f with
        | none => simp [he, hft, hff] at h
        | some f' =>
          simp only [he, hft, hff, Option.some.injEq] at h
          subst h
          simp only [Abi.returnWordStmt, lowerStmtsFold, lowerStmt1, he, iht hr.1 t' hft,
            ihf hr.2 f' hff, retToSlot]
  · intro e b ihb hr c h
    simp only [retLast] at hr
    simp only [lowerStmt1] at h
    cases he : lowerExp e with
    | none => simp [he] at h
    | some e' =>
      cases hfb : lowerStmtsFold b with
      | none => simp [he, hfb] at h
      | some b' =>
        simp only [he, hfb, Option.some.injEq] at h
        subst h
        simp only [Abi.returnWordStmt, lowerStmtsFold, lowerStmt1, he, ihb hr b' hfb, retToSlot]
  · intro s h1 h2 h3 _ c h
    cases s with
    | ret e => exact absurd rfl (h1 e)
    | ite e t f => exact absurd rfl (h2 e t f)
    | «while» e b => exact absurd rfl (h3 e b)
    | dec n v =>
      simp only [lowerStmt1] at h
      cases hv : lowerExp v with
      | none => simp [hv] at h
      | some v' =>
        simp only [hv, Option.some.injEq] at h
        subst h
        simp only [Abi.returnWordStmt, lowerStmtsFold, lowerStmt1, hv, retToSlot]
    | call r f args =>
      simp only [lowerStmt1] at h
      cases ha : lowerArgs args with
      | none => simp [ha] at h
      | some as' =>
        simp only [ha, Option.some.injEq] at h
        subst h
        simp only [Abi.returnWordStmt, lowerStmtsFold, lowerStmt1, ha, retToSlot]
    | assign y e =>
      simp only [lowerStmt1] at h
      cases he : lowerExp e with
      | none => simp [he] at h
      | some e' =>
        simp only [he, Option.some.injEq] at h
        subst h
        simp only [Abi.returnWordStmt, lowerStmtsFold, lowerStmt1, he, retToSlot]
    | store a b =>
      simp only [lowerStmt1] at h
      cases ha : lowerExp a with
      | none => simp [ha] at h
      | some a' =>
        cases hb : lowerExp b with
        | none => simp [ha, hb] at h
        | some b' =>
          simp only [ha, hb, Option.some.injEq] at h
          subst h
          simp only [Abi.returnWordStmt, lowerStmtsFold, lowerStmt1, ha, hb, retToSlot]
    | storeb a b =>
      simp only [lowerStmt1] at h
      cases ha : lowerExp a with
      | none => simp [ha] at h
      | some a' =>
        cases hb : lowerExp b with
        | none => simp [ha, hb] at h
        | some b' =>
          simp only [ha, hb, Option.some.injEq] at h
          subst h
          simp only [Abi.returnWordStmt, lowerStmtsFold, lowerStmt1, ha, hb, retToSlot]
    | ffi name args =>
      have hw : Abi.returnWordStmt (.ffi name args) = [.ffi name args] := rfl
      rw [hw]
      show lowerStmt1 (.ffi name args) = some (retToSlot c)
      rw [h]
      match args, h with
      | [c1, c2, c3, c4], h =>
        simp only [lowerStmt1] at h
        cases h1 : lowerExp c1 <;> cases h2 : lowerExp c2 <;> cases h3 : lowerExp c3 <;>
          cases h4 : lowerExp c4 <;> simp [h1, h2, h3, h4] at h
        subst h
        rfl
      | [], h | [_], h | [_, _], h | [_, _, _], h | _ :: _ :: _ :: _ :: _ :: _, h =>
        simp [lowerStmt1] at h
  · intro _ c h
    simp only [lowerStmtsFold, Option.some.injEq] at h
    subst h
    rfl
  · intro s rest ih1 ih2 hr c h
    simp only [retLastL, Bool.and_eq_true] at hr
    obtain ⟨⟨hs, hrest⟩, hlast⟩ := hr
    cases rest with
    | nil =>
      rw [rws_cons, show Abi.returnWordStmts [] = [] from rfl, List.append_nil]
      exact ih1 hs c h
    | cons r rs =>
      have hL : r :: rs ≠ [] := List.cons_ne_nil _ _
      have hL' := rws_ne_nil hL
      cases hdec : s.isDec with
      | false =>
        have hnr : ∀ e, s ≠ .ret e := by
          rintro e rfl
          simp at hlast
        rw [fold_seq hdec hL] at h
        cases hs1 : lowerStmt1 s with
        | none => simp [hs1] at h
        | some cs =>
          cases hr1 : lowerStmtsFold (r :: rs) with
          | none => simp [hs1, hr1] at h
          | some cr =>
            simp only [hs1, hr1, Option.some.injEq] at h
            subst h
            obtain ⟨s', hs', hsd⟩ := rewrite_single hdec hnr
            have hl1 : lowerStmt1 s' = some (retToSlot cs) := by
              have := ih1 hs cs hs1
              rw [hs'] at this
              exact this
            rw [rws_cons, hs', List.singleton_append, fold_seq hsd hL', hl1, ih2 hrest cr hr1]
            rfl
      | true =>
        cases s with
        | dec n v =>
          rw [fold_dec hL] at h
          cases hv : lowerExp v with
          | none => simp [hv] at h
          | some v' =>
            cases hr1 : lowerStmtsFold (r :: rs) with
            | none => simp [hv, hr1] at h
            | some cr =>
              simp only [hv, hr1, Option.some.injEq] at h
              subst h
              rw [rws_cons, show Abi.returnWordStmt (.dec n v) = [.dec n v] from rfl,
                List.singleton_append, fold_dec hL', hv, ih2 hrest cr hr1]
              rfl
        | call rt f args =>
          rw [fold_call hL] at h
          cases ha : lowerArgs args with
          | none => simp [ha] at h
          | some as' =>
            cases hr1 : lowerStmtsFold (r :: rs) with
            | none => simp [ha, hr1] at h
            | some cr =>
              simp only [ha, hr1, Option.some.injEq] at h
              subst h
              rw [rws_cons, show Abi.returnWordStmt (.call rt f args) = [.call rt f args] from rfl,
                List.singleton_append, fold_call hL', ha, ih2 hrest cr hr1]
              rfl
        | _ => simp [PStmt.isDec] at hdec

theorem paramScope_append : ∀ (ps qs : List (Nat × String)) (sc sc'' : List String),
    paramScope (ps ++ qs) sc = .ok sc'' → ∃ sc', paramScope ps sc = .ok sc' ∧
      paramScope qs sc' = .ok sc''
  | [], qs, sc, sc'', h => ⟨sc, rfl, h⟩
  | (shape, name) :: rest, qs, sc, sc'', h => by
    simp only [List.cons_append, paramScope] at h ⊢
    split at h
    · cases h
    · split at h
      · cases h
      · split at h
        · cases h
        · rename_i h1 h2 h3
          simp only [h1, h2, h3]
          exact paramScope_append rest qs _ sc'' h

/-- The slot's parameter, added last, is a name the function's own parameters did not take. -/
theorem paramScope_slot {sc sc' : List String} (h : paramScope [(1, slotName)] sc = .ok sc') :
    sc.contains slotName = false ∧ sc'.contains slotName = true := by
  simp only [paramScope] at h
  split at h
  · cases h
  · split at h
    · cases h
    · split at h
      · cases h
      · rename_i h3
        simp only [Except.ok.injEq] at h
        subst h
        exact ⟨by simpa using h3, by simp⟩

/-- What `Checked.emit` asks of a function it prints. -/
theorem emit_parts {f : PFun} {src : String} (h : emit f = .ok src) :
    f.params.length ≤ 4 ∧ ∃ scope, paramScope f.params [] = .ok scope ∧
      statements exportedProfile scope f.body = .ok () := by
  simp only [emit, bind, Except.bind] at h
  repeat' split at h
  all_goals first
    | (simp at h; done)
    | skip
  exact ⟨by assumption, _, by assumption, by assumption⟩

/-- …and `Checked.emitWith`, in the profile of the functions it may call. -/
theorem emitWith_parts {funs : List PFun} {f : PFun} {src : String} (h : emitWith funs f = .ok src) :
    f.params.length ≤ 4 ∧ ∃ scope, paramScope f.params [] = .ok scope ∧
      statements ⟨false, [], funs.map fun g => (g.name, g.params.length), none⟩ scope f.body = .ok () := by
  simp only [emitWith, bind, Except.bind] at h
  repeat' split at h
  all_goals first
    | (simp at h; done)
    | skip
  exact ⟨by assumption, _, by assumption, by assumption⟩

/-- A body the gate takes, in some profile, with and without the slot's parameter in scope. -/
theorem rewrite_lowers {p : Profile} {body : List PStmt} {scope1 scope2 : List String}
    (hs1 : statements p scope1 body = .ok ()) (hs2 : statements p scope2 (Abi.returnWordStmts body) = .ok ())
    (hout : scope1.contains slotName = false) (hin : scope2.contains slotName = true) :
    ∃ c, lowerStmtsFold body = some c ∧ lowerStmtsFold (Abi.returnWordStmts body) = some (retToSlot c) ∧
      ProgAvoids (· = slotName) c := by
  obtain ⟨c, hc⟩ := Option.isSome_iff_exists.mp (Checked.statements_lower hs1)
  have hret := (checked_retLast p).2 _ _ hs1
  have hdecl : declaresL slotName body = false := by
    rw [← (rewrite_declares slotName).2]
    exact (checked_no_redeclaration p slotName).2 _ _ hs2 hin
  have htouch := (checked_no_touch p slotName).2 _ _ hs1 hout hdecl
  exact ⟨c, hc, (lower_rewrite).2 _ hret c hc, (lower_avoids slotName).2 _ htouch hdecl c hc⟩

/-- The scopes of a function and of its rewrite: the second adds the slot's name, which the first
does not hold. -/
theorem rewrite_scopes {ps : List (Nat × String)} {scope1 scope2 : List String}
    (hp1 : paramScope ps [] = .ok scope1) (hp2 : paramScope (ps ++ [(1, "dn_result")]) [] = .ok scope2) :
    scope1.contains slotName = false ∧ scope2.contains slotName = true := by
  obtain ⟨sc, hsc, hslot⟩ := paramScope_append ps _ [] scope2 hp2
  rw [hp1] at hsc
  cases hsc
  exact paramScope_slot hslot

end Syntax

/-! ## What `Abi.emitWord` prints -/

/-- `f` lowers to `c`, its rewrite to `c` rewritten, and `c` never reads, writes or declares the
slot's name. -/
def Rewrites (f : PFun) (c : PancakeProg) : Prop :=
  lower f = some c ∧ lower (Abi.wordResult f) = some (retToSlot c) ∧ ProgAvoids (· = slotName) c

/-- **What `Abi.emitWord` accepts lowers, and its rewrite lowers to that lowering rewritten**; the
function has at most three parameters. -/
theorem emitWord_rewrites {f : PFun} {src : String} (h : Abi.emitWord f = .ok src) :
    f.params.length ≤ 3 ∧ ∃ c, Rewrites f c := by
  simp only [Abi.emitWord, bind, Except.bind] at h
  split at h
  · cases h
  · rename_i src1 h1
    obtain ⟨_, scope1, hp1, hs1⟩ := emit_parts h1
    obtain ⟨hl2, scope2, hp2, hs2⟩ := emit_parts h
    simp only [Abi.wordResult, List.length_append, List.length_singleton] at hl2 hp2 hs2
    obtain ⟨hout, hin⟩ := rewrite_scopes hp1 hp2
    obtain ⟨c, hc, hw, hav⟩ := rewrite_lowers hs1 hs2 hout hin
    exact ⟨by omega, c, hc, hw, hav⟩

/-- …and so does what `Abi.emitWordWith` accepts, with the functions it calls. -/
theorem emitWordWith_rewrites {funs : List PFun} {f : PFun} {src : String}
    (h : Abi.emitWordWith funs f = .ok src) : f.params.length ≤ 3 ∧ ∃ c, Rewrites f c := by
  simp only [Abi.emitWordWith, bind, Except.bind] at h
  split at h
  · cases h
  · rename_i src1 h1
    obtain ⟨_, scope1, hp1, hs1⟩ := emitWith_parts h1
    obtain ⟨hl2, scope2, hp2, hs2⟩ := emitWith_parts h
    simp only [Abi.wordResult, List.length_append, List.length_singleton] at hl2 hp2 hs2
    obtain ⟨hout, hin⟩ := rewrite_scopes hp1 hp2
    obtain ⟨c, hc, hw, hav⟩ := rewrite_lowers hs1 hs2 hout hin
    exact ⟨by omega, c, hc, hw, hav⟩

/-- **The run of a rewrite ends as the function's run does.** From states that agree but on the
slot's name, the rewrite's binding it to an address the function's state cannot reach and the
rewrite's can, a run of the function that does not fail ends the same way rewritten: a value
returned is at the slot and zero is returned instead, every other ending is the same, and the
memory the function can reach, the external world and the clock end the same. The functions it
calls run as they are, from the code both states hold. -/
theorem rewrites_run {f : PFun} {c : PancakeProg} (h : Rewrites f c) (o : Oracle σ) {a : Word}
    {s t : PancakeState σ} (hst : Agree (· = slotName) s t) (hout : s.memaddrs a = false)
    (hin : t.memaddrs a = true) (hb : t.locals slotName = some a)
    (hne : (PancakeSem o c s).1 ≠ some .error) :
    (PancakeSem o (retToSlot c) t).1 = slotResult (PancakeSem o c s).1 ∧
      Agree (· = slotName) (PancakeSem o c s).2 (PancakeSem o (retToSlot c) t).2 ∧
      SlotAfter a (PancakeSem o c s).1 (PancakeSem o (retToSlot c) t).2 :=
  slot_run o a s.clock c s t (Nat.le_refl _) h.2.2 hst hout hin hb hne

/-- …in particular, a value it returns is at the slot, and the rewrite returns zero. -/
theorem rewrites_returns {f : PFun} {c : PancakeProg} (h : Rewrites f c) (o : Oracle σ)
    {a v : Word} {s t : PancakeState σ} (hst : Agree (· = slotName) s t)
    (hout : s.memaddrs a = false) (hin : t.memaddrs a = true) (hb : t.locals slotName = some a)
    (hv : (PancakeSem o c s).1 = some (.return_ v)) :
    (PancakeSem o (retToSlot c) t).1 = some (.return_ 0) ∧
      (PancakeSem o (retToSlot c) t).2.memory a = v := by
  obtain ⟨hr, _, hs⟩ := rewrites_run h o hst hout hin hb (by rw [hv]; simp)
  rw [hv] at hr hs
  exact ⟨hr, hs⟩

/-! ## The premises hold -/

/-- `a + b`, exported. -/
def addFun : PFun :=
  { name := "dn_add", exported := true, params := [(1, "a"), (1, "b")],
    body := [.ret (.binop .add (.var "a") (.var "b"))] }

/-- Its state: 2 and 3, no memory. -/
def addState : PancakeState Unit :=
  { locals := fun x => if x = "a" then some 2 else if x = "b" then some 3 else none,
    memory := fun _ => 0, memaddrs := fun _ => false, be := false, clock := 0, ffi := (),
    baseAddr := 0 }

/-- The rewrite's: the slot at 16, the one word it can reach. -/
def addSlotState : PancakeState Unit :=
  { addState with locals := setLocal addState.locals slotName 16, memaddrs := fun w => w == 16 }

/-- The two states agree but on the slot's name. -/
theorem agree_witness : Agree (· = slotName) addState addSlotState :=
  ⟨fun x hx => by simp [addSlotState, setLocal, hx], fun _ h => by simp [addState] at h,
    fun _ h => by simp [addState] at h, rfl, rfl, rfl, rfl, rfl⟩

/-- An expression and a program that avoid the slot's name, and a state after a return of 5 with 5
at the slot. -/
theorem avoids_witness :
    ExpAvoids (· = slotName) (.var "a") ∧ ProgAvoids (· = slotName) (.ret (.var "a")) ∧
      SlotAfter (σ := Unit) 16 (some (.return_ 5)) { addSlotState with memory := fun _ => 5 } :=
  ⟨by simp [ExpAvoids, slotName], by simp [ProgAvoids, ExpAvoids, slotName], rfl⟩

/-- **The theorem is not vacuous**: `a + b` with 2 and 3, rewritten, returns zero with 5 at the
slot. -/
theorem wordResult_witness :
    ∃ c, Rewrites addFun c ∧
      (PancakeSem Oracle.idle (retToSlot c) addSlotState).1 = some (.return_ 0) ∧
      (PancakeSem Oracle.idle (retToSlot c) addSlotState).2.memory 16 = 5 := by
  have hok : (Abi.emitWord addFun).isOk = true := by decide
  cases he : Abi.emitWord addFun with
  | error e => rw [he] at hok; cases hok
  | ok src =>
    obtain ⟨_, c, hc⟩ := emitWord_rewrites he
    have hlow : c = .ret (.op .add (.var "a") (.var "b")) := by
      have := hc.1
      simp only [lower, addFun, lowerStmtsFold, lowerStmt1, lowerExp, Option.some.injEq] at this
      exact this.symm
    refine ⟨c, hc, rewrites_returns hc Oracle.idle agree_witness rfl rfl
      (by simp [addSlotState, setLocal]) ?_⟩
    rw [hlow, PancakeSem.eq_9]
    simp [eval, addState]

/-- `inc x = x + 1`, a function of a program. -/
def incFun : PFun :=
  { name := "inc", params := [(1, "x")]
    body := [.ret (.binop .add (.var "x") (.const 1))] }

/-- `if a < 4 then return inc(a) else return 0`, exported: a return in each branch, one after a
call. -/
def branchFun : PFun :=
  { name := "dn_branch", exported := true, params := [(1, "a")],
    body := [.ite (.binop .lt (.var "a") (.const 4)) [.call "r" "inc" [.var "a"], .ret (.var "r")]
      [.ret (.const 0)]] }

/-- Its state: 2, and `inc` in the code. -/
def branchState : PancakeState Unit :=
  { addState with
    locals := (fun x => if x = "a" then some 2 else none)
    clock := 1
    code := (fun g => if g = "inc" then some (["x"], .ret (.op .add (.var "x") (.const 1))) else none) }

def branchSlotState : PancakeState Unit :=
  { branchState with locals := setLocal branchState.locals slotName 16, memaddrs := fun w => w == 16 }

/-- **…and with a call**: `emitWordWith` takes it with `inc`, and, rewritten, it returns zero with
`inc 2 = 3` at the slot. -/
theorem rewritesWith_witness :
    ∃ c, Rewrites branchFun c ∧
      (PancakeSem Oracle.idle (retToSlot c) branchSlotState).1 = some (.return_ 0) ∧
      (PancakeSem Oracle.idle (retToSlot c) branchSlotState).2.memory 16 = 3 := by
  have hok : (Abi.emitWordWith [incFun] branchFun).isOk = true := by decide
  cases he : Abi.emitWordWith [incFun] branchFun with
  | error e => rw [he] at hok; cases hok
  | ok src =>
    obtain ⟨_, c, hc⟩ := emitWordWith_rewrites he
    have hst : Agree (· = slotName) branchState branchSlotState :=
      ⟨fun x hx => by simp [branchSlotState, setLocal, hx],
        fun _ h => by simp [branchState, addState] at h,
        fun _ h => by simp [branchState, addState] at h, rfl, rfl, rfl, rfl, rfl⟩
    have hlow : c = .cond (.cmp .less (.var "a") (.const 4))
        (.decCall "r" "inc" [.var "a"] (.ret (.var "r"))) (.ret (.const 0)) := by
      have := hc.1
      simp only [lower, branchFun, lowerStmtsFold, lowerStmt1, lowerExp, lowerArgs,
        Option.some.injEq] at this
      exact this.symm
    refine ⟨c, hc, rewrites_returns hc Oracle.idle hst rfl rfl
      (by simp [branchSlotState, setLocal]) ?_⟩
    rw [hlow, PancakeSem.eq_7]
    simp [eval, branchState, signedLt]
    rw [PancakeSem.eq_11]
    simp [evalArgs, eval, lookupCode, decClock, clampClock, PancakeSem, setLocal]

/-- A function of four parameters, which leaves no room for the slot. -/
def fourFun : PFun :=
  { name := "dn_four", exported := true, params := [(1, "a"), (1, "b"), (1, "c"), (1, "d")],
    body := [.ret (.var "a")] }

/-- `Abi.emitWord` refuses it, as `emitWord_rewrites` says it must, though `Checked.emit` takes it. -/
theorem four_params_refused :
    (Checked.emit fourFun).isOk = true ∧ (Abi.emitWord fourFun).isOk = false := by
  decide

end DN.Compiler.Preservation
