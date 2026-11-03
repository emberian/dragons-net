-- SPDX-License-Identifier: AGPL-3.0-or-later
import DN.Server.SessionAppend
import DN.Compiler.FragRules

/-!
# DN.Server.SessionText

`connText`, if it returns, writes a reply's text, `CommandSpec.text`, into a connection's output. Exactly the branch of
code `t` runs (`dispatch`), appending its octets; non-ending runs are not excluded. So it writes the greetings, fixed
texts, STAT, GROUP, LISTGROUP and DATE replies; witnesses `w_pre` to `w_pow`.
-/

namespace DN.Server.SessionText

open DN.Compiler DN.Compiler.Wp DN.Compiler.WpRet DN.Compiler.Bytes DN.Compiler.Preservation DN.Compiler.Frag DN.Server
  DN.News DN.News.DecimalRun DN.Server.SessionAppend

variable {σ : Type}

open SessionLayout
open DN.News.FramerCode (bw)

/-! ### The replies' branches -/

/-- The codes a test of `t` takes: `t == k`, or either of two. -/
def codesOf : Syntax.PExpr → Option (List Nat)
  | .binop .eq (.var "t") (.const k) => some [k]
  | .binop .lt (.const 0) (.binop .add (.binop .eq (.var "t") (.const a)) (.binop .eq (.var "t") (.const b))) =>
    some [a, b]
  | _ => none

theorem eq_word {t k : Nat} (ht : t < 2 ^ 64) (hk : k < 2 ^ 64) :
    (if BitVec.ofNat 64 t = BitVec.ofNat 64 k then (1 : Word) else 0) = bw (decide (t = k)) := by
  by_cases h : t = k
  · subst h; simp [bw]
  · rw [if_neg (fun e => h (NatToDec.ofNat64_inj ht hk e))]; simp [bw, h]

/-- **A test of `t`** lowers, and evaluates to zero exactly when `t` is not among its codes. -/
theorem codes_eval {e : Syntax.PExpr} {cs : List Nat} (h : codesOf e = some cs) (hcs : ∀ k ∈ cs, k < 2 ^ 32) :
    ∃ E, Lower.lowerExp e = some E ∧ ∀ (s : PancakeState σ) (t : Nat), t < 2 ^ 32 →
      s.locals "t" = some (BitVec.ofNat 64 t) → eval s E = some (bw (decide (t ∈ cs))) := by
  unfold codesOf at h
  split at h
  · rename_i k
    simp only [Option.some.injEq] at h
    subst h
    have hk := hcs k (by simp)
    refine ⟨_, rfl, fun s t ht hl => ?_⟩
    simp only [eval, hl]
    rw [eq_word (by omega) (by omega)]
    simp
  · rename_i a b
    simp only [Option.some.injEq] at h
    subst h
    have ha := hcs a (by simp)
    have hb := hcs b (by simp)
    refine ⟨_, rfl, fun s t ht hl => ?_⟩
    simp only [eval, hl]
    rw [eq_word (by omega) (by omega), eq_word (by omega) (by omega)]
    exact congrArg some ((SessionCheck.or_word _ _).trans (by simp [List.mem_cons]))
  · cases h

/-- A block that lowers with nothing after it. -/
def LowK (xs : List Syntax.PStmt) : Prop := ∃ c, Block.lowerK xs .skip = some c

/-- **A branch not taken**: its test fails, so it changes nothing. -/
theorem branch_skip {o : Oracle σ} {e : Syntax.PExpr} {body : List Syntax.PStmt} {cs : List Nat}
    (hcs : codesOf e = some cs) (hcb : ∀ k ∈ cs, k < 2 ^ 32) (hlow : LowK body) {t : Nat} (htb : t < 2 ^ 32)
    (ht : t ∉ cs) {P : Assn σ} (hP : Safe.ClockFree P) (htP : ∀ s, P s → s.locals "t" = some (BitVec.ofNat 64 t)) :
    Frag o [.ite e body []] P P := by
  obtain ⟨E, hE, hev⟩ := codes_eval hcs hcb
  obtain ⟨c', hc'⟩ := hlow
  obtain ⟨c, hc, -⟩ := fold_of_K o body hc'
  refine frag_oneR (a := .cond E c .skip) (by simp [Lower.lowerStmt1, hE, hc, Lower.lowerStmtsFold_nil]) rfl hP
    fun R => WpRet.cond (fun s hs => ⟨_, hev s t htb (htP s hs)⟩) (fun s ⟨hs, hne⟩ => ?_)
      (conseq (WpRet.skip o _ R) (fun s h => h) (fun _ _ h => h) (fun s h => h.1))
  rw [hev s t htb (htP s hs)] at hne
  simp [bw, ht] at hne

/-- **The branch taken**: its test holds, so its statements run. -/
theorem branch_take {o : Oracle σ} {e : Syntax.PExpr} {body : List Syntax.PStmt} {cs : List Nat}
    (hcs : codesOf e = some cs) (hcb : ∀ k ∈ cs, k < 2 ^ 32) {t : Nat} (htb : t < 2 ^ 32) (ht : t ∈ cs)
    {P P' : Assn σ} (hP' : Safe.ClockFree P') (htP : ∀ s, P s → s.locals "t" = some (BitVec.ofNat 64 t))
    (hbody : ∀ R, ∃ c, Lower.lowerStmtsFold body = some c ∧ SafeR o P c R P') :
    Frag o [.ite e body []] P P' := by
  obtain ⟨E, hE, hev⟩ := codes_eval hcs hcb
  obtain ⟨c, hc, -⟩ := hbody (fun _ _ => True)
  refine frag_oneR (a := .cond E c .skip) (by simp [Lower.lowerStmt1, hE, hc, Lower.lowerStmtsFold_nil]) rfl hP'
    fun R => WpRet.cond (fun s hs => ⟨_, hev s t htb (htP s hs)⟩) ?_ (fun s ⟨hs, he⟩ => ?_)
  · obtain ⟨c2, hc2, hs2⟩ := hbody R
    rw [hc] at hc2
    cases hc2
    exact conseq hs2 (fun s h => h.1) (fun _ _ h => h) (fun _ h => h)
  · rw [hev s t htb (htP s hs)] at he
    simp [bw, ht] at he

/-! ### Replies of texts, the revision and the source -/

/-- A part of such a reply. -/
inductive Part
  | text (k : Nat)
  | rev
  | src

def Part.stmts : Part → List Syntax.PStmt
  | .text k => Session.appendText k
  | .rev => Session.appendRevision
  | .src => Session.appendSource

/-- Its octets, of the identity `i`. -/
def Part.bytes (i : CommandSpec.Identity) : Part → List (BitVec 8)
  | .text k => texts.getD k []
  | .rev => i.revision
  | .src => i.source

/-- Its premise: a text one of the session's. -/
def Part.ok : Part → Prop
  | .text k => k < texts.length
  | _ => True

/-- What such a reply asks of the session's words: its texts, the identity's revision and source with
their lengths. -/
structure IdIn (b : Word) (i : CommandSpec.Identity) (s0 : PancakeState σ) : Prop where
  texts : TextsIn b s0.memory s0.memaddrs s0.be
  rev : memBytesAt s0.memory s0.memaddrs s0.be (b + BitVec.ofNat 64 (ownOff + ownRev)) i.revision
  src : memBytesAt s0.memory s0.memaddrs s0.be (b + BitVec.ofNat 64 (ownOff + ownSrc)) i.source
  revLen : i.revision.length ≤ revMax
  srcLen : i.source.length ≤ srcMax

theorem part_frag (o : Oracle σ) {b : Word} (hb : b.toNat % 8 = 0) {c t : Nat} {i : CommandSpec.Identity}
    {s0 : PancakeState σ} (hc : c < conns) (hcov : Analyzer.Covers SessionLayout.size s0.memaddrs b)
    (hid : IdIn b i s0) {acc : List (BitVec 8)} {p : Part} (hp : p.ok)
    (hroom : acc.length + (p.bytes i).length ≤ data) :
    Frag o p.stmts (fun s => TCtx b c t i.revision.length i.source.length s0 s ∧ Wrote b c acc s)
      (fun s => TCtx b c t i.revision.length i.source.length s0 s ∧ Wrote b c (acc ++ p.bytes i) s) := by
  cases p with
  | text k => exact appendText_frag o hb hc hcov hid.texts hp hroom
  | rev => exact appendRevision_frag o hb hc hcov hid.rev rfl hid.revLen hroom
  | src => exact appendSource_frag o hb hc hcov hid.src rfl hid.srcLen hroom

/-- **Parts in turn** append their octets. -/
theorem parts_frag (o : Oracle σ) {b : Word} (hb : b.toNat % 8 = 0) {c t : Nat} {i : CommandSpec.Identity}
    {s0 : PancakeState σ} (hc : c < conns) (hcov : Analyzer.Covers SessionLayout.size s0.memaddrs b)
    (hid : IdIn b i s0) : ∀ (ps : List Part) {acc : List (BitVec 8)}, (∀ p ∈ ps, p.ok) →
      acc.length + ((ps.map (Part.bytes i)).flatten).length ≤ data →
      Frag o (ps.map Part.stmts).flatten (fun s => TCtx b c t i.revision.length i.source.length s0 s ∧ Wrote b c acc s)
        (fun s => TCtx b c t i.revision.length i.source.length s0 s ∧
          Wrote b c (acc ++ (ps.map (Part.bytes i)).flatten) s)
  | [], acc, _, _ => by simpa using (fun k R Q _ hk => ⟨k, rfl, hk⟩ : Frag o [] _ _)
  | p :: ps, acc, hok, hroom => by
    simp only [List.map_cons, List.flatten_cons, List.length_append] at hroom ⊢
    have h2 := parts_frag o hb (t := t) hc hcov hid ps (acc := acc ++ p.bytes i) (fun q hq => hok q (by simp [hq]))
      (by simp only [List.length_append]; omega)
    rw [List.append_assoc] at h2
    exact frag_append (part_frag o hb hc hcov hid (hok p (by simp)) (by omega)) h2

/-! ### `connText` set up -/

/-- `connText` at its entry: connection `c` and code `t` in its parameters, the session's words `s0`'s. -/
structure TEntry (b : Word) (c t : Nat) (s0 s : PancakeState σ) : Prop where
  hc : s.locals "c" = some (BitVec.ofNat 64 c)
  ht : s.locals "t" = some (BitVec.ofNat 64 t)
  base : s.baseAddr = b
  memory : s.memory = s0.memory
  memaddrs : s.memaddrs = s0.memaddrs
  be : s.be = s0.be
  code : s.code = s0.code

theorem record_eval {s : PancakeState σ} {b : Word} {c : Nat} (hb : s.baseAddr = b)
    (hc : s.locals "c" = some (BitVec.ofNat 64 c)) {E : PancakeExp}
    (hE : Lower.lowerExp (Session.record (Syntax.v "c")) = some E) : eval s E = some (SessionFrame.recordAt b c) := by
  have e : SessionFrame.recordAt b c =
      b + BitVec.ofNat 64 tableOff + BitVec.ofNat 64 c * BitVec.ofNat 64 connSlot := by
    simp only [SessionFrame.recordAt, BitVec.ofNat_add, BitVec.ofNat_mul, BitVec.add_assoc]
  rw [e]
  revert hE
  unfold Session.record SessionStore.at_ Syntax.atOff
  by_cases h2 : (tableOff == 0) = true <;>
    simp only [h2, Bool.false_eq_true, ↓reduceIte, Lower.lowerExp, Syntax.eAdd, Syntax.eMul, Syntax.n, Syntax.v,
      Option.some.injEq] <;> intro hE <;> subst hE <;> simp only [eval, hb, hc]
  rw [beq_iff_eq.mp h2, BitVec.add_zero]

/-- Connection `c`'s record lowers. -/
theorem record_lower : ∃ E, Lower.lowerExp (Session.record (Syntax.v "c")) = some E := by
  unfold Session.record SessionStore.at_ Syntax.atOff
  by_cases h2 : (tableOff == 0) = true <;> simp [h2, Lower.lowerExp, Syntax.eAdd, Syntax.eMul, Syntax.n, Syntax.v]

/-- The session's texts and the lengths of those the replies here read, computed once. -/
theorem texts_length : texts.length = 98 := by decide +kernel
theorem len_stat : (texts.getD SessionStore.tStat []).length = 4 := by decide +kernel
theorem len_crlf : (texts.getD Session.tCrlf []).length = 2 := by decide +kernel
theorem len_selected : (texts.getD Session.tSelected []).length = 4 := by decide +kernel
theorem len_time : (texts.getD Session.tTime []).length = 4 := by decide +kernel
theorem get_crlf : texts.getD Session.tCrlf [] = CommandSpec.crlf := by decide +kernel
theorem get_stat : texts.getD SessionStore.tStat [] = CommandSpec.ascii "223 " := by decide +kernel
theorem get_selected : texts.getD Session.tSelected [] = CommandSpec.ascii "211 " := by decide +kernel
theorem get_time : texts.getD Session.tTime [] = CommandSpec.ascii "111 " := by decide +kernel
theorem get_greeting : texts.getD Session.tGreetingHead [] = CommandSpec.greetingHead ∧
    texts.getD Session.tGreetingMid [] = CommandSpec.greetingMid ∧
    texts.getD Session.tGreetingPostHead [] = CommandSpec.greetingPostHead ∧
    texts.getD Session.tGreetingPostMid [] = CommandSpec.greetingPostMid := by decide +kernel

/-- The statements before `connText`'s branches. -/
def textHead : List Syntax.PStmt := Session.connText.body.take 9

/-- **`connText` set up**: its locals bound, nothing written. -/
theorem textHead_frag (o : Oracle σ) {b : Word} {c t : Nat} {i : CommandSpec.Identity}
    {s0 : PancakeState σ} (hc : c < conns) (hcov : Analyzer.Covers SessionLayout.size s0.memaddrs b)
    (hrl : s0.memory (b + BitVec.ofNat 64 (ownOff + ownRevLen)) = BitVec.ofNat 64 i.revision.length)
    (hsl : s0.memory (b + BitVec.ofNat 64 (ownOff + ownSrcLen)) = BitVec.ofNat 64 i.source.length)
    (hrm : i.revision.length ≤ revMax) (hsm : i.source.length ≤ srcMax) :
    Frag o textHead (TEntry b c t s0)
      (fun s => TCtx b c t i.revision.length i.source.length s0 s ∧ Wrote b c [] s) := by
  obtain ⟨T, hT, h8, hend, hown⟩ := lay
  obtain ⟨-, -, -, hd, hn, h64⟩ := nums
  have hr : ownRevLen % 8 = 0 ∧ ownSrcLen % 8 = 0 ∧ ownSrcLen < ownTexts ∧ ownRevLen < ownSrcLen ∧
      ownOff % 8 = 0 ∧ cOut ≠ 0 ∧ conns - 1 < 2 ^ 63 ∧ revMax < 2 ^ 63 ∧ srcMax < 2 ^ 63 := by decide
  obtain ⟨E, hE⟩ := record_lower
  have hO : Lower.lowerExp (Syntax.atOff (Syntax.v "cb") cOut) = some
      (.op .add (.var "cb") (.const (BitVec.ofNat 64 cOut))) := by
    have : (cOut == 0) = false := by rw [beq_eq_false_iff_ne]; exact hr.2.2.2.2.2.1
    simp [Syntax.atOff, this, Lower.lowerExp, Syntax.eAdd, Syntax.n, Syntax.v]
  have hld : ∀ X, X ≠ 0 → Lower.lowerExp (SessionStore.ld (SessionStore.at_ X)) =
      some (.loadWord (.op .add .base (.const (BitVec.ofNat 64 X)))) := fun X hX => by
    simp [SessionStore.ld, Lower.lowerExp, at_lower hX]
  have hrd : ∀ (s : PancakeState σ) X, TEntry b c t s0 s → X % 8 = 0 → 64 ≤ X → X < tOff →
      eval s (.loadWord (.op .add .base (.const (BitVec.ofNat 64 X)))) = some (s0.memory (b + BitVec.ofNat 64 X)) :=
    fun s X h h1 h2 h3 => by simp only [eval, h.base, h.memaddrs, own_addr hcov h1 h2 h3, if_true, h.memory]
  have hset : ∀ s y (v : Value), TEntry b c t s0 s → y ≠ "c" → y ≠ "t" →
      TEntry b c t s0 { s with locals := setLocal s.locals y v } := fun s y v h h1 h2 =>
    ⟨by simp [setLocal, Ne.symm h1, h.hc], by simp [setLocal, Ne.symm h2, h.ht], h.base, h.memory, h.memaddrs, h.be,
      h.code⟩
  let F : PancakeState σ → Prop := fun s => s.locals "cb" = some (SessionFrame.recordAt b c) ∧
    s.locals "ob" = some (outAt b c) ∧ s.locals "o" = some 0 ∧ s.locals "j" = some 0 ∧
    s.locals "rl" = some (BitVec.ofNat 64 i.revision.length) ∧ s.locals "sl" = some (BitVec.ofNat 64 i.source.length)
  have e : textHead = [SessionStore.keptIn (Syntax.v "c") (conns - 1)] ++
      ([.dec "cb" (Session.record (Syntax.v "c"))] ++ ([.dec "ob" (Syntax.atOff (Syntax.v "cb") cOut)] ++
      ([.dec "o" (Syntax.n 0)] ++ ([.dec "j" (Syntax.n 0)] ++
      ([.dec "rl" (SessionStore.ld (SessionStore.at_ (ownOff + ownRevLen)))] ++
      ([.dec "sl" (SessionStore.ld (SessionStore.at_ (ownOff + ownSrcLen)))] ++
      ([SessionStore.keptIn (Syntax.v "rl") revMax] ++ [SessionStore.keptIn (Syntax.v "sl") srcMax]))))))) := rfl
  rw [e]
  have k1 := frag_keptIn o (e := Syntax.v "c") rfl hr.2.2.2.2.2.2.1
    (fun _ _ h => { h with } : Safe.ClockFree (TEntry b c t s0))
    fun s h => ⟨c, by omega, h.hc⟩
  let Q1 : Assn σ := fun s => TEntry b c t s0 s ∧ s.locals "cb" = some (SessionFrame.recordAt b c)
  let Q2 : Assn σ := fun s => Q1 s ∧ s.locals "ob" = some (outAt b c)
  let Q3 : Assn σ := fun s => Q2 s ∧ s.locals "o" = some 0
  let Q4 : Assn σ := fun s => Q3 s ∧ s.locals "j" = some 0
  let Q5 : Assn σ := fun s => Q4 s ∧ s.locals "rl" = some (BitVec.ofNat 64 i.revision.length)
  let Q6 : Assn σ := fun s => Q5 s ∧ s.locals "sl" = some (BitVec.ofNat 64 i.source.length)
  have d1 : Frag o [.dec "cb" (Session.record (Syntax.v "c"))] (TEntry b c t s0) Q1 :=
    frag_dec o hE fun s h => ⟨_, record_eval h.base h.hc hE, hset s _ _ h (by decide) (by decide),
      by simp [setLocal]⟩
  have d2 : Frag o [.dec "ob" (Syntax.atOff (Syntax.v "cb") cOut)] Q1 Q2 :=
    frag_dec o hO fun s ⟨h, hcb⟩ => ⟨outAt b c, by simp [eval, hcb, outAt], ⟨hset s _ _ h (by decide) (by decide),
      (by simp [setLocal, hcb])⟩, by simp [setLocal]⟩
  have d3 : Frag o [.dec "o" (Syntax.n 0)] Q2 Q3 :=
    frag_dec o rfl fun s ⟨⟨h, hcb⟩, hob⟩ => ⟨_, rfl, ⟨⟨hset s _ _ h (by decide) (by decide),
      (by simp [setLocal, hcb])⟩, (by simp [setLocal, hob])⟩, by simp [setLocal]⟩
  have d4 : Frag o [.dec "j" (Syntax.n 0)] Q3 Q4 :=
    frag_dec o rfl fun s ⟨⟨⟨h, hcb⟩, hob⟩, ho⟩ => ⟨_, rfl, ⟨⟨⟨hset s _ _ h (by decide) (by decide),
      (by simp [setLocal, hcb])⟩, (by simp [setLocal, hob])⟩, (by simp [setLocal, ho])⟩, by simp [setLocal]⟩
  have d5 : Frag o [.dec "rl" (SessionStore.ld (SessionStore.at_ (ownOff + ownRevLen)))] Q4 Q5 :=
    frag_dec o (hld _ (by omega)) fun s ⟨⟨⟨⟨h, hcb⟩, hob⟩, ho⟩, hj⟩ =>
      ⟨_, hrd s _ h (by omega) (by omega) (by omega), ⟨⟨⟨⟨hset s _ _ h (by decide) (by decide),
      (by simp [setLocal, hcb])⟩, (by simp [setLocal, hob])⟩, (by simp [setLocal, ho])⟩, (by simp [setLocal, hj])⟩,
      by simp [setLocal, hrl]⟩
  have d6 : Frag o [.dec "sl" (SessionStore.ld (SessionStore.at_ (ownOff + ownSrcLen)))] Q5 Q6 :=
    frag_dec o (hld _ (by omega)) fun s ⟨⟨⟨⟨⟨h, hcb⟩, hob⟩, ho⟩, hj⟩, hrl'⟩ =>
      ⟨_, hrd s _ h (by omega) (by omega) (by omega), ⟨⟨⟨⟨⟨hset s _ _ h (by decide) (by decide),
      (by simp [setLocal, hcb])⟩, (by simp [setLocal, hob])⟩, (by simp [setLocal, ho])⟩, (by simp [setLocal, hj])⟩,
      (by simp [setLocal, hrl'])⟩, by simp [setLocal, hsl]⟩
  have hQ6 : Safe.ClockFree Q6 := fun _ _ ⟨⟨⟨⟨⟨⟨h, hcb⟩, hob⟩, ho⟩, hj⟩, hrl'⟩, hsl'⟩ =>
    ⟨⟨⟨⟨⟨⟨{ h with }, hcb⟩, hob⟩, ho⟩, hj⟩, hrl'⟩, hsl'⟩
  have k2 : Frag o [SessionStore.keptIn (Syntax.v "rl") revMax] Q6 Q6 :=
    frag_keptIn o (e := Syntax.v "rl") rfl hr.2.2.2.2.2.2.2.1 hQ6 fun s h => ⟨_, hrm, h.1.2⟩
  have k3 : Frag o [SessionStore.keptIn (Syntax.v "sl") srcMax] Q6 Q6 :=
    frag_keptIn o (e := Syntax.v "sl") rfl hr.2.2.2.2.2.2.2.2 hQ6 fun s h => ⟨_, hsm, h.2⟩
  refine frag_conseq (frag_append k1 (frag_append d1 (frag_append d2 (frag_append d3 (frag_append d4
    (frag_append d5 (frag_append d6 (frag_append k2 k3)))))))) (fun s h => h) ?_
  rintro s ⟨⟨⟨⟨⟨⟨h, hcb⟩, hob⟩, ho⟩, hj⟩, hrl'⟩, hsl'⟩
  exact ⟨⟨h.hc, h.ht, hcb, hob, ⟨_, hj⟩, hrl', hsl', h.base, h.memaddrs, h.be, h.code,
    fun w _ _ => by rw [h.memory]⟩,
    ho, fun _ hi => by simp at hi⟩

/-! ### `connText`'s end -/

/-- Where connection `c`'s record keeps how long its output is. -/
def lenAt (b : Word) (c : Nat) : Word := SessionFrame.recordAt b c + BitVec.ofNat 64 cOutLen

theorem lenAt_off (b : Word) (c : Nat) : lenAt b c = b + BitVec.ofNat 64 (tOff + c * 2712 + 64) := by
  rw [lenAt, SessionFrame.recordAt, add_ofNat, ← tOff_eq, nums.slot, nums.outLen]

/-- …a word of its own, not one of the output's. -/
theorem lenAt_out {b : Word} (hb : b.toNat % 8 = 0) {c : Nat} (hc : c < conns) : ¬ OutWord b c (lenAt b c) := by
  obtain ⟨T, hT, h8, hend, -⟩ := lay
  obtain ⟨-, -, -, hd, hn, -⟩ := nums
  rintro ⟨i, hi, e⟩
  rw [lenAt_off, outAt_off, add_ofNat] at e
  rw [← byteAlign_of_aligned hb (X := tOff + c * 2712 + 64) (by omega)] at e
  exact words_apart hb (by omega) (by omega) (by omega) e

/-- What `connText` gives back if it returns: zero, connection `c`'s output `bs` and its length. Every word but those
and the return word as `m0` has it; octets past `bs` are not described. -/
def TextRet (b : Word) (c : Nat) (bs : List (BitVec 8)) (dm : Word → Bool) (be : Bool) (m0 : Word → Word) : Ret :=
  fun v m => v = 0 ∧ memBytesAt m dm be (outAt b c) bs ∧ m (lenAt b c) = BitVec.ofNat 64 bs.length ∧
    ∀ w, ¬ OutWord b c w → w ≠ lenAt b c → w ≠ SessionCheck.retW b → m w = m0 w

/-- The statements after `connText`'s branches. -/
def textTail : List Syntax.PStmt := Session.connText.body.drop 57

theorem textTail_eq :
    textTail = [.store (Syntax.atOff (Syntax.v "cb") cOutLen) (Syntax.v "o"), .ret (Syntax.n 0)] := rfl

/-- **`connText`'s end**: the output's length in the record, zero returned. -/
theorem textTail_run (o : Oracle σ) {b : Word} (hb : b.toNat % 8 = 0) {c t rl sl : Nat} {s0 : PancakeState σ}
    (hc : c < conns) (hcov : Analyzer.Covers SessionLayout.size s0.memaddrs b) {bs : List (BitVec 8)}
    (hroom : bs.length ≤ data) :
    ∃ k, Lower.lowerStmtsFold textTail = some k ∧
      SafeR o (fun s => TCtx b c t rl sl s0 s ∧ Wrote b c bs s) k (TextRet b c bs s0.memaddrs s0.be s0.memory)
        (fun _ => False) := by
  obtain ⟨T, hT, h8, hend, -⟩ := lay
  obtain ⟨-, -, -, hd, hn, -⟩ := nums
  have e := textTail_eq
  have h64 : (cOutLen == 0) = false := by decide
  have hL : lenAt b c = byteAlign (lenAt b c) := by
    rw [lenAt_off, byteAlign_of_aligned hb (by omega)]
  refine ⟨.seq (.store (.op .add (.var "cb") (.const (BitVec.ofNat 64 cOutLen))) (.var "o")) (.ret (.const 0)),
    by rw [e]; simp [Lower.lowerStmtsFold, Lower.lowerStmt1, Lower.lowerExp, Syntax.atOff, h64, Syntax.eAdd,
      Syntax.n, Syntax.v], ?_⟩
  refine WpRet.seq
      (M := fun s => s.memaddrs = s0.memaddrs ∧ s.be = s0.be ∧ TextRet b c bs s0.memaddrs s0.be s0.memory 0 s.memory)
    (WpRet.store fun s ⟨hx, hw⟩ => ⟨lenAt b c, BitVec.ofNat 64 bs.length,
      fun k => if k = lenAt b c then BitVec.ofNat 64 bs.length else s.memory k, by simp [eval, hx.hcb, lenAt],
      hw.1, ?_, ?_⟩) (WpRet.ret fun s ⟨_, _, h⟩ => ⟨0, rfl, h⟩) (fun _ _ h => h)
  · simp only [memStoreWord]
    rw [if_pos]
    rw [hx.memaddrs, lenAt_off]
    exact hcov.2 _ (by simp only [Analyzer.floor]; have := nums.own64; obtain ⟨T, hT, -, hroom, hown⟩ := lay; omega)
      (by have := out_in hc (show 0 < data by omega); omega) (by omega)
  · refine ⟨hx.memaddrs, hx.be, rfl, fun i hi => ?_, by simp, fun w hw' hne hr => by simp [hne, hx.words w hw' hr]⟩
    simp only
    have hi' : i < data := by omega
    rw [load_of_word (m := s.memory) (by rw [if_neg]; intro h; exact lenAt_out hb hc ⟨i, hi', h.symm⟩),
      ← hx.memaddrs, ← hx.be]
    exact hw.2 i hi

/-! ### The branch of a code -/

/-- The codes a branch takes, if it is one. -/
def stmtCodes : Syntax.PStmt → Option (List Nat)
  | .ite e _ [] => codesOf e
  | _ => none

/-- Its statements. -/
def stmtBody : Syntax.PStmt → List Syntax.PStmt
  | .ite _ body _ => body
  | _ => []

theorem stmtCodes_some {x : Syntax.PStmt} {l : List Nat} (h : stmtCodes x = some l) :
    ∃ e, x = .ite e (stmtBody x) [] ∧ codesOf e = some l := by
  unfold stmtCodes at h
  split at h
  · rename_i e body
    exact ⟨e, rfl, h⟩
  · cases h

/-- Branches and their codes, in turn. -/
def Coded : List Syntax.PStmt → List (List Nat) → Prop
  | [], [] => True
  | x :: L, l :: cs => stmtCodes x = some l ∧ Coded L cs
  | _, _ => False

theorem coded_of_map : ∀ (L : List Syntax.PStmt) (cs : List (List Nat)), L.map stmtCodes = cs.map some → Coded L cs
  | [], [], _ => trivial
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | x :: L, l :: cs, h => by
    simp only [List.map_cons, List.cons.injEq] at h
    exact ⟨h.1, coded_of_map L cs h.2⟩

/-- **Branches none of which takes `t`**, coded. -/
theorem coded_skip {o : Oracle σ} {t : Nat} (htb : t < 2 ^ 32) {P : Assn σ} (hP : Safe.ClockFree P)
    (htP : ∀ s, P s → s.locals "t" = some (BitVec.ofNat 64 t)) :
    ∀ (L : List Syntax.PStmt) (cs : List (List Nat)), Coded L cs → (∀ x ∈ L, LowK (stmtBody x)) →
      (∀ l ∈ cs, ∀ k ∈ l, k < 2 ^ 32) → (∀ l ∈ cs, t ∉ l) → Frag o L P P
  | [], _, _, _, _, _ => fun k R Q _ hk => ⟨k, rfl, hk⟩
  | _ :: _, [], h, _, _, _ => h.elim
  | x :: L, l :: cs, ⟨hx, hL⟩, hlow, hcb, hout => by
    obtain ⟨e, hxe, hce⟩ := stmtCodes_some hx
    have h1 := branch_skip (o := o) hce (hcb l (by simp)) (hlow x (by simp)) htb (hout l (by simp)) hP htP
    rw [← hxe] at h1
    exact frag_append (xs := [_]) h1 (coded_skip htb hP htP L cs hL (fun y hy => hlow y (by simp [hy]))
      (fun l' hl' => hcb l' (by simp [hl'])) (fun l' hl' => hout l' (by simp [hl'])))

/-- **The branch `j` of a code** runs, the others not. -/
theorem dispatch (o : Oracle σ) {t : Nat} (htb : t < 2 ^ 32) {P P' : Assn σ} (hP : Safe.ClockFree P)
    (hP' : Safe.ClockFree P') (htP : ∀ s, P s → s.locals "t" = some (BitVec.ofNat 64 t))
    (htP' : ∀ s, P' s → s.locals "t" = some (BitVec.ofNat 64 t)) :
    ∀ (L : List Syntax.PStmt) (cs : List (List Nat)), Coded L cs →
      (∀ x ∈ L, LowK (stmtBody x)) → (∀ l ∈ cs, ∀ k ∈ l, k < 2 ^ 32) → ∀ (j : Nat) (hj : j < L.length),
      t ∈ cs.getD j [] → (∀ l ∈ cs.take j, t ∉ l) → (∀ l ∈ cs.drop (j + 1), t ∉ l) →
      (∀ R, ∃ c, Lower.lowerStmtsFold (stmtBody L[j]) = some c ∧ SafeR o P c R P') → Frag o L P P'
  | [], _, _, _, _, _, hj, _, _, _, _ => absurd hj (by simp)
  | _ :: _, [], h, _, _, _, _, _, _, _, _ => h.elim
  | x :: L, l :: cs, ⟨hx, hL⟩, hlow, hcb, j, hj, hin, hpre, hpost, hbody => by
    obtain ⟨e, hxe, hce⟩ := stmtCodes_some hx
    have hlowL : ∀ y ∈ L, LowK (stmtBody y) := fun y hy => hlow y (by simp [hy])
    have hcbs : ∀ l' ∈ cs, ∀ k ∈ l', k < 2 ^ 32 := fun l' hl' => hcb l' (by simp [hl'])
    cases j with
    | zero =>
      have h1 := branch_take (o := o) hce (hcb l (by simp)) htb (by simpa using hin) hP' htP
        (by simpa [← hxe] using hbody)
      rw [← hxe] at h1
      exact frag_append (xs := [_]) h1 (coded_skip htb hP' htP' L cs hL hlowL hcbs (by simpa using hpost))
    | succ j =>
      have h1 := branch_skip (o := o) hce (hcb l (by simp)) (hlow x (by simp)) htb (hpre l (by simp)) hP htP
      rw [← hxe] at h1
      exact frag_append (xs := [_]) h1 (dispatch o htb hP hP' htP htP' L cs hL hlowL hcbs j (by simpa using hj)
        (by simpa using hin) (fun l' hl' => hpre l' (by simp [hl'])) (by simpa using hpost) (by simpa using hbody))

/-! ### `connText`'s branches -/

open DN.Server.Session (appendText appendRevision appendSource appendId appendNumber ownW tGreetingHead tGreetingMid tCrlf
  tCapabilitiesHead tBlockEnd tHelpHead tHelpMid tQuit tNoGroup tNoSuchId tUnknown tSyntax tGreetingPostHead
  tGreetingPostMid tCapabilitiesPostTail tHelpPostHead tPost tPosted tFailed tNotPermitted tUnavailable tSelected
  tNoSuchGroup tNoCurrent tNoNext tNoPrevious tNoNumber tActiveHead tNoDescriptions tNoNewGroups tTime
  tCapabilitiesReaderTail tModeReader tReaderPosting tReaderNoPosting tNoneOver tNoneHdr tNoRange tFieldRefused
  tOverviewFmtText tHeaderList tCapabilitiesAuthTail tAuthUser tAuthAccepted tAuthFailed tAuthSequence
  tEncryptionRequired tAuthDone tAuthRequired textLen)

/-- The replies that are one text of the session's, and their texts. -/
def textOnly : List (CommandSpec.Reply × Nat) :=
  [(.quit, tQuit), (.noGroup, tNoGroup), (.noSuchId, tNoSuchId), (.unknown, tUnknown),
   (.syntax, tSyntax), (.post, tPost), (.posted, tPosted), (.failed, tFailed),
   (.notPermitted, tNotPermitted), (.unavailable, tUnavailable), (.unreadable, SessionStore.tUnreadable),
   (.noSuchGroup, tNoSuchGroup), (.noCurrent, tNoCurrent), (.noNext, tNoNext),
   (.noPrevious, tNoPrevious), (.noNumber, tNoNumber), (.modeReader, tModeReader),
   (.readerPosting, tReaderPosting), (.readerNoPosting, tReaderNoPosting), (.noneOver, Session.tNoneOver),
   (.noneHdr, Session.tNoneHdr), (.noRange, Session.tNoRange), (.fieldRefused, Session.tFieldRefused),
   (.overviewFmt, tOverviewFmtText), (.headerList, Session.tHeaderList), (.authUser [], tAuthUser),
   (.authAccepted, tAuthAccepted), (.authFailed, tAuthFailed), (.authSequence, tAuthSequence),
   (.encryptionRequired, tEncryptionRequired), (.authDone, tAuthDone), (.authRequired, tAuthRequired)]

/-- What a branch of `connText` writes. -/
inductive Branch
  | parts (ps : List Part)
  | stat
  | time
  | listed

def Branch.body : Branch → List Syntax.PStmt
  | .parts ps => (ps.map Part.stmts).flatten
  | .stat => [appendText SessionStore.tStat, appendNumber "sn" (ownW ownNum), appendId, appendText tCrlf].flatten
  | .time => [appendText tTime, SessionStore.callS "dt" "dateText" [Syntax.v "c", Syntax.v "o"],
      [.assign "o" SessionStore.found, SessionStore.keptIn (Syntax.v "o") (data - textLen tCrlf)],
      appendText tCrlf].flatten
  | .listed => List.flatten
      [appendText tSelected, appendNumber "nc" (ownW ownCount), appendNumber "nl" (ownW ownLow),
       appendNumber "nh" (ownW ownHigh),
       [.dec "sg" (SessionStore.fld "cb" cGroup), SessionStore.keptIn (Syntax.v "sg") groupsMax,
        SessionStore.ifs (Syntax.eEq (Syntax.v "sg") (Syntax.n 0)) (SessionStore.stop brokenState),
        .dec "gp" (Syntax.eAdd (SessionStore.at_ (recOff + News.RecoverProg.rGroups))
          (Syntax.eMul (Syntax.eSub (Syntax.v "sg") (Syntax.n 1)) (Syntax.n News.RecoverProg.rGroupSlot))),
        .dec "gl" (SessionStore.ld (Syntax.v "gp")), SessionStore.keptIn (Syntax.v "gl") groupMax,
        SessionStore.keptIn (Syntax.v "o") (data - groupMax - 2)],
       SessionStore.copy "j" (Syntax.eAdd (Syntax.v "ob") (Syntax.v "o")) (Syntax.atOff (Syntax.v "gp") 8)
       (Syntax.v "gl"),
       [.assign "o" (Syntax.eAdd (Syntax.v "o") (Syntax.v "gl"))], appendText tCrlf]

/-- The branches, in turn. -/
def textKinds : List Branch :=
  [.parts [.text tGreetingHead, .rev, .text tGreetingMid, .src, .text tCrlf],
   .parts [.text tGreetingPostHead, .rev, .text tGreetingPostMid, .src, .text tCrlf],
   .parts [.text tCapabilitiesHead, .rev, .text tBlockEnd],
   .parts [.text tCapabilitiesHead, .rev, .text tCapabilitiesReaderTail, .text tCapabilitiesPostTail, .text tBlockEnd],
   .parts [.text tCapabilitiesHead, .rev, .text tCapabilitiesReaderTail, .text tBlockEnd],
   .parts [.text tCapabilitiesHead, .rev, .text tCapabilitiesAuthTail, .text tBlockEnd],
   .parts [.text tCapabilitiesHead, .rev, .text tCapabilitiesReaderTail, .text tCapabilitiesAuthTail, .text tBlockEnd],
   .parts [.text tCapabilitiesHead, .rev, .text tCapabilitiesReaderTail, .text tCapabilitiesPostTail,
     .text tCapabilitiesAuthTail, .text tBlockEnd],
   .parts [.text tHelpHead, .rev, .text tHelpMid, .src, .text tBlockEnd],
   .parts [.text tHelpPostHead, .rev, .text tHelpMid, .src, .text tBlockEnd],
   .stat, .parts [.text tActiveHead], .parts [.text tNoDescriptions], .parts [.text tNoNewGroups], .time, .listed] ++
  textOnly.map fun (_, k) => .parts [.text k]

/-- `connText`'s branches. -/
def textBranches : List Syntax.PStmt := (Session.connText.body.drop 9).take 48

/-- …their codes. -/
def textCodes : List (List Nat) :=
  [[15], [16], [1], [13], [40], [58], [59], [60], [2], [14], [18], [32], [33], [34], [36], [24, 31], [3], [4], [5],
   [6], [7], [8], [9], [10], [11], [12], [19], [25], [26], [27], [28], [29], [37], [38], [39], [44], [45], [46],
   [47], [48], [49], [51], [53], [54], [55], [56], [57], [61]]

theorem text_coded : Coded textBranches textCodes := coded_of_map _ _ (by decide +kernel)

theorem textBranches_length : textBranches.length = 48 := by decide +kernel

theorem text_bodies : textBranches.map stmtBody = textKinds.map Branch.body := by rfl

/-! ### Every branch lowers -/

theorem lowKK_copyAppend {src len : Syntax.PExpr} {SRC LEN : PancakeExp} (hs : Lower.lowerExp src = some SRC)
    (hl : Lower.lowerExp len = some LEN) :
    LowKK (SessionStore.copy "j" (Syntax.eAdd (Syntax.v "ob") (Syntax.v "o")) src len ++
      [.assign "o" (Syntax.eAdd (Syntax.v "o") len)]) := fun k => ⟨_, copyAppend_lowerK hs hl k⟩

theorem lowKK_part (p : Part) : LowKK p.stmts := by
  have h64 := nums.own64
  cases p with
  | text k => exact lowKK_copyAppend (at_lower (show ownOff + ownTexts + textAt k ≠ 0 by omega)) rfl
  | rev => exact lowKK_copyAppend (at_lower (show ownOff + ownRev ≠ 0 by omega)) rfl
  | src => exact lowKK_copyAppend (at_lower (show ownOff + ownSrc ≠ 0 by omega)) rfl

theorem lowKK_id : LowKK appendId := by
  have h64 := nums.own64
  rw [appendId_eq]
  exact lowKK_append (lowKK_dec (E := .loadWord (.op .add .base (.const (BitVec.ofNat 64 (ownOff + ownIdLen)))))
    (by simp [SessionStore.ld, Lower.lowerExp, at_lower (show ownOff + ownIdLen ≠ 0 by omega)]))
    (lowKK_append (lowKK_one rfl (SessionRun.keptIn_lower rfl 250))
      (lowKK_copyAppend (at_lower (show ownOff + ownId ≠ 0 by omega)) rfl))

theorem lowKK_number (p : String) {x : Syntax.PExpr} {X : PancakeExp} (hx : Lower.lowerExp x = some X) :
    LowKK (appendNumber p x) :=
  lowKK_append (fun k => ⟨_, digits_lowerK (DST := .var "ob") rfl hx k⟩)
    (lowKK_append (lowKK_one rfl rfl) (lowKK_one rfl rfl))

theorem ownW_lower (X : Nat) :
    Lower.lowerExp (ownW X) = some (.loadWord (.op .add .base (.const (BitVec.ofNat 64 (ownOff + X))))) := by
  have h64 := nums.own64
  simp [ownW, SessionStore.ld, Lower.lowerExp, at_lower (show ownOff + X ≠ 0 by omega)]

theorem lowKK_branch : ∀ br : Branch, LowKK br.body
  | .parts ps => lowKK_flatten _ fun p hp => by
      obtain ⟨q, -, rfl⟩ := List.mem_map.mp hp
      exact lowKK_part q
  | .stat => by
    have h := nums.own64
    refine lowKK_flatten _ fun p hp => ?_
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl
    · exact lowKK_part (.text _)
    · exact lowKK_number "sn" (ownW_lower _)
    · exact lowKK_id
    · exact lowKK_part (.text _)
  | .time => by
    have h := nums.own64
    refine lowKK_flatten _ fun p hp => ?_
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl
    · exact lowKK_part (.text _)
    · exact lowKK_append (lowKK_call rfl) (lowKK_one rfl rfl)
    · exact lowKK_append (lowKK_one (a := .assign "o" (.loadWord (.op .add .base
        (.const (BitVec.ofNat 64 (ownOff + ownRet)))))) rfl (by simp [Lower.lowerStmt1, SessionStore.found,
        SessionStore.ld, Lower.lowerExp, at_lower (show ownOff + ownRet ≠ 0 by omega)]))
        (lowKK_one rfl (SessionRun.keptIn_lower rfl _))
    · exact lowKK_part (.text _)
  | .listed => by
    have h := nums.own64
    have hr : recOff + News.RecoverProg.rGroups ≠ 0 :=
      Nat.ne_of_gt (Nat.lt_of_lt_of_le (show 0 < News.RecoverProg.rGroups by decide) (Nat.le_add_left _ _))
    refine lowKK_flatten _ fun p hp => ?_
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact lowKK_part (.text _)
    · exact lowKK_number "nc" (ownW_lower _)
    · exact lowKK_number "nl" (ownW_lower _)
    · exact lowKK_number "nh" (ownW_lower _)
    · have hg : (cGroup == 0) = false := by decide
      have hstop : Lower.lowerStmtsFold (SessionStore.stop brokenState) = some SessionRun.stopG := rfl
      have l1 : LowKK [.dec "sg" (SessionStore.fld "cb" cGroup)] :=
        lowKK_dec (E := .loadWord (.op .add (.var "cb") (.const (BitVec.ofNat 64 cGroup))))
          (by simp [SessionStore.fld, SessionStore.ld, Syntax.atOff, hg, Lower.lowerExp, Syntax.eAdd, Syntax.n, Syntax.v])
      have l2 : LowKK [SessionStore.keptIn (Syntax.v "sg") groupsMax] := lowKK_one rfl (SessionRun.keptIn_lower rfl _)
      have l3 : LowKK [SessionStore.ifs (Syntax.eEq (Syntax.v "sg") (Syntax.n 0)) (SessionStore.stop brokenState)] :=
        lowKK_one (a := .cond (.cmp .equal (.var "sg") (.const 0)) SessionRun.stopG .skip) rfl
          (by simp [SessionStore.ifs, Lower.lowerStmt1, Lower.lowerExp, Syntax.eEq, Syntax.v, Syntax.n, hstop,
            Lower.lowerStmtsFold_nil])
      have l4 : LowKK [.dec "gp" (Syntax.eAdd (SessionStore.at_ (recOff + News.RecoverProg.rGroups))
          (Syntax.eMul (Syntax.eSub (Syntax.v "sg") (Syntax.n 1)) (Syntax.n News.RecoverProg.rGroupSlot)))] :=
        lowKK_dec (E := .op .add (.op .add .base (.const (BitVec.ofNat 64 (recOff + News.RecoverProg.rGroups))))
          (.mul (.op .sub (.var "sg") (.const (BitVec.ofNat 64 1))) (.const (BitVec.ofNat 64 News.RecoverProg.rGroupSlot))))
          (at_add_lower hr rfl)
      have l5 : LowKK [.dec "gl" (SessionStore.ld (Syntax.v "gp"))] :=
        lowKK_dec (E := .loadWord (.var "gp")) rfl
      have l6 : LowKK [SessionStore.keptIn (Syntax.v "gl") groupMax] := lowKK_one rfl (SessionRun.keptIn_lower rfl _)
      have l7 : LowKK [SessionStore.keptIn (Syntax.v "o") (data - groupMax - 2)] :=
        lowKK_one rfl (SessionRun.keptIn_lower rfl _)
      have := lowKK_append l1 (lowKK_append l2 (lowKK_append l3 (lowKK_append l4 (lowKK_append l5
        (lowKK_append l6 l7)))))
      simp only [List.cons_append, List.nil_append] at this
      exact this
    · exact fun k => ⟨_, copy_lowerK (SRC := .op .add (.var "gp") (.const 8)) rfl
        (by simp [Syntax.atOff, Lower.lowerExp, Syntax.eAdd, Syntax.n, Syntax.v]) rfl k⟩
    · exact lowKK_one rfl rfl
    · exact lowKK_part (.text _)

/-! ### `connText` whole -/

theorem text_split : Session.connText.body = textHead ++ (textBranches ++ textTail) := by
  have e2 := List.take_append_drop 48 (Session.connText.body.drop 9)
  rw [List.drop_drop] at e2
  simp only [textHead, textBranches, textTail]
  rw [show 57 = 9 + 48 from rfl, e2]
  exact (List.take_append_drop 9 _).symm

theorem text_low : ∀ x ∈ textBranches, LowK (stmtBody x) := fun x hx => by
  have h : stmtBody x ∈ textKinds.map Branch.body := text_bodies ▸ List.mem_map_of_mem hx
  obtain ⟨br, -, e⟩ := List.mem_map.mp h
  rw [← e]
  exact lowKK_branch br .skip

theorem text_codes_small : ∀ l ∈ textCodes, ∀ k ∈ l, k < 2 ^ 32 := by decide +kernel

/-- The premises of `connText` on the session's words: aligned, covered, holding the texts and the identity. The
connection is one of the table's. -/
structure TextPre (b : Word) (c : Nat) (i : CommandSpec.Identity) (s0 : PancakeState σ) : Prop where
  hok : i.ok = true
  hb : b.toNat % 8 = 0
  hc : c < conns
  hcov : Analyzer.Covers SessionLayout.size s0.memaddrs b
  hid : IdIn b i s0
  hrl : s0.memory (b + BitVec.ofNat 64 (ownOff + ownRevLen)) = BitVec.ofNat 64 i.revision.length
  hsl : s0.memory (b + BitVec.ofNat 64 (ownOff + ownSrcLen)) = BitVec.ofNat 64 i.source.length

theorem tw_t {b : Word} {c t rl sl : Nat} {s0 : PancakeState σ} {acc : List (BitVec 8)} :
    ∀ s, (TCtx b c t rl sl s0 s ∧ Wrote b c acc s) → s.locals "t" = some (BitVec.ofNat 64 t) :=
  fun _ h => h.1.ht

/-- **`connText`, its branch `j` writing `bs`**: if it returns, zero returned, `bs` and its length in connection `c`'s
record. Every word but those and the return word is as it was. -/
theorem connText_branch (o : Oracle σ) {b : Word} {c t : Nat} {i : CommandSpec.Identity} {s0 : PancakeState σ}
    (hpre : TextPre b c i s0) (ht : t < 2 ^ 32) {bs : List (BitVec 8)} (hroom : bs.length ≤ data) (j : Nat)
    (hj : j < textBranches.length) (hin : t ∈ textCodes.getD j []) (hpre' : ∀ l ∈ textCodes.take j, t ∉ l)
    (hpost : ∀ l ∈ textCodes.drop (j + 1), t ∉ l)
    (hbody : ∀ R, ∃ c', Lower.lowerStmtsFold (stmtBody textBranches[j]) = some c' ∧
      SafeR o (fun s => TCtx b c t i.revision.length i.source.length s0 s ∧ Wrote b c [] s) c' R
        (fun s => TCtx b c t i.revision.length i.source.length s0 s ∧ Wrote b c bs s)) :
    ∃ k, Lower.lowerStmtsFold Session.connText.body = some k ∧
      SafeR o (TEntry b c t s0) k (TextRet b c bs s0.memaddrs s0.be s0.memory) (fun _ => False) := by
  have hd := dispatch o ht (tw_clock b c t _ _ s0 []) (tw_clock b c t _ _ s0 bs) tw_t tw_t textBranches textCodes
    text_coded text_low text_codes_small j hj hin hpre' hpost hbody
  have hh := textHead_frag o (t := t) hpre.hc hpre.hcov hpre.hrl hpre.hsl hpre.hid.revLen hpre.hid.srcLen
  obtain ⟨k, hk, hks⟩ := textTail_run o hpre.hb (t := t) (rl := i.revision.length) (sl := i.source.length)
    (s0 := s0) hpre.hc hpre.hcov hroom
  obtain ⟨c', hc', hs⟩ := frag_append hh hd k (TextRet b c bs s0.memaddrs s0.be s0.memory) (fun _ => False)
    (fun _ _ _ h _ => h) hks
  refine ⟨c', ?_, hs⟩
  rw [text_split, ← List.append_assoc, Block.fold_split _ _ (by rw [textTail_eq]; simp) hk]
  exact hc'

theorem body_at (j : Nat) (hj : j < textBranches.length) :
    stmtBody textBranches[j] = (textKinds.getD j (.parts [])).body := by
  have h := congrArg (fun l => l[j]?) text_bodies
  simp only [List.getElem?_map, List.getElem?_eq_getElem hj, Option.map_some] at h
  have hj' : j < textKinds.length := by
    have := congrArg List.length text_bodies
    simp only [List.length_map] at this
    omega
  rw [List.getElem?_eq_getElem hj', Option.map_some, Option.some.injEq] at h
  rw [h, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj', Option.getD_some]

theorem declared_parts : ∀ ps : List Part, declared (ps.map Part.stmts).flatten = []
  | [] => rfl
  | p :: ps => by
    rw [List.map_cons, List.flatten_cons, declared_append, declared_parts ps]
    cases p <;> rfl

/-- **A branch of texts, the revision and the source** writes their octets. -/
theorem connText_parts (o : Oracle σ) {b : Word} {c t : Nat} {i : CommandSpec.Identity} {s0 : PancakeState σ}
    (hpre : TextPre b c i s0) (ht : t < 2 ^ 32) (j : Nat) (hj : j < textBranches.length) {ps : List Part}
    (hk : textKinds.getD j (.parts []) = .parts ps) (hin : t ∈ textCodes.getD j [])
    (hpre' : ∀ l ∈ textCodes.take j, t ∉ l) (hpost : ∀ l ∈ textCodes.drop (j + 1), t ∉ l)
    (hok : ∀ p ∈ ps, p.ok)
    (hroom : ((ps.map (Part.bytes i)).flatten).length ≤ data) :
    ∃ k, Lower.lowerStmtsFold Session.connText.body = some k ∧
      SafeR o (TEntry b c t s0) k (TextRet b c (ps.map (Part.bytes i)).flatten s0.memaddrs s0.be s0.memory)
        (fun _ => False) := by
  refine connText_branch o hpre ht hroom j hj hin hpre' hpost fun R => ?_
  rw [body_at j hj, hk]
  have h := parts_frag o hpre.hb (t := t) hpre.hc hpre.hcov hpre.hid ps (acc := []) hok (by simpa using hroom)
  simp only [List.nil_append] at h
  exact frag_close h (fun u y v _ hy => by simp [declared_parts] at hy) R

theorem tw_restore {b : Word} {c t rl sl : Nat} {s0 : PancakeState σ} {acc : List (BitVec 8)} (u : PancakeState σ)
    (y : String) (v : Option Value) (h : TCtx b c t rl sl s0 u ∧ Wrote b c acc u) (hy : y ∉ ctxNames) :
    TCtx b c t rl sl s0 (restore u y v) ∧ Wrote b c acc (restore u y v) :=
  ⟨tctx_restore h.1 hy v, wrote_restore h.2 hy v⟩

/-- A branch declaring none of `connText`'s locals closes on its own. -/
theorem tw_close {o : Oracle σ} {b : Word} {c t rl sl : Nat} {s0 : PancakeState σ} {xs : List Syntax.PStmt}
    {acc : List (BitVec 8)} {P : Assn σ} (h : Frag o xs P (fun s => TCtx b c t rl sl s0 s ∧ Wrote b c acc s))
    (hd : (declared xs).all (fun y => !ctxNames.contains y) = true) (R : Ret) :
    ∃ c', Lower.lowerStmtsFold xs = some c' ∧ SafeR o P c' R (fun s => TCtx b c t rl sl s0 s ∧ Wrote b c acc s) :=
  frag_close h (fun u y v hq hy => tw_restore u y v hq fun hm => by
    have := List.all_eq_true.mp hd y hy
    simp [hm] at this) R

/-- A number the session keeps in its own words, read. -/
theorem eval_ownW {b : Word} (hb : b.toNat % 8 = 0) {c t rl sl : Nat} {s0 : PancakeState σ} (hc : c < conns)
    (hcov : Analyzer.Covers SessionLayout.size s0.memaddrs b) {X : Nat} (hX : X % 8 = 0) (hXt : X < ownTexts)
    (hXr : X ≠ ownRet)
    {s : PancakeState σ} (hx : TCtx b c t rl sl s0 s) :
    eval s (.loadWord (.op .add .base (.const (BitVec.ofNat 64 (ownOff + X))))) =
      some (s0.memory (b + BitVec.ofNat 64 (ownOff + X))) := by
  obtain ⟨T, hT, -, -, hown⟩ := lay
  obtain ⟨-, -, -, -, -, h64⟩ := nums
  have h8 := nums.ownAl
  exact eval_own hb hc hcov hx (by omega) (by omega) (by omega) (by omega)

/-- What STAT's reply asks of the session's words: the article's number and its message-id. -/
structure StatIn (b : Word) (n : Nat) (id : List (BitVec 8)) (s0 : PancakeState σ) : Prop where
  hnum : s0.memory (b + BitVec.ofNat 64 (ownOff + ownNum)) = BitVec.ofNat 64 n
  hsmall : n < 2 ^ 32
  hidLen : s0.memory (b + BitVec.ofNat 64 (ownOff + ownIdLen)) = BitVec.ofNat 64 id.length
  hid : memBytesAt s0.memory s0.memaddrs s0.be (b + BitVec.ofNat 64 (ownOff + ownId)) id
  hidMax : id.length ≤ 250

/-- STAT's octets. -/
def statBytes (n : Nat) (id : List (BitVec 8)) : List (BitVec 8) :=
  texts.getD SessionStore.tStat [] ++ CommandSpec.decimal n ++ [BitVec.ofNat 8 32] ++ id ++ texts.getD tCrlf []

/-- **STAT's branch** writes its octets. -/
theorem stat_body (o : Oracle σ) {b : Word} {c t : Nat} {i : CommandSpec.Identity} {s0 : PancakeState σ}
    (hpre : TextPre b c i s0) {n : Nat} {id : List (BitVec 8)} (hs : StatIn b n id s0)
    (hroom : (statBytes n id).length ≤ data) (R : Ret) :
    ∃ c', Lower.lowerStmtsFold Branch.stat.body = some c' ∧
      SafeR o (fun s => TCtx b c t i.revision.length i.source.length s0 s ∧ Wrote b c [] s) c' R
        (fun s => TCtx b c t i.revision.length i.source.length s0 s ∧ Wrote b c (statBytes n id) s) := by
  have hl := texts_length
  have ht4 : textLen SessionStore.tStat = 4 := len_stat
  have hd : data = 512 := nums.dataLen
  have hN := numDigits_le_ten n hs.hsmall
  have hdl := decimal_length n
  simp only [statBytes, List.length_append, List.length_singleton] at hroom
  have h1 := appendText_frag o hpre.hb (t := t) (rl := i.revision.length) (sl := i.source.length) (acc := [])
    (k := SessionStore.tStat) hpre.hc hpre.hcov hpre.hid.texts (by rw [hl]; decide)
    (by simp only [textLen, List.length_nil]; omega)
  have h2 := appendNumber_frag o (t := t) (rl := i.revision.length) (sl := i.source.length)
    (acc := [] ++ texts.getD SessionStore.tStat []) hpre.hc hpre.hcov (p := "sn") (x := ownW ownNum)
    (ownW_lower _) (by decide) (by simp [ExpAvoids]) hs.hsmall
    (fun s hx _ => by rw [eval_ownW hpre.hb hpre.hc hpre.hcov (by decide) (by decide) (by decide) hx, hs.hnum])
    (by simp only [List.length_nil, List.length_append, Nat.zero_add]; simp only [textLen] at ht4; omega)
  have h3 := appendId_frag o hpre.hb (t := t) (rl := i.revision.length) (sl := i.source.length)
    (acc := [] ++ texts.getD SessionStore.tStat [] ++ CommandSpec.decimal n ++ [BitVec.ofNat 8 32]) hpre.hc
    hpre.hcov hs.hidLen hs.hid hs.hidMax
    (by simp only [List.length_nil, List.length_append, List.length_singleton, Nat.zero_add]; omega)
  have h4 := appendText_frag o hpre.hb (t := t) (rl := i.revision.length) (sl := i.source.length)
    (acc := [] ++ texts.getD SessionStore.tStat [] ++ CommandSpec.decimal n ++ [BitVec.ofNat 8 32] ++ id)
    (k := tCrlf) hpre.hc hpre.hcov hpre.hid.texts (by rw [hl]; decide)
    (by simp only [textLen, List.length_nil, List.length_append, List.length_singleton]; omega)
  have hf := frag_append h1 (frag_append h2 (frag_append h3 (frag_append h4 (fun k _ _ _ hk => ⟨k, rfl, hk⟩ :
    Frag o [] _ _))))
  simp only [List.nil_append] at hf
  exact tw_close hf (by decide +kernel) R

/-! ### GROUP's and LISTGROUP's branch -/

/-- Where recovery keeps the name of group `sg`, counted from one. -/
@[irreducible] def groupAt (sg : Nat) : Nat := recOff + News.RecoverProg.rGroups +
    (sg - 1) * News.RecoverProg.rGroupSlot

/-- Recovery's area lies past the connections' records, its groups within it. -/
theorem group_in {sg : Nat} (h1 : 1 ≤ sg) (h2 : sg ≤ groupsMax) :
    tOff + 173568 ≤ groupAt sg ∧ groupAt sg + 8 + groupMax < 2 ^ 62 ∧ groupAt sg % 8 = 0 ∧
      groupAt sg + 8 + groupMax ≤ SessionLayout.size := by
  have hend := table_end
  have hrec := rec_off
  have h3 := size_fits
  rw [show heapBytes = 4194304 by decide +kernel] at h3
  have hr : News.RecoverProg.rGroups + groupsMax * News.RecoverProg.rGroupSlot ≤ News.RecoverProg.size ∧
      News.RecoverProg.rGroups % 8 = 0 ∧ News.RecoverProg.rGroupSlot = 72 ∧ groupsMax = 64 ∧ groupMax = 64 ∧
      conns = 64 ∧ connSlot = 2712 := by decide
  have h8 := table_aligned
  obtain ⟨hr1, hr2, hr3, hr4, hr5, hr6, hr7⟩ := hr
  rw [hr6, hr7] at hend hrec
  unfold groupAt
  rw [hrec, hr3]
  rw [hr4] at hr1 h2
  rw [hr5]
  rw [hr3] at hr1
  generalize SessionLayout.size = S at *
  generalize News.RecoverProg.size = RS at *
  generalize News.RecoverProg.rGroups = G at *
  generalize tOff = T at *
  have : (sg - 1) * 72 ≤ 63 * 72 := Nat.mul_le_mul_right 72 (by omega)
  refine ⟨by omega, by omega, by omega, by omega⟩

/-- What GROUP's and LISTGROUP's reply asks of the session's words: the group's count, lowest and highest numbers. Also
connection `c`'s group, whose name recovery keeps. -/
structure ListedIn (b : Word) (c count low high sg : Nat) (g : List (BitVec 8)) (s0 : PancakeState σ) : Prop where
  hcount : s0.memory (b + BitVec.ofNat 64 (ownOff + ownCount)) = BitVec.ofNat 64 count
  hlow : s0.memory (b + BitVec.ofNat 64 (ownOff + ownLow)) = BitVec.ofNat 64 low
  hhigh : s0.memory (b + BitVec.ofNat 64 (ownOff + ownHigh)) = BitVec.ofNat 64 high
  hsmall : count < 2 ^ 32 ∧ low < 2 ^ 32 ∧ high < 2 ^ 32
  hsg : s0.memory (SessionFrame.recordAt b c + BitVec.ofNat 64 cGroup) = BitVec.ofNat 64 sg
  hsg1 : 1 ≤ sg
  hsgm : sg ≤ groupsMax
  hgl : s0.memory (b + BitVec.ofNat 64 (groupAt sg)) = BitVec.ofNat 64 g.length
  hg : memBytesAt s0.memory s0.memaddrs s0.be (b + BitVec.ofNat 64 (groupAt sg + 8)) g
  hgm : g.length ≤ groupMax

/-- Their octets. -/
def listedBytes (count low high : Nat) (g : List (BitVec 8)) : List (BitVec 8) :=
  texts.getD tSelected [] ++ CommandSpec.decimal count ++ [BitVec.ofNat 8 32] ++ CommandSpec.decimal low ++
    [BitVec.ofNat 8 32] ++ CommandSpec.decimal high ++ [BitVec.ofNat 8 32] ++ g ++ texts.getD tCrlf []

/-- A word of the session's at offset `X`, below the output or past the connections' records, read. -/
theorem eval_word {b : Word} (hb : b.toNat % 8 = 0) {c t rl sl X : Nat} {s0 s : PancakeState σ} (hc : c < conns)
    (hcov : Analyzer.Covers SessionLayout.size s0.memaddrs b) (hx : TCtx b c t rl sl s0 s) (hX : X % 8 = 0)
    (h64 : 64 ≤ X) (hXs : X < SessionLayout.size) (hout : X < tOff + c * 2712 + 2200 ∨ tOff + 173568 ≤ X)
    (hXr : X ≠ ownOff + ownRet)
    {E : PancakeExp} (hE : eval s E = some (b + BitVec.ofNat 64 X)) :
    eval s (.loadWord E) = some (s0.memory (b + BitVec.ofNat 64 X)) := by
  obtain ⟨T, hT, h8, hend, -⟩ := lay
  obtain ⟨-, -, -, hd, hn, -⟩ := nums
  have hXe : X < 2 ^ 63 := by
    have := size_fits
    rw [show heapBytes = 4194304 by decide +kernel] at this
    revert hXs
    generalize SessionLayout.size = S at *
    intro hXs
    omega
  have hw : ¬ OutWord b c (b + BitVec.ofNat 64 X) := by
    rintro ⟨i, hi, e⟩
    rw [outAt_off, add_ofNat, ← byteAlign_of_aligned hb hX] at e
    exact words_apart hb (by omega) (by omega) (by rcases hout with h | h <;> omega) e
  have hr : ownOff + ownRet < 2 ^ 63 := by
    obtain ⟨T, hT, -, hroom, hown⟩ := lay; have := nums.ret8; omega
  simp only [eval, hE, hx.memaddrs, hcov.2 X (by simp only [Analyzer.floor]; omega) hXs hX, if_true,
    hx.words _ hw (region_addr_inj b _ _ (by omega) (by omega) hXr)]

theorem recordAt_off (b : Word) (c r : Nat) : SessionFrame.recordAt b c + BitVec.ofNat 64 r =
    b + BitVec.ofNat 64 (tOff + c * 2712 + r) := by
  rw [SessionFrame.recordAt, add_ofNat, ← tOff_eq, show connSlot = 2712 by decide]

/-- **GROUP's and LISTGROUP's branch** writes its octets. -/
theorem listed_body (o : Oracle σ) {b : Word} {c t : Nat} {i : CommandSpec.Identity} {s0 : PancakeState σ}
    (hpre : TextPre b c i s0) {count low high sg : Nat} {gn : List (BitVec 8)}
    (hl : ListedIn b c count low high sg gn s0)
    (R : Ret) :
    ∃ c', Lower.lowerStmtsFold Branch.listed.body = some c' ∧
      SafeR o (fun s => TCtx b c t i.revision.length i.source.length s0 s ∧ Wrote b c [] s) c' R
        (fun s => TCtx b c t i.revision.length i.source.length s0 s ∧ Wrote b c (listedBytes count low high gn) s) := by
  obtain ⟨T, hT, -, hend, hown⟩ := lay
  obtain ⟨-, -, -, hd, hn, h64⟩ := nums
  obtain ⟨hcs, hls, hhs⟩ := hl.hsmall
  have dc := numDigits_le_ten count hcs
  have dl := numDigits_le_ten low hls
  have dh := numDigits_le_ten high hhs
  rw [← decimal_length] at dc dl dh
  have hgm := hl.hgm
  have hsg1 := hl.hsg1
  have hsgm := hl.hsgm
  have hgm' : groupMax = 64 := rfl
  have hgsm : groupsMax = 64 := rfl
  have hr8 := nums.ret8
  obtain ⟨gi1, gi2, gi3, -⟩ := group_in hl.hsg1 hl.hsgm
  have hrl := hpre.hid.revLen
  have hsl := hpre.hid.srcLen
  let rl := i.revision.length
  let sl := i.source.length
  -- the texts and the numbers
  have h1 := appendText_frag o hpre.hb (t := t) (rl := rl) (sl := sl) (acc := []) (k := tSelected) hpre.hc hpre.hcov
    hpre.hid.texts (by rw [texts_length]; decide) (by simp only [textLen, List.length_nil, len_selected]; omega)
  have hnum : ∀ {acc : List (BitVec 8)} (p : String) (X v : Nat), X % 8 = 0 → X < ownTexts → X ≠ ownRet →
      s0.memory (b + BitVec.ofNat 64 (ownOff + X)) = BitVec.ofNat 64 v → v < 2 ^ 32 →
      p ++ "n" ≠ p ++ "t" ∧ p ++ "n" ≠ p ++ "q" ∧ p ++ "t" ≠ p ++ "q" ∧ p ++ "n" ∉ ctxNames ∧
        p ++ "t" ∉ ctxNames ∧ p ++ "q" ∉ ctxNames → acc.length + 11 ≤ data →
      Frag o (appendNumber p (ownW X)) (fun s => TCtx b c t rl sl s0 s ∧ Wrote b c acc s)
        (fun s => TCtx b c t rl sl s0 s ∧ Wrote b c (acc ++ CommandSpec.decimal v ++ [BitVec.ofNat 8 32]) s) :=
    fun p X v hX8 hXt hXr hv hv32 hp hroom =>
      appendNumber_frag o hpre.hc hpre.hcov (ownW_lower _) hp (by simp [ExpAvoids]) hv32
        (fun s hx _ => by rw [eval_ownW hpre.hb hpre.hc hpre.hcov hX8 hXt hXr hx, hv]) hroom
  have h2 := hnum (acc := [] ++ texts.getD tSelected []) "nc" ownCount count (by decide +kernel) (by decide +kernel)
    (by decide +kernel) hl.hcount hcs (by decide)
    (by simp only [List.length_append, List.length_nil, len_selected]; omega)
  have h3 := hnum (acc := [] ++ texts.getD tSelected [] ++ CommandSpec.decimal count ++ [BitVec.ofNat 8 32]) "nl"
    ownLow low (by decide +kernel) (by decide +kernel) (by decide +kernel) hl.hlow hls (by decide)
    (by simp only [List.length_append, List.length_nil, List.length_singleton, len_selected]; omega)
  have h4 := hnum (acc := [] ++ texts.getD tSelected [] ++ CommandSpec.decimal count ++ [BitVec.ofNat 8 32] ++
      CommandSpec.decimal low ++ [BitVec.ofNat 8 32]) "nh" ownHigh high (by decide +kernel) (by decide +kernel)
    (by decide +kernel) hl.hhigh
    hhs (by decide) (by simp only [List.length_append, List.length_nil, List.length_singleton, len_selected]; omega)
  -- the group's record
  obtain ⟨a4, ha4d⟩ : ∃ a : List (BitVec 8), a = [] ++ texts.getD tSelected [] ++ CommandSpec.decimal count ++
      [BitVec.ofNat 8 32] ++ CommandSpec.decimal low ++ [BitVec.ofNat 8 32] ++ CommandSpec.decimal high ++
      [BitVec.ofNat 8 32] := ⟨_, rfl⟩
  have ha4 : a4.length ≤ 37 := by
    rw [ha4d]
    simp only [List.length_append, List.length_nil, List.length_singleton,
      len_selected]
    omega
  rw [← ha4d] at h4
  let Q0 : Assn σ := fun s => TCtx b c t rl sl s0 s ∧ Wrote b c a4 s
  let Q1 : Assn σ := fun s => Q0 s ∧ s.locals "sg" = some (BitVec.ofNat 64 sg)
  let Q2 : Assn σ := fun s => Q1 s ∧ s.locals "gp" = some (b + BitVec.ofNat 64 (groupAt sg))
  let Q3 : Assn σ := fun s => Q2 s ∧ s.locals "gl" = some (BitVec.ofNat 64 gn.length)
  have cQ0 : ∀ s k, Q0 s → Q0 { s with clock := k } := fun s k h => tw_clock b c t rl sl s0 a4 s k h
  have cQ1 : Safe.ClockFree Q1 := fun s k ⟨h, h1⟩ => ⟨cQ0 s k h, h1⟩
  have cQ3 : Safe.ClockFree Q3 := fun s k ⟨⟨⟨h, h1⟩, h2⟩, h3⟩ => ⟨⟨⟨cQ0 s k h, h1⟩, h2⟩, h3⟩
  have setQ0 : ∀ s y (v : Value), Q0 s → y ∉ tNames → y ≠ "o" → Q0 { s with locals := setLocal s.locals y v } :=
    fun s y v ⟨hx, hw⟩ hy ho => ⟨hx.set hy v, hw.set ho v⟩
  have hsgX : (tOff + c * 2712 + cGroup) % 8 = 0 ∧ 64 ≤ tOff + c * 2712 + cGroup ∧
      tOff + c * 2712 + cGroup < SessionLayout.size ∧ tOff + c * 2712 + cGroup < tOff + c * 2712 + 2200 := by
    have := out_in hpre.hc (show 0 < data by omega)
    have hg : cGroup = 160 := rfl
    obtain ⟨_, _, h8, _, _⟩ := lay
    rw [hg]
    omega
  have hg8 : (cGroup == 0) = false := by decide
  have d1 : Frag o [.dec "sg" (SessionStore.fld "cb" cGroup)] Q0 Q1 :=
    frag_dec o (E := .loadWord (.op .add (.var "cb") (.const (BitVec.ofNat 64 cGroup))))
      (by simp [SessionStore.fld, SessionStore.ld, Syntax.atOff, hg8, Lower.lowerExp, Syntax.eAdd, Syntax.n, Syntax.v])
      fun s h => ⟨_, eval_word hpre.hb hpre.hc hpre.hcov h.1 hsgX.1 hsgX.2.1 hsgX.2.2.1 (Or.inl hsgX.2.2.2)
        (by obtain ⟨T, hT, -, hroom, hown⟩ := lay; have := nums.ret8; omega)
        (by simp [eval, h.1.hcb, recordAt_off]), setQ0 s _ _ h (by decide) (by decide),
        by simp [setLocal, ← recordAt_off, hl.hsg]⟩
  have k1 : Frag o [SessionStore.keptIn (Syntax.v "sg") groupsMax] Q1 Q1 :=
    frag_keptIn o (e := Syntax.v "sg") rfl (by decide) cQ1 fun s h => ⟨sg, hl.hsgm, h.2⟩
  have hstop : Lower.lowerStmtsFold (SessionStore.stop brokenState) = some SessionRun.stopG := rfl
  have i1 : Frag o [SessionStore.ifs (Syntax.eEq (Syntax.v "sg") (Syntax.n 0)) (SessionStore.stop brokenState)] Q1 Q1 :=
    frag_oneR (a := .cond (.cmp .equal (.var "sg") (.const 0)) SessionRun.stopG .skip)
      (by simp [SessionStore.ifs, Lower.lowerStmt1, Lower.lowerExp, Syntax.eEq, Syntax.v, Syntax.n, hstop,
        Lower.lowerStmtsFold_nil]) rfl cQ1 fun R => WpRet.cond (fun s h => ⟨_, by simp [eval, h.2]; rfl⟩)
        (fun s ⟨h, hne⟩ => absurd hne (by
          simp only [eval, h.2]
          rw [if_neg (fun e => by have := NatToDec.ofNat64_inj (a := sg) (b := 0) (by omega) (by decide) e; omega)]
          simp)) (conseq (WpRet.skip o _ R) (fun s h => h.1) (fun _ _ h => h) (fun _ h => h))
  have hgpE : Lower.lowerExp (Syntax.eAdd (SessionStore.at_ (recOff + News.RecoverProg.rGroups))
      (Syntax.eMul (Syntax.eSub (Syntax.v "sg") (Syntax.n 1)) (Syntax.n News.RecoverProg.rGroupSlot))) =
      some (.op .add (.op .add .base (.const (BitVec.ofNat 64 (recOff + News.RecoverProg.rGroups))))
        (.mul (.op .sub (.var "sg") (.const (BitVec.ofNat 64 1))) (.const (BitVec.ofNat 64 News.RecoverProg.rGroupSlot)))) :=
    at_add_lower (Nat.ne_of_gt (Nat.lt_of_lt_of_le (show 0 < News.RecoverProg.rGroups by decide) (Nat.le_add_left _ _)))
      rfl
  have hsize : groupAt sg < 2 ^ 63 := by omega
  have d2 : Frag o [.dec "gp" (Syntax.eAdd (SessionStore.at_ (recOff + News.RecoverProg.rGroups))
      (Syntax.eMul (Syntax.eSub (Syntax.v "sg") (Syntax.n 1)) (Syntax.n News.RecoverProg.rGroupSlot)))] Q1 Q2 :=
    frag_dec o hgpE fun s h => ⟨b + BitVec.ofNat 64 (groupAt sg), by
      simp only [eval, h.1.1.base, h.2]
      rw [SessionCheck.sub_small sg 1 hl.hsg1 (by omega), ← BitVec.ofNat_mul, BitVec.add_assoc, ← BitVec.ofNat_add,
        groupAt], ⟨setQ0 s _ _ h.1 (by decide) (by decide), by simp [setLocal, h.2]⟩, by simp [setLocal]⟩
  have d3 : Frag o [.dec "gl" (SessionStore.ld (Syntax.v "gp"))] Q2 Q3 :=
    frag_dec o (E := .loadWord (.var "gp")) rfl fun s h => ⟨_, eval_word hpre.hb hpre.hc hpre.hcov h.1.1.1 gi3
      (by have := nums.own64; omega) (Nat.lt_of_lt_of_le (by omega) (group_in hl.hsg1 hl.hsgm).2.2.2)
      (Or.inr gi1) (by obtain ⟨T, hT, -, hroom, hown⟩ := lay; have := nums.ret8; omega) h.2,
      ⟨⟨setQ0 s _ _ h.1.1 (by decide) (by decide), by simp [setLocal, h.1.2]⟩, by simp [setLocal, h.2]⟩,
      by simp [setLocal, hl.hgl]⟩
  have k2 : Frag o [SessionStore.keptIn (Syntax.v "gl") groupMax] Q3 Q3 :=
    frag_keptIn o (e := Syntax.v "gl") rfl (by decide) cQ3 fun s h => ⟨gn.length, hgm, h.2⟩
  have k3 : Frag o [SessionStore.keptIn (Syntax.v "o") (data - groupMax - 2)] Q3 Q3 :=
    frag_keptIn o (e := Syntax.v "o") rfl (by rw [hd]; decide) cQ3 fun s h =>
      ⟨a4.length, by rw [hd]; simp only [groupMax]; omega, h.1.1.1.2.1⟩
  have hgo : ownOff + ownRet + 8 ≤ groupAt sg + 8 := by
    have a1 : ownOff + ownRet + 8 ≤ ownOff + ownTexts := by rw [Nat.add_assoc]; exact Nat.add_le_add_left hr8 _
    have a2 : ownOff + ownTexts ≤ tOff := by rw [hT]; exact hown
    exact Nat.le_trans a1 (Nat.le_trans a2 (Nat.le_trans (Nat.le_add_right _ 173568)
      (Nat.le_trans gi1 (Nat.le_add_right _ 8))))
  have h6 := appendFrom_frag o hpre.hb hpre.hc hpre.hcov (P := Q3) (acc := a4) (bs := gn) (X := groupAt sg + 8)
    (src := Syntax.atOff (Syntax.v "gp") 8) (len := Syntax.v "gl") (SRC := .op .add (.var "gp") (.const 8))
    (by simp [Syntax.atOff, Lower.lowerExp, Syntax.eAdd, Syntax.n, Syntax.v]) rfl
    ⟨⟨trivial, trivial⟩, by simp [ExpAvoids]⟩ ⟨trivial, by simp [ExpAvoids], by simp [ExpAvoids]⟩
    (fun s h => ⟨h.1.1.1.1, h.1.1.1.2, by simp [eval, h.1.2, add_ofNat], h.2⟩) hl.hg
    (Or.inr (Nat.le_trans gi1 (Nat.le_add_right _ _)))
    (Nat.lt_of_le_of_lt (Nat.add_le_add_left hgm _) gi2)
    (Or.inr hgo) (by have := Nat.add_le_add ha4 hgm; rw [hgm'] at this; rw [hd]; exact Nat.le_trans this (by decide))
  have h7 := appendText_frag o hpre.hb (t := t) (rl := rl) (sl := sl) (acc := a4 ++ gn) (k := tCrlf) hpre.hc
    hpre.hcov hpre.hid.texts (by rw [texts_length]; decide)
    (by simp only [textLen, List.length_append, len_crlf]; omega)
  have hblk := frag_append d1 (frag_append k1 (frag_append i1 (frag_append d2 (frag_append d3 (frag_append k2 k3)))))
  have h67 := frag_append h6 (frag_append h7 (fun k _ _ _ hk => ⟨k, rfl, hk⟩ : Frag o [] _ _))
  rw [List.append_assoc] at h67
  have hf := frag_append h1 (frag_append h2 (frag_append h3 (frag_append h4 (frag_append hblk h67))))
  have e : listedBytes count low high gn = a4 ++ gn ++ texts.getD tCrlf [] := by
    simp [listedBytes, ha4d]
  rw [e]
  exact tw_close hf (by decide +kernel) R

/-! ### DATE's branch -/

/-- The article area's powers of two: word `j` of its table is `2^j`. -/
def PowIn (b : Word) (m : Word → Word) : Prop :=
  ∀ j, j < 64 → m (b + BitVec.ofNat 64 (News.AbnfProg.areaOffset + News.AbnfProg.aPow + 8 * j)) = BitVec.ofNat 64 (2 ^ j)

/-- The powers of two lie below the connections' records, so `dateText` keeps them. -/
theorem pow_keep {b : Word} (hb : b.toNat % 8 = 0) {c : Nat} (hc : c < conns) {m m0 : Word → Word}
    (hm : ∀ w, ¬ OutWord b c w → w ≠ SessionCheck.retW b → m w = m0 w) (h : PowIn b m0) : PowIn b m :=
    fun j hj => by
  obtain ⟨T, hT, -, hend, hown⟩ := lay
  have hp : News.AbnfProg.areaOffset + News.AbnfProg.aPow + 8 * 64 ≤ ownOff ∧
      (News.AbnfProg.areaOffset + News.AbnfProg.aPow) % 8 = 0 := by decide
  have e := byteAlign_of_aligned hb (X := News.AbnfProg.areaOffset + News.AbnfProg.aPow + 8 * j) (by omega)
  have hr : ownOff + ownRet < 2 ^ 63 := by have := nums.ret8; omega
  rw [hm _ (e ▸ below_table hb hc (by rw [hT]; omega)) (region_addr_inj b _ _ (by omega) (by omega) (by omega))]
  exact h j hj

/-- What `dateText` gives back if it returns, called at place `ofs` of connection `c`'s output. Zero, and the octets `d`
from `ofs`; the place past them in the return word. Every other octet and word as `m0` has them. -/
def DateRet (b : Word) (c ofs : Nat) (d : List (BitVec 8)) (dm : Word → Bool) (be : Bool) (m0 : Word → Word) : Ret :=
  fun v m => v = 0 ∧ memBytesAt m dm be (outAt b c + BitVec.ofNat 64 ofs) d ∧
    m (SessionCheck.retW b) = BitVec.ofNat 64 (ofs + d.length) ∧
    (∀ a, (∀ i, i < d.length → a ≠ outAt b c + BitVec.ofNat 64 ofs + BitVec.ofNat 64 i) →
      byteAlign a ≠ SessionCheck.retW b → memLoadByte m dm be a = memLoadByte m0 dm be a) ∧
    (∀ w, ¬ OutWord b c w → w ≠ SessionCheck.retW b → m w = m0 w)

/-- `dateText`'s entry: connection `c` and the place `ofs` in its parameters, the session's words with the wall
clock's seconds `secs`. -/
structure DEntry (b : Word) (c ofs secs : Nat) (s : PancakeState σ) : Prop where
  hb : b.toNat % 8 = 0
  hcc : c < conns
  hcov : Analyzer.Covers SessionLayout.size s.memaddrs b
  hc : s.locals "c" = some (BitVec.ofNat 64 c)
  ho : s.locals "o" = some (BitVec.ofNat 64 ofs)
  base : s.baseAddr = b
  hwall : s.memory (b + BitVec.ofNat 64 (ownOff + ownWall)) = BitVec.ofNat 64 secs
  hpow : PowIn b s.memory

/-- DATE's digits of the seconds `secs`: `SessionSpec.dateDigits` of as many milliseconds. -/
def dateBytes (secs : Nat) : List (BitVec 8) := News.SessionSpec.dateDigits (secs * 1000)

/-- They are the wall clock's when `secs` are its whole seconds. -/
theorem dateBytes_wall (w : Nat) : dateBytes (w / 1000) = News.SessionSpec.dateDigits w := by
  simp only [dateBytes, News.SessionSpec.dateDigits, Nat.mul_div_cancel _ (by decide : 0 < 1000)]

/-- `dateText` as the code holds it: from a place up to 8, if it returns, giving back `secs`'s digits. -/
def DateOk (o : Oracle σ) (b : Word) (secs : Nat) (code : String → Option (List String × PancakeProg)) : Prop :=
  ∃ body, code "dateText" = some (["c", "o"], body) ∧ ∀ c ofs (s1 : PancakeState σ), DEntry b c ofs secs s1 →
    s1.code = code → ofs ≤ 8 →
    SafeR o (fun s => s = s1) body (DateRet b c ofs (dateBytes secs) s1.memaddrs s1.be s1.memory) (fun _ => False)

/-- DATE's octets: the text before, the date and time, CRLF. -/
def timeBytes (d : List (BitVec 8)) : List (BitVec 8) := texts.getD tTime [] ++ d ++ texts.getD tCrlf []

/-- **DATE's branch** writes its octets, `dateText` writing the date and time. -/
theorem time_body (o : Oracle σ) {b : Word} {c t : Nat} {i : CommandSpec.Identity} {s0 : PancakeState σ}
    (hpre : TextPre b c i s0) {secs : Nat} {d : List (BitVec 8)}
    (hwall : s0.memory (b + BitVec.ofNat 64 (ownOff + ownWall)) = BitVec.ofNat 64 secs) (hpow : PowIn b s0.memory)
    (hdate : DateOk o b secs s0.code) (hd : dateBytes secs = d) (hdl : d.length ≤ 60) (R : Ret) :
    ∃ c', Lower.lowerStmtsFold Branch.time.body = some c' ∧
      SafeR o (fun s => TCtx b c t i.revision.length i.source.length s0 s ∧ Wrote b c [] s) c' R
        (fun s => TCtx b c t i.revision.length i.source.length s0 s ∧ Wrote b c (timeBytes d) s) := by
  obtain ⟨T, hT, h8, hend, hown⟩ := lay
  obtain ⟨-, -, -, hdd, hn, h64⟩ := nums
  obtain ⟨body, hcode, hsafe⟩ := hdate
  rw [hd] at hsafe
  have hcc := hpre.hc
  rw [hn] at hcc
  obtain ⟨a1, ha1d⟩ : ∃ a : List (BitVec 8), a = [] ++ texts.getD tTime [] := ⟨_, rfl⟩
  have ha1 : a1.length = 4 := by
    rw [ha1d]; simp only [List.nil_append, len_time]
  have hwr : ownOff + ownWall ≠ ownOff + ownRet ∧ (ownOff + ownWall) % 8 = 0 ∧ ownOff + ownWall < tOff := by
    have : ownWall + 8 = ownRet ∧ ownOff % 8 = 0 ∧ ownWall % 8 = 0 ∧ ownRet + 8 ≤ ownTexts := by decide
    rw [hT]; omega
  have h1 := appendText_frag o hpre.hb (t := t) (rl := i.revision.length) (sl := i.source.length) (acc := [])
    (k := tTime) hpre.hc hpre.hcov hpre.hid.texts (by rw [texts_length]; decide)
    (by simp only [textLen, List.length_nil, len_time]; omega)
  rw [← ha1d] at h1
  let P2 : Assn σ := fun s => TCtx b c t i.revision.length i.source.length s0 s ∧
    s.locals "o" = some (BitVec.ofNat 64 a1.length) ∧ memBytesAt s.memory s.memaddrs s.be (outAt b c) (a1 ++ d) ∧
    s.memory (SessionCheck.retW b) = BitVec.ofNat 64 (a1.length + d.length) ∧ s.locals "dt" = some 0
  have cP2 : Safe.ClockFree P2 := fun s k ⟨h, rest⟩ => ⟨h.clock k, rest⟩
  have hcall : Frag o [.call "dt" "dateText" [Syntax.v "c", Syntax.v "o"]]
      (fun s => TCtx b c t i.revision.length i.source.length s0 s ∧ Wrote b c a1 s) P2 := by
    refine frag_call o (args := [.var "c", .var "o"]) rfl (body := body)
      (Pc := fun s s1 => s1 = { decClock s with locals := fun k => (["c", "o"].zip
        [BitVec.ofNat 64 c, BitVec.ofNat 64 a1.length]).lookup k })
      (Rc := fun s => DateRet b c a1.length d s.memaddrs s.be s.memory) (fun s ⟨hx, hw⟩ => ?_)
      (fun s ⟨hx, hw⟩ => ⟨[BitVec.ofNat 64 c, BitVec.ofNat 64 a1.length], _, by simp [evalArgs, eval, hx.hc, hw.1],
        Block.lookupCode_of (by rw [hx.code]; exact hcode) (by decide) rfl, rfl⟩) (fun s u v ⟨hx, hw⟩ hR hsame => ?_)
    · exact hsafe c a1.length _ ⟨hpre.hb, hpre.hc, (hx.memaddrs ▸ hpre.hcov :), rfl, rfl, hx.base,
        (own_word hpre.hb hpre.hc hx hwr.2.1 hwr.2.2 hwr.1).trans hwall,
        pow_keep hpre.hb hpre.hc hx.words hpow⟩ hx.code (by omega)
    · obtain ⟨hv, hput, hret, hbytes, hwords⟩ := hR
      refine ⟨⟨by simp [setLocal, hx.hc], by simp [setLocal, hx.ht], by simp [setLocal, hx.hcb],
        by simp [setLocal, hx.hob], by obtain ⟨w, hw'⟩ := hx.hj; exact ⟨w, by simp [setLocal, hw']⟩,
        by simp [setLocal, hx.hrl], by simp [setLocal, hx.hsl], hsame.2.1.trans hx.base,
        hsame.1.trans hx.memaddrs, hsame.2.2.1.trans hx.be, hsame.2.2.2.trans hx.code,
        fun w hw1 hw2 => (hwords w hw1 hw2).trans (hx.words w hw1 hw2)⟩, by simp [setLocal, hw.1], ?_, hret,
        by simp [setLocal, hv]⟩
      simp only [hsame.1, hsame.2.2.1]
      refine memBytesAt_append (fun j hj => ?_) hput
      rw [hbytes _ (fun k hk e => ?_) (fun e => retW_out hpre.hb hpre.hc ?_)]
      · exact hw.2 j hj
      · rw [outAt_off, add_ofNat, add_ofNat, add_ofNat] at e
        exact region_addr_inj b _ _ (by omega) (by omega) (by omega) e
      · exact e ▸ ⟨j, by have := hw.2; omega, rfl⟩
  -- the call's result checked, the place past the date, CRLF
  have hdt : Frag o [.ite (Syntax.v "dt") [.ret (Syntax.v "dt")] []] P2 P2 :=
    frag_oneR (a := .cond (.var "dt") (.ret (.var "dt")) .skip) rfl rfl cP2 fun R =>
      WpRet.cond (fun s h => ⟨_, h.2.2.2.2⟩) (fun s ⟨h, hne⟩ => absurd h.2.2.2.2 (by simpa [eval] using hne))
        (conseq (WpRet.skip o _ R) (fun s h => h.1) (fun _ _ h => h) (fun _ h => h))
  have hro := ret_in
  have hfo : Frag o [.assign "o" SessionStore.found]
      P2 (fun s => TCtx b c t i.revision.length i.source.length s0 s ∧ Wrote b c (a1 ++ d) s) :=
    frag_one (a := .assign "o" (.loadWord (.op .add .base (.const (BitVec.ofNat 64 (ownOff + ownRet))))))
      (by simp [Lower.lowerStmt1, SessionStore.found, SessionStore.ld, Lower.lowerExp, at_lower hro.2.2.2]) rfl rfl
      (tw_clock b c t _ _ s0 _) (Safe.assign fun s ⟨hx, ho, hput, hret, _⟩ =>
      ⟨BitVec.ofNat 64 (a1 ++ d).length, _, by
        have hA := own_addr hpre.hcov hro.1 hro.2.1 hro.2.2.1
        simp only [eval, hx.base, hx.memaddrs]
        rw [show b + BitVec.ofNat 64 (ownOff + ownRet) = SessionCheck.retW b from rfl, hret, List.length_append]
        rw [show b + BitVec.ofNat 64 (ownOff + ownRet) = SessionCheck.retW b from rfl] at hA
        simp [hA],
        ho, hx.set (by decide) _, by simp [setLocal], hput⟩)
  have hl2 : textLen tCrlf = 2 := len_crlf
  have hk : Frag o [SessionStore.keptIn (Syntax.v "o") (data - textLen tCrlf)]
      (fun s => TCtx b c t i.revision.length i.source.length s0 s ∧ Wrote b c (a1 ++ d) s)
      (fun s => TCtx b c t i.revision.length i.source.length s0 s ∧ Wrote b c (a1 ++ d) s) :=
    frag_keptIn o (e := Syntax.v "o") rfl (by rw [hdd, hl2]; decide) (tw_clock b c t _ _ s0 _)
      fun s h => ⟨(a1 ++ d).length, by rw [hdd, hl2, List.length_append]; omega, h.2.1⟩
  have h7 := appendText_frag o hpre.hb (t := t) (rl := i.revision.length) (sl := i.source.length) (acc := a1 ++ d)
    (k := tCrlf) hpre.hc hpre.hcov hpre.hid.texts (by rw [texts_length]; decide)
    (by rw [hl2, List.length_append]; omega)
  have hf := frag_append h1 (frag_append hcall (frag_append hdt (frag_append hfo (frag_append hk
    (frag_append h7 (fun k _ _ _ hk => ⟨k, rfl, hk⟩ : Frag o [] _ _))))))
  simp only [List.append_nil] at hf
  have e : timeBytes d = a1 ++ d ++ texts.getD tCrlf [] := by simp [timeBytes, ha1d]
  rw [e]
  exact tw_close hf (by decide +kernel) R

/-! ### The replies `connText` writes -/

/-- The parts of a branch made of them, else none. -/
def Branch.partsOf : Branch → List Part
  | .parts ps => ps
  | _ => []

def Branch.isParts : Branch → Bool
  | .parts _ => true
  | _ => false

def Part.okB : Part → Bool
  | .text k => k < texts.length
  | _ => true

/-- The replies whose text is the identity's and the session's texts, and the branch writing each. -/
def fixedBranches : List (CommandSpec.Reply × Nat) :=
  [(.capabilities, 2), (.capabilitiesPost, 3), (.capabilitiesReader, 4), (.capabilitiesAuth, 5),
   (.capabilitiesReaderAuth, 6), (.capabilitiesPostAuth, 7), (.help, 8), (.helpPost, 9), (.active none, 11),
   (.newsgroups, 12), (.newGroups, 13), (.quit, 16), (.noGroup, 17), (.noSuchId, 18), (.unknown, 19),
   (.syntax, 20), (.post, 21), (.posted, 22), (.failed, 23), (.notPermitted, 24), (.unavailable, 25),
   (.unreadable, 26), (.noSuchGroup, 27), (.noCurrent, 28), (.noNext, 29), (.noPrevious, 30), (.noNumber, 31),
   (.modeReader, 32), (.readerPosting, 33), (.readerNoPosting, 34), (.noneOver, 35), (.noneHdr, 36),
   (.noRange, 37), (.fieldRefused, 38), (.overviewFmt, 39), (.headerList, 40), (.authUser [], 41),
   (.authAccepted, 42), (.authFailed, 43), (.authSequence, 44), (.encryptionRequired, 45), (.authDone, 46),
   (.authRequired, 47)]

/-- What the table of branches gives each of them, computed once. -/
theorem fixed_table : ∀ p ∈ fixedBranches, p.2 < 48 ∧ (textKinds.getD p.2 (.parts [])).isParts = true ∧
    ((textKinds.getD p.2 (.parts [])).partsOf.all Part.okB) = true ∧ CommandSpec.Reply.bounded p.1 = true ∧
    Session.replyCode p.1 < 2 ^ 32 ∧
    Session.replyCode p.1 ∈ textCodes.getD p.2 [] ∧ (∀ l ∈ textCodes.take p.2, Session.replyCode p.1 ∉ l) ∧
    ∀ l ∈ textCodes.drop (p.2 + 1), Session.replyCode p.1 ∉ l := by
  decide +kernel

/-- …and their octets. -/
theorem fixed_bytes (i : CommandSpec.Identity) : ∀ p ∈ fixedBranches,
    CommandSpec.text i p.1 = ((textKinds.getD p.2 (.parts [])).partsOf.map (Part.bytes i)).flatten := by
  intro p hp
  simp only [fixedBranches, List.mem_cons, List.mem_nil_iff, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [textKinds, textOnly, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.getD_cons_succ,
      List.getD_cons_zero, Branch.partsOf, Part.bytes, List.flatten_cons, List.flatten_nil, List.append_nil] <;>
    simp only [Session.tCapabilitiesHead,
      Session.tBlockEnd, Session.tHelpHead, Session.tHelpMid, Session.tQuit, Session.tNoGroup,
      Session.tNoSuchId, Session.tUnknown, Session.tSyntax,
      Session.tCapabilitiesPostTail, Session.tHelpPostHead, Session.tPost, Session.tPosted, Session.tFailed,
      Session.tNotPermitted, Session.tUnavailable, Session.tNoSuchGroup, Session.tNoCurrent, Session.tNoNext,
      Session.tNoPrevious, Session.tNoNumber, Session.tActiveHead, Session.tNoDescriptions,
      Session.tNoNewGroups, Session.tCapabilitiesReaderTail, Session.tModeReader, Session.tReaderPosting,
      Session.tReaderNoPosting, Session.tNoneOver, Session.tNoneHdr, Session.tNoRange, Session.tFieldRefused,
      Session.tOverviewFmtText, Session.tHeaderList, Session.tCapabilitiesAuthTail, Session.tAuthUser,
      Session.tAuthAccepted, Session.tAuthFailed, Session.tAuthSequence, Session.tEncryptionRequired,
      Session.tAuthDone, Session.tAuthRequired, SessionStore.tUnreadable] <;> simp only [texts,
      List.getD_cons_succ, List.getD_cons_zero, CommandSpec.text, List.append_assoc]

/-- **`connText` writes the text of a reply of the identity and the session's texts**, if it returns. That is
`CommandSpec.text`, into connection `c`'s output. -/
theorem connText_fixed (o : Oracle σ) {b : Word} {c : Nat} {i : CommandSpec.Identity} {s0 : PancakeState σ}
    (hpre : TextPre b c i s0) {r : CommandSpec.Reply} {j : Nat} (hrj : (r, j) ∈ fixedBranches) :
    ∃ k, Lower.lowerStmtsFold Session.connText.body = some k ∧
      SafeR o (TEntry b c (Session.replyCode r) s0) k (TextRet b c (CommandSpec.text i r) s0.memaddrs s0.be s0.memory)
        (fun _ => False) := by
  obtain ⟨hj, hparts, hok, hbd, hcode, hin, hpre', hpost⟩ := fixed_table _ hrj
  have hb := fixed_bytes i _ hrj
  simp only at hj hparts hok hbd hcode hin hpre' hpost hb
  obtain ⟨ps, hps⟩ : ∃ ps, textKinds.getD j (.parts []) = .parts ps := by
    revert hparts; cases textKinds.getD j (.parts []) <;> simp [Branch.isParts]
  rw [hps] at hok hb
  have hroom := CommandSpec.text_fits i hpre.hok r hbd
  rw [hb] at hroom ⊢
  have hl := textBranches_length
  exact connText_parts o hpre hcode j (by omega) hps hin hpre' hpost
    (fun p hp => by have := List.all_eq_true.mp hok p hp; cases p <;> simp_all [Part.okB, Part.ok])
    (by simpa [CommandSpec.actionData, nums.dataLen] using hroom)

/-- A branch other than one of parts, by its place: its codes apart from the others', computed once. -/
theorem other_table : ∀ j ∈ [0, 1, 10, 14, 15], j < 48 ∧ (∀ t ∈ textCodes.getD j [], t < 2 ^ 32 ∧
    (∀ l ∈ textCodes.take j, t ∉ l) ∧ ∀ l ∈ textCodes.drop (j + 1), t ∉ l) := by
  decide +kernel

theorem connText_other (o : Oracle σ) {b : Word} {c t : Nat} {i : CommandSpec.Identity} {s0 : PancakeState σ}
    (hpre : TextPre b c i s0) {j : Nat} (hjt : j ∈ [0, 1, 10, 14, 15]) (ht : t ∈ textCodes.getD j [])
    {bs : List (BitVec 8)} (hroom : bs.length ≤ data)
    (hbody : ∀ R, ∃ c', Lower.lowerStmtsFold (textKinds.getD j (.parts [])).body = some c' ∧
      SafeR o (fun s => TCtx b c t i.revision.length i.source.length s0 s ∧ Wrote b c [] s) c' R
        (fun s => TCtx b c t i.revision.length i.source.length s0 s ∧ Wrote b c bs s)) :
    ∃ k, Lower.lowerStmtsFold Session.connText.body = some k ∧
      SafeR o (TEntry b c t s0) k (TextRet b c bs s0.memaddrs s0.be s0.memory) (fun _ => False) := by
  obtain ⟨hj, hcs⟩ := other_table j hjt
  obtain ⟨h32, hpre', hpost⟩ := hcs t ht
  have hl := textBranches_length
  exact connText_branch o hpre h32 hroom j
      (by omega) ht hpre' hpost fun R => by rw [body_at j (by omega)]; exact hbody R

/-- **The greetings**, if it returns. -/
theorem connText_greeting (o : Oracle σ) {b : Word} {c : Nat} {i : CommandSpec.Identity} {s0 : PancakeState σ}
    (hpre : TextPre b c i s0) :
    (∃ k, Lower.lowerStmtsFold Session.connText.body = some k ∧ SafeR o (TEntry b c Session.greetCode s0) k
      (TextRet b c (CommandSpec.greeting i) s0.memaddrs s0.be s0.memory) (fun _ => False)) ∧
    ∃ k, Lower.lowerStmtsFold Session.connText.body = some k ∧ SafeR o (TEntry b c Session.greetPostCode s0) k
      (TextRet b c (CommandSpec.greetingPost i) s0.memaddrs s0.be s0.memory) (fun _ => False) := by
  have hf := CommandSpec.greeting_fits i hpre.hok
  have hd : data = CommandSpec.actionData := by decide
  have e1 : CommandSpec.greeting i = ([Part.text tGreetingHead, .rev, .text tGreetingMid, .src, .text tCrlf].map
      (Part.bytes i)).flatten := by
    simp [Part.bytes, CommandSpec.greeting, get_greeting.1, get_greeting.2.1, get_crlf, List.append_assoc,
        -List.getD_eq_getElem?_getD]
  have e2 : CommandSpec.greetingPost i = ([Part.text tGreetingPostHead, .rev, .text tGreetingPostMid, .src,
      .text tCrlf].map (Part.bytes i)).flatten := by
    simp [Part.bytes, CommandSpec.greetingPost, get_greeting.2.2.1, get_greeting.2.2.2, get_crlf, List.append_assoc,
        -List.getD_eq_getElem?_getD]
  refine ⟨?_, ?_⟩
  · rw [e1]
    exact connText_parts o hpre (by decide) 0 (by decide) rfl (by decide +kernel) (by decide +kernel)
      (by decide +kernel)
      (fun p hp => by
        have hall : ([Part.text tGreetingHead, .rev, .text tGreetingMid, .src, .text tCrlf].all Part.okB) = true := by
          decide +kernel
        have := List.all_eq_true.mp hall p hp
        cases p <;> simp_all [Part.okB, Part.ok]) (by rw [← e1, hd]; exact hf.1)
  · rw [e2]
    exact connText_parts o hpre (by decide) 1 (by decide) rfl (by decide +kernel) (by decide +kernel)
      (by decide +kernel)
      (fun p hp => by
        have hall : ([Part.text tGreetingPostHead, .rev, .text tGreetingPostMid, .src, .text tCrlf].all Part.okB) =
            true := by decide +kernel
        have := List.all_eq_true.mp hall p hp
        cases p <;> simp_all [Part.okB, Part.ok]) (by rw [← e2, hd]; exact hf.2)

/-- **STAT's reply**, if it returns. -/
theorem connText_stat (o : Oracle σ) {b : Word} {c : Nat} {i : CommandSpec.Identity} {s0 : PancakeState σ}
    (hpre : TextPre b c i s0) {n : Nat} {id : List (BitVec 8)} (hs : StatIn b n id s0) :
    ∃ k, Lower.lowerStmtsFold Session.connText.body = some k ∧
      SafeR o (TEntry b c (Session.replyCode (.stat n id)) s0) k
        (TextRet b c (CommandSpec.text i (.stat n id)) s0.memaddrs s0.be s0.memory) (fun _ => False) := by
  have e : CommandSpec.text i (.stat n id) = statBytes n id := by
    simp [CommandSpec.text, statBytes, get_stat, get_crlf, CommandSpec.SP, List.append_assoc,
        -List.getD_eq_getElem?_getD]
  have hN := numDigits_le_ten n hs.hsmall
  have hl := decimal_length n
  have hroom : (statBytes n id).length ≤ data := by
    have := hs.hidMax
    simp only [statBytes, List.length_append, List.length_singleton, len_stat, len_crlf, nums.dataLen]
    omega
  rw [e]
  exact connText_other o hpre (j := 10) (by decide) (by simp only [Session.replyCode]; decide) hroom
    fun R => stat_body o hpre hs hroom R

/-- **GROUP's and LISTGROUP's reply**, if it returns. -/
theorem connText_listed (o : Oracle σ) {b : Word} {c : Nat} {i : CommandSpec.Identity} {s0 : PancakeState σ}
    (hpre : TextPre b c i s0) {count low high sg : Nat} {gn : List (BitVec 8)}
    (hl : ListedIn b c count low high sg gn s0) {r : CommandSpec.Reply}
    (hr : r = .selected count low high gn ∨ ∃ lo hi, r = .listed count low high gn lo hi) :
    ∃ k, Lower.lowerStmtsFold Session.connText.body = some k ∧
      SafeR o (TEntry b c (Session.replyCode r) s0) k
        (TextRet b c (CommandSpec.text i r) s0.memaddrs s0.be s0.memory) (fun _ => False) := by
  have e : CommandSpec.text i r = listedBytes count low high gn := by
    rcases hr with rfl | ⟨lo, hi, rfl⟩ <;>
      simp [CommandSpec.text, listedBytes, get_selected, get_crlf, CommandSpec.SP, List.append_assoc,
          -List.getD_eq_getElem?_getD]
  obtain ⟨hcs, hls, hhs⟩ := hl.hsmall
  have := numDigits_le_ten count hcs
  have := numDigits_le_ten low hls
  have := numDigits_le_ten high hhs
  have := decimal_length count
  have := decimal_length low
  have := decimal_length high
  have := hl.hgm
  have hroom : (listedBytes count low high gn).length ≤ data := by
    simp only [listedBytes, List.length_append, List.length_singleton, len_selected, len_crlf, nums.dataLen,
      show groupMax = 64 from rfl] at *
    omega
  have hc : Session.replyCode r ∈ textCodes.getD 15 [] := by
    rcases hr with rfl | ⟨lo, hi, rfl⟩ <;> simp only [Session.replyCode] <;> decide
  rw [e]
  exact connText_other o hpre (j := 15) (by decide) hc hroom fun R => listed_body o hpre hl R

/-- **DATE's reply**, if it returns: `dateText` as the code holds it writes the date and time of wall seconds `secs`. -/
theorem connText_time (o : Oracle σ) {b : Word} {c : Nat} {i : CommandSpec.Identity} {s0 : PancakeState σ}
    (hpre : TextPre b c i s0) {secs : Nat}
    (hwall : s0.memory (b + BitVec.ofNat 64 (ownOff + ownWall)) = BitVec.ofNat 64 secs) (hpow : PowIn b s0.memory)
    (hdate : DateOk o b secs s0.code) (hdl : (dateBytes secs).length ≤ 60) :
    ∃ k, Lower.lowerStmtsFold Session.connText.body = some k ∧
      SafeR o (TEntry b c (Session.replyCode (.time (dateBytes secs))) s0) k
        (TextRet b c (CommandSpec.text i (.time (dateBytes secs))) s0.memaddrs s0.be s0.memory) (fun _ => False) := by
  generalize hd : dateBytes secs = d at hdl ⊢
  have e : CommandSpec.text i (.time d) = timeBytes d := by
    simp [CommandSpec.text, timeBytes, get_time, get_crlf, List.append_assoc, -List.getD_eq_getElem?_getD]
  have hroom : (timeBytes d).length ≤ data := by
    simp only [timeBytes, List.length_append, len_time,
      len_crlf, nums.dataLen]
    omega
  rw [e]
  exact connText_other o hpre (j := 14) (by decide) (by simp only [Session.replyCode]; decide) hroom
    fun R => time_body o hpre hwall hpow hdate hd hdl R

/-! ### The premises can hold -/

/-- The powers' table's place. -/
abbrev powOff : Nat := News.AbnfProg.areaOffset + News.AbnfProg.aPow

/-- The witnesses' wall clock: 2001-09-09 01:46:40 UTC. -/
def wSecs : Nat := 1000000000

/-- The words the witnesses set, by place past the base. One at the identity's, Message-ID's and group name's lengths,
the lowest number, connection zero's group. Three at the count and highest number, seven at the article's number; the
wall seconds; the powers of two. -/
def wMem0 (w : Word) : Word :=
  let d := (w - wb).toNat
  if d = ownOff + ownRevLen ∨ d = ownOff + ownSrcLen ∨ d = ownOff + ownIdLen ∨ d = ownOff + ownLow ∨
      d = tOff + cGroup ∨ d = groupAt 1 then 1
  else if d = ownOff + ownCount ∨ d = ownOff + ownHigh then 3
  else if d = ownOff + ownNum then 7
  else if d = ownOff + ownWall then BitVec.ofNat 64 wSecs
  else if powOff ≤ d ∧ d < powOff + 512 ∧ (d - powOff) % 8 = 0 then BitVec.ofNat 64 (2 ^ ((d - powOff) / 8))
  else 0

/-- …with the texts, and `1` as the revision, the source, the Message-ID and group one's name. -/
def wMem : Word → Word :=
  putAll (putAll (putAll (putAll (putAll wMem0 false (wb + BitVec.ofNat 64 (ownOff + ownTexts)) 0 texts.flatten)
    false (wb + BitVec.ofNat 64 (ownOff + ownRev)) 0 [49#8]) false (wb + BitVec.ofNat 64 (ownOff + ownSrc)) 0 [49#8])
    false (wb + BitVec.ofNat 64 (ownOff + ownId)) 0 [49#8]) false (wb + BitVec.ofNat 64 (groupAt 1 + 8)) 0 [49#8]

def wId : CommandSpec.Identity := ⟨[49#8], [49#8]⟩

def wLocals (x : String) : Option Word :=
  if x = "cb" then some (SessionFrame.recordAt wb 0) else if x = "ob" then some (outAt wb 0)
  else if x = "rl" ∨ x = "sl" then some 1 else if x = "c" ∨ x = "t" ∨ x = "o" ∨ x = "j" then some 0 else none

/-- The session's words at connection zero's `connText`. -/
def wState : PancakeState Unit :=
  { bareState () with
    memory := wMem
    memaddrs := Analyzer.heapWords wb SessionLayout.size
    baseAddr := wb
    locals := wLocals }

/-- The witnesses' places, computed once. -/
structure WVals : Prop where
  own : ownOff = 1032568
  revLen : ownRevLen = 24
  srcLen : ownSrcLen = 96
  rev : ownRev = 32
  src : ownSrc = 104
  texts : ownTexts = 6408
  num : ownNum = 6200
  count : ownCount = 6176
  low : ownLow = 6184
  high : ownHigh = 6192
  wall : ownWall = 344
  idLen : ownIdLen = 2472
  id : ownId = 2480
  group : cGroup = 160
  pow : powOff + 512 ≤ 1032568
  powAl : powOff % 8 = 0
  pow64 : 64 ≤ powOff

theorem w_vals : WVals := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17⟩ :
      ownOff = 1032568 ∧ ownRevLen = 24 ∧ ownSrcLen = 96 ∧ ownRev = 32 ∧ ownSrc = 104 ∧ ownTexts = 6408 ∧
      ownNum = 6200 ∧ ownCount = 6176 ∧ ownLow = 6184 ∧ ownHigh = 6192 ∧ ownWall = 344 ∧ ownIdLen = 2472 ∧
      ownId = 2480 ∧ cGroup = 160 ∧ powOff + 512 ≤ 1032568 ∧ powOff % 8 = 0 ∧ 64 ≤ powOff := by decide +kernel
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17⟩

/-- Where the texts, the records and group one lie. -/
structure WEnds : Prop where
  textsEnd : ownOff + ownTexts + textAt texts.length ≤ tOff
  group : tOff + 173568 ≤ groupAt 1
  groupAl : groupAt 1 % 8 = 0
  groupIn : groupAt 1 + 72 ≤ SessionLayout.size
  sizeLe : SessionLayout.size ≤ 4194304
  tAl : tOff % 8 = 0
  textsIn : ownOff + ownTexts + textAt texts.length ≤ 4194304

theorem w_ends : WEnds := by
  have h2 := group_in (sg := 1) (Nat.le_refl _) (by decide)
  have := size_fits
  have : heapBytes = 4194304 := by decide +kernel
  have : groupMax = 64 := rfl
  have h3 := texts_end
  refine ⟨h3, h2.1, h2.2.2.1, by omega, by omega, table_aligned, ?_⟩
  generalize tOff = T at *
  omega

theorem w_cov : Analyzer.Covers SessionLayout.size wState.memaddrs wb := by
  have := size_fits
  have : heapBytes = 4194304 := by decide +kernel
  exact Analyzer.covers_heap _ (Nat.le_refl _) (by decide) (by simp [wb]; omega)

theorem wMem0_at {Y : Nat} (hY : Y < 2 ^ 63) : wMem0 (wb + BitVec.ofNat 64 Y) =
    if Y = ownOff + ownRevLen ∨ Y = ownOff + ownSrcLen ∨ Y = ownOff + ownIdLen ∨ Y = ownOff + ownLow ∨
        Y = tOff + cGroup ∨ Y = groupAt 1 then 1
    else if Y = ownOff + ownCount ∨ Y = ownOff + ownHigh then 3
    else if Y = ownOff + ownNum then 7
    else if Y = ownOff + ownWall then BitVec.ofNat 64 wSecs
    else if powOff ≤ Y ∧ Y < powOff + 512 ∧ (Y - powOff) % 8 = 0 then BitVec.ofNat 64 (2 ^ ((Y - powOff) / 8))
    else 0 := by
  simp only [wMem0, wb_off Y hY]

/-- A word apart from the octets stored, as `wMem0` has it. -/
theorem wMem_word {Y : Nat} (hY : Y % 8 = 0) (hYs : Y + 8 ≤ SessionLayout.size)
    (hT : Y + 8 ≤ ownOff + ownTexts ∨ ownOff + ownTexts + textAt texts.length ≤ Y) (hR : Y ≠ ownOff + ownRev)
    (hS : Y ≠ ownOff + ownSrc) (hI : Y ≠ ownOff + ownId) (hG : Y ≠ groupAt 1 + 8) :
    wMem (wb + BitVec.ofNat 64 Y) = wMem0 (wb + BitVec.ofNat 64 Y) := by
  have v := w_vals
  have hs := w_ends.sizeLe
  have hg := w_ends.groupAl
  have hgi := w_ends.groupIn
  have hl := texts_len
  have ht := w_ends.textsIn
  have := v.own; have := v.rev; have := v.src; have := v.texts; have := v.id
  unfold wMem
  rw [putAll_far wb_aligned _ hY (by simp; omega) (by omega) (by simp; omega),
    putAll_far wb_aligned _ hY (by simp; omega) (by omega) (by simp; omega),
    putAll_far wb_aligned _ hY (by simp; omega) (by omega) (by simp; omega),
    putAll_far wb_aligned _ hY (by simp; omega) (by omega) (by simp; omega),
    putAll_far wb_aligned _ hY (by omega) (by omega) (by omega)]

theorem w_mem : wState.memory = wMem := rfl

/-- A word of the session's own area but the revision's, the source's and the Message-ID's. -/
theorem w_own {Y : Nat} (hY : Y % 8 = 0) (hhi : Y + 8 ≤ ownTexts) (hR : Y ≠ ownRev) (hS : Y ≠ ownSrc)
    (hI : Y ≠ ownId) :
    wMem (wb + BitVec.ofNat 64 (ownOff + Y)) =
      if Y = ownRevLen ∨ Y = ownSrcLen ∨ Y = ownIdLen ∨ Y = ownLow then 1
      else if Y = ownCount ∨ Y = ownHigh then 3
      else if Y = ownNum then 7
      else if Y = ownWall then BitVec.ofNat 64 wSecs
      else 0 := by
  have v := w_vals
  have he := w_ends
  have := v.own; have := v.rev; have := v.src; have := v.texts; have := v.id; have := v.pow
  have hs := he.sizeLe
  have hgi := he.groupIn
  have hte := he.textsEnd
  have hg := he.group
  have hYs : ownOff + Y + 8 ≤ SessionLayout.size := by generalize tOff = T at *; omega
  have hG : ownOff + Y ≠ groupAt 1 + 8 := by generalize tOff = T at *; omega
  rw [wMem_word (by omega) hYs (Or.inl (by omega)) (by omega) (by omega) (by omega) hG, wMem0_at (by omega)]
  have h1 : ownOff + Y ≠ tOff + cGroup := by generalize tOff = T at *; omega
  have h2 : ownOff + Y ≠ groupAt 1 := by generalize tOff = T at *; omega
  have h3 : ¬ (powOff ≤ ownOff + Y ∧ ownOff + Y < powOff + 512 ∧ (ownOff + Y - powOff) % 8 = 0) := by omega
  simp only [Nat.add_left_cancel_iff, h1, h2, h3, or_false, if_false]

/-- …as `wState` has it, the conditions and the value decided at once. -/
theorem w_own_val {Y : Nat} {v : Word}
    (h : Y % 8 = 0 ∧ Y + 8 ≤ ownTexts ∧ Y ≠ ownRev ∧ Y ≠ ownSrc ∧ Y ≠ ownId ∧
    (if Y = ownRevLen ∨ Y = ownSrcLen ∨ Y = ownIdLen ∨ Y = ownLow then (1 : Word)
      else if Y = ownCount ∨ Y = ownHigh then 3
      else if Y = ownNum then 7
      else if Y = ownWall then BitVec.ofNat 64 wSecs
      else 0) = v) : wState.memory (wb + BitVec.ofNat 64 (ownOff + Y)) = v := by
  rw [w_mem, w_own h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2.1]
  exact h.2.2.2.2.2

/-- A word of the table or past it. -/
theorem w_high {Y : Nat} (hY : Y % 8 = 0) (h1 : tOff ≤ Y) (h2 : Y + 8 ≤ SessionLayout.size) (hG : Y ≠ groupAt 1 + 8) :
    wMem (wb + BitVec.ofNat 64 Y) = if Y = tOff + cGroup ∨ Y = groupAt 1 then 1 else 0 := by
  have v := w_vals
  have he := w_ends
  have hTY : ownOff + ownTexts + textAt texts.length ≤ Y := Nat.le_trans he.textsEnd h1
  have := v.own; have := v.rev; have := v.src; have := v.texts; have := v.id; have := v.pow
  have := v.revLen; have := v.srcLen; have := v.idLen; have := v.low; have := v.count; have := v.high
  have := v.num; have := v.wall
  have hs := he.sizeLe
  have hY' : Y < 2 ^ 63 := by omega
  rw [wMem_word hY h2 (Or.inr hTY) (by clear h1; omega) (by clear h1; omega) (by clear h1; omega) hG, wMem0_at hY']
  have e1 : (Y = ownOff + ownRevLen ∨ Y = ownOff + ownSrcLen ∨ Y = ownOff + ownIdLen ∨ Y = ownOff + ownLow ∨
      Y = tOff + cGroup ∨ Y = groupAt 1) = (Y = tOff + cGroup ∨ Y = groupAt 1) := by
    apply propext; clear h1; omega
  have e2 : ¬ (Y = ownOff + ownCount ∨ Y = ownOff + ownHigh) := by clear h1; omega
  have e3 : ¬ Y = ownOff + ownNum := by clear h1; omega
  have e4 : ¬ Y = ownOff + ownWall := by clear h1; omega
  have e5 : ¬ (powOff ≤ Y ∧ Y < powOff + 512 ∧ (Y - powOff) % 8 = 0) := by clear h1; omega
  simp only [e1, e2, e3, e4, e5, if_false]

/-- The witnesses' facts, the layout's heavy terms as variables: `omega` or `simp` meeting the terms themselves
can evaluate the texts. -/
structure WFar (T G S E : Nat) : Prop where
  textsEnd : 1038976 + E ≤ T
  group : T + 173568 ≤ G
  groupAl : G % 8 = 0
  groupIn : G + 72 ≤ S
  sizeLe : S ≤ 4194304

theorem w_far : ∃ T G S E, WFar T G S E ∧ tOff = T ∧ groupAt 1 = G ∧ SessionLayout.size = S ∧
    textAt texts.length = E := by
  have he := w_ends
  have v := w_vals
  have := v.own; have := v.texts
  exact ⟨_, _, _, _, ⟨by have := he.textsEnd; omega, he.group, he.groupAl, he.groupIn, he.sizeLe⟩, rfl, rfl, rfl,
    rfl⟩

theorem w_texts : TextsIn wb wState.memory wState.memaddrs wState.be := by
  intro k hk
  obtain ⟨T, G, S, E, f, hT, hG, hS, hE⟩ := w_far
  have := f.textsEnd; have := f.group; have := f.groupIn; have := f.sizeLe
  have hl : texts.flatten.length = E := hE ▸ texts_len
  have hb : ownOff + ownTexts + textAt k + Session.textLen k ≤ T := hT ▸ text_below hk
  have hlk : (texts.getD k []).length = Session.textLen k := rfl
  have hone : ([49#8] : List (BitVec 8)).length = 1 := rfl
  have v := w_vals
  have := v.own; have := v.rev; have := v.src; have := v.texts; have := v.id
  have hall := putAll_in (be := false) (X := ownOff + ownTexts) (xs := texts.flatten) wMem0 w_cov (by omega)
    (by rw [hS]; omega)
  rw [w_mem]
  unfold wMem
  rw [hG]
  generalize putAll wMem0 false (wb + BitVec.ofNat 64 (ownOff + ownTexts)) 0 texts.flatten = M at hall ⊢
  have e : texts.flatten = (texts.take k).flatten ++ (texts.getD k [] ++ (texts.drop (k + 1)).flatten) := by
    rw [← List.flatten_cons, ← List.flatten_append, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk,
      Option.getD_some, ← List.drop_eq_getElem_cons hk, List.take_append_drop]
  have hk' : ((texts.take k).flatten).length = textAt k := by simp [textAt, List.length_flatten]
  rw [e] at hall
  have h2 := memBytesAt_left (memBytesAt_right hall)
  rw [hk', add_ofNat] at h2
  generalize Session.textLen k = L at hb hlk
  generalize textAt k = A at hb h2
  exact memBytesAt_away (memBytesAt_away (memBytesAt_away (memBytesAt_away h2 (by omega) (by omega)
    (Or.inr (by omega))) (by omega) (by omega) (Or.inr (by omega))) (by omega) (by omega) (Or.inr (by omega)))
    (by omega) (by omega) (Or.inl (by omega))

/-- `1` stored at `X` over the memory `m`, as the witnesses store it, read back. -/
theorem w_one {m : Word → Word} {X : Nat} (hX : 64 ≤ X) (hXs : X + 1 ≤ SessionLayout.size) :
    memBytesAt (putAll m false (wb + BitVec.ofNat 64 X) 0 [49#8]) wState.memaddrs false (wb + BitVec.ofNat 64 X)
      [49#8] :=
  putAll_in _ w_cov hX hXs

theorem w_id : IdIn wb wId wState where
  texts := w_texts
  rev := by
    obtain ⟨T, G, S, E, f, hT, hG, hS, hE⟩ := w_far
    have := f.textsEnd; have := f.group; have := f.groupIn; have := f.sizeLe
    have v := w_vals
    have := v.own; have := v.rev; have := v.src; have := v.id
    have hone : ([49#8] : List (BitVec 8)).length = 1 := rfl
    have hrv : wId.revision.length = 1 := rfl
    rw [w_mem]
    unfold wMem
    rw [hG]
    exact memBytesAt_away (memBytesAt_away (memBytesAt_away (w_one (by omega) (by rw [hS]; omega)) (by omega)
      (by omega) (Or.inl (by omega))) (by omega) (by omega) (Or.inl (by omega))) (by omega) (by omega)
      (Or.inl (by omega))
  src := by
    obtain ⟨T, G, S, E, f, hT, hG, hS, hE⟩ := w_far
    have := f.textsEnd; have := f.group; have := f.groupIn; have := f.sizeLe
    have v := w_vals
    have := v.own; have := v.src; have := v.id
    have hone : ([49#8] : List (BitVec 8)).length = 1 := rfl
    have hsv : wId.source.length = 1 := rfl
    rw [w_mem]
    unfold wMem
    rw [hG]
    exact memBytesAt_away (memBytesAt_away (w_one (by omega) (by rw [hS]; omega)) (by omega) (by omega)
      (Or.inl (by omega))) (by omega) (by omega) (Or.inl (by omega))
  revLen := by decide
  srcLen := by decide

theorem w_pre : TextPre wb 0 wId wState where
  hok := by decide
  hb := wb_aligned
  hc := by rw [nums.count]; decide
  hcov := w_cov
  hid := w_id
  hrl := w_own_val (by decide +kernel)
  hsl := w_own_val (by decide +kernel)

theorem w_entry : TEntry wb 0 0 wState wState := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem w_ctx : TCtx wb 0 0 1 1 wState wState := ⟨rfl, rfl, rfl, rfl, ⟨_, rfl⟩, rfl, rfl, rfl, rfl, rfl, rfl,
    fun _ _ _ => rfl⟩

theorem w_wrote : Wrote wb 0 [] wState := ⟨rfl, fun _ h => absurd h (by simp)⟩

/-- Article 7 of Message-ID `1`. -/
theorem w_stat : StatIn wb 7 [49#8] wState where
  hnum := w_own_val (by decide +kernel)
  hsmall := by decide
  hidLen := w_own_val (by decide +kernel)
  hid := by
    obtain ⟨T, G, S, E, f, hT, hG, hS, hE⟩ := w_far
    have := f.textsEnd; have := f.group; have := f.groupIn; have := f.sizeLe
    have v := w_vals
    have := v.own; have := v.id
    have hone : ([49#8] : List (BitVec 8)).length = 1 := rfl
    rw [w_mem]
    unfold wMem
    rw [hG]
    exact memBytesAt_away (w_one (by omega) (by rw [hS]; omega)) (by omega) (by omega) (Or.inl (by omega))
  hidMax := by decide

/-- Group one, named `1`, of three articles from 1 to 3, connection zero's. -/
theorem w_listed : ListedIn wb 0 3 1 3 1 [49#8] wState where
  hcount := w_own_val (by decide +kernel)
  hlow := w_own_val (by decide +kernel)
  hhigh := w_own_val (by decide +kernel)
  hsmall := by decide
  hsg := by
    have he := w_ends
    obtain ⟨b1, b2, b3, b4⟩ : (tOff + cGroup) % 8 = 0 ∧ tOff ≤ tOff + cGroup ∧
        tOff + cGroup + 8 ≤ SessionLayout.size ∧ tOff + cGroup ≠ groupAt 1 + 8 := by
      have := he.group; have := he.groupIn; have := he.tAl; have := w_vals.group
      generalize tOff = T at *
      omega
    rw [w_mem, SessionFrame.recordAt, add_ofNat, Nat.zero_mul, Nat.add_zero, ← tOff_eq,
      w_high b1 b2 b3 b4, if_pos (Or.inl rfl)]
    rfl
  hsg1 := Nat.le_refl _
  hsgm := by decide
  hgl := by
    have he := w_ends
    obtain ⟨b1, b2, b3⟩ :
        tOff ≤ groupAt 1 ∧ groupAt 1 + 8 ≤ SessionLayout.size ∧ groupAt 1 ≠ groupAt 1 + 8 := by
      have := he.group; have := he.groupIn
      generalize tOff = T at *
      omega
    rw [w_mem, w_high he.groupAl b1 b2 b3, if_pos (Or.inr rfl)]
    rfl
  hg := by
    obtain ⟨T, G, S, E, f, hT, hG, hS, hE⟩ := w_far
    have := f.group; have := f.groupIn; have := f.sizeLe; have := w_vals.own
    rw [w_mem]
    unfold wMem
    rw [hG]
    exact w_one (by omega) (by rw [hS]; omega)
  hgm := by decide

theorem w_pow : PowIn wb wState.memory := fun j hj => by
  show wMem (wb + BitVec.ofNat 64 (powOff + 8 * j)) = _
  have v := w_vals
  have he := w_ends
  have := v.own; have := v.rev; have := v.src; have := v.texts; have := v.id; have := v.pow; have := v.powAl
  have := v.pow64; have := v.revLen; have := v.srcLen; have := v.idLen; have := v.low; have := v.count
  have := v.high; have := v.num; have := v.wall
  have hs := he.sizeLe; have hgi := he.groupIn; have hte := he.textsEnd; have hg := he.group
  have hY : powOff + 8 * j < 2 ^ 63 := by omega
  rw [wMem_word (by omega) (by generalize tOff = T at *; omega) (Or.inl (by omega)) (by omega) (by omega) (by omega)
    (by generalize tOff = T at *; omega), wMem0_at hY]
  generalize tOff = T at *
  generalize groupAt 1 = G at *
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos (by omega),
    show powOff + 8 * j - powOff = 8 * j by omega, Nat.mul_div_cancel_left _ (by decide)]

theorem lowK_witness : LowK [] := ⟨.skip, rfl⟩

theorem part_ok_witness : (Part.text 0).ok := (by decide +kernel : 0 < texts.length)

end DN.Server.SessionText
