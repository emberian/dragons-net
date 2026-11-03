-- SPDX-License-Identifier: AGPL-3.0-or-later
import DN.Server.SessionView
import DN.Server.SessionList

/-!
# DN.Server.SessionCalls

`classify` with the functions it calls proven: if it goes on, `r` holds `CommandSpec.replyIn`'s reply code
(`classify_ok`). Its premises hold together on a one-word line naming no command (`classify_premises`). There a LIST
call keeps its contract (`list_call`); what the reply carries past its code is not shown.
-/

namespace DN.Server.SessionClassify

open DN.Compiler DN.Compiler.WpRet DN.Compiler.Bytes DN.Compiler.Frag DN.News DN.News.WordsRun DN.News.FrameSpec
open DN.Server.SessionLayout (texts ownTexts ownStore connSlot cFramer)

variable {σ : Type}

/-- **`classify` gives the code of `CommandSpec.replyIn`'s reply**, its callees as the code holds them. From its entry,
if it goes on, `r` holds that code; other locals and all words but `clsWords` stay. What the reply carries past its code
is not shown. -/
theorem classify_ok (o : Oracle σ) {b : Word} {ci : Nat} {offered : Bool} {k : FrameSpec.Kind} {L : List Byte}
    {s0 : PancakeState σ} (hs : ClsIn b ci offered k L s0) (hgn : GnCode s0.code) {vb lb : PancakeProg}
    (hvc : s0.code "viewClassify" = some (["c", "cmd"], vb)) (hvl : Lower.lower Session.viewClassify = some vb)
    (hlc : s0.code "listClassify" = some (["c", "cmd"], lb)) (hll : Lower.lower Session.listClassify = some lb) :
    Frag o Session.classify (Like s0) (Out b s0 (Session.replyCode (CommandSpec.replyIn offered ⟨k, L⟩))) :=
  classify_frag o hs hgn (viewClassify_ok o b hvc hvl) (listClassify_ok o b hlc hll hgn)

/-! ### The premises can hold -/

/-- A code with `groupName` as it lowers. -/
def gnCode : String → Option (List String × PancakeProg) := fun f =>
  if f = "groupName" then some (["c", "s1", "l1"], (SessionCheck.gnA (σ := Unit) 0 [] (bareState ())).erase) else none

/-- `groupName` as it lowers, `viewClassify` as `vb` and `listClassify` as `lb`. -/
def jointCode (vb lb : PancakeProg) : String → Option (List String × PancakeProg) := fun f =>
  if f = "groupName" then gnCode f else if f = "viewClassify" then some (["c", "cmd"], vb)
  else if f = "listClassify" then some (["c", "cmd"], lb) else none

/-- The kept word of block zero's line. -/
def jKept : Word := SessionFrame.blockAt SessionAppend.wb 0 + BitVec.ofNat 64 32

/-- The witnesses' words at connection zero's `classify`, the line of the one octet zero, no store. -/
def jState (vb lb : PancakeProg) : PancakeState Unit :=
  { SessionText.wState with
    memory := fun a => if a = jKept then 1 else SessionText.wState.memory a
    code := jointCode vb lb
    locals := fun x => if x = "blk" then some (SessionFrame.blockAt SessionAppend.wb 0)
      else if x = "kind" ∨ x = "kept" then some 1 else some 0 }

theorem jKept_eq : jKept = SessionAppend.wb + BitVec.ofNat 64 (SessionAppend.tOff + cFramer + 32) := by
  rw [jKept, SessionAppend.blockAt_off, Nat.zero_mul,
    show SessionAppend.tOff + 0 = SessionAppend.tOff from Nat.add_zero _]

theorem j_ne {x : Nat} (hx : x < SessionAppend.tOff + cFramer + 32 ∨ SessionAppend.tOff + cFramer + 32 < x)
    (h64 : x < 2 ^ 64) : SessionAppend.wb + BitVec.ofNat 64 x ≠ jKept := by
  rw [jKept_eq]
  obtain ⟨T, hT⟩ := SessionAppend.lay
  rw [hT.eq] at hx ⊢
  have := hT.room
  have hc : cFramer < 2712 := by
    have := SessionAppend.block_facts.fits; have := SessionAppend.block_facts.slot
    have := SessionAppend.block_facts.head; omega
  exact region_addr_inj _ _ _ h64 (by omega) (by omega)

theorem j_far {x : Nat} (hx : x < SessionAppend.tOff) :
    byteAlign (SessionAppend.wb + BitVec.ofNat 64 x) ≠ jKept := by
  rw [byteAlign_base (by decide)]
  obtain ⟨T, hT⟩ := SessionAppend.lay
  have := hT.room
  rw [hT.eq] at hx
  exact j_ne (by rw [hT.eq]; omega) (by omega)

/-- Block zero's first octet, zero. -/
theorem j_line (vb lb : PancakeProg) : memLoadByte (jState vb lb).memory (jState vb lb).memaddrs (jState vb lb).be
    (SessionFrame.blockAt SessionAppend.wb 0 + BitVec.ofNat 64 40 + BitVec.ofNat 64 0) = some 0 := by
  rw [add_ofNat, SessionAppend.blockAt_off]
  obtain ⟨T, G, S, E, hw, hT, hG, hS, -⟩ := SessionText.w_far
  obtain ⟨hc1, hc2, hc3⟩ : cFramer + 40 ≠ SessionLayout.cGroup ∧ cFramer % 8 = 0 ∧ cFramer + 48 ≤ 173568 := by
    decide +kernel
  have hal : T % 8 = 0 := hT ▸ SessionText.w_ends.tAl
  have g1 := hw.group
  have g2 := hw.groupIn
  have g3 := hw.sizeLe
  have g4 := hw.textsEnd
  have hX : SessionAppend.tOff + 0 * connSlot + cFramer + (40 + 0) = T + cFramer + 40 := by rw [hT]; omega
  rw [hX]
  have hm : (T + cFramer + 40) % 8 = 0 := by omega
  have h8 : (T + cFramer + 40) / 8 * 8 = T + cFramer + 40 := by omega
  have ha : byteAlign (SessionAppend.wb + BitVec.ofNat 64 (T + cFramer + 40)) =
      SessionAppend.wb + BitVec.ofNat 64 (T + cFramer + 40) := by
    rw [byteAlign_base (by decide), h8]
  have hd : (jState vb lb).memaddrs (SessionAppend.wb + BitVec.ofNat 64 (T + cFramer + 40)) = true := by
    rw [show (jState vb lb).memaddrs = SessionText.wState.memaddrs from rfl]
    exact SessionText.w_cov.2 _ (by simp only [Analyzer.floor]; omega) (by rw [hS]; omega) hm
  have hY := SessionText.w_high (Y := T + cFramer + 40) (by omega) (by rw [hT]; omega) (by rw [hS]; omega)
    (by rw [hG]; omega)
  have hne := j_ne (x := T + cFramer + 40) (by rw [hT]; omega) (by omega)
  simp only [memLoadByte, ha, hd, if_true]
  rw [show (jState vb lb).memory = fun a => if a = jKept then 1 else SessionText.wState.memory a from rfl]
  dsimp only
  rw [if_neg hne, SessionText.w_mem, hY, if_neg (by rw [hT, hG]; omega)]
  generalize SessionAppend.wb + _ = a
  simp [getByte]

theorem j_texts (vb lb : PancakeProg) :
    SessionAppend.TextsIn SessionAppend.wb (jState vb lb).memory (jState vb lb).memaddrs (jState vb lb).be := by
  intro k hk i hi
  have hb := SessionText.w_texts k hk i hi
  have ht := SessionAppend.text_below hk
  rw [add_ofNat] at hb ⊢
  have hl : (texts.getD k []).length = Session.textLen k := rfl
  rw [show (jState vb lb).memaddrs = SessionText.wState.memaddrs from rfl,
    show (jState vb lb).be = SessionText.wState.be from rfl,
    load_of_word (m := SessionText.wState.memory) (by
      show (if _ = jKept then _ else _) = _
      rw [if_neg (j_far (by omega))])]
  exact hb

theorem clsIn_joint (vb lb : PancakeProg) : ClsIn SessionAppend.wb 0 false .command [0] (jState vb lb) where
  line := ⟨rfl, rfl, fun j hj => by
      have hj0 : j = 0 := by simp at hj; omega
      subst hj0
      exact j_line vb lb, by decide⟩
  c := rfl
  hci := by decide
  kind := rfl
  r := ⟨0, rfl⟩
  base := rfl
  hb := by decide
  hcov := SessionText.w_cov
  texts := j_texts vb lb
  store := by
    rw [show (jState vb lb).memory = fun a => if a = jKept then 1 else SessionText.wState.memory a from rfl]
    dsimp only
    obtain ⟨T, hT⟩ := SessionAppend.lay
    have := hT.above
    have := hT.room
    have h : ownStore + 8 ≤ ownTexts := by decide +kernel
    rw [if_neg (j_ne (by rw [hT.eq]; omega) (by omega))]
    exact SessionText.w_own_val (by decide +kernel)
  short := by decide
  keptW := by
    rw [show (jState vb lb).memory = fun a => if a = jKept then 1 else SessionText.wState.memory a from rfl]
    exact if_pos rfl

theorem gnCode_joint (vb lb : PancakeProg) : GnCode (jState vb lb).code :=
  ⟨_, rfl, SessionCheck.groupName_lower (σ := Unit) 0 [] (bareState ())⟩

theorem view_joint (vb lb : PancakeProg) : (jState vb lb).code "viewClassify" = some (["c", "cmd"], vb) := by
  show jointCode vb lb "viewClassify" = _
  unfold jointCode
  rw [if_neg (by decide), if_pos rfl]

theorem list_joint (vb lb : PancakeProg) : (jState vb lb).code "listClassify" = some (["c", "cmd"], lb) := by
  show jointCode vb lb "listClassify" = _
  unfold jointCode
  rw [if_neg (by decide), if_neg (by decide), if_pos rfl]

/-- **`classify_ok`'s premises hold together**, on a line of one word: its octet zero names no command. -/
theorem classify_premises : ∃ (s0 : PancakeState Unit) (vb lb : PancakeProg),
    ClsIn SessionAppend.wb 0 false .command [0] s0 ∧ GnCode s0.code ∧
    s0.code "viewClassify" = some (["c", "cmd"], vb) ∧ Lower.lower Session.viewClassify = some vb ∧
    s0.code "listClassify" = some (["c", "cmd"], lb) ∧ Lower.lower Session.listClassify = some lb ∧
    1 ≤ (spans [0]).length := by
  obtain ⟨vb, hvb⟩ := view_lowers
  obtain ⟨lb, hlb⟩ := list_lowers
  exact ⟨jState vb lb, vb, lb, clsIn_joint vb lb, gnCode_joint vb lb, view_joint vb lb, hvb, list_joint vb lb, hlb,
    by decide⟩

/-- The same words with `cmd` LIST's code, the state `listClassify` would enter on. -/
def leState (vb lb : PancakeProg) : PancakeState Unit :=
  { jState vb lb with locals := fun x => if x = "cmd" then some 13 else some 0 }

theorem lEntry (vb lb : PancakeProg) : VEntry SessionAppend.wb 0 (cmdCode (some .list)) [0] (leState vb lb) where
  base := rfl
  hb := by decide
  hcov := SessionText.w_cov
  c := rfl
  hci := by decide
  cmd := rfl
  kept := by
    rw [show (leState vb lb).memory = fun a => if a = jKept then 1 else SessionText.wState.memory a from rfl]
    exact if_pos rfl
  bytes := fun j hj => by
    have hj0 : j = 0 := by simp at hj; omega
    subst hj0
    exact j_line vb lb
  short := by decide
  texts := j_texts vb lb

theorem vEntry_witness : VEntry SessionAppend.wb 0 (cmdCode (some .list)) [0] (leState .skip .skip) :=
  lEntry .skip .skip

/-- **A LIST call keeps the contract** on such a state: `listClassify`, as it lowers, if it returns. It gives back the
code of `answerIn`'s reply in the return word. -/
theorem list_call : ∃ lb, SafeR (σ := Unit) Oracle.idle (fun s => s = leState .skip lb) lb
    (CallRet SessionAppend.wb (Session.replyCode (CommandSpec.answerIn .list (argsOf [0])))
      (leState .skip lb).memory) (fun _ => False) := by
  obtain ⟨lb, hlb⟩ := list_lowers
  obtain ⟨body, hc, h⟩ := listClassify_ok (σ := Unit) Oracle.idle SessionAppend.wb (list_joint .skip lb) hlb
    (gnCode_joint .skip lb)
  have : body = lb := by
    have := (list_joint .skip lb).symm.trans hc; simp at this; exact this.symm
  subst this
  exact ⟨body, h 0 .list [0] (leState .skip body) (Or.inr (Or.inl rfl)) (by decide) (lEntry .skip body) rfl⟩

/-- `listClassify`'s contract held by the code as it lowers. -/
theorem fnOk_witness : ∃ code, FnOk (σ := Unit) Oracle.idle "listClassify" SessionAppend.wb IsList code := by
  obtain ⟨lb, hlb⟩ := list_lowers
  exact ⟨_, listClassify_ok Oracle.idle SessionAppend.wb (list_joint .skip lb) hlb (gnCode_joint .skip lb)⟩

end DN.Server.SessionClassify
