-- SPDX-License-Identifier: AGPL-3.0-or-later
import DN.Server.SessionFn

/-!
# DN.Server.SessionView

`viewClassify` keeps its contract `FnOk` for OVER, HDR, XOVER and XHDR (`viewClassify_ok`). On a line of words, if it
returns, it gives back zero and `answerIn`'s code. What its own words hold is not shown.
-/

namespace DN.Server.SessionClassify

open DN.Compiler DN.Compiler.Wp DN.Compiler.Bytes DN.Compiler.Frag DN.News DN.News.WordsRun DN.News.FrameSpec
  DN.Server.SessionText DN.Server.SessionWords
open DN.Server.SessionLayout (framerHead texts ownOff ownVSel ownVs ownVl ownLo ownHi ownFs ownFl)
open DN.News.FramerCode (bw leE or2E bw_ne0 bw_eq0 eval_lt eval_le eval_eq eval_and eval_or2)

variable {σ : Type}

/-! ## `viewClassify` -/

/-- The own words `viewClassify` writes. -/
def vOffs : List Nat := [ownVSel, ownVs, ownVl, ownLo, ownHi, ownFs, ownFl]

theorem vOffs_ok : OffsOk vOffs := by unfold OffsOk; decide +kernel

/-- The locals `viewClassify` declares. -/
def vNames : List String :=
  ["blk", "kept", "w", "s0", "l0", "s1", "l1", "s2", "l2", "s3", "l3", "inw", "ws", "q", "cq", "args", "r", "ok", "val",
   "jq", "lo", "hi", "sel", "good", "eqk", "cz", "dn", "dp", "f0", "meta", "served"]

/-- The locals bound within, those `viewClassify` declares zero. -/
def vBound : List String := ["ok", "val", "jq", "lo", "hi", "sel", "good", "eqk"]

/-- Within `viewClassify`. -/
abbrev VAt : Word → Nat → List Byte → PancakeState σ → PancakeState σ → Prop :=
  FAt vNames vBound vOffs (Session.replyCode .syntax)

/-- Before its last words, `sel` bound. -/
abbrev VEnd : Word → PancakeState σ → Nat → PancakeState σ → Prop := FEnd vNames ["sel"] vOffs

section ViewTree
open DN.Compiler.Syntax DN.Server.Session
open DN.Server.SessionStore (ne or2 ifs inc give)

/-- A message-id where `ids` is one, or a range: `sel` one or two, their places or bounds kept. Else zero. -/
def vpick (s l ids : PExpr) : List PStmt :=
  [.assign "ok" (n 0), ifs ids (messageIdCheckAt s l),
   .ite (v "ok") [.assign "sel" (n 1), fset ownVs s, fset ownVl l]
     (rangeCheckAt s l ++ [ifs (v "ok") [.assign "sel" (n 2), fset ownLo (v "lo"), fset ownHi (v "hi")]])]

/-- OVER's and XOVER's arguments: none, or a message-id or a range. -/
def overTree : List PStmt :=
  [ifs (eEq (v "args") (n 0)) [.assign "good" (n 1)],
   ifs (eEq (v "args") (n 1))
     (vpick (v "s1") (v "l1") (eEq (v "cmd") (n 17)) ++ [.assign "good" (ne (v "sel") (n 0))]),
   ifs (v "good") [fsay (.over false .current)]]

/-- A field's reply: served where it is no metadata item, or `:bytes` or `:lines`. -/
def fieldServe : List PStmt :=
  [fset ownFs (v "s1"), fset ownFl (v "l1"), .dec "served" (eEq (v "meta") (n 0))] ++
    wordIsAt "s1" "l1" SessionStore.tMetaBytes ++ [ifs (v "eqk") [.assign "served" (n 1)]] ++
    wordIsAt "s1" "l1" SessionStore.tMetaLines ++ [ifs (v "eqk") [.assign "served" (n 1)]] ++
    [.ite (v "served") [fsay (.hdr false [] .current)] [fsay .fieldRefused]]

/-- HDR's field: a header's name or a metadata item's, and whether it is served. -/
def fieldTree : List PStmt :=
  [.dec "f0" (kept (v "s1")), .dec "meta" (eEq (v "f0") (n 58)),
   .assign "ok" (eLe (eAdd (n 1) (v "meta")) (v "l1")), .assign "jq" (v "meta"),
   .while (eAnd (v "ok") (eLt (v "jq") (v "l1")))
     [.dec "cz" (kept (eAdd (v "s1") (v "jq"))),
      .assign "ok" (or2 (between 33 57 (v "cz")) (between 59 126 (v "cz"))), inc "jq"],
   ifs (v "ok") fieldServe]

/-- HDR's and XHDR's arguments: a field, and a message-id or a range or nothing. -/
def hdrTree : List PStmt :=
  [ifs (eEq (v "args") (n 1)) [.assign "good" (n 1)],
   ifs (eEq (v "args") (n 2)) (vpick (v "s2") (v "l2") (n 1) ++ [.assign "good" (ne (v "sel") (n 0))]),
   ifs (v "good") fieldTree]

/-- The locals the branches use. -/
def viewDecs : List PStmt := (vBound.map fun x => (x, 0)).map fun p => .dec p.1 (n p.2)

/-- `viewClassify` up to its last words. -/
def viewBody : List PStmt := fnHead ++ scanWords 4 ++ fnKept ++ fnArgs ++ viewDecs ++
  [.ite (or2 (eEq (v "cmd") (n 17)) (eEq (v "cmd") (n 19))) overTree hdrTree, fset ownVSel (v "sel")]

theorem view_eq : Session.viewClassify.body = viewBody ++ give (v "r") := rfl

end ViewTree

/-- If they go on, `viewClassify`'s declarations reach `VAt` with `sel` and `good` zero. -/
theorem vdecs_frag (o : Oracle σ) {b : Word} {ci : Nat} {L : List Byte} {e : PancakeState σ} :
    Frag o viewDecs (FArgs b ci L e) (fun u => VAt b ci L e u ∧ u.locals "sel" = some 0 ∧ u.locals "good" = some 0) :=
  frag_conseq (fdecs_frag o (vBound.map fun x => (x, 0)) (by decide) (by decide) (by decide) (by decide))
    (fun _ h => h) fun u ⟨h, hv⟩ => ⟨h, hv ("sel", 0) (by decide), hv ("good", 0) (by decide)⟩

theorem chk_vBound : ∀ y ∈ chkBound, y ∈ vBound := by decide

theorem vend_of {b : Word} {ci : Nat} {L : List Byte} {e u : PancakeState σ} (h : VAt b ci L e u) :
    VEnd b e (Session.replyCode .syntax) u := fend_of (bnd' := ["sel"]) h (by decide)

/-- **An own word written** within `viewClassify`. -/
theorem vset_frag (o : Oracle σ) {b : Word} {ci K : Nat} {L : List Byte} {e : PancakeState σ}
    (he : VEntry b ci K L e) {X : Nat} (hX : X ∈ vOffs) {x : Syntax.PExpr} {E : PancakeExp}
    (hx : Lower.lowerExp x = some E) {P : Assn σ} (hP : ∀ u, P u → VAt b ci L e u ∧ ∃ v, eval u E = some v)
    {P' : Assn σ} (hcl : Safe.ClockFree P')
    (hP' : ∀ u m, P u → (∀ a, a ≠ b + BitVec.ofNat 64 (ownOff + X) → m a = u.memory a) →
      P' { u with memory := m }) : Frag o [fset X x] P P' :=
  fset_frag o vOffs_ok hX hx (fun u h => ⟨(hP u h).1.base.trans he.base, (hP u h).1.memaddrs ▸ he.hcov,
    (hP u h).2⟩) hcl hP'

/-- The reply `X` set at the end. -/
theorem vsay_frag (o : Oracle σ) {b : Word} {ci : Nat} {L : List Byte} {e : PancakeState σ} (X : CommandSpec.Reply)
    {R : Nat} {P : Assn σ} (hP : ∀ u, P u → VAt b ci L e u ∧ Session.replyCode X = R) :
    Frag o [fsay X] P (VEnd b e R) :=
  fsay_frag o (by decide) (by decide) X hP

theorem vcmd {b : Word} {ci K : Nat} {L : List Byte} {e u : PancakeState σ} (he : VEntry b ci K L e)
    (h : VAt b ci L e u) : u.locals "cmd" = some (BitVec.ofNat 64 K) := fcmd he h (by decide)

/-- **A word's comparison with a text** within `viewClassify`, what else the state holds kept. -/
theorem vcmp_frag (o : Oracle σ) {b : Word} {ci K : Nat} {L : List Byte} {e : PancakeState σ}
    (he : VEntry b ci K L e) (h2 : 2 ≤ (spans L).length) {t : Nat} (ht : t < texts.length)
    {Q : PancakeState σ → Prop} (hQ : ∀ u u', Q u → SessionCheck.ButFor ["eqk", "jq"] u u' → Q u') :
    Frag o (Session.wordIsAt "s1" "l1" t) (fun u => VAt b ci L e u ∧ Q u) (fun u => VAt b ci L e u ∧ Q u ∧
      u.locals "eqk" = some
          (bw (decide ((cut L ((spans L).getD 1 (0, 0))).map CommandSpec.upper = texts.getD t [])))) :=
  fcmp_frag o vOffs_ok (by decide) (by decide) he (by decide) (by decide) (fun u h => fword1 vOffs_ok he h h2) ht hQ

/-! ### Steps within `viewClassify` -/

/-- What `vpick` leaves in `sel`: one for a message-id where `p` asks for one, two for a range, else zero. -/
def selOf (p : Bool) (a : List Byte) : Nat :=
  if p && CommandSpec.isMessageId a then 1 else if (CommandSpec.range? a).isSome then 2 else 0

/-- **A message-id or a range**: if it goes on, which one it is in `sel`. -/
theorem vpick_frag (o : Oracle σ) {b : Word} {ci K : Nat} {L : List Byte} {e : PancakeState σ}
    (he : VEntry b ci K L e) {sn ln : String} (hsn : sn ∉ SessionCheck.rngNames ∧ sn ∉ SessionCheck.midNames)
    (hln : ln ∉ SessionCheck.rngNames ∧ ln ∉ SessionCheck.midNames) {S : Word} {w : List Byte}
    (hW : ∀ u, VAt b ci L e u → WordAt sn ln (SessionFrame.blockAt b ci) S w u)
    {ids : Syntax.PExpr} {IDS : PancakeExp} (hids : Lower.lowerExp ids = some IDS) {p : Bool}
    (hI : ∀ u, VAt b ci L e u → eval u IDS = some (bw p)) :
    Frag o (vpick (Syntax.v sn) (Syntax.v ln) ids) (fun u => VAt b ci L e u ∧ u.locals "sel" = some 0)
      (fun u => VAt b ci L e u ∧ u.locals "sel" = some (BitVec.ofNat 64 (selOf p w))) := by
  let M1 : Assn σ := fun u => VAt b ci L e u ∧ u.locals "sel" = some 0 ∧ u.locals "ok" = some 0
  have f1 : Frag o [.assign "ok" (Syntax.n 0)] (fun u => VAt b ci L e u ∧ u.locals "sel" = some 0) M1 :=
    frag_one (a := .assign "ok" (.const (BitVec.ofNat 64 0))) rfl rfl rfl
      (fat_and fun _ _ h => h) (Safe.assign fun u ⟨h, hs⟩ => by
        obtain ⟨v, hv⟩ := h.bound "ok" (by decide)
        exact ⟨0, v, rfl, hv, fat_set h (by decide) 0, by simp [setLocal, hs], by simp [setLocal]⟩)
  let M2 : Assn σ := fun u => VAt b ci L e u ∧ u.locals "sel" = some 0 ∧
    u.locals "ok" = some (bw (p && CommandSpec.isMessageId w))
  have f2 : Frag o [SessionStore.ifs ids (Session.messageIdCheckAt (Syntax.v sn) (Syntax.v ln))] M1 M2 := by
    refine frag_ite o hids (fat_and fun _ _ h => h) (fun s h => ⟨_, hI s h.1⟩) ?_
      (fun _ _ _ _ h => by simp [declared, Session.messageIdCheckAt] at h)
      (frag_nil o fun s ⟨h, hc⟩ => ⟨h.1, h.2.1, ?_⟩) (fun _ _ _ _ h => by simp [declared] at h)
    · refine frag_conseq (fmid_frag o hsn.2 hln.2 (S := S) (w := w)
        (P := fun s => M1 s ∧ eval s IDS ≠ some 0) fun u h => ⟨fun y hy => h.1.1.bound y (chk_vBound y hy),
          hW u h.1.1⟩) (fun _ h => h)
        fun u ⟨u0, ⟨h0, hc⟩, hm, hk⟩ => ⟨fat_but h0.1 hm.1 (by decide) (fun y _ hy => hk y hy), ?_, ?_⟩
      · rw [hm.1.locals "sel" (by decide)]; exact h0.2.1
      · have hp : p = true := by rw [hI u0 h0.1] at hc; exact bw_ne0 hc
        rw [hm.2, hp]; rfl
    · rw [hI s h.1] at hc
      rw [h.2.2, bw_eq0 hc]; rfl
  -- a message-id kept, or a range checked and kept
  let Q : Assn σ := fun u => VAt b ci L e u ∧ u.locals "sel" = some (BitVec.ofNat 64 (selOf p w))
  have hQ : Safe.ClockFree Q := fat_and fun _ _ h => h
  have hQr : ∀ u y v, Q u → y ∈ ["dn", "dp"] → Q (restore u y v) := fun u y v h hy => by
    simp at hy
    have hne : y ≠ "sel" := by rcases hy with rfl | rfl <;> decide
    refine ⟨fat_restore h.1 (by rcases hy with rfl | rfl <;> decide) v, ?_⟩
    simp only [restore, resVar, if_neg (Ne.symm hne)]; exact h.2
  have sq : ∀ {P : Assn σ} (X : Nat) (hX : X ∈ vOffs) (x : String) {V : Nat}, (∀ u, P u → VAt b ci L e u ∧
      (∃ v, u.locals x = some v) ∧ u.locals "sel" = some (BitVec.ofNat 64 V)) →
      Frag o [fset X (Syntax.v x)] P (fun u => VAt b ci L e u ∧ u.locals "sel" = some (BitVec.ofNat 64 V)) :=
    fun {P} X hX x {V} hP => vset_frag o he hX (x := Syntax.v x) (E := .var x) rfl
      (fun u h => ⟨(hP u h).1, (hP u h).2.1⟩)
      (fat_and fun _ _ h => h) fun u m h hm => ⟨fat_store (hP u h).1 hX hm, (hP u h).2.2⟩
  refine frag_append (xs := [_]) f1 (frag_append (xs := [_]) f2 ?_)
  refine frag_ite o (C := .var "ok") rfl hQ (fun s h => ⟨_, h.2.2⟩) ?_ (fun _ _ _ _ h => by simp [declared, fset] at h)
    ?_ (fun u y v h hy => hQr u y v h (by
      rw [declared_append, show declared (Session.rangeCheckAt (Syntax.v sn) (Syntax.v ln)) = ["dn", "dp"] from rfl]
        at hy
      simpa [declared, SessionStore.ifs] using hy))
  · -- a message-id where one is asked for
    refine frag_pure ((p && CommandSpec.isMessageId w) = true) (fun s ⟨h, hc⟩ => by
      simp only [eval, h.2.2] at hc; exact bw_ne0 hc) (lowK_any _ (k := .skip) (c := _) rfl) fun hpm => ?_
    have e1 : selOf p w = 1 := by simp [selOf, hpm]
    refine frag_append (xs := [_]) (frag_one (a := .assign "sel" (.const (BitVec.ofNat 64 1))) rfl rfl rfl
      (P' := fun u => VAt b ci L e u ∧ u.locals "sel" = some (BitVec.ofNat 64 (selOf p w))) hQ
      (Safe.assign fun u h => ?_))
      (frag_append (xs := [_]) (sq ownVs (by decide) sn fun u h => ⟨h.1, ⟨_, (hW u h.1).start⟩, h.2⟩)
        (sq ownVl (by decide) ln fun u h => ⟨h.1, ⟨_, (hW u h.1).len⟩, h.2⟩))
    obtain ⟨v, hv⟩ := h.1.1.bound "sel" (by decide)
    exact ⟨_, v, rfl, hv, fat_set h.1.1 (by decide) _, by simp [setLocal, e1]⟩
  have hpm0 : ∀ s, M2 s ∧ eval s (.var "ok") = some 0 → (p && CommandSpec.isMessageId w) = false :=
    fun s ⟨h, hc⟩ => by simp only [eval, h.2.2] at hc; exact bw_eq0 hc
  refine frag_pure ((p && CommandSpec.isMessageId w) = false) hpm0 (lowK_any _ (k := .skip) (c := _) rfl)
    fun hpm => ?_
  have fr := frng_frag o hsn.1 hln.1 (S := S) (w := w) (ks := vBound) (by decide)
    (P := fun s => M2 s ∧ eval s (.var "ok") = some 0) fun u h =>
      ⟨fun y hy => h.1.1.bound y (chk_vBound y hy), hW u h.1.1⟩
  let M3 : Assn σ := fun u => ∃ u0, (M2 u0 ∧ eval u0 (.var "ok") = some 0) ∧ SessionCheck.RngPost w u0 u ∧
    ∀ y ∈ vBound, (u0.locals y).isSome → (u.locals y).isSome
  have m3 : ∀ u, M3 u → VAt b ci L e u ∧ u.locals "sel" = some 0 ∧
      u.locals "ok" = some (bw (CommandSpec.range? w).isSome) ∧ ∀ lo hi, CommandSpec.range? w = some (lo, hi) →
        u.locals "lo" = some (BitVec.ofNat 64 lo) ∧ u.locals "hi" = some (BitVec.ofNat 64 hi) :=
    fun u ⟨u0, ⟨h0, _⟩, hr, hk⟩ => ⟨fat_but h0.1 hr.1 (by decide) hk,
      by rw [hr.1.locals "sel" (by decide)]; exact h0.2.1, hr.2.1, hr.2.2⟩
  refine frag_append fr (frag_ite o (C := .var "ok") rfl hQ (fun s h => ⟨_, (m3 s h).2.2.1⟩) ?_
    (fun _ _ _ _ h => by simp [declared, fset] at h) (frag_nil o fun s ⟨h, hc⟩ => ?_)
    (fun _ _ _ _ h => by simp [declared] at h))
  · refine frag_pure ((CommandSpec.range? w).isSome = true) (fun s ⟨h, hc⟩ => by
      simp only [eval, (m3 s h).2.2.1] at hc; exact bw_ne0 hc) (lowK_any _ (k := .skip) (c := _) rfl)
      fun hrs => ?_
    have e2 : selOf p w = 2 := by simp [selOf, hpm, hrs]
    obtain ⟨⟨lo, hi⟩, hlh⟩ := Option.isSome_iff_exists.mp hrs
    refine frag_append (xs := [_]) (frag_one (a := .assign "sel" (.const (BitVec.ofNat 64 2))) rfl rfl rfl
      (P' := fun u => (VAt b ci L e u ∧ u.locals "sel" = some (BitVec.ofNat 64 (selOf p w))) ∧
        u.locals "lo" = some (BitVec.ofNat 64 lo) ∧ u.locals "hi" = some (BitVec.ofNat 64 hi))
      (fun u k h => ⟨hQ u k h.1, h.2⟩) (Safe.assign fun u h => ?_))
      (frag_append (xs := [_]) (vset_frag o he (X := ownLo) (by decide) (x := Syntax.v "lo") (E := .var "lo") rfl
        (P' := fun u => (VAt b ci L e u ∧ u.locals "sel" = some (BitVec.ofNat 64 (selOf p w))) ∧
          u.locals "hi" = some (BitVec.ofNat 64 hi)) (fun u h => ⟨h.1.1, _, h.2.1⟩)
        (fun u k h => ⟨hQ u k h.1, h.2⟩) fun u m h hm => ⟨⟨fat_store h.1.1 (by decide) hm, h.1.2⟩, h.2.2⟩)
        (sq ownHi (by decide) "hi" fun u h => ⟨h.1.1, ⟨_, h.2⟩, h.1.2⟩))
    obtain ⟨v, hv⟩ := (m3 u h.1).1.bound "sel" (by decide)
    obtain ⟨hlo, hhi⟩ := (m3 u h.1).2.2.2 lo hi hlh
    exact ⟨_, v, rfl, hv, ⟨fat_set (m3 u h.1).1 (by decide) _, by simp [setLocal, e2]⟩,
      by simp [setLocal, hlo], by simp [setLocal, hhi]⟩
  · have hrs : (CommandSpec.range? w).isSome = false := by
      simp only [eval, (m3 s h).2.2.1] at hc; exact bw_eq0 hc
    have e0 : selOf p w = 0 := by simp [selOf, hpm, hrs]
    exact ⟨(m3 s h).1, by rw [e0]; exact (m3 s h).2.1⟩

/-! ### OVER and XOVER -/

theorem ans_over {c : CommandSpec.Cmd} (hc : c = .over ∨ c = .xover) (args : List (List Byte)) :
    (args.length = 0 → Session.replyCode (CommandSpec.answerIn c args) = 41) ∧
    (args.length = 1 → Session.replyCode (CommandSpec.answerIn c args) =
      if selOf (decide (c = .over)) (args.getD 0 []) ≠ 0 then 41 else 7) ∧
    (2 ≤ args.length → Session.replyCode (CommandSpec.answerIn c args) = 7) := by
  rcases hc with rfl | rfl <;> rcases args with _ | ⟨a, _ | ⟨a2, rest⟩⟩ <;>
    simp [CommandSpec.answerIn, CommandSpec.answer, Session.replyCode] <;>
    (cases hm : CommandSpec.isMessageId a <;> cases hr : CommandSpec.range? a <;>
      simp [selOf, hm, hr])

theorem selOf_lt (p : Bool) (a : List Byte) : selOf p a < 3 := by unfold selOf; split <;> (try split) <;> omega

/-- **OVER's and XOVER's branch**: if it goes on, the code of the reply `answerIn` gives. -/
theorem over_frag (o : Oracle σ) {b : Word} {ci : Nat} {L : List Byte} {e : PancakeState σ} {c : CommandSpec.Cmd}
    (hc : c = .over ∨ c = .xover) (he : VEntry b ci (cmdCode (some c)) L e) :
    Frag o overTree (fun u => VAt b ci L e u ∧ u.locals "sel" = some 0 ∧ u.locals "good" = some 0)
      (VEnd b e (Session.replyCode (CommandSpec.answerIn c (argsOf L)))) := by
  have hsh := he.short62
  let A := (spans L).length - 1
  have hlen : (argsOf L).length = A := by simp [argsOf, A]
  let a := cut L ((spans L).getD 1 (0, 0))
  have ha : (argsOf L).getD 0 [] = a := argsOf_head L
  obtain ⟨r0, r1, r2⟩ := ans_over hc (argsOf L)
  rw [hlen] at r0 r1 r2; rw [ha] at r1
  let p := decide (c = .over)
  have hp : ∀ u, VAt b ci L e u → eval u (.cmp .equal (.var "cmd") (.const (BitVec.ofNat 64 17))) = some (bw p) :=
    fun u h => by
      rw [eval_eq (x := cmdCode (some c)) (y := 17) (by have := cmdCode_lt (some c); omega) (by decide)
        (by simp only [eval]; exact vcmd he h) rfl]
      rcases hc with rfl | rfl <;> rfl
  -- no argument
  let G0 : Assn σ := fun u => VAt b ci L e u ∧ u.locals "sel" = some 0 ∧
    u.locals "good" = some (bw (decide (A = 0)))
  have f1 : Frag o [SessionStore.ifs (Syntax.eEq (Syntax.v "args") (Syntax.n 0)) [.assign "good" (Syntax.n 1)]]
      (fun u => VAt b ci L e u ∧ u.locals "sel" = some 0 ∧ u.locals "good" = some 0) G0 := by
    refine frag_ite o (C := .cmp .equal (.var "args") (.const (BitVec.ofNat 64 0))) rfl
      (fat_and fun _ _ h => h) (fun s h => ⟨_, fargs_eval h.1 hsh 0 (by decide)⟩) ?_
      (fun _ _ _ _ h => by simp [declared] at h) (frag_nil o fun s ⟨h, hc⟩ => ⟨h.1, h.2.1, ?_⟩)
      (fun _ _ _ _ h => by simp [declared] at h)
    · refine frag_one (a := .assign "good" (.const (BitVec.ofNat 64 1))) rfl rfl rfl
        (fat_and fun _ _ h => h) (Safe.assign fun u ⟨h, hc⟩ => ?_)
      rw [fargs_eval h.1 hsh 0 (by decide)] at hc
      have e0 := of_decide_eq_true (bw_ne0 hc)
      exact ⟨_, _, rfl, h.2.2, fat_set h.1 (by decide) _, by simp [setLocal, h.2.1],
        by simp [setLocal, e0, A]; rfl⟩
    · rw [fargs_eval h.1 hsh 0 (by decide)] at hc
      rw [h.2.2, bw_eq0 hc]; rfl
  -- one argument: a message-id where OVER asks for one, or a range
  let gv := decide (A = 0) || (decide (A = 1) && decide (selOf p a ≠ 0))
  let G1 : Assn σ := fun u => VAt b ci L e u ∧ u.locals "good" = some (bw gv)
  have f2 : Frag o [SessionStore.ifs (Syntax.eEq (Syntax.v "args") (Syntax.n 1))
      (vpick (Syntax.v "s1") (Syntax.v "l1") (Syntax.eEq (Syntax.v "cmd") (Syntax.n 17)) ++
        [.assign "good" (SessionStore.ne (Syntax.v "sel") (Syntax.n 0))])] G0 G1 := by
    refine frag_ite o (C := .cmp .equal (.var "args") (.const (BitVec.ofNat 64 1))) rfl
      (fat_and fun _ _ h => h) (fun s h => ⟨_, fargs_eval h.1 hsh 1 (by decide)⟩) ?_
      (fun _ _ _ _ h => by simp [declared, vpick, SessionStore.ifs] at h)
      (frag_nil o fun s ⟨h, hc⟩ => ⟨h.1, ?_⟩) (fun _ _ _ _ h => by simp [declared] at h)
    · refine frag_pure (A = 1) (fun s ⟨h, hc⟩ => by
        rw [fargs_eval h.1 hsh 1 (by decide)] at hc; exact of_decide_eq_true (bw_ne0 hc))
        (lowK_any _ (k := .skip) (c := _) rfl) fun hA1 => ?_
      refine frag_append (frag_conseq (vpick_frag o he (sn := "s1") (ln := "l1") (by decide) (by decide)
        (fun u h => fword1 vOffs_ok he h (by omega)) rfl hp) (fun s ⟨h, _⟩ => ⟨h.1, h.2.1⟩) fun _ h => h)
        (frag_one (a := .assign "good" (.cmp .equal (.cmp .equal (.var "sel") (.const (BitVec.ofNat 64 0)))
          (.const (BitVec.ofNat 64 0)))) rfl rfl rfl (fat_and fun _ _ h => h)
          (Safe.assign fun u h => ?_))
      obtain ⟨v, hv⟩ := h.1.bound "good" (by decide)
      refine ⟨_, v, ne0_eval (by have := selOf_lt p (cut L ((spans L).getD 1 (0, 0))); omega) h.2, hv,
        fat_set h.1 (by decide) _, ?_⟩
      simp only [setLocal, if_pos, gv, hA1, a]
      simp
    · rw [fargs_eval h.1 hsh 1 (by decide)] at hc
      have h1 : ¬A = 1 := of_decide_eq_false (bw_eq0 hc)
      rw [h.2.2]; show _ = some (bw (decide (A = 0) || (decide (A = 1) && _)))
      rw [show decide (A = 1) = false from decide_eq_false h1]; simp
  have f3 : Frag o [SessionStore.ifs (Syntax.v "good") [fsay (.over false .current)]] G1
      (VEnd b e (Session.replyCode (CommandSpec.answerIn c (argsOf L)))) := by
    refine frag_ite o (C := .var "good") rfl (fend_clock _ _ _) (fun s h => ⟨_, h.2⟩)
      (vsay_frag o _ fun u ⟨h, hc⟩ => ⟨h.1, ?_⟩) (fun _ _ _ _ h => by simp [declared, fsay] at h)
      (frag_nil o fun s ⟨h, hc⟩ => ?_) (fun _ _ _ _ h => by simp [declared] at h)
    · simp only [eval, h.2] at hc
      have := bw_ne0 hc
      simp only [gv, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at this
      rcases this with e0 | ⟨e1, e2⟩
      · rw [r0 e0]; rfl
      · rw [r1 e1, if_pos e2]; rfl
    · simp only [eval, h.2] at hc
      have := bw_eq0 hc
      simp only [gv, Bool.or_eq_false_iff, Bool.and_eq_false_iff, decide_eq_false_iff_not] at this
      have hR : Session.replyCode (CommandSpec.answerIn c (argsOf L)) = Session.replyCode .syntax := by
        rcases this with ⟨n0, n1 | n2⟩
        · rw [r2 (by omega)]; rfl
        · have : A = 1 ∨ 2 ≤ A := by omega
          rcases this with e1 | e2
          · rw [r1 e1, if_neg (by simpa using n2)]; rfl
          · rw [r2 e2]; rfl
      rw [hR]; exact vend_of h.1
  exact frag_append (xs := [_]) f1 (frag_append (xs := [_]) f2 f3)

/-! ### HDR and XHDR -/

/-- HDR's field check after `i` octets, `m` one when the field starts with a colon. -/
def fieldOk (f : List Byte) (m i : Nat) : Bool :=
  decide (1 + m ≤ f.length) && ((f.drop m).take (i - m)).all CommandSpec.isNotColon

/-- Whether a field starts with a colon, as `meta` holds it. -/
def metaOf (f : List Byte) : Nat := if f.getD 0 0 = 58#8 then 1 else 0

theorem fieldOk_full (f : List Byte) : fieldOk f (metaOf f) f.length = CommandSpec.isFieldName f := by
  cases f with
  | nil => simp [fieldOk, metaOf, CommandSpec.isFieldName]
  | cons b rest =>
    by_cases h : b = 58#8
    · subst h
      simp only [fieldOk, metaOf, List.getD_cons_zero, if_true, CommandSpec.isFieldName, List.length_cons]
      simp
      cases rest <;> simp
    · simp only [fieldOk, metaOf, List.getD_cons_zero, if_neg h, CommandSpec.isFieldName, List.length_cons]
      simp [h]

theorem fieldOk_step {f : List Byte} {m i : Nat} (hm : m ≤ i) (hi : i < f.length) :
    fieldOk f m (i + 1) = (fieldOk f m i && CommandSpec.isNotColon f[i]) := by
  simp only [fieldOk]
  rw [show i + 1 - m = (i - m) + 1 by omega, List.take_add_one, List.getElem?_drop,
    show m + (i - m) = i by omega, List.getElem?_eq_getElem hi]
  simp [Bool.and_assoc]

theorem fieldOk_mono {f : List Byte} {m i j : Nat} (hij : i ≤ j) (h : fieldOk f m j = true) :
    fieldOk f m i = true := by
  simp only [fieldOk, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h ⊢
  exact ⟨h.1, fun x hx => h.2 x (List.take_subset_take_left _ (by omega) hx)⟩

theorem notColon_lower {e : Syntax.PExpr} {E : PancakeExp} (he : Lower.lowerExp e = some E) :
    Lower.lowerExp (SessionStore.or2 (Session.between 33 57 e) (Session.between 59 126 e)) =
      some (or2E (SessionCheck.betweenE (BitVec.ofNat 64 33) (BitVec.ofNat 64 57) E)
        (SessionCheck.betweenE (BitVec.ofNat 64 59) (BitVec.ofNat 64 126) E)) := by
  simp [SessionStore.or2, Session.between, or2E, SessionCheck.betweenE, leE, Syntax.eAnd,
    Syntax.eLe, Syntax.eLt, Syntax.eAdd, Syntax.n, Lower.lowerExp, he]

theorem notColon_eval {s : PancakeState σ} {E : PancakeExp} {y : Byte} (h : eval s E = some (y.setWidth 64)) :
    eval s (or2E (SessionCheck.betweenE (BitVec.ofNat 64 33) (BitVec.ofNat 64 57) E)
      (SessionCheck.betweenE (BitVec.ofNat 64 59) (BitVec.ofNat 64 126) E)) =
      some (bw (CommandSpec.isNotColon y)) := by
  rw [setWidth8_64] at h
  rw [eval_or2 (SessionCheck.eval_between (by omega) (by decide) (by decide) h rfl rfl)
    (SessionCheck.eval_between (by omega) (by decide) (by decide) h rfl rfl)]
  simp [CommandSpec.isNotColon]

theorem metaOf_eq {f : List Byte} (h : 0 < f.length) :
    bw (decide (f[0].toNat = 58)) = BitVec.ofNat 64 (metaOf f) := by
  simp only [metaOf, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h, Option.getD_some]
  by_cases e : f[0] = 58#8
  · simp [e, bw]
  · have : f[0].toNat ≠ 58 := fun h' => e (BitVec.eq_of_toNat_eq (by simp [h']))
    simp [e, this, bw]

theorem metaOf_le (f : List Byte) : metaOf f ≤ 1 := by unfold metaOf; split <;> omega

/-- **HDR's field name check is `CommandSpec.isFieldName`**, of the second word, if it goes on. -/
theorem fcheck_frag (o : Oracle σ) {b : Word} {ci K : Nat} {L : List Byte} {e : PancakeState σ}
    (he : VEntry b ci K L e) (h2 : 2 ≤ (spans L).length) :
    Frag o (fieldTree.take 5) (VAt b ci L e) (fun u => VAt b ci L e u ∧
      u.locals "meta" = some (BitVec.ofNat 64 (metaOf (cut L ((spans L).getD 1 (0, 0))))) ∧
      u.locals "ok" = some (bw (CommandSpec.isFieldName (cut L ((spans L).getD 1 (0, 0)))))) := by
  let p := (spans L).getD 1 (0, 0)
  let f := cut L p
  have hpm : p ∈ spans L := by
    exact spans_getD_mem (by omega)
  have hf1 : 0 < f.length := by rw [cut_length (spans_bound L p hpm)]; have := spans_pos L p hpm; omega
  have hsh := he.short62
  have hfl : f.length < 2 ^ 62 := by
    have e1 : f.length = p.2 := cut_length (spans_bound L p hpm)
    have := spans_bound L p hpm; omega
  let m := metaOf f
  have hm1 := metaOf_le f
  let F1 : Assn σ := fun u => VAt b ci L e u ∧ u.locals "f0" = some (f[0].setWidth 64)
  have g1 : Frag o [.dec "f0" (Session.kept (Syntax.v "s1"))] (VAt b ci L e) F1 :=
    frag_dec o (E := .loadByte (.op .add (.op .add (.var "blk") (.const (BitVec.ofNat 64 framerHead))) (.var "s1")))
      (by simp [Session.kept, Syntax.eAdd, Syntax.v, Syntax.n, Lower.lowerExp]) fun u h => by
      have hw := fword1 vOffs_ok he h h2
      have hb := hw.bytes 0 hf1
      rw [show (BitVec.ofNat 64 p.1) + BitVec.ofNat 64 0 = BitVec.ofNat 64 p.1 by simp] at hb
      refine ⟨f[0].setWidth 64, ?_, fat_set h (by decide) _, by simp [setLocal]⟩
      simp only [eval, h.blk, h.s1, show framerHead = 40 from rfl]
      rw [hb]
  let F2 : Assn σ := fun u => VAt b ci L e u ∧ u.locals "meta" = some (BitVec.ofNat 64 m)
  have g2 : Frag o [.dec "meta" (Syntax.eEq (Syntax.v "f0") (Syntax.n 58))] F1 F2 :=
    frag_dec o (E := .cmp .equal (.var "f0") (.const (BitVec.ofNat 64 58))) rfl fun u h => by
      refine ⟨_, eval_eq (x := f[0].toNat) (y := 58) (by omega) (by decide)
        (by simp only [eval, h.2, setWidth8_64]) rfl, fat_set h.1 (by decide) _, ?_⟩
      simp [setLocal, metaOf_eq hf1, m]
  let I (i : Nat) (u : PancakeState σ) : Prop := VAt b ci L e u ∧ u.locals "meta" = some (BitVec.ofNat 64 m) ∧
    u.locals "jq" = some (BitVec.ofNat 64 i) ∧ m ≤ i ∧ i ≤ f.length ∧ u.locals "ok" = some (bw (fieldOk f m i))
  have Iclock : ∀ i, Safe.ClockFree (I i) := fun _ => fat_and fun _ _ h => h
  have g3 : Frag o [.assign "ok" (Syntax.eLe (Syntax.eAdd (Syntax.n 1) (Syntax.v "meta")) (Syntax.v "l1")),
      .assign "jq" (Syntax.v "meta")] F2 (I m) := by
    refine frag_append (xs := [_]) (frag_one (a := .assign "ok" (leE (.op .add (.const 1)
      (.var "meta")) (.var "l1"))) rfl rfl rfl (P' := fun u => F2 u ∧ u.locals "ok" = some (bw (fieldOk f m m)))
      (fun u k h => ⟨⟨fat_clock b ci L e u k h.1.1, h.1.2⟩, h.2⟩) (Safe.assign fun u h => ?_))
      (frag_one (a := .assign "jq" (.var "meta")) rfl rfl rfl (Iclock m) (Safe.assign fun u h => ?_))
    · obtain ⟨v, hv⟩ := h.1.bound "ok" (by decide)
      have hl : u.locals "l1" = some (BitVec.ofNat 64 f.length) := by
        rw [h.1.l1, cut_length (spans_bound L p hpm)]
      refine ⟨_, v, eval_le (x := 1 + m) (y := f.length) (by omega) (by omega)
        (by simp only [eval, h.2]; rw [show (1 : Word) = BitVec.ofNat 64 1 from rfl, ← BitVec.ofNat_add])
        (by simp only [eval]; exact hl), hv, ⟨fat_set h.1 (by decide) _, by simp [setLocal, h.2]⟩, ?_⟩
      simp [setLocal, fieldOk]
    · obtain ⟨v, hv⟩ := h.1.1.bound "jq" (by decide)
      exact ⟨_, v, by simp only [eval]; exact h.1.2, hv, fat_set h.1.1 (by decide) _, by simp [setLocal, h.1.2],
        by simp [setLocal], Nat.le_refl _, by omega, by simp [setLocal, h.2]⟩
  let body : List Syntax.PStmt := [.dec "cz" (Session.kept (Syntax.eAdd (Syntax.v "s1") (Syntax.v "jq"))),
    .assign "ok" (SessionStore.or2 (Session.between 33 57 (Syntax.v "cz")) (Session.between 59 126 (Syntax.v "cz"))),
    SessionStore.inc "jq"]
  have hbody : ∀ i, m ≤ i → i < f.length → fieldOk f m i = true → Frag o body (I i) (I (i + 1)) :=
      fun i hmi hi hp => by
    let M1 : Assn σ := fun u => VAt b ci L e u ∧ u.locals "meta" = some (BitVec.ofNat 64 m) ∧
      u.locals "jq" = some (BitVec.ofNat 64 i) ∧ u.locals "cz" = some (f[i].setWidth 64)
    let M2 : Assn σ := fun u => VAt b ci L e u ∧ u.locals "meta" = some (BitVec.ofNat 64 m) ∧
      u.locals "jq" = some (BitVec.ofNat 64 i) ∧ u.locals "ok" = some (bw (CommandSpec.isNotColon f[i]))
    have b1 : Frag o [body[0]] (I i) M1 := frag_dec o (E := SessionCheck.kb (.var "s1") (.var "jq")) rfl fun s h => by
      have hw := fword1 vOffs_ok he h.1 h2
      have hA : eval s (.op .add (.var "s1") (.var "jq")) = some (BitVec.ofNat 64 p.1 + BitVec.ofNat 64 i) := by
        simp only [eval, h.1.s1, h.2.2.1]; rfl
      refine ⟨_, SessionCheck.kb_eval h.1.blk hA (hw.bytes i hi), fat_set h.1 (by decide) _,
        by simp [setLocal, h.2.1], by simp [setLocal, h.2.2.1], by simp only [setLocal]; rfl⟩
    have b2 : Frag o [body[1]] M1 M2 := frag_one (a := .assign "ok" (or2E
      (SessionCheck.betweenE (BitVec.ofNat 64 33) (BitVec.ofNat 64 57) (.var "cz"))
      (SessionCheck.betweenE (BitVec.ofNat 64 59) (BitVec.ofNat 64 126) (.var "cz"))))
      (by show Lower.lowerStmt1 (.assign "ok" _) = _
          simp only [Lower.lowerStmt1, notColon_lower (e := Syntax.v "cz") rfl]) rfl rfl
      (fat_and fun _ _ h => h) (Safe.assign fun u h => by
        obtain ⟨v, hv⟩ := h.1.bound "ok" (by decide)
        exact ⟨_, v, notColon_eval (by simp only [eval]; exact h.2.2.2), hv, fat_set h.1 (by decide) _,
          by simp [setLocal, h.2.1], by simp [setLocal, h.2.2.1], by simp [setLocal]⟩)
    have b3 : Frag o [body[2]] M2 (I (i + 1)) :=
      frag_one (a := .assign "jq" (.op .add (.var "jq") (.const 1))) rfl rfl rfl (Iclock (i + 1))
        (Safe.assign fun u h => ⟨BitVec.ofNat 64 (i + 1), _, by simp only [eval, h.2.2.1]; rw [BitVec.ofNat_add]; rfl,
          h.2.2.1, fat_set h.1 (by decide) _, by simp [setLocal, h.2.1], by simp [setLocal],
          by omega, by omega, by simp [setLocal, h.2.2.2, fieldOk_step hmi hi, hp]⟩)
    exact frag_append (xs := [_]) b1 (frag_append (xs := [_]) b2 b3)
  have hlow : LowKK body := lowK_any _ (k := .skip) (c := _) rfl
  let COND : PancakeExp := .op .and_ (.var "ok") (.cmp .less (.var "jq") (.var "l1"))
  have hl1 : ∀ u, VAt b ci L e u → u.locals "l1" = some (BitVec.ofNat 64 f.length) := fun u h => by
    rw [h.l1, cut_length (spans_bound L p hpm)]
  have hcond : ∀ i u, I i u → eval u COND = some (bw (fieldOk f m i && decide (i < f.length))) := fun i u h =>
    eval_and (by simp only [eval]; exact h.2.2.2.2.2)
      (eval_lt (by omega) (by omega) (by simp only [eval]; exact h.2.2.1)
        (by simp only [eval]; exact hl1 u h.1))
  have g4 := frag_count o (c := Syntax.eAnd (Syntax.v "ok") (Syntax.eLt (Syntax.v "jq") (Syntax.v "l1"))) (C := COND)
    (by simp [Syntax.eAnd, Syntax.eLt, Syntax.v, Lower.lowerExp, COND]) hlow Iclock
    (fun i u y v h hy => by
      simp [body, declared, SessionStore.inc] at hy; subst hy
      refine ⟨fat_restore h.1 (by decide) v, ?_⟩
      simp only [restore, resVar, if_neg (by decide : ("meta" : String) ≠ "cz"),
        if_neg (by decide : ("jq" : String) ≠ "cz"), if_neg (by decide : ("ok" : String) ≠ "cz")]
      exact h.2) hcond
    (fun i hg => by
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hg
      exact frag_pure (m ≤ i) (fun _ h => h.2.2.2.1) hlow fun hmi => hbody i hmi hg.2 hg.1) m
  refine frag_conseq (frag_append (xs := [_]) g1 (frag_append (xs := [_]) g2 (frag_append (xs := [_, _]) g3 g4)))
    (fun _ h => h) fun u ⟨i, h, hz⟩ => ⟨h.1, h.2.1, ?_⟩
  rw [h.2.2.2.2.2, ← fieldOk_full, count_exit (p := fieldOk f m) (fun _ _ hij h => fieldOk_mono hij h)
    h.2.2.2.2.1 hz]

/-- HDR's reply to a field. -/
def hdrCode (f : List Byte) : Nat :=
  if CommandSpec.isFieldName f then (if CommandSpec.isServedField f then 42 else 47) else 7

theorem served_eq {f : List Byte} (h : 0 < f.length) : CommandSpec.isServedField f =
    (decide (metaOf f = 0) || decide (f.map CommandSpec.upper = texts.getD SessionStore.tMetaBytes []) ||
      decide (f.map CommandSpec.upper = texts.getD SessionStore.tMetaLines [])) := by
  have e1 : texts.getD SessionStore.tMetaBytes [] = CommandSpec.ascii ":BYTES" := rfl
  have e2 : texts.getD SessionStore.tMetaLines [] = CommandSpec.ascii ":LINES" := rfl
  rw [e1, e2]
  cases f with
  | nil => simp at h
  | cons x rest =>
    simp only [CommandSpec.isServedField, metaOf, List.head?_cons, List.getD_cons_zero]
    by_cases hx : x = 58#8 <;> simp [hx]

/-- `served` set where the field is a metadata item served. -/
theorem vserved_frag (o : Oracle σ) {b : Word} {ci : Nat} {L : List Byte} {e : PancakeState σ} (sv uv : Bool) :
    Frag o [SessionStore.ifs (Syntax.v "eqk") [.assign "served" (Syntax.n 1)]]
      (fun u => VAt b ci L e u ∧ u.locals "served" = some (bw sv) ∧ u.locals "eqk" = some (bw uv))
      (fun u => VAt b ci L e u ∧ u.locals "served" = some (bw (sv || uv))) := by
  refine frag_ite o (C := .var "eqk") rfl (fat_and fun _ _ h => h)
    (fun s h => ⟨_, h.2.2⟩) ?_ (fun _ _ _ _ h => by simp [declared] at h)
    (frag_nil o fun s ⟨h, hc⟩ => ⟨h.1, ?_⟩) (fun _ _ _ _ h => by simp [declared] at h)
  · refine frag_one (a := .assign "served" (.const (BitVec.ofNat 64 1))) rfl rfl rfl
      (fat_and fun _ _ h => h) (Safe.assign fun u ⟨h, hc⟩ => ?_)
    simp only [eval, h.2.2] at hc
    have := bw_ne0 hc
    exact ⟨_, _, rfl, h.2.1, fat_set h.1 (by decide) _, by simp [setLocal, this]; rfl⟩
  · simp only [eval, h.2.2] at hc
    rw [h.2.1, bw_eq0 hc, Bool.or_false]

theorem lowKK_serve : LowKK fieldServe :=
  lowKK_append (lowKK_append (lowKK_append (lowKK_append (lowKK_append
    (lowKK_append (xs := [_]) (lowKK_one rfl (fset_lower (X := ownFs) rfl))
      (lowKK_append (xs := [_]) (lowKK_one rfl (fset_lower (X := ownFl) rfl)) (lowKK_dec rfl)))
    (wordIsAt_low "s1" "l1" (by rw [texts_length]; decide))) (lowKK_one rfl rfl))
    (wordIsAt_low "s1" "l1" (by rw [texts_length]; decide)))
    (lowKK_one rfl rfl)) (lowKK_one rfl rfl)

theorem lowKK_field : LowKK fieldTree := by
  have hsplit : fieldTree = fieldTree.take 5 ++ fieldTree.drop 5 := (List.take_append_drop 5 _).symm
  rw [hsplit]
  exact lowKK_append (lowK_any _ (k := .skip) (c := _) rfl) (lowKK_ite rfl lowKK_serve fun k => ⟨k, rfl⟩)

/-- **HDR's field**: a header's or a metadata item's name, and whether it is served. If it goes on, the code `hdrCode`.
-/
theorem field_frag (o : Oracle σ) {b : Word} {ci K : Nat} {L : List Byte} {e : PancakeState σ}
    (he : VEntry b ci K L e) (h2 : 2 ≤ (spans L).length) :
    Frag o fieldTree (VAt b ci L e) (VEnd b e (hdrCode (cut L ((spans L).getD 1 (0, 0))))) := by
  let p := (spans L).getD 1 (0, 0)
  let f := cut L p
  have hpm : p ∈ spans L := by
    exact spans_getD_mem (by omega)
  have hf1 : 0 < f.length := by rw [cut_length (spans_bound L p hpm)]; have := spans_pos L p hpm; omega
  have hsplit : fieldTree = fieldTree.take 5 ++ fieldTree.drop 5 := (List.take_append_drop 5 _).symm
  rw [hsplit]
  refine frag_append (fcheck_frag o he h2) ?_
  have hR : ∀ {Rn : Nat} {P : Assn σ}, (∀ u, P u → VAt b ci L e u) → (∀ u, P u → Rn = 7) →
      Frag o [] P (VEnd b e Rn) := fun hv h7 => frag_nil o fun u h => by rw [h7 u h]; exact vend_of (hv u h)
  refine frag_ite o (C := .var "ok") rfl (fend_clock _ _ _) (fun s h => ⟨_, h.2.2⟩) ?_ ?_
    (hR (fun u h => h.1.1) fun u ⟨h, hc⟩ => by
      simp only [eval, h.2.2] at hc
      have hn : CommandSpec.isFieldName f = false := bw_eq0 hc
      show hdrCode f = 7
      simp only [hdrCode, hn]; rfl)
    (fun _ _ _ _ h => by simp [declared] at h)
  · refine frag_pure (CommandSpec.isFieldName f = true) (fun s ⟨h, hc⟩ => by
      simp only [eval, h.2.2] at hc; exact bw_ne0 hc) lowKK_serve fun hfn => ?_
    let m := metaOf f
    let T1 : Assn σ := fun u => VAt b ci L e u ∧ u.locals "meta" = some (BitVec.ofNat 64 m)
    have st : ∀ (X : Nat) (hX : X ∈ vOffs) (x : String) {P : Assn σ}, (∀ u, P u → T1 u ∧ ∃ v, u.locals x = some v) →
        Frag o [fset X (Syntax.v x)] P T1 := fun X hX x {P} hP =>
      vset_frag o he hX (x := Syntax.v x) (E := .var x) rfl (fun u h => ⟨(hP u h).1.1, (hP u h).2⟩)
        (fat_and fun _ _ h => h) fun u m h hm => ⟨fat_store (hP u h).1.1 hX hm, (hP u h).1.2⟩
    let sv0 := decide (m = 0)
    have h3 : Frag o [.dec "served" (Syntax.eEq (Syntax.v "meta") (Syntax.n 0))] T1
        (fun u => VAt b ci L e u ∧ u.locals "served" = some (bw sv0)) :=
      frag_dec o (E := .cmp .equal (.var "meta") (.const (BitVec.ofNat 64 0))) rfl fun u h =>
        ⟨_, eval_eq (x := m) (y := 0) (by have := metaOf_le f; omega) (by decide)
          (by simp only [eval]; exact h.2) rfl, fat_set h.1 (by decide) _, by simp [setLocal]; rfl⟩
    have hQ : ∀ (w : Value) (u u' : PancakeState σ), u.locals "served" = some w →
        SessionCheck.ButFor ["eqk", "jq"] u u' → u'.locals "served" = some w := fun w u u' h hb => by
      rw [hb.locals "served" (by decide)]; exact h
    have h4 := vcmp_frag o he h2 (t := SessionStore.tMetaBytes) (by rw [texts_length]; decide)
      (Q := fun u => u.locals "served" = some (bw sv0)) (hQ _)
    have h5 := vserved_frag o (b := b) (ci := ci) (L := L) (e := e) sv0
      (decide (f.map CommandSpec.upper = texts.getD SessionStore.tMetaBytes []))
    let sv1 := sv0 || decide (f.map CommandSpec.upper = texts.getD SessionStore.tMetaBytes [])
    have h6 := vcmp_frag o he h2 (t := SessionStore.tMetaLines) (by rw [texts_length]; decide)
      (Q := fun u => u.locals "served" = some (bw sv1)) (hQ _)
    have h7 := vserved_frag o (b := b) (ci := ci) (L := L) (e := e) sv1
      (decide (f.map CommandSpec.upper = texts.getD SessionStore.tMetaLines []))
    have hsv : (sv1 || decide (f.map CommandSpec.upper = texts.getD SessionStore.tMetaLines [])) =
        CommandSpec.isServedField f := by rw [served_eq hf1]
    have h8 : Frag o [.ite (Syntax.v "served") [fsay (.hdr false [] .current)] [fsay .fieldRefused]]
        (fun u => VAt b ci L e u ∧ u.locals "served" = some (bw (CommandSpec.isServedField f)))
        (VEnd b e (hdrCode f)) :=
      frag_ite o (C := .var "served") rfl (fend_clock _ _ _) (fun s h => ⟨_, h.2⟩)
        (vsay_frag o _ fun u ⟨h, hc⟩ => ⟨h.1, by
          simp only [eval, h.2] at hc; simp [hdrCode, hfn, bw_ne0 hc, Session.replyCode]⟩)
        (fun _ _ _ _ h => by simp [declared, fsay] at h)
        (vsay_frag o _ fun u ⟨h, hc⟩ => ⟨h.1, by
          simp only [eval, h.2] at hc; simp [hdrCode, hfn, bw_eq0 hc, Session.replyCode]⟩)
        (fun _ _ _ _ h => by simp [declared, fsay] at h)
    exact frag_append (frag_append (frag_append (frag_append (frag_append
      (frag_append (xs := [_]) (st ownFs (by decide) "s1" fun u h => ⟨⟨h.1.1, h.1.2.1⟩, _, h.1.1.s1⟩)
        (frag_append (xs := [_]) (st ownFl (by decide) "l1" fun u h => ⟨h, _, h.1.l1⟩) h3)) h4) h5) h6) h7)
      (frag_conseq h8 (fun u h => ⟨h.1, by rw [← hsv]; exact h.2⟩) fun _ h => h)
  · intro u y v h hy
    have : y = "served" := by
      simp [fieldServe, declared, fset, Session.wordIsAt, SessionStore.ifs] at hy; exact hy
    subst this; exact fend_restore h (by decide) v

theorem hdrOf_code (c : CommandSpec.Cmd) (f : List Byte) (s : CommandSpec.Sel) :
    Session.replyCode (CommandSpec.hdrOf c f s) = hdrCode f := by
  unfold CommandSpec.hdrOf hdrCode
  cases CommandSpec.isFieldName f <;> cases CommandSpec.isServedField f <;> rfl

theorem ans_hdr {c : CommandSpec.Cmd} (hc : c = .hdr ∨ c = .xhdr) (args : List (List Byte)) :
    (args.length = 1 → Session.replyCode (CommandSpec.answerIn c args) = hdrCode (args.getD 0 [])) ∧
    (args.length = 2 → Session.replyCode (CommandSpec.answerIn c args) =
      if selOf true (args.getD 1 []) ≠ 0 then hdrCode (args.getD 0 []) else 7) ∧
    (args.length ≠ 1 → args.length ≠ 2 → Session.replyCode (CommandSpec.answerIn c args) = 7) := by
  have two : ∀ f a, Session.replyCode (CommandSpec.answerIn c [f, a]) =
      if selOf true a ≠ 0 then hdrCode f else 7 := by
    intro f a
    have e : CommandSpec.answerIn c [f, a] = if CommandSpec.isMessageId a then CommandSpec.hdrOf c f (.id a)
        else match CommandSpec.range? a with
          | some (lo, hi) => CommandSpec.hdrOf c f (.range lo hi)
          | none => .syntax := by rcases hc with rfl | rfl <;> rfl
    rw [e]
    have rs : Session.replyCode .syntax = 7 := rfl
    cases hm : CommandSpec.isMessageId a
    · cases hr : CommandSpec.range? a with
      | none => simp [selOf, hm, hr, rs]
      | some v => obtain ⟨lo, hi⟩ := v; simp [selOf, hm, hr, hdrOf_code]
    · simp [selOf, hm, hdrOf_code]
  have one : ∀ f, Session.replyCode (CommandSpec.answerIn c [f]) = hdrCode f := by
    intro f
    have e : CommandSpec.answerIn c [f] = CommandSpec.hdrOf c f .current := by rcases hc with rfl | rfl <;> rfl
    rw [e, hdrOf_code]
  refine ⟨fun h => ?_, fun h => ?_, fun h1 h2 => ?_⟩
  · rcases args with _ | ⟨f, _ | ⟨a, rest⟩⟩ <;> simp at h; exact one f
  · rcases args with _ | ⟨f, _ | ⟨a, _ | ⟨a3, rest⟩⟩⟩ <;> simp at h; exact two f a
  · rcases args with _ | ⟨f, _ | ⟨a, _ | ⟨a3, rest⟩⟩⟩
    · rcases hc with rfl | rfl <;> rfl
    · simp at h1
    · simp at h2
    · rcases hc with rfl | rfl <;> rfl

/-- **HDR's and XHDR's branch**: if it goes on, the code of the reply `answerIn` gives. -/
theorem hdr_frag (o : Oracle σ) {b : Word} {ci : Nat} {L : List Byte} {e : PancakeState σ} {c : CommandSpec.Cmd}
    (hc : c = .hdr ∨ c = .xhdr) (he : VEntry b ci (cmdCode (some c)) L e) :
    Frag o hdrTree (fun u => VAt b ci L e u ∧ u.locals "sel" = some 0 ∧ u.locals "good" = some 0)
      (VEnd b e (Session.replyCode (CommandSpec.answerIn c (argsOf L)))) := by
  have hsh := he.short62
  let A := (spans L).length - 1
  have hlen : (argsOf L).length = A := by simp [argsOf, A]
  let f := cut L ((spans L).getD 1 (0, 0))
  let a := cut L ((spans L).getD 2 (0, 0))
  obtain ⟨r1, r2, r3⟩ := ans_hdr hc (argsOf L)
  rw [hlen, argsOf_head] at r1
  rw [hlen, argsOf_head, argsOf_second] at r2
  rw [hlen] at r3
  -- one argument
  let G0 : Assn σ := fun u => VAt b ci L e u ∧ u.locals "sel" = some 0 ∧
    u.locals "good" = some (bw (decide (A = 1)))
  have f1 : Frag o [SessionStore.ifs (Syntax.eEq (Syntax.v "args") (Syntax.n 1)) [.assign "good" (Syntax.n 1)]]
      (fun u => VAt b ci L e u ∧ u.locals "sel" = some 0 ∧ u.locals "good" = some 0) G0 := by
    refine frag_ite o (C := .cmp .equal (.var "args") (.const (BitVec.ofNat 64 1))) rfl
      (fat_and fun _ _ h => h) (fun s h => ⟨_, fargs_eval h.1 hsh 1 (by decide)⟩) ?_
      (fun _ _ _ _ h => by simp [declared] at h) (frag_nil o fun s ⟨h, hc⟩ => ⟨h.1, h.2.1, ?_⟩)
      (fun _ _ _ _ h => by simp [declared] at h)
    · refine frag_one (a := .assign "good" (.const (BitVec.ofNat 64 1))) rfl rfl rfl
        (fat_and fun _ _ h => h) (Safe.assign fun u ⟨h, hc⟩ => ?_)
      rw [fargs_eval h.1 hsh 1 (by decide)] at hc
      have e0 := of_decide_eq_true (bw_ne0 hc)
      exact ⟨_, _, rfl, h.2.2, fat_set h.1 (by decide) _, by simp [setLocal, h.2.1],
        by simp [setLocal, e0, A]; rfl⟩
    · rw [fargs_eval h.1 hsh 1 (by decide)] at hc
      rw [h.2.2, bw_eq0 hc]; rfl
  -- two arguments: a message-id or a range
  let gv := decide (A = 1) || (decide (A = 2) && decide (selOf true a ≠ 0))
  let G1 : Assn σ := fun u => VAt b ci L e u ∧ u.locals "good" = some (bw gv)
  have f2 : Frag o [SessionStore.ifs (Syntax.eEq (Syntax.v "args") (Syntax.n 2))
      (vpick (Syntax.v "s2") (Syntax.v "l2") (Syntax.n 1) ++
        [.assign "good" (SessionStore.ne (Syntax.v "sel") (Syntax.n 0))])] G0 G1 := by
    refine frag_ite o (C := .cmp .equal (.var "args") (.const (BitVec.ofNat 64 2))) rfl
      (fat_and fun _ _ h => h) (fun s h => ⟨_, fargs_eval h.1 hsh 2 (by decide)⟩) ?_
      (fun _ _ _ _ h => by simp [declared, vpick, SessionStore.ifs] at h)
      (frag_nil o fun s ⟨h, hc⟩ => ⟨h.1, ?_⟩) (fun _ _ _ _ h => by simp [declared] at h)
    · refine frag_pure (A = 2) (fun s ⟨h, hc⟩ => by
        rw [fargs_eval h.1 hsh 2 (by decide)] at hc; exact of_decide_eq_true (bw_ne0 hc))
        (lowK_any _ (k := .skip) (c := _) rfl) fun hA2 => ?_
      refine frag_append (frag_conseq (vpick_frag o he (sn := "s2") (ln := "l2") (by decide) (by decide)
        (fun u h => fword2 vOffs_ok he h (by omega)) (IDS := .const (BitVec.ofNat 64 1)) rfl (p := true)
        (fun u _ => rfl)) (fun s ⟨h, _⟩ => ⟨h.1, h.2.1⟩) fun _ h => h)
        (frag_one (a := .assign "good" (.cmp .equal (.cmp .equal (.var "sel") (.const (BitVec.ofNat 64 0)))
          (.const (BitVec.ofNat 64 0)))) rfl rfl rfl (fat_and fun _ _ h => h)
          (Safe.assign fun u h => ?_))
      obtain ⟨v, hv⟩ := h.1.bound "good" (by decide)
      refine ⟨_, v, ne0_eval (by have := selOf_lt true (cut L ((spans L).getD 2 (0, 0))); omega) h.2, hv,
        fat_set h.1 (by decide) _, ?_⟩
      simp only [setLocal, gv, hA2, a]
      simp
    · have h1 : ¬A = 2 :=
        of_decide_eq_false (bw_eq0 (by rw [fargs_eval h.1 hsh 2 (by decide)] at hc; exact hc))
      rw [h.2.2]; show _ = some (bw (decide (A = 1) || (decide (A = 2) && _)))
      rw [show decide (A = 2) = false from decide_eq_false h1]; simp
  have f3 : Frag o [SessionStore.ifs (Syntax.v "good") fieldTree] G1
      (VEnd b e (Session.replyCode (CommandSpec.answerIn c (argsOf L)))) := by
    refine frag_ite o (C := .var "good") rfl (fend_clock _ _ _) (fun s h => ⟨_, h.2⟩) ?_
      (fun u y v h hy => fend_restore h (by
        rw [show declared fieldTree = ["f0", "meta"] from rfl] at hy; simp at hy; rcases hy with rfl | rfl <;>
            decide) v)
      (frag_nil o fun s ⟨h, hc⟩ => ?_) (fun _ _ _ _ h => by simp [declared] at h)
    · have hg : ∀ s, G1 s ∧ eval s (.var "good") ≠ some 0 → gv = true := fun s ⟨h, hc⟩ => by
        simp only [eval, h.2] at hc; exact bw_ne0 hc
      refine frag_pure (gv = true) hg lowKK_field fun hgv => ?_
      have hgv' := hgv
      simp only [gv, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hgv'
      have h2 : 2 ≤ (spans L).length := by rcases hgv' with e1 | ⟨e1, _⟩ <;> omega
      have hR : Session.replyCode (CommandSpec.answerIn c (argsOf L)) = hdrCode f := by
        rcases hgv' with e1 | ⟨e1, e2⟩
        · exact r1 e1
        · rw [r2 e1, if_pos e2]
      rw [hR]
      exact frag_conseq (field_frag o he h2) (fun s h => h.1.1) fun _ h => h
    · simp only [eval, h.2] at hc
      have hgv := bw_eq0 hc
      simp only [gv, Bool.or_eq_false_iff, Bool.and_eq_false_iff, decide_eq_false_iff_not] at hgv
      have hR : Session.replyCode (CommandSpec.answerIn c (argsOf L)) = Session.replyCode .syntax := by
        rcases hgv with ⟨n1, n2 | n2⟩
        · exact r3 n1 n2
        · by_cases e2 : A = 2
          · rw [r2 e2, if_neg (by simpa using n2)]; rfl
          · exact r3 n1 e2
      rw [hR]; exact vend_of h.1
  exact frag_append (xs := [_]) f1 (frag_append (xs := [_]) f2 f3)

/-! ### `viewClassify` whole -/

theorem lowKK_hdr : LowKK hdrTree :=
  lowKK_append (xs := [_]) (lowK_any _ (k := .skip) (c := _) rfl) (lowKK_append (xs := [_])
    (lowK_any _ (k := .skip) (c := _) rfl) (lowKK_ite rfl lowKK_field fun k => ⟨k, rfl⟩))

/-- `viewClassify` up to its last words: if it goes on, the reply's code in `r`. -/
theorem view_frag (o : Oracle σ) {b : Word} {ci : Nat} {L : List Byte} {e : PancakeState σ} {c : CommandSpec.Cmd}
    (hc : IsView c) (hw1 : 1 ≤ (spans L).length) (he : VEntry b ci (cmdCode (some c)) L e) :
    Frag o viewBody (Like e) (VEnd b e (Session.replyCode (CommandSpec.answerIn c (argsOf L)))) := by
  have hsh := he.short62
  let R := Session.replyCode (CommandSpec.answerIn c (argsOf L))
  let P0 : Assn σ := fun u => VAt b ci L e u ∧ u.locals "sel" = some 0 ∧ u.locals "good" = some 0
  have hK := cmdCode_lt (some c)
  have hor : ∀ u, P0 u → eval u (or2E (.cmp .equal (.var "cmd") (.const (BitVec.ofNat 64 17)))
      (.cmp .equal (.var "cmd") (.const (BitVec.ofNat 64 19)))) =
      some (bw (decide (cmdCode (some c) = 17) || decide (cmdCode (some c) = 19))) := fun u h =>
    eval_or2 (eval_eq (by omega) (by decide) (by simp only [eval]; exact vcmd he h.1) rfl)
      (eval_eq (by omega) (by decide) (by simp only [eval]; exact vcmd he h.1) rfl)
  have fi : Frag o [.ite (SessionStore.or2 (Syntax.eEq (Syntax.v "cmd") (Syntax.n 17))
      (Syntax.eEq (Syntax.v "cmd") (Syntax.n 19))) overTree hdrTree] P0 (VEnd b e R) := by
    refine frag_ite o (C := or2E (.cmp .equal (.var "cmd") (.const (BitVec.ofNat 64 17)))
      (.cmp .equal (.var "cmd") (.const (BitVec.ofNat 64 19)))) rfl (fend_clock _ _ _) (fun s h => ⟨_, hor s h⟩)
      ?_ (fun _ _ _ _ h => by simp [declared, overTree, SessionStore.ifs] at h) ?_
      (fun _ _ _ _ h => by simp [declared, hdrTree, SessionStore.ifs] at h)
    · refine frag_pure (c = .over ∨ c = .xover) (fun s ⟨h, hc'⟩ => ?_) (lowK_any _ (k := .skip) (c := _) rfl)
        fun hco => frag_conseq (over_frag o hco he) (fun s h => h.1) fun _ h => h
      rw [hor s h] at hc'
      have := bw_ne0 hc'
      rcases hc with rfl | rfl | rfl | rfl <;> simp [cmdCode] at this ⊢
    · refine frag_pure (c = .hdr ∨ c = .xhdr) (fun s ⟨h, hc'⟩ => ?_) lowKK_hdr
        fun hch => frag_conseq (hdr_frag o hch he) (fun s h => h.1) fun _ h => h
      rw [hor s h] at hc'
      have := bw_eq0 hc'
      rcases hc with rfl | rfl | rfl | rfl <;> simp [cmdCode] at this ⊢
  have fs : Frag o [fset ownVSel (Syntax.v "sel")] (VEnd b e R) (VEnd b e R) :=
    fset_frag o vOffs_ok (by decide) (E := .var "sel") rfl (fun u h => ⟨h.base.trans he.base,
      h.memaddrs ▸ he.hcov, h.bound "sel" (by decide)⟩) (fend_clock _ _ _) fun u m h hm => fend_store h (by decide) hm
  exact frag_append (frag_append (frag_append (frag_append (frag_append (fhead_frag o he) (fscan_frag o he))
    (fkept_frag o he)) (fargs_frag o hw1 hsh)) (vdecs_frag o)) (frag_append (xs := [_]) fi fs)

/-- `viewClassify`'s body lowers before anything. -/
theorem lowKK_view : LowKK viewBody := by
  exact lowKK_append (lowKK_append (lowKK_append (lowKK_append (lowKK_append lowKK_fnHead
    (lowK_any _ (k := .skip) (c := _) rfl)) (lowK_any _ (k := .skip) (c := _) rfl))
    (lowK_any _ (k := .skip) (c := _) rfl))
    (lowK_any _ (k := .skip) (c := _) rfl))
    (lowKK_append (xs := [_]) (lowKK_ite rfl (lowK_any _ (k := .skip) (c := _) rfl) lowKK_hdr)
      (lowKK_one rfl (fset_lower rfl)))

/-- `viewClassify` lowers. -/
theorem view_lowers : ∃ body, Lower.lower Session.viewClassify = some body := by
  obtain ⟨c, hc⟩ := lowKK_view _
  refine ⟨c, ?_⟩
  rw [Lower.lower, view_eq, Block.fold_split viewBody _ (by simp [SessionStore.give]) give_lower]
  exact hc

/-- **`viewClassify` gives the code of `answerIn`'s reply to OVER, HDR, XOVER and XHDR.** From its entry on a line of
words, if it returns, it gives back zero and that code. Every word but `clsWords` is as it was. -/
theorem viewClassify_ok (o : Oracle σ) (b : Word) {code : String → Option (List String × PancakeProg)}
    {body : PancakeProg} (hcode : code "viewClassify" = some (["c", "cmd"], body))
    (hbody : Lower.lower Session.viewClassify = some body) : FnOk o "viewClassify" b IsView code := by
  refine ⟨body, hcode, fun ci c L s1 hc hw1 he _ => ?_⟩
  have hsplit := Block.fold_split viewBody (SessionStore.give (Syntax.v "r")) (by simp [SessionStore.give]) give_lower
  rw [Lower.lower, view_eq, hsplit] at hbody
  obtain ⟨c', hc', hs⟩ := view_frag o hc hw1 he _ (CallRet b (Session.replyCode (CommandSpec.answerIn c (argsOf L)))
    s1.memory) (fun _ => False) (fun _ _ _ h _ => h) (give_run o vOffs_ok he.hcov he.base)
  rw [hbody] at hc'; cases hc'
  exact WpRet.conseq hs (fun u (hu : u = s1) => hu ▸ like_refl s1) (fun _ _ h => h) fun _ h => h

/-! ### The premises can hold -/

/-- `viewClassify`'s locals declared, of an empty line in block zero past base zero. -/
def vState : PancakeState Unit :=
  { bareState () with
    locals := fun x => if x = "blk" then some (SessionFrame.blockAt 0 0)
      else if x = "r" then some (BitVec.ofNat 64 (Session.replyCode .syntax)) else some 0 }

theorem vat_witness : VAt 0 0 [] vState vState :=
  ⟨fun _ _ => rfl, fun _ _ => rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    fun y hy => by simp only [vBound, List.mem_cons, List.not_mem_nil, or_false] at hy
                   rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨0, rfl⟩⟩

theorem fat_witness : FAt vNames vBound vOffs (Session.replyCode .syntax) 0 0 [] vState vState := vat_witness

theorem vend_witness : VEnd 0 vState (Session.replyCode .syntax) vState :=
  vend_of vat_witness

end DN.Server.SessionClassify
