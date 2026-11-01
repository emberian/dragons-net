-- SPDX-License-Identifier: AGPL-3.0-or-later
import DN.Server.SessionFn

/-!
# DN.Server.SessionList

`listClassify` keeps its contract `FnOk`: on a line of words, if it returns, it gives back zero and leaves in the
return word the code of the reply `CommandSpec.answerIn` gives LISTGROUP, LIST, DATE, NEWGROUPS and MODE
(`listClassify_ok`); `DN.Server.SessionCalls` puts it together with `classify`. What its own words hold is not shown.
The fragments hold if they go on.
-/

namespace DN.Server.SessionClassify

open DN.Compiler DN.Compiler.Wp DN.Compiler.WpRet DN.Compiler.Frag DN.News DN.News.WordsRun DN.News.FrameSpec
  DN.Server.SessionText DN.Server.SessionWords
open DN.Server.SessionLayout (texts ownRet ownNamed ownLo ownHi ownWs ownWl)
open DN.News.FramerCode (bw leE bw_ne0 bw_eq0 eval_le eval_and)

variable {σ : Type}

/-! ## `listClassify` -/

/-- The own words `listClassify` writes, the return word with them. -/
def lOffs : List Nat := [ownRet, ownNamed, ownLo, ownHi, ownWs, ownWl]

theorem lOffs_ok : OffsOk lOffs := by unfold OffsOk; decide +kernel

/-- The locals `listClassify` declares or its checks and call set. -/
def lNames : List String :=
  ["blk", "kept", "w", "s0", "l0", "s1", "l1", "s2", "l2", "s3", "l3", "inw", "ws", "q", "cq", "args", "r", "ok", "val",
   "jq", "eqk", "lo", "hi", "cz", "dn", "dp", "gn", "ovf", "hdl", "nd", "clo", "chi", "items", "bang"]

/-- The locals bound within, those `listClassify` declares with their constants. -/
def lDecls : List (String × Nat) :=
  [("ok", 1), ("val", 0), ("jq", 0), ("eqk", 0), ("lo", 1), ("hi", CommandSpec.numberMax)]

/-- The locals bound within. -/
def lBound : List String := lDecls.map Prod.fst

/-- Within `listClassify`. -/
abbrev LAt : Word → Nat → List Byte → PancakeState σ → PancakeState σ → Prop :=
  FAt lNames lBound lOffs (Session.replyCode .syntax)

/-- Within, `r` holding `R`. -/
abbrev LAtR (R : Nat) : Word → Nat → List Byte → PancakeState σ → PancakeState σ → Prop := FAt lNames lBound lOffs R

/-- Before its last words. -/
abbrev LEnd : Word → PancakeState σ → Nat → PancakeState σ → Prop := FEnd lNames lBound lOffs

section ListTree
open DN.Compiler.Syntax DN.Server.Session
open DN.Server.SessionStore (ifs give callS found)

/-- LISTGROUP's group named and found: its reply, its range kept. -/
def lgFound : List PStmt :=
  [.ite (eLe (v "l1") (n News.CommandSpec.groupNameMax))
    [fsay (.listGroup none 0 0), fset ownNamed (n 1), fset ownLo (v "lo"), fset ownHi (v "hi")]
    [fsay .noSuchGroup]]

/-- LISTGROUP's branch. -/
def lgTree : List PStmt :=
  [.ite (eEq (v "args") (n 0))
    [fsay (.listGroup none 0 0), fset ownNamed (n 0), fset ownLo (v "lo"), fset ownHi (v "hi")]
    [ifs (eLe (v "args") (n 2))
      ([ifs (eEq (v "args") (n 2)) rangeCheck] ++
       [ifs (v "ok") (callS "gn" "groupName" [v "c", v "s1", v "l1"] ++ [ifs found lgFound])])]]

/-- LIST HEADERS's branch. -/
def headersTree : List PStmt :=
  [ifs (eEq (v "args") (n 1)) [fsay .headerList],
   ifs (eEq (v "args") (n 2))
     (wordIsAt "s2" "l2" tMsgid ++ [ifs (v "eqk") [fsay .headerList]] ++
      wordIsAt "s2" "l2" tRange ++ [ifs (v "eqk") [fsay .headerList]])]

/-- LIST ACTIVE's and NEWSGROUPS's branch. -/
def activeTree : List PStmt :=
  [.ite (eEq (v "args") (n 0)) [fsay (.active none)]
    [ifs (eLe (v "args") (n 2))
      ([ifs (eEq (v "args") (n 2)) (wildmatCheck ++ [fset ownWs (v "s2"), fset ownWl (v "l2")])] ++
       [ifs (v "ok")
         (wordIsAt "s1" "l1" tActive ++ [ifs (v "eqk") [fsay (.active none)]] ++
          wordIsAt "s1" "l1" tNewsgroups ++ [ifs (v "eqk") [fsay .newsgroups]])])]]

/-- LIST's branch. -/
def listTree : List PStmt :=
  [fset ownWs (n 0), fset ownWl (n 0), .dec "ovf" (n 0), .dec "hdl" (n 0),
   ifs (eLe (n 1) (v "args"))
     (wordIsAt "s1" "l1" tOverviewFmt ++ [.assign "ovf" (v "eqk")] ++ wordIsAt "s1" "l1" tHeaders ++
      [.assign "hdl" (v "eqk")]),
   .ite (v "ovf") [ifs (eEq (v "args") (n 1)) [fsay .overviewFmt]] [.ite (v "hdl") headersTree activeTree]]

/-- DATE's branch. -/
def dateTree : List PStmt := [ifs (eEq (v "args") (n 0)) [fsay .date]]

/-- NEWGROUPS's branch. -/
def ngTree : List PStmt :=
  [ifs (eAnd (eLe (n 2) (v "args")) (eLe (v "args") (n 3)))
    (dateTimeCheck ++
     [ifs (eAnd (v "ok") (eEq (v "args") (n 3))) (wordIsAt "s3" "l3" tGmt ++ [.assign "ok" (v "eqk")]),
      ifs (v "ok") [fsay .newGroups]])]

/-- MODE's branch. -/
def modeTree : List PStmt :=
  [ifs (eEq (v "args") (n 1)) (wordIsAt "s1" "l1" tReader ++ [ifs (v "eqk") [fsay .modeReader]])]

/-- The branches on the command. -/
def listBranches : List PStmt :=
  [ifs (eEq (v "cmd") (n 12)) lgTree, ifs (eEq (v "cmd") (n 13)) listTree, ifs (eEq (v "cmd") (n 14)) dateTree,
   ifs (eEq (v "cmd") (n 15)) ngTree, ifs (eEq (v "cmd") (n 16)) modeTree]

/-- `listClassify` up to its last words. -/
def listBody : List PStmt :=
  fnHead ++ scanWords 4 ++ fnKept ++ fnArgs ++ lDecls.map (fun p => .dec p.1 (n p.2)) ++ listBranches

theorem list_eq : Session.listClassify.body = listBody ++ give (v "r") := rfl

end ListTree

/-! ### The trees lower -/

theorem lowKK_headers : LowKK headersTree :=
  lowKK_append (xs := [_]) (lowK_any _ (k := .skip) (c := _) rfl) (lowKK_ite rfl (lowKK_append (lowKK_append
    (lowKK_append (wordIsAt_low "s2" "l2" (by rw [texts_length]; decide)) (lowK_any _ (k := .skip) (c := _) rfl))
    (wordIsAt_low "s2" "l2" (by rw [texts_length]; decide))) (lowK_any _ (k := .skip) (c := _) rfl)) fun k => ⟨k, rfl⟩)

theorem lowKK_active : LowKK activeTree :=
  lowKK_ite rfl (lowK_any _ (k := .skip) (c := _) rfl) (lowKK_ite rfl (lowKK_append
    (lowK_any _ (k := .skip) (c := _) rfl) (lowKK_ite rfl (lowKK_append (lowKK_append (lowKK_append
      (wordIsAt_low "s1" "l1" (by rw [texts_length]; decide)) (lowK_any _ (k := .skip) (c := _) rfl))
      (wordIsAt_low "s1" "l1" (by rw [texts_length]; decide))) (lowK_any _ (k := .skip) (c := _) rfl))
      fun k => ⟨k, rfl⟩)) fun k => ⟨k, rfl⟩)

theorem lowKK_lg : LowKK lgTree := lowK_any _ (k := .skip) (c := _) rfl

theorem lowKK_list : LowKK listTree :=
  lowKK_append (xs := [_, _, _, _]) (lowK_any _ (k := .skip) (c := _) rfl) (lowKK_append (xs := [_])
    (lowKK_ite rfl (lowKK_append (lowKK_append (lowKK_append (wordIsAt_low "s1" "l1" (by rw [texts_length]; decide))
      (lowK_any _ (k := .skip) (c := _) rfl)) (wordIsAt_low "s1" "l1" (by rw [texts_length]; decide)))
      (lowK_any _ (k := .skip) (c := _) rfl)) fun k => ⟨k, rfl⟩)
    (lowKK_ite rfl (lowK_any _ (k := .skip) (c := _) rfl) (lowKK_ite rfl lowKK_headers lowKK_active)))

theorem lowKK_date : LowKK dateTree := lowK_any _ (k := .skip) (c := _) rfl

theorem lowKK_ng : LowKK ngTree :=
  lowKK_ite rfl (lowKK_append (lowK_any _ (k := .skip) (c := _) rfl) (lowKK_append (xs := [_])
    (lowKK_ite rfl (lowKK_append (wordIsAt_low "s3" "l3" (by rw [texts_length]; decide))
      (lowK_any _ (k := .skip) (c := _) rfl)) fun k => ⟨k, rfl⟩) (lowK_any _ (k := .skip) (c := _) rfl)))
    fun k => ⟨k, rfl⟩

theorem lowKK_mode : LowKK modeTree :=
  lowKK_ite rfl (lowKK_append (wordIsAt_low "s1" "l1" (by rw [texts_length]; decide))
    (lowK_any _ (k := .skip) (c := _) rfl)) fun k => ⟨k, rfl⟩

/-! ### Steps within `listClassify` -/

/-- Within, `r` holding `R`, is before the last words. -/
theorem lend_of {R : Nat} {b : Word} {ci : Nat} {L : List Byte} {e u : PancakeState σ} (h : LAtR R b ci L e u) :
    LEnd b e R u := fend_of h fun _ h => h

theorem largs_len (L : List Byte) : (argsOf L).length = (spans L).length - 1 := by simp [argsOf]

section Args
variable {b : Word} {ci : Nat} {L : List Byte} {e : PancakeState σ} {A : Nat}

/-- The arguments' count `A` tested against `k`. -/
theorem largs_eq (hAe : A = (spans L).length - 1) (hsh : L.length < 2 ^ 62) {R : Nat} {u : PancakeState σ}
    (h : LAtR R b ci L e u) (k : Nat) (hk : k < 2 ^ 63) :
    eval u (.cmp .equal (.var "args") (.const (BitVec.ofNat 64 k))) = some (bw (decide (A = k))) := by
  rw [hAe]; exact fargs_eval h hsh k hk

theorem largs_le (hAe : A = (spans L).length - 1) (hsh : L.length < 2 ^ 62) {R : Nat} {u : PancakeState σ}
    (h : LAtR R b ci L e u) (k : Nat) (hk : k < 2 ^ 63) :
    eval u (leE (.var "args") (.const (BitVec.ofNat 64 k))) = some (bw (decide (A ≤ k))) := by
  have := spans_length L
  exact eval_le (by omega) hk (by simp only [eval]; rw [hAe]; exact h.args) rfl

theorem largs_ge (hAe : A = (spans L).length - 1) (hsh : L.length < 2 ^ 62) {R : Nat} {u : PancakeState σ}
    (h : LAtR R b ci L e u) (k : Nat) (hk : k < 2 ^ 63) :
    eval u (leE (.const (BitVec.ofNat 64 k)) (.var "args")) = some (bw (decide (k ≤ A))) := by
  have := spans_length L
  exact eval_le hk (by omega) rfl (by simp only [eval]; rw [hAe]; exact h.args)

end Args

/-- The reply `X` set within, what else the state holds kept. -/
theorem lsayR_frag (o : Oracle σ) {b : Word} {ci : Nat} {L : List Byte} {e : PancakeState σ} (X : CommandSpec.Reply)
    {R0 : Nat} {Q : Assn σ} (hQc : Safe.ClockFree Q) (hQ : ∀ u v, Q u → Q (setL u "r" v)) :
    Frag o [fsay X] (fun u => LAtR R0 b ci L e u ∧ Q u)
      (fun u => LAtR (Session.replyCode X) b ci L e u ∧ Q u) :=
  frag_one (a := .assign "r" (.const (BitVec.ofNat 64 (Session.replyCode X)))) rfl rfl rfl (fat_and hQc)
    (Safe.assign fun u ⟨h, hq⟩ => ⟨_, _, rfl, h.r, fat_say h (by decide) _, hQ u _ hq⟩)

/-- The reply `X` set within where the local `x` is one. -/
theorem lsayIfR_frag (o : Oracle σ) {b : Word} {ci : Nat} {L : List Byte} {e : PancakeState σ} (x : String)
    (X : CommandSpec.Reply) {R0 : Nat} {p : Bool} {Q : Assn σ} (hQc : Safe.ClockFree Q)
    (hQ : ∀ u v, Q u → Q (setL u "r" v)) :
    Frag o [SessionStore.ifs (Syntax.v x) [fsay X]] (fun u => LAtR R0 b ci L e u ∧ u.locals x = some (bw p) ∧ Q u)
      (fun u => LAtR (if p then Session.replyCode X else R0) b ci L e u ∧ Q u) := by
  refine frag_ite o (C := .var x) rfl (fat_and hQc) (fun s h => ⟨_, h.2.1⟩) ?_
    (fun _ _ _ _ h => by simp [declared, fsay] at h) (frag_nil o fun s ⟨h, hc⟩ => ?_)
    (fun _ _ _ _ h => by simp [declared] at h)
  · refine frag_pure (p = true) (fun s ⟨h, hc⟩ => by simp only [eval, h.2.1] at hc; exact bw_ne0 hc)
      (lowK_any _ (k := .skip) (c := _) rfl) fun hp => ?_
    rw [if_pos hp]
    exact frag_conseq (lsayR_frag o X hQc hQ) (fun s h => ⟨h.1.1, h.1.2.2⟩) fun _ h => h
  · simp only [eval, h.2.1] at hc
    rw [if_neg (by rw [bw_eq0 hc]; decide)]
    exact ⟨h.1, h.2.2⟩

/-- An own word `listClassify` writes, written within. -/
theorem lsetR_frag (o : Oracle σ) {b : Word} {ci K : Nat} {L : List Byte} {e : PancakeState σ}
    (he : VEntry b ci K L e) {X : Nat} (hX : X ∈ lOffs) {x : Syntax.PExpr} {E : PancakeExp}
    (hx : Lower.lowerExp x = some E) {R : Nat} {Q : Assn σ} (hQc : Safe.ClockFree Q)
    (hQm : ∀ u (m : Word → Word), Q u → Q { u with memory := m })
    (hE : ∀ u, LAtR R b ci L e u → Q u → ∃ v, eval u E = some v) :
    Frag o [fset X x] (fun u => LAtR R b ci L e u ∧ Q u) (fun u => LAtR R b ci L e u ∧ Q u) :=
  fset_frag o lOffs_ok hX hx (fun u h => ⟨h.1.base.trans he.base, h.1.memaddrs ▸ he.hcov, hE u h.1 h.2⟩)
    (fat_and hQc) fun u m h hm => ⟨fat_store h.1 hX hm, hQm u m h.2⟩

/-- The second word compared with the text `t`, within. -/
theorem lcmp2_frag (o : Oracle σ) {R : Nat} {b : Word} {ci K : Nat} {L : List Byte} {e : PancakeState σ}
    (he : VEntry b ci K L e) (h3 : 3 ≤ (spans L).length) {t : Nat} (ht : t < texts.length) :
    Frag o (Session.wordIsAt "s2" "l2" t) (fun u => LAtR R b ci L e u ∧ True)
      (fun u => LAtR R b ci L e u ∧ True ∧ u.locals "eqk" = some
        (bw (decide ((cut L ((spans L).getD 2 (0, 0))).map CommandSpec.upper = texts.getD t [])))) :=
  fcmp_frag o lOffs_ok (by decide) (by decide) he (by decide) (by decide) (fun u h => fword2 lOffs_ok he h h3) ht
    fun _ _ _ _ => trivial

/-- The first word compared with the text `t`, within, what else the state holds kept. -/
theorem lcmp1_frag (o : Oracle σ) {R : Nat} {b : Word} {ci K : Nat} {L : List Byte} {e : PancakeState σ}
    (he : VEntry b ci K L e) (h2 : 2 ≤ (spans L).length) {t : Nat} (ht : t < texts.length) {Q : Assn σ}
    (hQ : ∀ u u', Q u → SessionCheck.ButFor ["eqk", "jq"] u u' → Q u') :
    Frag o (Session.wordIsAt "s1" "l1" t) (fun u => LAtR R b ci L e u ∧ Q u)
      (fun u => LAtR R b ci L e u ∧ Q u ∧ u.locals "eqk" = some
        (bw (decide ((cut L ((spans L).getD 1 (0, 0))).map CommandSpec.upper = texts.getD t [])))) :=
  fcmp_frag o lOffs_ok (by decide) (by decide) he (by decide) (by decide) (fun u h => fword1 lOffs_ok he h h2) ht hQ

theorem chk_lBound : ∀ y ∈ chkBound, y ∈ lBound := by decide

theorem rng_lNames : ∀ y ∈ SessionCheck.rngNames, y ∈ lNames ∧ y ∉ fFixed := by decide

theorem wm_lNames : ∀ y ∈ SessionCheck.wmNames, y ∈ lNames ∧ y ∉ fFixed := by decide

/-- **LIST's wildmat check** within `listClassify`: `ok` whether the third word is one. -/
theorem lwm_frag (o : Oracle σ) {R : Nat} {b : Word} {ci K : Nat} {L : List Byte} {e : PancakeState σ}
    (he : VEntry b ci K L e) (h3 : 3 ≤ (spans L).length) :
    Frag o Session.wildmatCheck (fun u => LAtR R b ci L e u ∧ u.locals "ok" = some 1)
      (fun u => LAtR R b ci L e u ∧
        u.locals "ok" = some (bw (CommandSpec.wildmat? (cut L ((spans L).getD 2 (0, 0)))).isSome)) := by
  let w := cut L ((spans L).getD 2 (0, 0))
  let ds : List (String × Syntax.PExpr) := [("nd", Syntax.n 0), ("clo", Syntax.n 128), ("chi", Syntax.n 191),
    ("items", Syntax.n 0), ("bang", Syntax.n 0)]
  have hsplit : Session.wildmatCheck = ds.map (fun d => .dec d.1 d.2) ++ Session.wildmatCheck.drop 5 := rfl
  have hc := SessionCheck.wildmatCheck_lower (σ := Unit) [] (bareState ()) true
  have hds : ∀ y ∈ ds.map (·.1), (y ∈ lNames ∧ y ∉ fFixed ∧ y ∉ lBound) ∧ y ≠ "ok" := by decide
  rw [hsplit]
  refine frag_decs o ds (body := Session.wildmatCheck.drop 5) rfl (by simp [Session.wildmatCheck])
    (by simp [Session.wildmatCheck, Syntax.PStmt.isDec, SessionStore.ifs]) rfl
    (fun u y v hy h => ⟨fat_restore h.1 (hds y hy).1 v, by
      simp only [restore, resVar, if_neg (Ne.symm (hds y hy).2)]; exact h.2⟩) fun R' s hp => ?_
  obtain ⟨c', hc', hsafe⟩ := SessionCheck.wildmatCheck_safe o (SessionFrame.blockAt b ci)
    (BitVec.ofNat 64 ((spans L).getD 2 (0, 0)).1) w true s R'
  rw [hc] at hc'; cases hc'
  have hw := fword2 lOffs_ok he hp.1 h3
  have hk := safeR_keeps (WpRet.conseq hsafe (fun u (hu : u = s) => ⟨hu, hu ▸ ⟨hw.start, hw.len, hw.blk, hw.bytes,
    hw.short, hp.2, hp.1.bound "jq" (by decide)⟩⟩) (fun _ _ h => h) fun _ h => h)
  exact WpRet.conseq hk (fun u (hu : u = s) => hu) (fun _ _ h => h) (fun u ⟨⟨hb, hok⟩, hkk⟩ =>
    ⟨fat_but hp.1 hb wm_lNames fun y _ hy => hkk y hy, by rw [hok]; rfl⟩) s rfl

/-- **NEWGROUPS's date and time check** within `listClassify`, what else the state holds kept. -/
theorem ldt_frag (o : Oracle σ) {b : Word} {ci K : Nat} {L : List Byte} {e : PancakeState σ}
    (he : VEntry b ci K L e) (h3 : 3 ≤ (spans L).length) {Q : Assn σ}
    (hQ : ∀ u u', Q u → SessionCheck.ButFor SessionCheck.dtNames u u' → Q u') :
    Frag o Session.dateTimeCheck (fun u => LAt b ci L e u ∧ Q u)
      (fun u => LAt b ci L e u ∧ Q u ∧ u.locals "ok" = some (bw (CommandSpec.isDate (cut L ((spans L).getD 1 (0, 0)))
        && CommandSpec.isTime (cut L ((spans L).getD 2 (0, 0)))))) := by
  let w1 := cut L ((spans L).getD 1 (0, 0))
  let w2 := cut L ((spans L).getD 2 (0, 0))
  have hc := SessionCheck.dateTimeCheck_lower (σ := Unit) [] [] (bareState ())
  refine frag_conseq (frag_pinned o (by simp [Session.dateTimeCheck]) (by simp [Session.dateTimeCheck,
    Session.allDigits, SessionStore.ifs, Syntax.PStmt.isDec]) hc rfl
    (Post := fun s u => SessionCheck.DTPost w1 w2 s u ∧ Safe.Keeps s u)
    (fun _ _ _ h => ⟨⟨{ h.1.1 with }, h.1.2⟩, h.2⟩) fun s hp => ?_)
    (fun _ h => h) fun u ⟨s, ⟨hl, hq⟩, ⟨hb, hok⟩, hk⟩ => ⟨fat_but hl hb (fun y hy => by
      simp [SessionCheck.dtNames] at hy; rcases hy with rfl | rfl <;> decide) fun y _ hs => hk y hs, hQ s u hq hb, hok⟩
  · obtain ⟨c', hc', hsafe⟩ := SessionCheck.dateTimeCheck_safe o (SessionFrame.blockAt b ci)
      (BitVec.ofNat 64 ((spans L).getD 1 (0, 0)).1) (BitVec.ofNat 64 ((spans L).getD 2 (0, 0)).1) w1 w2 s
    rw [hc] at hc'; cases hc'
    have hw1 := fword1 lOffs_ok he hp.1 (by omega)
    have hw2 := fword2 lOffs_ok he hp.1 (by omega)
    exact Safe.safe_keeps (Safe.conseq hsafe (fun u (hu : u = s) => ⟨hu, hu ▸ ⟨hw1.start, hw1.len, hw2.start,
      hw2.len, hw1.blk, hw1.bytes, hw2.bytes, hw1.short, hw2.short, hp.1.bound "ok" (by decide),
      hp.1.bound "jq" (by decide)⟩⟩) fun _ h => h)

/-- The state the branches start from. -/
def LPre (b : Word) (ci : Nat) (L : List Byte) (e u : PancakeState σ) : Prop :=
  LAt b ci L e u ∧ u.locals "ok" = some 1 ∧ u.locals "lo" = some 1 ∧
    u.locals "hi" = some (BitVec.ofNat 64 CommandSpec.numberMax)

theorem lpre_clock (b : Word) (ci : Nat) (L : List Byte) (e : PancakeState σ) : Safe.ClockFree (LPre b ci L e) :=
  fun u k h => ⟨fat_clock b ci L e u k h.1, h.2⟩

/-- **`listClassify`'s own declarations**: the state the branches start from. -/
theorem ldecs_frag (o : Oracle σ) {b : Word} {ci : Nat} {L : List Byte} {e : PancakeState σ} :
    Frag o (lDecls.map fun p => .dec p.1 (Syntax.n p.2)) (FArgs b ci L e) (LPre b ci L e) :=
  frag_conseq (fdecs_frag o lDecls (by decide) (by decide) (by decide) (by decide)) (fun _ h => h)
    fun u ⟨h, hv⟩ => ⟨h, hv ("ok", 1) (by decide), hv ("lo", 1) (by decide), hv ("hi", _) (by decide)⟩

/-- A fact of no state holds at every clock. -/
theorem true_clock : Safe.ClockFree (fun _ : PancakeState σ => True) := fun _ _ _ => trivial

/-- **DATE's branch**: if it goes on, the code of the reply `answerIn` gives. -/
theorem date_frag (o : Oracle σ) {b : Word} {ci : Nat} {L : List Byte} {e : PancakeState σ}
    (hsh : L.length < 2 ^ 62) :
    Frag o dateTree (LPre b ci L e) (LAtR (Session.replyCode (CommandSpec.answerIn .date (argsOf L))) b ci L e) := by
  obtain ⟨A, hAe⟩ : ∃ A, A = (spans L).length - 1 := ⟨_, rfl⟩
  have hlen := largs_len L
  refine frag_bw o rfl (lowK_any _ (k := .skip) (c := _) rfl) (fun k => ⟨k, rfl⟩) (fat_clock _ _ _ _)
    (fun s h => largs_eq hAe hsh h.1 0 (by decide)) (fun h0 => ?_) (fun _ _ _ _ h => by simp [declared, fsay] at h)
    (fun h0 => frag_nil o fun s h => ?_) (fun _ _ _ _ h => by simp [declared] at h)
  · have : (argsOf L).length = 0 := by rw [hlen, ← hAe]; exact of_decide_eq_true h0
    rw [List.length_eq_zero_iff.mp this]
    exact frag_conseq (lsayR_frag o .date (Q := fun _ => True) true_clock fun _ _ _ => trivial)
      (fun s h => ⟨h.1, trivial⟩) fun _ h => h.1
  · obtain ⟨a, rest, hr⟩ : ∃ a rest, argsOf L = a :: rest := by
      cases e' : argsOf L with
      | nil => rw [e'] at hlen; have := of_decide_eq_false h0; simp at hlen; omega
      | cons a rest => exact ⟨a, rest, rfl⟩
    rw [hr]; exact h.1

theorem lowKK_modeIn : LowKK (Session.wordIsAt "s1" "l1" Session.tReader ++
    [SessionStore.ifs (Syntax.v "eqk") [fsay .modeReader]]) :=
  lowKK_append (wordIsAt_low "s1" "l1" (by rw [texts_length]; decide)) (lowK_any _ (k := .skip) (c := _) rfl)

/-- **MODE's branch**: if it goes on, the code of the reply `answerIn` gives. -/
theorem mode_frag (o : Oracle σ) {b : Word} {ci K : Nat} {L : List Byte} {e : PancakeState σ}
    (he : VEntry b ci K L e) (hsh : L.length < 2 ^ 62) :
    Frag o modeTree (LPre b ci L e) (LAtR (Session.replyCode (CommandSpec.answerIn .mode (argsOf L))) b ci L e) := by
  obtain ⟨A, hAe⟩ : ∃ A, A = (spans L).length - 1 := ⟨_, rfl⟩
  have hlen := largs_len L
  refine frag_bw o rfl lowKK_modeIn (fun k => ⟨k, rfl⟩) (fat_clock _ _ _ _)
    (fun s h => largs_eq hAe hsh h.1 1 (by decide)) (fun h1 => ?_)
    (fun _ _ _ _ h => by simp [declared, fsay, Session.wordIsAt, SessionStore.ifs] at h)
    (fun h1 => frag_nil o fun s h => ?_) (fun _ _ _ _ h => by simp [declared] at h)
  · have hA : A = 1 := of_decide_eq_true h1
    obtain ⟨a, ha⟩ : ∃ a, argsOf L = [a] := by
      cases e' : argsOf L with
      | nil => rw [e'] at hlen; simp at hlen; omega
      | cons a rest => cases rest with
        | nil => exact ⟨a, rfl⟩
        | cons _ _ => rw [e'] at hlen; simp at hlen; omega
    have hw : a = cut L ((spans L).getD 1 (0, 0)) := by
      have := argsOf_head L; rw [ha] at this; simpa using this
    have hT : texts.getD Session.tReader [] = CommandSpec.ascii "READER" := rfl
    have e1 : Session.replyCode (CommandSpec.answerIn .mode (argsOf L)) =
        if decide (a.map CommandSpec.upper = texts.getD Session.tReader []) then Session.replyCode .modeReader
        else Session.replyCode .syntax := by
      rw [ha, hT]
      simp only [CommandSpec.answerIn, CommandSpec.answer]
      by_cases hr : a.map CommandSpec.upper = CommandSpec.ascii "READER" <;> simp [hr]
    rw [e1, hw]
    exact frag_append (frag_conseq (lcmp1_frag o (R := Session.replyCode .syntax) he (by omega)
      (t := Session.tReader) (by rw [texts_length]; decide) (Q := fun _ => True) fun _ _ _ _ => trivial)
      (fun s h => ⟨h.1, trivial⟩) fun _ h => ⟨h.1, h.2.2, trivial⟩)
      (frag_conseq (lsayIfR_frag o "eqk" .modeReader true_clock fun _ _ _ => trivial) (fun _ h => h) fun _ h => h.1)
  · have : Session.replyCode (CommandSpec.answerIn .mode (argsOf L)) = Session.replyCode .syntax := by
      have h1' := of_decide_eq_false h1
      cases e' : argsOf L with
      | nil => rfl
      | cons a rest => cases rest with
        | nil => rw [e'] at hlen; simp at hlen; omega
        | cons _ _ => rfl
    rw [this]; exact h.1

/-- NEWGROUPS's reply's code. -/
theorem ans_ng (args : List (List Byte)) : Session.replyCode (CommandSpec.answerIn .newgroups args) =
    if 2 ≤ args.length ∧ args.length ≤ 3 ∧
      (CommandSpec.isDate (args.getD 0 []) && CommandSpec.isTime (args.getD 1 [])) = true ∧
      (args.length = 2 ∨ (args.getD 2 []).map CommandSpec.upper = CommandSpec.ascii "GMT") then 34 else 7 := by
  rcases args with _ | ⟨d, _ | ⟨t, rest⟩⟩
  · rfl
  · rfl
  simp only [CommandSpec.answerIn, List.length_cons, List.getD_cons_succ, List.getD_cons_zero]
  generalize CommandSpec.ascii "GMT" = A
  cases CommandSpec.isDate d <;> cases CommandSpec.isTime t <;> simp only [Bool.false_and, Bool.and_false,
    Bool.true_and, Bool.false_eq_true, and_false, false_and, if_false, Session.replyCode]
  rcases rest with _ | ⟨g, _ | ⟨x, rest⟩⟩
  · rfl
  · by_cases hg : g.map CommandSpec.upper = A <;> simp [hg]
  · simp

theorem lowKK_ngIn : LowKK (Session.dateTimeCheck ++
    [SessionStore.ifs (Syntax.eAnd (Syntax.v "ok") (Syntax.eEq (Syntax.v "args") (Syntax.n 3)))
      (Session.wordIsAt "s3" "l3" Session.tGmt ++ [.assign "ok" (Syntax.v "eqk")]),
     SessionStore.ifs (Syntax.v "ok") [fsay .newGroups]]) :=
  lowKK_append (lowK_any _ (k := .skip) (c := _) rfl) (lowKK_append (xs := [_])
    (lowKK_ite rfl (lowKK_append (wordIsAt_low "s3" "l3" (by rw [texts_length]; decide))
      (lowK_any _ (k := .skip) (c := _) rfl)) fun k => ⟨k, rfl⟩) (lowK_any _ (k := .skip) (c := _) rfl))

/-- **NEWGROUPS's branch**: if it goes on, the code of the reply `answerIn` gives. -/
theorem ng_frag (o : Oracle σ) {b : Word} {ci K : Nat} {L : List Byte} {e : PancakeState σ}
    (he : VEntry b ci K L e) (hsh : L.length < 2 ^ 62) :
    Frag o ngTree (LPre b ci L e)
      (LAtR (Session.replyCode (CommandSpec.answerIn .newgroups (argsOf L))) b ci L e) := by
  obtain ⟨A, hAe⟩ : ∃ A, A = (spans L).length - 1 := ⟨_, rfl⟩
  obtain ⟨dt, hdt⟩ : ∃ dt, dt = (CommandSpec.isDate (cut L ((spans L).getD 1 (0, 0))) &&
      CommandSpec.isTime (cut L ((spans L).getD 2 (0, 0)))) := ⟨_, rfl⟩
  obtain ⟨gmt, hgmt⟩ : ∃ gmt, gmt = decide ((cut L ((spans L).getD 3 (0, 0))).map CommandSpec.upper =
      texts.getD Session.tGmt []) := ⟨_, rfl⟩
  have hT : texts.getD Session.tGmt [] = CommandSpec.ascii "GMT" := rfl
  have hR : Session.replyCode (CommandSpec.answerIn .newgroups (argsOf L)) =
      if 2 ≤ A ∧ A ≤ 3 ∧ dt = true ∧ (A = 2 ∨ gmt = true) then 34 else 7 := by
    rw [ans_ng, largs_len, argsOf_head, argsOf_second, argsOf_third, hAe, hdt, hgmt, hT]
    simp only [decide_eq_true_eq]
  rw [hR]
  refine frag_bw o rfl lowKK_ngIn (fun k => ⟨k, rfl⟩) (fat_clock _ _ _ _)
    (fun s h => eval_and (largs_ge hAe hsh h.1 2 (by decide)) (largs_le hAe hsh h.1 3 (by decide)))
    (fun hc => ?_) (fun _ _ _ _ h => by simp [declared, fsay, Session.wordIsAt, SessionStore.ifs,
      Session.dateTimeCheck, Session.allDigits] at h)
    (fun hc => frag_nil o fun s h => ?_) (fun _ _ _ _ h => by simp [declared] at h)
  · simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
    have f1 : Frag o Session.dateTimeCheck (LPre b ci L e) (fun u => LAt b ci L e u ∧ True ∧
        u.locals "ok" = some (bw dt)) :=
      frag_conseq (ldt_frag o he (by omega) (Q := fun _ => True) (fun _ _ _ _ => trivial))
        (fun s h => ⟨h.1, trivial⟩) (fun u h => ⟨h.1, h.2.1, hdt ▸ h.2.2⟩)
    obtain ⟨v, hv⟩ : ∃ v, v = (dt && (decide (A = 2) || gmt)) := ⟨_, rfl⟩
    have f2 : Frag o [SessionStore.ifs (Syntax.eAnd (Syntax.v "ok") (Syntax.eEq (Syntax.v "args") (Syntax.n 3)))
        (Session.wordIsAt "s3" "l3" Session.tGmt ++ [.assign "ok" (Syntax.v "eqk")])]
        (fun u => LAt b ci L e u ∧ True ∧ u.locals "ok" = some (bw dt))
        (fun u => LAt b ci L e u ∧ u.locals "ok" = some (bw v)) := by
      refine frag_bw o rfl (lowKK_append (wordIsAt_low "s3" "l3" (by rw [texts_length]; decide))
        (lowK_any _ (k := .skip) (c := _) rfl)) (fun k => ⟨k, rfl⟩) (fat_and fun _ _ h => h)
        (fun s h => eval_and (by simp only [eval]; exact h.2.2) (largs_eq hAe hsh h.1 3 (by decide)))
        (fun hd3 => ?_) (fun _ _ _ _ h => by simp [declared, Session.wordIsAt] at h)
        (fun hd3 => frag_nil o fun s h => ⟨h.1, ?_⟩) (fun _ _ _ _ h => by simp [declared] at h)
      · simp only [Bool.and_eq_true, decide_eq_true_eq] at hd3
        have hv1 : v = gmt := by rw [hv, hd3.1, hd3.2]; simp
        refine frag_append (frag_conseq (fcmp_frag o lOffs_ok (by decide) (by decide) he (sn := "s3") (ln := "l3")
          (by decide) (by decide) (fun u h => fword3 lOffs_ok he h (by omega)) (t := Session.tGmt)
          (by rw [texts_length]; decide) (Q := fun _ => True) (fun _ _ _ _ => trivial)) (fun s h => ⟨h.1, trivial⟩)
          (fun _ h => h)) (frag_one (a := .assign "ok" (.var "eqk")) rfl rfl rfl (fat_and fun _ _ h => h)
          (Safe.assign fun u ⟨h, _, hk⟩ => ?_))
        obtain ⟨w0, hw0⟩ := h.bound "ok" (by decide)
        refine ⟨_, w0, by simp only [eval]; exact hk, hw0, fat_set h (by decide) _, ?_⟩
        simp only [setLocal, if_pos, hv1, hgmt]
      · rw [h.2.2, hv]
        cases hd : dt
        · rfl
        · rw [hd, Bool.true_and, decide_eq_false_iff_not] at hd3
          have : A = 2 := by omega
          simp [this]
    refine frag_append f1 (frag_append (xs := [_]) f2 (frag_conseq (lsayIfR_frag o "ok" .newGroups (p := v) true_clock
      fun _ _ _ => trivial) (fun s h => ⟨h.1, h.2, trivial⟩) fun u h => ?_))
    have e1 : (if v = true then Session.replyCode .newGroups else Session.replyCode .syntax) =
        if 2 ≤ A ∧ A ≤ 3 ∧ dt = true ∧ (A = 2 ∨ gmt = true) then 34 else 7 := by
      rw [hv]
      by_cases h2 : A = 2
      · cases dt <;> simp [h2, Session.replyCode]
      · have h3 : A = 3 := by omega
        cases dt <;> cases gmt <;> simp [h3, Session.replyCode]
    rw [← e1]; exact h.1
  · simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not] at hc
    rw [if_neg (show ¬(2 ≤ A ∧ A ≤ 3 ∧ dt = true ∧ (A = 2 ∨ gmt = true)) from fun ⟨h1, h2, _⟩ => by
      rcases hc with hc | hc <;> omega)]
    exact h.1

/-- LISTGROUP's reply's code. -/
theorem ans_lg (args : List (List Byte)) : Session.replyCode (CommandSpec.answerIn .listgroup args) =
    if args.length = 0 then 30
    else if args.length ≤ 2 ∧ (args.length = 1 ∨ (CommandSpec.range? (args.getD 1 [])).isSome = true) then
      (if CommandSpec.isGroupName (args.getD 0 []) then
        (if (args.getD 0 []).length ≤ CommandSpec.groupNameMax then 30 else 25) else 7)
    else 7 := by
  rcases args with _ | ⟨g, _ | ⟨r, _ | ⟨x, rest⟩⟩⟩
  · rfl
  · simp only [CommandSpec.answerIn]
    cases hg : CommandSpec.isGroupName g <;> by_cases hl : g.length ≤ CommandSpec.groupNameMax <;>
      simp [hg, hl, Session.replyCode]
  · simp only [CommandSpec.answerIn]
    cases hr : CommandSpec.range? r with
    | none => simp [hr, Session.replyCode]
    | some lh =>
      cases hg : CommandSpec.isGroupName g <;> by_cases hl : g.length ≤ CommandSpec.groupNameMax <;>
        simp [hr, hg, hl, Session.replyCode]
  · simp [CommandSpec.answerIn, Session.replyCode]

/-- LISTGROUP's reply set within, its words written. -/
theorem lgSayR_frag (o : Oracle σ) {b : Word} {ci K : Nat} {L : List Byte} {e : PancakeState σ}
    (he : VEntry b ci K L e) (nm : Nat) {R0 : Nat} {P : Assn σ} (hP : ∀ u, P u → LAtR R0 b ci L e u) :
    Frag o [fsay (.listGroup none 0 0), fset ownNamed (Syntax.n nm), fset ownLo (Syntax.v "lo"),
      fset ownHi (Syntax.v "hi")] P (LAtR 30 b ci L e) :=
  frag_conseq (frag_append (xs := [_]) (lsayR_frag o (.listGroup none 0 0) (Q := fun _ => True) true_clock
      fun _ _ _ => trivial) (frag_append (xs := [_])
    (lsetR_frag o he (X := ownNamed) (by decide) (E := .const (BitVec.ofNat 64 nm)) rfl true_clock (fun _ _ h => h)
      fun _ _ _ => ⟨_, rfl⟩) (frag_append (xs := [_])
    (lsetR_frag o he (X := ownLo) (by decide) (E := .var "lo") rfl true_clock (fun _ _ h => h)
      fun _ h _ => h.bound "lo" (by decide))
    (lsetR_frag o he (X := ownHi) (by decide) (E := .var "hi") rfl true_clock (fun _ _ h => h)
      fun _ h _ => h.bound "hi" (by decide)))))
    (fun s h => ⟨hP s h, trivial⟩) fun _ h => h.1

theorem lowKK_lgIn : LowKK (SessionStore.callS "gn" "groupName" [Syntax.v "c", Syntax.v "s1", Syntax.v "l1"] ++
    [SessionStore.ifs SessionStore.found lgFound]) :=
  lowKK_append (lowKK_append (lowKK_call rfl) (lowK_any _ (k := .skip) (c := _) rfl))
    (lowKK_ite found_lower (lowK_any _ (k := .skip) (c := _) rfl) fun k => ⟨k, rfl⟩)

/-- **LISTGROUP's branch**: if it goes on, the code of the reply `answerIn` gives. -/
theorem lg_frag (o : Oracle σ) {b : Word} {ci K : Nat} {L : List Byte} {e : PancakeState σ}
    (he : VEntry b ci K L e) (hgn : GnCode e.code) (hsh : L.length < 2 ^ 62) :
    Frag o lgTree (LPre b ci L e)
      (LAtR (Session.replyCode (CommandSpec.answerIn .listgroup (argsOf L))) b ci L e) := by
  obtain ⟨A, hAe⟩ : ∃ A, A = (spans L).length - 1 := ⟨_, rfl⟩
  obtain ⟨rok, hrok⟩ : ∃ rok, rok = (CommandSpec.range? (cut L ((spans L).getD 2 (0, 0)))).isSome := ⟨_, rfl⟩
  obtain ⟨gnm, hgnm⟩ : ∃ g, g = CommandSpec.isGroupName (cut L ((spans L).getD 1 (0, 0))) := ⟨_, rfl⟩
  obtain ⟨gl, hgl⟩ : ∃ g, g = decide ((cut L ((spans L).getD 1 (0, 0))).length ≤ CommandSpec.groupNameMax) :=
    ⟨_, rfl⟩
  have hR : Session.replyCode (CommandSpec.answerIn .listgroup (argsOf L)) =
      if A = 0 then 30 else if A ≤ 2 ∧ (A = 1 ∨ rok = true) then
        (if gnm = true then (if gl = true then 30 else 25) else 7) else 7 := by
    rw [ans_lg, largs_len, argsOf_head, argsOf_second, ← hAe, ← hrok, ← hgnm, hgl]
    simp only [decide_eq_true_eq]
  rw [hR]
  let M : Assn σ := fun u => LAt b ci L e u ∧ u.locals "ok" = some (bw (decide (A = 1) || rok))
  have hMc : Safe.ClockFree M := fat_and fun _ _ h => h
  -- the range, where there is one
  have f1 : 1 ≤ A ∧ A ≤ 2 →
      Frag o [SessionStore.ifs (Syntax.eEq (Syntax.v "args") (Syntax.n 2)) Session.rangeCheck] (LPre b ci L e) M :=
    fun h12 => frag_bw o rfl (lowK_any _ (k := .skip) (c := _) rfl) (fun k => ⟨k, rfl⟩) hMc
      (fun s h => largs_eq hAe hsh h.1 2 (by decide))
      (fun hA2 => frag_conseq (frng_frag o (sn := "s2") (ln := "l2") (by decide) (by decide) (ks := lBound)
        (by decide) (fun u h => ⟨fun y hy => h.1.bound y (chk_lBound y hy), fword2 lOffs_ok he h.1 (by
          have := of_decide_eq_true hA2; omega)⟩))
        (fun _ h => h) fun u ⟨u0, h0, hr, hk⟩ => ⟨fat_but h0.1 hr.1 rng_lNames hk, by
          rw [hr.2.1, of_decide_eq_true hA2, hrok]; rfl⟩)
      (fun u y v h hy => by
        rw [show declared Session.rangeCheck = ["dn", "dp"] from rfl] at hy
        have hds : (y ∈ lNames ∧ y ∉ fFixed ∧ y ∉ lBound) ∧ y ≠ "ok" := by
          simp at hy; rcases hy with rfl | rfl <;> decide
        exact ⟨fat_restore h.1 hds.1 v, by simp only [restore, resVar, if_neg (Ne.symm hds.2)]; exact h.2⟩)
      (fun hA2 => frag_nil o fun s h => ⟨h.1, by
        have h1 : A = 1 := by have := of_decide_eq_false hA2; omega
        rw [h.2.1, h1]; rfl⟩)
      (fun _ _ _ _ h => by simp [declared] at h)
  -- the group, where the range is good
  have f2 : 1 ≤ A ∧ A ≤ 2 → Frag o [SessionStore.ifs (Syntax.v "ok") (SessionStore.callS "gn" "groupName"
      [Syntax.v "c", Syntax.v "s1", Syntax.v "l1"] ++ [SessionStore.ifs SessionStore.found lgFound])] M
        (LAtR (if decide (A = 1) || rok then
          (if gnm = true then (if gl = true then 30 else 25) else 7) else 7) b ci L e) := fun h12 => by
    refine frag_bw o rfl lowKK_lgIn (fun k => ⟨k, rfl⟩) (fat_clock _ _ _ _) (fun s h => by
      simp only [eval]; exact h.2) (fun hok => ?_) (fun u y v h hy => fat_restore h (by
        rw [show declared (SessionStore.callS "gn" "groupName" [Syntax.v "c", Syntax.v "s1", Syntax.v "l1"] ++
          [SessionStore.ifs SessionStore.found lgFound]) = ["gn"] from rfl] at hy
        simp at hy; rw [hy]; decide) v)
      (fun hok => frag_nil o fun s h => by rw [if_neg (by rw [hok]; decide)]; exact h.1)
      (fun _ _ _ _ h => by simp [declared] at h)
    have h2 : 2 ≤ (spans L).length := by omega
    rw [if_pos hok]
    refine frag_append (frag_conseq (fgn_frag o lOffs_ok (by decide) (by decide) (by decide) he hgn h2
      (Q := fun _ => True) (fun _ _ _ => trivial) (fun _ _ _ _ => trivial)) (fun s h => ⟨h.1, trivial⟩)
      (fun _ h => h)) ?_
    refine frag_bw o found_lower (lowK_any _ (k := .skip) (c := _) rfl) (fun k => ⟨k, rfl⟩) (fat_clock _ _ _ _)
      (fun s h => by rw [ffound_eval he h.1, h.2.2.2, ← hgnm]) (fun hg => ?_)
      (fun _ _ _ _ h => by simp [declared, lgFound] at h)
      (fun hg => frag_nil o fun s h => by rw [if_neg (by rw [hg]; decide)]; exact h.1)
      (fun _ _ _ _ h => by simp [declared] at h)
    rw [if_pos hg]
    have hb := spans_bound L _ (spans_getD_mem (L := L) (j := 1) (by omega))
    have hcl := cut_length hb
    refine frag_bw o rfl (lowK_any _ (k := .skip) (c := _) rfl) (lowK_any _ (k := .skip) (c := _) rfl)
      (fat_clock _ _ _ _) (p := gl) (fun s h => by
        rw [hgl]
        exact eval_le (by omega) (by decide) (by simp only [eval]; rw [h.1.l1, cut_length hb]) rfl)
      (fun hg1 => by rw [if_pos hg1]; exact lgSayR_frag o he 1 fun u h => h.1)
      (fun _ _ _ _ h => by simp [declared, fsay, fset] at h)
      (fun hg1 => by
        rw [if_neg (by rw [hg1]; decide)]
        exact frag_conseq (lsayR_frag o .noSuchGroup (Q := fun _ => True) true_clock fun _ _ _ => trivial)
          (fun s h => ⟨h.1, trivial⟩) fun _ h => h.1)
      (fun _ _ _ _ h => by simp [declared, fsay] at h)
  refine frag_bw o (C := .cmp .equal (.var "args") (.const (BitVec.ofNat 64 0))) rfl
    (lowK_any _ (k := .skip) (c := _) rfl) (lowKK_ite rfl (lowKK_append (lowK_any _ (k := .skip) (c := _) rfl)
      (lowKK_ite rfl lowKK_lgIn fun k => ⟨k, rfl⟩)) fun k => ⟨k, rfl⟩) (fat_clock _ _ _ _)
    (fun s h => largs_eq hAe hsh h.1 0 (by decide))
    (fun hA0 => by rw [if_pos (of_decide_eq_true hA0)]; exact lgSayR_frag o he 0 fun u h => h.1)
    (fun _ _ _ _ h => by simp [declared, fsay, fset] at h) (fun hA0 => ?_)
    (fun _ _ _ _ h => by simp [declared] at h)
  have hA0' : ¬A = 0 := of_decide_eq_false hA0
  rw [if_neg hA0']
  refine frag_bw o (C := leE (.var "args") (.const (BitVec.ofNat 64 2))) rfl
    (lowKK_append (lowK_any _ (k := .skip) (c := _) rfl) (lowKK_ite rfl lowKK_lgIn fun k => ⟨k, rfl⟩))
    (fun k => ⟨k, rfl⟩) (fat_clock _ _ _ _) (fun s h => largs_le hAe hsh h.1 2 (by decide)) (fun hle => ?_)
    (fun _ _ _ _ h => by simp [declared, SessionStore.ifs] at h)
    (fun hle => frag_nil o fun s h => by
      rw [if_neg (show ¬(A ≤ 2 ∧ _) from fun h' => by have := of_decide_eq_false hle; omega)]; exact h.1)
    (fun _ _ _ _ h => by simp [declared] at h)
  have h12 : 1 ≤ A ∧ A ≤ 2 := ⟨by omega, of_decide_eq_true hle⟩
  refine frag_append (f1 h12) (frag_conseq (f2 h12) (fun _ h => h) fun u h => ?_)
  have e1 : (if decide (A = 1) || rok then (if gnm = true then (if gl = true then 30 else 25) else 7) else 7) =
      if A ≤ 2 ∧ (A = 1 ∨ rok = true) then (if gnm = true then (if gl = true then 30 else 25) else 7) else 7 := by
    by_cases h1 : A = 1
    · rw [if_pos (show (decide (A = 1) || rok) = true by simp [h1]),
        if_pos (show A ≤ 2 ∧ (A = 1 ∨ rok = true) from ⟨by omega, Or.inl h1⟩)]
    · cases rok
      · rw [if_neg (show ¬(decide (A = 1) || false) = true by simp [h1]),
          if_neg (show ¬(A ≤ 2 ∧ (A = 1 ∨ false = true)) by simp [h1])]
      · rw [if_pos (show (decide (A = 1) || true) = true by simp),
          if_pos (show A ≤ 2 ∧ (A = 1 ∨ true = true) from ⟨by omega, Or.inr rfl⟩)]
  rw [← e1]; exact h

/-- LIST's reply's code. -/
theorem ans_list (args : List (List Byte)) : Session.replyCode (CommandSpec.answerIn .list args) =
    if args.length = 0 then 32
    else if (args.getD 0 []).map CommandSpec.upper = CommandSpec.ascii "OVERVIEW.FMT" then
      (if args.length = 1 then 48 else 7)
    else if (args.getD 0 []).map CommandSpec.upper = CommandSpec.ascii "HEADERS" then
      (if args.length = 1 ∨ (args.length = 2 ∧ ((args.getD 1 []).map CommandSpec.upper = CommandSpec.ascii "MSGID" ∨
        (args.getD 1 []).map CommandSpec.upper = CommandSpec.ascii "RANGE")) then 49 else 7)
    else if args.length ≤ 2 ∧ (args.length = 1 ∨ (CommandSpec.wildmat? (args.getD 1 [])).isSome = true) then
      (if (args.getD 0 []).map CommandSpec.upper = CommandSpec.ascii "ACTIVE" then 32
       else if (args.getD 0 []).map CommandSpec.upper = CommandSpec.ascii "NEWSGROUPS" then 33 else 7)
    else 7 := by
  have d1 : CommandSpec.ascii "HEADERS" ≠ CommandSpec.ascii "OVERVIEW.FMT" := by decide
  have d2 : CommandSpec.ascii "ACTIVE" ≠ CommandSpec.ascii "OVERVIEW.FMT" := by decide
  have d3 : CommandSpec.ascii "ACTIVE" ≠ CommandSpec.ascii "HEADERS" := by decide
  have d4 : CommandSpec.ascii "NEWSGROUPS" ≠ CommandSpec.ascii "OVERVIEW.FMT" := by decide
  have d5 : CommandSpec.ascii "NEWSGROUPS" ≠ CommandSpec.ascii "HEADERS" := by decide
  have d6 : CommandSpec.ascii "NEWSGROUPS" ≠ CommandSpec.ascii "ACTIVE" := by decide
  rcases args with _ | ⟨k, _ | ⟨a, _ | ⟨x, rest⟩⟩⟩
  · rfl
  · simp only [CommandSpec.answerIn]
    by_cases h1 : k.map CommandSpec.upper = CommandSpec.ascii "OVERVIEW.FMT"
    · simp [*, Session.replyCode]
    · by_cases h2 : k.map CommandSpec.upper = CommandSpec.ascii "HEADERS"
      · simp [*, Session.replyCode]
      · by_cases h3 : k.map CommandSpec.upper = CommandSpec.ascii "ACTIVE" <;>
          by_cases h4 : k.map CommandSpec.upper = CommandSpec.ascii "NEWSGROUPS" <;> simp [*, Session.replyCode]
  · simp only [CommandSpec.answerIn]
    by_cases h1 : k.map CommandSpec.upper = CommandSpec.ascii "OVERVIEW.FMT"
    · simp [*, Session.replyCode]
    · by_cases h2 : k.map CommandSpec.upper = CommandSpec.ascii "HEADERS"
      · by_cases h5 : a.map CommandSpec.upper = CommandSpec.ascii "MSGID" <;>
          by_cases h6 : a.map CommandSpec.upper = CommandSpec.ascii "RANGE" <;> simp [*, Session.replyCode]
      · cases hw : CommandSpec.wildmat? a <;>
          by_cases h3 : k.map CommandSpec.upper = CommandSpec.ascii "ACTIVE" <;>
          by_cases h4 : k.map CommandSpec.upper = CommandSpec.ascii "NEWSGROUPS" <;>
          simp [*, Session.replyCode]
  · simp only [CommandSpec.answerIn]
    by_cases h1 : k.map CommandSpec.upper = CommandSpec.ascii "OVERVIEW.FMT"
    · simp [*, Session.replyCode]
    · by_cases h2 : k.map CommandSpec.upper = CommandSpec.ascii "HEADERS"
      · simp [*, Session.replyCode]
      · simp [*, Session.replyCode]

/-- **LIST HEADERS's arguments**: one, or a second word MSGID or RANGE in any case. -/
theorem hdrs_frag (o : Oracle σ) {b : Word} {ci K : Nat} {L : List Byte} {e : PancakeState σ}
    (he : VEntry b ci K L e) (hsh : L.length < 2 ^ 62) {A : Nat} (hAe : A = (spans L).length - 1) :
    Frag o headersTree (LAt b ci L e) (LAtR (if A = 1 then 49 else
      if A = 2 ∧ ((cut L ((spans L).getD 2 (0, 0))).map CommandSpec.upper = texts.getD Session.tMsgid [] ∨
        (cut L ((spans L).getD 2 (0, 0))).map CommandSpec.upper = texts.getD Session.tRange []) then 49 else 7)
      b ci L e) := by
  have ev : ∀ {R} u, LAtR R b ci L e u → ∀ k, k < 2 ^ 63 → _ := fun u h k hk => largs_eq hAe hsh h k hk
  let w := cut L ((spans L).getD 2 (0, 0))
  let mid := decide (w.map CommandSpec.upper = texts.getD Session.tMsgid [])
  let rng := decide (w.map CommandSpec.upper = texts.getD Session.tRange [])
  have f1 : Frag o [SessionStore.ifs (Syntax.eEq (Syntax.v "args") (Syntax.n 1)) [fsay .headerList]] (LAt b ci L e)
      (LAtR (if A = 1 then 49 else 7) b ci L e) := by
    refine frag_ite o (C := .cmp .equal (.var "args") (.const (BitVec.ofNat 64 1))) rfl (fat_clock _ _ _ _)
      (fun s h => ⟨_, ev s h 1 (by decide)⟩) ?_ (fun _ _ _ _ h => by simp [declared, fsay] at h)
      (frag_nil o fun s ⟨h, hc⟩ => ?_) (fun _ _ _ _ h => by simp [declared] at h)
    · refine frag_pure (A = 1) (fun s ⟨h, hc⟩ => by
        rw [ev s h 1 (by decide)] at hc; exact of_decide_eq_true (bw_ne0 hc))
        (lowK_any _ (k := .skip) (c := _) rfl) fun h1 => ?_
      rw [if_pos h1]
      exact frag_conseq (lsayR_frag o .headerList (Q := fun _ => True) true_clock fun _ _ _ => trivial)
        (fun s h => ⟨h.1, trivial⟩) fun _ h => h.1
    · rw [ev s h 1 (by decide)] at hc
      rw [if_neg (of_decide_eq_false (bw_eq0 hc))]; exact h
  refine frag_append (xs := [_]) f1 ?_
  refine frag_ite o (C := .cmp .equal (.var "args") (.const (BitVec.ofNat 64 2))) rfl (fat_clock _ _ _ _)
    (fun s h => ⟨_, ev s h 2 (by decide)⟩) ?_
    (fun _ _ _ _ h => by simp [declared, fsay, Session.wordIsAt, SessionStore.ifs] at h)
    (frag_nil o fun s ⟨h, hc⟩ => ?_) (fun _ _ _ _ h => by simp [declared] at h)
  · refine frag_pure (A = 2) (fun s ⟨h, hc⟩ => by
      rw [ev s h 2 (by decide)] at hc; exact of_decide_eq_true (bw_ne0 hc))
      (lowKK_append (lowKK_append (lowKK_append (wordIsAt_low "s2" "l2" (by rw [texts_length]; decide))
        (lowK_any _ (k := .skip) (c := _) rfl)) (wordIsAt_low "s2" "l2" (by rw [texts_length]; decide)))
        (lowK_any _ (k := .skip) (c := _) rfl)) fun h2 => ?_
    have hn1 : ¬A = 1 := by omega
    simp only [if_neg hn1]
    refine frag_append (frag_append (frag_append (frag_conseq (lcmp2_frag o (R := 7) he (by omega)
      (t := Session.tMsgid) (by rw [texts_length]; decide)) (fun s h => ⟨h.1, trivial⟩)
        fun _ h => ⟨h.1, h.2.2, trivial⟩)
      (lsayIfR_frag o "eqk" .headerList (R0 := 7) (p := mid) true_clock (fun _ _ _ => trivial)))
      (frag_conseq (lcmp2_frag o (R := if mid = true then Session.replyCode .headerList else 7) he (by omega)
        (t := Session.tRange) (by rw [texts_length]; decide)) (fun s h => h) fun _ h => ⟨h.1, h.2.2, trivial⟩))
      (frag_conseq (lsayIfR_frag o "eqk" .headerList (p := rng) true_clock (fun _ _ _ => trivial)) (fun _ h => h)
        fun u h => ?_)
    have e : (if rng = true then Session.replyCode .headerList else if mid = true then Session.replyCode .headerList
        else 7) = if A = 2 ∧ (w.map CommandSpec.upper = texts.getD Session.tMsgid [] ∨
          w.map CommandSpec.upper = texts.getD Session.tRange []) then 49 else 7 := by
      simp only [rng, mid, decide_eq_true_eq, h2, true_and]
      by_cases hm : w.map CommandSpec.upper = texts.getD Session.tMsgid []
      · by_cases hr : w.map CommandSpec.upper = texts.getD Session.tRange []
        · rw [if_pos hr, if_pos (Or.inl hm)]; rfl
        · rw [if_neg hr, if_pos hm, if_pos (Or.inl hm)]; rfl
      · by_cases hr : w.map CommandSpec.upper = texts.getD Session.tRange []
        · rw [if_pos hr, if_pos (Or.inr hr)]; rfl
        · rw [if_neg hr, if_neg hm, if_neg (fun h => h.elim hm hr)]
    rw [← e]; exact h.1
  · rw [ev s h 2 (by decide)] at hc
    have hn2 := of_decide_eq_false (bw_eq0 hc)
    by_cases h1 : A = 1
    · rw [if_pos h1] at h ⊢; exact h
    · rw [if_neg h1] at h ⊢; rw [if_neg (fun hh => hn2 hh.1)]; exact h

/-- **LIST ACTIVE's and NEWSGROUPS's arguments**: none, or the keyword and a wildmat or nothing. -/
theorem active_frag (o : Oracle σ) {b : Word} {ci K : Nat} {L : List Byte} {e : PancakeState σ}
    (he : VEntry b ci K L e) (hsh : L.length < 2 ^ 62) {A : Nat} (hAe : A = (spans L).length - 1) :
    Frag o activeTree (fun u => LAt b ci L e u ∧ u.locals "ok" = some 1) (LAtR (if A = 0 then 32 else
      if A ≤ 2 ∧ (A = 1 ∨ (CommandSpec.wildmat? (cut L ((spans L).getD 2 (0, 0)))).isSome = true) then
        (if (cut L ((spans L).getD 1 (0, 0))).map CommandSpec.upper = texts.getD Session.tActive [] then 32
         else if (cut L ((spans L).getD 1 (0, 0))).map CommandSpec.upper = texts.getD Session.tNewsgroups [] then 33
         else 7) else 7) b ci L e) := by
  have ev : ∀ {R} u, LAtR R b ci L e u → ∀ k, k < 2 ^ 63 → _ := fun u h k hk => largs_eq hAe hsh h k hk
  have hle2 : ∀ u, LAt b ci L e u → _ := fun u h => largs_le hAe hsh h 2 (by decide)
  obtain ⟨wm, hwm⟩ : ∃ x, x = (CommandSpec.wildmat? (cut L ((spans L).getD 2 (0, 0)))).isSome := ⟨_, rfl⟩
  let w1 := cut L ((spans L).getD 1 (0, 0))
  obtain ⟨act, hact⟩ : ∃ x, x = decide (w1.map CommandSpec.upper = texts.getD Session.tActive []) := ⟨_, rfl⟩
  obtain ⟨ngs, hngs⟩ : ∃ x, x = decide (w1.map CommandSpec.upper = texts.getD Session.tNewsgroups []) := ⟨_, rfl⟩
  have hdis : act = true → ngs = false := fun ha => by
    rw [hact, decide_eq_true_eq] at ha
    rw [hngs, decide_eq_false_iff_not, ha]; decide
  let M : Assn σ := fun u => LAt b ci L e u ∧ u.locals "ok" = some (bw (decide (A = 1) || wm))
  have hMc : Safe.ClockFree M := fat_and fun _ _ h => h
  have hds : ∀ y ∈ declared (Session.wildmatCheck ++ [fset ownWs (Syntax.v "s2"), fset ownWl (Syntax.v "l2")]),
      (y ∈ lNames ∧ y ∉ fFixed ∧ y ∉ lBound) ∧ y ≠ "ok" := by
    rw [show declared (Session.wildmatCheck ++ [fset ownWs (Syntax.v "s2"), fset ownWl (Syntax.v "l2")]) =
      ["nd", "clo", "chi", "items", "bang"] from rfl]; decide
  have fW : ∀ {P : Assn σ}, (∀ u, P u → LAt b ci L e u ∧ u.locals "ok" = some 1 ∧ 1 ≤ A ∧ A ≤ 2) →
      Frag o [SessionStore.ifs (Syntax.eEq (Syntax.v "args") (Syntax.n 2))
        (Session.wildmatCheck ++ [fset ownWs (Syntax.v "s2"), fset ownWl (Syntax.v "l2")])] P M := fun {P} hP => by
    refine frag_ite o (C := .cmp .equal (.var "args") (.const (BitVec.ofNat 64 2))) rfl hMc
      (fun s h => ⟨_, ev s (hP s h).1 2 (by decide)⟩) ?_ (fun u y v h hy => ⟨fat_restore h.1 (hds y hy).1 v, by
        simp only [restore, resVar, if_neg (Ne.symm (hds y hy).2)]; exact h.2⟩)
      (frag_nil o fun s ⟨h, hc⟩ => ?_) (fun _ _ _ _ h => by simp [declared] at h)
    · refine frag_pure (A = 2) (fun s ⟨h, hc⟩ => by
        rw [ev s (hP s h).1 2 (by decide)] at hc; exact of_decide_eq_true (bw_ne0 hc))
        (lowKK_append (lowK_any _ (k := .skip) (c := _) rfl) (lowKK_append (xs := [_])
          (lowKK_one rfl (fset_lower rfl)) (lowKK_one rfl (fset_lower rfl)))) fun hA2 => ?_
      have hok : ∀ u, LAt b ci L e u ∧ u.locals "ok" = some (bw wm) → M u := fun u h =>
        ⟨h.1, by rw [h.2, hA2]; rfl⟩
      let Q : Assn σ := fun u => u.locals "ok" = some (bw (decide (A = 1) || wm))
      have sw : ∀ (X : Nat) (hX : X ∈ lOffs) (x : String) (hx : ∀ u, LAt b ci L e u → ∃ v, u.locals x = some v),
          Frag o [fset X (Syntax.v x)] M M := fun X hX x hx =>
        lsetR_frag o he hX (E := .var x) rfl (Q := Q) (fun _ _ h => h) (fun _ _ h => h) fun u h _ => hx u h
      refine frag_append (frag_conseq (lwm_frag o (R := Session.replyCode .syntax) he (by omega))
        (fun s h => ⟨(hP s h.1).1, (hP s h.1).2.1⟩) fun u h => hok u ⟨h.1, hwm ▸ h.2⟩) (frag_append (xs := [_])
          (sw ownWs (by decide) "s2" fun u h => ⟨_, h.s2⟩) (sw ownWl (by decide) "l2" fun u h => ⟨_, h.l2⟩))
    · rw [ev s (hP s h).1 2 (by decide)] at hc
      have hn2 := of_decide_eq_false (bw_eq0 hc)
      have h1 : A = 1 := by have := (hP s h).2.2; omega
      exact ⟨(hP s h).1, by rw [(hP s h).2.1, h1]; rfl⟩
  -- the keyword, where the wildmat is good
  have fC : Frag o [SessionStore.ifs (Syntax.v "ok") (Session.wordIsAt "s1" "l1" Session.tActive ++
      [SessionStore.ifs (Syntax.v "eqk") [fsay (.active none)]] ++ Session.wordIsAt "s1" "l1" Session.tNewsgroups ++
      [SessionStore.ifs (Syntax.v "eqk") [fsay .newsgroups]])] (fun u => M u ∧ 1 ≤ A)
      (LAtR (if (decide (A = 1) || wm) then (if ngs then 33 else if act then 32 else 7) else 7) b ci L e) := by
    refine frag_ite o (C := .var "ok") rfl (fat_clock _ _ _ _) (fun s h => ⟨_, h.1.2⟩) ?_
      (fun _ _ _ _ h => by simp [declared, fsay, Session.wordIsAt, SessionStore.ifs] at h)
      (frag_nil o fun s ⟨h, hc⟩ => ?_) (fun _ _ _ _ h => by simp [declared] at h)
    · refine frag_pure ((decide (A = 1) || wm) = true ∧ 1 ≤ A) (fun s ⟨h, hc⟩ => by
        simp only [eval, h.1.2] at hc; exact ⟨bw_ne0 hc, h.2⟩)
        (lowKK_append (lowKK_append (lowKK_append (wordIsAt_low "s1" "l1" (by rw [texts_length]; decide))
          (lowK_any _ (k := .skip) (c := _) rfl)) (wordIsAt_low "s1" "l1" (by rw [texts_length]; decide)))
          (lowK_any _ (k := .skip) (c := _) rfl)) fun ⟨hok, hA1⟩ => ?_
      rw [if_pos hok]
      refine frag_append (frag_append (frag_append (frag_conseq (lcmp1_frag o (R := Session.replyCode .syntax) he
        (by omega) (t := Session.tActive) (by rw [texts_length]; decide) (Q := fun _ => True) fun _ _ _ _ => trivial)
        (fun s h => ⟨h.1.1.1, trivial⟩) fun _ h => ⟨h.1, hact ▸ h.2.2, trivial⟩)
        (lsayIfR_frag o "eqk" (.active none) (p := act) true_clock (fun _ _ _ => trivial)))
        (frag_conseq (lcmp1_frag o (R := if act then Session.replyCode (.active none) else 7) he (by omega)
          (t := Session.tNewsgroups) (by rw [texts_length]; decide) (Q := fun _ => True) fun _ _ _ _ => trivial)
          (fun s h => h) fun _ h => ⟨h.1, hngs ▸ h.2.2, trivial⟩))
        (frag_conseq (lsayIfR_frag o "eqk" .newsgroups (p := ngs) true_clock (fun _ _ _ => trivial)) (fun _ h => h)
          fun u h => h.1)
    · simp only [eval, h.1.2] at hc
      rw [if_neg (by rw [bw_eq0 hc]; decide)]
      exact h.1.1
  refine frag_ite o (C := .cmp .equal (.var "args") (.const (BitVec.ofNat 64 0))) rfl (fat_clock _ _ _ _)
    (fun s h => ⟨_, ev s h.1 0 (by decide)⟩) ?_ (fun _ _ _ _ h => by simp [declared, fsay] at h) ?_
    (fun _ _ _ _ h => by simp [declared, SessionStore.ifs] at h)
  · refine frag_pure (A = 0) (fun s ⟨h, hc⟩ => by
      rw [ev s h.1 0 (by decide)] at hc; exact of_decide_eq_true (bw_ne0 hc))
      (lowK_any _ (k := .skip) (c := _) rfl) fun hA0 => ?_
    rw [if_pos hA0]
    exact frag_conseq (lsayR_frag o (.active none) (Q := fun _ => True) true_clock (fun _ _ _ => trivial))
      (fun s h => ⟨h.1.1, trivial⟩) fun _ h => h.1
  refine frag_ite o (C := leE (.var "args") (.const (BitVec.ofNat 64 2))) rfl (fat_clock _ _ _ _)
    (fun s h => ⟨_, hle2 s h.1.1⟩) ?_ (fun _ _ _ _ h => by simp [declared, SessionStore.ifs] at h)
    (frag_nil o fun s ⟨h, hc⟩ => ?_) (fun _ _ _ _ h => by simp [declared] at h)
  · refine frag_pure (1 ≤ A ∧ A ≤ 2) (fun s ⟨⟨h, hc0⟩, hc⟩ => by
      rw [ev s h.1 0 (by decide)] at hc0; rw [hle2 s h.1] at hc
      have := of_decide_eq_false (bw_eq0 hc0); have := of_decide_eq_true (bw_ne0 hc)
      omega) (lowKK_append (lowK_any _ (k := .skip) (c := _) rfl) (lowKK_ite rfl (lowKK_append (lowKK_append
        (lowKK_append (wordIsAt_low "s1" "l1" (by rw [texts_length]; decide)) (lowK_any _ (k := .skip) (c := _) rfl))
        (wordIsAt_low "s1" "l1" (by rw [texts_length]; decide))) (lowK_any _ (k := .skip) (c := _) rfl))
          fun k => ⟨k, rfl⟩)) fun h12 => ?_
    refine frag_append (fW fun u h => ⟨h.1.1.1, h.1.1.2, h12⟩) (frag_conseq fC (fun s h => ⟨h, h12.1⟩) fun u h => ?_)
    have e : (if (decide (A = 1) || wm) then (if ngs then 33 else if act then 32 else 7) else 7) =
        (if A = 0 then 32 else if A ≤ 2 ∧ (A = 1 ∨ (CommandSpec.wildmat? (cut L ((spans L).getD 2 (0, 0)))).isSome =
          true) then (if w1.map CommandSpec.upper = texts.getD Session.tActive [] then 32
            else if w1.map CommandSpec.upper = texts.getD Session.tNewsgroups [] then 33 else 7) else 7) := by
      rw [if_neg (show ¬A = 0 by omega), ← hwm]
      have hc2 : (A ≤ 2 ∧ (A = 1 ∨ wm = true)) ↔ (decide (A = 1) || wm) = true := by
        constructor
        · rintro ⟨-, h | h⟩ <;> simp [h]
        · intro h; simp only [Bool.or_eq_true, decide_eq_true_eq] at h; exact ⟨h12.2, h⟩
      by_cases hc : (decide (A = 1) || wm) = true
      · rw [if_pos hc, if_pos (hc2.mpr hc)]
        cases ha : act
        · have na : ¬w1.map CommandSpec.upper = texts.getD Session.tActive [] := fun e => by
            rw [hact, decide_eq_false_iff_not] at ha; exact ha e
          rw [if_neg na]
          cases hn : ngs
          · have nn : ¬w1.map CommandSpec.upper = texts.getD Session.tNewsgroups [] := fun e => by
              rw [hngs, decide_eq_false_iff_not] at hn; exact hn e
            rw [if_neg nn]; rfl
          · have yn : w1.map CommandSpec.upper = texts.getD Session.tNewsgroups [] := by
              rw [hngs, decide_eq_true_eq] at hn; exact hn
            rw [if_pos yn]; rfl
        · have ya : w1.map CommandSpec.upper = texts.getD Session.tActive [] := by
            rw [hact, decide_eq_true_eq] at ha; exact ha
          rw [if_pos ya, hdis ha]; rfl
      · rw [if_neg hc, if_neg (fun h => hc (hc2.mp h))]
    rw [← e]; exact h
  · rw [hle2 s h.1.1] at hc
    have h3 := of_decide_eq_false (bw_eq0 hc)
    rw [if_neg (by rw [ev s h.1.1 0 (by decide)] at *; omega), if_neg (by omega)]
    exact h.1.1

/-- **LIST's branch**: if it goes on, the code of the reply `answerIn` gives. -/
theorem list_frag (o : Oracle σ) {b : Word} {ci K : Nat} {L : List Byte} {e : PancakeState σ}
    (he : VEntry b ci K L e) (hsh : L.length < 2 ^ 62) :
    Frag o listTree (LPre b ci L e) (LAtR (Session.replyCode (CommandSpec.answerIn .list (argsOf L))) b ci L e) := by
  obtain ⟨A, hAe⟩ : ∃ A, A = (spans L).length - 1 := ⟨_, rfl⟩
  obtain ⟨w1, hw1⟩ : ∃ w, w = cut L ((spans L).getD 1 (0, 0)) := ⟨_, rfl⟩
  obtain ⟨w2, hw2⟩ : ∃ w, w = cut L ((spans L).getD 2 (0, 0)) := ⟨_, rfl⟩
  obtain ⟨fmt, hfmt⟩ : ∃ x, x = decide (w1.map CommandSpec.upper = texts.getD Session.tOverviewFmt []) := ⟨_, rfl⟩
  obtain ⟨hdr, hhdr⟩ : ∃ x, x = decide (w1.map CommandSpec.upper = texts.getD Session.tHeaders []) := ⟨_, rfl⟩
  have ev : ∀ {R} u, LAtR R b ci L e u → ∀ k, k < 2 ^ 63 → _ := fun u h k hk => largs_eq hAe hsh h k hk
  -- the spec in the program's terms
  have hR : Session.replyCode (CommandSpec.answerIn .list (argsOf L)) =
      if 1 ≤ A ∧ fmt = true then (if A = 1 then 48 else 7)
      else if 1 ≤ A ∧ hdr = true then
        (if A = 1 then 49 else if A = 2 ∧ (w2.map CommandSpec.upper = texts.getD Session.tMsgid [] ∨
          w2.map CommandSpec.upper = texts.getD Session.tRange []) then 49 else 7)
      else (if A = 0 then 32 else if A ≤ 2 ∧ (A = 1 ∨ (CommandSpec.wildmat? w2).isSome = true) then
        (if w1.map CommandSpec.upper = texts.getD Session.tActive [] then 32
         else if w1.map CommandSpec.upper = texts.getD Session.tNewsgroups [] then 33 else 7) else 7) := by
    rw [ans_list, largs_len, argsOf_head, argsOf_second, ← hAe, ← hw1, ← hw2]
    rw [show CommandSpec.ascii "OVERVIEW.FMT" = texts.getD Session.tOverviewFmt [] from rfl,
      show CommandSpec.ascii "HEADERS" = texts.getD Session.tHeaders [] from rfl,
      show CommandSpec.ascii "MSGID" = texts.getD Session.tMsgid [] from rfl,
      show CommandSpec.ascii "RANGE" = texts.getD Session.tRange [] from rfl,
      show CommandSpec.ascii "ACTIVE" = texts.getD Session.tActive [] from rfl,
      show CommandSpec.ascii "NEWSGROUPS" = texts.getD Session.tNewsgroups [] from rfl]
    by_cases h0 : A = 0
    · rw [if_pos h0, if_neg (show ¬(1 ≤ A ∧ fmt = true) from fun h => by omega),
        if_neg (show ¬(1 ≤ A ∧ hdr = true) from fun h => by omega), if_pos h0]
    · have h1 : 1 ≤ A := by omega
      rw [if_neg h0]
      by_cases hf : w1.map CommandSpec.upper = texts.getD Session.tOverviewFmt []
      · rw [if_pos hf, if_pos (show 1 ≤ A ∧ fmt = true from ⟨h1, by rw [hfmt]; exact decide_eq_true hf⟩)]
      · rw [if_neg hf, if_neg (show ¬(1 ≤ A ∧ fmt = true) from fun h => hf (by
          have := h.2; rw [hfmt] at this; exact of_decide_eq_true this))]
        by_cases hh : w1.map CommandSpec.upper = texts.getD Session.tHeaders []
        · rw [if_pos hh, if_pos (show 1 ≤ A ∧ hdr = true from ⟨h1, by rw [hhdr]; exact decide_eq_true hh⟩)]
          by_cases ha1 : A = 1
          · rw [if_pos (show A = 1 ∨ _ from Or.inl ha1), if_pos ha1]
          · rw [if_neg ha1]
            by_cases hm : A = 2 ∧ (w2.map CommandSpec.upper = texts.getD Session.tMsgid [] ∨
                w2.map CommandSpec.upper = texts.getD Session.tRange [])
            · rw [if_pos (show A = 1 ∨ _ from Or.inr hm), if_pos hm]
            · rw [if_neg (show ¬(A = 1 ∨ _) from fun h => h.elim ha1 hm), if_neg hm]
        · rw [if_neg hh, if_neg (show ¬(1 ≤ A ∧ hdr = true) from fun h => hh (by
            have := h.2; rw [hhdr] at this; exact of_decide_eq_true this)), if_neg h0]
  subst hw1 hw2
  have h1x : ∀ {R} u, LAtR R b ci L e u → _ := fun u h => largs_ge hAe hsh h 1 (by decide)
  -- the wildmat's place cleared
  let Q0 : Assn σ := fun u => u.locals "ok" = some 1 ∧ u.locals "lo" = some 1 ∧
    u.locals "hi" = some (BitVec.ofNat 64 CommandSpec.numberMax)
  have fa : Frag o [fset ownWs (Syntax.n 0), fset ownWl (Syntax.n 0)] (LPre b ci L e) (LPre b ci L e) :=
    frag_append (xs := [_]) (lsetR_frag o he (X := ownWs) (by decide) (E := .const (BitVec.ofNat 64 0)) rfl (Q := Q0)
      (fun _ _ h => h) (fun _ _ h => h) fun _ _ _ => ⟨_, rfl⟩)
      (lsetR_frag o he (X := ownWl) (by decide) (E := .const (BitVec.ofNat 64 0)) rfl (Q := Q0)
        (fun _ _ h => h) (fun _ _ h => h) fun _ _ _ => ⟨_, rfl⟩)
  -- `ovf` and `hdl` declared
  let N0 : Assn σ := fun u => LAt b ci L e u ∧ u.locals "ok" = some 1 ∧ u.locals "ovf" = some 0 ∧
    u.locals "hdl" = some 0
  have fb : Frag o [.dec "ovf" (Syntax.n 0), .dec "hdl" (Syntax.n 0)] (LPre b ci L e) N0 :=
    frag_append (xs := [_]) (frag_dec o (P' := fun u => LAt b ci L e u ∧ u.locals "ok" = some 1 ∧
      u.locals "ovf" = some 0) rfl fun s h => ⟨0, rfl, fat_set h.1 (by decide) 0, by simp [setLocal, h.2.1],
        by simp [setLocal]⟩)
      (frag_dec o rfl fun s h => ⟨0, rfl, fat_set h.1 (by decide) 0, by simp [setLocal, h.2.1],
        by simp [setLocal, h.2.2], by simp [setLocal]⟩)
  -- the first word's keyword
  let N1 : Assn σ := fun u => LAt b ci L e u ∧ u.locals "ok" = some 1 ∧
    u.locals "ovf" = some (bw (decide (1 ≤ A) && fmt)) ∧ u.locals "hdl" = some (bw (decide (1 ≤ A) && hdr))
  have fc : Frag o [SessionStore.ifs (Syntax.eLe (Syntax.n 1) (Syntax.v "args"))
      (Session.wordIsAt "s1" "l1" Session.tOverviewFmt ++ [.assign "ovf" (Syntax.v "eqk")] ++
        Session.wordIsAt "s1" "l1" Session.tHeaders ++ [.assign "hdl" (Syntax.v "eqk")])] N0 N1 := by
    have bq : ∀ (P : Assn σ), (∀ u u', P u → (∀ y, y ≠ "eqk" → y ≠ "jq" → u'.locals y = u.locals y) → P u') →
        ∀ u u', P u → SessionCheck.ButFor ["eqk", "jq"] u u' → P u' := fun P hP u u' h hb =>
      hP u u' h fun y h1 h2 => hb.locals y (by simp [h1, h2])
    refine frag_ite o rfl (fat_and fun _ _ h => h) (fun s h => ⟨_, h1x s h.1⟩) ?_
      (fun _ _ _ _ h => by simp [declared, Session.wordIsAt] at h)
      (frag_nil o fun s ⟨h, hc⟩ => ?_) (fun _ _ _ _ h => by simp [declared] at h)
    · refine frag_pure (1 ≤ A) (fun s ⟨h, hc⟩ => by
        rw [h1x s h.1] at hc; exact of_decide_eq_true (bw_ne0 hc))
        (lowKK_append (lowKK_append (lowKK_append (wordIsAt_low "s1" "l1" (by rw [texts_length]; decide))
          (lowK_any _ (k := .skip) (c := _) rfl)) (wordIsAt_low "s1" "l1" (by rw [texts_length]; decide)))
          (lowK_any _ (k := .skip) (c := _) rfl)) fun hA1 => ?_
      have h2 : 2 ≤ (spans L).length := by omega
      refine frag_conseq (frag_append (frag_append (frag_append
        (lcmp1_frag o (R := Session.replyCode .syntax) he h2 (t := Session.tOverviewFmt) (by rw [texts_length]; decide)
          (Q := fun u => u.locals "ok" = some 1 ∧ u.locals "ovf" = some 0 ∧ u.locals "hdl" = some 0)
          (bq _ fun u u' h hl => ⟨by rw [hl "ok" (by decide) (by decide)]; exact h.1,
            by rw [hl "ovf" (by decide) (by decide)]; exact h.2.1,
            by rw [hl "hdl" (by decide) (by decide)]; exact h.2.2⟩))
        (frag_one (a := .assign "ovf" (.var "eqk")) rfl rfl rfl
          (P' := fun u => LAt b ci L e u ∧ u.locals "ok" = some 1 ∧ u.locals "ovf" = some (bw fmt) ∧
            u.locals "hdl" = some 0) (fat_and fun _ _ h => h) (Safe.assign fun u ⟨h, ⟨hok, ho, hh⟩, hk⟩ =>
              ⟨_, _, by simp only [eval]; exact hk, ho, fat_set h (by decide) _, by simp [setLocal, hok],
                by simp [setLocal, hfmt], by simp [setLocal, hh]⟩)))
        (lcmp1_frag o (R := Session.replyCode .syntax) he h2 (t := Session.tHeaders) (by rw [texts_length]; decide)
          (Q := fun u => u.locals "ok" = some 1 ∧ u.locals "ovf" = some (bw fmt) ∧ u.locals "hdl" = some 0)
          (bq _ fun u u' h hl => ⟨by rw [hl "ok" (by decide) (by decide)]; exact h.1,
            by rw [hl "ovf" (by decide) (by decide)]; exact h.2.1,
            by rw [hl "hdl" (by decide) (by decide)]; exact h.2.2⟩)))
        (frag_one (a := .assign "hdl" (.var "eqk")) rfl rfl rfl
          (P' := fun u => LAt b ci L e u ∧ u.locals "ok" = some 1 ∧ u.locals "ovf" = some (bw fmt) ∧
            u.locals "hdl" = some (bw hdr)) (fat_and fun _ _ h => h) (Safe.assign fun u ⟨h, ⟨hok, ho, hh⟩, hk⟩ =>
              ⟨_, _, by simp only [eval]; exact hk, hh, fat_set h (by decide) _, by simp [setLocal, hok],
                by simp [setLocal, ho], by simp [setLocal, hhdr]⟩)))
        (fun s h => h.1) fun u h => ⟨h.1, h.2.1, by rw [h.2.2.1, decide_eq_true hA1]; rfl,
          by rw [h.2.2.2, decide_eq_true hA1]; rfl⟩
    · rw [h1x s h.1] at hc
      have hA0 := of_decide_eq_false (bw_eq0 hc)
      exact ⟨h.1, h.2.1, by rw [h.2.2.1, decide_eq_false hA0]; rfl, by rw [h.2.2.2, decide_eq_false hA0]; rfl⟩
  -- the branches on the keyword
  have fd : Frag o [.ite (Syntax.v "ovf") [SessionStore.ifs (Syntax.eEq (Syntax.v "args") (Syntax.n 1))
      [fsay .overviewFmt]] [.ite (Syntax.v "hdl") headersTree activeTree]] N1
      (LAtR (Session.replyCode (CommandSpec.answerIn .list (argsOf L))) b ci L e) := by
    rw [hR]
    have cf : ∀ x : Bool, (decide (1 ≤ A) && x) = true ↔ (1 ≤ A ∧ x = true) := fun x => by simp
    refine frag_bw o (C := .var "ovf") rfl (lowK_any _ (k := .skip) (c := _) rfl)
      (lowKK_ite rfl lowKK_headers lowKK_active) (fat_clock _ _ _ _) (fun s h => by simp only [eval]; exact h.2.2.1)
      (fun hf => ?_) (fun _ _ _ _ h => by simp [declared, SessionStore.ifs] at h) (fun hf => ?_)
      (fun _ _ _ _ h => by simp [declared] at h)
    · rw [if_pos ((cf fmt).mp hf)]
      refine frag_bw o (C := .cmp .equal (.var "args") (.const (BitVec.ofNat 64 1))) rfl
        (lowK_any _ (k := .skip) (c := _) rfl) (fun k => ⟨k, rfl⟩) (fat_clock _ _ _ _)
        (fun s h => ev s h.1 1 (by decide)) (fun h1 => ?_) (fun _ _ _ _ h => by simp [declared, fsay] at h)
        (fun h1 => frag_nil o fun s h => by rw [if_neg (of_decide_eq_false h1)]; exact h.1)
        (fun _ _ _ _ h => by simp [declared] at h)
      rw [if_pos (of_decide_eq_true h1)]
      exact frag_conseq (lsayR_frag o .overviewFmt (Q := fun _ => True) true_clock fun _ _ _ => trivial)
        (fun s h => ⟨h.1, trivial⟩) fun _ h => h.1
    · rw [if_neg (fun h => by rw [(cf fmt).mpr h] at hf; exact absurd hf (by decide))]
      refine frag_bw o (C := .var "hdl") rfl lowKK_headers lowKK_active (fat_clock _ _ _ _)
        (fun s h => by simp only [eval]; exact h.2.2.2) (fun hh => ?_)
        (fun _ _ _ _ h => by simp [declared, headersTree, SessionStore.ifs] at h) (fun hh => ?_)
        (fun _ _ _ _ h => by simp [declared, activeTree] at h)
      · rw [if_pos ((cf hdr).mp hh)]
        exact frag_conseq (hdrs_frag o he hsh hAe) (fun s h => h.1) fun _ h => h
      · rw [if_neg (fun h => by rw [(cf hdr).mpr h] at hh; exact absurd hh (by decide))]
        exact frag_conseq (active_frag o he hsh hAe) (fun s h => ⟨h.1, h.2.1⟩) fun _ h => h
  exact frag_append (xs := [_, _]) fa (frag_append (xs := [_, _]) fb (frag_append (xs := [_]) fc fd))

/-! ### `listClassify` whole -/

section Branches
variable {b : Word} {ci K : Nat} {L : List Byte} {e : PancakeState σ}

theorem lat_cmd (he : VEntry b ci K L e) {R : Nat} {u : PancakeState σ} (h : LAtR R b ci L e u) :
    u.locals "cmd" = some (BitVec.ofNat 64 K) := fcmd he h (by decide)

theorem lpre_restore {u : PancakeState σ} (h : LPre b ci L e u) {y : String}
    (hy : y ∈ lNames ∧ y ∉ fFixed ∧ y ∉ lBound) (v : Option Value) : LPre b ci L e (restore u y v) := by
  have n1 : y ≠ "ok" := fun e => hy.2.2 (by rw [e]; decide)
  have n2 : y ≠ "lo" := fun e => hy.2.2 (by rw [e]; decide)
  have n3 : y ≠ "hi" := fun e => hy.2.2 (by rw [e]; decide)
  refine ⟨fat_restore h.1 hy v, ?_, ?_, ?_⟩ <;> simp only [restore, resVar]
  · rw [if_neg (Ne.symm n1)]; exact h.2.1
  · rw [if_neg (Ne.symm n2)]; exact h.2.2.1
  · rw [if_neg (Ne.symm n3)]; exact h.2.2.2

/-- The branch of the command `listClassify` was called for. -/
theorem lhit_frag (o : Oracle σ) (he : VEntry b ci K L e) (hK : K < 2 ^ 63) {j : Nat} (hj : K = j)
    {T : List Syntax.PStmt} (hlow : LowKK T) {R : Nat} (hT : Frag o T (LPre b ci L e) (LAtR R b ci L e))
    (hdec : ∀ y ∈ declared T, y ∈ lNames ∧ y ∉ fFixed ∧ y ∉ lBound) :
    Frag o [SessionStore.ifs (Syntax.eEq (Syntax.v "cmd") (Syntax.n j)) T] (LPre b ci L e) (LAtR R b ci L e) :=
  frag_bw o (C := .cmp .equal (.var "cmd") (.const (BitVec.ofNat 64 j))) rfl hlow (fun k => ⟨k, rfl⟩)
    (fat_clock _ _ _ _) (fun s h => cmd_eval hK (lat_cmd he h.1) j (by omega)) (fun _ => hT)
    (fun u y v h hy => fat_restore h (hdec y hy) v)
    (fun hp => frag_nil o fun s h => absurd (of_decide_eq_false hp) (by simp [hj]))
    (fun _ _ _ _ h => by simp [declared] at h)

/-- Another command's branch, skipped. -/
theorem lmiss_frag (o : Oracle σ) (hK : K < 2 ^ 63) {j : Nat} (hj : K ≠ j) (hj63 : j < 2 ^ 63)
    {T : List Syntax.PStmt} (hlow : LowKK T) {P : Assn σ} (hPc : Safe.ClockFree P)
    (hcmd : ∀ u, P u → u.locals "cmd" = some (BitVec.ofNat 64 K))
    (hdec : ∀ u y v, P u → y ∈ declared T → P (restore u y v)) :
    Frag o [SessionStore.ifs (Syntax.eEq (Syntax.v "cmd") (Syntax.n j)) T] P P :=
  frag_skip o (C := .cmp .equal (.var "cmd") (.const (BitVec.ofNat 64 j))) rfl hlow hPc
    (fun s h => by rw [cmd_eval hK (hcmd s h) j hj63]; simp [hj, bw]) hdec

end Branches

theorem decl_lg : ∀ y ∈ declared lgTree, y ∈ lNames ∧ y ∉ fFixed ∧ y ∉ lBound := by
  rw [show declared lgTree = [] from rfl]; decide

theorem decl_list : ∀ y ∈ declared listTree, y ∈ lNames ∧ y ∉ fFixed ∧ y ∉ lBound := by
  rw [show declared listTree = ["ovf", "hdl"] from rfl]; decide

theorem decl_date : ∀ y ∈ declared dateTree, y ∈ lNames ∧ y ∉ fFixed ∧ y ∉ lBound := by
  rw [show declared dateTree = [] from rfl]; decide

theorem decl_ng : ∀ y ∈ declared ngTree, y ∈ lNames ∧ y ∉ fFixed ∧ y ∉ lBound := by
  rw [show declared ngTree = [] from rfl]; decide

theorem decl_mode : ∀ y ∈ declared modeTree, y ∈ lNames ∧ y ∉ fFixed ∧ y ∉ lBound := by
  rw [show declared modeTree = [] from rfl]; decide

/-- **`listClassify`'s branches on the command**: if they go on, the code of `answerIn`'s reply. -/
theorem lbranches_frag (o : Oracle σ) {b : Word} {ci : Nat} {L : List Byte} {e : PancakeState σ}
    {c : CommandSpec.Cmd} (hc : IsList c) (he : VEntry b ci (cmdCode (some c)) L e) (hgn : GnCode e.code)
    (hsh : L.length < 2 ^ 62) :
    Frag o listBranches (LPre b ci L e)
      (LAtR (Session.replyCode (CommandSpec.answerIn c (argsOf L))) b ci L e) := by
  have hK : cmdCode (some c) < 2 ^ 63 := by have := cmdCode_lt (some c); omega
  have pc : ∀ u, LPre b ci L e u → _ := fun u h => lat_cmd he h.1
  have pr : ∀ {T : List Syntax.PStmt}, (∀ y ∈ declared T, y ∈ lNames ∧ y ∉ fFixed ∧ y ∉ lBound) →
      ∀ u y v, LPre b ci L e u → y ∈ declared T → LPre b ci L e (restore u y v) := fun hd u y v h hy =>
    lpre_restore h (hd y hy) v
  have ac : ∀ {R} u, LAtR R b ci L e u → _ := fun u h => lat_cmd he h
  have ar : ∀ {T : List Syntax.PStmt} {R}, (∀ y ∈ declared T, y ∈ lNames ∧ y ∉ fFixed ∧ y ∉ lBound) →
      ∀ u y v, LAtR R b ci L e u → y ∈ declared T → LAtR R b ci L e (restore u y v) := fun hd u y v h hy =>
    fat_restore h (hd y hy) v
  have mp : ∀ {j T}, cmdCode (some c) ≠ j → j < 2 ^ 63 → LowKK T →
      (∀ y ∈ declared T, y ∈ lNames ∧ y ∉ fFixed ∧ y ∉ lBound) → Frag o [SessionStore.ifs (Syntax.eEq (Syntax.v "cmd")
        (Syntax.n j)) T] (LPre b ci L e) (LPre b ci L e) := fun hj h63 hl hd =>
    lmiss_frag o hK hj h63 hl (lpre_clock _ _ _ _) pc (pr hd)
  have ma : ∀ {j T R}, cmdCode (some c) ≠ j → j < 2 ^ 63 → LowKK T →
      (∀ y ∈ declared T, y ∈ lNames ∧ y ∉ fFixed ∧ y ∉ lBound) → Frag o [SessionStore.ifs (Syntax.eEq (Syntax.v "cmd")
        (Syntax.n j)) T] (LAtR R b ci L e) (LAtR R b ci L e) := fun hj h63 hl hd =>
    lmiss_frag o hK hj h63 hl (fat_clock _ _ _ _) ac (ar hd)
  rcases hc with rfl | rfl | rfl | rfl | rfl
  · exact frag_append (xs := [_]) (lhit_frag o he hK rfl lowKK_lg (lg_frag o he hgn hsh) decl_lg)
      (frag_append (xs := [_]) (ma (by decide) (by decide) lowKK_list decl_list)
      (frag_append (xs := [_]) (ma (by decide) (by decide) lowKK_date decl_date)
      (frag_append (xs := [_]) (ma (by decide) (by decide) lowKK_ng decl_ng)
        (ma (by decide) (by decide) lowKK_mode decl_mode))))
  · exact frag_append (xs := [_]) (mp (by decide) (by decide) lowKK_lg decl_lg)
      (frag_append (xs := [_]) (lhit_frag o he hK rfl lowKK_list (list_frag o he hsh) decl_list)
      (frag_append (xs := [_]) (ma (by decide) (by decide) lowKK_date decl_date)
      (frag_append (xs := [_]) (ma (by decide) (by decide) lowKK_ng decl_ng)
        (ma (by decide) (by decide) lowKK_mode decl_mode))))
  · exact frag_append (xs := [_]) (mp (by decide) (by decide) lowKK_lg decl_lg)
      (frag_append (xs := [_]) (mp (by decide) (by decide) lowKK_list decl_list)
      (frag_append (xs := [_]) (lhit_frag o he hK rfl lowKK_date (date_frag o hsh) decl_date)
      (frag_append (xs := [_]) (ma (by decide) (by decide) lowKK_ng decl_ng)
        (ma (by decide) (by decide) lowKK_mode decl_mode))))
  · exact frag_append (xs := [_]) (mp (by decide) (by decide) lowKK_lg decl_lg)
      (frag_append (xs := [_]) (mp (by decide) (by decide) lowKK_list decl_list)
      (frag_append (xs := [_]) (mp (by decide) (by decide) lowKK_date decl_date)
      (frag_append (xs := [_]) (lhit_frag o he hK rfl lowKK_ng (ng_frag o he hsh) decl_ng)
        (ma (by decide) (by decide) lowKK_mode decl_mode))))
  · exact frag_append (xs := [_]) (mp (by decide) (by decide) lowKK_lg decl_lg)
      (frag_append (xs := [_]) (mp (by decide) (by decide) lowKK_list decl_list)
      (frag_append (xs := [_]) (mp (by decide) (by decide) lowKK_date decl_date)
      (frag_append (xs := [_]) (mp (by decide) (by decide) lowKK_ng decl_ng)
        (lhit_frag o he hK rfl lowKK_mode (mode_frag o he hsh) decl_mode))))

/-- `listClassify` up to its last words: if it goes on, the reply's code in `r`. -/
theorem listBody_frag (o : Oracle σ) {b : Word} {ci : Nat} {L : List Byte} {e : PancakeState σ}
    {c : CommandSpec.Cmd} (hc : IsList c) (hw1 : 1 ≤ (spans L).length) (he : VEntry b ci (cmdCode (some c)) L e)
    (hgn : GnCode e.code) :
    Frag o listBody (Like e) (LEnd b e (Session.replyCode (CommandSpec.answerIn c (argsOf L)))) := by
  have hsh := he.short62
  exact frag_conseq (frag_append (frag_append (frag_append (frag_append (frag_append (fhead_frag o he)
    (fscan_frag o he)) (fkept_frag o he)) (fargs_frag o hw1 hsh)) (ldecs_frag o)) (lbranches_frag o hc he hgn hsh))
    (fun _ h => h) fun _ h => lend_of h

/-- **`listClassify` keeps its contract** as the code holds it, with `groupName` as it lowers: on a line of words,
if it returns, it gives back zero and leaves in the return word the code of `CommandSpec.answerIn`'s reply to
LISTGROUP, LIST, DATE, NEWGROUPS and MODE, every word but `clsWords` as it was. -/
theorem listClassify_ok (o : Oracle σ) (b : Word) {code : String → Option (List String × PancakeProg)}
    {body : PancakeProg} (hcode : code "listClassify" = some (["c", "cmd"], body))
    (hbody : Lower.lower Session.listClassify = some body) (hgn : GnCode code) :
    FnOk o "listClassify" b IsList code := by
  refine ⟨body, hcode, fun ci c L s1 hc hw1 he hcd => ?_⟩
  have hsplit := Block.fold_split listBody (SessionStore.give (Syntax.v "r")) (by simp [SessionStore.give]) give_lower
  rw [Lower.lower, list_eq, hsplit] at hbody
  obtain ⟨c', hc', hs⟩ := listBody_frag o hc hw1 he (hcd ▸ hgn) _ (CallRet b (Session.replyCode
    (CommandSpec.answerIn c (argsOf L))) s1.memory) (fun _ => False) (fun _ _ _ h _ => h)
    (give_run o lOffs_ok he.hcov he.base)
  rw [hbody] at hc'; cases hc'
  exact WpRet.conseq hs (fun u (hu : u = s1) => hu ▸ like_refl s1) (fun _ _ h => h) fun _ h => h

/-- `listClassify`'s body lowers before anything. -/
theorem lowKK_listBody : LowKK listBody :=
  lowKK_append (lowKK_append (lowKK_append (lowKK_append (lowKK_append lowKK_fnHead
    (lowK_any _ (k := .skip) (c := _) rfl)) (lowK_any _ (k := .skip) (c := _) rfl))
    (lowK_any _ (k := .skip) (c := _) rfl)) (lowKK_decsC lDecls))
    (lowKK_append (xs := [_]) (lowKK_ite rfl lowKK_lg fun k => ⟨k, rfl⟩) (lowKK_append (xs := [_])
      (lowKK_ite rfl lowKK_list fun k => ⟨k, rfl⟩) (lowKK_append (xs := [_])
        (lowKK_ite rfl lowKK_date fun k => ⟨k, rfl⟩) (lowKK_append (xs := [_])
          (lowKK_ite rfl lowKK_ng fun k => ⟨k, rfl⟩) (lowKK_ite rfl lowKK_mode fun k => ⟨k, rfl⟩)))))

/-- `listClassify` lowers. -/
theorem list_lowers : ∃ body, Lower.lower Session.listClassify = some body := by
  obtain ⟨c, hc⟩ := lowKK_listBody _
  refine ⟨c, ?_⟩
  rw [Lower.lower, list_eq, Block.fold_split listBody _ (by simp [SessionStore.give]) give_lower]
  exact hc

/-! ### The premises can hold -/

/-- `listClassify`'s locals declared, of an empty line in block zero past base zero. -/
def lState : PancakeState Unit :=
  { bareState () with
    locals := fun x => if x = "blk" then some (SessionFrame.blockAt 0 0)
      else if x = "r" then some (BitVec.ofNat 64 (Session.replyCode .syntax))
      else if x = "ok" ∨ x = "lo" then some 1
      else if x = "hi" then some (BitVec.ofNat 64 CommandSpec.numberMax) else some 0 }

theorem lpre_witness : LPre 0 0 [] lState lState :=
  ⟨⟨fun _ _ => rfl, fun _ _ => rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    fun y hy => by
      simp only [lBound, lDecls, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hy
      rcases hy with rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨_, rfl⟩⟩, rfl, rfl, rfl⟩

theorem lat_witness : LAt 0 0 [] lState lState := lpre_witness.1

theorem latR_witness : LAtR (Session.replyCode .syntax) 0 0 [] lState lState := lat_witness

theorem lend_witness : LEnd 0 lState (Session.replyCode .syntax) lState := lend_of lat_witness

end DN.Server.SessionClassify
