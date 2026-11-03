-- SPDX-License-Identifier: AGPL-3.0-or-later
import DN.Server.SessionWords

/-!
# DN.Server.SessionClassify

`classify`, the reply's first stage: if it goes on, `r` holds the code `CommandSpec.replyIn` gives the line
(`classify_frag`). The command is `commandIn`'s (`pick_spec`); the branches are `answer`'s and `answerIn`'s. What the
reply carries past its code is not shown.
-/

namespace DN.Server.SessionClassify

open DN.Compiler DN.Compiler.Wp DN.Compiler.WpRet DN.Compiler.Bytes DN.Compiler.Preservation DN.Compiler.Frag DN.Server
  DN.News DN.News.WordsRun DN.News.FrameSpec DN.Server.SessionText DN.Server.SessionWords
open DN.Server.SessionLayout (framerHead texts textAt ownOff ownTexts ownRet ownVSel ownVs ownVl ownLo ownHi ownFs
  ownFl ownNamed ownWs ownWl ownStore conns tableOff connSlot cFramer)
open DN.News.FramerCode (bw leE or2E bw_ne0 bw_eq0 eval_le eval_eq eval_or2)
open DN.Server.SessionCheck (zeroState)

variable {σ : Type}

/-! ### The command a line names -/

/-- The code `cmd` holds for a command, zero for none. -/
def cmdCode : Option CommandSpec.Cmd → Nat
  | none => 0 | some .capabilities => 1 | some .help => 2 | some .quit => 3 | some .head => 4 | some .stat => 5
  | some .post => 6 | some .article => 7 | some .body => 8 | some .group => 9 | some .next => 10
  | some .last => 11 | some .listgroup => 12 | some .list => 13 | some .date => 14 | some .newgroups => 15
  | some .mode => 16 | some .over => 17 | some .hdr => 18 | some .xover => 19 | some .xhdr => 20
  | some .authinfo => 21

/-- Of the names `ps` (a text's place, a code), the last the word `u` is: its code, or `c`. -/
def pickFold (u : List Byte) (ps : List (Nat × Nat)) (c : Nat) : Nat :=
  ps.foldl (fun acc p => if u = texts.getD p.1 [] then p.2 else acc) c

/-- The commands of a server with a store or without: a text's index, and the code. -/
def baseNames : List (Nat × Nat) :=
  [(12, 1), (13, 2), (14, 3), (15, 4), (16, 5), (Session.tMode, 16), (Session.tAuthinfo, 21)]
/-- The commands of a server with a store only. -/
def storeNames : List (Nat × Nat) :=
  [(17, 6), (Session.tArticle, 7), (Session.tBody, 8), (Session.tGroup, 9), (Session.tNext, 10),
   (Session.tLast, 11), (Session.tListgroup, 12), (Session.tList, 13), (Session.tDate, 14), (Session.tNewgroups, 15),
   (Session.tOver, 17), (Session.tHdr, 18), (Session.tXover, 19), (Session.tXhdr, 20)]

/-- The names' statements. -/
def picks (ps : List (Nat × Nat)) : List Syntax.PStmt :=
  ps.flatMap fun p => Session.nameIsAt p.1 ++ [SessionStore.ifs (Syntax.v "eqk") [.assign "cmd" (Syntax.n p.2)]]

theorem picks_eq : (List.range 5).flatMap (fun k => Session.nameIs k ++
      [.ite (Syntax.v "eqk") [.assign "cmd" (Syntax.n (k + 1))] []]) ++
    Session.nameIsAt Session.tMode ++ [SessionStore.ifs (Syntax.v "eqk") [.assign "cmd" (Syntax.n 16)]] ++
    Session.nameIsAt Session.tAuthinfo ++ [SessionStore.ifs (Syntax.v "eqk") [.assign "cmd" (Syntax.n 21)]] =
    picks baseNames := by
  simp [picks, baseNames, Session.nameIs, SessionStore.ifs, Session.tNames, List.range_succ]

/-- **The names the session tries are `commandIn`'s.** -/
theorem pick_spec (offered : Bool) (w : List Byte) :
    pickFold (w.map CommandSpec.upper) (baseNames ++ if offered then storeNames else []) 0 =
      cmdCode (CommandSpec.commandIn offered w) := by
  simp only [CommandSpec.commandIn, CommandSpec.command?]
  generalize w.map CommandSpec.upper = u
  by_cases hm : u ∈ [CommandSpec.ascii "CAPABILITIES", CommandSpec.ascii "HELP", CommandSpec.ascii "QUIT",
    CommandSpec.ascii "HEAD", CommandSpec.ascii "STAT", CommandSpec.ascii "MODE", CommandSpec.ascii "AUTHINFO",
    CommandSpec.ascii "POST", CommandSpec.ascii "ARTICLE", CommandSpec.ascii "BODY", CommandSpec.ascii "GROUP",
    CommandSpec.ascii "NEXT", CommandSpec.ascii "LAST", CommandSpec.ascii "LISTGROUP", CommandSpec.ascii "LIST",
    CommandSpec.ascii "DATE", CommandSpec.ascii "NEWGROUPS", CommandSpec.ascii "OVER", CommandSpec.ascii "HDR",
    CommandSpec.ascii "XOVER", CommandSpec.ascii "XHDR"]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst h <;>
        cases offered <;> decide
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hm
    obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20⟩ := hm
    have t12 : texts[12]?.getD [] = CommandSpec.ascii "CAPABILITIES" := rfl
    have t13 : texts[13]?.getD [] = CommandSpec.ascii "HELP" := rfl
    have t14 : texts[14]?.getD [] = CommandSpec.ascii "QUIT" := rfl
    have t15 : texts[15]?.getD [] = CommandSpec.ascii "HEAD" := rfl
    have t16 : texts[16]?.getD [] = CommandSpec.ascii "STAT" := rfl
    have t56 : texts[56]?.getD [] = CommandSpec.ascii "MODE" := rfl
    have t87 : texts[87]?.getD [] = CommandSpec.ascii "AUTHINFO" := rfl
    have t17 : texts[17]?.getD [] = CommandSpec.ascii "POST" := rfl
    have t27 : texts[27]?.getD [] = CommandSpec.ascii "ARTICLE" := rfl
    have t28 : texts[28]?.getD [] = CommandSpec.ascii "BODY" := rfl
    have t36 : texts[36]?.getD [] = CommandSpec.ascii "GROUP" := rfl
    have t37 : texts[37]?.getD [] = CommandSpec.ascii "NEXT" := rfl
    have t38 : texts[38]?.getD [] = CommandSpec.ascii "LAST" := rfl
    have t45 : texts[45]?.getD [] = CommandSpec.ascii "LISTGROUP" := rfl
    have t46 : texts[46]?.getD [] = CommandSpec.ascii "LIST" := rfl
    have t47 : texts[47]?.getD [] = CommandSpec.ascii "DATE" := rfl
    have t48 : texts[48]?.getD [] = CommandSpec.ascii "NEWGROUPS" := rfl
    have t62 : texts[62]?.getD [] = CommandSpec.ascii "OVER" := rfl
    have t63 : texts[63]?.getD [] = CommandSpec.ascii "HDR" := rfl
    have t64 : texts[64]?.getD [] = CommandSpec.ascii "XOVER" := rfl
    have t65 : texts[65]?.getD [] = CommandSpec.ascii "XHDR" := rfl
    cases offered <;>
      simp [pickFold, baseNames, storeNames, Session.tMode, Session.tAuthinfo, Session.tArticle, Session.tBody,
        Session.tGroup, Session.tNext, Session.tLast, Session.tListgroup, Session.tList, Session.tDate,
        Session.tNewgroups, Session.tOver, Session.tHdr, Session.tXover, Session.tXhdr, t12, t13, t14, t15, t16, t56,
            t87, t17, t27, t28, t36, t37, t38, t45, t46, t47, t48, t62, t63, t64, t65, n0, n1, n2, n3, n4, n5, n6, n7,
                n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, cmdCode]

/-- While the names are tried: `cmd` holding `c`, the rest as at `s0`. -/
structure PickAt (s0 : PancakeState σ) (c : Nat) (u : PancakeState σ) : Prop where
  but : SessionCheck.ButFor ["eqk", "jq", "cmd"] s0 u
  cmd : u.locals "cmd" = some (BitVec.ofNat 64 c)
  eqk : ∃ v, u.locals "eqk" = some v
  jq : ∃ v, u.locals "jq" = some v

theorem pickAt_clock (s0 : PancakeState σ) (c : Nat) : Safe.ClockFree (PickAt s0 c) :=
  fun _ _ h => ⟨{ h.but with }, h.cmd, h.eqk, h.jq⟩

/-- **The names tried in turn**: `cmd` the code of the last the first word is. -/
theorem picks_frag (o : Oracle σ) {b B S : Word} {w : List Byte} {s0 : PancakeState σ}
    (hw : WordAt "s0" "l0" B S w s0) (hb : s0.baseAddr = b)
        (htx : SessionAppend.TextsIn b s0.memory s0.memaddrs s0.be) :
    ∀ (ps : List (Nat × Nat)) (c : Nat), (∀ p ∈ ps, p.1 < texts.length ∧ p.2 < 2 ^ 64) →
      Frag o (picks ps) (PickAt s0 c) (PickAt s0 (pickFold (w.map CommandSpec.upper) ps c))
  | [], c, _ => frag_nil o fun _ h => h
  | p :: ps, c, hps => by
    have hp := hps p (by simp)
    let d := decide (w.map CommandSpec.upper = texts.getD p.1 [])
    have f1 := wordIsAt_any o (P := PickAt s0 c) (sn := "s0") (ln := "l0") (by decide) (by decide) hp.1 (b := b)
        (B := B) (S := S) (w := w)
      fun s h => by
        have hl : ∀ y, y ∉ ["eqk", "jq", "cmd"] → s.locals y = s0.locals y := h.but.locals
        exact ⟨⟨by rw [hl "blk" (by decide)]; exact hw.blk, by rw [hl "s0" (by decide)]; exact hw.start,
          by rw [hl "l0" (by decide)]; exact hw.len, fun i hi => by
            rw [h.but.memory, h.but.memaddrs, h.but.be]; exact hw.bytes i hi, hw.short⟩,
          h.but.base.trans hb, by rw [h.but.memory, h.but.memaddrs, h.but.be]; exact htx, h.eqk, h.jq⟩
    have f2 : Frag o [SessionStore.ifs (Syntax.v "eqk") [.assign "cmd" (Syntax.n p.2)]]
        (fun u => ∃ s1, PickAt s0 c s1 ∧ SessionCheck.ButFor ["eqk", "jq"] s1 u ∧ (∃ v, u.locals "jq" = some v) ∧
          u.locals "eqk" = some (bw d))
        (PickAt s0 (if w.map CommandSpec.upper = texts.getD p.1 [] then p.2 else c)) := by
      have keep : ∀ u, (∃ s1, PickAt s0 c s1 ∧ SessionCheck.ButFor ["eqk", "jq"] s1 u ∧ (∃ v, u.locals "jq" = some v) ∧
          u.locals "eqk" = some (bw d)) → PickAt s0 c u :=
        fun u ⟨s1, h1, h2, h3, h4⟩ => ⟨SessionCheck.but_trans h1.but (SessionCheck.but_mono h2 (by simp)),
          by rw [h2.locals "cmd" (by decide)]; exact h1.cmd, ⟨_, h4⟩, h3⟩
      refine frag_ite o (C := .var "eqk") rfl (pickAt_clock _ _) (fun s h => ⟨_, (keep s h).eqk.choose_spec⟩) ?_
        (fun _ _ _ _ h => by simp [declared] at h) (frag_nil o fun s ⟨h, hz⟩ => ?_)
        (fun _ _ _ _ h => by simp [declared] at h)
      · refine frag_one (a := .assign "cmd" (.const (BitVec.ofNat 64 p.2))) rfl rfl rfl (pickAt_clock _ _)
          (Safe.assign fun s ⟨h, hn⟩ => ⟨_, _, rfl, (keep s h).cmd, ?_⟩)
        have hk := keep s h
        obtain ⟨_, _, _, _, h4⟩ := h
        have hd : d = true := by
          cases e : d
          · rw [e] at h4; exact absurd (by simp only [eval]; rw [h4]; rfl) hn
          · rfl
        rw [if_pos (of_decide_eq_true hd)]
        exact ⟨SessionCheck.but_set hk.but (by simp) _, by simp [setLocal], by simpa [setLocal] using hk.eqk,
          by simpa [setLocal] using hk.jq⟩
      · have hk := keep s h
        obtain ⟨_, _, _, _, h4⟩ := h
        have hd : d = false := by
          cases e : d
          · rfl
          · rw [e] at h4; simp only [eval] at hz; rw [h4] at hz; exact absurd hz (by decide)
        rw [if_neg (of_decide_eq_false hd)]
        exact hk
    have f3 := picks_frag o hw hb htx ps (if w.map CommandSpec.upper = texts.getD p.1 [] then p.2 else c)
      fun q hq => hps q (List.mem_cons_of_mem _ hq)
    rw [picks, List.flatMap_cons, ← picks]
    exact frag_append (frag_append f1 f2) f3

/-! ## `classify` -/

/-- The locals `classify` declares or writes. -/
def clsNames : List String :=
  ["w", "s0", "l0", "s1", "l1", "inw", "ws", "q", "cq", "cmd", "eqk", "jq", "ok", "val", "cz", "args", "r", "gn", "vc",
   "lc"]

/-- The words of the session's own area the functions `classify` calls write. -/
def clsOffs : List Nat :=
  [ownRet, ownVSel, ownVs, ownVl, ownLo, ownHi, ownFs, ownFl, ownNamed, ownWs, ownWl]

/-- The addresses of those words. -/
def clsWords (b : Word) : List Word := clsOffs.map fun x => b + BitVec.ofNat 64 (ownOff + x)

/-- What `classify` leaves: every local but its own and every word but `clsWords` as at `s0`, `r` holding `R`. -/
structure Out (b : Word) (s0 : PancakeState σ) (R : Nat) (u : PancakeState σ) : Prop where
  loc : ∀ y, y ∉ clsNames → u.locals y = s0.locals y
  memory : ∀ a, a ∉ clsWords b → u.memory a = s0.memory a
  memaddrs : u.memaddrs = s0.memaddrs
  be : u.be = s0.be
  base : u.baseAddr = s0.baseAddr
  code : u.code = s0.code
  r : u.locals "r" = some (BitVec.ofNat 64 R)

theorem out_clock (b : Word) (s0 : PancakeState σ) (R : Nat) : Safe.ClockFree (Out b s0 R) :=
  fun _ _ h => { h with }

theorem out_restore {b : Word} {s0 : PancakeState σ} {R : Nat} {u : PancakeState σ} (h : Out b s0 R u) {y : String}
    (hy : y ∈ clsNames) (hr : y ≠ "r") (v : Option Value) : Out b s0 R (restore u y v) where
  loc x hx := by
    simp only [restore, resVar]; rw [if_neg (fun (e : x = y) => hx (e ▸ hy))]; exact h.loc x hx
  memory := h.memory
  memaddrs := h.memaddrs
  be := h.be
  base := h.base
  code := h.code
  r := by simp only [restore, resVar]; rw [if_neg (Ne.symm hr)]; exact h.r

/-- Within `classify`'s branches, before a call: every local but its own and every word as at `s0`, `r` bound. -/
structure Kept (s0 u : PancakeState σ) : Prop where
  loc : ∀ y, y ∉ clsNames → u.locals y = s0.locals y
  memory : u.memory = s0.memory
  memaddrs : u.memaddrs = s0.memaddrs
  be : u.be = s0.be
  ffi : u.ffi = s0.ffi
  base : u.baseAddr = s0.baseAddr
  code : u.code = s0.code
  r : ∃ v, u.locals "r" = some v

/-- After a call: every local but `classify`'s own and every word but `clsWords` as at `s0`, `r` bound. -/
structure After (b : Word) (s0 u : PancakeState σ) : Prop where
  loc : ∀ y, y ∉ clsNames → u.locals y = s0.locals y
  memory : ∀ a, a ∉ clsWords b → u.memory a = s0.memory a
  memaddrs : u.memaddrs = s0.memaddrs
  be : u.be = s0.be
  base : u.baseAddr = s0.baseAddr
  code : u.code = s0.code
  r : ∃ v, u.locals "r" = some v

theorem kept_but {s0 u u' : PancakeState σ} (h : Kept s0 u) {xs : List String} (h2 : SessionCheck.ButFor xs u u')
    (hxs : ∀ y ∈ xs, y ∈ clsNames) (hr : "r" ∉ xs) : Kept s0 u' :=
  ⟨fun y hy => by rw [h2.locals y fun e => hy (hxs y e)]; exact h.loc y hy, h2.memory.trans h.memory,
    h2.memaddrs.trans h.memaddrs, h2.be.trans h.be, h2.ffi.trans h.ffi, h2.base.trans h.base, h2.code.trans h.code,
    by rw [h2.locals _ hr]; exact h.r⟩

/-- …and the words' places and count, the locals bound. -/
structure TreeAt (L : List Byte) (s0 u : PancakeState σ) : Prop extends Kept s0 u where
  w : u.locals "w" = some (BitVec.ofNat 64 (spans L).length)
  s0 : u.locals "s0" = some (BitVec.ofNat 64 ((spans L).getD 0 (0, 0)).1)
  l0 : u.locals "l0" = some (BitVec.ofNat 64 ((spans L).getD 0 (0, 0)).2)
  s1 : u.locals "s1" = some (BitVec.ofNat 64 ((spans L).getD 1 (0, 0)).1)
  l1 : u.locals "l1" = some (BitVec.ofNat 64 ((spans L).getD 1 (0, 0)).2)
  cmd : ∃ v, u.locals "cmd" = some v
  eqk : ∃ v, u.locals "eqk" = some v
  jq : ∃ v, u.locals "jq" = some v
  ok : ∃ v, u.locals "ok" = some v
  val : ∃ v, u.locals "val" = some v

theorem treeAt_clock (L : List Byte) (s0 : PancakeState σ) : Safe.ClockFree (TreeAt L s0) := fun _ _ h => { h with }

/-- The reply `X` set after a call. -/
theorem leafA_frag (o : Oracle σ) (b : Word) {s0 : PancakeState σ} (X : CommandSpec.Reply) {R : Nat}
    {P : Assn σ} (hP : ∀ u, P u → After b s0 u ∧ Session.replyCode X = R) :
    Frag o [Session.reply X] P (Out b s0 R) :=
  frag_one (a := .assign "r" (.const (BitVec.ofNat 64 (Session.replyCode X)))) rfl rfl rfl (out_clock b s0 R)
    (Safe.assign fun u hu => by
      obtain ⟨h, hX⟩ := hP u hu
      obtain ⟨v, hv⟩ := h.r
      refine ⟨_, v, rfl, hv, ?_⟩
      exact ⟨fun y hy => by
          have : y ≠ "r" := fun e => hy (by simp [e, clsNames])
          simp only [setLocal, if_neg this]; exact h.loc y hy,
        h.memory, h.memaddrs, h.be, h.base, h.code, by simp [setLocal, hX]⟩)

theorem kept_after {b : Word} {s0 u : PancakeState σ} (h : Kept s0 u) : After b s0 u :=
  ⟨h.loc, fun a _ => by rw [h.memory], h.memaddrs, h.be, h.base, h.code, h.r⟩

/-- The reply `X` set before a call. -/
theorem leaf_frag (o : Oracle σ) (b : Word) {s0 : PancakeState σ} (X : CommandSpec.Reply) {R : Nat}
    {P : Assn σ} (hP : ∀ u, P u → Kept s0 u ∧ Session.replyCode X = R) :
    Frag o [Session.reply X] P (Out b s0 R) :=
  leafA_frag o b X fun u hu => ⟨kept_after (hP u hu).1, (hP u hu).2⟩

/-- A branch of `classify` on `c`. -/
theorem tree_ite (o : Oracle σ) {b : Word} {s0 : PancakeState σ} {R : Nat} {c : Syntax.PExpr} {C : PancakeExp}
    (hc : Lower.lowerExp c = some C) {t e : List Syntax.PStmt} {P : Assn σ}
    (hdef : ∀ s, P s → ∃ v, eval s C = some v)
    (ht : Frag o t (fun s => P s ∧ eval s C ≠ some 0) (Out b s0 R))
    (he : Frag o e (fun s => P s ∧ eval s C = some 0) (Out b s0 R))
    (hdt : ∀ y ∈ declared t, y ∈ clsNames ∧ y ≠ "r") (hde : ∀ y ∈ declared e, y ∈ clsNames ∧ y ≠ "r") :
    Frag o [.ite c t e] P (Out b s0 R) :=
  frag_ite o hc (out_clock b s0 R) hdef ht (fun _ _ v h hy => out_restore h (hdt _ hy).1 (hdt _ hy).2 v) he
    (fun _ _ v h hy => out_restore h (hde _ hy).1 (hde _ hy).2 v)

/-- What `classify` takes at its entry `s0`: connection `ci`'s line, of kind `k`, in its framer's block. Also the locals
it reads, the session's words with the texts, and whether there is a store. -/
structure ClsIn (b : Word) (ci : Nat) (offered : Bool) (k : FrameSpec.Kind) (L : List Byte) (s0 : PancakeState σ) :
    Prop where
  line : LineIn (SessionFrame.blockAt b ci) L s0
  c : s0.locals "c" = some (BitVec.ofNat 64 ci)
  hci : ci < conns
  kind : s0.locals "kind" = some (BitVec.ofNat 64 (FramerProg.kindCode k))
  r : ∃ v, s0.locals "r" = some v
  base : s0.baseAddr = b
  hb : b.toNat % 8 = 0
  hcov : Analyzer.Covers SessionLayout.size s0.memaddrs b
  texts : SessionAppend.TextsIn b s0.memory s0.memaddrs s0.be
  store : s0.memory (b + BitVec.ofNat 64 (ownOff + ownStore)) = bw offered
  short : L.length ≤ News.SessionSpec.lineLimit
  keptW : s0.memory (SessionFrame.blockAt b ci + BitVec.ofNat 64 32) = BitVec.ofNat 64 L.length

theorem treeAt_but {L : List Byte} {s0 u u' : PancakeState σ} (h : TreeAt L s0 u) {xs : List String}
    (h2 : SessionCheck.ButFor xs u u') (hxs : ∀ y ∈ xs, y ∈ clsNames ∧ y ∉ ["w", "s0", "l0", "s1", "l1"])
    (hex : ∀ y ∈ ["r", "cmd", "eqk", "jq", "ok", "val"], ∃ v, u'.locals y = some v) : TreeAt L s0 u' := by
  have k : ∀ y ∈ ["w", "s0", "l0", "s1", "l1"], u'.locals y = u.locals y := fun y hy =>
    h2.locals y fun e => (hxs y e).2 hy
  exact ⟨⟨fun y hy => by rw [h2.locals y fun e => hy (hxs y e).1]; exact h.loc y hy, h2.memory.trans h.memory,
    h2.memaddrs.trans h.memaddrs, h2.be.trans h.be, h2.ffi.trans h.ffi, h2.base.trans h.base, h2.code.trans h.code,
    hex "r" (by simp)⟩, by rw [k "w" (by simp)]; exact h.w, by rw [k "s0" (by simp)]; exact h.s0,
    by rw [k "l0" (by simp)]; exact h.l0, by rw [k "s1" (by simp)]; exact h.s1, by rw [k "l1" (by simp)]; exact h.l1,
    hex "cmd" (by simp), hex "eqk" (by simp), hex "jq" (by simp), hex "ok" (by simp), hex "val" (by simp)⟩

/-- …after a check that writes `xs`, the others bound. -/
theorem treeAt_check {L : List Byte} {s0 u u' : PancakeState σ} (h : TreeAt L s0 u) {xs : List String}
    (h2 : SessionCheck.ButFor xs u u') (hxs : ∀ y ∈ xs, y ∈ clsNames ∧ y ∉ ["w", "s0", "l0", "s1", "l1"])
    (hok : ∃ v, u'.locals "ok" = some v) (hjq : ∃ v, u'.locals "jq" = some v) (hval : ∃ v, u'.locals "val" = some v)
    (hr : "r" ∉ xs) (hc : "cmd" ∉ xs) (he : "eqk" ∉ xs) : TreeAt L s0 u' :=
  treeAt_but h h2 hxs fun y hy => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl
    · rw [h2.locals _ hr]; exact h.r
    · rw [h2.locals _ hc]; exact h.cmd
    · rw [h2.locals _ he]; exact h.eqk
    · exact hjq
    · exact hok
    · exact hval

/-- The line in place at a state of the branches. -/
theorem treeAt_line {b : Word} {ci : Nat} {offered : Bool} {k : FrameSpec.Kind} {L : List Byte}
    {s0 u : PancakeState σ} (hs : ClsIn b ci offered k L s0) (h : TreeAt L s0 u) :
    LineIn (SessionFrame.blockAt b ci) L u :=
  ⟨by rw [h.loc "blk" (by decide)]; exact hs.line.blk, by rw [h.loc "kept" (by decide)]; exact hs.line.kept,
    fun j hj => by rw [h.memory, h.memaddrs, h.be]; exact hs.line.bytes j hj, hs.line.short⟩

/-- The second word in place, when there is one. -/
theorem treeAt_second {b : Word} {ci : Nat} {offered : Bool} {k : FrameSpec.Kind} {L : List Byte}
    {s0 u : PancakeState σ} (hs : ClsIn b ci offered k L s0) (h : TreeAt L s0 u) (h2 : 2 ≤ (spans L).length) :
    WordAt "s1" "l1" (SessionFrame.blockAt b ci) (BitVec.ofNat 64 ((spans L).getD 1 (0, 0)).1)
      (cut L ((spans L).getD 1 (0, 0))) u :=
  wordAt_of (treeAt_line hs h) (spans_getD_mem (by omega)) h.s1 h.l1

section Tree
open DN.Compiler.Syntax DN.Server.Session
open DN.Server.SessionStore (ne or2 ifs callS found)

/-- CAPABILITIES's branch. -/
def capaTree : List PStmt :=
  [.ite (eEq (v "args") (n 0)) [reply .capabilities]
    [.ite (eEq (v "args") (n 1))
      (keywordCheck ++ [.ite (v "ok") [reply .capabilities] [reply .syntax]])
      [reply .syntax]]]

/-- GROUP's branch. -/
def groupTree : List PStmt :=
  [.ite (eEq (v "args") (n 1))
    (callS "gn" "groupName" [v "c", v "s1", v "l1"] ++
     [.ite found
       [.ite (eLe (v "l1") (n News.CommandSpec.groupNameMax))
         [reply (.select [])] [reply .noSuchGroup]]
       [reply .syntax]])
    [reply .syntax]]

/-- HEAD's, STAT's, ARTICLE's and BODY's branch. -/
def readTree : List PStmt :=
  [.ite (eEq (v "args") (n 0))
    [.ite hasStore [reply (.current .head)] [reply .noGroup]]
    [.ite (eEq (v "args") (n 1))
      (numberCheck ++
       [.ite (v "ok")
         [.ite hasStore [reply (.byNumber .head 0)] [reply .noGroup]]
         (messageIdCheck ++
          [.ite (v "ok")
            [.ite hasStore [reply (.lookup .head 0 [])] [reply .noSuchId]]
            [reply .syntax]])])
      [reply .syntax]]]

/-- The branches on the command once the arguments are counted. -/
def argsTree : List PStmt :=
  [.dec "args" (eSub (v "w") (n 1)),
   .ite (eEq (v "cmd") (n 1)) capaTree
     [.ite (eEq (v "cmd") (n 2))
       [.ite (eEq (v "args") (n 0)) [reply .help] [reply .syntax]]
       [.ite (eEq (v "cmd") (n 3))
         [.ite (eEq (v "args") (n 0)) [reply .quit] [reply .syntax]]
         [.ite (eEq (v "cmd") (n 6))
           [.ite (eEq (v "args") (n 0)) [reply .post] [reply .syntax]]
           [.ite (eEq (v "cmd") (n 9)) groupTree
             [.ite (or2 (eEq (v "cmd") (n 10)) (eEq (v "cmd") (n 11)))
               [.ite (eEq (v "args") (n 0)) [reply (.move true)] [reply .syntax]]
               readTree]]]]]]

/-- The tree for a known command on a command line. -/
def knownTree : List PStmt :=
  [.ite (eEq (v "cmd") (n 21)) [reply (.authinfo [])]
   [.ite (eLe (n 17) (v "cmd")) (callS "vc" "viewClassify" [v "c", v "cmd"] ++ [.assign "r" found])
    [.ite (eLe (n 12) (v "cmd"))
     (callS "lc" "listClassify" [v "c", v "cmd"] ++ [.assign "r" found])
     argsTree]]]

/-- The branches on the command. -/
def cmdTree : List PStmt :=
  [.ite (eEq (v "cmd") (n 0)) [reply .unknown]
    [.ite (ne (v "kind") (n (News.FramerProg.kindCode .command))) [reply .syntax] knownTree]]

theorem classify_eq : Session.classify = scanWords 2 ++
    [.dec "cmd" (n 0), .dec "eqk" (n 0), .dec "jq" (n 0), .dec "ok" (n 0), .dec "val" (n 0),
     .ite (eEq (v "w") (n 0)) [.ite (isKind .overlong) [reply .unknown] [reply .ignore]]
       (picks baseNames ++ [ifs hasStore (picks storeNames)] ++ cmdTree)] := by
  rw [← picks_eq]
  rfl

end Tree

theorem argsEq_eval {u : PancakeState σ} {A k : Nat} (hA : A < 2 ^ 63) (hk : k < 2 ^ 63)
    (h : u.locals "args" = some (BitVec.ofNat 64 A)) :
    eval u (.cmp .equal (.var "args") (.const (BitVec.ofNat 64 k))) = some (bw (decide (A = k))) :=
  eval_eq (by omega) (by omega) (by simp only [eval]; exact h) rfl

theorem nodecl {xs : List Syntax.PStmt} (h : declared xs = []) : ∀ y ∈ declared xs, y ∈ clsNames ∧ y ≠ "r" :=
  fun y hy => by rw [h] at hy; simp at hy

/-- **CAPABILITIES's branch**: with `A` arguments, the reply `R`. -/
theorem capa_frag (o : Oracle σ) {b : Word} {ci : Nat} {offered : Bool} {k : FrameSpec.Kind} {L : List Byte}
    {s0 : PancakeState σ} (hs : ClsIn b ci offered k L s0) {A R : Nat} (hA : A + 1 = (spans L).length)
    (h0 : A = 0 → R = 1)
    (h1 : A = 1 → R = if CommandSpec.isKeyword (cut L ((spans L).getD 1 (0, 0))) then 1 else 7)
    (h2 : 2 ≤ A → R = 7) :
    Frag o capaTree (fun u => TreeAt L s0 u ∧ u.locals "args" = some (BitVec.ofNat 64 A)) (Out b s0 R) := by
  have hAs : A < 2 ^ 62 := by have := spans_length L; have := hs.line.short; omega
  refine tree_ite o (C := .cmp .equal (.var "args") (.const (BitVec.ofNat 64 0))) rfl
    (fun s h => ⟨_, argsEq_eval (by omega) (by decide) h.2⟩)
    (leaf_frag o b .capabilities fun u ⟨h, hc⟩ => ⟨h.1.toKept, by
      rw [argsEq_eval (by omega) (by decide) h.2] at hc; rw [h0 (of_decide_eq_true (bw_ne0 hc))]; rfl⟩) ?_
    (nodecl rfl) (nodecl rfl)
  refine tree_ite o (C := .cmp .equal (.var "args") (.const (BitVec.ofNat 64 1))) rfl
    (fun s h => ⟨_, argsEq_eval (by omega) (by decide) h.1.2⟩) ?_
    (leaf_frag o b .syntax fun u ⟨⟨h, hc0⟩, hc1⟩ => ⟨h.1.toKept, by
      rw [argsEq_eval (by omega) (by decide) h.2] at hc0 hc1
      have := of_decide_eq_false (bw_eq0 hc0); have := of_decide_eq_false (bw_eq0 hc1)
      rw [h2 (by omega)]; rfl⟩)
    (nodecl rfl) (nodecl rfl)
  let K := cut L ((spans L).getD 1 (0, 0))
  have hA1 : ∀ s, ((TreeAt L s0 s ∧ s.locals "args" = some (BitVec.ofNat 64 A)) ∧
      eval s (.cmp .equal (.var "args") (.const (BitVec.ofNat 64 0))) = some 0) ∧
      eval s (.cmp .equal (.var "args") (.const (BitVec.ofNat 64 1))) ≠ some 0 → A = 1 := fun s ⟨⟨h, _⟩, hc⟩ => by
    rw [argsEq_eval (by omega) (by decide) h.2] at hc; exact of_decide_eq_true (bw_ne0 hc)
  have fk : Frag o Session.keywordCheck (fun s => ((TreeAt L s0 s ∧ s.locals "args" = some (BitVec.ofNat 64 A)) ∧
      eval s (.cmp .equal (.var "args") (.const (BitVec.ofNat 64 0))) = some 0) ∧
      eval s (.cmp .equal (.var "args") (.const (BitVec.ofNat 64 1))) ≠ some 0)
      (fun u => TreeAt L s0 u ∧ A = 1 ∧ u.locals "ok" = some (bw (CommandSpec.isKeyword K))) :=
    frag_each o lowKK_keyword fun s hst => by
      have e1 := hA1 s hst
      have ht := hst.1.1.1
      exact frag_conseq (keyword_frag o (treeAt_second hs ht (by omega)) ht.ok ht.jq) (fun _ h => h)
        fun u ⟨hb, hj, hk⟩ => ⟨treeAt_check ht hb (by decide) ⟨_, hk⟩ hj
          (by rw [hb.locals "val" (by decide)]; exact ht.val) (by decide) (by decide) (by decide), e1, hk⟩
  refine frag_append fk (tree_ite o (C := .var "ok") rfl (fun s h => ⟨_, h.2.2⟩)
    (leaf_frag o b .capabilities fun u ⟨h, hc⟩ => ⟨h.1.toKept, ?_⟩)
        (leaf_frag o b .syntax fun u ⟨h, hc⟩ => ⟨h.1.toKept, ?_⟩)
    (nodecl rfl) (nodecl rfl))
  · simp only [eval, h.2.2] at hc
    rw [h1 h.2.1, if_pos (bw_ne0 hc)]; rfl
  · simp only [eval, h.2.2] at hc
    rw [h1 h.2.1, if_neg (by rw [bw_eq0 hc]; decide)]; rfl

/-- The branch on whether there are no arguments: `X`, else 501. -/
theorem zero_frag (o : Oracle σ) (b : Word) {L : List Byte} {s0 : PancakeState σ} (X : CommandSpec.Reply)
    {A R : Nat} (hAs : A < 2 ^ 62) (h0 : A = 0 → R = Session.replyCode X) (h1 : A ≠ 0 → R = 7) :
    Frag o [.ite (Syntax.eEq (Syntax.v "args") (Syntax.n 0)) [Session.reply X] [Session.reply .syntax]]
      (fun u => TreeAt L s0 u ∧ u.locals "args" = some (BitVec.ofNat 64 A)) (Out b s0 R) :=
  tree_ite o (C := .cmp .equal (.var "args") (.const (BitVec.ofNat 64 0))) rfl
    (fun s h => ⟨_, argsEq_eval (by omega) (by decide) h.2⟩)
    (leaf_frag o b X fun u ⟨h, hc⟩ => ⟨h.1.toKept, by
      rw [argsEq_eval (by omega) (by decide) h.2] at hc; rw [h0 (of_decide_eq_true (bw_ne0 hc))]⟩)
    (leaf_frag o b .syntax fun u ⟨h, hc⟩ => ⟨h.1.toKept, by
      rw [argsEq_eval (by omega) (by decide) h.2] at hc; rw [h1 (of_decide_eq_false (bw_eq0 hc))]; rfl⟩)
    (nodecl rfl) (nodecl rfl)

/-- A word of the session's own area before the texts, read at a branch's state. -/
theorem own_eval {b : Word} {ci : Nat} {offered : Bool} {k : FrameSpec.Kind} {L : List Byte} {s0 u : PancakeState σ}
    (hs : ClsIn b ci offered k L s0) (h : Kept s0 u) {X : Nat} (hX8 : X % 8 = 0) (h64 : 64 ≤ X)
    (hXt : X + 8 ≤ ownOff + ownTexts) :
    eval u (.loadWord (.op .add .base (.const (BitVec.ofNat 64 X)))) = some (s0.memory (b + BitVec.ofNat 64 X)) := by
  obtain ⟨T0, hT0⟩ := SessionAppend.lay
  have he := SessionAppend.texts_end
  rw [hT0.eq] at he
  have ha := SessionAppend.own_addr hs.hcov hX8 h64 (by rw [hT0.eq]; omega)
  simp only [eval, h.base, hs.base, h.memaddrs, ha, if_true, h.memory]

/-- Whether there is a store, read at a branch's state. -/
theorem store_eval {b : Word} {ci : Nat} {offered : Bool} {k : FrameSpec.Kind} {L : List Byte} {s0 u : PancakeState σ}
    (hs : ClsIn b ci offered k L s0) (h : Kept s0 u) :
    eval u (.loadWord (.op .add .base (.const (BitVec.ofNat 64 (ownOff + ownStore))))) = some (bw offered) := by
  obtain ⟨h1, h2, h3, -⟩ := SessionAppend.store_facts
  rw [own_eval hs h h1 h2 h3, hs.store]

theorem store_lower : Lower.lowerExp Session.hasStore =
    some (.loadWord (.op .add .base (.const (BitVec.ofNat 64 (ownOff + ownStore))))) := by
  simp [Session.hasStore, Session.ownW, SessionStore.ld, Lower.lowerExp,
    SessionAppend.at_lower SessionAppend.store_facts.2.2.2]

/-- The second word's number check at a branch's state. -/
theorem number_frag (o : Oracle σ) {b : Word} {ci : Nat} {offered : Bool} {k : FrameSpec.Kind} {L : List Byte}
    {s0 : PancakeState σ} (hs : ClsIn b ci offered k L s0) {P : Assn σ}
    (hP : ∀ u, P u → TreeAt L s0 u ∧ 2 ≤ (spans L).length) :
    Frag o Session.numberCheck P
      (fun u => ∃ s, P s ∧ SessionCheck.NumPost (cut L ((spans L).getD 1 (0, 0))) s u) := by
  have hc := SessionCheck.numberCheck_lowerP (s := Syntax.v "s1") (l := Syntax.v "l1") rfl rfl
  refine frag_pinned o (by simp [Session.numberCheckAt])
    (by simp [Session.numberCheckAt, Syntax.PStmt.isDec]) hc (by decide)
    (fun _ _ _ h => ⟨{ h.1 with }, h.2⟩) fun s hp => ?_
  obtain ⟨ht, h2⟩ := hP s hp
  have hw := treeAt_second hs ht h2
  obtain ⟨c', hc', hsafe⟩ := SessionCheck.numberCheck_safe o (s := Syntax.v "s1") (l := Syntax.v "l1") rfl rfl
    (by simp [ExpAvoids, SessionCheck.numNames]) (by simp [ExpAvoids, SessionCheck.numNames])
    (SessionFrame.blockAt b ci) (BitVec.ofNat 64 ((spans L).getD 1 (0, 0)).1) (cut L ((spans L).getD 1 (0, 0))) s
  rw [hc] at hc'; cases hc'
  exact Safe.conseq hsafe (fun u (hu : u = s) => ⟨hu, hu ▸ ⟨hw.start, hw.len, hw.blk, hw.bytes, hw.short, ht.ok, ht.val,
    ht.jq⟩⟩) fun _ h => h

/-- The second word's message-id check at a branch's state. -/
theorem mid_frag (o : Oracle σ) {b : Word} {ci : Nat} {offered : Bool} {k : FrameSpec.Kind} {L : List Byte}
    {s0 : PancakeState σ} (hs : ClsIn b ci offered k L s0) {P : Assn σ}
    (hP : ∀ u, P u → TreeAt L s0 u ∧ 2 ≤ (spans L).length) :
    Frag o Session.messageIdCheck P
      (fun u => ∃ s, P s ∧ SessionCheck.MidPost (cut L ((spans L).getD 1 (0, 0))) s u) := by
  have hc := SessionCheck.messageIdCheck_lower (σ := Unit) (s := Syntax.v "s1") (l := Syntax.v "l1") rfl rfl []
    (bareState ())
  refine frag_pinned o (by simp [Session.messageIdCheckAt])
    (by simp [Session.messageIdCheckAt, Syntax.PStmt.isDec]) hc (by decide)
    (fun _ _ _ h => ⟨{ h.1 with }, h.2⟩) fun s hp => ?_
  obtain ⟨ht, h2⟩ := hP s hp
  have hw := treeAt_second hs ht h2
  obtain ⟨c', hc', hsafe⟩ := SessionCheck.messageIdCheck_safe o (s := Syntax.v "s1") (l := Syntax.v "l1") rfl rfl
    (by simp [ExpAvoids, SessionCheck.midNames]) (by simp [ExpAvoids, SessionCheck.midNames])
    (SessionFrame.blockAt b ci) (BitVec.ofNat 64 ((spans L).getD 1 (0, 0)).1) (cut L ((spans L).getD 1 (0, 0))) s
  rw [hc] at hc'; cases hc'
  exact Safe.conseq hsafe (fun u (hu : u = s) => ⟨hu, hu ▸ ⟨hw.start, hw.len, hw.blk, hw.bytes, hw.short, ht.ok,
    ht.jq⟩⟩) fun _ h => h

theorem treeAt_num {L w : List Byte} {s0 s u : PancakeState σ} (ht : TreeAt L s0 s)
    (hp : SessionCheck.NumPost w s u) : TreeAt L s0 u :=
  treeAt_check ht hp.1 (by decide) ⟨_, hp.2.1⟩ hp.2.2.2.1 hp.2.2.1 (by decide) (by decide) (by decide)

theorem kept_mid {w : List Byte} {s0 s u : PancakeState σ} (ht : Kept s0 s) (hp : SessionCheck.MidPost w s u) :
    Kept s0 u :=
  kept_but ht hp.1 (by decide) (by decide)

/-- **HEAD's, STAT's, ARTICLE's and BODY's branch**: with `A` arguments, the second word `a`, the reply `R`. -/
theorem read_frag (o : Oracle σ) {b : Word} {ci : Nat} {offered : Bool} {k : FrameSpec.Kind} {L : List Byte}
    {s0 : PancakeState σ} (hs : ClsIn b ci offered k L s0) {A R : Nat} (hA : A + 1 = (spans L).length)
    (h0 : A = 0 → R = if offered then 22 else 4)
    (hn : A = 1 → CommandSpec.isArticleNumber (cut L ((spans L).getD 1 (0, 0))) = true →
      R = if offered then 21 else 4)
    (hm : A = 1 → CommandSpec.isArticleNumber (cut L ((spans L).getD 1 (0, 0))) = false →
      CommandSpec.isMessageId (cut L ((spans L).getD 1 (0, 0))) = true → R = if offered then 17 else 5)
    (hx : A = 1 → CommandSpec.isArticleNumber (cut L ((spans L).getD 1 (0, 0))) = false →
      CommandSpec.isMessageId (cut L ((spans L).getD 1 (0, 0))) = false → R = 7)
    (h2 : 2 ≤ A → R = 7) :
    Frag o readTree (fun u => TreeAt L s0 u ∧ u.locals "args" = some (BitVec.ofNat 64 A)) (Out b s0 R) := by
  have hAs : A < 2 ^ 62 := by have := spans_length L; have := hs.line.short; omega
  let a := cut L ((spans L).getD 1 (0, 0))
  have st : ∀ {P : Assn σ} (X Y : CommandSpec.Reply), (∀ u, P u → Kept s0 u) →
      (∀ u, P u → offered = true → R = Session.replyCode X) → (∀ u, P u → offered = false → R = Session.replyCode Y) →
      Frag o [.ite Session.hasStore [Session.reply X] [Session.reply Y]] P (Out b s0 R) :=
    fun X Y hk hX hY => tree_ite o store_lower (fun s h => ⟨_, store_eval hs (hk s h)⟩)
      (leaf_frag o b X fun u ⟨h, hc⟩ =>
        ⟨hk u h, (hX u h (bw_ne0 (by rwa [store_eval hs (hk u h)] at hc))).symm⟩)
      (leaf_frag o b Y fun u ⟨h, hc⟩ =>
        ⟨hk u h, (hY u h (bw_eq0 (by rwa [store_eval hs (hk u h)] at hc))).symm⟩) (nodecl rfl) (nodecl rfl)
  refine tree_ite o (C := .cmp .equal (.var "args") (.const (BitVec.ofNat 64 0))) rfl
    (fun s h => ⟨_, argsEq_eval (by omega) (by decide) h.2⟩)
    (st _ _ (fun u h => h.1.1.toKept) (fun u ⟨h, hc⟩ ho => ?_) (fun u ⟨h, hc⟩ ho => ?_)) ?_ (nodecl rfl)
    (nodecl rfl)
  · rw [argsEq_eval (by omega) (by decide) h.2] at hc; rw [h0 (of_decide_eq_true (bw_ne0 hc)), ho]; rfl
  · rw [argsEq_eval (by omega) (by decide) h.2] at hc; rw [h0 (of_decide_eq_true (bw_ne0 hc)), ho]; rfl
  refine tree_ite o (C := .cmp .equal (.var "args") (.const (BitVec.ofNat 64 1))) rfl
    (fun s h => ⟨_, argsEq_eval (by omega) (by decide) h.1.2⟩) ?_
    (leaf_frag o b .syntax fun u ⟨⟨h, hc0⟩, hc1⟩ => ⟨h.1.toKept, by
      rw [argsEq_eval (by omega) (by decide) h.2] at hc0 hc1
      have := of_decide_eq_false (bw_eq0 hc0); have := of_decide_eq_false (bw_eq0 hc1)
      rw [h2 (by omega)]; rfl⟩)
    (nodecl rfl) (nodecl rfl)
  -- one argument
  let P1 : Assn σ := fun s => ((TreeAt L s0 s ∧ s.locals "args" = some (BitVec.ofNat 64 A)) ∧
      eval s (.cmp .equal (.var "args") (.const (BitVec.ofNat 64 0))) = some 0) ∧
      eval s (.cmp .equal (.var "args") (.const (BitVec.ofNat 64 1))) ≠ some 0
  have hA1 : ∀ s, P1 s → A = 1 := fun s ⟨⟨h, _⟩, hc⟩ => by
    rw [argsEq_eval (by omega) (by decide) h.2] at hc; exact of_decide_eq_true (bw_ne0 hc)
  have hP1 : ∀ s, P1 s → TreeAt L s0 s ∧ 2 ≤ (spans L).length := fun s h => ⟨h.1.1.1, by have := hA1 s h; omega⟩
  have fn := number_frag o hs (P := P1) hP1
  refine frag_append fn (tree_ite o (C := .var "ok") rfl (fun u ⟨s, _, hp⟩ => ⟨_, hp.2.1⟩) ?_ ?_ (nodecl rfl)
    (nodecl rfl))
  · refine st _ _ (fun u ⟨⟨s, h, hp⟩, _⟩ => (treeAt_num h.1.1.1 hp).toKept) (fun u ⟨⟨s, h, hp⟩, hc⟩ ho => ?_)
      (fun u ⟨⟨s, h, hp⟩, hc⟩ ho => ?_)
    · simp only [eval, hp.2.1] at hc; rw [hn (hA1 s h) (bw_ne0 hc), ho]; rfl
    · simp only [eval, hp.2.1] at hc; rw [hn (hA1 s h) (bw_ne0 hc), ho]; rfl
  · have fm := mid_frag o hs (P := fun u => (∃ s, P1 s ∧ SessionCheck.NumPost a s u) ∧
      eval u (.var "ok") = some 0) (fun u ⟨⟨s, h, hp⟩, _⟩ => ⟨treeAt_num h.1.1.1 hp, (hP1 s h).2⟩)
    have hnum : ∀ u1, (∃ s, P1 s ∧ SessionCheck.NumPost a s u1) ∧ eval u1 (.var "ok") = some 0 →
        A = 1 ∧ CommandSpec.isArticleNumber a = false := fun u1 ⟨⟨s, h, hp⟩, hc⟩ => by
      simp only [eval, hp.2.1] at hc; exact ⟨hA1 s h, bw_eq0 hc⟩
    have hkm : ∀ u, (∃ u1, ((∃ s, P1 s ∧ SessionCheck.NumPost a s u1) ∧ eval u1 (.var "ok") = some 0) ∧
        SessionCheck.MidPost a u1 u) → Kept s0 u := fun u ⟨u1, ⟨⟨s, h, hp⟩, _⟩, hq⟩ =>
      kept_mid (treeAt_num h.1.1.1 hp).toKept hq
    refine frag_append fm (tree_ite o (C := .var "ok") rfl (fun u ⟨_, _, hq⟩ => ⟨_, hq.2⟩) ?_
      (leaf_frag o b .syntax fun u ⟨hu, hc'⟩ => ⟨hkm u hu, ?_⟩) (nodecl rfl) (nodecl rfl))
    · refine st _ _ (fun u ⟨hu, _⟩ => hkm u hu) (fun u ⟨⟨u1, h1, hq⟩, hc'⟩ ho => ?_)
        (fun u ⟨⟨u1, h1, hq⟩, hc'⟩ ho => ?_)
      · simp only [eval, hq.2] at hc'
        obtain ⟨e1, e2⟩ := hnum u1 h1
        rw [hm e1 e2 (bw_ne0 hc'), ho]; rfl
      · simp only [eval, hq.2] at hc'
        obtain ⟨e1, e2⟩ := hnum u1 h1
        rw [hm e1 e2 (bw_ne0 hc'), ho]; rfl
    · obtain ⟨u1, h1, hq⟩ := hu
      simp only [eval, hq.2] at hc'
      obtain ⟨e1, e2⟩ := hnum u1 h1
      rw [hx e1 e2 (bw_eq0 hc')]; rfl

theorem found_lower : Lower.lowerExp SessionStore.found =
    some (.loadWord (.op .add .base (.const (BitVec.ofNat 64 (ownOff + ownRet))))) := by
  simp [SessionStore.found, SessionStore.ld, Lower.lowerExp, SessionAppend.at_lower SessionAppend.ret_facts.2.2.2]

/-- What a callee left in the return word, read. -/
theorem found_eval {b : Word} {ci : Nat} {offered : Bool} {k : FrameSpec.Kind} {L : List Byte} {s0 u : PancakeState σ}
    (hs : ClsIn b ci offered k L s0) (hb : u.baseAddr = b) (hd : u.memaddrs = s0.memaddrs) :
    eval u (.loadWord (.op .add .base (.const (BitVec.ofNat 64 (ownOff + ownRet))))) =
      some (u.memory (SessionCheck.retW b)) := by
  have := SessionAppend.retW_addr hs.hcov
  rw [SessionCheck.retW] at this ⊢
  simp only [eval, hb, hd, this, if_true]

/-- `groupName` as the code holds it. -/
def GnCode (code : String → Option (List String × PancakeProg)) : Prop :=
  ∃ body, code "groupName" = some (["c", "s1", "l1"], body) ∧ Lower.lower Session.groupName = some body

theorem retW_mem (b : Word) : SessionCheck.retW b ∈ clsWords b := by
  simp [clsWords, clsOffs, SessionCheck.retW]

/-- The call's result checked: a callee that gave back zero goes on. -/
theorem zeroRet_frag (o : Oracle σ) (rt : String) {P : Assn σ} (hP : Safe.ClockFree P)
    (h : ∀ s, P s → s.locals rt = some 0) : Frag o [.ite (Syntax.v rt) [.ret (Syntax.v rt)] []] P P :=
  frag_oneR (a := .cond (.var rt) (.ret (.var rt)) .skip) rfl rfl hP fun R =>
    WpRet.cond (fun s hs => ⟨_, h s hs⟩) (fun s ⟨hs, hne⟩ => absurd (h s hs) (by simpa [eval] using hne))
      (conseq (WpRet.skip o _ R) (fun s h => h.1) (fun _ _ h => h) (fun _ h => h))

/-- **GROUP's branch**: with `A` arguments, the second word `g`, the reply `R`. -/
theorem group_frag (o : Oracle σ) {b : Word} {ci : Nat} {offered : Bool} {k : FrameSpec.Kind} {L : List Byte}
    {s0 : PancakeState σ} (hs : ClsIn b ci offered k L s0) (hgn : GnCode s0.code) {A R : Nat}
    (hA : A + 1 = (spans L).length)
    (h1 : A = 1 → R = if CommandSpec.isGroupName (cut L ((spans L).getD 1 (0, 0))) then
      (if (cut L ((spans L).getD 1 (0, 0))).length ≤ CommandSpec.groupNameMax then 20 else 25) else 7)
    (h2 : A ≠ 1 → R = 7) :
    Frag o groupTree (fun u => TreeAt L s0 u ∧ u.locals "args" = some (BitVec.ofNat 64 A)) (Out b s0 R) := by
  obtain ⟨body, hcode, hlow⟩ := hgn
  have hAs : A < 2 ^ 62 := by have := spans_length L; have := hs.line.short; omega
  let p := (spans L).getD 1 (0, 0)
  let gw := cut L p
  refine tree_ite o (C := .cmp .equal (.var "args") (.const (BitVec.ofNat 64 1))) rfl
    (fun s h => ⟨_, argsEq_eval (by omega) (by decide) h.2⟩) ?_
    (leaf_frag o b .syntax fun u ⟨h, hc⟩ => ⟨h.1.toKept, by
      rw [argsEq_eval (by omega) (by decide) h.2] at hc; rw [h2 (of_decide_eq_false (bw_eq0 hc))]; rfl⟩)
    (fun y hy => by simp [declared, SessionStore.callS] at hy; subst hy; decide) (nodecl rfl)
  let P1 : Assn σ := fun s => (TreeAt L s0 s ∧ s.locals "args" = some (BitVec.ofNat 64 A)) ∧
    eval s (.cmp .equal (.var "args") (.const (BitVec.ofNat 64 1))) ≠ some 0
  have hA1 : ∀ s, P1 s → A = 1 := fun s ⟨h, hc⟩ => by
    rw [argsEq_eval (by omega) (by decide) h.2] at hc; exact of_decide_eq_true (bw_ne0 hc)
  let P2 : Assn σ := fun t => After b s0 t ∧ A = 1 ∧ t.locals "gn" = some 0 ∧
    t.memory (SessionCheck.retW b) = bw (CommandSpec.isGroupName gw) ∧ t.memaddrs = s0.memaddrs ∧ t.baseAddr = b ∧
    t.locals "l1" = some (BitVec.ofNat 64 gw.length)
  have fc : Frag o [.call "gn" "groupName" [Syntax.v "c", Syntax.v "s1", Syntax.v "l1"]] P1 P2 := by
    refine frag_call o (args := [.var "c", .var "s1", .var "l1"]) rfl (body := body)
      (Pc := fun s s1 => s1 = { decClock s with locals := fun k => (["c", "s1", "l1"].zip
        [BitVec.ofNat 64 ci, BitVec.ofNat 64 p.1, BitVec.ofNat 64 gw.length]).lookup k } ∧
          SessionCheck.GnPre b ci p.1 gw s1)
      (Rc := fun s => SessionCheck.gnRet b gw s.memory) (fun s h => ?_) (fun s h => ?_)
      (fun s u v h hR hsame => ?_)
    · intro s1 ⟨e, hpre⟩
      have := SessionCheck.groupName_run o b ci p.1 gw s1 hlow s1 ⟨rfl, hpre⟩
      have hm : s1.memory = s.memory := by rw [e]; rfl
      rw [hm] at this; exact this
    · have ht := h.1.1
      have h2' : 2 ≤ (spans L).length := by have := hA1 s h; omega
      have hw := treeAt_second hs ht h2'
      have hb := spans_bound L p (spans_getD_mem (by omega))
      have hgl : gw.length = p.2 := cut_length hb
      have hsh := hs.short
      refine ⟨[BitVec.ofNat 64 ci, BitVec.ofNat 64 p.1, BitVec.ofNat 64 gw.length], _, ?_,
        Block.lookupCode_of (by rw [ht.code]; exact hcode) (by decide) rfl, rfl, ?_⟩
      · simp only [evalArgs, eval, ht.loc "c" (by decide), hs.c, ht.s1, ht.l1, hgl]; rfl
      · exact ⟨by simp only [decClock]; rw [ht.base, hs.base], rfl, by have := hs.hci; omega, rfl, by omega, rfl,
          by omega, fun j hj => by
            simp only [decClock]; rw [SessionCheck.gnBlock_eq]; exact hw.bytes j hj,
          by simp only [decClock]; rw [ht.memaddrs]; exact SessionAppend.retW_addr hs.hcov⟩
    · obtain ⟨hv, hret, hother⟩ := hR
      have ht := h.1.1
      refine ⟨⟨fun y hy => ?_, fun a ha => ?_, hsame.1.trans ht.memaddrs, hsame.2.2.1.trans ht.be,
        hsame.2.1.trans ht.base, hsame.2.2.2.trans ht.code, ?_⟩, hA1 s h, by simp [setLocal, hv], hret,
        hsame.1.trans ht.memaddrs, by rw [hsame.2.1, ht.base, hs.base], ?_⟩
      · have : y ≠ "gn" := fun e => hy (by simp [e, clsNames])
        simp only [setLocal, if_neg this]; exact ht.loc y hy
      · have : a ≠ SessionCheck.retW b := fun e => ha (e ▸ retW_mem b)
        rw [hother a this, ht.memory]
      · obtain ⟨w, hw⟩ := ht.r; exact ⟨w, by simp [setLocal, hw]⟩
      · have hb := spans_bound L p (spans_getD_mem (by have := hA1 s h; omega))
        simp only [setLocal, if_neg (by decide : ("l1" : String) ≠ "gn")]
        rw [ht.l1, cut_length hb]
  have cP2 : Safe.ClockFree P2 := fun _ _ ⟨h, rest⟩ => ⟨{ h with }, rest⟩
  rw [SessionStore.callS]
  refine frag_append (xs := [_, _]) (frag_append (xs := [_]) fc (zeroRet_frag o "gn" cP2 fun s h => h.2.2.1)) ?_
  have hgl : gw.length < 2 ^ 63 := by
    have : gw.length ≤ L.length := by simp only [gw, cut, List.length_take, List.length_drop]; omega
    have := hs.line.short; omega
  have hfound : ∀ s, P2 s → eval s (.loadWord (.op .add .base (.const (BitVec.ofNat 64 (ownOff + ownRet))))) =
      some (bw (CommandSpec.isGroupName gw)) := fun s h => by
    rw [found_eval hs h.2.2.2.2.2.1 h.2.2.2.2.1, h.2.2.2.1]
  have hle : ∀ s, P2 s → eval s (leE (.var "l1") (.const (BitVec.ofNat 64 CommandSpec.groupNameMax))) =
      some (bw (decide (gw.length ≤ CommandSpec.groupNameMax))) := fun s h =>
    eval_le hgl (by decide) (by simp only [eval]; exact h.2.2.2.2.2.2) rfl
  refine tree_ite o found_lower (fun s h => ⟨_, hfound s h⟩) ?_
    (leafA_frag o b .syntax fun u ⟨h, hc⟩ => ⟨h.1, ?_⟩) (nodecl rfl) (nodecl rfl)
  · refine tree_ite o (C := leE (.var "l1") (.const (BitVec.ofNat 64 CommandSpec.groupNameMax))) rfl
      (fun s ⟨h, _⟩ => ⟨_, hle s h⟩)
      (leafA_frag o b (.select []) fun u ⟨⟨h, hc⟩, hl⟩ => ⟨h.1, ?_⟩)
      (leafA_frag o b .noSuchGroup fun u ⟨⟨h, hc⟩, hl⟩ => ⟨h.1, ?_⟩) (nodecl rfl) (nodecl rfl)
    · rw [hfound u h] at hc; rw [hle u h] at hl
      rw [h1 h.2.1, if_pos (bw_ne0 hc), if_pos (of_decide_eq_true (bw_ne0 hl))]; rfl
    · rw [hfound u h] at hc; rw [hle u h] at hl
      rw [h1 h.2.1, if_pos (bw_ne0 hc), if_neg (of_decide_eq_false (bw_eq0 hl))]; rfl
  · rw [hfound u h] at hc
    rw [h1 h.2.1, if_neg (by rw [bw_eq0 hc]; decide)]; rfl

/-! ### The branches on the command -/

/-- The test of `cmd` against a code. -/
theorem cmd_eval {s : PancakeState σ} {K : Nat} (hK : K < 2 ^ 63) (h : s.locals "cmd" = some (BitVec.ofNat 64 K))
    (j : Nat) (hj : j < 2 ^ 63) :
    eval s (.cmp .equal (.var "cmd") (.const (BitVec.ofNat 64 j))) = some (bw (decide (K = j))) :=
  eval_eq (by omega) (by omega) (by simp only [eval]; exact h) rfl

/-- The reply to a command with its arguments, as `replyIn` gives it on a command line. -/
def ans (offered : Bool) (c : CommandSpec.Cmd) (args : List (List Byte)) : CommandSpec.Reply :=
  if offered then CommandSpec.answerIn c args else CommandSpec.answer c args

theorem ans_capa (offered : Bool) (args : List (List Byte)) :
    (args.length = 0 → Session.replyCode (ans offered .capabilities args) = 1) ∧
    (args.length = 1 → Session.replyCode (ans offered .capabilities args) =
      if CommandSpec.isKeyword (args.getD 0 []) then 1 else 7) ∧
    (2 ≤ args.length → Session.replyCode (ans offered .capabilities args) = 7) := by
  rcases args with _ | ⟨a, _ | ⟨a2, rest⟩⟩
  · cases offered <;> simp [ans, CommandSpec.answerIn, CommandSpec.answer, Session.replyCode]
  · cases hk : CommandSpec.isKeyword a <;> cases offered <;>
      simp [ans, CommandSpec.answerIn, CommandSpec.answer, Session.replyCode, hk]
  · cases offered <;> simp [ans, CommandSpec.answerIn, CommandSpec.answer, Session.replyCode]

theorem ans_zero (offered : Bool) (c : CommandSpec.Cmd) (X : CommandSpec.Reply)
    (hc : c = .help ∧ X = .help ∨ c = .quit ∧ X = .quit ∨ (offered = true ∧ c = .post ∧ X = .post) ∨
      (offered = true ∧ (c = .next ∨ c = .last) ∧ X = .move true)) (args : List (List Byte)) :
    (args.length = 0 → Session.replyCode (ans offered c args) = Session.replyCode X) ∧
    (args.length ≠ 0 → Session.replyCode (ans offered c args) = 7) := by
  rcases hc with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, hc, rfl⟩ <;>
    (try rcases hc with rfl | rfl) <;> rcases args with _ | ⟨a, rest⟩ <;> (try cases offered) <;>
    simp [ans, CommandSpec.answerIn, CommandSpec.answer, Session.replyCode]

theorem ans_group (args : List (List Byte)) :
    (args.length = 1 → Session.replyCode (ans true .group args) =
      if CommandSpec.isGroupName (args.getD 0 []) then
        (if (args.getD 0 []).length ≤ CommandSpec.groupNameMax then 20 else 25) else 7) ∧
    (args.length ≠ 1 → Session.replyCode (ans true .group args) = 7) := by
  rcases args with _ | ⟨a, _ | ⟨a2, rest⟩⟩
  · simp [ans, CommandSpec.answerIn, CommandSpec.answer, Session.replyCode]
  · cases hg : CommandSpec.isGroupName a <;> by_cases hl : a.length ≤ CommandSpec.groupNameMax <;>
      simp [ans, CommandSpec.answerIn, Session.replyCode, hg, hl]
  · simp [ans, CommandSpec.answerIn, CommandSpec.answer, Session.replyCode]

theorem ans_read (offered : Bool) (c : CommandSpec.Cmd)
    (hc : c = .head ∨ c = .stat ∨ (offered = true ∧ (c = .article ∨ c = .body))) (args : List (List Byte)) :
    (args.length = 0 → ans offered c args = if offered then .current c else .noGroup) ∧
    (args.length = 1 → CommandSpec.isArticleNumber (args.getD 0 []) = true →
      ans offered c args = if offered then .byNumber c (CommandSpec.value (args.getD 0 [])) else .noGroup) ∧
    (args.length = 1 → CommandSpec.isArticleNumber (args.getD 0 []) = false →
      CommandSpec.isMessageId (args.getD 0 []) = true →
        ans offered c args = if offered then .lookup c 0 (args.getD 0 []) else .noSuchId) ∧
    (args.length = 1 → CommandSpec.isArticleNumber (args.getD 0 []) = false →
      CommandSpec.isMessageId (args.getD 0 []) = false → ans offered c args = .syntax) ∧
    (2 ≤ args.length → ans offered c args = .syntax) := by
  rcases hc with rfl | rfl | ⟨rfl, rfl | rfl⟩ <;> rcases args with _ | ⟨a, _ | ⟨a2, rest⟩⟩ <;> (try cases offered) <;>
    (try cases hn : CommandSpec.isArticleNumber a) <;> (try cases hm : CommandSpec.isMessageId a) <;>
    simp [ans, CommandSpec.answerIn, CommandSpec.answer, *]

theorem lowKK_capa : LowKK capaTree := lowK_any _ (k := .skip) (c := _) rfl
theorem lowKK_group : LowKK groupTree := lowK_any _ (k := .skip) (c := _) rfl
theorem lowKK_read : LowKK readTree := lowK_any _ (k := .skip) (c := _) rfl

/-- The arguments: the words after the first. -/
def argsOf (L : List Byte) : List (List Byte) := (spans L).tail.map (cut L)

theorem argsOf_head (L : List Byte) : (argsOf L).getD 0 [] = cut L ((spans L).getD 1 (0, 0)) := by
  rcases h : spans L with _ | ⟨p0, _ | ⟨p1, rest⟩⟩ <;> simp [argsOf, h, cut]

theorem argsOf_second (L : List Byte) : (argsOf L).getD 1 [] = cut L ((spans L).getD 2 (0, 0)) := by
  rcases h : spans L with _ | ⟨p0, _ | ⟨p1, _ | ⟨p2, rest⟩⟩⟩ <;> simp [argsOf, h, cut]

theorem argsOf_third (L : List Byte) : (argsOf L).getD 2 [] = cut L ((spans L).getD 3 (0, 0)) := by
  rcases h : spans L with _ | ⟨p0, _ | ⟨p1, _ | ⟨p2, _ | ⟨p3, rest⟩⟩⟩⟩ <;> simp [argsOf, h, cut]

theorem treeAt_set {L : List Byte} {s0 s : PancakeState σ} (h : TreeAt L s0 s) {x : String}
    (hx : x ∈ clsNames ∧ x ∉ ["w", "s0", "l0", "s1", "l1", "r", "cmd", "eqk", "jq", "ok", "val"]) (v : Value) :
    TreeAt L s0 (setL s x v) :=
  treeAt_but h (SessionCheck.but_set (SessionCheck.but_refl [x] s) (by simp) v)
    (fun y hy => by simp at hy; subst hy; exact ⟨hx.1, fun e => hx.2 (by simp_all)⟩) fun y hy => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
      rcases hy with rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [setL, setLocal] <;>
        rw [if_neg (fun e => hx.2 (by rw [← e]; decide))]
      · exact h.r
      · exact h.cmd
      · exact h.eqk
      · exact h.jq
      · exact h.ok
      · exact h.val

/-- The command a code stands for. -/
def cmdOf : Nat → Option CommandSpec.Cmd
  | 1 => some .capabilities | 2 => some .help | 3 => some .quit | 4 => some .head | 5 => some .stat
  | 6 => some .post | 7 => some .article | 8 => some .body | 9 => some .group | 10 => some .next
  | 11 => some .last | 12 => some .listgroup | 13 => some .list | 14 => some .date | 15 => some .newgroups
  | 16 => some .mode | 17 => some .over | 18 => some .hdr | 19 => some .xover | 20 => some .xhdr
  | 21 => some .authinfo | _ => none

theorem cmdOf_code (c : Option CommandSpec.Cmd) : cmdOf (cmdCode c) = c := by
  rcases c with _ | c
  · rfl
  · cases c <;> rfl

theorem cmdCode_lt (c : Option CommandSpec.Cmd) : cmdCode c < 22 := by
  rcases c with _ | c
  · decide
  · cases c <;> decide

/-- **The branches on the command once the arguments are counted**: if they go on, the code of the reply `ans`. -/
theorem args_frag (o : Oracle σ) {b : Word} {ci : Nat} {offered : Bool} {k : FrameSpec.Kind} {L : List Byte}
    {s0 : PancakeState σ} (hs : ClsIn b ci offered k L s0) (hgn : GnCode s0.code) {c : CommandSpec.Cmd}
    (hc : c = .capabilities ∨ c = .help ∨ c = .quit ∨ c = .head ∨ c = .stat ∨
      (offered = true ∧ (c = .post ∨ c = .article ∨ c = .body ∨ c = .group ∨ c = .next ∨ c = .last)))
    (hw1 : 1 ≤ (spans L).length) :
    Frag o argsTree (fun u => TreeAt L s0 u ∧ u.locals "cmd" = some (BitVec.ofNat 64 (cmdCode (some c))))
      (Out b s0 (Session.replyCode (ans offered c (argsOf L)))) := by
  have hsh := hs.line.short
  have hsp := spans_length L
  let A := (spans L).length - 1
  have hA : A + 1 = (spans L).length := by omega
  have hAs : A < 2 ^ 62 := by omega
  have hlen : (argsOf L).length = A := by simp [argsOf, A]
  have hhead := argsOf_head L
  let K := cmdCode (some c)
  have hK := cmdCode_lt (some c)
  let P3 : Assn σ := fun u => TreeAt L s0 u ∧ u.locals "cmd" = some (BitVec.ofNat 64 K) ∧
    u.locals "args" = some (BitVec.ofNat 64 A)
  have cmdEq : ∀ s, P3 s → ∀ j, j < 2 ^ 63 →
      eval s (.cmp .equal (.var "cmd") (.const (BitVec.ofNat 64 j))) = some (bw (decide (K = j))) := fun s h =>
    cmd_eval (by omega) h.2.1
  have f0 : Frag o [.dec "args" (Syntax.eSub (Syntax.v "w") (Syntax.n 1))]
      (fun u => TreeAt L s0 u ∧ u.locals "cmd" = some (BitVec.ofNat 64 K)) P3 :=
    frag_dec o (E := .op .sub (.var "w") (.const 1)) rfl fun s ⟨h, hk⟩ => ⟨BitVec.ofNat 64 A, by
        simp only [eval, h.w]; rw [show (1 : Word) = BitVec.ofNat 64 1 from rfl,
          SessionCheck.sub_small _ 1 hw1 (by omega)], treeAt_set h (by decide) _,
      by simp [setLocal, hk], by simp [setLocal]⟩
  rw [argsTree]
  refine frag_append (xs := [_]) f0 ?_
  have dec : ∀ j, K = j → cmdOf j = some c := fun j h => by rw [← h]; exact cmdOf_code (some c)
  have isC : ∀ s, P3 s → ∀ j, j < 2 ^ 63 → eval s (.cmp .equal (.var "cmd") (.const (BitVec.ofNat 64 j))) ≠ some 0 →
      cmdOf j = some c := fun s h j hj hc => by
    rw [cmdEq s h j hj] at hc; exact dec j (of_decide_eq_true (bw_ne0 hc))
  have notC : ∀ s, P3 s → ∀ j, j < 2 ^ 63 → eval s (.cmp .equal (.var "cmd") (.const (BitVec.ofNat 64 j))) = some 0 →
      K ≠ j := fun s h j hj hc => by
    rw [cmdEq s h j hj] at hc; exact of_decide_eq_false (bw_eq0 hc)
  have zero : ∀ (X : CommandSpec.Reply) (j : Nat) (cx : CommandSpec.Cmd), cmdOf j = some cx → j < 2 ^ 63 →
      (c = cx → c = .help ∧ X = .help ∨ c = .quit ∧ X = .quit ∨ (offered = true ∧ c = .post ∧ X = .post) ∨
        (offered = true ∧ (c = .next ∨ c = .last) ∧ X = .move true)) → ∀ {P : Assn σ},
      (∀ s, P s → P3 s ∧ cmdOf j = some c) →
      Frag o [.ite (Syntax.eEq (Syntax.v "args") (Syntax.n 0)) [Session.reply X] [Session.reply .syntax]] P
        (Out b s0 (Session.replyCode (ans offered c (argsOf L)))) := fun X j cx hj _ hx P hP =>
    frag_pure (c = cx) (fun s h => by have := (hP s h).2; rw [hj] at this; exact (Option.some.inj this).symm)
      (lowKK_one rfl rfl (a := .cond (.cmp .equal (.var "args") (.const (BitVec.ofNat 64 0)))
        (.assign "r" (.const (BitVec.ofNat 64 (Session.replyCode X))))
        (.assign "r" (.const (BitVec.ofNat 64 7))))) fun hcx => by
      obtain ⟨z0, z1⟩ := ans_zero offered c X (hx hcx) (argsOf L)
      exact frag_conseq (zero_frag o b X hAs (fun h => (z0 (by omega)).symm ▸ rfl) (fun h => z1 (by omega)))
        (fun s h => ⟨(hP s h).1.1, (hP s h).1.2.2⟩) fun _ h => h
  -- CAPABILITIES
  refine tree_ite o (C := .cmp .equal (.var "cmd") (.const (BitVec.ofNat 64 1))) rfl
    (fun s h => ⟨_, cmdEq s h 1 (by decide)⟩) ?_ ?_ (nodecl rfl) (nodecl rfl)
  · refine frag_pure (c = .capabilities) (fun s ⟨h, hc⟩ => by
      have := isC s h 1 (by decide) hc; simp only [cmdOf, Option.some.injEq] at this; exact this.symm) lowKK_capa
      fun hcc => ?_
    subst hcc
    obtain ⟨a0, a1, a2⟩ := ans_capa offered (argsOf L)
    exact frag_conseq (capa_frag o hs hA (fun h => a0 (by omega)) (fun h => by rw [a1 (by omega), hhead])
      (fun h => a2 (by omega))) (fun s ⟨h, _⟩ => ⟨h.1, h.2.2⟩) (fun _ h => h)
  -- HELP, QUIT, POST
  refine tree_ite o (C := .cmp .equal (.var "cmd") (.const (BitVec.ofNat 64 2))) rfl
    (fun s h => ⟨_, cmdEq s h.1 2 (by decide)⟩)
    (zero .help 2 .help rfl (by decide) (fun h => Or.inl ⟨h, rfl⟩) fun s ⟨⟨h, _⟩, hc⟩ => ⟨h, isC s h 2 (by decide) hc⟩)
    ?_ (nodecl rfl) (nodecl rfl)
  refine tree_ite o (C := .cmp .equal (.var "cmd") (.const (BitVec.ofNat 64 3))) rfl
    (fun s h => ⟨_, cmdEq s h.1.1 3 (by decide)⟩)
    (zero .quit 3 .quit rfl (by decide) (fun h => Or.inr (Or.inl ⟨h, rfl⟩))
      fun s ⟨⟨⟨h, _⟩, _⟩, hc⟩ => ⟨h, isC s h 3 (by decide) hc⟩) ?_ (nodecl rfl) (nodecl rfl)
  have offd : ∀ cx, c = cx → cx ≠ .capabilities → cx ≠ .help → cx ≠ .quit → cx ≠ .head → cx ≠ .stat →
      offered = true := fun cx e h1 h2 h3 h4 h5 => by
    subst e; rcases hc with h | h | h | h | h | ⟨ho, -⟩ <;> first | exact ho | contradiction
  refine tree_ite o (C := .cmp .equal (.var "cmd") (.const (BitVec.ofNat 64 6))) rfl
    (fun s h => ⟨_, cmdEq s h.1.1.1 6 (by decide)⟩)
    (zero .post 6 .post rfl (by decide) (fun h => Or.inr (Or.inr (Or.inl ⟨offd .post h (by decide) (by decide)
      (by decide) (by decide) (by decide), h, rfl⟩)))
      fun s ⟨⟨⟨⟨h, _⟩, _⟩, _⟩, hc⟩ => ⟨h, isC s h 6 (by decide) hc⟩) ?_ (nodecl rfl) (nodecl rfl)
  -- GROUP
  refine tree_ite o (C := .cmp .equal (.var "cmd") (.const (BitVec.ofNat 64 9))) rfl
    (fun s h => ⟨_, cmdEq s h.1.1.1.1 9 (by decide)⟩) ?_ ?_ (nodecl rfl) (nodecl rfl)
  · refine frag_pure (c = .group) (fun s ⟨⟨⟨⟨⟨h, _⟩, _⟩, _⟩, _⟩, hc⟩ => by
      have := isC s h 9 (by decide) hc; simp only [cmdOf, Option.some.injEq] at this; exact this.symm) lowKK_group
      fun hcc => ?_
    have ho := offd .group hcc (by decide) (by decide) (by decide) (by decide) (by decide)
    subst hcc ho
    obtain ⟨g1, g2⟩ := ans_group (argsOf L)
    exact frag_conseq (group_frag o hs hgn hA (fun h => by rw [g1 (by omega), hhead]) (fun h => g2 (by omega)))
      (fun s ⟨⟨⟨⟨⟨h, _⟩, _⟩, _⟩, _⟩, _⟩ => ⟨h.1, h.2.2⟩) (fun _ h => h)
  -- NEXT and LAST
  have hor : ∀ s, P3 s → eval s (or2E (.cmp .equal (.var "cmd") (.const (BitVec.ofNat 64 10)))
      (.cmp .equal (.var "cmd") (.const (BitVec.ofNat 64 11)))) = some (bw (decide (K = 10) || decide (K = 11))) :=
    fun s h => eval_or2 (cmdEq s h 10 (by decide)) (cmdEq s h 11 (by decide))
  refine tree_ite o (C := or2E (.cmp .equal (.var "cmd") (.const (BitVec.ofNat 64 10)))
      (.cmp .equal (.var "cmd") (.const (BitVec.ofNat 64 11)))) rfl
    (fun s h => ⟨_, hor s h.1.1.1.1.1⟩) ?_ ?_ (nodecl rfl) (nodecl rfl)
  · refine frag_pure (c = .next ∨ c = .last) (fun s ⟨⟨⟨⟨⟨⟨h, _⟩, _⟩, _⟩, _⟩, _⟩, hc⟩ => by
        rw [hor s h] at hc
        have := bw_ne0 hc
        simp only [Bool.or_eq_true, decide_eq_true_eq] at this
        rcases this with e | e
        · have := dec 10 e; simp only [cmdOf, Option.some.injEq] at this; exact Or.inl this.symm
        · have := dec 11 e; simp only [cmdOf, Option.some.injEq] at this; exact Or.inr this.symm) (lowKK_one rfl rfl
            (a := .cond (.cmp .equal (.var "args")
      (.const (BitVec.ofNat 64 0))) (.assign "r" (.const (BitVec.ofNat 64 23))) (.assign "r"
          (.const (BitVec.ofNat 64 7)))))
      fun hcc => ?_
    have ho : offered = true := by
      rcases hcc with e | e
      · exact offd .next e (by decide) (by decide) (by decide) (by decide) (by decide)
      · exact offd .last e (by decide) (by decide) (by decide) (by decide) (by decide)
    obtain ⟨z0, z1⟩ := ans_zero offered c (.move true) (Or.inr (Or.inr (Or.inr ⟨ho, hcc, rfl⟩))) (argsOf L)
    exact frag_conseq (zero_frag o b (.move true) hAs (fun h => (z0 (by omega)).symm ▸ rfl) (fun h => z1 (by omega)))
      (fun s ⟨⟨⟨⟨⟨⟨h, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩ => ⟨h.1, h.2.2⟩) fun _ h => h
  -- HEAD, STAT, ARTICLE and BODY
  refine frag_pure (c = .head ∨ c = .stat ∨ (offered = true ∧ (c = .article ∨ c = .body)))
    (fun s ⟨⟨⟨⟨⟨⟨h, c1⟩, c2⟩, c3⟩, c6⟩, c9⟩, c10⟩ => ?_) lowKK_read fun hcc => ?_
  · have n1 := notC s h 1 (by decide) c1
    have n2 := notC s h 2 (by decide) c2
    have n3 := notC s h 3 (by decide) c3
    have n6 := notC s h 6 (by decide) c6
    have n9 := notC s h 9 (by decide) c9
    rw [hor s h] at c10
    have n10 := bw_eq0 c10
    simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not] at n10
    rcases hc with e | e | e | e | e | ⟨ho, e | e | e | e | e | e⟩ <;> subst e
    · exact absurd rfl n1
    · exact absurd rfl n2
    · exact absurd rfl n3
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact absurd rfl n6
    · exact Or.inr (Or.inr ⟨ho, Or.inl rfl⟩)
    · exact Or.inr (Or.inr ⟨ho, Or.inr rfl⟩)
    · exact absurd rfl n9
    · exact absurd rfl n10.1
    · exact absurd rfl n10.2
  · obtain ⟨r0, r1, r2, r3, r4⟩ := ans_read offered c hcc (argsOf L)
    rw [hhead] at r1 r2 r3
    exact frag_conseq (read_frag o hs hA (fun h => by rw [r0 (by omega)]; cases offered <;> rfl)
      (fun h hn => by rw [r1 (by omega) hn]; cases offered <;> rfl)
      (fun h hn hm => by rw [r2 (by omega) hn hm]; cases offered <;> rfl)
      (fun h hn hm => by rw [r3 (by omega) hn hm]; rfl) (fun h => by rw [r4 (by omega)]; rfl))
      (fun s ⟨⟨⟨⟨⟨⟨h, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩ => ⟨h.1, h.2.2⟩) (fun _ h => h)

/-! ### The functions `classify` calls for the listings and the overview -/

/-- A function's entry with connection `ci`'s line `L` and the command coded `K`. -/
structure VEntry (b : Word) (ci K : Nat) (L : List Byte) (s : PancakeState σ) : Prop where
  base : s.baseAddr = b
  hb : b.toNat % 8 = 0
  hcov : Analyzer.Covers SessionLayout.size s.memaddrs b
  c : s.locals "c" = some (BitVec.ofNat 64 ci)
  hci : ci < conns
  cmd : s.locals "cmd" = some (BitVec.ofNat 64 K)
  kept : s.memory (SessionFrame.blockAt b ci + BitVec.ofNat 64 32) = BitVec.ofNat 64 L.length
  bytes : ∀ j (h : j < L.length), memLoadByte s.memory s.memaddrs s.be
    (SessionFrame.blockAt b ci + BitVec.ofNat 64 40 + BitVec.ofNat 64 j) = some L[j]
  short : L.length ≤ News.SessionSpec.lineLimit
  texts : SessionAppend.TextsIn b s.memory s.memaddrs s.be

/-- Such a line is far shorter than a word's range. -/
theorem VEntry.short62 {b : Word} {ci K : Nat} {L : List Byte} {s : PancakeState σ} (he : VEntry b ci K L s) :
    L.length < 2 ^ 62 := by
  have := he.short; simp [News.SessionSpec.lineLimit] at this; omega

/-- What such a function gives back: zero, the reply's code `R` in the return word. Every word but `clsWords` is as it
was. -/
def CallRet (b : Word) (R : Nat) (m0 : Word → Word) : Ret :=
  fun v m => v = 0 ∧ m (SessionCheck.retW b) = BitVec.ofNat 64 R ∧ ∀ a, a ∉ clsWords b → m a = m0 a

/-- The function `f` as the code holds it, for the commands `cs` on a line of words. If it returns, it gives back zero,
the code of `answerIn`'s reply to the arguments in the return word. -/
def FnOk (o : Oracle σ) (f : String) (b : Word) (cs : CommandSpec.Cmd → Prop)
    (code : String → Option (List String × PancakeProg)) : Prop :=
  ∃ body, code f = some (["c", "cmd"], body) ∧ ∀ ci c L (s1 : PancakeState σ), cs c → 1 ≤ (spans L).length →
    VEntry b ci (cmdCode (some c)) L s1 → s1.code = code →
    SafeR o (fun s => s = s1) body (CallRet b (Session.replyCode (CommandSpec.answerIn c (argsOf L))) s1.memory)
      (fun _ => False)

/-- **A call of such a function, its reply taken.** -/
theorem callFound_frag (o : Oracle σ) {b : Word} {ci : Nat} {offered : Bool} {k : FrameSpec.Kind} {L : List Byte}
    {s0 : PancakeState σ} (hs : ClsIn b ci offered k L s0) {f rt : String} {cs : CommandSpec.Cmd → Prop}
    (hf : FnOk o f b cs s0.code) (hrt : rt ∈ clsNames ∧ rt ≠ "r") {c : CommandSpec.Cmd} (hc : cs c)
    (hw1 : 1 ≤ (spans L).length) {P : Assn σ}
    (hP : ∀ s, P s → TreeAt L s0 s ∧ s.locals "cmd" = some (BitVec.ofNat 64 (cmdCode (some c)))) :
    Frag o (SessionStore.callS rt f [Syntax.v "c", Syntax.v "cmd"] ++ [.assign "r" SessionStore.found]) P
      (Out b s0 (Session.replyCode (CommandSpec.answerIn c (argsOf L)))) := by
  obtain ⟨body, hcode, hsafe⟩ := hf
  let R := Session.replyCode (CommandSpec.answerIn c (argsOf L))
  let P2 : Assn σ := fun t => After b s0 t ∧ t.locals rt = some 0 ∧
    t.memory (SessionCheck.retW b) = BitVec.ofNat 64 R ∧ t.memaddrs = s0.memaddrs ∧ t.baseAddr = b
  have cP2 : Safe.ClockFree P2 := fun _ _ ⟨h, rest⟩ => ⟨{ h with }, rest⟩
  have fc : Frag o [.call rt f [Syntax.v "c", Syntax.v "cmd"]] P P2 := by
    refine frag_call o (args := [.var "c", .var "cmd"]) rfl (body := body)
      (Pc := fun s s1 => s1 = { decClock s with locals := fun x => (["c", "cmd"].zip
        [BitVec.ofNat 64 ci, BitVec.ofNat 64 (cmdCode (some c))]).lookup x })
      (Rc := fun s => CallRet b R s.memory) (fun s h => ?_) (fun s h => ?_) (fun s u v h hR hsame => ?_)
    · obtain ⟨ht, hk⟩ := hP s h
      intro s1 e
      have hm : s1.memory = s0.memory := by rw [e]; exact ht.memory
      have hd : s1.memaddrs = s0.memaddrs := by rw [e]; exact ht.memaddrs
      have hbe : s1.be = s0.be := by rw [e]; exact ht.be
      have hv : VEntry b ci (cmdCode (some c)) L s1 := by
        refine ⟨by rw [e]; exact ht.base.trans hs.base, hs.hb, by rw [hd]; exact hs.hcov, by rw [e]; rfl, hs.hci,
          by rw [e]; rfl, by rw [hm]; exact hs.keptW, fun j hj => ?_, hs.short, by rw [hm, hd, hbe]; exact hs.texts⟩
        rw [hm, hd, hbe]; exact hs.line.bytes j hj
      have := hsafe ci c L s1 hc hw1 hv (by rw [e]; exact ht.code) s1 rfl
      rw [hm] at this
      show OkR (CallRet b R s.memory) _ _
      rw [ht.memory]; exact this
    · obtain ⟨ht, hk⟩ := hP s h
      exact ⟨[BitVec.ofNat 64 ci, BitVec.ofNat 64 (cmdCode (some c))], _,
        by simp only [evalArgs, eval, ht.loc "c" (by decide), hs.c, hk],
        Block.lookupCode_of (by rw [ht.code]; exact hcode) (by decide) rfl, rfl⟩
    · obtain ⟨ht, hk⟩ := hP s h
      obtain ⟨hv, hret, hother⟩ := hR
      refine ⟨⟨fun y hy => ?_, fun a ha => ?_, hsame.1.trans ht.memaddrs, hsame.2.2.1.trans ht.be,
        hsame.2.1.trans ht.base, hsame.2.2.2.trans ht.code, ?_⟩, by simp [setLocal, hv], hret,
        hsame.1.trans ht.memaddrs, by rw [hsame.2.1, ht.base, hs.base]⟩
      · have : y ≠ rt := fun e => hy (e ▸ hrt.1)
        simp only [setLocal, if_neg this]; exact ht.loc y hy
      · rw [hother a ha, ht.memory]
      · obtain ⟨w, hw⟩ := ht.r
        exact ⟨w, by simp only [setLocal, if_neg (Ne.symm hrt.2)]; exact hw⟩
  rw [SessionStore.callS]
  refine frag_append (xs := [_, _]) (frag_append (xs := [_]) fc (zeroRet_frag o rt cP2 fun s h => h.2.1)) ?_
  refine frag_one (a := .assign "r" (.loadWord (.op .add .base (.const (BitVec.ofNat 64 (ownOff + ownRet))))))
    (by simp [Lower.lowerStmt1, found_lower]) rfl rfl (out_clock b s0 R) (Safe.assign fun u h => ?_)
  obtain ⟨v, hv⟩ := h.1.r
  refine ⟨_, v, found_eval hs h.2.2.2.2 h.2.2.2.1, hv, ?_⟩
  exact ⟨fun y hy => by
      have : y ≠ "r" := fun e => hy (by simp [e, clsNames])
      simp only [setLocal, if_neg this]; exact h.1.loc y hy,
    h.1.memory, h.1.memaddrs, h.1.be, h.1.base, h.1.code, by simp [setLocal, h.2.2.1, R]⟩

/-! ### The branches on whether the line names a command -/

theorem pickFold_cases (u : List Byte) : ∀ (ps : List (Nat × Nat)) (c : Nat),
    pickFold u ps c = c ∨ ∃ p ∈ ps, pickFold u ps c = p.2
  | [], c => Or.inl rfl
  | p :: ps, c => by
    have hs : pickFold u (p :: ps) c = pickFold u ps (if u = texts.getD p.1 [] then p.2 else c) := rfl
    rw [hs]
    rcases pickFold_cases u ps (if u = texts.getD p.1 [] then p.2 else c) with h | ⟨q, hq, h⟩
    · rw [h]
      by_cases e : u = texts.getD p.1 []
      · exact Or.inr ⟨p, List.mem_cons_self .., if_pos e⟩
      · exact Or.inl (if_neg e)
    · exact Or.inr ⟨q, List.mem_cons_of_mem _ hq, h⟩

/-- Without a store a line names a command of the base set or none. -/
theorem commandIn_base (w : List Byte) {c : CommandSpec.Cmd} (h : CommandSpec.commandIn false w = some c) :
    c = .capabilities ∨ c = .help ∨ c = .quit ∨ c = .head ∨ c = .stat ∨ c = .mode ∨ c = .authinfo := by
  have hp : pickFold (w.map CommandSpec.upper) baseNames 0 = cmdCode (some c) := by
    have := pick_spec false w; rw [h] at this; simpa using this
  have hc := cmdOf_code (some c)
  rcases pickFold_cases (w.map CommandSpec.upper) baseNames 0 with e | ⟨p, hp', e⟩
  · rw [← hp, e] at hc; simp [cmdOf] at hc
  · rw [← hp, e] at hc
    simp only [baseNames, List.mem_cons, List.not_mem_nil, or_false] at hp'
    rcases hp' with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [cmdOf] at hc <;> simp [← hc]

theorem ans_authinfo (offered : Bool) (args : List (List Byte)) :
    Session.replyCode (ans offered .authinfo args) = 50 := by
  cases offered <;> rcases args with _ | ⟨a, _ | ⟨a2, _ | ⟨a3, rest⟩⟩⟩ <;> rfl

theorem ans_mode (args : List (List Byte)) : ans false .mode args = CommandSpec.answerIn .mode args := by
  rcases args with _ | ⟨a, _ | ⟨a2, rest⟩⟩ <;> rfl

/-- The commands `viewClassify` answers. -/
def IsView (c : CommandSpec.Cmd) : Prop := c = .over ∨ c = .hdr ∨ c = .xover ∨ c = .xhdr
/-- The commands `listClassify` answers. -/
def IsList (c : CommandSpec.Cmd) : Prop := c = .listgroup ∨ c = .list ∨ c = .date ∨ c = .newgroups ∨ c = .mode

theorem kind_eval {k : FrameSpec.Kind} {s : PancakeState σ}
    (h : s.locals "kind" = some (BitVec.ofNat 64 (FramerProg.kindCode k))) :
    eval s (.cmp .equal (.cmp .equal (.var "kind") (.const (BitVec.ofNat 64 1))) (.const (BitVec.ofNat 64 0))) =
      some (bw (decide (k ≠ .command))) := by
  cases k <;> simp [eval, h, FramerProg.kindCode, bw]

theorem words_split {L : List Byte} (hw1 : 1 ≤ (spans L).length) :
    CommandSpec.words L = cut L ((spans L).getD 0 (0, 0)) :: argsOf L := by
  rw [words_spans]
  rcases h : spans L with _ | ⟨p0, rest⟩
  · rw [h] at hw1; simp at hw1
  · simp [argsOf, h]

theorem cmdCode_some (c : CommandSpec.Cmd) : cmdCode (some c) ≠ 0 := by cases c <;> decide

theorem code_auth {c : CommandSpec.Cmd} (h : cmdCode (some c) = 21) : c = .authinfo := by
  have := cmdOf_code (some c); rw [h] at this; simpa [cmdOf] using this.symm

theorem code_view {c : CommandSpec.Cmd} (hv : IsView c) : 17 ≤ cmdCode (some c) ∧ cmdCode (some c) ≠ 21 := by
  rcases hv with rfl | rfl | rfl | rfl <;> decide

theorem code_notView {c : CommandSpec.Cmd} (hv : ¬IsView c) (ha : c ≠ .authinfo) : cmdCode (some c) < 17 := by
  cases c <;> simp_all [IsView, cmdCode]

theorem code_list {c : CommandSpec.Cmd} (hl : IsList c) : 12 ≤ cmdCode (some c) ∧ cmdCode (some c) < 17 := by
  rcases hl with rfl | rfl | rfl | rfl | rfl <;> decide

theorem code_notList {c : CommandSpec.Cmd} (hl : ¬IsList c) (hv : ¬IsView c) (ha : c ≠ .authinfo) :
    cmdCode (some c) < 12 := by
  cases c <;> simp_all [IsView, IsList, cmdCode]

theorem rest_cmd {offered : Bool} {c : CommandSpec.Cmd}
    (base : offered = false → c = .capabilities ∨ c = .help ∨ c = .quit ∨ c = .head ∨ c = .stat ∨ c = .mode ∨
      c = .authinfo) (hl : ¬IsList c) (hv : ¬IsView c) (ha : c ≠ .authinfo) :
    c = .capabilities ∨ c = .help ∨ c = .quit ∨ c = .head ∨ c = .stat ∨
      (offered = true ∧ (c = .post ∨ c = .article ∨ c = .body ∨ c = .group ∨ c = .next ∨ c = .last)) := by
  cases ho : offered
  · rcases base ho with e | e | e | e | e | e | e <;> subst e <;> simp_all [IsList]
  · cases c <;> simp_all [IsView, IsList]

theorem args_decl : ∀ y ∈ declared argsTree, y ∈ clsNames ∧ y ≠ "r" := fun y hy => by
  rw [show declared argsTree = ["args"] from rfl] at hy; simp at hy; subst hy; decide

theorem callS_decl (rt f : String) (as : List Syntax.PExpr) (hrt : rt ∈ clsNames ∧ rt ≠ "r") :
    ∀ y ∈ declared (SessionStore.callS rt f as ++ [.assign "r" SessionStore.found]), y ∈ clsNames ∧ y ≠ "r" :=
  fun y hy => by simp [declared, SessionStore.callS] at hy; subst hy; exact hrt

/-- The branches once the line is known to name the command `c`. If they go on, `r` holds its reply code `ans`. -/
theorem known_frag (o : Oracle σ) {b : Word} {ci : Nat} {offered : Bool} {k : FrameSpec.Kind} {L : List Byte}
    {s0 : PancakeState σ} (hs : ClsIn b ci offered k L s0) (hgn : GnCode s0.code)
    (hvc : FnOk o "viewClassify" b IsView s0.code) (hlc : FnOk o "listClassify" b IsList s0.code)
    (hw1 : 1 ≤ (spans L).length) {c : CommandSpec.Cmd}
    (base : offered = false → c = .capabilities ∨ c = .help ∨ c = .quit ∨ c = .head ∨ c = .stat ∨ c = .mode ∨
      c = .authinfo) {P : Assn σ}
    (hP : ∀ s, P s → TreeAt L s0 s ∧ s.locals "cmd" = some (BitVec.ofNat 64 (cmdCode (some c)))) :
    Frag o knownTree P (Out b s0 (Session.replyCode (ans offered c (argsOf L)))) := by
  have hKl := cmdCode_lt (some c)
  have ev : ∀ s, P s → ∀ j, j < 2 ^ 63 →
      eval s (.cmp .equal (.var "cmd") (.const (BitVec.ofNat 64 j))) = some (bw (decide (cmdCode (some c) = j))) :=
    fun s h => cmd_eval (by omega) (hP s h).2
  have le : ∀ s, P s → ∀ j, j < 2 ^ 63 →
      eval s (leE (.const (BitVec.ofNat 64 j)) (.var "cmd")) = some (bw (decide (j ≤ cmdCode (some c)))) :=
    fun s h j hj => eval_le (by omega) (by omega) rfl (by simp only [eval]; exact (hP s h).2)
  -- AUTHINFO
  by_cases hca : c = .authinfo
  · subst hca
    exact tree_ite o (C := .cmp .equal (.var "cmd") (.const (BitVec.ofNat 64 21))) rfl
      (fun s h => ⟨_, ev s h 21 (by decide)⟩)
      (leaf_frag o b (.authinfo []) fun u ⟨h, _⟩ => ⟨(hP u h).1.toKept, (ans_authinfo offered _).symm⟩)
      (frag_unsat (lowK_any _ (k := .skip) (c := _) rfl) fun s ⟨h, hc⟩ => by
        rw [ev s h 21 (by decide)] at hc; exact absurd hc (by decide)) (nodecl rfl) (nodecl rfl)
  refine tree_ite o (C := .cmp .equal (.var "cmd") (.const (BitVec.ofNat 64 21))) rfl
    (fun s h => ⟨_, ev s h 21 (by decide)⟩)
    (frag_unsat (lowK_any _ (k := .skip) (c := _) rfl) fun s ⟨h, hc⟩ => by
      rw [ev s h 21 (by decide)] at hc
      exact hca (code_auth (of_decide_eq_true (bw_ne0 hc)))) ?_ (nodecl rfl)
    (nodecl rfl)
  -- OVER, HDR, XOVER and XHDR
  by_cases hv : IsView c
  · have ho : offered = true := by
      cases ho : offered
      · rcases base ho with e | e | e | e | e | e | e <;> subst e <;> simp [IsView] at hv
      · rfl
    have hcv := code_view hv
    refine tree_ite o (C := leE (.const (BitVec.ofNat 64 17)) (.var "cmd")) rfl
      (fun s h => ⟨_, le s h.1 17 (by decide)⟩) ?_
      (frag_unsat (lowK_any _ (k := .skip) (c := _) rfl) fun s ⟨⟨h, _⟩, hc⟩ => by
        rw [le s h 17 (by decide)] at hc; exact absurd hcv.1 (of_decide_eq_false (bw_eq0 hc)))
      (callS_decl _ _ _ (by decide)) (nodecl rfl)
    rw [ans, if_pos ho]
    exact callFound_frag o hs hvc (rt := "vc") (by decide) hv hw1 fun s h => hP s h.1.1
  have hnv := code_notView hv hca
  refine tree_ite o (C := leE (.const (BitVec.ofNat 64 17)) (.var "cmd")) rfl
    (fun s h => ⟨_, le s h.1 17 (by decide)⟩)
    (frag_unsat (lowK_any _ (k := .skip) (c := _) rfl) fun s ⟨⟨h, _⟩, hc⟩ => by
      rw [le s h 17 (by decide)] at hc
      exact absurd hnv (Nat.not_lt.mpr (of_decide_eq_true (bw_ne0 hc)))) ?_
    (callS_decl _ _ _ (by decide)) (nodecl rfl)
  -- LISTGROUP, LIST, DATE, NEWGROUPS and MODE
  by_cases hl : IsList c
  · have hcl := code_list hl
    refine tree_ite o (C := leE (.const (BitVec.ofNat 64 12)) (.var "cmd")) rfl
      (fun s h => ⟨_, le s h.1.1 12 (by decide)⟩) ?_
      (frag_unsat (lowK_any _ (k := .skip) (c := _) rfl) fun s ⟨⟨⟨h, _⟩, _⟩, hc⟩ => by
        rw [le s h 12 (by decide)] at hc; exact absurd hcl.1 (of_decide_eq_false (bw_eq0 hc)))
      (callS_decl _ _ _ (by decide)) args_decl
    have he : ans offered c (argsOf L) = CommandSpec.answerIn c (argsOf L) := by
      cases ho : offered
      · rcases base ho with e | e | e | e | e | e | e <;> subst e <;> simp [IsList] at hl
        exact ans_mode _
      · rfl
    rw [he]
    exact callFound_frag o hs hlc (rt := "lc") (by decide) hl hw1 fun s h => hP s h.1.1.1
  have hnl := code_notList hl hv hca
  refine tree_ite o (C := leE (.const (BitVec.ofNat 64 12)) (.var "cmd")) rfl
    (fun s h => ⟨_, le s h.1.1 12 (by decide)⟩)
    (frag_unsat (lowK_any _ (k := .skip) (c := _) rfl) fun s ⟨⟨⟨h, _⟩, _⟩, hc⟩ => by
      rw [le s h 12 (by decide)] at hc
      exact absurd hnl (Nat.not_lt.mpr (of_decide_eq_true (bw_ne0 hc)))) ?_
    (callS_decl _ _ _ (by decide)) args_decl
  exact frag_conseq (args_frag o hs hgn (rest_cmd base hl hv hca) hw1) (fun s h => hP s h.1.1.1) fun _ h => h

/-- **The branches on the command**: if they go on, the code of the reply `replyIn` gives the line. -/
theorem cmd_frag (o : Oracle σ) {b : Word} {ci : Nat} {offered : Bool} {k : FrameSpec.Kind} {L : List Byte}
    {s0 : PancakeState σ} (hs : ClsIn b ci offered k L s0) (hgn : GnCode s0.code)
    (hvc : FnOk o "viewClassify" b IsView s0.code) (hlc : FnOk o "listClassify" b IsList s0.code)
    (hw1 : 1 ≤ (spans L).length) :
    Frag o cmdTree (fun u => TreeAt L s0 u ∧ u.locals "cmd" = some (BitVec.ofNat 64
        (cmdCode (CommandSpec.commandIn offered (cut L ((spans L).getD 0 (0, 0)))))))
      (Out b s0 (Session.replyCode (CommandSpec.replyIn offered ⟨k, L⟩))) := by
  let w0 := cut L ((spans L).getD 0 (0, 0))
  have hR : CommandSpec.replyIn offered ⟨k, L⟩ = match CommandSpec.commandIn offered w0 with
      | none => .unknown | some c => if k = .command then ans offered c (argsOf L) else .syntax := by
    simp only [CommandSpec.replyIn, words_split hw1, ans]; rfl
  rw [cmdTree, hR]
  have ev : ∀ s cv, TreeAt L s0 s ∧ s.locals "cmd" = some (BitVec.ofNat 64 (cmdCode cv)) → ∀ j, j < 2 ^ 63 →
      eval s (.cmp .equal (.var "cmd") (.const (BitVec.ofNat 64 j))) = some (bw (decide (cmdCode cv = j))) :=
    fun s cv h => cmd_eval (by have := cmdCode_lt cv; omega) h.2
  have kd : ∀ s, TreeAt L s0 s → s.locals "kind" = some (BitVec.ofNat 64 (FramerProg.kindCode k)) := fun s h => by
    rw [h.loc "kind" (by decide)]; exact hs.kind
  rcases hcv : CommandSpec.commandIn offered w0 with _ | c
  · -- no command
    refine tree_ite o (C := .cmp .equal (.var "cmd") (.const (BitVec.ofNat 64 0))) rfl
      (fun s h => ⟨_, ev s none h 0 (by decide)⟩) (leaf_frag o b .unknown fun u ⟨h, _⟩ => ⟨h.1.toKept, rfl⟩)
      (frag_unsat (lowK_any _ (k := .skip) (c := _) rfl) fun s ⟨h, hc⟩ => by
        rw [ev s none h 0 (by decide)] at hc; exact absurd hc (by decide)) (nodecl rfl) (nodecl rfl)
  have hK0 := cmdCode_some c
  refine tree_ite o (C := .cmp .equal (.var "cmd") (.const (BitVec.ofNat 64 0))) rfl
    (fun s h => ⟨_, ev s _ h 0 (by decide)⟩)
    (frag_unsat (lowK_any _ (k := .skip) (c := _) rfl) fun s ⟨h, hc⟩ => by
      rw [ev s _ h 0 (by decide)] at hc
      exact hK0 (of_decide_eq_true (bw_ne0 hc))) ?_ (nodecl rfl) (nodecl rfl)
  simp only
  -- a line not of a command's kind
  by_cases hkn : k ≠ .command
  · have hkc := hkn
    rw [if_neg hkc]
    refine tree_ite o (C := .cmp .equal (.cmp .equal (.var "kind") (.const (BitVec.ofNat 64 1)))
        (.const (BitVec.ofNat 64 0))) rfl (fun s h => ⟨_, kind_eval (kd s h.1.1)⟩)
      (leaf_frag o b .syntax fun u ⟨⟨h, _⟩, _⟩ => ⟨h.1.toKept, rfl⟩)
      (frag_unsat (lowK_any _ (k := .skip) (c := _) rfl) fun s ⟨⟨h, _⟩, hc⟩ => by
        rw [kind_eval (kd s h.1)] at hc; exact hkc (by simpa using bw_eq0 hc)) (nodecl rfl) (nodecl rfl)
  have hkc : k = .command := by simpa using hkn
  rw [if_pos hkc]
  refine tree_ite o (C := .cmp .equal (.cmp .equal (.var "kind") (.const (BitVec.ofNat 64 1)))
      (.const (BitVec.ofNat 64 0))) rfl (fun s h => ⟨_, kind_eval (kd s h.1.1)⟩)
    (frag_unsat (lowK_any _ (k := .skip) (c := _) rfl) fun s ⟨⟨h, _⟩, hc⟩ => by
      rw [kind_eval (kd s h.1)] at hc
      exact absurd hkc (by simpa using bw_ne0 hc)) ?_ (nodecl rfl) (nodecl rfl)
  exact known_frag o hs hgn hvc hlc hw1 (fun ho => commandIn_base w0 (ho ▸ hcv)) fun s ⟨⟨h, _⟩, _⟩ => h

/-! ### `classify` from its entry -/

theorem lowKK_picks : ∀ ps : List (Nat × Nat), (∀ p ∈ ps, p.1 < texts.length) → LowKK (picks ps)
  | [], _ => fun k => ⟨k, rfl⟩
  | p :: ps, h => by
    rw [picks, List.flatMap_cons, ← picks]
    exact lowKK_append (lowKK_append (wordIsAt_low "s0" "l0" (h p (by simp))) (lowKK_one rfl rfl
      (a := .cond (.var "eqk") (.assign "cmd" (.const (BitVec.ofNat 64 p.2))) .skip)))
      (lowKK_picks ps fun q hq => h q (by simp [hq]))

theorem pickFold_append (u : List Byte) (xs ys : List (Nat × Nat)) (c : Nat) :
    pickFold u (xs ++ ys) c = pickFold u ys (pickFold u xs c) := by
  simp only [pickFold, List.foldl_append]

theorem picks_decl : ∀ ps : List (Nat × Nat), declared (picks ps) = []
  | [] => rfl
  | p :: ps => by rw [picks, List.flatMap_cons, ← picks, declared_append, picks_decl ps]; rfl

theorem names_ok : (∀ p ∈ baseNames ++ storeNames, p.1 < texts.length ∧ p.2 < 2 ^ 64) := by
  rw [texts_length]; decide

/-- The names tried at a branch's state: `cmd` the code of the last the first word is. -/
theorem picksT_frag (o : Oracle σ) {b : Word} {ci : Nat} {offered : Bool} {k : FrameSpec.Kind} {L : List Byte}
    {s0 : PancakeState σ} (hs : ClsIn b ci offered k L s0) (ps : List (Nat × Nat))
    (hps : ∀ p ∈ ps, p.1 < texts.length ∧ p.2 < 2 ^ 64) (c : Nat) {P : Assn σ}
    (hP : ∀ s, P s → TreeAt L s0 s ∧ s.locals "cmd" = some (BitVec.ofNat 64 c) ∧ 1 ≤ (spans L).length) :
    Frag o (picks ps) P (fun v => TreeAt L s0 v ∧ v.locals "cmd" = some (BitVec.ofNat 64
      (pickFold ((cut L ((spans L).getD 0 (0, 0))).map CommandSpec.upper) ps c))) :=
  frag_each o (lowKK_picks ps fun p hp => (hps p hp).1) fun s hsP => by
    obtain ⟨ht, hc, h1⟩ := hP s hsP
    have hw := wordAt_of (treeAt_line hs ht) (p := (spans L).getD 0 (0, 0))
      (spans_getD_mem (by omega)) ht.s0 ht.l0
    refine frag_conseq (picks_frag o hw (ht.base.trans hs.base)
      (by rw [ht.memory, ht.memaddrs, ht.be]; exact hs.texts) ps c hps) (fun u hu => ⟨⟨fun y _ => by
        rw [hu.locals], hu.memory, hu.memaddrs, hu.be, hu.base, hu.ffi, hu.code⟩, by rw [hu.locals]; exact hc,
        by rw [hu.locals]; exact ht.eqk, by rw [hu.locals]; exact ht.jq⟩) fun v hv => ⟨?_, hv.cmd⟩
    exact treeAt_but ht hv.but (by decide) fun y hy => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
      rcases hy with rfl | rfl | rfl | rfl | rfl | rfl
      · rw [hv.but.locals "r" (by decide)]; exact ht.r
      · exact ⟨_, hv.cmd⟩
      · exact hv.eqk
      · exact hv.jq
      · rw [hv.but.locals "ok" (by decide)]; exact ht.ok
      · rw [hv.but.locals "val" (by decide)]; exact ht.val

/-- The words scanned and the locals declared: a branch's state. -/
theorem treeAt_start {L : List Byte} {s0 s1 u : PancakeState σ} (h1 : WordsAt L (scanNmFrom 0 2) s0 s1)
    (h2 : Zeros s1 ["cmd", "eqk", "jq", "ok", "val"] u) (hr : ∃ v, s0.locals "r" = some v) : TreeAt L s0 u := by
  have fr : ∀ y, y ∉ ["cmd", "eqk", "jq", "ok", "val"] → y ∉ scanNames (scanNmFrom 0 2) →
      u.locals y = s0.locals y := fun y h h' => (h2.frame y h).trans (h1.frame y h')
  have sl0 := h1.slots 0 (by decide)
  have sl1 := h1.slots 1 (by decide)
  have d1 : ∀ y ∈ ["cmd", "eqk", "jq", "ok", "val"], y ∈ clsNames := by decide
  have d2 : ∀ y ∈ scanNames (scanNmFrom 0 2), y ∈ clsNames := by decide
  refine ⟨⟨fun y hy => fr y (fun e => hy (d1 y e)) (fun e => hy (d2 y e)),
    h2.memory.trans h1.memory, h2.memaddrs.trans h1.memaddrs, h2.be.trans h1.be, h2.ffi.trans h1.ffi,
    h2.base.trans h1.base, h2.code.trans h1.code, by rw [fr "r" (by decide) (by decide)]; exact hr⟩,
    by rw [h2.frame "w" (by decide)]; exact h1.hw, by rw [h2.frame "s0" (by decide)]; exact sl0.1,
    by rw [h2.frame "l0" (by decide)]; exact sl0.2, by rw [h2.frame "s1" (by decide)]; exact sl1.1,
    by rw [h2.frame "l1" (by decide)]; exact sl1.2, ⟨0, h2.zero "cmd" (by decide)⟩, ⟨0, h2.zero "eqk" (by decide)⟩,
    ⟨0, h2.zero "jq" (by decide)⟩, ⟨0, h2.zero "ok" (by decide)⟩, ⟨0, h2.zero "val" (by decide)⟩⟩

theorem kindIs_eval {k : FrameSpec.Kind} {s : PancakeState σ}
    (h : s.locals "kind" = some (BitVec.ofNat 64 (FramerProg.kindCode k))) (k' : FrameSpec.Kind) :
    eval s (.cmp .equal (.var "kind") (.const (BitVec.ofNat 64 (FramerProg.kindCode k')))) =
      some (bw (decide (k = k'))) := by
  cases k <;> cases k' <;> simp [eval, h, FramerProg.kindCode, bw]

/-- **`classify` gives the code of `CommandSpec.replyIn`'s reply.** From its entry, if it goes on, `r` holds it; other
locals and all words but `clsWords` stay. `viewClassify` and `listClassify` are as their contracts give them. -/
theorem classify_frag (o : Oracle σ) {b : Word} {ci : Nat} {offered : Bool} {k : FrameSpec.Kind} {L : List Byte}
    {s0 : PancakeState σ} (hs : ClsIn b ci offered k L s0) (hgn : GnCode s0.code)
    (hvc : FnOk o "viewClassify" b IsView s0.code) (hlc : FnOk o "listClassify" b IsList s0.code) :
    Frag o Session.classify (Like s0) (Out b s0 (Session.replyCode (CommandSpec.replyIn offered ⟨k, L⟩))) := by
  rw [classify_eq]
  have f1 := scanWords_frag o 2 nm2_ok (by decide) (by decide) hs.line
  have f2 : Frag o [.dec "cmd" (Syntax.n 0), .dec "eqk" (Syntax.n 0), .dec "jq" (Syntax.n 0),
      .dec "ok" (Syntax.n 0), .dec "val" (Syntax.n 0)] (WordsAt L (scanNmFrom 0 2) s0)
      (fun u => TreeAt L s0 u ∧ u.locals "cmd" = some (BitVec.ofNat 64 0)) :=
    frag_each o (lowKK_decs ["cmd", "eqk", "jq", "ok", "val"]) fun s1 h1 =>
      frag_conseq (decs_frag o s1 ["cmd", "eqk", "jq", "ok", "val"] []) (fun u (hu : Like s1 u) =>
        ⟨fun _ h => by simp at h, fun y _ => by rw [hu.locals], hu.memory, hu.memaddrs, hu.be, hu.ffi, hu.base,
          hu.code⟩) fun u hu => ⟨treeAt_start h1 (by simpa using hu) hs.r, hu.zero "cmd" (by simp)⟩
  refine frag_append f1 (frag_append (xs := [_, _, _, _, _]) f2 ?_)
  have hsp := spans_length L
  have hsh := hs.line.short
  have wEq : ∀ s, TreeAt L s0 s → eval s (.cmp .equal (.var "w") (.const (BitVec.ofNat 64 0))) =
      some (bw (decide ((spans L).length = 0))) := fun s h =>
    eval_eq (by omega) (by decide) (by simp only [eval]; exact h.w) rfl
  have kd : ∀ s, TreeAt L s0 s → s.locals "kind" = some (BitVec.ofNat 64 (FramerProg.kindCode k)) := fun s h => by
    rw [h.loc "kind" (by decide)]; exact hs.kind
  refine tree_ite o (C := .cmp .equal (.var "w") (.const (BitVec.ofNat 64 0))) rfl (fun s h => ⟨_, wEq s h.1⟩) ?_ ?_
    (nodecl rfl) (nodecl rfl)
  · -- no words
    have hR : ∀ s, TreeAt L s0 s → eval s (.cmp .equal (.var "w") (.const (BitVec.ofNat 64 0))) ≠ some 0 →
        CommandSpec.replyIn offered ⟨k, L⟩ = if k = .overlong then .unknown else .ignore := fun s h hc => by
      rw [wEq s h] at hc
      have e := of_decide_eq_true (bw_ne0 hc)
      rw [List.length_eq_zero_iff] at e
      simp [CommandSpec.replyIn, words_spans, e]
    refine tree_ite o (C := .cmp .equal (.var "kind") (.const (BitVec.ofNat 64 (FramerProg.kindCode .overlong)))) rfl
      (fun s h => ⟨_, kindIs_eval (kd s h.1.1) .overlong⟩)
      (leaf_frag o b .unknown fun u ⟨⟨⟨h, _⟩, hc⟩, hk⟩ => ⟨h.toKept, ?_⟩)
      (leaf_frag o b .ignore fun u ⟨⟨⟨h, _⟩, hc⟩, hk⟩ => ⟨h.toKept, ?_⟩) (nodecl rfl) (nodecl rfl)
    · rw [kindIs_eval (kd u h) .overlong] at hk
      rw [hR u h hc, if_pos (of_decide_eq_true (bw_ne0 hk))]
    · rw [kindIs_eval (kd u h) .overlong] at hk
      rw [hR u h hc, if_neg (of_decide_eq_false (bw_eq0 hk))]
  -- a command's name tried, the store's ones when there is a store
  have hlow : LowKK (picks baseNames ++ [SessionStore.ifs Session.hasStore (picks storeNames)] ++ cmdTree) :=
    lowKK_append (lowKK_append (lowKK_picks _ fun p hp => (names_ok p (by simp [hp])).1)
      (lowKK_ite store_lower (lowKK_picks _ fun p hp => (names_ok p (by simp [hp])).1) fun k => ⟨k, rfl⟩))
      (lowK_any _ (k := .skip) (c := _) rfl)
  refine frag_pure (1 ≤ (spans L).length) (fun s ⟨⟨h, _⟩, hc⟩ => by
    rw [wEq s h] at hc; have := of_decide_eq_false (bw_eq0 hc); omega) hlow fun hw1 => ?_
  let w0 := cut L ((spans L).getD 0 (0, 0))
  let U := w0.map CommandSpec.upper
  have sp := pick_spec offered w0
  have fb := picksT_frag o hs baseNames (fun p hp => names_ok p (by simp [hp])) 0
    (P := fun s => (TreeAt L s0 s ∧ s.locals "cmd" = some (BitVec.ofNat 64 0)) ∧
      eval s (.cmp .equal (.var "w") (.const (BitVec.ofNat 64 0))) = some 0) fun s ⟨⟨h, hc0⟩, _⟩ => ⟨h, hc0, hw1⟩
  let Q : Assn σ := fun v => TreeAt L s0 v ∧
    v.locals "cmd" = some (BitVec.ofNat 64 (cmdCode (CommandSpec.commandIn offered w0)))
  have fs : Frag o [SessionStore.ifs Session.hasStore (picks storeNames)]
      (fun v => TreeAt L s0 v ∧ v.locals "cmd" = some (BitVec.ofNat 64 (pickFold U baseNames 0))) Q := by
    have hQ : Safe.ClockFree Q := fun _ _ ⟨h, rest⟩ => ⟨treeAt_clock L s0 _ _ h, rest⟩
    refine frag_ite o (C := .loadWord (.op .add .base (.const (BitVec.ofNat 64 (ownOff + ownStore))))) store_lower hQ
      (fun s h => ⟨_, store_eval hs h.1.toKept⟩) ?_ (fun _ _ _ _ h => by rw [picks_decl] at h; simp at h)
      (frag_nil o fun s ⟨⟨h, hc⟩, hn⟩ => ⟨h, ?_⟩) (fun _ _ _ _ h => by simp [declared] at h)
    · refine frag_pure (offered = true)
        (fun s ⟨h, hn⟩ => bw_ne0 (by rwa [store_eval hs h.1.toKept] at hn))
        (lowKK_picks _ fun p hp => (names_ok p (by simp [hp])).1) fun ho => ?_
      refine frag_conseq (picksT_frag o hs storeNames (fun p hp => names_ok p (by simp [hp])) _
        (P := fun s => (TreeAt L s0 s ∧ s.locals "cmd" = some (BitVec.ofNat 64 (pickFold U baseNames 0))) ∧ _)
        fun s ⟨⟨h, hc⟩, _⟩ => ⟨h, hc, hw1⟩) (fun _ h => h) fun v ⟨h, hc⟩ => ⟨h, ?_⟩
      rw [hc, ← sp, ho, if_pos rfl, pickFold_append]
    · have ho := bw_eq0 (by rwa [store_eval hs h.toKept] at hn)
      rw [hc, ← sp, ho]; simp only [Bool.false_eq_true, if_false, List.append_nil]; rfl
  refine frag_append (frag_append fb fs) ?_
  exact cmd_frag o hs hgn hvc hlc hw1

/-! ### The premises can hold -/

theorem kept_witness : Kept zeroState zeroState := ⟨fun _ _ => rfl, rfl, rfl, rfl, rfl, rfl, rfl, ⟨0, rfl⟩⟩

theorem treeAt_witness : TreeAt [] zeroState zeroState :=
  ⟨kept_witness, rfl, rfl, rfl, rfl, rfl, ⟨0, rfl⟩, ⟨0, rfl⟩, ⟨0, rfl⟩, ⟨0, rfl⟩, ⟨0, rfl⟩⟩

theorem after_witness : After 0 zeroState zeroState := ⟨fun _ _ => rfl, fun _ _ => rfl, rfl, rfl, rfl, rfl, ⟨0, rfl⟩⟩

theorem out_witness : Out 0 zeroState 0 zeroState := ⟨fun _ _ => rfl, fun _ _ => rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem pickAt_witness : PickAt zeroState 0 zeroState := ⟨SessionCheck.but_refl _ _, rfl, ⟨0, rfl⟩, ⟨0, rfl⟩⟩

theorem isView_witness : IsView .over := Or.inl rfl

theorem isList_witness : IsList .mode := Or.inr (Or.inr (Or.inr (Or.inr rfl)))

end DN.Server.SessionClassify
