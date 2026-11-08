-- SPDX-License-Identifier: AGPL-3.0-or-later
import DN.News.ArticleFields

/-!
# DN.News.ArticleCheck

`artCheck` answers as `ArticleSpec.checkWith` does (`artCheck_ok`). The checks after the fields' loop go one at a
time, in `ArticleSpec.articleRefusal`'s order. An accepted article gets `artAdded`'s header section.
-/

namespace DN.News.ArticleCheck

open DN.News.ArticleSpec (Bytes Field Refusal Verdict)
open DN.News.ArticleLines (seg Lines cont groups fieldOf)
open DN.Compiler DN.Compiler.Wp DN.Compiler.WpRet DN.Compiler.Frag DN.News.AbnfProg
open DN.News.AbnfSets DN.News.FunRun DN.News.AbnfLeaves DN.News.ArticleRun
open DN.News.ScanRun (at_ vals_lookup Fresh fresh_cons lookup_cons_ne lookup_head)
open DN.News.ArticleProg (artMax guardL guardS ifs wd)
open DN.News.FramerCode (bw ev_var)
open DN.News.ArticleTables (esP allNames esP_size)
open DN.News.ArticleAdded (optW esP_length)
open DN.News.ArticleFields (ChkScr HiScr ChkM ChkBase classG firstK placeOf nameCall_frag)
open DN.News.ArticleListRun (elemScratch gScratch gWrites)
open DN.News.AbnfGen (AllSets)

variable {σ : Type}

/-! ## The checks after the fields, one at a time -/

/-- The groups an article names. -/
def groupsOf (fs : List Field) : List Bytes :=
  ((ArticleSpec.find? fs "Newsgroups").map (ArticleSpec.listed ·.value)).getD []

def arGroups (ctx : ArticleSpec.Context) (fs : List Field) : Option Refusal :=
  if (groupsOf fs).length > ArticleSpec.spec.groupsMax then some .tooManyGroups
  else if ArticleSpec.spec.reserved && (groupsOf fs).any ArticleSpec.reserved then some .reservedGroup
  else if ArticleSpec.spec.known && !(groupsOf fs).any (ctx.groups.contains ·) then some .noKnownGroup
  else none

/-- The window check of the date field `n`. -/
def window (ctx : ArticleSpec.Context) (fs : List Field) (n : String) : Option Refusal :=
  match (ArticleSpec.find? fs n).bind (ArticleSpec.dateValue ·.value) with
  | some t =>
    if t - (ctx.wall : Int) > (ArticleSpec.spec.ahead : Int) then some (.dateAhead (DN.News.CommandSpec.ascii n))
    else if (ctx.wall : Int) - t > (ArticleSpec.spec.past : Int) then
      some (.datePast (DN.News.CommandSpec.ascii n))
    else none
  | none => none

def arWindows (ctx : ArticleSpec.Context) (fs : List Field) : Option Refusal :=
  if let some x := window ctx fs "Date" then some x
  else if let some x := window ctx fs "Injection-Date" then some x
  else arGroups ctx fs

def arBad (ctx : ArticleSpec.Context) (fs : List Field) : Option Refusal :=
  if let some f := fs.find? (fun f => ArticleSpec.spec.dates &&
      (ArticleSpec.dateText f).any (fun t => (ArticleSpec.dateValue t).isNone))
    then some (.badDate f.name)
  else arWindows ctx fs

def arDist (ctx : ArticleSpec.Context) (fs : List Field) : Option Refusal :=
  if ArticleSpec.spec.distributionAll &&
      ((ArticleSpec.find? fs "Distribution").map
        (fun f => (ArticleSpec.listed f.value).any (ArticleSpec.named · "all"))).getD false
    then some .distributionAll
  else arBad ctx fs

def arSender (ctx : ArticleSpec.Context) (fs : List Field) : Option Refusal :=
  if ArticleSpec.spec.sender && !ArticleSpec.has fs "Sender" &&
      ((ArticleSpec.find? fs "From").map
        (fun f => !ArticleSpec.grammarSays (ArticleSpec.ruleNamed "mailbox") f.value)).getD false
    then some .noSender
  else arDist ctx fs

def arLong (ctx : ArticleSpec.Context) (fs : List Field) : Option Refusal :=
  if let some f := fs.find? (fun f => ArticleSpec.isOne ArticleSpec.idFields f &&
      (ArticleSpec.msgIds f.value).any (·.length > ArticleSpec.spec.idMax))
    then some (.longMessageId f.name)
  else arSender ctx fs

def arPosted (ctx : ArticleSpec.Context) (fs : List Field) : Option Refusal :=
  if ArticleSpec.spec.posted && ((ArticleSpec.find? fs "Path").map (·.value)).any
      (fun v => (ArticleSpec.pathElements v).any ArticleSpec.isPosted)
    then some .posted
  else arLong ctx fs

def arMissing (ctx : ArticleSpec.Context) (fs : List Field) : Option Refusal :=
  if let some n := ArticleSpec.spec.required.find? (!ArticleSpec.has fs ·)
    then some (.missing (DN.News.CommandSpec.ascii n))
  else arPosted ctx fs

theorem articleRefusal_eq (ctx : ArticleSpec.Context) (fs : List Field) :
    ArticleSpec.articleRefusal ArticleSpec.spec ctx fs =
      if let some n := ArticleSpec.repeatedFrom ArticleSpec.spec fs [] then some (.repeated n)
      else arMissing ctx fs := rfl

/-! ## What `artCheck` gives back -/

/-- The name a refusal carries, or none. -/
def nameOf : Refusal → Bytes
  | .injected n | .traced n | .deprecated n | .notOffered n | .blankLine n | .badField n | .repeated n
  | .missing n | .longMessageId n | .badDate n | .dateAhead n | .datePast n => n
  | _ => []

/-- A name in the name's area, with its length. -/
def NameAt (A : Word) (dm : Word → Bool) (be : Bool) (B : Bytes) (m : Word → Word) : Prop :=
  m (at_ A ArticleProg.xNameLen) = BitVec.ofNat 64 B.length ∧
    DN.News.ArticleListRun.BytesAt A dm be ArticleProg.xName ArticleProg.nameCap B m

/-- The words `artCheck` may write. They are the loop's, `artGroups`' and `artAdded`'s, the name's area, and those
its prologue clears or stores. -/
def CheckScr (A : Word) (x : Word) : Prop :=
  ChkScr A x ∨ gScratch A x ∨ DN.News.ArticleAdded.AddScr A x ∨
    (∃ y, ArticleProg.xName ≤ y ∧ y < ArticleProg.xName + ArticleProg.nameCap ∧ x = at_ A y) ∨
    ∃ i, (i = 11 ∨ i = 12 ∨ i = 13 ∨ i = 14 ∨ i = 16) ∧ x = at_ A (ArticleProg.w i)

/-- **What `artCheck` gives back**: the verdict's number, the failed flag clear, other words kept, every set in place.
A refusal's name is in the name's area; an accepted article's header section, message identifier and known groups. -/
def CheckRet (A : Word) (dm : Word → Bool) (be : Bool) (ctx : ArticleSpec.Context) (a : Bytes) (m0 : Word → Word) :
    Ret := fun v m =>
  m (at_ A aBroken) = 0 ∧ (∀ x, ¬CheckScr A x → m x = m0 x) ∧ AllSets A m ∧
    match ArticleSpec.checkWith ArticleSpec.spec ctx a with
    | .refused x => v = BitVec.ofNat 64 (DN.News.ArticleFields.refNum x) ∧ NameAt A dm be (nameOf x) m ∧
      (nameOf x).length ≤ ArticleProg.nameCap
    | .accepted acc => v = 0 ∧
      DN.News.ArticleListRun.BytesAt A dm be ArticleProg.xOut ArticleProg.outMax acc.header m ∧
      acc.header.length ≤ ArticleProg.outMax ∧ m (at_ A ArticleProg.xOutLen) = BitVec.ofNat 64 acc.header.length ∧
      DN.News.ArticleListRun.BytesAt A dm be ArticleProg.xMsg ArticleProg.msgCap acc.messageId m ∧
      acc.messageId.length < ArticleProg.msgCap ∧ m (at_ A ArticleProg.xMsgLen) = BitVec.ofNat 64 acc.messageId.length ∧
      DN.News.ArticleListRun.KnownAt A ctx.groups acc.groups m ∧ acc.groups.length ≤ ArticleProg.knownMax

/-- The verdict's number names the host's reason. -/
theorem refNum_reason (x : Refusal) :
    (ArticleProg.refusals[DN.News.ArticleFields.refNum x - 1]?).map (fun r => (ArticleModel.reason r).1) =
      some (ArticleModel.reason x).1 := by
  cases x <;> rfl

theorem refNum_range (x : Refusal) :
    1 ≤ DN.News.ArticleFields.refNum x ∧ DN.News.ArticleFields.refNum x ≤ ArticleProg.refusals.length := by
  cases x <;> exact ⟨Nat.le_of_ble_eq_true rfl, Nat.le_of_ble_eq_true rfl⟩

/-! ## The memory after the fields -/

/-- One fixed memory at a time, each the premise allows. -/
theorem runF_pin (o : Oracle σ) {R : Ret} {xs : List Syntax.PStmt} (hlow : LowKK xs) {s1 : PancakeState σ}
    {L : List (String × Value)} {F : (Word → Word) → Prop} {Q : Assn σ}
    (h : ∀ M, F M → FragR o R xs (RunF s1 L (· = M)) Q) : FragR o R xs (RunF s1 L F) Q := by
  refine fragR_conseq (P0 := fun u => ∃ M, RunF s1 L (· = M) u ∧ F M) ?_ (fun u h => ⟨u.memory, ⟨h.1, rfl⟩, h.2⟩)
    fun _ h => h
  refine fragR_exists hlow fun M => ?_
  exact fragR_pure (F M) (fun u h => h.2) hlow fun hM => fragR_conseq (h M hM) (fun u h => h.1) fun _ h => h

/-- An `artGroups` word lies past the slots and before the first fields' table. -/
theorem g_at {A : Word} {x : Word} (h : gScratch A x) :
    ∃ y, ArticleProg.X ≤ y ∧ y < ArticleProg.xFirst ∧ x = at_ A y := by
  have hX := X_val; have hF := xFirst_eq; have hE := DN.News.ArticleListRun.xElem_eq
  have hG := DN.News.ArticleListRun.xGroups_eq
  have hs := DN.News.ArticleFields.w_eq
  rcases h with (⟨k, hk, rfl⟩ | rfl | rfl) | ⟨y, hy, rfl⟩
  · exact ⟨_, by omega, by omega, rfl⟩
  · exact ⟨_, by simp only [ArticleProg.xElemLen, hs]; omega, by simp only [ArticleProg.xElemLen, hs]; omega, rfl⟩
  · exact ⟨_, by simp only [ArticleProg.xElemRes, hs]; omega, by simp only [ArticleProg.xElemRes, hs]; omega, rfl⟩
  · refine ⟨y, ?_, by have := DN.News.ArticleListRun.gWrites_lt hy; omega, rfl⟩
    rcases hy with rfl | rfl | rfl | rfl | ⟨h1, -⟩
    · simp only [ArticleProg.xKnownN, hs]; omega
    · simp only [ArticleProg.xGCount, hs]; omega
    · simp only [ArticleProg.xGRes, hs]; omega
    · simp only [ArticleProg.xGKnown, hs]; omega
    · have : ArticleProg.xKnown = ArticleProg.w 32 := rfl
      rw [this, hs] at h1; omega

/-- **The memory in the checks after the fields**: as after the loop, but `artGroups`' words may change too. -/
structure ChkT (s1 : PancakeState σ) (A : Word) (m0 : Word → Word) (a : Bytes) (gs : List (List (Nat × Nat)))
    (M : Word → Word) : Prop where
  reads : Reads s1 A a M
  sets : AllSets A M
  frame : ∀ x, ¬ChkScr A x → ¬gScratch A x → M x = m0 x
  first : ∀ k, k ≤ esP.length → M (at_ A (ArticleProg.xFirst + 8 * k)) = optW (firstK a gs k)

theorem chkT_of {s1 : PancakeState σ} {A : Word} {m0 : Word → Word} {a : Bytes} {gs : List (List (Nat × Nat))}
    {M : Word → Word} (h : ChkM s1 A m0 a gs M) : ChkT s1 A m0 a gs M :=
  ⟨h.reads, h.sets, fun x hx _ => h.frame x hx, h.first⟩

/-- What the leaves read, kept where the words below `X` are. -/
theorem reads_lo {s1 : PancakeState σ} {A : Word} (hA8 : A.toNat % 8 = 0) {a : Bytes} (hlen : a.length ≤ artMax)
    {m : Word → Word} (hR : Reads s1 A a m) {M : Word → Word}
    (hk : ∀ y, y < ArticleProg.X → M (at_ A y) = m (at_ A y)) : Reads s1 A a M :=
  DN.News.ArticleFields.reads_keep' hA8 hlen hR fun x hx => hk x (by have := sets_le_X; omega)

/-- Every set kept where the words below `X` are. -/
theorem sets_lo {A : Word} {m M : Word → Word} (hall : AllSets A m)
    (hk : ∀ y, y < ArticleProg.X → M (at_ A y) = m (at_ A y)) : AllSets A M := fun k hk' => by
  obtain ⟨S, hS⟩ := hall k hk'
  refine ⟨S, setAt_frame hS fun i hi => hk _ ?_⟩
  have h3 := DN.News.AbnfSets.off_lt hk' (8 * i) (by rw [DN.News.AbnfSets.setSize_eq] at hi ⊢; omega)
  have hX' := X_eq
  omega

/-- **Words past the slots and before the table written**, the memory after the fields kept. -/
theorem chkT_mid {s1 : PancakeState σ} {A : Word} (hA8 : A.toNat % 8 = 0) {m0 : Word → Word} {a : Bytes}
    (hlen : a.length ≤ artMax) {gs : List (List (Nat × Nat))} {M M' : Word → Word} (h : ChkT s1 A m0 a gs M)
    {S : Word → Prop} (hS : ∀ x, S x → ∃ y, ArticleProg.X ≤ y ∧ y < ArticleProg.xFirst ∧ x = at_ A y)
    (hSc : ∀ x, S x → HiScr A x ∨ gScratch A x) (hk : ∀ x, ¬S x → M' x = M x) : ChkT s1 A m0 a gs M' := by
  have hX := X_val; have hF := xFirst_eq
  have nlo : ∀ y, y < ArticleProg.X → M' (at_ A y) = M (at_ A y) := fun y hy => hk _ fun hh => by
    obtain ⟨z, h1, h2, e⟩ := hS _ hh
    have := DN.News.ScanRun.at_inj (by omega) (by omega) e; omega
  refine ⟨reads_lo hA8 hlen h.reads nlo, sets_lo h.sets nlo, fun x h1 h2 => ?_, fun k hk' => ?_⟩
  · rw [hk x fun hh => by rcases hSc x hh with h3 | h3 <;> first | exact h1 (.inl h3) | exact h2 h3]
    exact h.frame x h1 h2
  · rw [esP_length] at hk'
    rw [hk _ fun hh => by
      obtain ⟨z, h1, h2, e⟩ := hS _ hh
      have := DN.News.ScanRun.at_inj (by omega) (by omega) e; omega]
    exact h.first k (by rw [esP_length]; exact hk')

/-- **The grammar called** in the checks after the fields. -/
theorem chkT_gram {s1 : PancakeState σ} {A : Word} {m0 : Word → Word} {a : Bytes} {gs : List (List (Nat × Nat))}
    {M M' : Word → Word} (h : ChkT s1 A m0 a gs M) (hR : Reads s1 A a M') (hall : AllSets A M')
    (hfr : ∀ x, (∀ k, k < slots → ¬InSlot A k x) → x ≠ at_ A aLen → M' x = M x) : ChkT s1 A m0 a gs M' :=
  ⟨hR, hall, fun x hx hg => (hfr x (fun k hk hin => hx (.inr (.inr (.inl ⟨k, hk, hin⟩)))) fun e =>
    hx (.inr (.inl e))).trans (h.frame x hx hg), DN.News.ArticleFields.first_gram h.first hfr⟩

theorem not_g {A : Word} {y : Nat} (hy : y < ArticleProg.X ∨ ArticleProg.xFirst ≤ y) (hy2 : y < 2 ^ 40) :
    ¬gScratch A (at_ A y) := fun h => by
  have hX := X_val; have hF := xFirst_eq
  obtain ⟨z, h1, h2, e⟩ := g_at h
  have := DN.News.ScanRun.at_inj (by omega) (by omega) e; omega

theorem not_g_w {A : Word} {i : Nat} (hi : i < 32) (h14 : i ≠ 14) (h21 : i ≠ 21) (h22 : i ≠ 22) (h26 : i ≠ 26)
    (h27 : i ≠ 27) (h28 : i ≠ 28) : ¬gScratch A (at_ A (ArticleProg.w i)) := fun h => by
  have hE := DN.News.ArticleListRun.xElem_eq; have hG := DN.News.ArticleListRun.xGroups_eq
  have hs := DN.News.ArticleFields.w_eq
  have hw : ∀ y, y < 2 ^ 40 → at_ A (ArticleProg.w i) = at_ A y → 497936 + 8 * i = y := fun y hy e => by
    rw [← hs]; exact DN.News.ScanRun.at_inj (by rw [hs]; omega) (by omega) e
  rcases h with (⟨k, hk, e⟩ | e | e) | ⟨y, hy, e⟩
  · have := hw _ (by omega) e; omega
  · have := hw _ (by simp only [ArticleProg.xElemLen, hs]; omega) e; simp only [ArticleProg.xElemLen, hs] at this; omega
  · have := hw _ (by simp only [ArticleProg.xElemRes, hs]; omega) e; simp only [ArticleProg.xElemRes, hs] at this; omega
  · have hlt := DN.News.ArticleListRun.gWrites_lt hy
    have := hw _ (by omega) e
    rcases hy with rfl | rfl | rfl | rfl | ⟨h1, -⟩
    · simp only [ArticleProg.xKnownN, hs] at this; omega
    · simp only [ArticleProg.xGCount, hs] at this; omega
    · simp only [ArticleProg.xGRes, hs] at this; omega
    · simp only [ArticleProg.xGKnown, hs] at this; omega
    · have : ArticleProg.xKnown = ArticleProg.w 32 := rfl
      rw [this, hs] at h1; omega

theorem chkT_broken {s1 : PancakeState σ} {A : Word} {m0 : Word → Word} {a : Bytes} {gs : List (List (Nat × Nat))}
    {M : Word → Word} (h : ChkT s1 A m0 a gs M) (hb : m0 (at_ A aBroken) = 0) : M (at_ A aBroken) = 0 :=
  (h.frame _ (DN.News.ArticleFields.not_chk (.inl DN.News.ArticleGrammar.broken_low) (by decide) (by decide))
    (not_g (.inl (by have := DN.News.ArticleGrammar.broken_low; have := sets_le_X; omega)) (by decide))).trans hb

theorem chkT_sep {s1 : PancakeState σ} {A : Word} {m0 : Word → Word} {a : Bytes} {gs : List (List (Nat × Nat))}
    {M : Word → Word} (h : ChkT s1 A m0 a gs M) {SEP : Nat} {es : List String} (hB : ChkBase s1 A m0 SEP es) :
    M (at_ A ArticleProg.xSep) = BitVec.ofNat 64 SEP :=
  (h.frame _ (DN.News.ArticleFields.not_chk_w (i := 16) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)) (not_g_w (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide))).trans hB.sep

/-- **A refusal with a field's name**, if the local `x` holds a field's place: the name kept, `N` given back. -/
theorem name_ret (o : Oracle σ) {R : Ret} {A : Word} {s1 : PancakeState σ} (hA : Area ArticleProg.ofs A s1)
    (hD : ArtDom A s1.memaddrs) (hcode : ArtCode s1.code) {m0 : Word → Word} {a : Bytes} (hlen : a.length ≤ artMax)
    {SEP : Nat} (hB : ChkBase s1 A m0 SEP esP) {gs : List (List (Nat × Nat))} {L : List (String × Value)}
    (hla : L.lookup "a" = some A) {x c : String} (hc : c ≠ "a") (hcf : Fresh c L = true) {op : Option Nat}
    (hx : L.lookup x = some (optW op)) (hop63 : ∀ p, op = some p → p < 2 ^ 63) {N : Nat}
    (hlow : LowKK (guardS (.call c "artNameAt" [Syntax.v x]) ++ [.ret (Syntax.n N)]))
    (hop : ∀ p, op = some p → ∃ e more, DN.News.ArticleLines.FieldAt a SEP p e more ∧
      DN.News.ArticleLines.nameLen a p e < ArticleProg.nameCap ∧ ∀ M, ChkT s1 A m0 a gs M →
      R (BitVec.ofNat 64 N) (nameMem A s1.be (seg a p (p + DN.News.ArticleLines.nameLen a p e))
        (DN.News.ArticleLines.nameLen a p e) e M)) :
    FragR o R (guardS (ifs (Syntax.eLe (Syntax.n 0) (Syntax.v x)) [.call c "artNameAt" [Syntax.v x], .ret
      (Syntax.n N)]))
      (RunF s1 L (ChkT s1 A m0 a gs)) (fun u => RunF s1 L (ChkT s1 A m0 a gs) u ∧ op = none) := by
  refine fragR_if o rfl hlow (lowK_any _ (k := .skip) rfl) (fun u k h => ⟨runF_clock _ _ _ u k h.1, h.2⟩)
    (fun u y w h hy => by
      have : y = c := by simpa [declared, guardS, guardL, ifs] using hy
      subst this; exact ⟨runF_restore h.1 hcf w, h.2⟩)
    (fun _ _ _ _ hy => nomatch hy) (b := op.isSome)
    (fun u h => DN.News.ArticleAdded.flag_eval hop63 (ev_var (vals_lookup h.1.vals hx))) (fun hs => ?_) fun hs => ?_
  · obtain ⟨p, hp⟩ := Option.isSome_iff_exists.1 hs
    obtain ⟨e, more, hf, hK, hRp⟩ := hop p hp
    refine runF_pin o hlow fun M hM => fragR_append (nameCall_frag o hA hD hcode hlen (rt := c) hc (l := L) hla hcf
      (e1 := Syntax.v x) rfl hf hK (fun u h => by rw [ev_var (vals_lookup h.1.vals hx), hp]; rfl) hM.reads.input
      (chkT_broken hM hB.broken) (chkT_sep hM hB)) (fragR_ret o rfl fun u h => ⟨_, rfl, by rw [h.2]; exact hRp M hM⟩)
  · exact fragR_of (frag_nil o fun u h => ⟨h, by cases op <;> simp_all⟩)

/-! ## A field the rules require -/

/-- **The table read by name** in the checks after the fields. -/
theorem chkT_firstW {s1 : PancakeState σ} {A : Word} {m0 : Word → Word} {a : Bytes} {L : List (Nat × Nat)}
    {M : Word → Word} (h : ChkT s1 A m0 a (groups a L) M) {nm : String} (hn : nm ∈ allNames) :
    DN.News.ArticleAdded.FirstW A M a L nm := DN.News.ArticleFields.firstW_of h.first hn

/-- The table's word of a named field, as `artCheck` reads it. -/
theorem firstE_eval {s1 : PancakeState σ} {A : Word} {m0 : Word → Word} {a : Bytes} {L : List (Nat × Nat)}
    {SEP : Nat} (hB : ChkBase s1 A m0 SEP esP) {l : List (String × Value)} (hla : l.lookup "a" = some A)
    {u : PancakeState σ} (h : RunF s1 l (ChkT s1 A m0 a (groups a L)) u) {nm : String} (hn : nm ∈ allNames) :
    eval u (DN.News.ArticleAdded.firstE esP nm) = some (optW (DN.News.ArticleAdded.firstP a L nm)) := by
  rw [DN.News.ArticleAdded.firstE, loadA_eval h.1.memaddrs (DN.News.ArticleAdded.first_dom hB.tdom
    (DN.News.ArticleAdded.entry_le esP nm)) (atA_eval (vals_lookup h.1.vals hla))]
  exact congrArg some (chkT_firstW h.2 hn)

theorem name_dom {A : Word} {dm : Word → Bool} (hD : ArtDom A dm) (hA8 : A.toNat % 8 = 0) :
    ∀ y, ArticleProg.xName ≤ y → y < ArticleProg.xName + ArticleProg.nameCap →
      dm (byteAlign (at_ A y)) = true := fun y h1 h2 => by
  rw [DN.News.ScanRun.align_at hA8]
  have hn := xName_eq; have hF := xFirst_eq; have hs := sets_le_X; have hX := X_val
  have hc : ArticleProg.nameCap = 1024 := rfl
  exact hD _ (by omega) (by omega) (by omega)

theorem storesB_declared (B : Nat) : ∀ (cs : List Nat) (i0 : Nat),
    declared (DN.News.ArticleTables.storesB B cs i0) = []
  | [], _ => rfl
  | c :: cs, i0 => by
    show declared ([_] ++ DN.News.ArticleTables.storesB B cs (i0 + 1)) = []
    rw [declared_append, storesB_declared B cs (i0 + 1)]; rfl

/-- A constant name written, its length, `N` given back. -/
def cRet (nm : String) (N : Nat) : List Syntax.PStmt :=
  DN.News.ArticleTables.storesB ArticleProg.xName (ArticleProg.codes nm) 0 ++
    ([ArticleProg.setW ArticleProg.xNameLen (Syntax.n nm.length)] ++ [.ret (Syntax.n N)])

theorem cRet_declared (nm : String) (N : Nat) : declared (cRet nm N) = [] := by
  unfold cRet; rw [declared_append, declared_append, storesB_declared]; rfl

theorem constName_g (nm : String) (N : Nat) : guardL (ArticleProg.constName nm ++ [.ret (Syntax.n N)]) =
    cRet nm N := by
  rw [show ArticleProg.constName nm = DN.News.ArticleTables.storesB ArticleProg.xName (ArticleProg.codes nm) 0 ++
    [ArticleProg.setW ArticleProg.xNameLen (Syntax.n nm.length)] from rfl, DN.News.ArticleGrammar.guardL_append,
    DN.News.ArticleGrammar.guardL_append, DN.News.ArticleTables.guardL_storesB, List.append_assoc]
  rfl

/-- What a constant name written leaves: its bytes, its length, every other word as before. -/
def ConstAt (A : Word) (dm : Word → Bool) (be : Bool) (nm : String) (M m : Word → Word) : Prop :=
  (∀ j (hj : j < (ArticleProg.codes nm).length), memLoadByte m dm be (at_ A (ArticleProg.xName + j)) =
    some (BitVec.ofNat 8 (ArticleProg.codes nm)[j])) ∧
  m (at_ A ArticleProg.xNameLen) = BitVec.ofNat 64 nm.length ∧
  ∀ x, (∀ y, ArticleProg.xName ≤ y → y < ArticleProg.xName + ArticleProg.nameCap → x ≠ at_ A y) →
    x ≠ at_ A ArticleProg.xNameLen → m x = M x

theorem xNameLen_ne0 : (ArticleProg.xNameLen == 0) = false := by
  simp only [ArticleProg.xNameLen, ArticleProg.w, X_val]; rfl

theorem const_low (nm : String) (N : Nat) : LowKK (cRet nm N) :=
  lowKK_append (DN.News.ArticleTables.storesB_low (by rw [xName_eq]; decide) _ 0)
    (lowKK_append (DN.News.ArticleTables.setW_low xNameLen_ne0 _) (lowKK_ret rfl))

/-- **A constant name written and `N` given back.** -/
theorem const_ret (o : Oracle σ) {R : Ret} {A : Word} {s1 : PancakeState σ} (hA : Area ArticleProg.ofs A s1)
    (hD : ArtDom A s1.memaddrs) {l : List (String × Value)} (hla : l.lookup "a" = some A) {nm : String}
    (hnl : nm.length < ArticleProg.nameCap) {N : Nat} {M : Word → Word} {Q : Assn σ}
    (hR : ∀ m, ConstAt A s1.memaddrs s1.be nm M m → R (BitVec.ofNat 64 N) m) :
    FragR o R (cRet nm N) (RunF s1 l (· = M)) Q := by
  have hA8 := hA.hA
  have hn' := xName_eq; have hc : ArticleProg.nameCap = 1024 := rfl
  have hcl := DN.News.ArticleOut.codes_length nm
  have hlow2 : LowKK ([ArticleProg.setW ArticleProg.xNameLen (Syntax.n nm.length)] ++ [.ret (Syntax.n N)]) :=
    lowKK_append (DN.News.ArticleTables.setW_low xNameLen_ne0 _) (lowKK_ret rfl)
  refine fragR_append (xs := DN.News.ArticleTables.storesB ArticleProg.xName (ArticleProg.codes nm) 0)
    (fragR_of (DN.News.ArticleTables.bytes_frag o hla hA8 (NB := ArticleProg.xName)
    (B := ArticleProg.xName) (LIM := ArticleProg.xName + ArticleProg.nameCap) (by omega) (Nat.le_refl _) (by omega)
    (by omega) (name_dom hD hA8) (ArticleProg.codes nm) 0 M (by omega))) ?_
  refine fragR_exists hlow2 fun m => ?_
  refine fragR_pure _ (fun u h => h.2) hlow2 fun ⟨hby, _, _, hfr⟩ => ?_
  refine fragR_conseq (P0 := RunF s1 l (· = m)) ?_ (fun u h => h.1) fun _ h => h
  have hwl : ArticleProg.xNameLen < ArticleProg.xName := by
    simp only [ArticleProg.xNameLen, ArticleProg.w, X_val]; omega
  refine fragR_append (fragR_of (DN.News.ArticleTables.setC_frag o hla xNameLen_ne0
    (artDom_w hD (i := 11) (by decide))))
    (fragR_ret o rfl fun u h => ⟨_, rfl, ?_⟩)
  rw [h.2]
  refine hR _ ⟨fun j hj => ?_, upd_eq _ _ _, fun x h1 h2 => ?_⟩
  · have := hby j hj
    rw [Nat.add_zero] at this
    unfold memLoadByte at this ⊢
    rw [upd_ne _ (by
      rw [DN.News.ScanRun.align_at hA8]
      exact DN.News.ScanRun.at_ne (by omega) (by omega) (by omega))]
    exact this
  · rw [upd_ne _ h2]; exact hfr x h1

/-- **A missing field the rules require**: its name written, 13 given back. -/
theorem missing_step (o : Oracle σ) {R : Ret} {A : Word} {s1 : PancakeState σ} (hA : Area ArticleProg.ofs A s1)
    (hD : ArtDom A s1.memaddrs) {m0 : Word → Word} {a : Bytes} (hlen : a.length ≤ artMax) {SEP : Nat}
    (hB : ChkBase s1 A m0 SEP esP) {L : List (Nat × Nat)} (hL : Lines a 0 L SEP)
      (hok : L.any (DN.News.ArticleLines.malLine a) = false)
    {l : List (String × Value)} (hla : l.lookup "a" = some A) {nm : String} (hn : nm ∈ allNames)
    (hnl : nm.length < ArticleProg.nameCap)
    (hR : DN.News.ArticleAdded.firstP a L nm = none → ∀ M m, ChkT s1 A m0 a (groups a L) M →
      (∀ j (hj : j < (ArticleProg.codes nm).length), memLoadByte m s1.memaddrs s1.be
        (at_ A (ArticleProg.xName + j)) = some (BitVec.ofNat 8 (ArticleProg.codes nm)[j])) →
      m (at_ A ArticleProg.xNameLen) = BitVec.ofNat 64 nm.length →
      (∀ x, (∀ y, ArticleProg.xName ≤ y → y < ArticleProg.xName + ArticleProg.nameCap → x ≠ at_ A y) →
        x ≠ at_ A ArticleProg.xNameLen → m x = M x) →
      R (BitVec.ofNat 64 13) m) :
    FragR o R (guardS (ifs (Syntax.eLt (ArticleProg.firstOf esP nm) (Syntax.n 0))
        (ArticleProg.constName nm ++ [.ret (Syntax.n 13)])))
      (RunF s1 l (ChkT s1 A m0 a (groups a L)))
      (fun u => RunF s1 l (ChkT s1 A m0 a (groups a L)) u ∧ (DN.News.ArticleAdded.firstP a L nm).isSome) := by
  have hM := artMax_eq
  have hlow : LowKK (cRet nm 13) := const_low nm 13
  rw [DN.News.ArticleAdded.guardS_ifs, constName_g]
  refine fragR_if o (DN.News.ArticleAdded.lt0_lower esP nm) hlow (lowK_any _ (k := .skip) rfl)
    (fun u k h => ⟨runF_clock _ _ _ u k h.1, h.2⟩) (fun _ _ _ _ hy => by rw [cRet_declared] at hy; nomatch hy)
    (fun _ _ _ _ hy => nomatch hy) (b := (DN.News.ArticleAdded.firstP a L nm).isNone)
    (fun u h => DN.News.ArticleAdded.lt0_eval (fun x hx => by have := DN.News.ArticleAdded.firstP_lt hL hok x hx; omega)
      (firstE_eval hB hla h hn)) (fun hs => ?_) fun hs => ?_
  · exact runF_pin o hlow fun M hM => const_ret o hA hD hla hnl fun m hm =>
      hR (by simpa using hs) M m hM hm.1 hm.2.1 hm.2.2
  · exact fragR_of (frag_nil o fun u h => ⟨h, by simpa using hs⟩)

/-! ## A named field's value -/

open DN.News.ArticleAdded (Ss)

/-- **The first field of a name read**: its place, end, name's length and value's bounds in the locals. -/
theorem field_frag (o : Oracle σ) {R : Ret} {A : Word} {s1 : PancakeState σ} (hA : Area ArticleProg.ofs A s1)
    (hD : ArtDom A s1.memaddrs) (hcode : ArtCode s1.code) {m0 : Word → Word} {a : Bytes} (hlen : a.length ≤ artMax)
    {SEP : Nat} (hB : ChkBase s1 A m0 SEP esP) {L : List (Nat × Nat)} {l : List (String × Value)}
    (hla : l.lookup "a" = some A) {nm : String} (hn : nm ∈ allNames) {P e : Nat} {more : List (Nat × Nat)}
    (hP : DN.News.ArticleAdded.firstP a L nm = some P) (hf : DN.News.ArticleLines.FieldAt a SEP P e more)
    {xp xf xn xs xe : String} (hxf : xf ≠ "a") (h1 : Fresh xp l = true)
    (h2 : Fresh xf ((xp, BitVec.ofNat 64 P) :: l) = true)
    (h3 : Fresh xn ((xf, BitVec.ofNat 64 (DN.News.ArticleLines.nextOf a more SEP)) :: (xp, BitVec.ofNat 64 P) :: l)
      = true)
    (h4 : Fresh xs ((xn, BitVec.ofNat 64 (DN.News.ArticleLines.nameLen a P e)) ::
      (xf, BitVec.ofNat 64 (DN.News.ArticleLines.nextOf a more SEP)) :: (xp, BitVec.ofNat 64 P) :: l) = true)
    (h5 : Fresh xe ((xs, BitVec.ofNat 64 (P + DN.News.ArticleLines.nameLen a P e + 1)) ::
      (xn, BitVec.ofNat 64 (DN.News.ArticleLines.nameLen a P e)) ::
      (xf, BitVec.ofNat 64 (DN.News.ArticleLines.nextOf a more SEP)) :: (xp, BitVec.ofNat 64 P) :: l) = true)
    (hxp : ∀ w, ((xp, w) :: l).lookup "a" = some A)
    (hpf : ∀ w1 w2 w3, ((xn, w3) :: (xf, w2) :: (xp, w1) :: l).lookup xp = some w1 ∧
      ((xn, w3) :: (xf, w2) :: (xp, w1) :: l).lookup xn = some w3)
    (hfe : ∀ w1 w2 w3 w4, ((xs, w4) :: (xn, w3) :: (xf, w2) :: (xp, w1) :: l).lookup xf = some w2) :
    FragR o R ([.dec xp (ArticleProg.firstOf esP nm)] ++ guardS (.call xf "artField" [Syntax.v xp]) ++
        ([.dec xn (wd ArticleProg.xNl), .dec xs (Syntax.eAdd (Syntax.eAdd (Syntax.v xp) (Syntax.v xn)) (Syntax.n 1)),
          .dec xe (Syntax.eSub (Syntax.v xf) (Syntax.n 2))] : Ss))
      (RunF s1 l (ChkT s1 A m0 a (groups a L)))
      (RunF s1 ((xe, BitVec.ofNat 64 (DN.News.ArticleLines.nextOf a more SEP - 2)) ::
        (xs, BitVec.ofNat 64 (P + DN.News.ArticleLines.nameLen a P e + 1)) ::
        (xn, BitVec.ofNat 64 (DN.News.ArticleLines.nameLen a P e)) ::
        (xf, BitVec.ofNat 64 (DN.News.ArticleLines.nextOf a more SEP)) :: (xp, BitVec.ofNat 64 P) :: l)
        (ChkT s1 A m0 a (groups a L))) := by
  have hA8 := hA.hA
  let K := DN.News.ArticleLines.nameLen a P e
  let NX := DN.News.ArticleLines.nextOf a more SEP
  have hmore := (DN.News.ArticleLines.lines_tail hf.lines).2
  have hNXg := (DN.News.ArticleLines.nextOf_ge hmore).1
  have hw : ∀ M, ChkT s1 A m0 a (groups a L) M → ChkT s1 A m0 a (groups a L) (fieldMem A K e M) := fun M hM =>
    chkT_mid hA8 hlen hM (S := HiScr A) (fun _ h => DN.News.ArticleFields.hi_at h) (fun _ h => .inl h) fun x hx => by
      simp only [fieldMem]
      rw [upd_ne _ fun h => hx (.inr (.inl h)), upd_ne _ fun h => hx (.inl h)]
  have hla2 : ∀ w1 w2, ((xf, w2) :: (xp, w1) :: l).lookup "a" = some A := fun w1 w2 => by
    rw [List.lookup_cons, beq_false_of_ne (Ne.symm hxf)]; exact hxp w1
  refine fragR_append (xs := [.dec xp (ArticleProg.firstOf esP nm)] ++ guardS (.call xf "artField" [Syntax.v xp]) ++
    [.dec xn (wd ArticleProg.xNl)])
    (M := RunF s1 ((xn, BitVec.ofNat 64 K) :: (xf, BitVec.ofNat 64 NX) :: (xp, BitVec.ofNat 64 P) :: l)
      (ChkT s1 A m0 a (groups a L))) (runF_pin o (lowKK_append (lowKK_append (lowKK_dec (DN.News.ArticleAdded.wd_lowerX
        (DN.News.ArticleAdded.first_ne0 esP nm))) (lowK_any _ (k := .skip) rfl)) (lowKK_dec (wd_lower 17)))
        fun M hM => ?_) ?_
  · refine fragR_append (fragR_append (fragR_of (runF_dec o (DN.News.ArticleAdded.wd_lowerX
      (DN.News.ArticleAdded.first_ne0 esP nm)) h1 (v := BitVec.ofNat 64 P) fun u h => ?_))
      (fieldCall_frag o hA hD hcode hlen (rt := xf) hxf (l := (xp, BitVec.ofNat 64 P) :: l) (hxp _) h2
        (e1 := Syntax.v xp) rfl hf (fun u h => ev_var (vals_lookup h.1.vals (by simp))) hM.reads.input
        (chkT_broken hM hB.broken) (chkT_sep hM hB))) ?_
    · rw [loadA_eval h.1.memaddrs (DN.News.ArticleAdded.first_dom hB.tdom (DN.News.ArticleAdded.entry_le esP nm))
        (atA_eval (vals_lookup h.1.vals hla)), h.2]
      have := chkT_firstW hM hn
      unfold DN.News.ArticleAdded.FirstW at this
      rw [this, hP]; rfl
    · exact fragR_conseq (fragR_of (runF_dec o (wd_lower 17) h3 (v := BitVec.ofNat 64 K) fun u h => by
        rw [loadA_eval h.1.memaddrs (artDom_w hD (i := 17) (by decide)) (atA_eval (vals_lookup h.1.vals (hla2 _ _))),
          h.2]
        exact congrArg some (fieldMem_nl A K e M))) (fun _ h => h)
        fun u h => runF_mono h (fun q hq => hq) fun m hm => by rw [hm]; exact hw M hM
  refine fragR_append (xs := [_]) (fragR_of (runF_dec o rfl h4 (v := BitVec.ofNat 64 (P + K + 1)) fun u h =>
    ev_add3 (vals_lookup h.1.vals (hpf _ _ _).1) (vals_lookup h.1.vals (hpf _ _ _).2))) ?_
  exact fragR_of (runF_dec o rfl h5 (v := BitVec.ofNat 64 (NX - 2)) fun u h =>
    ev_sub (y := 2) (by rw [show 2 + (NX - 2) = NX by omega]; exact ev_var (vals_lookup h.1.vals (hfe _ _ _ _))) rfl)

theorem mem_artPosted : gd ArticleProg.artPosted ∈ ArticleProg.functions ArticleSpec.spec esP .none :=
  List.mem_append_right _ (List.mem_map.2 ⟨ArticleProg.artPosted, by simp, rfl⟩)

theorem mem_artDistAll : gd ArticleProg.artDistAll ∈ ArticleProg.functions ArticleSpec.spec esP .none :=
  List.mem_append_right _ (List.mem_map.2 ⟨ArticleProg.artDistAll, by simp, rfl⟩)

/-- **A call of a list element's test** `f`: whether an element passes `p`; only the element's words change. -/
theorem elemCall_frag (o : Oracle σ) {R : Ret} {A : Word} {s0 : PancakeState σ} (hA : Area ArticleProg.ofs A s0)
    (hD : ArtDom A s0.memaddrs) (hcode : ArtCode s0.code) {a : Bytes} {rt : String}
    (hra : rt ≠ "a") {l : List (String × Value)} (hla : l.lookup "a" = some A) (hrt : Fresh rt l = true)
    {m0 : Word → Word} (hb : m0 (at_ A aBroken) = 0) (hin : InputAt m0 s0.memaddrs s0.be A a) {S E : Nat}
    {e1 e2 : Syntax.PExpr} {E1 E2 : PancakeExp} (he1 : Lower.lowerExp e1 = some E1) (he2 : Lower.lowerExp e2 = some E2)
    (hv1 : ∀ u, RunF s0 l (· = m0) u → eval u E1 = some (BitVec.ofNat 64 S))
    (hv2 : ∀ u, RunF s0 l (· = m0) u → eval u E2 = some (BitVec.ofNat 64 E))
    {f : Syntax.PFun} (hfm : gd f ∈ ArticleProg.functions ArticleSpec.spec esP .none)
    (hps : f.params.map (·.2) = ["s", "e"]) {p : Bytes → Bool}
    (hok : ∀ s : PancakeState σ, Area ArticleProg.ofs A s → ArtDom A s.memaddrs → ArtCode s.code →
      s.memory (at_ A aBroken) = 0 → InputAt s.memory s.memaddrs s.be A a →
      s.locals "s" = some (BitVec.ofNat 64 S) → s.locals "e" = some (BitVec.ofNat 64 E) →
      ∃ body, Lower.lower (gd f) = some body ∧ SafeR o (fun s' => s' = s) body
        (fun v m => v = bw (p (seg a S E)) ∧ ∀ x, ¬elemScratch A x → m x = s.memory x) fun _ => False) :
    FragR o R (guardS (.call rt f.name [e1, e2])) (RunF s0 l (· = m0))
      (fun u => ∃ m, RunF s0 ((rt, bw (p (seg a S E))) :: l) (· = m) u ∧ ∀ x, ¬elemScratch A x → m x = m0 x) := by
  refine fragR_conseq (gcall_frag o hA hcode hra (f := f) hfm (by rw [hps]; decide) (F := (· = m0))
    (DN.News.AbnfGen.lowerArgs_two he1 he2) hla (vs := [BitVec.ofNat 64 S, BitVec.ofNat 64 E]) (by rw [hps]; rfl)
    (fun u h => by simp only [evalArgs, hv1 u h, hv2 u h])
    (Rf := fun m1 v m => v = bw (p (seg a S E)) ∧ ∀ x, ¬elemScratch A x → m x = m1 x)
    (fun s1 hA1 hc hm hbe hloc hF => hok s1 hA1 (by rw [hm]; exact hD) (by rw [hc]; exact hcode) (by rw [hF]; exact hb)
      (by rw [hF, hm, hbe]; exact hin) ((hloc "s").trans (by rw [hps]; rfl)) ((hloc "e").trans (by rw [hps]; rfl))) hrt
    (G := fun v m => v = bw (p (seg a S E)) ∧ ∀ x, ¬elemScratch A x → m x = m0 x)
    (fun m m' v hm hr => by subst hm; exact hr) fun v m h => by
      rw [h.2 _ (DN.News.ArticleListRun.not_scratch_low DN.News.ArticleGrammar.broken_low)]; exact hb)
    (fun u h => h) fun u ⟨v, h⟩ => ?_
  obtain ⟨hv, hm⟩ := h.2
  subst hv; exact ⟨u.memory, ⟨h.1, rfl⟩, hm⟩

/-- **The first field of a name**, if the table has its place: where it lies, and its value's bounds. -/
theorem first_field {a : Bytes} {SEP : Nat} {L : List (Nat × Nat)} (hL : Lines a 0 L SEP)
    (hok : L.any (DN.News.ArticleLines.malLine a) = false) {nm : String} {P : Nat}
    (hP : DN.News.ArticleAdded.firstP a L nm = some P) :
    ∃ e more, DN.News.ArticleLines.FieldAt a SEP P e more ∧
      ArticleSpec.find? ((groups a L).map (fieldOf a)) nm = some (fieldOf a ((P, e) :: more.takeWhile (cont a))) ∧
      (fieldOf a ((P, e) :: more.takeWhile (cont a))).value =
        seg a (P + DN.News.ArticleLines.nameLen a P e + 1) (DN.News.ArticleLines.nextOf a more SEP - 2) ∧
      P + DN.News.ArticleLines.nameLen a P e + 1 ≤ DN.News.ArticleLines.nextOf a more SEP - 2 ∧
      DN.News.ArticleLines.nextOf a more SEP - 2 ≤ a.length := by
  unfold DN.News.ArticleAdded.firstP at hP
  cases hg : DN.News.ArticleAdded.firstG a L nm with
  | none => rw [hg] at hP; nomatch hP
  | some g =>
    obtain ⟨P', e, more, rfl, hf, -, hP'⟩ := DN.News.ArticleAdded.first_at hL hok hg
    have hPP : P' = P := by
      unfold DN.News.ArticleAdded.firstP at hP'; rw [hg] at hP hP'; exact Option.some.inj (hP'.symm.trans hP)
    subst hPP
    have hcol := DN.News.ArticleLines.fieldAt_colon hf
    have hmore := (DN.News.ArticleLines.lines_tail hf.lines).2
    have hNXs := DN.News.ArticleLines.lines_sep (DN.News.ArticleAdded.lines_next more (e + 2) hmore)
    have hNXg := (DN.News.ArticleLines.nextOf_ge hmore).1
    refine ⟨e, more, hf, by rw [DN.News.ArticleAdded.find_fields, hg]; rfl,
      DN.News.ArticleAdded.value_seg hf.lines hcol.2.1, by omega, by omega⟩

/-- The first field of a name read into locals: its place, end, name's length, value's start and end. -/
def fieldS (nm pp pf pn ps pe : String) : List Syntax.PStmt :=
  [.dec pp (ArticleProg.firstOf esP nm), .call pf "artField" [Syntax.v pp], .dec pn (wd ArticleProg.xNl),
   .dec ps (Syntax.eAdd (Syntax.eAdd (Syntax.v pp) (Syntax.v pn)) (Syntax.n 1)),
   .dec pe (Syntax.eSub (Syntax.v pf) (Syntax.n 2))]

/-- `fieldS` with its call guarded. -/
def fieldG (nm pp pf pn ps pe : String) : List Syntax.PStmt :=
  [.dec pp (ArticleProg.firstOf esP nm)] ++ guardS (.call pf "artField" [Syntax.v pp]) ++
    ([.dec pn (wd ArticleProg.xNl), .dec ps (Syntax.eAdd (Syntax.eAdd (Syntax.v pp) (Syntax.v pn)) (Syntax.n 1)),
      .dec pe (Syntax.eSub (Syntax.v pf) (Syntax.n 2))] : Ss)

theorem fieldG_low (nm pp pf pn ps pe : String) : LowKK (fieldG nm pp pf pn ps pe) :=
  lowKK_append (lowKK_append (lowKK_dec (DN.News.ArticleAdded.wd_lowerX (DN.News.ArticleAdded.first_ne0 esP nm)))
    (lowK_any _ (k := .skip) rfl)) (lowK_any _ (k := .skip) rfl)

/-- A list element's test `f` on the first field of a name: `N` given back if an element passes. -/
def elemS (nm pp pf pn ps pe pv : String) (f : Syntax.PFun) (N : Nat) : List Syntax.PStmt :=
  guardS (ifs (Syntax.eLe (Syntax.n 0) (ArticleProg.firstOf esP nm))
    (fieldS nm pp pf pn ps pe ++ [.call pv f.name [Syntax.v ps, Syntax.v pe], ifs (Syntax.v pv) [.ret (Syntax.n N)]]))

theorem elem_g (nm pp pf pn ps pe pv : String) (f : Syntax.PFun) (N : Nat) :
    guardL (fieldS nm pp pf pn ps pe ++ [.call pv f.name [Syntax.v ps, Syntax.v pe], ifs (Syntax.v pv)
      [.ret (Syntax.n N)]]) =
    fieldG nm pp pf pn ps pe ++ (guardS (.call pv f.name [Syntax.v ps, Syntax.v pe]) ++
      [.ite (Syntax.v pv) [.ret (Syntax.n N)] []]) := rfl

theorem elemB_low (nm pp pf pn ps pe pv : String) (f : Syntax.PFun) (N : Nat) :
    LowKK (fieldG nm pp pf pn ps pe ++ (guardS (.call pv f.name [Syntax.v ps, Syntax.v pe]) ++
      [.ite (Syntax.v pv) [.ret (Syntax.n N)] []])) :=
  lowKK_append (fieldG_low _ _ _ _ _ _) (lowK_any _ (k := .skip) rfl)

theorem elemS_low (nm pp pf pn ps pe pv : String) (f : Syntax.PFun) (N : Nat) :
    LowKK (elemS nm pp pf pn ps pe pv f N) := by
  unfold elemS
  rw [DN.News.ArticleAdded.guardS_ifs, elem_g]
  exact lowKK_ite (DN.News.ArticleAdded.flag_lower esP nm) (elemB_low _ _ _ _ _ _ _ _ _) fun k => ⟨k, rfl⟩

/-- **A list element tested**, looked for in the first field of a name: `N` given back if one passes `p`. -/
theorem elem_step (o : Oracle σ) {R : Ret} {A : Word} {s1 : PancakeState σ} (hA : Area ArticleProg.ofs A s1)
    (hD : ArtDom A s1.memaddrs) (hcode : ArtCode s1.code) {m0 : Word → Word} {a : Bytes} (hlen : a.length ≤ artMax)
    {SEP : Nat} (hB : ChkBase s1 A m0 SEP esP) {L : List (Nat × Nat)} (hL : Lines a 0 L SEP)
    (hok : L.any (DN.News.ArticleLines.malLine a) = false) {l : List (String × Value)}
    (hla : l.lookup "a" = some A) {nm pp pf pn ps pe pv : String} (hn : nm ∈ allNames)
    (hd : [pp, pf, pn, ps, pe, pv, "a"].Nodup) (hfr : ∀ y, y ∈ [pp, pf, pn, ps, pe, pv] → Fresh y l = true)
    {f : Syntax.PFun} (hfm : gd f ∈ ArticleProg.functions ArticleSpec.spec esP .none)
    (hps : f.params.map (·.2) = ["s", "e"]) {p : Bytes → Bool}
    (hfok : ∀ S E, S ≤ E → E ≤ a.length → ∀ s : PancakeState σ, Area ArticleProg.ofs A s → ArtDom A s.memaddrs →
      ArtCode s.code → s.memory (at_ A aBroken) = 0 → InputAt s.memory s.memaddrs s.be A a →
      s.locals "s" = some (BitVec.ofNat 64 S) → s.locals "e" = some (BitVec.ofNat 64 E) →
      ∃ body, Lower.lower (gd f) = some body ∧ SafeR o (fun s' => s' = s) body
        (fun v m => v = bw (p (seg a S E)) ∧ ∀ x, ¬elemScratch A x → m x = s.memory x) fun _ => False)
    {N : Nat} (hR : ((ArticleSpec.find? ((groups a L).map (fieldOf a)) nm).map (fun g => p g.value)).getD false = true →
      ∀ M, ChkT s1 A m0 a (groups a L) M → R (BitVec.ofNat 64 N) M) :
    FragR o R (elemS nm pp pf pn ps pe pv f N) (RunF s1 l (ChkT s1 A m0 a (groups a L)))
      (fun u => RunF s1 l (ChkT s1 A m0 a (groups a L)) u ∧
        ((ArticleSpec.find? ((groups a L).map (fieldOf a)) nm).map (fun g => p g.value)).getD false = false) := by
  simp only [List.nodup_cons, List.mem_cons, List.mem_nil_iff, or_false, not_or, List.nodup_nil, and_true] at hd
  obtain ⟨⟨h12, h13, h14, h15, h16, h1a⟩, ⟨h23, h24, h25, h26, h2a⟩, ⟨h34, h35, h36, h3a⟩, ⟨h45, h46, h4a⟩,
    ⟨h56, h5a⟩, h6a, -⟩ := hd
  have hM := artMax_eq
  unfold elemS
  rw [DN.News.ArticleAdded.guardS_ifs, elem_g]
  refine fragR_if o (DN.News.ArticleAdded.flag_lower esP nm) (elemB_low _ _ _ _ _ _ _ _ _)
    (lowK_any _ (k := .skip) rfl) (fun u k h => ⟨runF_clock _ _ _ u k h.1, h.2⟩)
    (fun u y w h hy => ⟨runF_restore h.1 (hfr y (by simpa [fieldG, declared, guardS, guardL, ifs] using hy)) w, h.2⟩)
    (fun _ _ _ _ hy => nomatch hy) (b := (DN.News.ArticleAdded.firstP a L nm).isSome)
    (fun u h => DN.News.ArticleAdded.flag_eval
      (fun x hx => by have := DN.News.ArticleAdded.firstP_lt hL hok x hx; omega)
      (firstE_eval hB hla h hn)) (fun hs => ?_) fun hs => ?_
  · obtain ⟨P, hP⟩ := Option.isSome_iff_exists.1 hs
    obtain ⟨e, more, hf, hfind, hval, hSE, hE⟩ := first_field hL hok hP
    refine fragR_append (field_frag o hA hD hcode hlen hB hla hn hP hf (xp := pp) (xf := pf) (xn := pn)
      (xs := ps) (xe := pe) h2a (hfr _ (by simp)) (fresh_cons h12 (hfr _ (by simp)))
      (fresh_cons h23 (fresh_cons h13 (hfr _ (by simp))))
      (fresh_cons h34 (fresh_cons h24 (fresh_cons h14 (hfr _ (by simp)))))
      (fresh_cons h45 (fresh_cons h35 (fresh_cons h25 (fresh_cons h15 (hfr _ (by simp))))))
      (fun w => (lookup_cons_ne (Ne.symm h1a) w l).trans hla)
      (fun _ _ _ => ⟨by rw [lookup_cons_ne h13, lookup_cons_ne h12, lookup_head], lookup_head _ _ _⟩)
      fun _ _ _ _ => by rw [lookup_cons_ne h24, lookup_cons_ne h23, lookup_head]) ?_
    refine runF_pin o (lowK_any _ (k := .skip) rfl) fun M hM => ?_
    refine fragR_append (elemCall_frag o hA hD hcode (rt := pv) h6a
      (by rw [lookup_cons_ne (Ne.symm h5a), lookup_cons_ne (Ne.symm h4a), lookup_cons_ne (Ne.symm h3a),
        lookup_cons_ne (Ne.symm h2a), lookup_cons_ne (Ne.symm h1a)]; exact hla)
      (fresh_cons h56 (fresh_cons h46 (fresh_cons h36 (fresh_cons h26 (fresh_cons h16 (hfr _ (by simp)))))))
      (chkT_broken hM hB.broken) hM.reads.input (e1 := Syntax.v ps) (e2 := Syntax.v pe) rfl rfl
      (fun u h => ev_var (vals_lookup h.1.vals (by rw [lookup_cons_ne h45, lookup_head])))
      (fun u h => ev_var (vals_lookup h.1.vals (lookup_head _ _ _))) hfm hps (hfok _ _ hSE hE)) ?_
    refine fragR_exists (lowK_any _ (k := .skip) rfl) fun m => ?_
    refine fragR_pure (∀ x, ¬elemScratch A x → m x = M x) (fun u h => h.2) (lowK_any _ (k := .skip) rfl)
      fun hm => ?_
    have hT : ChkT s1 A m0 a (groups a L) m := chkT_mid hA.hA hlen hM (S := elemScratch A)
      (fun _ h => g_at (.inl h)) (fun _ h => .inr (.inl h)) hm
    have hspec : ((ArticleSpec.find? ((groups a L).map (fieldOf a)) nm).map (fun g => p g.value)).getD false =
        p (seg a (P + DN.News.ArticleLines.nameLen a P e + 1) (DN.News.ArticleLines.nextOf a more SEP - 2)) := by
      rw [hfind, Option.map_some, Option.getD_some, hval]
    refine fragR_conseq (P0 := RunF s1 _ (· = m)) ?_ (fun u h => h.1) fun _ h => h
    refine fragR_if o rfl (lowK_any _ (k := .skip) rfl) (lowK_any _ (k := .skip) rfl)
      (fun u k h => ⟨runF_clock _ _ _ u k h.1, h.2⟩) (fun _ _ _ _ hy => nomatch hy) (fun _ _ _ _ hy => nomatch hy)
      (b := p (seg a (P + DN.News.ArticleLines.nameLen a P e + 1) (DN.News.ArticleLines.nextOf a more SEP - 2)))
      (fun u h => ev_var (vals_lookup h.1.vals (lookup_head _ _ _))) (fun hb => ?_) fun hb => ?_
    · exact fragR_ret o rfl fun u h => ⟨_, rfl, by rw [h.2]; exact hR (by rw [hspec]; exact hb) m hT⟩
    · exact fragR_of (frag_nil o fun u h => ⟨runF_mono h (fun q hq => by simp [hq]) fun _ hh => hh ▸ hT,
        by rw [hspec]; simpa using hb⟩)
  · have hnone : DN.News.ArticleAdded.firstP a L nm = none := by simpa using hs
    refine fragR_of (frag_nil o fun u h => ⟨h, ?_⟩)
    unfold DN.News.ArticleAdded.firstP at hnone
    rw [DN.News.ArticleAdded.find_fields]
    cases hg : DN.News.ArticleAdded.firstG a L nm with
    | none => rfl
    | some g => rw [hg] at hnone; nomatch hnone

/-! ## Sender -/

theorem mailbox_used : AbnfProg.ruleIndex "mailbox" ∈ ArticleProg.usedRules := by
  unfold ArticleProg.usedRules; exact List.mem_eraseDups.2 (List.mem_append_right _ (by simp))

/-- The condition of the Sender check: no Sender, a From. -/
def senderE : PancakeExp :=
  .op .and_ (.cmp .less (DN.News.ArticleAdded.firstE esP "Sender") (.const (BitVec.ofNat 64 0)))
    (.cmp .notLess (DN.News.ArticleAdded.firstE esP "From") (.const (BitVec.ofNat 64 0)))

theorem sender_lower : Lower.lowerExp (Syntax.eAnd (Syntax.eLt (ArticleProg.firstOf esP "Sender") (Syntax.n 0))
    (Syntax.eLe (Syntax.n 0) (ArticleProg.firstOf esP "From"))) = some senderE := by
  simp only [Syntax.eAnd, Lower.lowerExp, DN.News.ArticleAdded.flag_lower, DN.News.ArticleAdded.lt0_lower]; rfl

theorem sender_spec {fs : List Field} {f : Field} (h1 : ArticleSpec.has fs "Sender" = false)
    (h2 : ArticleSpec.find? fs "From" = some f) :
    (!ArticleSpec.has fs "Sender" && ((ArticleSpec.find? fs "From").map
      (fun f => !ArticleSpec.grammarSays (ArticleSpec.ruleNamed "mailbox") f.value)).getD false) =
      !ArticleSpec.grammarSays (ArticleSpec.ruleNamed "mailbox") f.value := by
  rw [h1, h2, Option.map_some, Option.getD_some, Bool.not_false, Bool.true_and]

/-- Sender. -/
def tSender : List Syntax.PStmt :=
  guardS (ifs (Syntax.eAnd (Syntax.eLt (ArticleProg.firstOf esP "Sender") (Syntax.n 0))
    (Syntax.eLe (Syntax.n 0) (ArticleProg.firstOf esP "From")))
    (fieldS "From" "fp" "ff" "fn" "fs" "fe" ++
     [.call "mb" "artGrammar" [Syntax.n (AbnfProg.ruleIndex "mailbox"), Syntax.v "fs", Syntax.v "fe"],
      ifs (Syntax.eEq (Syntax.v "mb") (Syntax.n 0)) [.ret (Syntax.n 16)]]))

theorem senderB_low : LowKK (fieldG "From" "fp" "ff" "fn" "fs" "fe" ++
    (guardS (.call "mb" "artGrammar" [Syntax.n (AbnfProg.ruleIndex "mailbox"), Syntax.v "fs", Syntax.v "fe"]) ++
      [.ite (Syntax.eEq (Syntax.v "mb") (Syntax.n 0)) [.ret (Syntax.n 16)] []])) :=
  lowKK_append (fieldG_low _ _ _ _ _ _) (lowK_any _ (k := .skip) rfl)

theorem tSender_low : LowKK tSender := by
  unfold tSender
  rw [DN.News.ArticleAdded.guardS_ifs]
  exact lowKK_ite sender_lower senderB_low fun k => ⟨k, rfl⟩

/-- **No Sender and a From that is no mailbox**: 16 given back. -/
theorem sender_step (o : Oracle σ) {R : Ret} {A : Word} {s1 : PancakeState σ} (hA : Area ArticleProg.ofs A s1)
    (hD : ArtDom A s1.memaddrs) (hcode : ArtCode s1.code) {m0 : Word → Word} {a : Bytes} (hlen : a.length ≤ artMax)
    {SEP : Nat} (hB : ChkBase s1 A m0 SEP esP) (hSI : SEP ≤ inputMax) {L : List (Nat × Nat)} (hL : Lines a 0 L SEP)
    (hok : L.any (DN.News.ArticleLines.malLine a) = false) {l : List (String × Value)}
    (hla : l.lookup "a" = some A) (hfr : ∀ y, y ∈ ["fp", "ff", "fn", "fs", "fe", "mb"] → Fresh y l = true)
    (hgm : ArticleSpec.has ((groups a L).map (fieldOf a)) "Sender" = false →
      ∀ f, ArticleSpec.find? ((groups a L).map (fieldOf a)) "From" = some f →
      ∃ b, DN.News.Abnf.matches? AbnfRules.grammar AbnfRules.depth (ArticleSpec.ruleNamed "mailbox")
        (f.value.map BitVec.toNat) = .ok b)
    (hR : (!ArticleSpec.has ((groups a L).map (fieldOf a)) "Sender" &&
      ((ArticleSpec.find? ((groups a L).map (fieldOf a)) "From").map
        (fun f => !ArticleSpec.grammarSays (ArticleSpec.ruleNamed "mailbox") f.value)).getD false) = true →
      ∀ M, ChkT s1 A m0 a (groups a L) M → R (BitVec.ofNat 64 16) M) :
    FragR o R tSender
      (RunF s1 l (ChkT s1 A m0 a (groups a L)))
      (fun u => RunF s1 l (ChkT s1 A m0 a (groups a L)) u ∧
        (!ArticleSpec.has ((groups a L).map (fieldOf a)) "Sender" &&
          ((ArticleSpec.find? ((groups a L).map (fieldOf a)) "From").map
            (fun f => !ArticleSpec.grammarSays (ArticleSpec.ruleNamed "mailbox") f.value)).getD false) = false) := by
  have hnS : "Sender" ∈ allNames := by simp [allNames, ArticleProg.readNames]
  have hnF : "From" ∈ allNames := by simp [allNames, ArticleProg.readNames]
  have hM := artMax_eq
  have hsep := DN.News.ArticleLines.lines_sep hL
  have hhas : ∀ nm, ArticleSpec.has ((groups a L).map (fieldOf a)) nm = (DN.News.ArticleAdded.firstP a L nm).isSome :=
    DN.News.ArticleAdded.has_fields a L
  unfold tSender
  rw [DN.News.ArticleAdded.guardS_ifs]
  have h63 : ∀ nm, ∀ x, DN.News.ArticleAdded.firstP a L nm = some x → x < 2 ^ 63 := fun nm x hx => by
    have := DN.News.ArticleAdded.firstP_lt hL hok x hx; omega
  refine fragR_if o sender_lower senderB_low (lowK_any _ (k := .skip) rfl)
    (fun u k h => ⟨runF_clock _ _ _ u k h.1, h.2⟩) (fun u y w h hy => ⟨runF_restore h.1 (hfr y (by
      simpa [fieldG, declared, guardS, guardL, ifs] using hy)) w, h.2⟩)
    (fun _ _ _ _ hy => nomatch hy)
    (b := (DN.News.ArticleAdded.firstP a L "Sender").isNone && (DN.News.ArticleAdded.firstP a L "From").isSome)
    (fun u h => DN.News.FramerCode.eval_and (DN.News.ArticleAdded.lt0_eval (h63 _) (firstE_eval hB hla h hnS))
      (DN.News.ArticleAdded.flag_eval (h63 _) (firstE_eval hB hla h hnF))) (fun hs => ?_) fun hs => ?_
  · obtain ⟨hS0, hF1⟩ := Bool.and_eq_true_iff.1 hs
    obtain ⟨P, hP⟩ := Option.isSome_iff_exists.1 hF1
    obtain ⟨e, more, hf, hfind, hval, hSE, hE⟩ := first_field hL hok hP
    have hnoS : ArticleSpec.has ((groups a L).map (fieldOf a)) "Sender" = false := by
      rw [hhas]; simpa using hS0
    obtain ⟨b, hb⟩ := hgm hnoS _ hfind
    rw [hval] at hb
    have hfrs : ∀ y, y ∈ ["fp", "ff", "fn", "fs", "fe", "mb"] → Fresh y l = true := hfr
    let S := P + DN.News.ArticleLines.nameLen a P e + 1
    let E := DN.News.ArticleLines.nextOf a more SEP - 2
    have hNX := (DN.News.ArticleLines.lines_sep (DN.News.ArticleAdded.lines_next more (e + 2)
      (DN.News.ArticleLines.lines_tail hf.lines).2)).1
    have hG : DN.News.AbnfGen.setOf (DN.News.AbnfMatch.Matches AbnfRules.grammar (inputOf (a.take E))
        (.ref (AbnfProg.ruleIndex "mailbox")) S) E = ArticleSpec.grammarSays (ArticleSpec.ruleNamed "mailbox")
          (seg a S E) :=
      DN.News.ArticleFields.gram_field hSE hE hb
    have hspec : (!ArticleSpec.has ((groups a L).map (fieldOf a)) "Sender" &&
        ((ArticleSpec.find? ((groups a L).map (fieldOf a)) "From").map
          (fun f => !ArticleSpec.grammarSays (ArticleSpec.ruleNamed "mailbox") f.value)).getD false) =
        !ArticleSpec.grammarSays (ArticleSpec.ruleNamed "mailbox") (seg a S E) := by
      rw [sender_spec hnoS hfind, hval]
    refine fragR_append (field_frag o hA hD hcode hlen hB hla hnF hP hf (xp := "fp") (xf := "ff")
      (xn := "fn") (xs := "fs") (xe := "fe") (by decide) (hfrs _ (by simp)) (hfrs _ (by simp)) (hfrs _ (by simp))
      (hfrs _ (by simp)) (hfrs _ (by simp)) (fun _ => hla) (fun _ _ _ => ⟨rfl, rfl⟩) (fun _ _ _ _ => rfl)) ?_
    refine runF_pin o (lowK_any _ (k := .skip) rfl) fun M hM => ?_
    refine fragR_append (DN.News.ArticleFields.gramCall_frag o hA hcode (rt := "mb") (by decide) ?_ ?_ hlen hM.reads
      hM.sets (chkT_broken hM hB.broken) mailbox_used (by omega) (by omega) hE
      (e1 := Syntax.n (AbnfProg.ruleIndex "mailbox")) (e2 := Syntax.v "fs") (e3 := Syntax.v "fe") rfl rfl rfl
      (fun _ _ => rfl) (fun u h => ev_var (vals_lookup h.1.vals rfl)) (fun u h => ev_var (vals_lookup h.1.vals rfl))) ?_
    · exact hla
    · exact hfrs _ (by simp)
    refine fragR_exists (lowK_any _ (k := .skip) rfl) fun m => ?_
    refine fragR_pure (Reads s1 A a m ∧ AllSets A m ∧
      ∀ x, (∀ k, k < slots → ¬InSlot A k x) → x ≠ at_ A aLen → m x = M x) (fun u h => h.2)
      (lowK_any _ (k := .skip) rfl) fun ⟨hR', hall, hfr'⟩ => ?_
    have hT := chkT_gram hM hR' hall hfr'
    refine fragR_conseq (P0 := RunF s1 _ (· = m)) ?_ (fun u h => h.1) fun _ h => h
    obtain ⟨G, hGdef⟩ : ∃ G, ArticleSpec.grammarSays (ArticleSpec.ruleNamed "mailbox") (seg a S E) = G := ⟨_, rfl⟩
    rw [hGdef] at hG hspec
    rw [hG]
    have hGv : bw G = BitVec.ofNat 64 (if G then 1 else 0) := DN.News.ArticleRun.bw_ofNat G
    refine fragR_if o rfl (lowK_any _ (k := .skip) rfl) (lowK_any _ (k := .skip) rfl)
      (fun u k h => ⟨runF_clock _ _ _ u k h.1, h.2⟩) (fun _ _ _ _ hy => nomatch hy) (fun _ _ _ _ hy => nomatch hy)
      (b := decide ((if G then 1 else 0) = 0)) (fun u h => DN.News.FramerCode.eval_eq (by split <;> decide) (by decide)
        (by rw [ev_var (vals_lookup h.1.vals rfl), hGv]) rfl) (fun hb1 => ?_) fun hb1 => ?_
    · have hG0 : G = false := by cases hG' : G <;> simp_all
      exact fragR_ret o rfl fun u h => ⟨_, rfl, by rw [h.2]; exact hR (by rw [hspec, hG0]; rfl) m hT⟩
    · have hG1 : G = true := by cases hG' : G <;> simp_all
      exact fragR_of (frag_nil o fun u h => ⟨runF_mono h (fun q hq => by simp [hq]) fun _ hh => hh ▸ hT,
        by rw [hspec, hG1]; rfl⟩)
  · refine fragR_of (frag_nil o fun u h => ⟨h, ?_⟩)
    rw [hhas]
    cases hs1 : (DN.News.ArticleAdded.firstP a L "Sender").isNone
    · have : (DN.News.ArticleAdded.firstP a L "Sender").isSome = true := by
        cases e : DN.News.ArticleAdded.firstP a L "Sender" <;> simp_all
      rw [this]; rfl
    · rw [hs1, Bool.true_and] at hs
      have hnone : DN.News.ArticleAdded.firstP a L "From" = none := by simpa using hs
      rw [DN.News.ArticleAdded.find_fields]
      unfold DN.News.ArticleAdded.firstP at hnone
      cases hg : DN.News.ArticleAdded.firstG a L "From" with
      | none => simp
      | some g => rw [hg] at hnone; nomatch hnone

/-! ## The dates' windows -/

/-- The checks of a window after the date, over any name: nothing to work out in them. -/
def winAhead (t nm : String) : Syntax.PStmt :=
  .ite (Syntax.eLt (Syntax.n ArticleSpec.spec.ahead) (Syntax.eSub (Syntax.v t) (wd ArticleProg.xWall))) (cRet nm 19) []

def winPast (t nm : String) : Syntax.PStmt :=
  .ite (Syntax.eLt (Syntax.n ArticleSpec.spec.past) (Syntax.eSub (wd ArticleProg.xWall) (Syntax.v t))) (cRet nm 20) []

def winTail (v t nm : String) : List Syntax.PStmt :=
  [.ite (Syntax.eEq (Syntax.v v) (Syntax.n 2)) (cRet nm 19) [],
   .ite (Syntax.eEq (Syntax.v v) (Syntax.n 1)) ([.dec t (wd ArticleProg.xValue)] ++ [winAhead t nm, winPast t nm]) []]

theorem winAhead_low (t nm : String) : LowKK [winAhead t nm] := lowKK_ite rfl (const_low nm 19) fun k => ⟨k, rfl⟩
theorem winPast_low (t nm : String) : LowKK [winPast t nm] := lowKK_ite rfl (const_low nm 20) fun k => ⟨k, rfl⟩

theorem winIn_low (t nm : String) : LowKK ([.dec t (wd ArticleProg.xValue)] ++ [winAhead t nm, winPast t nm]) :=
  lowKK_append (lowKK_dec (wd_lower 15)) (lowKK_append (winAhead_low t nm) (winPast_low t nm))

/-- A date's window on a name's first field: 19 given back for a date ahead, 20 for one past. -/
def winS (nm pp pf pn ps pe pv pt : String) : List Syntax.PStmt :=
  guardS (ifs (Syntax.eLe (Syntax.n 0) (ArticleProg.firstOf esP nm))
    (fieldS nm pp pf pn ps pe ++
     [.call pv "artDate" [Syntax.v ps, Syntax.v pe],
      ifs (Syntax.eEq (Syntax.v pv) (Syntax.n 2)) (ArticleProg.constName nm ++ [.ret (Syntax.n 19)]),
      ifs (Syntax.eEq (Syntax.v pv) (Syntax.n 1))
        [.dec pt (wd ArticleProg.xValue),
         ifs (Syntax.eLt (Syntax.n ArticleSpec.spec.ahead) (Syntax.eSub (Syntax.v pt) (wd ArticleProg.xWall)))
           (ArticleProg.constName nm ++ [.ret (Syntax.n 19)]),
         ifs (Syntax.eLt (Syntax.n ArticleSpec.spec.past) (Syntax.eSub (wd ArticleProg.xWall) (Syntax.v pt)))
           (ArticleProg.constName nm ++ [.ret (Syntax.n 20)])]]))

theorem win_g (nm pp pf pn ps pe pv pt : String) :
    guardL (fieldS nm pp pf pn ps pe ++
      [.call pv "artDate" [Syntax.v ps, Syntax.v pe],
       ifs (Syntax.eEq (Syntax.v pv) (Syntax.n 2)) (ArticleProg.constName nm ++ [.ret (Syntax.n 19)]),
       ifs (Syntax.eEq (Syntax.v pv) (Syntax.n 1))
         [.dec pt (wd ArticleProg.xValue),
          ifs (Syntax.eLt (Syntax.n ArticleSpec.spec.ahead) (Syntax.eSub (Syntax.v pt) (wd ArticleProg.xWall)))
            (ArticleProg.constName nm ++ [.ret (Syntax.n 19)]),
          ifs (Syntax.eLt (Syntax.n ArticleSpec.spec.past) (Syntax.eSub (wd ArticleProg.xWall) (Syntax.v pt)))
            (ArticleProg.constName nm ++ [.ret (Syntax.n 20)])]]) =
    fieldG nm pp pf pn ps pe ++ (guardS (.call pv "artDate" [Syntax.v ps, Syntax.v pe]) ++ winTail pv pt nm) := by
  unfold winTail winAhead winPast
  rw [← constName_g, ← constName_g]
  rfl

theorem winTail_declared (v t nm : String) : declared (winTail v t nm) = [] := rfl

theorem winTail_low (v t nm : String) : LowKK (winTail v t nm) :=
  lowKK_append (lowKK_ite rfl (const_low nm 19) fun k => ⟨k, rfl⟩) (lowKK_ite rfl (winIn_low t nm) fun k => ⟨k, rfl⟩)

theorem winS_low (nm pp pf pn ps pe pv pt : String) : LowKK (winS nm pp pf pn ps pe pv pt) := by
  unfold winS
  rw [DN.News.ArticleAdded.guardS_ifs, win_g]
  exact lowKK_ite (DN.News.ArticleAdded.flag_lower esP nm) (lowKK_append (fieldG_low _ _ _ _ _ _)
    (lowKK_append (lowK_any _ (k := .skip) rfl) (winTail_low _ _ _))) fun k => ⟨k, rfl⟩

theorem window_none {ctx : ArticleSpec.Context} {fs : List Field} {nm : String} (h : ArticleSpec.find? fs nm = none) :
    window ctx fs nm = none := by unfold window; rw [h]; rfl

theorem window_nodate {ctx : ArticleSpec.Context} {fs : List Field} {nm : String} {f : Field}
    (h : ArticleSpec.find? fs nm = some f) (hd : ArticleSpec.dateValue f.value = none) : window ctx fs nm = none := by
  unfold window; rw [h, Option.bind_some, hd]

theorem window_date {ctx : ArticleSpec.Context} {fs : List Field} {nm : String} {f : Field} {t : Int}
    (h : ArticleSpec.find? fs nm = some f) (hd : ArticleSpec.dateValue f.value = some t) :
    window ctx fs nm = if t - (ctx.wall : Int) > (ArticleSpec.spec.ahead : Int) then
      some (.dateAhead (DN.News.CommandSpec.ascii nm))
      else if (ctx.wall : Int) - t > (ArticleSpec.spec.past : Int) then some (.datePast (DN.News.CommandSpec.ascii nm))
      else none := by
  unfold window; rw [h, Option.bind_some, hd]

/-- A signed comparison with a difference, all small. -/
theorem slt_sub {c : Nat} (hc : c < 2 ^ 62) {X Y : Word} {t w : Int} (hX : X.toInt = t) (hY : Y.toInt = w)
    (ht : -2 ^ 61 < t ∧ t < 2 ^ 61) (hw : -2 ^ 61 < w ∧ w < 2 ^ 61) :
    signedLt (BitVec.ofNat 64 c) (X - Y) = decide ((c : Int) < t - w) := by
  simp only [signedLt, BitVec.slt_eq_decide, BitVec.toInt_sub, hX, hY, BitVec.toInt_ofNat']
  rw [Int.bmod_eq_of_le (by omega) (by omega), Int.bmod_eq_of_le (by omega) (by omega)]

theorem toInt_ofInt_small {t : Int} (ht : -2 ^ 61 < t ∧ t < 2 ^ 61) : (BitVec.ofInt 64 t).toInt = t := by
  rw [BitVec.toInt_ofInt, Int.bmod_eq_of_le (by omega) (by omega)]

theorem toInt_ofNat_small {w : Nat} (hw : w < 2 ^ 61) : (BitVec.ofNat 64 w).toInt = w := by
  rw [BitVec.toInt_ofNat', Int.bmod_eq_of_le (by omega) (by omega)]

theorem eval_slt_sub {u : PancakeState σ} {a b : PancakeExp} {c : Nat} (hc : c < 2 ^ 62) {X Y : Word} {t w : Int}
    (ha : eval u a = some X) (hb : eval u b = some Y) (hX : X.toInt = t) (hY : Y.toInt = w)
    (ht : -2 ^ 61 < t ∧ t < 2 ^ 61) (hw : -2 ^ 61 < w ∧ w < 2 ^ 61) :
    eval u (.cmp .less (.const (BitVec.ofNat 64 c)) (.op .sub a b)) = some (bw (decide ((c : Int) < t - w))) := by
  simp only [eval, ha, hb, slt_sub hc hX hY ht hw]
  cases decide ((c : Int) < t - w) <;> rfl

/-- **A date's window**: 19 given back for a date ahead, 20 for one past, the name written. -/
theorem window_step (o : Oracle σ) {R : Ret} {A : Word} {s1 : PancakeState σ} (hA : Area ArticleProg.ofs A s1)
    (hD : ArtDom A s1.memaddrs) (hcode : ArtCode s1.code) {m0 : Word → Word} {a : Bytes} (hlen : a.length ≤ artMax)
    {SEP : Nat} (hB : ChkBase s1 A m0 SEP esP) {L : List (Nat × Nat)} (hL : Lines a 0 L SEP)
    (hok : L.any (DN.News.ArticleLines.malLine a) = false) {l : List (String × Value)}
    (hla : l.lookup "a" = some A) {nm pp pf pn ps pe pv pt : String} (hn : nm ∈ allNames)
    (hnl : nm.length < ArticleProg.nameCap) (hd : [pp, pf, pn, ps, pe, pv, pt, "a"].Nodup)
    (hfr : ∀ y, y ∈ [pp, pf, pn, ps, pe, pv, pt] → Fresh y l = true)
    {ctx : ArticleSpec.Context} (hwall : m0 (at_ A ArticleProg.xWall) = BitVec.ofNat 64 ctx.wall)
    (hwm : ctx.wall < ArticleProg.wallMax)
    (hR : ∀ x, window ctx ((groups a L).map (fieldOf a)) nm = some x → ∀ M m,
      ChkT s1 A m0 a (groups a L) M → ConstAt A s1.memaddrs s1.be nm M m →
      R (BitVec.ofNat 64 (DN.News.ArticleFields.refNum x)) m) :
    FragR o R (winS nm pp pf pn ps pe pv pt)
      (RunF s1 l (ChkT s1 A m0 a (groups a L)))
      (fun u => RunF s1 l (ChkT s1 A m0 a (groups a L)) u ∧ window ctx ((groups a L).map (fieldOf a)) nm = none) :=
        by
  simp only [List.nodup_cons, List.mem_cons, List.mem_nil_iff, or_false, not_or, List.nodup_nil, and_true] at hd
  obtain ⟨⟨h12, h13, h14, h15, h16, h17, h1a⟩, ⟨h23, h24, h25, h26, h27, h2a⟩, ⟨h34, h35, h36, h37, h3a⟩,
    ⟨h45, h46, h47, h4a⟩, ⟨h56, h57, h5a⟩, ⟨h67, h6a⟩, h7a, -⟩ := hd
  have ha5 : ∀ w5 w4 w3 w2 w1, ((pe, w5) :: (ps, w4) :: (pn, w3) :: (pf, w2) :: (pp, w1) :: l).lookup "a" = some A :=
    fun _ _ _ _ _ => by
      rw [lookup_cons_ne (Ne.symm h5a), lookup_cons_ne (Ne.symm h4a), lookup_cons_ne (Ne.symm h3a),
        lookup_cons_ne (Ne.symm h2a), lookup_cons_ne (Ne.symm h1a)]
      exact hla
  have ha6 : ∀ w6 w5 w4 w3 w2 w1,
      ((pv, w6) :: (pe, w5) :: (ps, w4) :: (pn, w3) :: (pf, w2) :: (pp, w1) :: l).lookup "a" = some A :=
    fun _ _ _ _ _ _ => by rw [lookup_cons_ne (Ne.symm h6a)]; exact ha5 _ _ _ _ _
  have ha7 : ∀ w7 w6 w5 w4 w3 w2 w1,
      ((pt, w7) :: (pv, w6) :: (pe, w5) :: (ps, w4) :: (pn, w3) :: (pf, w2) :: (pp, w1) :: l).lookup "a" = some A :=
    fun _ _ _ _ _ _ _ => by rw [lookup_cons_ne (Ne.symm h7a)]; exact ha6 _ _ _ _ _ _
  have hM := artMax_eq
  have hwm' : ArticleProg.wallMax = 2 ^ 40 := rfl
  have hah : ArticleSpec.spec.ahead = 86400 := rfl
  let Q : Assn σ := fun u => RunF s1 l (ChkT s1 A m0 a (groups a L)) u ∧
    window ctx ((groups a L).map (fieldOf a)) nm = none
  have hQ : Safe.ClockFree Q := fun u k h => ⟨runF_clock _ _ _ u k h.1, h.2⟩
  have hQr : ∀ y, y ∈ [pp, pf, pn, ps, pe, pv, pt] → ∀ u w, Q u → Q (restore u y w) :=
    fun y hy u w h => ⟨runF_restore h.1 (hfr y hy) w, h.2⟩
  unfold winS
  rw [DN.News.ArticleAdded.guardS_ifs, win_g]
  have hlow := lowKK_append (fieldG_low nm pp pf pn ps pe) (lowKK_append (lowK_any (k := .skip)
    (guardS (.call pv "artDate" [Syntax.v ps, Syntax.v pe])) rfl) (winTail_low pv pt nm))
  have h63 : ∀ x, DN.News.ArticleAdded.firstP a L nm = some x → x < 2 ^ 63 := fun x hx => by
    have := DN.News.ArticleAdded.firstP_lt hL hok x hx; omega
  refine fragR_if o (DN.News.ArticleAdded.flag_lower esP nm) hlow (lowK_any _ (k := .skip) rfl) hQ
    (fun u y w h hy => hQr y (by
      simp only [fieldG, guardS, ifs, List.cons_append, List.nil_append, declared, winTail_declared, List.mem_cons,
        List.not_mem_nil, or_false] at hy; rcases hy with rfl | rfl | rfl | rfl | rfl | rfl <;> simp) u
        w h)
    (fun _ _ _ _ hy => nomatch hy) (b := (DN.News.ArticleAdded.firstP a L nm).isSome)
    (fun u h => DN.News.ArticleAdded.flag_eval h63 (firstE_eval hB hla h hn)) (fun hs => ?_) fun hs => ?_
  · obtain ⟨P, hP⟩ := Option.isSome_iff_exists.1 hs
    obtain ⟨e, more, hf, hfind, hval, hSE, hE⟩ := first_field hL hok hP
    have hfrs : ∀ y, y ∈ [pp, pf, pn, ps, pe, pv, pt] → Fresh y l = true := hfr
    refine fragR_append (field_frag o hA hD hcode hlen hB hla hn hP hf (xp := pp) (xf := pf) (xn := pn)
      (xs := ps) (xe := pe) h2a (hfrs _ (by simp)) (fresh_cons h12 (hfrs _ (by simp)))
      (fresh_cons h23 (fresh_cons h13 (hfrs _ (by simp))))
      (fresh_cons h34 (fresh_cons h24 (fresh_cons h14 (hfrs _ (by simp)))))
      (fresh_cons h45 (fresh_cons h35 (fresh_cons h25 (fresh_cons h15 (hfrs _ (by simp))))))
      (fun w => (lookup_cons_ne (Ne.symm h1a) w l).trans hla)
      (fun _ _ _ => ⟨by rw [lookup_cons_ne h13, lookup_cons_ne h12, lookup_head], lookup_head _ _ _⟩)
      fun _ _ _ _ => by rw [lookup_cons_ne h24, lookup_cons_ne h23, lookup_head]) ?_
    refine runF_pin o (lowKK_append (lowK_any _ (k := .skip) rfl) (winTail_low _ _ _)) fun M hM => ?_
    have hlowR : LowKK (winTail pv pt nm) := winTail_low _ _ _
    refine fragR_append (DN.News.ArticleFields.dateCall_frag o hA hD hcode hlen (rt := pv)
      h6a (ha5 _ _ _ _ _) (fresh_cons h56 (fresh_cons h46 (fresh_cons h36 (fresh_cons h26 (fresh_cons h16
        (hfrs _ (by simp))))))) hM.reads.pows
      (chkT_broken hM hB.broken) hM.reads.input hSE hE (e1 := Syntax.v ps) (e2 := Syntax.v pe) rfl rfl
      (fun u h => ev_var (vals_lookup h.1.vals (by rw [lookup_cons_ne h45, lookup_head])))
      fun u h => ev_var (vals_lookup h.1.vals (lookup_head _ _ _))) ?_
    refine fragR_exists hlowR fun w => fragR_exists hlowR fun m => ?_
    refine fragR_pure _ (fun u h => h.2) hlowR fun hr => ?_
    refine fragR_conseq (P0 := RunF s1 _ (· = m)) ?_ (fun u h => h.1) fun _ h => h
    have hT : ChkT s1 A m0 a (groups a L) m := chkT_mid hA.hA hlen hM (S := DN.News.ArticleDateRun.scratch A)
      (fun _ h => DN.News.ArticleFields.hi_at (.inr (.inr (.inl h)))) (fun _ h => .inl (.inr (.inr (.inl h)))) hr.1
    have hwm2 : m (at_ A ArticleProg.xWall) = BitVec.ofNat 64 ctx.wall :=
      (hT.frame _ (DN.News.ArticleFields.not_chk_w (i := 2) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide)) (not_g_w (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide))).trans hwall
    have hwin_t : ∀ t, ArticleSpec.dateValue (seg a (P + DN.News.ArticleLines.nameLen a P e + 1)
        (DN.News.ArticleLines.nextOf a more SEP - 2)) = some t →
        window ctx ((groups a L).map (fieldOf a)) nm = if t - (ctx.wall : Int) > (ArticleSpec.spec.ahead : Int) then
          some (.dateAhead (DN.News.CommandSpec.ascii nm))
        else if (ctx.wall : Int) - t > (ArticleSpec.spec.past : Int) then some
          (.datePast (DN.News.CommandSpec.ascii nm)) else none :=
      fun t ht => window_date hfind (by rw [hval]; exact ht)
    have hQm : ∀ l' : List (String × Value), (∀ q ∈ l, q ∈ l') → ∀ u, RunF s1 l' (· = m) u →
        window ctx ((groups a L).map (fieldOf a)) nm = none → Q u :=
      fun l' hl' u h hw => ⟨runF_mono h hl' fun _ hh => hh ▸ hT, hw⟩
    have hev : ∀ (x : Nat), x < 3 → ∀ (l' : List (String × Value)) u, RunF s1 ((pv, BitVec.ofNat 64 x) :: l')
        (· = m) u → ∀ y, y < 3 →
        eval u (.cmp .equal (.var pv) (.const (BitVec.ofNat 64 y))) = some (bw (decide (x = y))) :=
      fun x hx l' u h y hy => DN.News.FramerCode.eval_eq (by omega) (by omega)
        (ev_var (vals_lookup h.1.vals (lookup_head _ _ _))) rfl
    have hlowI := winIn_low pt nm
    simp only [winTail, winAhead, winPast]
    rcases hr.2 with ⟨rfl, h0⟩ | ⟨rfl, t, ht, h1, h2, hv⟩ | ⟨rfl, t, ht, h2⟩
    · have hw0 : window ctx ((groups a L).map (fieldOf a)) nm = none := window_nodate hfind (by rw [hval]; exact h0)
      refine fragR_append (xs := [_]) (fragR_if o rfl (const_low _ _) (fun k => ⟨k, rfl⟩) (runF_clock _ _ _)
        (fun _ _ _ _ hy => by rw [cRet_declared] at hy; nomatch hy) (fun _ _ _ _ hy => nomatch hy)
        (b := false) (fun u h => hev 0 (by decide) _ u h 2 (by decide)) (fun h => nomatch h) fun _ =>
          fragR_of (frag_nil o fun _ h => h)) ?_
      exact fragR_if o rfl (lowKK_append (lowKK_dec (wd_lower 15)) (lowKK_append (lowKK_ite rfl (const_low _ _)
          fun k => ⟨k, rfl⟩) (lowKK_ite rfl (const_low _ _) fun k => ⟨k, rfl⟩))) (fun k => ⟨k, rfl⟩) hQ
        (fun u y w h hy => hQr y (by simp only [List.cons_append, List.nil_append, declared, List.mem_cons,
                                      List.not_mem_nil, or_false] at hy; subst hy; simp) u w h)
                                        (fun _ _ _ _ hy => nomatch hy)
        (b := false) (fun u h => hev 0 (by decide) _ u h 1 (by decide)) (fun h => nomatch h) fun _ =>
          fragR_of (frag_nil o fun u h => hQm _ (fun q hq => by simp [hq]) u h hw0)
    · refine fragR_append (xs := [_]) (fragR_if o rfl (const_low _ _) (fun k => ⟨k, rfl⟩) (runF_clock _ _ _)
        (fun _ _ _ _ hy => by rw [cRet_declared] at hy; nomatch hy) (fun _ _ _ _ hy => nomatch hy)
        (b := false) (fun u h => hev 1 (by decide) _ u h 2 (by decide)) (fun h => nomatch h) fun _ =>
          fragR_of (frag_nil o fun _ h => h)) ?_
      refine fragR_if o rfl hlowI (fun k => ⟨k, rfl⟩) hQ
        (fun u y w h hy => hQr y (by simp only [winAhead, winPast, List.cons_append, List.nil_append, declared,
                                      List.mem_cons, List.not_mem_nil, or_false] at hy; subst hy; simp) u w h)
        (fun _ _ _ _ hy => nomatch hy) (b := true) (fun u h => hev 1 (by decide) _ u h 1 (by decide))
          (fun _ => ?_) fun h => nomatch h
      have ht61 : -2 ^ 61 < t ∧ t < 2 ^ 61 := ⟨by omega, by omega⟩
      have hw61 : -2 ^ 61 < (ctx.wall : Int) ∧ (ctx.wall : Int) < 2 ^ 61 := ⟨by omega, by omega⟩
      have hwi : (BitVec.ofNat 64 ctx.wall).toInt = ctx.wall := toInt_ofNat_small (by omega)
      have hti : (BitVec.ofInt 64 t).toInt = t := toInt_ofInt_small ht61
      have hwall_eval : ∀ (l' : List (String × Value)), l'.lookup "a" = some A → ∀ u, RunF s1 l' (· = m) u →
          eval u (.loadWord (.op .add (.var "a") (.const (BitVec.ofNat 64 ArticleProg.xWall)))) =
            some (BitVec.ofNat 64 ctx.wall) := fun l' hl u h => by
        rw [loadA_eval (y := ArticleProg.xWall) h.1.memaddrs (artDom_w hD (i := 2) (by decide))
          (atA_eval (vals_lookup h.1.vals hl)), h.2]
        exact congrArg some hwm2
      refine fragR_append (xs := [_]) (fragR_of (runF_dec o (F := (· = m)) (wd_lower 15)
        (fresh_cons h67 (fresh_cons h57 (fresh_cons h47 (fresh_cons h37 (fresh_cons h27 (fresh_cons h17
          (hfrs pt (by simp))))))))
        (v := BitVec.ofInt 64 t) fun u h => by
          rw [loadA_eval h.1.memaddrs (artDom_w hD (i := 15) (by decide)) (atA_eval
            (vals_lookup h.1.vals (ha6 _ _ _ _ _ _))), h.2]
          exact congrArg some hv)) ?_
      have hwt := hwin_t t ht
      have hl4 := winPast_low pt nm
      simp only [winPast] at hl4
      by_cases h3 : ((ArticleSpec.spec.ahead : Nat) : Int) < t - ctx.wall
      · have hx : window ctx ((groups a L).map (fieldOf a)) nm =
            some (.dateAhead (DN.News.CommandSpec.ascii nm)) := by rw [hwt, if_pos h3]
        refine fragR_append (xs := [_]) (fragR_if o rfl (const_low _ _) (fun k => ⟨k, rfl⟩) (fun _ _ h => h)
          (Q := fun _ => False) (fun _ _ _ h _ => h) (fun _ _ _ h _ => h) (b := true)
          (fun u h => by
            rw [eval_slt_sub (c := ArticleSpec.spec.ahead) (by decide) (ev_var
              (vals_lookup h.1.vals (lookup_head _ _ _)))
              (hwall_eval _ (ha7 _ _ _ _ _ _ _) u h) hti hwi ht61 hw61, decide_eq_true h3]; rfl)
          (fun _ => const_ret o hA hD (ha7 _ _ _ _ _ _ _) hnl (N := 19) fun m' hc => hR _ hx m m' hT hc)
          fun h => nomatch h) ?_
        exact fragR_of (frag_unsat hl4 fun _ h => h.elim)
      refine fragR_append (xs := [_]) (fragR_if o rfl (const_low _ _) (fun k => ⟨k, rfl⟩) (runF_clock _ _ _)
        (fun _ _ _ _ hy => by rw [cRet_declared] at hy; nomatch hy) (fun _ _ _ _ hy => nomatch hy) (b := false)
        (fun u h => by
          rw [eval_slt_sub (c := ArticleSpec.spec.ahead) (by decide) (ev_var (vals_lookup h.1.vals (lookup_head _ _ _)))
            (hwall_eval _ (ha7 _ _ _ _ _ _ _) u h) hti hwi ht61 hw61, decide_eq_false h3]; rfl)
        (fun h => nomatch h) fun _ => fragR_of (frag_nil o fun _ h => h)) ?_
      refine fragR_if o rfl (const_low _ _) (fun k => ⟨k, rfl⟩) hQ
        (fun _ _ _ _ hy => by rw [cRet_declared] at hy; nomatch hy) (fun _ _ _ _ hy => nomatch hy)
        (b := decide (((ArticleSpec.spec.past : Nat) : Int) < ctx.wall - t))
        (fun u h => eval_slt_sub (c := ArticleSpec.spec.past) (by decide) (hwall_eval _ (ha7 _ _ _ _ _ _ _) u h)
          (ev_var (vals_lookup h.1.vals (lookup_head _ _ _))) hwi hti hw61 ht61) (fun hb => ?_) fun hb => ?_
      · have hx : window ctx ((groups a L).map (fieldOf a)) nm =
            some (.datePast (DN.News.CommandSpec.ascii nm)) := by
          rw [hwt, if_neg h3, if_pos (of_decide_eq_true hb)]
        exact const_ret o hA hD (ha7 _ _ _ _ _ _ _) hnl (N := 20) fun m' hc => hR _ hx m m' hT hc
      · have hx : window ctx ((groups a L).map (fieldOf a)) nm = none := by
          rw [hwt, if_neg h3, if_neg (of_decide_eq_false hb)]
        exact fragR_of (frag_nil o fun u h => hQm _ (fun q hq => by simp [hq]) u h hx)
    · have hx : window ctx ((groups a L).map (fieldOf a)) nm = some (.dateAhead (DN.News.CommandSpec.ascii nm))
        := by
        rw [hwin_t t ht, if_pos (by omega)]
      refine fragR_append (xs := [_]) (fragR_if o rfl (const_low _ _) (fun k => ⟨k, rfl⟩) (fun _ _ h => h)
        (Q := fun _ => False) (fun _ _ _ h _ => h) (fun _ _ _ h _ => h) (b := true)
        (fun u h => hev 2 (by decide) _ u h 2 (by decide))
        (fun _ => const_ret o hA hD (ha6 _ _ _ _ _ _) hnl (N := 19) fun m' hc => hR _ hx m m' hT hc)
        fun h => nomatch h) ?_
      exact fragR_of (frag_unsat (lowKK_ite rfl hlowI fun k => ⟨k, rfl⟩) fun _ h => h.elim)
  · have hnone : DN.News.ArticleAdded.firstP a L nm = none := by simpa using hs
    refine fragR_of (frag_nil o fun u h => ⟨h, window_none ?_⟩)
    rw [DN.News.ArticleAdded.find_fields]
    unfold DN.News.ArticleAdded.firstP at hnone
    cases hg : DN.News.ArticleAdded.firstG a L nm with
    | none => rfl
    | some g => rw [hg] at hnone; nomatch hnone

/-! ## The groups -/

open DN.News.ArticleListRun (GroupsAt gAt KnownAt Kf)

/-- A word of the context's groups is none the checks write. -/
theorem groups_free {A : Word} {y : Nat} (hy1 : ArticleProg.xGroups ≤ y) (hy2 : y < ArticleProg.xName) :
    ¬ChkScr A (at_ A y) ∧ ¬gScratch A (at_ A y) := by
  have hX := X_val; have hF := xFirst_eq; have hT := DN.News.ArticleScan.xTok_eq
  have hG := DN.News.ArticleListRun.xGroups_eq; have hI := xName_eq
  have hE := DN.News.ArticleListRun.xElem_eq
  have hs := DN.News.ArticleFields.w_eq
  have hw : ∀ z, z < 2 ^ 40 → at_ A y = at_ A z → y = z := fun z hz e =>
    DN.News.ScanRun.at_inj (by omega) (by omega) e
  constructor
  · rintro (h | h | ⟨k, hk, hin⟩ | ⟨k, hk, e⟩)
    · rcases h with e | e | (e | e | e | e | e) | e | e
      · have := hw _ (by simp only [ArticleProg.xNl, hs]; omega) e; simp only [ArticleProg.xNl, hs] at this; omega
      · have := hw _ (by simp only [ArticleProg.xE1, hs]; omega) e; simp only [ArticleProg.xE1, hs] at this; omega
      · have := hw _ (by simp only [ArticleProg.xTokS, hs]; omega) e; simp only [ArticleProg.xTokS, hs] at this; omega
      · have := hw _ (by simp only [ArticleProg.xTokLen, hs]; omega) e
        simp only [ArticleProg.xTokLen, hs] at this; omega
      · have := hw _ (by simp only [ArticleProg.xNumMod, hs]; omega) e
        simp only [ArticleProg.xNumMod, hs] at this; omega
      · have := hw _ (by simp only [ArticleProg.xValue, hs]; omega) e
        simp only [ArticleProg.xValue, hs] at this; omega
      · have := hw _ (by omega) e; omega
      · have := hw _ (by simp only [ArticleProg.xMsgS, hs]; omega) e; simp only [ArticleProg.xMsgS, hs] at this; omega
      · have := hw _ (by simp only [ArticleProg.xMsgL, hs]; omega) e; simp only [ArticleProg.xMsgL, hs] at this; omega
    · have := hw _ (by decide) h; have : aLen = 8 := rfl; omega
    · exact DN.News.ArticleFields.notInSlot_high hk (by omega) (by omega) hin
    · rw [esP_length] at hk; have := hw _ (by omega) e; omega
  · intro h
    obtain ⟨z, h1, h2, e⟩ := g_at h
    have hz := hw _ (by omega) e
    subst hz
    rcases h with (⟨k, hk, e⟩ | e | e) | ⟨y', hy', e⟩
    · have := hw _ (by omega) e; omega
    · have := hw _ (by simp only [ArticleProg.xElemLen, hs]; omega) e; simp only
        [ArticleProg.xElemLen, hs] at this; omega
    · have := hw _ (by simp only [ArticleProg.xElemRes, hs]; omega) e; simp only
        [ArticleProg.xElemRes, hs] at this; omega
    · have hlt := DN.News.ArticleListRun.gWrites_lt hy'
      have := hw _ (by omega) e; omega

/-- **The context kept** where its words are. -/
theorem ctxAt_keep {A : Word} (hA8 : A.toNat % 8 = 0) {dm : Word → Bool} {be : Bool} {ctx : ArticleSpec.Context}
    {m M : Word → Word} (hw : ∀ i, 2 ≤ i → i ≤ 7 → M (at_ A (ArticleProg.w i)) = m (at_ A (ArticleProg.w i)))
    (hk : ∀ y, ArticleProg.xGroups ≤ y → y < ArticleProg.xName → M (at_ A y) = m (at_ A y))
    (hc : DN.News.ArticleAdded.CtxAt A dm be ctx m) : DN.News.ArticleAdded.CtxAt A dm be ctx M := by
  have hG := DN.News.ArticleListRun.xGroups_eq; have hI := DN.News.ArticleAdded.xId_eq; have hN := xName_eq
  have hR := DN.News.ArticleAdded.xRand_eq
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩ := hc
  refine ⟨h1, (hw 6 (by decide) (by decide)).trans h2, DN.News.ArticleListRun.bytesAt_frame h3 fun i hi _ => ?_, h4,
    (hw 7 (by decide) (by decide)).trans h5, DN.News.ArticleListRun.bytesAt_frame h6 fun i hi _ => ?_, h7,
    (hw 3 (by decide) (by decide)).trans h8, h9, (hw 4 (by decide) (by decide)).trans h10, h11,
    (hw 5 (by decide) (by decide)).trans h12, h13, (hw 2 (by decide) (by decide)).trans h14⟩
  · rw [DN.News.ScanRun.align_at hA8]; exact hk _ (by omega) (by omega)
  · rw [DN.News.ScanRun.align_at hA8]; exact hk _ (by omega) (by omega)

/-- **The context's groups kept** where their words are. -/
theorem groupsAt_keep {A : Word} (hA8 : A.toNat % 8 = 0) {dm : Word → Bool} {be : Bool} {G : List Bytes}
    {m M : Word → Word} (h8 : M (at_ A ArticleProg.xGroupsN) = m (at_ A ArticleProg.xGroupsN))
    (hk : ∀ y, ArticleProg.xGroups ≤ y → y < ArticleProg.xName → M (at_ A y) = m (at_ A y))
    (hG : GroupsAt A dm be G m) : GroupsAt A dm be G M := by
  have hGe := DN.News.ArticleListRun.xGroups_eq; have hN := xName_eq
  have hgs : ArticleProg.groupSize = 80 := rfl
  obtain ⟨hl, hn, hj⟩ := hG
  refine ⟨hl, h8.trans hn, fun j hj' => ?_⟩
  obtain ⟨h1, h2, h3⟩ := hj j hj'
  have hgj : gAt j = ArticleProg.xGroups + j * 80 := by unfold gAt; rw [hgs]
  refine ⟨h1, by rw [hk _ (by omega) (by rw [hgj]; omega)]; exact h2, fun i hi1 hi2 => ?_⟩
  have := h3 i hi1 hi2
  unfold memLoadByte at this ⊢
  rw [DN.News.ScanRun.align_at hA8] at this ⊢
  rw [hk _ (by omega) (by rw [hgj]; omega)]; exact this

/-- **The context's groups kept** in the checks after the fields. -/
theorem groupsAt_T {s1 : PancakeState σ} {A : Word} (hA8 : A.toNat % 8 = 0) {m0 : Word → Word} {a : Bytes}
    {gs : List (List (Nat × Nat))} {M : Word → Word} (h : ChkT s1 A m0 a gs M) {dm : Word → Bool} {be : Bool}
    {G : List Bytes} (hG : GroupsAt A dm be G m0) : GroupsAt A dm be G M := by
  exact groupsAt_keep hA8 (h.frame _ (DN.News.ArticleFields.not_chk_w (i := 8) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
      (not_g_w (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide))) (fun y h1 h2 => h.frame _ (groups_free h1 h2).1
    (groups_free h1 h2).2) hG

theorem mem_artGroups : gd ArticleProg.artGroups ∈ ArticleProg.functions ArticleSpec.spec esP .none :=
  List.mem_append_right _ (List.mem_map.2 ⟨ArticleProg.artGroups, by simp, rfl⟩)

/-- **A call of `artGroups`** on the value from `S` to `E`: its counts and the known groups' places. -/
theorem groupsCall_frag (o : Oracle σ) {R : Ret} {A : Word} {s0 : PancakeState σ} (hA : Area ArticleProg.ofs A s0)
    (hD : ArtDom A s0.memaddrs) (hcode : ArtCode s0.code) {a : Bytes} (hlen : a.length ≤ artMax) {rt : String}
    (hra : rt ≠ "a") {l : List (String × Value)} (hla : l.lookup "a" = some A) (hrt : Fresh rt l = true)
    {m0 : Word → Word} (hb : m0 (at_ A aBroken) = 0) {G : List Bytes} (hG : GroupsAt A s0.memaddrs s0.be G m0)
    (hin : InputAt m0 s0.memaddrs s0.be A a) {S E : Nat} (hSE : S ≤ E) (hE : E ≤ a.length) {e1 e2 : Syntax.PExpr}
    {E1 E2 : PancakeExp} (he1 : Lower.lowerExp e1 = some E1) (he2 : Lower.lowerExp e2 = some E2)
    (hv1 : ∀ u, RunF s0 l (· = m0) u → eval u E1 = some (BitVec.ofNat 64 S))
    (hv2 : ∀ u, RunF s0 l (· = m0) u → eval u E2 = some (BitVec.ofNat 64 E)) :
    FragR o R (guardS (.call rt "artGroups" [e1, e2])) (RunF s0 l (· = m0))
      (fun u => ∃ w m, RunF s0 ((rt, w) :: l) (· = m) u ∧ DN.News.ArticleListRun.GroupsRet A G a S E m0 w m) := by
  refine fragR_conseq (gcall_frag o hA hcode hra (f := ArticleProg.artGroups) mem_artGroups (by decide)
    (F := (· = m0)) (DN.News.AbnfGen.lowerArgs_two he1 he2) hla (vs := [BitVec.ofNat 64 S, BitVec.ofNat 64 E]) rfl
    (fun u h => by simp only [evalArgs, hv1 u h, hv2 u h]) (Rf := DN.News.ArticleListRun.GroupsRet A G a S E)
    (fun s1 hA1 hc hm hbe hloc hF => by
      have := DN.News.ArticleListRun.artGroups_ok o hA1 (by rw [hm]; exact hD) (by rw [hc]; exact hcode)
        (by rw [hF]; exact hb) (by rw [hF, hm, hbe]; exact hG) hlen (by rw [hF, hm, hbe]; exact hin) hSE hE
        ((hloc "s").trans rfl) ((hloc "e").trans rfl)
      exact this) hrt
    (G := DN.News.ArticleListRun.GroupsRet A G a S E m0) (fun m m' w hm hr => by subst hm; exact hr) fun w m h => by
      rw [h.1 _ (fun hg => not_g (.inl (by have := DN.News.ArticleGrammar.broken_low; have := sets_le_X; omega))
        (by decide) hg)]; exact hb) (fun u h => h) fun u ⟨w, h⟩ => ⟨w, u.memory, ⟨h.1, rfl⟩, h.2⟩

/-- What the groups' checks read: the count, whether one is reserved, whether one is known, the known ones' places. -/
def GFacts (A : Word) (gs G : List Bytes) (m : Word → Word) : Prop :=
  m (at_ A ArticleProg.xGCount) = BitVec.ofNat 64 G.length ∧ m (at_ A ArticleProg.xGRes) = bw
    (G.any ArticleSpec.reserved) ∧
    m (at_ A ArticleProg.xGKnown) = bw (G.any (gs.contains ·)) ∧ (G.any (gs.contains ·) = true → KnownAt A gs
      (Kf gs G) m)

theorem groupsOf_find {fs : List Field} {f : Field} (h : ArticleSpec.find? fs "Newsgroups" = some f) :
    groupsOf fs = ArticleSpec.listed f.value := by unfold groupsOf; rw [h]; rfl

theorem groupsOf_none {fs : List Field} (h : ArticleSpec.find? fs "Newsgroups" = none) : groupsOf fs = [] := by
  unfold groupsOf; rw [h]; rfl

theorem gw_ne0 {i : Nat} (hi : i < 32) : (ArticleProg.w i == 0) = false := by
  simp only [ArticleProg.w, X_val]; exact beq_false_of_ne (by omega)

/-- The groups counted. -/
def tGroups : List Syntax.PStmt :=
  [ArticleProg.setW ArticleProg.xGCount (Syntax.n 0), ArticleProg.setW ArticleProg.xGRes (Syntax.n 0),
    ArticleProg.setW ArticleProg.xGKnown (Syntax.n 0)] ++
  guardS (ifs (Syntax.eLe (Syntax.n 0) (ArticleProg.firstOf esP "Newsgroups"))
    (fieldS "Newsgroups" "np" "nf" "nn" "ns" "ne" ++ [.call "gr" "artGroups" [Syntax.v "ns", Syntax.v "ne"]]))

theorem groupsB_low : LowKK (fieldG "Newsgroups" "np" "nf" "nn" "ns" "ne" ++
    guardS (.call "gr" "artGroups" [Syntax.v "ns", Syntax.v "ne"])) :=
  lowKK_append (fieldG_low _ _ _ _ _ _) (lowK_any _ (k := .skip) rfl)

theorem tGroups_low : LowKK tGroups := by
  unfold tGroups
  rw [DN.News.ArticleAdded.guardS_ifs]
  exact lowKK_append (lowK_any _ (k := .skip) rfl) (lowKK_ite (DN.News.ArticleAdded.flag_lower esP "Newsgroups")
    groupsB_low fun k => ⟨k, rfl⟩)

/-- **The article's groups counted**: how many, whether one is reserved or known, the known ones' places. -/
theorem groups_step (o : Oracle σ) {R : Ret} {A : Word} {s1 : PancakeState σ} (hA : Area ArticleProg.ofs A s1)
    (hD : ArtDom A s1.memaddrs) (hcode : ArtCode s1.code) {m0 : Word → Word} {a : Bytes} (hlen : a.length ≤ artMax)
    {SEP : Nat} (hB : ChkBase s1 A m0 SEP esP) {L : List (Nat × Nat)} (hL : Lines a 0 L SEP)
    (hok : L.any (DN.News.ArticleLines.malLine a) = false) {l : List (String × Value)}
    (hla : l.lookup "a" = some A) (hfr : ∀ y, y ∈ ["np", "nf", "nn", "ns", "ne", "gr"] → Fresh y l = true)
    {ctx : ArticleSpec.Context} (hGr : GroupsAt A s1.memaddrs s1.be ctx.groups m0) :
    FragR o R tGroups
      (RunF s1 l (ChkT s1 A m0 a (groups a L)))
      (RunF s1 l (fun m => ChkT s1 A m0 a (groups a L) m ∧
        GFacts A ctx.groups (groupsOf ((groups a L).map (fieldOf a))) m)) := by
  have hA8 := hA.hA
  have hn : "Newsgroups" ∈ allNames := by simp [allNames, ArticleProg.readNames]
  have hM := artMax_eq
  let Z : (Word → Word) → Prop := fun m => ChkT s1 A m0 a (groups a L) m ∧
    m (at_ A ArticleProg.xGCount) = 0 ∧ m (at_ A ArticleProg.xGRes) = 0 ∧ m (at_ A ArticleProg.xGKnown) = 0
  have hgw : ∀ y, gWrites y → gScratch A (at_ A y) := fun y hy => .inr ⟨y, hy, rfl⟩
  unfold tGroups
  refine fragR_append (xs := [_, _, _]) (M := RunF s1 l Z) (runF_pin o (lowK_any _ (k := .skip) rfl) fun M hM => ?_) ?_
  · refine fragR_of (frag_conseq (frag_append (xs := [_]) (DN.News.ArticleTables.setC_frag o hla (gw_ne0 (by decide))
      (artDom_w hD (i := 26) (by decide))) (frag_append (xs := [_]) (DN.News.ArticleTables.setC_frag o hla
      (gw_ne0 (by decide)) (artDom_w hD (i := 27) (by decide))) (DN.News.ArticleTables.setC_frag o hla
      (gw_ne0 (by decide)) (artDom_w hD (i := 28) (by decide))))) (fun _ h => h) fun u h => ?_)
    refine runF_mono h (fun q hq => hq) fun m hm => ?_
    subst hm
    have h26 := DN.News.ArticleRun.w_ne (A := A) (i := 26) (j := 27) (by decide) (by decide) (by decide)
    have h27 := DN.News.ArticleRun.w_ne (A := A) (i := 27) (j := 28) (by decide) (by decide) (by decide)
    have h28 := DN.News.ArticleRun.w_ne (A := A) (i := 26) (j := 28) (by decide) (by decide) (by decide)
    refine ⟨chkT_mid hA8 hlen hM (S := fun x => x = at_ A ArticleProg.xGCount ∨ x = at_ A ArticleProg.xGRes ∨
      x = at_ A ArticleProg.xGKnown) (fun x hx => g_at (by rcases hx with rfl | rfl | rfl <;> exact hgw _ (by
        simp [gWrites]))) (fun x hx => .inr (by rcases hx with rfl | rfl | rfl <;> exact hgw _ (by simp [gWrites])))
      (fun x hx => ?_), ?_, ?_, upd_eq _ _ _⟩
    · simp only [not_or] at hx
      rw [upd_ne _ hx.2.2, upd_ne _ hx.2.1, upd_ne _ hx.1]
    · exact (upd_ne _ h28).trans ((upd_ne _ h26).trans (upd_eq _ _ _))
    · exact (upd_ne _ h27).trans (upd_eq _ _ _)
  rw [DN.News.ArticleAdded.guardS_ifs]
  have h63 : ∀ x, DN.News.ArticleAdded.firstP a L "Newsgroups" = some x → x < 2 ^ 63 := fun x hx => by
    have := DN.News.ArticleAdded.firstP_lt hL hok x hx; omega
  refine fragR_if o (DN.News.ArticleAdded.flag_lower esP "Newsgroups") groupsB_low (lowK_any _ (k := .skip) rfl)
    (runF_clock _ _ _) (fun u y w h hy => runF_restore h (hfr y (by
      simpa [fieldG, declared, guardS, guardL, ifs] using hy)) w) (fun _ _ _ _ hy => nomatch hy)
    (b := (DN.News.ArticleAdded.firstP a L "Newsgroups").isSome)
    (fun u h => DN.News.ArticleAdded.flag_eval h63 (firstE_eval hB hla (runF_mono h (fun q hq => hq) fun _ hm => hm.1)
      hn))
    (fun hs => ?_) fun hs => ?_
  · obtain ⟨P, hP⟩ := Option.isSome_iff_exists.1 hs
    obtain ⟨e, more, hf, hfind, hval, hSE, hE⟩ := first_field hL hok hP
    have hfrs : ∀ y, y ∈ ["np", "nf", "nn", "ns", "ne", "gr"] → Fresh y l = true := hfr
    refine fragR_conseq (P0 := RunF s1 l (ChkT s1 A m0 a (groups a L))) ?_
      (fun u h => runF_mono h (fun q hq => hq) fun _ hm => hm.1) fun _ h => h
    refine fragR_append (field_frag o hA hD hcode hlen hB hla hn hP hf (xp := "np") (xf := "nf") (xn := "nn")
      (xs := "ns") (xe := "ne") (by decide) (hfrs _ (by simp)) (hfrs _ (by simp)) (hfrs _ (by simp))
      (hfrs _ (by simp)) (hfrs _ (by simp)) (fun _ => hla) (fun _ _ _ => ⟨rfl, rfl⟩) (fun _ _ _ _ => rfl)) ?_
    refine runF_pin o (lowK_any _ (k := .skip) rfl) fun M hM => ?_
    refine fragR_conseq (groupsCall_frag o hA hD hcode hlen (rt := "gr") (by decide) ?_ ?_ (chkT_broken hM hB.broken)
      (groupsAt_T hA.hA hM hGr) hM.reads.input hSE hE (e1 := Syntax.v "ns") (e2 := Syntax.v "ne") rfl rfl
      (fun u h => ev_var (vals_lookup h.1.vals rfl)) (fun u h => ev_var (vals_lookup h.1.vals rfl))) (fun _ h => h)
      fun u ⟨w, m, h, hfrm, hc, hr, hk, hK⟩ => runF_mono h (fun q hq => by simp [hq]) fun m' hm' => ?_
    · exact hla
    · exact hfrs _ (by simp)
    subst hm'
    have hgo : groupsOf ((groups a L).map (fieldOf a)) = ArticleSpec.listed (seg a (P +
        DN.News.ArticleLines.nameLen a P e + 1) (DN.News.ArticleLines.nextOf a more SEP - 2)) := by
      rw [groupsOf_find hfind, hval]
    refine ⟨chkT_mid hA.hA hlen hM (S := gScratch A) (fun _ h => g_at h) (fun _ h => .inr h) hfrm, ?_⟩
    rw [hgo]
    exact ⟨hc, hr, hk, fun _ => hK⟩
  · have hnone : DN.News.ArticleAdded.firstP a L "Newsgroups" = none := by simpa using hs
    have hgo : groupsOf ((groups a L).map (fieldOf a)) = [] := by
      refine groupsOf_none ?_
      rw [DN.News.ArticleAdded.find_fields]
      unfold DN.News.ArticleAdded.firstP at hnone
      cases hg : DN.News.ArticleAdded.firstG a L "Newsgroups" with
      | none => rfl
      | some g => rw [hg] at hnone; nomatch hnone
    refine fragR_of (frag_nil o fun u h => runF_mono h (fun q hq => hq) fun m ⟨hT, h1, h2, h3⟩ => ⟨hT, ?_⟩)
    rw [hgo]
    exact ⟨h1, h2, h3, fun h => nomatch h⟩

/-! ## The header section added -/

theorem chkT_w {s1 : PancakeState σ} {A : Word} {m0 : Word → Word} {a : Bytes} {gs : List (List (Nat × Nat))}
    {M : Word → Word} (h : ChkT s1 A m0 a gs M) {i : Nat} (hi : i < 14) :
    M (at_ A (ArticleProg.w i)) = m0 (at_ A (ArticleProg.w i)) :=
  h.frame _ (DN.News.ArticleFields.not_chk_w (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega)) (not_g_w (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega))

/-- **The context kept** in the checks after the fields. -/
theorem ctxAt_T {s1 : PancakeState σ} {A : Word} (hA8 : A.toNat % 8 = 0) {m0 : Word → Word} {a : Bytes}
    {gs : List (List (Nat × Nat))} {M : Word → Word} (h : ChkT s1 A m0 a gs M) {dm : Word → Bool} {be : Bool}
    {ctx : ArticleSpec.Context} (hc : DN.News.ArticleAdded.CtxAt A dm be ctx m0) :
    DN.News.ArticleAdded.CtxAt A dm be ctx M := by
  exact ctxAt_keep hA8 (fun i _ h7 => chkT_w h (by omega)) (fun y h1 h2 => h.frame _ (groups_free h1 h2).1
    (groups_free h1 h2).2) hc

/-! ## The bounds `artAdded` needs -/

theorem flat_len : ∀ (l : List Bytes),
    ((l.map (· ++ DN.News.CommandSpec.crlf)).flatten).length = (l.map List.length).sum + 2 * l.length
  | [] => rfl
  | x :: l => by
    simp only [List.map_cons, List.flatten_cons, List.length_append, flat_len l, List.sum_cons, List.length_cons]
    have : DN.News.CommandSpec.crlf.length = 2 := rfl
    omega

theorem text_len (f : Field) : f.text.length = (f.lines.map List.length).sum + 2 * f.lines.length := flat_len _

theorem head_len (ctx : ArticleSpec.Context) :
    (DN.News.CommandSpec.ascii "Path: " ++ ctx.identity ++ DN.News.CommandSpec.ascii "!.POSTED").length =
      14 + ctx.identity.length := by
  simp only [List.length_append, DN.News.ArticleOut.ascii_length]
  have : "Path: ".length = 6 := rfl; have : "!.POSTED".length = 8 := rfl; omega

/-- **Path as added**: at most the old field's and the identity's lengths, and 33. -/
theorem pathField_le (ctx : ArticleSpec.Context) (old : Option Field) :
    (ArticleSpec.pathField ArticleSpec.spec ctx old).length ≤
      (old.map (·.text.length)).getD 0 + ctx.identity.length + 33 := by
  have hh := head_len ctx
  have hc : DN.News.CommandSpec.crlf.length = 2 := rfl
  unfold ArticleSpec.pathField
  split
  · rename_i first more hb
    cases old with
    | none => nomatch hb
    | some f =>
      simp only [Option.map_some] at hb ⊢
      have hb' := Option.some.inj hb
      unfold ArticleSpec.Field.body at hb'
      cases hl : f.lines with
      | nil => rw [hl] at hb'; nomatch hb'
      | cons l0 tail =>
        rw [hl] at hb'
        simp only [List.cons.injEq] at hb'
        obtain ⟨h1, h2⟩ := hb'
        subst h1 h2
        have ht := text_len f
        rw [hl] at ht
        simp only [List.map_cons, List.sum_cons, List.length_cons] at ht
        have hd : (List.dropWhile DN.News.CommandSpec.isWS (l0.drop (f.name.length + 1))).length ≤ l0.length := by
          have := (List.dropWhile_sublist (p := DN.News.CommandSpec.isWS) (l := l0.drop (f.name.length + 1))).length_le
          simp only [List.length_drop] at this; omega
        rw [flat_len]
        simp only [List.map_append, List.sum_append, List.length_append, Option.getD_some]
        split
        · simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons, List.length_nil,
            List.length_append, hh]
          have : [ArticleSpec.BANG].length = 1 := rfl
          omega
        · simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons, List.length_nil,
            List.length_append, hh, DN.News.ArticleOut.ascii_length]
          have : " !".length = 2 := rfl
          omega
  · simp only [List.length_append, DN.News.ArticleOut.ascii_length, hh]
    have : "!not-for-mail".length = 13 := rfl
    cases old <;> simp <;> omega

theorem filter_sum_le {α : Type} (f : α → Nat) (q : α → Bool) :
    ∀ (l : List α), ((l.filter q).map f).sum ≤ (l.map f).sum
  | [] => Nat.le_refl _
  | x :: l => by
    have := filter_sum_le f q l
    rw [List.filter_cons]; split <;> simp only [List.map_cons, List.sum_cons] <;> omega

theorem filter_sum_out {α : Type} (f : α → Nat) (q : α → Bool) :
    ∀ (l : List α) (x : α), x ∈ l → q x = false → ((l.filter q).map f).sum + f x ≤ (l.map f).sum
  | [], _, h, _ => nomatch h
  | y :: l, x, h, hq => by
    rcases List.mem_cons.1 h with rfl | h
    · rw [List.filter_cons, if_neg (by simp [hq])]
      have := filter_sum_le f q l
      simp only [List.map_cons, List.sum_cons]; omega
    · have := filter_sum_out f q l x h hq
      rw [List.filter_cons]; split <;> simp only [List.map_cons, List.sum_cons] <;> omega

/-- **The header section added** is at most the fields' and three identities' lengths, and 281. -/
theorem header_le (ctx : ArticleSpec.Context) (fs : List Field) (hr : ctx.random.length ≤ 16) (hs : ctx.seq < 2 ^ 64)
    (hrun : ctx.run < 2 ^ 64) (hcn : ctx.conn < 2 ^ 64) (hw : ctx.wall < 2 ^ 40) :
    (ArticleSpec.added ArticleSpec.spec ctx fs).header.length ≤
      (fs.map (·.text.length)).sum + 3 * ctx.identity.length + 281 := by
  have hc : DN.News.CommandSpec.crlf.length = 2 := rfl
  have hf : (ArticleSpec.formatDate ctx.wall).length ≤ 47 := by
    rw [DN.News.ArticleOut.formatDate_length hw]
    have := DN.News.Calendar.civilFrom_range (ctx.wall / 86400) (by omega)
    have := DN.News.ArticleAdded.decimal_le20 _ (show (ArticleSpec.civilFromDays (ctx.wall / 86400)).1 < 2 ^ 64
      by omega)
    omega
  have hd1 := DN.News.ArticleAdded.decimal_le20 _ hs
  have hd2 := DN.News.ArticleAdded.decimal_le20 _ hrun
  have hd3 := DN.News.ArticleAdded.decimal_le20 _ hcn
  have hp := pathField_le ctx (ArticleSpec.find? fs "Path")
  let q : Field → Bool := fun f => !ArticleSpec.named f.name "Path" &&
    !(ArticleSpec.spec.replace && (ArticleSpec.named f.name "Message-ID" || ArticleSpec.named f.name "Date"))
  have hk : (((fs.filter (fun f => !ArticleSpec.named f.name "Path" &&
      !(ArticleSpec.spec.replace && (ArticleSpec.named f.name "Message-ID" || ArticleSpec.named f.name "Date")))).map
        (·.text)).flatten).length + (((ArticleSpec.find? fs "Path").map (·.text.length)).getD 0)
      ≤ (fs.map (·.text.length)).sum := by
    rw [List.length_flatten, List.map_map]
    cases hfd : ArticleSpec.find? fs "Path" with
    | none => exact filter_sum_le _ q fs
    | some f =>
      have hm := List.mem_of_find?_eq_some hfd
      have hn := List.find?_some hfd
      exact filter_sum_out (fun f : Field => f.text.length) q fs f hm (by simp [q, hn])
  unfold ArticleSpec.added
  simp only [List.length_append, DN.News.ArticleOut.ascii_length]
  have h1 : "Message-ID: ".length = 12 := rfl
  have h2 : "Date: ".length = 6 := rfl
  have h3 : "Injection-Info: ".length = 16 := rfl
  have h4 : "; logging-data=".length = 15 := rfl
  have h5 : "Injection-Date: ".length = 16 := rfl
  have h6 : ".".length = 1 := rfl
  have hg : (ArticleSpec.generatedId ctx).length ≤ ctx.identity.length + 40 := by
    unfold ArticleSpec.generatedId
    simp only [List.length_append, DN.News.ArticleOut.ascii_length]
    have : "<".length = 1 := rfl; have : ".".length = 1 := rfl; have : "@".length = 1 := rfl
    have : ">".length = 1 := rfl
    omega
  split <;> split <;> split <;> simp only [List.length_append, DN.News.ArticleOut.ascii_length, List.length_nil] <;>
    omega

/-- **The fields' texts make up the header section** up to the empty line. -/
theorem texts_len {a : Bytes} {SEP : Nat} : ∀ (n : Nat) (L : List (Nat × Nat)) (s : Nat), L.length ≤ n →
    Lines a s L SEP → (∀ q r, L = q :: r → cont a q = false) →
    ((groups a L).map (fun g => (fieldOf a g).text.length)).sum = SEP - s
  | _, [], s, _, hL, _ => by
    cases hL with
    | sep => rw [show groups a [] = [] by rw [groups]]; simp
  | 0, _ :: _, _, hn, _, _ => absurd hn (by simp)
  | n + 1, (q1, q2) :: more, s, hn, hL, _ => by
    have h1 := (DN.News.ArticleLines.lines_tail hL).1
    simp only at h1
    subst h1
    have hmore := (DN.News.ArticleLines.lines_tail hL).2
    have hnext := DN.News.ArticleAdded.lines_next more (q2 + 2) hmore
    have hNXs := DN.News.ArticleLines.lines_sep hnext
    have hNXg := (DN.News.ArticleLines.nextOf_ge hmore).1
    have hmem := DN.News.ArticleLines.lines_mem hL (q1, q2) List.mem_cons_self
    rw [DN.News.ArticleAdded.groups_cons, List.map_cons, List.sum_cons, DN.News.ArticleAdded.fieldText hL,
      DN.News.ArticleLines.seg_length a (by omega) (by omega),
      texts_len n _ _ (by have := (List.dropWhile_sublist (p := cont a) (l := more)).length_le; simp only
                           [List.length_cons, Nat.add_le_add_iff_right] at hn; omega) hnext
        (fun q r h => DN.News.ArticleAdded.dropWhile_head _ _ q r h)]
    omega

/-- **The message identifier** is shorter than its area, when none is too long. -/
theorem mid_lt (ctx : ArticleSpec.Context) (fs : List Field) (hid : ctx.identity.length ≤ 200)
    (hr : ctx.random.length ≤ 16) (hs : ctx.seq < 2 ^ 64)
    (hlong : fs.find? (fun f => ArticleSpec.isOne ArticleSpec.idFields f &&
      (ArticleSpec.msgIds f.value).any (·.length > ArticleSpec.spec.idMax)) = none) :
    (ArticleSpec.added ArticleSpec.spec ctx fs).messageId.length < ArticleProg.msgCap := by
  have hmc : ArticleProg.msgCap = 256 := rfl
  have hd1 := DN.News.ArticleAdded.decimal_le20 _ hs
  unfold ArticleSpec.added
  simp only
  split
  · unfold ArticleSpec.generatedId
    simp only [List.length_append, DN.News.ArticleOut.ascii_length]
    have : "<".length = 1 := rfl; have : ".".length = 1 := rfl; have : "@".length = 1 := rfl
    have : ">".length = 1 := rfl
    omega
  · cases hf : ArticleSpec.find? fs "Message-ID" with
    | none => simp only [Option.map_none, Option.getD_none, List.headD_eq_head?_getD, List.head?_nil, List.length_nil,
               gt_iff_lt]; omega
    | some f =>
      have hm := List.mem_of_find?_eq_some hf
      have hn := List.find?_some hf
      have hno := List.find?_eq_none.1 hlong f hm
      have hone : ArticleSpec.isOne ArticleSpec.idFields f = true := by
        unfold ArticleSpec.isOne; exact List.any_eq_true.2 ⟨"Message-ID", by decide, hn⟩
      rw [hone, Bool.true_and] at hno
      have hall : ∀ x ∈ ArticleSpec.msgIds f.value, x.length ≤ 250 := fun x hx => by
        have h' : ∀ x, x ∈ ArticleSpec.msgIds f.value → x.length ≤ ArticleSpec.spec.idMax := by simpa using hno
        exact h' x hx
      simp only [Option.map_some, Option.getD_some]
      cases hl : ArticleSpec.msgIds f.value with
      | nil => simp only [List.headD_eq_head?_getD, List.head?_nil, Option.getD_none, List.length_nil, gt_iff_lt]; omega
      | cons x xs =>
        have := hall x (by rw [hl]; exact List.mem_cons_self)
        simp only [List.headD_cons]; omega

/-! ## The article accepted -/

theorem mem_artAdded : gd (ArticleProg.artAdded ArticleSpec.spec esP .none) ∈
    ArticleProg.functions ArticleSpec.spec esP .none :=
  List.mem_append_right _ (List.mem_map.2 ⟨ArticleProg.artAdded ArticleSpec.spec esP .none, by simp, rfl⟩)

/-- **A call of `artAdded`**: the header section and message identifier written. -/
theorem addedCall_frag (o : Oracle σ) {R : Ret} {A : Word} {s0 : PancakeState σ} (hA : Area ArticleProg.ofs A s0)
    (hD : ArtDom A s0.memaddrs) (hcode : ArtCode s0.code) (hT : TabDom A s0.memaddrs esP) {rt : String}
    (hra : rt ≠ "a") {l : List (String × Value)} (hla : l.lookup "a" = some A) (hrt : Fresh rt l = true)
    {m0 : Word → Word} (htab : TablesAt A s0.memaddrs s0.be m0 esP) (hP : Pows m0 A) (hb : m0 (at_ A aBroken) = 0)
    {ctx : ArticleSpec.Context} (hctx : DN.News.ArticleAdded.CtxAt A s0.memaddrs s0.be ctx m0) {a : Bytes}
    (hlen : a.length ≤ artMax) (hin : InputAt m0 s0.memaddrs s0.be A a) {SEP : Nat}
    (hsep : m0 (at_ A ArticleProg.xSep) = BitVec.ofNat 64 SEP) {L : List (Nat × Nat)} (hL : Lines a 0 L SEP)
    (hok : L.any (DN.News.ArticleLines.malLine a) = false) (hf1 : DN.News.ArticleAdded.FirstW A m0 a L "Path")
    (hf2 : DN.News.ArticleAdded.FirstW A m0 a L "Message-ID") (hf3 : DN.News.ArticleAdded.FirstW A m0 a L "Date")
    (hf4 : DN.News.ArticleAdded.FirstW A m0 a L "Injection-Date")
    (hfit : (ArticleSpec.added ArticleSpec.spec ctx ((groups a L).map (fieldOf a))).header.length ≤ ArticleProg.outMax)
    (hmidl : (ArticleSpec.added ArticleSpec.spec ctx ((groups a L).map (fieldOf a))).messageId.length <
      ArticleProg.msgCap) :
    FragR o R (guardS (.call rt "artAdded" [])) (RunF s0 l (· = m0))
      (fun u => ∃ w m, RunF s0 ((rt, w) :: l) (· = m) u ∧ DN.News.ArticleAdded.AddRet A s0.memaddrs s0.be
        (ArticleSpec.added ArticleSpec.spec ctx ((groups a L).map (fieldOf a))).header
        (ArticleSpec.added ArticleSpec.spec ctx ((groups a L).map (fieldOf a))).messageId m0 w m) := by
  refine fragR_conseq (gcall_frag o hA hcode hra (f := ArticleProg.artAdded ArticleSpec.spec esP .none) mem_artAdded
    (by decide) (F := (· = m0)) (args := []) rfl hla (vs := []) rfl (fun _ _ => rfl)
    (Rf := DN.News.ArticleAdded.AddRet A s0.memaddrs s0.be
      (ArticleSpec.added ArticleSpec.spec ctx ((groups a L).map (fieldOf a))).header
      (ArticleSpec.added ArticleSpec.spec ctx ((groups a L).map (fieldOf a))).messageId)
    (fun s1 hA1 hc hm hbe _ hF => by
      have := DN.News.ArticleAdded.artAdded_ok o hA1 (by rw [hm]; exact hD) (by rw [hc]; exact hcode)
        (by rw [hm]; exact hT) (by rw [hF, hm, hbe]; exact htab) DN.News.ArticleFields.esP_short esP_size
        (by rw [hF]; exact hP) (by rw [hF]; exact hb) (by rw [hF, hm, hbe]; exact hctx) hlen
        (by rw [hF, hm, hbe]; exact hin) (by rw [hF]; exact hsep) hL hok (by rw [hF]; exact hf1)
        (by rw [hF]; exact hf2) (by rw [hF]; exact hf3) (by rw [hF]; exact hf4) hfit hmidl
      rw [hm, hbe] at this; exact this) hrt
    (G := DN.News.ArticleAdded.AddRet A s0.memaddrs s0.be
      (ArticleSpec.added ArticleSpec.spec ctx ((groups a L).map (fieldOf a))).header
      (ArticleSpec.added ArticleSpec.spec ctx ((groups a L).map (fieldOf a))).messageId m0)
    (fun m m' w hm hr => by subst hm; exact hr) fun w m h => by
      rw [h.2.1 _ DN.News.ArticleAdded.broken_add]; exact hb) (fun u h => h)
    fun u ⟨w, h⟩ => ⟨w, u.memory, ⟨h.1, rfl⟩, h.2⟩

/-- **The groups' checks and the article accepted**: 21, 22 or 23 given back, else `artAdded`'s header and 0. -/
theorem tail_end (o : Oracle σ) {R : Ret} {A : Word} {s1 : PancakeState σ} (hA : Area ArticleProg.ofs A s1)
    (hD : ArtDom A s1.memaddrs) (hcode : ArtCode s1.code) {m0 : Word → Word} {a : Bytes} (hlen : a.length ≤ artMax)
    {SEP : Nat} (hB : ChkBase s1 A m0 SEP esP) {L : List (Nat × Nat)} (hL : Lines a 0 L SEP)
    (hok : L.any (DN.News.ArticleLines.malLine a) = false) {l : List (String × Value)}
    (hla : l.lookup "a" = some A) (had : Fresh "ad" l = true) {ctx : ArticleSpec.Context}
    (hctx : DN.News.ArticleAdded.CtxAt A s1.memaddrs s1.be ctx m0)
    (hG63 : (groupsOf ((groups a L).map (fieldOf a))).length < 2 ^ 63)
    (hfit : (ArticleSpec.added ArticleSpec.spec ctx ((groups a L).map (fieldOf a))).header.length ≤ ArticleProg.outMax)
    (hmidl : (ArticleSpec.added ArticleSpec.spec ctx ((groups a L).map (fieldOf a))).messageId.length <
      ArticleProg.msgCap)
    (h21 : 16 < (groupsOf ((groups a L).map (fieldOf a))).length → ∀ M, ChkT s1 A m0 a (groups a L) M →
      R (BitVec.ofNat 64 21) M)
    (h22 : ¬16 < (groupsOf ((groups a L).map (fieldOf a))).length →
      (groupsOf ((groups a L).map (fieldOf a))).any ArticleSpec.reserved = true → ∀ M, ChkT s1 A m0 a (groups a L) M →
      R (BitVec.ofNat 64 22) M)
    (h23 : ¬16 < (groupsOf ((groups a L).map (fieldOf a))).length →
      (groupsOf ((groups a L).map (fieldOf a))).any ArticleSpec.reserved = false →
      (groupsOf ((groups a L).map (fieldOf a))).any (ctx.groups.contains ·) = false →
      ∀ M, ChkT s1 A m0 a (groups a L) M → R (BitVec.ofNat 64 23) M)
    (h0 : ¬16 < (groupsOf ((groups a L).map (fieldOf a))).length →
      (groupsOf ((groups a L).map (fieldOf a))).any ArticleSpec.reserved = false →
      (groupsOf ((groups a L).map (fieldOf a))).any (ctx.groups.contains ·) = true →
      ∀ M, ChkT s1 A m0 a (groups a L) M → GFacts A ctx.groups (groupsOf ((groups a L).map (fieldOf a))) M →
      ∀ w m, DN.News.ArticleAdded.AddRet A s1.memaddrs s1.be
        (ArticleSpec.added ArticleSpec.spec ctx ((groups a L).map (fieldOf a))).header
        (ArticleSpec.added ArticleSpec.spec ctx ((groups a L).map (fieldOf a))).messageId M w m → R 0 m) :
    FragR o R ([ifs (Syntax.eLt (Syntax.n ArticleSpec.spec.groupsMax) (wd ArticleProg.xGCount)) [.ret (Syntax.n 21)],
        ifs (wd ArticleProg.xGRes) [.ret (Syntax.n 22)],
        ifs (Syntax.eEq (wd ArticleProg.xGKnown) (Syntax.n 0)) [.ret (Syntax.n 23)]] ++
        guardS (.call "ad" "artAdded" []) ++ [.ret (Syntax.n 0)])
      (RunF s1 l (fun m => ChkT s1 A m0 a (groups a L) m ∧
        GFacts A ctx.groups (groupsOf ((groups a L).map (fieldOf a))) m)) (fun _ => False) := by
  let G := groupsOf ((groups a L).map (fieldOf a))
  have hA8 := hA.hA
  have hrd : ∀ (l' : List (String × Value)), l'.lookup "a" = some A → ∀ u M, RunF s1 l' (· = M) u → ∀ i, i < 32 →
      eval u (.loadWord (.op .add (.var "a") (.const (BitVec.ofNat 64 (ArticleProg.w i))))) =
        some (M (at_ A (ArticleProg.w i))) := fun l' hl u M h i hi => by
    rw [loadA_eval h.1.memaddrs (artDom_w hD hi) (atA_eval (vals_lookup h.1.vals hl)), h.2]
  refine runF_pin o (lowK_any _ (k := .skip) rfl) fun M ⟨hM, hc, hr, hk, hK⟩ => ?_
  have hlow3 : LowKK ([ifs (wd ArticleProg.xGRes) [.ret (Syntax.n 22)],
      ifs (Syntax.eEq (wd ArticleProg.xGKnown) (Syntax.n 0)) [.ret (Syntax.n 23)]] ++
      guardS (.call "ad" "artAdded" []) ++ [.ret (Syntax.n 0)]) := lowK_any _ (k := .skip) rfl
  by_cases g1 : 16 < G.length
  · refine fragR_append (xs := [_]) (fragR_if o rfl (lowKK_ret rfl) (fun k => ⟨k, rfl⟩) (Q := fun _ => False)
      (fun _ _ h => h) (fun _ _ _ h _ => h) (fun _ _ _ h _ => h) (b := true)
      (fun u h => by
        refine (DN.News.FramerCode.eval_lt (b := .loadWord (.op .add (.var "a")
          (.const (BitVec.ofNat 64 ArticleProg.xGCount)))) (x := 16) (y := G.length) (by decide) hG63 rfl
          ((hrd _ hla u M h 26 (by decide)).trans (congrArg some hc))).trans ?_
        rw [decide_eq_true g1]; rfl)
      (fun _ => fragR_ret o rfl fun u h => ⟨_, rfl, by rw [h.2]; exact h21 g1 M hM⟩) fun h => nomatch h) ?_
    exact fragR_of (frag_unsat hlow3 fun _ h => h.elim)
  refine fragR_append (xs := [_]) (fragR_if o rfl (lowKK_ret rfl) (fun k => ⟨k, rfl⟩) (runF_clock _ _ _)
    (fun _ _ _ _ hy => nomatch hy) (fun _ _ _ _ hy => nomatch hy) (b := false)
    (fun u h => by
      refine (DN.News.FramerCode.eval_lt (b := .loadWord (.op .add (.var "a")
        (.const (BitVec.ofNat 64 ArticleProg.xGCount)))) (x := 16) (y := G.length) (by decide) hG63 rfl
        ((hrd _ hla u M h 26 (by decide)).trans (congrArg some hc))).trans ?_
      rw [decide_eq_false g1]; rfl)
    (fun h => nomatch h) fun _ => fragR_of (frag_nil o fun _ h => h)) ?_
  have hhi : ∀ y, ArticleProg.xFlags esP ≤ y → y < 2 ^ 40 → M (at_ A y) = m0 (at_ A y) := fun y h1 h2 => by
    have hl := (DN.News.ArticleTables.lay esP).1
    have hF := xFirst_eq
    exact hM.frame _ (DN.News.ArticleFields.not_chk (.inr (hl ▸ h1)) h2 (by have : aLen = 8 := rfl; omega))
      (not_g (.inr (by omega)) h2)
  have hlow4 : LowKK ([ifs (Syntax.eEq (wd ArticleProg.xGKnown) (Syntax.n 0)) [.ret (Syntax.n 23)]] ++
      guardS (.call "ad" "artAdded" []) ++ [.ret (Syntax.n 0)]) := lowK_any _ (k := .skip) rfl
  by_cases g2 : G.any ArticleSpec.reserved = true
  · refine fragR_append (xs := [_]) (fragR_if o rfl (lowKK_ret rfl) (fun k => ⟨k, rfl⟩) (Q := fun _ => False)
      (fun _ _ h => h) (fun _ _ _ h _ => h) (fun _ _ _ h _ => h) (b := true)
      (fun u h => (hrd _ hla u M h 27 (by decide)).trans (by rw [show ArticleProg.w 27 = ArticleProg.xGRes from rfl, hr,
                                                              g2]; rfl))
      (fun _ => fragR_ret o rfl fun u h => ⟨_, rfl, by rw [h.2]; exact h22 g1 g2 M hM⟩) fun h => nomatch h) ?_
    exact fragR_of (frag_unsat hlow4 fun _ h => h.elim)
  have g2' : G.any ArticleSpec.reserved = false := by simpa using g2
  refine fragR_append (xs := [_]) (fragR_if o rfl (lowKK_ret rfl) (fun k => ⟨k, rfl⟩) (runF_clock _ _ _)
    (fun _ _ _ _ hy => nomatch hy) (fun _ _ _ _ hy => nomatch hy) (b := false)
    (fun u h => (hrd _ hla u M h 27 (by decide)).trans (by rw [show ArticleProg.w 27 = ArticleProg.xGRes from rfl, hr,
                                                            g2']; rfl))
    (fun h => nomatch h) fun _ => fragR_of (frag_nil o fun _ h => h)) ?_
  have hkv : M (at_ A ArticleProg.xGKnown) = BitVec.ofNat 64 (if G.any (ctx.groups.contains ·) then 1 else 0) := by
    rw [hk]; exact DN.News.ArticleRun.bw_ofNat _
  by_cases g3 : G.any (ctx.groups.contains ·) = true
  · refine fragR_append (xs := [_]) (fragR_if o rfl (lowKK_ret rfl) (fun k => ⟨k, rfl⟩) (runF_clock _ _ _)
      (fun _ _ _ _ hy => nomatch hy) (fun _ _ _ _ hy => nomatch hy) (b := false)
      (fun u h => (DN.News.FramerCode.eval_eq (by rw [g3]; decide) (by decide)
        ((hrd _ hla u M h 28 (by decide)).trans (congrArg some hkv)) rfl).trans (by rw [g3]; rfl))
      (fun h => nomatch h) fun _ => fragR_of (frag_nil o fun _ h => h)) ?_
    have hn : ∀ nm, nm ∈ ["Path", "Message-ID", "Date", "Injection-Date"] → nm ∈ allNames := fun nm hnm => by
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hnm
      rcases hnm with rfl | rfl | rfl | rfl <;> simp [allNames, ArticleProg.readNames, ArticleProg.dateFields]
    refine fragR_append (addedCall_frag o hA hD hcode hB.tdom (rt := "ad") (by decide) hla had
      (DN.News.ArticleFields.tablesAt_hi hA8 esP_size hhi hB.tabs) hM.reads.pows (chkT_broken hM hB.broken)
      (ctxAt_T hA8 hM hctx) hlen hM.reads.input (chkT_sep hM hB) hL hok (chkT_firstW hM (hn _ (by simp)))
      (chkT_firstW hM (hn _ (by simp))) (chkT_firstW hM (hn _ (by simp))) (chkT_firstW hM (hn _ (by simp))) hfit hmidl)
        ?_
    refine fragR_exists (lowKK_ret rfl) fun w => fragR_exists (lowKK_ret rfl) fun m => ?_
    refine fragR_pure _ (fun u h => h.2) (lowKK_ret rfl) fun hadd => ?_
    exact fragR_ret o rfl fun u h => ⟨_, rfl, by rw [h.1.2]; exact h0 g1 g2' g3 M hM ⟨hc, hr, hk, hK⟩ w m hadd⟩
  · have g3' : G.any (ctx.groups.contains ·) = false := by simpa using g3
    refine fragR_append (xs := [_]) (fragR_if o rfl (lowKK_ret rfl) (fun k => ⟨k, rfl⟩) (Q := fun _ => False)
      (fun _ _ h => h) (fun _ _ _ h _ => h) (fun _ _ _ h _ => h) (b := true)
      (fun u h => (DN.News.FramerCode.eval_eq (by rw [g3']; decide) (by decide)
        ((hrd _ hla u M h 28 (by decide)).trans (congrArg some hkv)) rfl).trans (by rw [g3']; rfl))
      (fun _ => fragR_ret o rfl fun u h => ⟨_, rfl, by rw [h.2]; exact h23 g1 g2' g3' M hM⟩) fun h => nomatch h) ?_
    exact fragR_of (frag_unsat (lowK_any _ (k := .skip) rfl) fun _ h => h.elim)

theorem spp_le (p : BitVec 8 → Bool) : ∀ (l acc : Bytes),
    ((List.splitOnPPrepend p l acc).filter (!·.isEmpty)).length ≤ l.length + acc.length
  | [], acc => by
    rw [DN.News.ArticleDate.spp_nil]
    cases acc with
    | nil => simp
    | cons x acc => simp
  | b :: l, acc => by
    rw [DN.News.ArticleDate.spp_cons]
    split
    · have := spp_le p l []
      cases acc with
      | nil => simp only [List.reverse_nil, List.filter_cons, List.isEmpty_nil]; simp at this ⊢; omega
      | cons x acc =>
        rw [List.filter_cons, if_pos (by simp)]
        simp only [List.length_cons, List.length_nil] at this ⊢; omega
    · have := spp_le p l (b :: acc)
      simp only [List.length_cons] at this ⊢; omega

/-- The groups an article names are at most its value's bytes. -/
theorem listed_le (v : Bytes) : (ArticleSpec.listed v).length ≤ v.length := by
  unfold ArticleSpec.listed
  generalize hw : List.filter _ v = w
  have h2 : w.length ≤ v.length := hw ▸ List.filter_sublist.length_le
  have := spp_le (· == ArticleSpec.COMMA) w []
  simp only [List.length_nil, Nat.add_zero] at this
  exact Nat.le_trans this h2

/-! ## The verdict, a check at a time -/

theorem opt_any_map {α β : Type} (o : Option α) (g : α → β) (q : β → Bool) :
    (o.map g).any q = (o.map (fun x => q (g x))).getD false := by cases o <;> rfl

theorem tail_art {ctx : ArticleSpec.Context} {fs : List Field}
    (hnf : fs.findSome? (ArticleSpec.fieldRefusal ArticleSpec.spec) = none) :
    DN.News.ArticleLines.tailOf ArticleSpec.spec ctx fs = match ArticleSpec.articleRefusal ArticleSpec.spec ctx fs with
      | some x => .refused x
      | none => .accepted (ArticleSpec.added ArticleSpec.spec ctx fs) := by
  unfold DN.News.ArticleLines.tailOf; rw [hnf]; rfl

theorem ar_rep {ctx : ArticleSpec.Context} {fs : List Field} {n : Bytes}
    (h : ArticleSpec.repeatedFrom ArticleSpec.spec fs [] = some n) :
    ArticleSpec.articleRefusal ArticleSpec.spec ctx fs = some (.repeated n) := by
  rw [articleRefusal_eq, h]

theorem ar_norep {ctx : ArticleSpec.Context} {fs : List Field}
    (h : ArticleSpec.repeatedFrom ArticleSpec.spec fs [] = none) :
    ArticleSpec.articleRefusal ArticleSpec.spec ctx fs = arMissing ctx fs := by
  rw [articleRefusal_eq, h]

theorem am_miss {ctx : ArticleSpec.Context} {fs : List Field} {nm : String}
    (h : ArticleSpec.spec.required.find? (!ArticleSpec.has fs ·) = some nm) :
    arMissing ctx fs = some (.missing (DN.News.CommandSpec.ascii nm)) := by
  unfold arMissing; rw [h]

theorem am_ok {ctx : ArticleSpec.Context} {fs : List Field}
    (h : ArticleSpec.spec.required.find? (!ArticleSpec.has fs ·) = none) : arMissing ctx fs = arPosted ctx fs := by
  unfold arMissing; rw [h]

theorem ap_eq {ctx : ArticleSpec.Context} {fs : List Field} :
    arPosted ctx fs = if ((ArticleSpec.find? fs "Path").map
        (fun f => (ArticleSpec.pathElements f.value).any ArticleSpec.isPosted)).getD false then some .posted
      else arLong ctx fs := by
  unfold arPosted; rw [opt_any_map]; rfl

theorem al_some {ctx : ArticleSpec.Context} {fs : List Field} {f : Field}
    (h : fs.find? (fun f => ArticleSpec.isOne ArticleSpec.idFields f &&
      (ArticleSpec.msgIds f.value).any (·.length > ArticleSpec.spec.idMax)) = some f) :
    arLong ctx fs = some (.longMessageId f.name) := by
  unfold arLong; rw [h]

theorem al_none {ctx : ArticleSpec.Context} {fs : List Field}
    (h : fs.find? (fun f => ArticleSpec.isOne ArticleSpec.idFields f &&
      (ArticleSpec.msgIds f.value).any (·.length > ArticleSpec.spec.idMax)) = none) :
    arLong ctx fs = arSender ctx fs := by
  unfold arLong; rw [h]

theorem as_eq {ctx : ArticleSpec.Context} {fs : List Field} :
    arSender ctx fs = if (!ArticleSpec.has fs "Sender" && ((ArticleSpec.find? fs "From").map
        (fun f => !ArticleSpec.grammarSays (ArticleSpec.ruleNamed "mailbox") f.value)).getD false) then some .noSender
      else arDist ctx fs := by
  unfold arSender; rfl

theorem ad_eq {ctx : ArticleSpec.Context} {fs : List Field} :
    arDist ctx fs = if ((ArticleSpec.find? fs "Distribution").map
        (fun f => (ArticleSpec.listed f.value).any (ArticleSpec.named · "all"))).getD false then some .distributionAll
      else arBad ctx fs := by
  unfold arDist; rfl

theorem ab_some {ctx : ArticleSpec.Context} {fs : List Field} {f : Field}
    (h : fs.find? (fun f => (ArticleSpec.dateText f).any (fun t => (ArticleSpec.dateValue t).isNone)) = some f) :
    arBad ctx fs = some (.badDate f.name) := by
  unfold arBad; rw [show ArticleSpec.spec.dates = true from rfl]; simp only [Bool.true_and]; rw [h]

theorem ab_none {ctx : ArticleSpec.Context} {fs : List Field}
    (h : fs.find? (fun f => (ArticleSpec.dateText f).any (fun t => (ArticleSpec.dateValue t).isNone)) = none) :
    arBad ctx fs = arWindows ctx fs := by
  unfold arBad; rw [show ArticleSpec.spec.dates = true from rfl]; simp only [Bool.true_and]; rw [h]

theorem aw_date {ctx : ArticleSpec.Context} {fs : List Field} {x : Refusal} (h : window ctx fs "Date" = some x) :
    arWindows ctx fs = some x := by unfold arWindows; rw [h]

theorem aw_inj {ctx : ArticleSpec.Context} {fs : List Field} {x : Refusal} (h1 : window ctx fs "Date" = none)
    (h : window ctx fs "Injection-Date" = some x) : arWindows ctx fs = some x := by unfold arWindows; rw [h1, h]

theorem aw_none {ctx : ArticleSpec.Context} {fs : List Field} (h1 : window ctx fs "Date" = none)
    (h2 : window ctx fs "Injection-Date" = none) : arWindows ctx fs = arGroups ctx fs := by
  unfold arWindows; rw [h1, h2]

/-! ## What a return leaves -/

theorem ret_refused {A : Word} {dm : Word → Bool} {be : Bool} {ctx : ArticleSpec.Context} {a : Bytes}
    {ms m : Word → Word} {x : Refusal} (hcw : ArticleSpec.checkWith ArticleSpec.spec ctx a = .refused x)
    (hb : m (at_ A aBroken) = 0) (hf : ∀ w, ¬CheckScr A w → m w = ms w) (hs : AllSets A m)
    (hn : NameAt A dm be (nameOf x) m) (hl : (nameOf x).length ≤ ArticleProg.nameCap) :
    CheckRet A dm be ctx a ms (BitVec.ofNat 64 (DN.News.ArticleFields.refNum x)) m := by
  refine ⟨hb, hf, hs, ?_⟩
  rw [hcw]; exact ⟨rfl, hn, hl⟩

theorem nameAt_empty {A : Word} {dm : Word → Bool} {be : Bool} {m : Word → Word}
    (h : m (at_ A ArticleProg.xNameLen) = 0) : NameAt A dm be [] m :=
  ⟨h, fun _ _ hi => absurd hi (Nat.not_lt_zero _)⟩

/-- **A field's name kept** by `artNameAt`. -/
theorem nameAt_mem {A : Word} (hA8 : A.toNat % 8 = 0) {dm : Word → Bool} (hD : ArtDom A dm) {be : Bool}
    {name : Bytes} (hn : name.length ≤ ArticleProg.nameCap) (K e : Nat) (M : Word → Word) :
    NameAt A dm be name (nameMem A be name K e M) := by
  have hN := xName_eq; have hc : ArticleProg.nameCap = 1024 := rfl
  have hwl : ArticleProg.xNameLen < ArticleProg.xName := by simp only [ArticleProg.xNameLen, ArticleProg.w, X_val];
                                                             omega
  refine ⟨upd_eq _ _ _, fun i hi hl => ?_⟩
  unfold nameMem memLoadByte
  rw [upd_ne _ (by
    rw [DN.News.ScanRun.align_at hA8]; exact DN.News.ScanRun.at_ne (by omega) (by omega) (by omega))]
  have := DN.News.ArticleDateOk.load_putB (m := fieldMem A K e M) (dm := dm) (be := be) (A := A)
    (x := ArticleProg.xName)
    (bs := name) (by omega) i hl (name_dom hD hA8 _ (by omega) (by omega))
  unfold memLoadByte at this
  rw [this, getElem!_pos name i hl]

/-- What `artNameAt` writes lies past the slots. -/
theorem nameMem_lo {A : Word} (hA8 : A.toNat % 8 = 0) {be : Bool} {name : Bytes}
    (hn : name.length ≤ ArticleProg.nameCap) (K e : Nat) (M : Word → Word) {y : Nat} (hy : y < ArticleProg.X) :
    nameMem A be name K e M (at_ A y) = M (at_ A y) := by
  have hN := xName_eq; have hc : ArticleProg.nameCap = 1024 := rfl; have hX := X_val
  have hw : ∀ i, i < 32 → at_ A y ≠ at_ A (ArticleProg.w i) := fun i hi =>
    DN.News.ScanRun.at_ne (by omega) (w_lt64 hi) (by simp only [ArticleProg.w, hX]; omega)
  exact (upd_ne _ (hw 11 (by decide))).trans ((DN.News.ArticleRun.putB_other _ hA8 _ _ _ _ (by omega) (by omega)).trans
    ((upd_ne _ (hw 18 (by decide))).trans (upd_ne _ (hw 17 (by decide)))))

theorem nameMem_broken {A : Word} (hA8 : A.toNat % 8 = 0) {be : Bool} {name : Bytes}
    (hn : name.length ≤ ArticleProg.nameCap) (K e : Nat) {M : Word → Word} (hb : M (at_ A aBroken) = 0) :
    nameMem A be name K e M (at_ A aBroken) = 0 :=
  (nameMem_lo hA8 hn K e M (by have := DN.News.ArticleGrammar.broken_low; have := sets_le_X; omega)).trans hb

/-- Bytes put from `x` change only the words they fall in. -/
theorem putB_word (be : Bool) {A : Word} (hA8 : A.toNat % 8 = 0) : ∀ (bs : Bytes) (m : Word → Word) (x : Nat)
    (w : Word),
    (∀ y, x ≤ y → y < x + bs.length → w ≠ at_ A (y / 8 * 8)) → putB m be A x bs w = m w
  | [], _, _, _, _ => rfl
  | b :: bs, m, x, w, h => by
    simp only [putB, List.length_cons] at h ⊢
    rw [putB_word be hA8 bs _ (x + 1) w fun y h1 h2 => h y (by omega) (by omega)]
    simp only [DN.Compiler.Bytes.putByte, DN.News.ScanRun.align_at hA8]
    rw [if_neg (h x (Nat.le_refl _) (by omega))]

/-- `artNameAt` keeps the words `artCheck` keeps. -/
theorem nameMem_frame {A : Word} (hA8 : A.toNat % 8 = 0) {be : Bool} {name : Bytes}
    (hn : name.length ≤ ArticleProg.nameCap) (K e : Nat) (M : Word → Word) {x : Word} (hx : ¬CheckScr A x) :
    nameMem A be name K e M x = M x := by
  have hN := xName_eq; have hc : ArticleProg.nameCap = 1024 := rfl
  have h11 : x ≠ at_ A ArticleProg.xNameLen := fun e => hx (.inr (.inr (.inr (.inr ⟨11, .inl rfl, e⟩))))
  have h18 : x ≠ at_ A ArticleProg.xE1 := fun e => hx (.inl (.inl (.inr (.inl e))))
  have h17 : x ≠ at_ A ArticleProg.xNl := fun e => hx (.inl (.inl (.inl e)))
  unfold nameMem fieldMem
  exact (upd_ne _ h11).trans ((putB_word be hA8 _ _ _ x fun y h1 h2 e =>
    hx (.inr (.inr (.inr (.inl ⟨y / 8 * 8, by omega, by omega, e⟩))))).trans ((upd_ne _ h18).trans (upd_ne _ h17)))

/-- **A constant name kept**. -/
theorem nameAt_const {A : Word} {dm : Word → Bool} {be : Bool} {nm : String} {M m : Word → Word}
    (h : ConstAt A dm be nm M m) : NameAt A dm be (DN.News.CommandSpec.ascii nm) m := by
  have hcl := DN.News.ArticleOut.codes_length nm
  have hal := DN.News.ArticleOut.ascii_length nm
  refine ⟨by rw [h.2.1, hal], fun i _ hl => ?_⟩
  rw [h.1 i (by omega)]
  have hl' : i < nm.toList.length := by simpa [DN.News.CommandSpec.ascii] using hl
  congr 1
  simp [DN.News.CommandSpec.ascii, ArticleProg.codes, List.getElem?_eq_getElem hl']

/-! ## `artCheck`'s checks after the fields -/

/-- The repeated field. -/
def tRep : List Syntax.PStmt :=
  guardS (ifs (Syntax.eLe (Syntax.n 0) (Syntax.v "rep")) [.call "cr" "artNameAt" [Syntax.v "rep"], .ret (Syntax.n 12)])

/-- From required. -/
def tFrom : List Syntax.PStmt :=
  guardS (ifs (Syntax.eLt (ArticleProg.firstOf esP "From") (Syntax.n 0)) (ArticleProg.constName "From" ++
    [.ret (Syntax.n 13)]))

/-- Newsgroups required. -/
def tNews : List Syntax.PStmt :=
  guardS (ifs (Syntax.eLt (ArticleProg.firstOf esP "Newsgroups") (Syntax.n 0))
    (ArticleProg.constName "Newsgroups" ++ [.ret (Syntax.n 13)]))

/-- Subject required. -/
def tSubj : List Syntax.PStmt :=
  guardS (ifs (Syntax.eLt (ArticleProg.firstOf esP "Subject") (Syntax.n 0))
    (ArticleProg.constName "Subject" ++ [.ret (Syntax.n 13)]))

/-- POSTED in Path. -/
def tPosted : List Syntax.PStmt :=
  elemS "Path" "hp" "hf" "hn" "hs" "he" "po" ArticleProg.artPosted 14

/-- The long Message-ID. -/
def tLid : List Syntax.PStmt :=
  guardS (ifs (Syntax.eLe (Syntax.n 0) (Syntax.v "lid")) [.call "cl" "artNameAt" [Syntax.v "lid"], .ret (Syntax.n 15)])

/-- Distribution all. -/
def tDist : List Syntax.PStmt :=
  elemS "Distribution" "dp" "df" "dn" "ds" "de" "da" ArticleProg.artDistAll 17

/-- The date that means none. -/
def tBd : List Syntax.PStmt :=
  guardS (ifs (Syntax.eLe (Syntax.n 0) (Syntax.v "bd")) [.call "cb" "artNameAt" [Syntax.v "bd"], .ret (Syntax.n 18)])

/-- Date's window. -/
def tDate : List Syntax.PStmt :=
  winS "Date" "wp" "wf" "wn" "ws" "we" "wv" "wt"

/-- Injection-Date's window. -/
def tInj : List Syntax.PStmt :=
  winS "Injection-Date" "xp" "xf" "xn" "xs" "xe" "xv" "xt"

/-- The groups' checks and the article accepted. -/
def tEnd : List Syntax.PStmt :=
  [ifs (Syntax.eLt (Syntax.n ArticleSpec.spec.groupsMax) (wd ArticleProg.xGCount)) [.ret (Syntax.n 21)],
        ifs (wd ArticleProg.xGRes) [.ret (Syntax.n 22)],
        ifs (Syntax.eEq (wd ArticleProg.xGKnown) (Syntax.n 0)) [.ret (Syntax.n 23)]] ++
        guardS (.call "ad" "artAdded" []) ++ [.ret (Syntax.n 0)]

/-- The checks after the fields' loop, a step at a time. -/
def tailS : List Syntax.PStmt :=
  tRep ++ (tFrom ++ (tNews ++ (tSubj ++ (tPosted ++ (tLid ++ (tSender ++ (tDist ++
    (tBd ++ (tDate ++ (tInj ++ (tGroups ++ (tEnd))))))))))))

/-! ## The steps lowered -/

theorem tRep_low : LowKK tRep := lowK_any _ (k := .skip) rfl
theorem tLid_low : LowKK tLid := lowK_any _ (k := .skip) rfl
theorem tBd_low : LowKK tBd := lowK_any _ (k := .skip) rfl
theorem tEnd_low : LowKK tEnd := lowK_any _ (k := .skip) rfl

theorem miss_low (nm : String) : LowKK (guardS (ifs (Syntax.eLt (ArticleProg.firstOf esP nm) (Syntax.n 0))
    (ArticleProg.constName nm ++ [.ret (Syntax.n 13)]))) := by
  rw [DN.News.ArticleAdded.guardS_ifs, constName_g]
  exact lowKK_ite (DN.News.ArticleAdded.lt0_lower esP nm) (const_low nm 13) fun k => ⟨k, rfl⟩

theorem tFrom_low : LowKK tFrom := miss_low "From"
theorem tNews_low : LowKK tNews := miss_low "Newsgroups"
theorem tSubj_low : LowKK tSubj := miss_low "Subject"

theorem tDate_low : LowKK tDate := winS_low _ _ _ _ _ _ _ _
theorem tInj_low : LowKK tInj := winS_low _ _ _ _ _ _ _ _
theorem tPosted_low : LowKK tPosted := elemS_low _ _ _ _ _ _ _ _ _
theorem tDist_low : LowKK tDist := elemS_low _ _ _ _ _ _ _ _ _

/-- The words cleared, the shape found, a refused shape given back. -/
def hPro : List Syntax.PStmt :=
  [ArticleProg.area, ArticleProg.setW ArticleProg.xNameLen (Syntax.n 0), ArticleProg.setW ArticleProg.xOutLen
    (Syntax.n 0),
    ArticleProg.setW ArticleProg.xMsgLen (Syntax.n 0), ArticleProg.setW ArticleProg.xKnownN (Syntax.n 0)] ++
  guardS (.call "sh" "artStruct" []) ++ [.ite (Syntax.v "sh") [.ret (Syntax.v "sh")] []]

/-- The empty line's place read, the first fields' table cleared, the loop's locals declared. -/
def hPre : List Syntax.PStmt :=
  [.dec "sep" (wd ArticleProg.xSep), kept "sep" artMax, .dec "i" (Syntax.n 0),
   .while (Syntax.eLt (Syntax.v "i") (Syntax.n (ArticleProg.E esP + 1)))
     [.store (Syntax.eAdd (Syntax.atOff (Syntax.v "a") ArticleProg.xFirst) (Syntax.eMul (Syntax.v "i") (Syntax.n 8)))
       ArticleProg.neg1, inc "i"],
   .dec "rep" ArticleProg.neg1, .dec "lid" ArticleProg.neg1, .dec "bd" ArticleProg.neg1, .dec "p" (Syntax.n 0)]

/-- The fields' loop. -/
def hLoop : List Syntax.PStmt :=
  [.while (Syntax.eLt (Syntax.v "p") (Syntax.v "sep")) (guardL (DN.News.ArticleFields.chkHead ++
    DN.News.ArticleFields.chkTail))]

def headS : List Syntax.PStmt := hPro ++ hPre ++ hLoop

theorem artCheck_g : guardL (ArticleProg.artCheck ArticleSpec.spec esP).body = headS ++ tailS := rfl

/-! ## The checks after the fields as `checkWith` -/

/-- The tables lie outside the words `artCheck` may write. -/
theorem checkScr_tables {A : Word} {y : Nat} (h1 : ArticleProg.xFlags esP ≤ y) (h2 : y < 2 ^ 40) :
    ¬CheckScr A (at_ A y) := by
  have hl := (DN.News.ArticleTables.lay esP).1; have hF := xFirst_eq; have hN := xName_eq
  have hc : ArticleProg.nameCap = 1024 := rfl
  have hs := DN.News.ArticleFields.w_eq
  rintro (h | h | h | ⟨z, z1, z2, e⟩ | ⟨i, hi, e⟩)
  · exact DN.News.ArticleFields.not_chk (.inr (hl ▸ h1)) h2 (by have : aLen = 8 := rfl; omega) h
  · exact not_g (.inr (by omega)) h2 h
  · exact DN.News.ArticleAdded.high_add (by omega) h2 h
  · have := DN.News.ScanRun.at_inj (by omega) (by omega) e; omega
  · have := DN.News.ScanRun.at_inj (by omega) (w_lt64 (i := i) (by omega)) e
    rw [hs] at this; omega

/-- The words a memory after the loop keeps, as in `ms`. -/
theorem chkT_frame {s1 : PancakeState σ} {A : Word} {m0 ms : Word → Word} {a : Bytes} {gs : List (List (Nat × Nat))}
    {M : Word → Word} (h : ChkT s1 A m0 a gs M) (hm0f : ∀ w, ¬CheckScr A w → m0 w = ms w) :
    ∀ w, ¬CheckScr A w → M w = ms w := fun w hw =>
  (h.frame w (fun h' => hw (.inl h')) fun h' => hw (.inr (.inl h'))).trans (hm0f w hw)

theorem ret_plain {s1 : PancakeState σ} {A : Word} {m0 ms : Word → Word} {a : Bytes} {gs : List (List (Nat × Nat))}
    {M : Word → Word} (hM : ChkT s1 A m0 a gs M) {SEP : Nat} (hB : ChkBase s1 A m0 SEP esP)
    (hm0f : ∀ w, ¬CheckScr A w → m0 w = ms w)
    (hm0n : m0 (at_ A ArticleProg.xNameLen) = 0) {ctx : ArticleSpec.Context} {x : Refusal}
    (hcw : ArticleSpec.checkWith ArticleSpec.spec ctx a = .refused x) (hx : nameOf x = []) :
    CheckRet A s1.memaddrs s1.be ctx a ms (BitVec.ofNat 64 (DN.News.ArticleFields.refNum x)) M :=
  ret_refused hcw (chkT_broken hM hB.broken) (chkT_frame hM hm0f) hM.sets
    (by rw [hx]; exact nameAt_empty ((chkT_w hM (i := 11) (by decide)).trans hm0n)) (by rw [hx]; exact Nat.zero_le _)

theorem ret_name {s1 : PancakeState σ} {A : Word} (hA8 : A.toNat % 8 = 0) (hD : ArtDom A s1.memaddrs)
    {m0 ms : Word → Word} {a : Bytes} {gs : List (List (Nat × Nat))} {M : Word → Word} (hM : ChkT s1 A m0 a gs M)
    {SEP : Nat} (hB : ChkBase s1 A m0 SEP esP)
    (hm0f : ∀ w, ¬CheckScr A w → m0 w = ms w)
    {ctx : ArticleSpec.Context} {x : Refusal} (hcw : ArticleSpec.checkWith ArticleSpec.spec ctx a = .refused x)
    {name : Bytes} (hx : nameOf x = name) (hn : name.length ≤ ArticleProg.nameCap) (K e : Nat) :
    CheckRet A s1.memaddrs s1.be ctx a ms (BitVec.ofNat 64 (DN.News.ArticleFields.refNum x))
      (nameMem A s1.be name K e M) :=
  ret_refused hcw (nameMem_broken hA8 hn K e (chkT_broken hM hB.broken))
    (fun w hw => (nameMem_frame hA8 hn K e M hw).trans (chkT_frame hM hm0f w hw))
    (sets_lo hM.sets fun y hy => nameMem_lo hA8 hn K e M hy) (by rw [hx]; exact nameAt_mem hA8 hD hn K e M)
    (by rw [hx]; exact hn)

theorem ret_const {s1 : PancakeState σ} {A : Word} {m0 ms : Word → Word} {a : Bytes} {gs : List (List (Nat × Nat))}
    {M m : Word → Word} (hM : ChkT s1 A m0 a gs M) {SEP : Nat} (hB : ChkBase s1 A m0 SEP esP)
    (hm0f : ∀ w, ¬CheckScr A w → m0 w = ms w)
    {ctx : ArticleSpec.Context} {x : Refusal} (hcw : ArticleSpec.checkWith ArticleSpec.spec ctx a = .refused x)
    {nm : String} (hx : nameOf x = DN.News.CommandSpec.ascii nm) (hc : ConstAt A s1.memaddrs s1.be nm M m)
    (hnl : nm.length ≤ ArticleProg.nameCap) :
    CheckRet A s1.memaddrs s1.be ctx a ms (BitVec.ofNat 64 (DN.News.ArticleFields.refNum x)) m := by
  have hN := xName_eq; have hcap : ArticleProg.nameCap = 1024 := rfl; have hX := X_val
  have hlo : ∀ y, y < ArticleProg.X → m (at_ A y) = M (at_ A y) := fun y hy =>
    hc.2.2 _ (fun z h3 h4 e => by have := DN.News.ScanRun.at_inj (by omega) (by omega) e; omega)
      (DN.News.ScanRun.at_ne (by omega) (by simp only [ArticleProg.xNameLen, ArticleProg.w, hX]; omega)
        (by simp only [ArticleProg.xNameLen, ArticleProg.w, hX]; omega))
  refine ret_refused hcw ?_ (fun w hw => ?_) (sets_lo hM.sets hlo) (by rw [hx]; exact nameAt_const hc)
    (by rw [hx, DN.News.ArticleOut.ascii_length]; exact hnl)
  · rw [hlo _ (by have := DN.News.ArticleGrammar.broken_low; have := sets_le_X; omega)]
    exact chkT_broken hM hB.broken
  · rw [hc.2.2 w (fun y h1 h2 e => hw (.inr (.inr (.inr (.inl ⟨y, h1, h2, e⟩)))))
      fun e => hw (.inr (.inr (.inr (.inr ⟨11, .inl rfl, e⟩))))]
    exact chkT_frame hM hm0f w hw

theorem Kf_nodup (gs : List Bytes) : ∀ (n : Nat) (F : List Bytes), F.length = n → (Kf gs F).Nodup
  | 0, F, h => by
    have : F = [] := List.length_eq_zero_iff.1 h
    subst this; exact List.nodup_nil
  | n + 1, F, h => by
    obtain ⟨G, x, hF⟩ := (List.eq_nil_or_concat F).resolve_left (by rintro rfl; simp at h)
    rw [List.concat_eq_append] at hF
    subst hF
    have ih := Kf_nodup gs n G (by simp only [List.length_append, List.length_cons, List.length_nil, Nat.zero_add,
                                    Nat.add_right_cancel_iff] at h; omega)
    by_cases hx : x ∈ gs
    · rw [DN.News.ArticleListRun.Kf_in hx]; exact DN.News.ArticleListRun.kAdd_nodup ih x
    · rw [DN.News.ArticleListRun.Kf_out hx]; exact ih

theorem Kf_len (gs F : List Bytes) : (Kf gs F).length ≤ gs.length :=
  DN.News.ArticleListRun.nodup_len (Kf_nodup gs _ F rfl) fun _ h => DN.News.ArticleListRun.Kf_mem h

/-- A word of the known groups' list is none `artAdded` writes. -/
theorem known_add {A : Word} {y : Nat} (h1 : ArticleProg.xKnown ≤ y) (h2 : y < ArticleProg.xGroups) :
    ¬DN.News.ArticleAdded.AddScr A (at_ A y) := by
  have hX := X_val; have hG := DN.News.ArticleListRun.xGroups_eq; have hm := DN.News.ArticleOut.xMsg_eq
  have hd := DN.News.ArticleOut.xDec_eq; have hF := xFirst_eq
  have hk : ArticleProg.xKnown = 498192 := rfl
  have hmc : ArticleProg.msgCap = 256 := rfl
  have hw : ∀ i, i < 32 → at_ A y ≠ at_ A (ArticleProg.w i) := fun i hi => by
    refine DN.News.ScanRun.at_ne (by omega) (w_lt64 hi) ?_
    simp only [ArticleProg.w]; omega
  rintro (h | h | h | h | h | h | h)
  · obtain ⟨z, h4, h5, e⟩ := h
    have := DN.News.ScanRun.at_inj (by omega) (by omega) e; omega
  · rcases h with e | ⟨z, h4, h5, e⟩
    · exact hw 13 (by decide) e
    · have := DN.News.ScanRun.at_inj (by omega) (by omega) e; omega
  · exact hw 17 (by decide) h
  · exact hw 18 (by decide) h
  · exact hw 23 (by decide) h
  · exact hw 24 (by decide) h
  · exact hw 12 (by decide) h

/-- **The known groups kept** by `artAdded`. -/
theorem knownAt_add {A : Word} {gs K : List Bytes} {M m : Word → Word} (h : KnownAt A gs K M) (hK : K.length ≤ 64)
    (hfr : ∀ x, ¬DN.News.ArticleAdded.AddScr A x → m x = M x) : KnownAt A gs K m := by
  have hG := DN.News.ArticleListRun.xGroups_eq
  have hk : ArticleProg.xKnown = 498192 := rfl
  refine ⟨(hfr _ (DN.News.ArticleAdded.not_addScr_w (i := 14) (by decide) (by decide))).trans h.1, fun i hi => ?_⟩
  rw [hfr _ (known_add (by omega) (by omega))]; exact h.2 i hi

/-- A group of the article as a field. -/
theorem group_field {a : Bytes} {SEP : Nat} {L : List (Nat × Nat)} (hL : Lines a 0 L SEP)
    (hok : L.any (DN.News.ArticleLines.malLine a) = false) {g : List (Nat × Nat)} (hg : g ∈ groups a L) :
    ∃ P e more, g = (P, e) :: more.takeWhile (cont a) ∧ DN.News.ArticleLines.FieldAt a SEP P e more ∧ (P, e) ∈ L := by
  obtain ⟨P, e, more, rfl, h2, h3, h4⟩ := DN.News.ArticleAdded.mem_groups L.length L 0 (Nat.le_refl _) hL
    (DN.News.ArticleFields.head_ok hL hok) g hg
  have hmal : DN.News.ArticleLines.malName a (P, e) = false := by
    have := List.any_eq_false.1 hok (P, e) h4
    simpa [DN.News.ArticleLines.malLine, h3] using this
  exact ⟨P, e, more, rfl, ⟨h2, h3, hmal⟩, h4⟩

theorem window_name {ctx : ArticleSpec.Context} {fs : List Field} {nm : String} {x : Refusal}
    (h : window ctx fs nm = some x) : nameOf x = DN.News.CommandSpec.ascii nm := by
  unfold window at h
  split at h
  · split at h
    · cases h; rfl
    · split at h
      · cases h; rfl
      · nomatch h
  · nomatch h

theorem seq_fact (o : Oracle σ) {R : Ret} {xs ys : List Syntax.PStmt} {P Q R' : Assn σ} {F : Prop}
    (h1 : FragR o R xs P (fun u => Q u ∧ F)) (hl : LowKK ys) (h2 : F → FragR o R ys Q R') :
    FragR o R (xs ++ ys) P R' :=
  fragR_append h1 (fragR_pure F (fun _ h => h.2) hl fun hf => fragR_conseq (h2 hf) (fun _ h => h.1) fun _ h => h)

/-- **The checks after the fields answer as `checkWith`**, given the fields none refused. -/
theorem tail_check (o : Oracle σ) {A : Word} {s1 : PancakeState σ} (hA : Area ArticleProg.ofs A s1)
    (hD : ArtDom A s1.memaddrs) (hcode : ArtCode s1.code) {m0 ms : Word → Word} {a : Bytes} (hlen : a.length ≤ artMax)
    {SEP : Nat} (hB : ChkBase s1 A m0 SEP esP) (hSH : SEP ≤ ArticleSpec.spec.headerMax) {L : List (Nat × Nat)}
    (hL : Lines a 0 L SEP) (hok : L.any (DN.News.ArticleLines.malLine a) = false)
    (hline : ∀ q ∈ L, q.2 - q.1 ≤ ArticleProg.nameCap) {ctx : ArticleSpec.Context}
    (hctx : DN.News.ArticleAdded.CtxAt A s1.memaddrs s1.be ctx m0) (hGr : GroupsAt A s1.memaddrs s1.be ctx.groups m0)
    (hm0f : ∀ w, ¬CheckScr A w → m0 w = ms w)
    (hm0n : m0 (at_ A ArticleProg.xNameLen) = 0)
    (hcw : ArticleSpec.checkWith ArticleSpec.spec ctx a =
      DN.News.ArticleLines.tailOf ArticleSpec.spec ctx ((groups a L).map (fieldOf a)))
    (hnoref : ∀ g ∈ groups a L, DN.News.ArticleFields.fieldNum (fieldOf a g) = 0)
    (hgm : ArticleSpec.has ((groups a L).map (fieldOf a)) "Sender" = false →
      ∀ f, ArticleSpec.find? ((groups a L).map (fieldOf a)) "From" = some f →
      ∃ b, DN.News.Abnf.matches? AbnfRules.grammar AbnfRules.depth (ArticleSpec.ruleNamed "mailbox")
        (f.value.map BitVec.toNat) = .ok b) :
    FragR o (CheckRet A s1.memaddrs s1.be ctx a ms) tailS
      (RunF s1 (DN.News.ArticleFields.chkL A SEP SEP (optW (DN.News.ArticleFields.repP a (groups a L)))
        (optW (DN.News.ArticleFields.placeBy (DN.News.ArticleFields.lidQ a) (groups a L)))
        (optW (DN.News.ArticleFields.placeBy (DN.News.ArticleFields.bdQ a) (groups a L))))
        (ChkT s1 A m0 a (groups a L))) (fun _ => False) := by
  have hA8 := hA.hA
  have hM := artMax_eq
  have hsepA := (DN.News.ArticleLines.lines_sep hL).2.2
  have hSI : SEP ≤ inputMax := by have : ArticleSpec.spec.headerMax = 65536 := rfl; rw [inputMax_eq]; omega
  have hfind : ((groups a L).map (fieldOf a)).findSome? (ArticleSpec.fieldRefusal ArticleSpec.spec) = none := by
    rw [List.findSome?_eq_none_iff]
    intro f hf
    obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hf
    exact DN.News.ArticleFields.fieldNum_zero (hnoref g hg)
  have hv : ArticleSpec.checkWith ArticleSpec.spec ctx a =
      match ArticleSpec.articleRefusal ArticleSpec.spec ctx ((groups a L).map (fieldOf a)) with
      | some x => .refused x
      | none => .accepted (ArticleSpec.added ArticleSpec.spec ctx ((groups a L).map (fieldOf a))) := hcw.trans
                 (tail_art hfind)
  have hsmall : DN.News.ArticleFields.Placed (groups a L) := fun g hg => by
    have := DN.News.ArticleFields.groups_place hL hok g hg; omega
  have L13 := tEnd_low
  have L12 := lowKK_append tGroups_low L13
  have L11 := lowKK_append tInj_low L12
  have L10 := lowKK_append tDate_low L11
  have L9 := lowKK_append tBd_low L10
  have L8 := lowKK_append tDist_low L9
  have L7 := lowKK_append tSender_low L8
  have L6 := lowKK_append tLid_low L7
  have L5 := lowKK_append tPosted_low L6
  have L4 := lowKK_append tSubj_low L5
  have L3 := lowKK_append tNews_low L4
  have L2 := lowKK_append tFrom_low L3
  have hrd : ∀ name : Bytes, ArticleSpec.repeatedFrom ArticleSpec.spec ((groups a L).map (fieldOf a)) [] = some name →
      ArticleSpec.checkWith ArticleSpec.spec ctx a = .refused (.repeated name) := fun name h => by
    rw [hv, ar_rep h]
  unfold tailS
  -- the repeated field
  refine seq_fact o (name_ret o hA hD hcode hlen hB (gs := groups a L) rfl (x := "rep") (c := "cr") (by decide) rfl rfl
    (DN.News.ArticleFields.repP_small hsmall) (N := 12) (lowK_any _ (k := .skip) rfl) ?_) L2 fun hrep => ?_
  · intro p hp
    unfold DN.News.ArticleFields.repP at hp
    cases hg : DN.News.ArticleFields.repG a [] (groups a L) with
    | none => rw [hg] at hp; nomatch hp
    | some g =>
      rw [hg] at hp
      obtain ⟨P, e, more, rfl, hf, hmemL⟩ := group_field hL hok (DN.News.ArticleFields.repG_mem hg)
      have hpP : p = P := (Option.some.inj hp).symm
      subst hpP
      have hcol := DN.News.ArticleLines.fieldAt_colon hf
      have hmem := DN.News.ArticleLines.lines_mem hf.lines (p, e) List.mem_cons_self
      have hK : DN.News.ArticleLines.nameLen a p e < ArticleProg.nameCap := by
        have := hline (p, e) hmemL; simp only at this; omega
      refine ⟨e, more, hf, hK, fun M hM => ?_⟩
      have hname : ArticleSpec.repeatedFrom ArticleSpec.spec ((groups a L).map (fieldOf a)) [] =
          some (seg a p (p + DN.News.ArticleLines.nameLen a p e)) := by
        rw [DN.News.ArticleFields.repeatedFrom_repG, hg]; rfl
      exact ret_name hA8 hD hM hB hm0f (hrd _ hname) rfl
        (by show (seg a p (p + DN.News.ArticleLines.nameLen a p e)).length ≤ _
            rw [DN.News.ArticleLines.seg_length a (by omega) (by omega)]; omega) _ e
  have hnr : ArticleSpec.repeatedFrom ArticleSpec.spec ((groups a L).map (fieldOf a)) [] = none := by
    rw [DN.News.ArticleFields.repeatedFrom_repG]
    unfold DN.News.ArticleFields.repP at hrep
    cases h : DN.News.ArticleFields.repG a [] (groups a L) with
    | none => rfl
    | some g => rw [h] at hrep; nomatch hrep
  have hv1 : ArticleSpec.checkWith ArticleSpec.spec ctx a = match arMissing ctx ((groups a L).map (fieldOf a)) with
      | some x => .refused x
      | none => .accepted (ArticleSpec.added ArticleSpec.spec ctx ((groups a L).map (fieldOf a))) :=
                 by rw [hv, ar_norep hnr]
  have hhas : ∀ nm, ArticleSpec.has ((groups a L).map (fieldOf a)) nm = (DN.News.ArticleAdded.firstP a L nm).isSome :=
    DN.News.ArticleAdded.has_fields a L
  have hreq : ArticleSpec.spec.required = ["From", "Newsgroups", "Subject"] := rfl
  have hmiss : ∀ nm, ArticleSpec.spec.required.find? (!ArticleSpec.has ((groups a L).map (fieldOf a)) ·) = some nm →
      ArticleSpec.checkWith ArticleSpec.spec ctx a = .refused (.missing (DN.News.CommandSpec.ascii nm)) :=
    fun nm h => by rw [hv1, am_miss h]
  -- From
  refine seq_fact o (missing_step o hA hD hlen hB hL hok (l := DN.News.ArticleFields.chkL A SEP SEP _ _ _) rfl
    (nm := "From") (by simp [allNames, hreq]) (by decide) fun hn M m hM hby hln hfr =>
      ret_const hM hB hm0f (hmiss "From" (by rw [hreq, List.find?_cons, hhas, hn]; rfl)) rfl ⟨hby, hln, hfr⟩
        (by decide)) L3
    fun hF => ?_
  -- Newsgroups
  refine seq_fact o (missing_step o hA hD hlen hB hL hok (l := DN.News.ArticleFields.chkL A SEP SEP _ _ _) rfl
    (nm := "Newsgroups") (by simp [allNames, hreq]) (by decide) fun hn M m hM hby hln hfr =>
      ret_const hM hB hm0f (hmiss "Newsgroups" (by
        rw [hreq, List.find?_cons, hhas, hF, List.find?_cons, hhas, hn]; rfl)) rfl ⟨hby, hln, hfr⟩ (by decide))
    L4 fun hN => ?_
  -- Subject
  refine seq_fact o (missing_step o hA hD hlen hB hL hok (l := DN.News.ArticleFields.chkL A SEP SEP _ _ _) rfl
    (nm := "Subject") (by simp [allNames, hreq]) (by decide) fun hn M m hM hby hln hfr =>
      ret_const hM hB hm0f (hmiss "Subject" (by
        rw [hreq, List.find?_cons, hhas, hF, List.find?_cons, hhas, hN, List.find?_cons, hhas, hn]; rfl)) rfl
        ⟨hby, hln, hfr⟩ (by decide)) L5 fun hS => ?_
  have hv2 : ArticleSpec.checkWith ArticleSpec.spec ctx a = match arPosted ctx ((groups a L).map (fieldOf a)) with
      | some x => .refused x
      | none => .accepted (ArticleSpec.added ArticleSpec.spec ctx ((groups a L).map (fieldOf a))) := by
    rw [hv1, am_ok (by rw [hreq, List.find?_cons, hhas, hF, List.find?_cons, hhas, hN, List.find?_cons, hhas, hS]; rfl)]
  have hfr6 : ∀ (ns : List String), (∀ y ∈ ns, y ∉ ["p", "bd", "lid", "rep", "sep", "a"]) → ∀ y, y ∈ ns →
      Fresh y (DN.News.ArticleFields.chkL A SEP SEP (optW (DN.News.ArticleFields.repP a (groups a L)))
        (optW (DN.News.ArticleFields.placeBy (DN.News.ArticleFields.lidQ a) (groups a L)))
        (optW (DN.News.ArticleFields.placeBy (DN.News.ArticleFields.bdQ a) (groups a L)))) = true := fun ns hns y hy =>
          by
    have := hns y hy
    simp only [List.mem_cons, List.mem_nil_iff, or_false, not_or] at this
    simp only [Fresh, DN.News.ArticleFields.chkL, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true,
      bne_iff_ne, ne_eq]
    exact ⟨fun h => this.1 h.symm, fun h => this.2.1 h.symm, fun h => this.2.2.1 h.symm, fun h => this.2.2.2.1 h.symm,
      fun h => this.2.2.2.2.1 h.symm, fun h => this.2.2.2.2.2 h.symm⟩
  -- POSTED
  refine seq_fact o (elem_step o hA hD hcode hlen hB hL hok rfl (nm := "Path") (pp := "hp") (pf := "hf") (pn := "hn")
    (ps := "hs") (pe := "he") (pv := "po") (by simp [allNames, ArticleProg.readNames]) (by decide) (hfr6 _ (by decide))
    mem_artPosted rfl (p := fun v => (ArticleSpec.pathElements v).any ArticleSpec.isPosted)
    (fun _ _ hSE hE _ hA1 hD1 hc1 hb1 hin1 hs he =>
      DN.News.ArticleListRun.artPosted_ok o hA1 hD1 hc1 hb1 hlen hin1 hSE hE hs he) (N := 14) fun hc M hM =>
    ret_plain hM hB hm0f hm0n (x := .posted) (by rw [hv2, ap_eq, if_pos hc]) rfl) L6 fun hP => ?_
  have hv3 : ArticleSpec.checkWith ArticleSpec.spec ctx a = match arLong ctx ((groups a L).map (fieldOf a)) with
      | some x => .refused x
      | none => .accepted (ArticleSpec.added ArticleSpec.spec ctx ((groups a L).map (fieldOf a))) := by
    rw [hv2, ap_eq, if_neg (by rw [hP]; decide)]
  have hfm : ∀ q : List (Nat × Nat) → Bool, ∀ q' : Field → Bool, (∀ g, q g = q' (fieldOf a g)) →
      ((groups a L).map (fieldOf a)).find? q' = ((groups a L).find? q).map (fieldOf a) := fun q q' h => by
    rw [List.find?_map, show (q' ∘ fieldOf a) = q from funext fun g => (h g).symm]
  -- the long Message-ID
  refine seq_fact o (name_ret o hA hD hcode hlen hB (gs := groups a L) rfl (x := "lid") (c := "cl") (by decide) rfl rfl
    (DN.News.ArticleFields.placeBy_small hsmall) (N := 15) (lowK_any _ (k := .skip) rfl) ?_) L7 fun hlid => ?_
  · intro p hp
    unfold DN.News.ArticleFields.placeBy at hp
    cases hg : (groups a L).find? (DN.News.ArticleFields.lidQ a) with
    | none => rw [hg] at hp; nomatch hp
    | some g =>
      rw [hg] at hp
      obtain ⟨P, e, more, rfl, hf, hmemL⟩ := group_field hL hok (List.mem_of_find?_eq_some hg)
      have hpP : p = P := (Option.some.inj hp).symm
      subst hpP
      have hcol := DN.News.ArticleLines.fieldAt_colon hf
      have hmem := DN.News.ArticleLines.lines_mem hf.lines (p, e) List.mem_cons_self
      have hK : DN.News.ArticleLines.nameLen a p e < ArticleProg.nameCap := by
        have := hline (p, e) hmemL; simp only at this; omega
      refine ⟨e, more, hf, hK, fun M hM => ?_⟩
      have hfl := hfm (DN.News.ArticleFields.lidQ a) (fun f => ArticleSpec.isOne ArticleSpec.idFields f &&
        (ArticleSpec.msgIds f.value).any (·.length > ArticleSpec.spec.idMax)) (fun g => rfl)
      rw [hg] at hfl
      exact ret_name hA8 hD hM hB hm0f (by rw [hv3, al_some hfl]) rfl
        (by show (seg a p (p + DN.News.ArticleLines.nameLen a p e)).length ≤ _
            rw [DN.News.ArticleLines.seg_length a (by omega) (by omega)]; omega) _ e
  have hlong : ((groups a L).map (fieldOf a)).find? (fun f => ArticleSpec.isOne ArticleSpec.idFields f &&
      (ArticleSpec.msgIds f.value).any (·.length > ArticleSpec.spec.idMax)) = none := by
    rw [hfm (DN.News.ArticleFields.lidQ a) _ (fun g => rfl)]
    unfold DN.News.ArticleFields.placeBy at hlid
    cases h : (groups a L).find? (DN.News.ArticleFields.lidQ a) with
    | none => rfl
    | some g => rw [h] at hlid; nomatch hlid
  have hv4 : ArticleSpec.checkWith ArticleSpec.spec ctx a = match arSender ctx ((groups a L).map (fieldOf a)) with
      | some x => .refused x
      | none => .accepted (ArticleSpec.added ArticleSpec.spec ctx ((groups a L).map (fieldOf a))) :=
                 by rw [hv3, al_none hlong]
  -- Sender
  refine seq_fact o (sender_step o hA hD hcode hlen hB hSI hL hok rfl (hfr6 _ (by decide)) hgm fun hc M hM =>
    ret_plain hM hB hm0f hm0n (x := .noSender) (by rw [hv4, as_eq, if_pos hc]) rfl) L8 fun hSd => ?_
  have hv5 : ArticleSpec.checkWith ArticleSpec.spec ctx a = match arDist ctx ((groups a L).map (fieldOf a)) with
      | some x => .refused x
      | none => .accepted (ArticleSpec.added ArticleSpec.spec ctx ((groups a L).map (fieldOf a))) := by
    rw [hv4, as_eq, if_neg (by rw [hSd]; decide)]
  -- Distribution
  refine seq_fact o (elem_step o hA hD hcode hlen hB hL hok rfl (nm := "Distribution") (pp := "dp") (pf := "df")
    (pn := "dn") (ps := "ds") (pe := "de") (pv := "da") (by simp [allNames, ArticleProg.readNames]) (by decide)
    (hfr6 _ (by decide)) mem_artDistAll rfl (p := fun v => (ArticleSpec.listed v).any (ArticleSpec.named · "all"))
    (fun _ _ hSE hE _ hA1 hD1 hc1 hb1 hin1 hs he =>
      DN.News.ArticleListRun.artDistAll_ok o hA1 hD1 hc1 hb1 hlen hin1 hSE hE hs he) (N := 17) fun hc M hM =>
    ret_plain hM hB hm0f hm0n (x := .distributionAll) (by rw [hv5, ad_eq, if_pos hc]) rfl) L9 fun hDi => ?_
  have hv6 : ArticleSpec.checkWith ArticleSpec.spec ctx a = match arBad ctx ((groups a L).map (fieldOf a)) with
      | some x => .refused x
      | none => .accepted (ArticleSpec.added ArticleSpec.spec ctx ((groups a L).map (fieldOf a))) := by
    rw [hv5, ad_eq, if_neg (by rw [hDi]; decide)]
  -- the date that means none
  refine seq_fact o (name_ret o hA hD hcode hlen hB (gs := groups a L) rfl (x := "bd") (c := "cb") (by decide) rfl rfl
    (DN.News.ArticleFields.placeBy_small hsmall) (N := 18) (lowK_any _ (k := .skip) rfl) ?_) L10 fun hbd => ?_
  · intro p hp
    unfold DN.News.ArticleFields.placeBy at hp
    cases hg : (groups a L).find? (DN.News.ArticleFields.bdQ a) with
    | none => rw [hg] at hp; nomatch hp
    | some g =>
      rw [hg] at hp
      obtain ⟨P, e, more, rfl, hf, hmemL⟩ := group_field hL hok (List.mem_of_find?_eq_some hg)
      have hpP : p = P := (Option.some.inj hp).symm
      subst hpP
      have hcol := DN.News.ArticleLines.fieldAt_colon hf
      have hmem := DN.News.ArticleLines.lines_mem hf.lines (p, e) List.mem_cons_self
      have hK : DN.News.ArticleLines.nameLen a p e < ArticleProg.nameCap := by
        have := hline (p, e) hmemL; simp only at this; omega
      refine ⟨e, more, hf, hK, fun M hM => ?_⟩
      have hfl := hfm (DN.News.ArticleFields.bdQ a) (fun f => (ArticleSpec.dateText f).any
        (fun t => (ArticleSpec.dateValue t).isNone))
        (fun g => rfl)
      rw [hg] at hfl
      exact ret_name hA8 hD hM hB hm0f (by rw [hv6, ab_some hfl]) rfl
        (by show (seg a p (p + DN.News.ArticleLines.nameLen a p e)).length ≤ _
            rw [DN.News.ArticleLines.seg_length a (by omega) (by omega)]; omega) _ e
  have hbad : ((groups a L).map (fieldOf a)).find? (fun f => (ArticleSpec.dateText f).any
    (fun t => (ArticleSpec.dateValue t).isNone)) = none := by
    rw [hfm (DN.News.ArticleFields.bdQ a) _ (fun g => rfl)]
    unfold DN.News.ArticleFields.placeBy at hbd
    cases h : (groups a L).find? (DN.News.ArticleFields.bdQ a) with
    | none => rfl
    | some g => rw [h] at hbd; nomatch hbd
  have hv7 : ArticleSpec.checkWith ArticleSpec.spec ctx a = match arWindows ctx ((groups a L).map (fieldOf a)) with
      | some x => .refused x
      | none => .accepted (ArticleSpec.added ArticleSpec.spec ctx ((groups a L).map (fieldOf a))) :=
                 by rw [hv6, ab_none hbad]
  have hctx' := hctx
  obtain ⟨hid, _, _, hrnd, _, _, hseq, _, hrun, _, hcn, _, hwm, hwall⟩ := hctx
  -- the dates' windows
  refine seq_fact o (window_step o hA hD hcode hlen hB hL hok rfl (nm := "Date") (pp := "wp") (pf := "wf") (pn := "wn")
    (ps := "ws") (pe := "we") (pv := "wv") (pt := "wt") (by simp [allNames, ArticleProg.dateFields]) (by decide)
    (by decide) (hfr6 _ (by decide)) hwall hwm
    fun x hw M m hM hc => ret_const hM hB hm0f (by rw [hv7, aw_date hw]) (window_name hw) hc
      (by decide)) L11 fun hWd => ?_
  refine seq_fact o (window_step o hA hD hcode hlen hB hL hok rfl (nm := "Injection-Date") (pp := "xp") (pf := "xf")
    (pn := "xn") (ps := "xs") (pe := "xe") (pv := "xv") (pt := "xt") (by simp [allNames, ArticleProg.dateFields])
    (by decide) (by decide) (hfr6 _ (by decide)) hwall hwm
    fun x hw M m hM hc => ret_const hM hB hm0f (by rw [hv7, aw_inj hWd hw]) (window_name hw) hc
      (by decide)) L12 fun hWi => ?_
  have hv8 : ArticleSpec.checkWith ArticleSpec.spec ctx a = match arGroups ctx ((groups a L).map (fieldOf a)) with
      | some x => .refused x
      | none => .accepted (ArticleSpec.added ArticleSpec.spec ctx ((groups a L).map (fieldOf a))) :=
                 by rw [hv7, aw_none hWd hWi]
  -- the groups
  have hG63 : (groupsOf ((groups a L).map (fieldOf a))).length < 2 ^ 63 := by
    unfold groupsOf
    cases hf : ArticleSpec.find? ((groups a L).map (fieldOf a)) "Newsgroups" with
    | none => simp
    | some f =>
      simp only [Option.map_some, Option.getD_some]
      obtain ⟨g, hg, rfl⟩ := List.mem_map.1 (List.mem_of_find?_eq_some hf)
      obtain ⟨P, e, more, rfl, hfa, _⟩ := group_field hL hok hg
      have hcol := DN.News.ArticleLines.fieldAt_colon hfa
      have hmore := (DN.News.ArticleLines.lines_tail hfa.lines).2
      have hNXs := DN.News.ArticleLines.lines_sep (DN.News.ArticleAdded.lines_next more (e + 2) hmore)
      have hNXg := (DN.News.ArticleLines.nextOf_ge hmore).1
      rw [DN.News.ArticleAdded.value_seg hfa.lines hcol.2.1]
      have := listed_le (seg a (P + DN.News.ArticleLines.nameLen a P e + 1)
        (DN.News.ArticleLines.nextOf a more SEP - 2))
      rw [DN.News.ArticleLines.seg_length a (by omega) (by omega)] at this
      omega
  have hfit : (ArticleSpec.added ArticleSpec.spec ctx ((groups a L).map (fieldOf a))).header.length ≤ ArticleProg.outMax
    := by
    have htl := texts_len (a := a) (SEP := SEP) L.length L 0 (Nat.le_refl _) hL (DN.News.ArticleFields.head_ok hL hok)
    have hh := header_le ctx ((groups a L).map (fieldOf a)) hrnd hseq hrun hcn
      (by have : ArticleProg.wallMax = 2 ^ 40 := rfl; omega)
    have hsum : (((groups a L).map (fieldOf a)).map (·.text.length)).sum = ((groups a L).map
      (fun g => (fieldOf a g).text.length)).sum := by
      simp only [List.map_map]; rfl
    have : ArticleSpec.spec.headerMax = 65536 := rfl
    have : ArticleProg.outMax = 69632 := rfl
    omega
  have hmidl := mid_lt ctx ((groups a L).map (fieldOf a)) hid hrnd hseq hlong
  refine fragR_append (groups_step o hA hD hcode hlen hB hL hok rfl (hfr6 _ (by decide)) hGr) ?_
  have harg : ¬16 < (groupsOf ((groups a L).map (fieldOf a))).length →
    (groupsOf ((groups a L).map (fieldOf a))).any ArticleSpec.reserved = false →
      arGroups ctx ((groups a L).map (fieldOf a)) = if !(groupsOf ((groups a L).map (fieldOf a))).any
        (ctx.groups.contains ·) then some .noKnownGroup else none :=
    fun h1 h2 => by
      unfold arGroups; rw [if_neg (show ¬(_ > ArticleSpec.spec.groupsMax) from h1), if_neg (by simp [h2])]; rfl
  refine tail_end o hA hD hcode hlen hB hL hok rfl rfl hctx' hG63 hfit hmidl (fun g1 M hM =>
    ret_plain hM hB hm0f hm0n (x := .tooManyGroups) (by
      rw [hv8]; unfold arGroups; rw [if_pos (show _ > ArticleSpec.spec.groupsMax from g1)]) rfl)
    (fun g1 g2 M hM => ret_plain hM hB hm0f hm0n (x := .reservedGroup)
      (by rw [hv8]; unfold arGroups
          rw [if_neg (show ¬(_ > ArticleSpec.spec.groupsMax) from g1), if_pos (by simp only [g2, Bool.and_true]; rfl)])
            rfl)
    (fun g1 g2 g3 M hM => ret_plain hM hB hm0f hm0n (x := .noKnownGroup)
      (by rw [hv8, harg g1 g2, if_pos (by rw [g3]; rfl)]) rfl)
    (fun g1 g2 g3 M hM hG w m hadd => ?_)
  obtain ⟨_, hfrm, hout, holen, hmsg, hmlen⟩ := hadd
  have hacc : ArticleSpec.checkWith ArticleSpec.spec ctx a = .accepted (ArticleSpec.added ArticleSpec.spec ctx
    ((groups a L).map (fieldOf a))) := by
    rw [hv8, harg g1 g2, if_neg (by rw [g3]; decide)]
  have hX := X_val; have hm := DN.News.ArticleOut.xMsg_eq; have hd := DN.News.ArticleOut.xDec_eq
  have hK := Nat.le_trans (Kf_len ctx.groups (groupsOf ((groups a L).map (fieldOf a)))) hGr.1
  refine ⟨by rw [hfrm _ DN.News.ArticleAdded.broken_add]; exact chkT_broken hM hB.broken,
    fun w hw => (hfrm w fun h' => hw (.inr (.inr (.inl h')))).trans (chkT_frame hM hm0f w hw),
    sets_lo hM.sets fun y hy => hfrm _ (DN.News.ArticleAdded.not_addScr (.inl hy) (by omega) (by omega)), ?_⟩
  rw [hacc]
  exact ⟨rfl, hout, hfit, holen, hmsg, hmidl, hmlen, knownAt_add (hG.2.2.2 g3) hK hfrm, hK⟩

/-! ## The section's shape and the fields' refusals -/

theorem fieldRefusal_name {f : Field} {x : Refusal} (h : ArticleSpec.fieldRefusal ArticleSpec.spec f = some x) :
    nameOf x = f.name := by
  unfold ArticleSpec.fieldRefusal at h
  by_cases h1 : ArticleSpec.isOne ArticleSpec.spec.injected f = true
  · rw [if_pos h1] at h; cases h; rfl
  rw [if_neg h1] at h
  by_cases h2 : ArticleSpec.isOne ArticleSpec.spec.traced f = true
  · rw [if_pos h2] at h; cases h; rfl
  rw [if_neg h2] at h
  by_cases h3 : ArticleSpec.isOne ArticleSpec.spec.deprecated f = true
  · rw [if_pos h3] at h; cases h; rfl
  rw [if_neg h3] at h
  by_cases h4 : ArticleSpec.isOne ArticleSpec.spec.notOffered f = true
  · rw [if_pos h4] at h; cases h; rfl
  rw [if_neg h4] at h
  by_cases h5 : (ArticleSpec.spec.blank && f.body.any (·.all DN.News.CommandSpec.isWS)) = true
  · rw [if_pos h5] at h; cases h; rfl
  rw [if_neg h5] at h
  by_cases h6 : (!ArticleSpec.grammarSays (ArticleSpec.ruleOf f) f.text) = true
  · rw [if_pos h6] at h; cases h; rfl
  rw [if_neg h6] at h; nomatch h

theorem findSome_first {fs1 fs2 : List Field} {f : Field}
    (h1 : ∀ g ∈ fs1, ArticleSpec.fieldRefusal ArticleSpec.spec g = none) :
    (fs1 ++ f :: fs2).findSome? (ArticleSpec.fieldRefusal ArticleSpec.spec) =
      match ArticleSpec.fieldRefusal ArticleSpec.spec f with
      | some x => some x
      | none => fs2.findSome? (ArticleSpec.fieldRefusal ArticleSpec.spec) := by
  rw [List.findSome?_append, List.findSome?_eq_none_iff.2 h1, Option.none_or, List.findSome?_cons]
  cases ArticleSpec.fieldRefusal ArticleSpec.spec f <;> rfl

/-- **A field refused**: the verdict is its refusal, with its number and name. -/
theorem refused_field {ctx : ArticleSpec.Context} {a : Bytes} {L : List (Nat × Nat)}
    (hcw : ArticleSpec.checkWith ArticleSpec.spec ctx a =
      DN.News.ArticleLines.tailOf ArticleSpec.spec ctx ((groups a L).map (fieldOf a)))
    {gd rest : List (List (Nat × Nat))} {g : List (Nat × Nat)} (hgr : groups a L = gd ++ g :: rest)
    (hz : ∀ g' ∈ gd, DN.News.ArticleFields.fieldNum (fieldOf a g') = 0)
    (hne : DN.News.ArticleFields.fieldNum (fieldOf a g) ≠ 0) :
    ∃ x, ArticleSpec.checkWith ArticleSpec.spec ctx a = .refused x ∧
      DN.News.ArticleFields.refNum x = DN.News.ArticleFields.fieldNum (fieldOf a g) ∧ nameOf x =
        (fieldOf a g).name := by
  cases hx : ArticleSpec.fieldRefusal ArticleSpec.spec (fieldOf a g) with
  | none => exact absurd (by unfold DN.News.ArticleFields.fieldNum; rw [hx]; rfl) hne
  | some x =>
    refine ⟨x, ?_, by unfold DN.News.ArticleFields.fieldNum; rw [hx]; rfl, fieldRefusal_name hx⟩
    rw [hcw]
    unfold DN.News.ArticleLines.tailOf
    rw [hgr, List.map_append, List.map_cons, findSome_first (fun g' hg' => by
      obtain ⟨g'', hg'', rfl⟩ := List.mem_map.1 hg'
      exact DN.News.ArticleFields.fieldNum_zero (hz g'' hg'')), hx]

theorem shape_le (a : Bytes) : DN.News.ArticleLines.shapeOf ArticleSpec.spec a ≤ 5 := by
  unfold DN.News.ArticleLines.shapeOf
  split
  · decide
  · split
    · decide
    · split
      · decide
      · split
        · decide
        · split <;> decide

/-- **A shape refused**: the verdict carries the shape's number and no name. -/
theorem refused_shape {ctx : ArticleSpec.Context} {a : Bytes}
    (h : DN.News.ArticleLines.shapeOf ArticleSpec.spec a ≠ 0) :
    ∃ x, ArticleSpec.checkWith ArticleSpec.spec ctx a = .refused x ∧
      DN.News.ArticleFields.refNum x = DN.News.ArticleLines.shapeOf ArticleSpec.spec a ∧ nameOf x = [] := by
  have hle := shape_le a
  rw [DN.News.ArticleLines.checkWith_shape]
  generalize DN.News.ArticleLines.shapeOf ArticleSpec.spec a = k at h hle ⊢
  have : k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 := by omega
  rcases this with rfl | rfl | rfl | rfl | rfl <;> exact ⟨_, rfl, rfl, rfl⟩

theorem shape_zero {ctx : ArticleSpec.Context} {a : Bytes} (h : DN.News.ArticleLines.shapeOf ArticleSpec.spec a = 0) :
    ArticleSpec.checkWith ArticleSpec.spec ctx a =
      DN.News.ArticleLines.tailOf ArticleSpec.spec ctx ((groups a (DN.News.ArticleLines.spans a 0).1).map (fieldOf a))
        := by
  rw [DN.News.ArticleLines.checkWith_shape, h]

theorem shape0_facts {a : Bytes} (h : DN.News.ArticleLines.shapeOf ArticleSpec.spec a = 0) :
    ∃ p, (DN.News.ArticleLines.spans a 0).2 = some p ∧ p ≤ ArticleSpec.spec.headerMax ∧
      (DN.News.ArticleLines.spans a 0).1.any (fun q => decide (ArticleSpec.spec.lineMax < q.2 - q.1)) = false ∧
      (DN.News.ArticleLines.spans a 0).1.any (DN.News.ArticleLines.malLine a) = false := by
  unfold DN.News.ArticleLines.shapeOf at h
  split at h
  · nomatch h
  · split at h
    · nomatch h
    · rename_i p hp
      split at h
      · nomatch h
      · rename_i h1
        split at h
        · nomatch h
        · rename_i h2
          split at h
          · nomatch h
          · rename_i h3
            exact ⟨p, hp, by omega, by simpa using h2, by simpa using h3⟩

theorem mem_artStruct : gd (ArticleProg.artStruct ArticleSpec.spec) ∈ ArticleProg.functions ArticleSpec.spec esP .none
    :=
  List.mem_append_right _ (List.mem_map.2 ⟨ArticleProg.artStruct ArticleSpec.spec, by simp, rfl⟩)

/-- **A call of `artStruct`**: the section's shape; the empty line's place in `xSep` if the shape is right. -/
theorem structCall_frag (o : Oracle σ) {R : Ret} {A : Word} {s0 : PancakeState σ} (hA : Area ArticleProg.ofs A s0)
    (hD : ArtDom A s0.memaddrs) (hcode : ArtCode s0.code) {rt : String} (hra : rt ≠ "a") {l : List (String × Value)}
    (hla : l.lookup "a" = some A) (hrt : Fresh rt l = true) {m0 : Word → Word} {a : Bytes} (hlen : a.length ≤ artMax)
    (hin : InputAt m0 s0.memaddrs s0.be A a) (hb : m0 (at_ A aBroken) = 0)
    (hlw : m0 (at_ A ArticleProg.xLen) = BitVec.ofNat 64 a.length) :
    FragR o R (guardS (.call rt "artStruct" [])) (RunF s0 l (· = m0))
      (RunF s0 ((rt, BitVec.ofNat 64 (DN.News.ArticleLines.shapeOf ArticleSpec.spec a)) :: l)
        (· = structMem ArticleSpec.spec A a m0)) := by
  refine fragR_conseq (gcall_frag o hA hcode hra (f := ArticleProg.artStruct ArticleSpec.spec) mem_artStruct
    (by decide) (F := (· = m0)) (args := []) rfl hla (vs := []) rfl (fun _ _ => rfl)
    (Rf := StructRet ArticleSpec.spec A a)
    (fun s1 hA1 hc hm hbe _ hF => by
      have := artStruct_ok o (r := ArticleSpec.spec) (by decide) (by decide) hA1 (by rw [hm]; exact hD)
        (by rw [hc]; exact hcode) hlen
        (by rw [hF, hm, hbe]; exact hin) (by rw [hF]; exact hb) (by rw [hF]; exact hlw)
      exact this) hrt
    (G := fun v m => m = structMem ArticleSpec.spec A a m0 ∧
      v = BitVec.ofNat 64 (DN.News.ArticleLines.shapeOf ArticleSpec.spec a))
    (fun m m' v hm hr => by subst hm; exact hr) fun v m h => by
      rw [h.1]; unfold structMem; split
      · exact (upd_ne _ (broken_ne_w (i := 16) (by decide) A)).trans hb
      · exact hb) (fun u h => h) fun u ⟨v, h⟩ => ?_
  obtain ⟨hm, hv⟩ := h.2
  subst hv; exact ⟨h.1, hm⟩

theorem tailS_low : LowKK tailS :=
  lowKK_append tRep_low (lowKK_append tFrom_low (lowKK_append tNews_low (lowKK_append tSubj_low
    (lowKK_append tPosted_low
    (lowKK_append tLid_low (lowKK_append tSender_low (lowKK_append tDist_low
      (lowKK_append tBd_low (lowKK_append tDate_low
      (lowKK_append tInj_low (lowKK_append tGroups_low tEnd_low)))))))))))

theorem pre_low : LowKK hPre := lowK_any _ (k := .skip) rfl

theorem loop_low : LowKK hLoop := lowK_any _ (k := .skip) rfl

/-! ## The prologue -/

/-- The memory once the name's, the header's, the identifier's lengths and the known groups' count are cleared. -/
def m4 (A : Word) (m : Word → Word) : Word → Word :=
  upd (upd (upd (upd m (at_ A ArticleProg.xNameLen) (BitVec.ofNat 64 0)) (at_ A ArticleProg.xOutLen)
    (BitVec.ofNat 64 0))
    (at_ A ArticleProg.xMsgLen) (BitVec.ofNat 64 0)) (at_ A ArticleProg.xKnownN) (BitVec.ofNat 64 0)

/-- The memory after the prologue: those cleared, then the empty line's place stored if the shape is right. -/
def proMem (A : Word) (a : Bytes) (m : Word → Word) : Word → Word := structMem ArticleSpec.spec A a (m4 A m)

theorem m4_at {A : Word} {m : Word → Word} {y : Nat} (hy : y < 2 ^ 64)
    (h : y < ArticleProg.w 11 ∨ ArticleProg.w 14 < y) : m4 A m (at_ A y) = m (at_ A y) := by
  have hs := DN.News.ArticleFields.w_eq
  have e : ∀ j, j < 32 → y ≠ ArticleProg.w j → at_ A y ≠ at_ A (ArticleProg.w j) := fun j hj hne =>
    DN.News.ScanRun.at_ne hy (w_lt64 hj) hne
  simp only [hs] at h
  exact (upd_ne _ (e 14 (by decide) (by rw [hs]; omega))).trans ((upd_ne _ (e 13 (by decide) (by rw [hs]; omega))).trans
    ((upd_ne _ (e 12 (by decide) (by rw [hs]; omega))).trans (upd_ne _ (e 11 (by decide) (by rw [hs]; omega)))))

theorem pro_at {A : Word} {a : Bytes} {m : Word → Word} {y : Nat} (hy : y < 2 ^ 64)
    (h : y < ArticleProg.w 11 ∨ ArticleProg.w 16 < y) : proMem A a m (at_ A y) = m (at_ A y) := by
  have hs := DN.News.ArticleFields.w_eq
  simp only [hs] at h
  have h4 := m4_at (A := A) (m := m) hy (by rw [hs, hs]; omega)
  unfold proMem structMem
  split
  · exact (upd_ne _ (DN.News.ScanRun.at_ne hy (w_lt64 (i := 16) (by decide)) (by rw [hs]; omega))).trans h4
  · exact h4

theorem pro_nameLen {A : Word} {a : Bytes} {m : Word → Word} : proMem A a m (at_ A ArticleProg.xNameLen) = 0 := by
  have e : ∀ i j, i < 32 → j < 32 → i ≠ j → at_ A (ArticleProg.w i) ≠ at_ A (ArticleProg.w j) := fun i j hi hj h =>
    DN.News.ScanRun.at_ne (w_lt64 hi) (w_lt64 hj) (by simp only [ArticleProg.w]; omega)
  have h4 : m4 A m (at_ A ArticleProg.xNameLen) = 0 :=
    (upd_ne _ (e 11 14 (by decide) (by decide) (by decide))).trans ((upd_ne _ (e 11 13 (by decide) (by decide)
      (by decide))).trans ((upd_ne _ (e 11 12 (by decide) (by decide) (by decide))).trans (upd_eq _ _ _)))
  unfold proMem structMem
  split
  · exact (upd_ne _ (e 11 16 (by decide) (by decide) (by decide))).trans h4
  · exact h4

theorem pro_free {A : Word} {a : Bytes} {m : Word → Word} {x : Word} (hx : ¬CheckScr A x) :
    proMem A a m x = m x := by
  have e : ∀ i, (i = 11 ∨ i = 12 ∨ i = 13 ∨ i = 14 ∨ i = 16) → x ≠ at_ A (ArticleProg.w i) := fun i hi h =>
    hx (.inr (.inr (.inr (.inr ⟨i, hi, h⟩))))
  have h4 : m4 A m x = m x := (upd_ne _ (e 14 (by decide))).trans ((upd_ne _ (e 13 (by decide))).trans
    ((upd_ne _ (e 12 (by decide))).trans (upd_ne _ (e 11 (by decide)))))
  unfold proMem structMem
  split
  · exact (upd_ne _ (e 16 (by decide))).trans h4
  · exact h4

theorem pro_sep {A : Word} {a : Bytes} {m : Word → Word} (h0 : DN.News.ArticleLines.shapeOf ArticleSpec.spec a = 0)
    {p : Nat} (hp : (DN.News.ArticleLines.spans a 0).2 = some p) :
    proMem A a m (at_ A ArticleProg.xSep) = BitVec.ofNat 64 p := by
  unfold proMem structMem; rw [if_pos h0, hp]; exact upd_eq _ _ _

/-- **`artCheck` answers as `checkWith`**: the verdict's number, the refusal's name or the accepted article's header,
message identifier and known groups. The grammar's answers on the fields and on the sender are premises. -/
theorem artCheck_ok (o : Oracle σ) {A : Word} {s1 : PancakeState σ} (hA : Area ArticleProg.ofs A s1)
    (hD : ArtDom A s1.memaddrs) (hT : TabDom A s1.memaddrs esP) (hcode : ArtCode s1.code) {a : Bytes}
    (hlen : a.length ≤ artMax) (hR : Reads s1 A a s1.memory) (hall : AllSets A s1.memory)
    (htab : TablesAt A s1.memaddrs s1.be s1.memory esP)
    (hkd : DN.News.ArticleTables.KindsAt ArticleSpec.spec esP A s1.memory)
    (hb : s1.memory (at_ A aBroken) = 0) (hlw : s1.memory (at_ A ArticleProg.xLen) = BitVec.ofNat 64 a.length)
    {ctx : ArticleSpec.Context} (hctx : DN.News.ArticleAdded.CtxAt A s1.memaddrs s1.be ctx s1.memory)
    (hGr : GroupsAt A s1.memaddrs s1.be ctx.groups s1.memory)
    (hgram : DN.News.ArticleLines.shapeOf ArticleSpec.spec a = 0 →
      DN.News.ArticleFields.GramOk a (DN.News.ArticleLines.spans a 0).1)
    (hgm : DN.News.ArticleLines.shapeOf ArticleSpec.spec a = 0 →
      (∀ g ∈ groups a (DN.News.ArticleLines.spans a 0).1, DN.News.ArticleFields.fieldNum (fieldOf a g) = 0) →
      ArticleSpec.has ((groups a (DN.News.ArticleLines.spans a 0).1).map (fieldOf a)) "Sender" = false →
      ∀ f, ArticleSpec.find? ((groups a (DN.News.ArticleLines.spans a 0).1).map (fieldOf a)) "From" = some f →
      ∃ b, DN.News.Abnf.matches? AbnfRules.grammar AbnfRules.depth (ArticleSpec.ruleNamed "mailbox")
        (f.value.map BitVec.toNat) = .ok b) :
    ∃ body, Lower.lower (gd (ArticleProg.artCheck ArticleSpec.spec esP)) = some body ∧
      SafeR o (fun s => s = s1) body (CheckRet A s1.memaddrs s1.be ctx a s1.memory) fun _ => False := by
  have hA8 := hA.hA
  have hM := artMax_eq
  have hs := DN.News.ArticleFields.w_eq
  have hF := xFirst_eq; have hl := (DN.News.ArticleTables.lay esP).1; have hsz := esP_size
  have hbX : aBroken < ArticleProg.X := by have := DN.News.ArticleGrammar.broken_low; have := sets_le_X; omega
  -- the prologue's memory
  have hlo : ∀ y, y < ArticleProg.X → proMem A a s1.memory (at_ A y) = s1.memory (at_ A y) := fun y hy =>
    pro_at (by rw [X_val] at hy; omega) (.inl (by rw [hs]; rw [X_val] at hy; omega))
  have hlo4 : ∀ y, y < ArticleProg.X → m4 A s1.memory (at_ A y) = s1.memory (at_ A y) := fun y hy =>
    m4_at (by rw [X_val] at hy; omega) (.inl (by rw [hs]; rw [X_val] at hy; omega))
  have hhi : ∀ y, ArticleProg.xFlags esP ≤ y → y < 2 ^ 40 →
      proMem A a s1.memory (at_ A y) = s1.memory (at_ A y) := fun y h1 h2 =>
    pro_at (by omega) (.inr (by rw [hs]; omega))
  have hm0f : ∀ w, ¬CheckScr A w → proMem A a s1.memory w = s1.memory w := fun w hw => pro_free hw
  have hbr : proMem A a s1.memory (at_ A aBroken) = 0 := (hlo _ hbX).trans hb
  refine body_of ?_
  show FragR o _ (guardL (ArticleProg.artCheck ArticleSpec.spec esP).body) _ _
  rw [artCheck_g, headS, List.append_assoc, List.append_assoc]
  have hle := shape_le a
  refine fragR_append (M := fun u => RunF s1 [("sh", BitVec.ofNat 64 (DN.News.ArticleLines.shapeOf ArticleSpec.spec a)),
    ("a", A)] (· = proMem A a s1.memory) u ∧ DN.News.ArticleLines.shapeOf ArticleSpec.spec a = 0) ?_
    (fragR_pure _ (fun u h => h.2) (lowKK_append pre_low (lowKK_append loop_low tailS_low)) fun h0 =>
      fragR_conseq (P0 := RunF s1 [("sh", BitVec.ofNat 64 (DN.News.ArticleLines.shapeOf ArticleSpec.spec a)),
        ("a", A)] (· = proMem A a s1.memory)) ?_ (fun u h => h.1) fun _ h => h)
  · unfold hPro
    obtain ⟨EA, hEA⟩ := DN.News.AbnfSets.atOff_lower ArticleProg.ofs
    refine fragR_conseq (P0 := RunF s1 [] (· = s1.memory)) ?_ (entry_run (l := []) (fun q hq => nomatch hq) rfl)
      fun _ h => h
    refine fragR_append (xs := [_]) (fragR_of (runF_dec o hEA rfl (v := A) fun u h =>
      DN.News.AbnfSets.areaAt_eval hA h.1.base hEA)) ?_
    refine fragR_append (xs := [_]) (fragR_of (DN.News.ArticleTables.setC_frag o rfl (off := ArticleProg.xNameLen)
      (c := 0)
      (by decide) (artDom_w hD (i := 11) (by decide)))) ?_
    refine fragR_append (xs := [_]) (fragR_of (DN.News.ArticleTables.setC_frag o rfl (off := ArticleProg.xOutLen)
      (c := 0)
      (by decide) (artDom_w hD (i := 12) (by decide)))) ?_
    refine fragR_append (xs := [_]) (fragR_of (DN.News.ArticleTables.setC_frag o rfl (off := ArticleProg.xMsgLen)
      (c := 0)
      (by decide) (artDom_w hD (i := 13) (by decide)))) ?_
    refine fragR_append (xs := [_]) (fragR_of (DN.News.ArticleTables.setC_frag o rfl (off := ArticleProg.xKnownN)
      (c := 0)
      (by decide) (artDom_w hD (i := 14) (by decide)))) ?_
    refine fragR_conseq (P0 := RunF s1 [("a", A)] (· = m4 A s1.memory)) ?_ (fun u h => h) fun _ h => h
    -- the section's shape
    have hR4 := reads_lo hA8 hlen hR hlo4
    refine fragR_append (xs := [_, _]) (structCall_frag o hA hD hcode (rt := "sh") (by decide) rfl rfl hlen hR4.input
      ((hlo4 _ hbX).trans hb) ((m4_at (w_lt64 (i := 1) (by decide)) (.inl (by rw [hs, hs]; omega))).trans hlw)) ?_
    refine fragR_ite o rfl (fun u k h => ⟨runF_clock _ _ _ u k h.1, h.2⟩)
      (fun u h => ⟨_, ev_var (vals_lookup h.1.vals rfl)⟩) ?_
      (fun _ _ _ _ hy => by simp [declared] at hy) (fragR_of (frag_nil o fun u h => ⟨h.1, ?_⟩))
      (fun _ _ _ _ hy => by simp [declared] at hy)
    · -- a shape refused
      refine fragR_ret o rfl fun u h => ⟨_, ev_var (vals_lookup h.1.1.vals rfl), ?_⟩
      have hne : DN.News.ArticleLines.shapeOf ArticleSpec.spec a ≠ 0 := fun e => h.2 (by
        rw [ev_var (vals_lookup h.1.1.vals rfl), e]; rfl)
      obtain ⟨x, hx1, hx2, hx3⟩ := refused_shape (ctx := ctx) hne
      have hmu : u.memory = proMem A a s1.memory := h.1.2
      have := ret_refused (dm := s1.memaddrs) (be := s1.be) (ms := s1.memory) hx1 (m := u.memory)
        (by rw [hmu]; exact hbr)
        (fun w hw => by rw [hmu]; exact hm0f w hw) (by rw [hmu]; exact sets_lo hall hlo)
        (by rw [hx3, hmu]; exact nameAt_empty pro_nameLen) (by rw [hx3]; exact Nat.zero_le _)
      rwa [hx2] at this
    · have he : eval u (.var "sh") = some (BitVec.ofNat 64 (DN.News.ArticleLines.shapeOf ArticleSpec.spec a)) :=
        ev_var (vals_lookup h.1.1.vals rfl)
      rw [he] at h
      have := congrArg BitVec.toNat (Option.some.inj h.2)
      simp only [BitVec.toNat_ofNat] at this
      rw [Nat.mod_eq_of_lt (by omega)] at this
      exact this
  obtain ⟨p, hp, hpH, hlong, hmal⟩ := shape0_facts h0
  have hL : Lines a 0 (DN.News.ArticleLines.spans a 0).1 p :=
    DN.News.ArticleLines.spans_lines a _ 0 rfl (Nat.zero_le _) (by rw [← hp])
  have hline : ∀ q ∈ (DN.News.ArticleLines.spans a 0).1, q.2 - q.1 ≤ ArticleProg.nameCap := fun q hq => by
    have := List.any_eq_false.1 hlong q hq
    have hlm : ArticleSpec.spec.lineMax ≤ ArticleProg.nameCap := by decide
    simp only [decide_eq_true_eq] at this; omega
  have hSI : p ≤ inputMax := by have : ArticleSpec.spec.headerMax = 65536 := rfl; rw [inputMax_eq]; omega
  have hB : ChkBase s1 A (proMem A a s1.memory) p esP :=
    ⟨hbr, pro_sep h0 hp, hT, DN.News.ArticleFields.tablesAt_hi hA8 hsz hhi htab,
      DN.News.ArticleFields.kindsAt_hi hsz hhi hkd⟩
  -- the empty line's place
  refine fragR_append (xs := [_]) (fragR_of (runF_dec o (wd_lower 16) rfl (v := BitVec.ofNat 64 p) fun u h => by
    rw [loadA_eval h.1.memaddrs (artDom_w hD (i := 16) (by decide)) (atA_eval (vals_lookup h.1.vals rfl)), h.2]
    exact congrArg some (pro_sep h0 hp))) ?_
  refine fragR_append (xs := [_]) (fragR_of (kept_frag o (by omega) (runF_clock _ _ _) fun u h =>
    ⟨p, vals_lookup h.1.vals rfl, by have : ArticleSpec.spec.headerMax = 65536 := rfl; omega⟩)) ?_
  -- the first fields' table cleared
  refine fragR_append (xs := [_]) (fragR_of (runF_dec o rfl rfl (v := 0) fun _ _ => rfl)) ?_
  refine fragR_append (xs := [_]) (DN.News.ArticleFields.chk_clear o hA hlen hT (reads_lo hA8 hlen hR hlo)
    (sets_lo hall hlo) rfl rfl) ?_
  refine fragR_append (xs := [_]) (DN.News.ArticleFields.cs_dec o rfl rfl (val := optW none) fun _ _ _ _ => rfl) ?_
  refine fragR_append (xs := [_]) (DN.News.ArticleFields.cs_dec o rfl rfl (val := optW none) fun _ _ _ _ => rfl) ?_
  refine fragR_append (xs := [_]) (DN.News.ArticleFields.cs_dec o rfl rfl (val := optW none) fun _ _ _ _ => rfl) ?_
  refine fragR_append (xs := [_]) (DN.News.ArticleFields.cs_dec o rfl rfl (val := BitVec.ofNat 64 0)
    fun _ _ _ _ => rfl) ?_
  -- the fields
  have hRef : DN.News.ArticleFields.RefR s1 A (proMem A a s1.memory) a (DN.News.ArticleLines.spans a 0).1
      (CheckRet A s1.memaddrs s1.be ctx a s1.memory) := by
    intro gd P e more rest hgr hz hne M hM
    obtain ⟨x, hx1, hx2, hx3⟩ := refused_field (ctx := ctx) (shape_zero h0) hgr hz hne
    have hg : ((P, e) :: more.takeWhile (cont a)) ∈ groups a (DN.News.ArticleLines.spans a 0).1 := by
      rw [hgr]; exact List.mem_append_right _ List.mem_cons_self
    obtain ⟨P', e', more', heq, hf, hmemL⟩ := group_field hL hmal hg
    obtain ⟨h1, -⟩ := List.cons.inj heq
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj h1
    have hcol := DN.News.ArticleLines.fieldAt_colon hf
    have hmem := DN.News.ArticleLines.lines_mem hf.lines (P, e) List.mem_cons_self
    have hK : DN.News.ArticleLines.nameLen a P e < ArticleProg.nameCap := by
      have := hline (P, e) hmemL; simp only at this; omega
    have := ret_name hA8 hD (chkT_of hM) hB hm0f hx1 (name := seg a P (P + DN.News.ArticleLines.nameLen a P e))
      hx3 (by show (seg a P (P + DN.News.ArticleLines.nameLen a P e)).length ≤ _
              rw [DN.News.ArticleLines.seg_length a (by omega) (by omega)]; omega)
                (DN.News.ArticleLines.nameLen a P e) e
    rwa [hx2] at this
  refine fragR_append (xs := [_]) (fragR_conseq (DN.News.ArticleFields.chk_loop o hA hD hcode hlen hB hSI hL hmal hline
    (hgram h0) hRef) (fun u ⟨M, h, hM⟩ => ⟨M, runF_mono h (fun q hq => by
      simp only [DN.News.ArticleFields.chkL, List.mem_cons, List.mem_nil_iff, or_false] at hq ⊢
      rcases hq with rfl | rfl | rfl | rfl | rfl | rfl <;> simp) (fun _ h => h), hM⟩) fun _ h => h) ?_
  -- the checks after the fields
  refine fragR_pure _ (fun u h => h.2) tailS_low fun hnoref => fragR_conseq
    (tail_check o hA hD hcode hlen hB hpH hL hmal
    hline (ctxAt_keep hA8 (fun i _ h7 => pro_at (w_lt64 (by omega)) (.inl (by rw [hs, hs]; omega)))
      (fun y h1 h2 => pro_at (by rw [xName_eq] at h2; omega)
        (.inr (by rw [hs]; have := DN.News.ArticleListRun.xGroups_eq; omega))) hctx)
    (groupsAt_keep hA8 (pro_at (w_lt64 (i := 8) (by decide)) (.inl (by simp only [ArticleProg.xGroupsN, hs]; omega)))
      (fun y h1 h2 => pro_at (by rw [xName_eq] at h2; omega)
        (.inr (by rw [hs]; have := DN.News.ArticleListRun.xGroups_eq; omega))) hGr)
    hm0f pro_nameLen (shape_zero h0) hnoref (hgm h0 hnoref)) (fun u h => ?_) fun _ h => h
  obtain ⟨M, hr, hM⟩ := h.1
  exact ⟨hr.1, by rw [hr.2]; exact chkT_of hM⟩

/-! ## The premises can hold -/

theorem chkT_witness : ChkT (bareState ()) 0 DN.News.ArticleFields.wClr [] [] DN.News.ArticleFields.wClr :=
  chkT_of DN.News.ArticleFields.chkM_witness

theorem nameAt_witness : NameAt 0 (fun _ => true) false [] (fun _ => 0) := nameAt_empty rfl

theorem constAt_witness : ConstAt 0 (fun _ => true) false "" (fun _ => 0) (fun _ => 0) :=
  ⟨fun _ hj => absurd hj (Nat.not_lt_zero _), rfl, fun _ _ _ => rfl⟩

theorem gScratch_witness : gScratch 0 (at_ 0 ArticleProg.xKnownN) := .inr ⟨_, DN.News.ArticleListRun.gWrites_witness,
    rfl⟩

/-- The empty article only, of a refused shape: the kernel does not reduce `spans` on a real one. It meets both grammar
premises of `artCheck_ok` with nothing to match. -/
theorem gram_witness : DN.News.ArticleFields.GramOk [] (DN.News.ArticleLines.spans [] 0).1 := by
  rw [(DN.News.ArticleLines.spans_nil []).2 (.inl rfl)]; exact DN.News.ArticleFields.gramOk_witness

theorem sender_witness :
    ∀ f, ArticleSpec.find? ((groups [] (DN.News.ArticleLines.spans [] 0).1).map (fieldOf [])) "From" = some f → ∃ b,
      DN.News.Abnf.matches? AbnfRules.grammar AbnfRules.depth (ArticleSpec.ruleNamed "mailbox")
      (f.value.map BitVec.toNat) = .ok b := fun f h => by
  rw [(DN.News.ArticleLines.spans_nil []).2 (.inl rfl), groups] at h
  exact absurd h (by simp [ArticleSpec.find?])

end DN.News.ArticleCheck
